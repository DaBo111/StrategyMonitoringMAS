"""Modularity: the components can be mixed and matched.

Three axes are exercised here:

1. the strategy is *given* (any of the three classes, from a file or built in
   Python) or *obtained* from VITAMIN's NatATL synthesis;
2. the goal monitor is the plain LTL monitor or the one refined by intersecting
   with the CGS;
3. the assembled monitor need not have every component, and the repair pipeline
   follows whichever components are present.
"""

import pytest

from conftest import requires_vitamin

from strategy_monitor.goal import GoalMonitor
from strategy_monitor.ltl import alphabet_of
from strategy_monitor.monitors import (
    AdherenceMonitor,
    KBoundedMonitor,
    NaturalMemorylessAdherenceMonitor,
    NaturalMemorylessMonitor,
    NaturalRecallMonitor,
)
from strategy_monitor.repair import RepairOutcome, RepairPipeline, fixed_synthesiser
from strategy_monitor.strategies import (
    KBoundedStrategy,
    NaturalMemorylessStrategy,
    NaturalRecallStrategy,
    StrategyError,
    load_strategy,
    strategy_from_dict,
)
from strategy_monitor.suite import PRECEDENCE, MonitorSuite, build_strategy_monitor
from strategy_monitor.trace import replay
from strategy_monitor.verdict import Verdict

GOAL = "G(p | (q & X p))"


@pytest.fixture
def recall_strategy(running_example):
    return NaturalRecallStrategy.from_regex_sequences(
        ["a", "b"],
        {"a": [(".*[q].*", "out"), (".*", "in")], "b": [(".*[q].*", "out"), (".*", "in")]},
        alphabet_of(running_example.ap),
    )


# ======================================================================
# 1. the strategy is given, or synthesised
# ======================================================================


class TestStrategySource:
    def test_every_strategy_class_gets_the_right_monitor(
        self, running_example, paper_memoryless_strategy, paper_natural_strategy, recall_strategy
    ):
        cases = [
            (paper_memoryless_strategy, False, KBoundedMonitor),
            (paper_memoryless_strategy, True, AdherenceMonitor),
            (paper_natural_strategy, False, NaturalMemorylessMonitor),
            (paper_natural_strategy, True, NaturalMemorylessAdherenceMonitor),
            (recall_strategy, False, NaturalRecallMonitor),
        ]
        for strategy, adherence, expected in cases:
            monitor = build_strategy_monitor(running_example, strategy, adherence=adherence)
            assert type(monitor) is expected, (type(strategy).__name__, adherence)

    def test_adherence_is_refused_for_recall(self, running_example, recall_strategy):
        """Section 6.1 leaves the recall case for future work."""
        with pytest.raises(StrategyError, match="recall is left for future work"):
            build_strategy_monitor(running_example, recall_strategy, adherence=True)

    def test_strategy_from_a_file_drives_a_suite(self, running_example, tmp_path):
        import json

        path = tmp_path / "strategy.json"
        path.write_text(
            json.dumps(
                {
                    "type": "natural_memoryless",
                    "coalition": ["a", "b"],
                    "rules": {
                        "a": [["p", "in"], ["true", "idle"]],
                        "b": [["p", "in"], ["true", "idle"]],
                    },
                }
            ),
            encoding="utf-8",
        )
        strategy = load_strategy(str(path), alphabet_of(running_example.ap))
        suite = MonitorSuite.build(running_example, strategy=strategy)
        assert suite.run(replay(running_example, [("in", "in", "out")])) is Verdict.UNKNOWN

    def test_every_serialised_form_round_trips_into_a_suite(self, running_example):
        forms = [
            {"type": "k_bounded", "coalition": ["a"], "k": 1, "table": {s: {"a": "in"} for s in running_example.states}},
            {"type": "natural_memoryless", "coalition": ["a"], "rules": {"a": [["true", "in"]]}},
            {"type": "natural_recall", "coalition": ["a"], "regexes": {"a": [[".*", "in"]]}},
        ]
        for form in forms:
            strategy = strategy_from_dict(form, alphabet_of(running_example.ap))
            suite = MonitorSuite.build(running_example, strategy=strategy)
            assert suite.observe("s0", ("in", "in", "in")) is Verdict.UNKNOWN, form["type"]

    @requires_vitamin
    def test_synthesised_strategy_drops_straight_into_a_suite(self, running_example):
        """VITAMIN returns an ordinary NaturalMemorylessStrategy, so no adapter is needed."""
        from strategy_monitor.vitamin import natatl_synthesize

        result = natatl_synthesize(running_example, ["a"], "G(p || q)", k=2)
        assert result.satisfiable
        assert isinstance(result.strategy, NaturalMemorylessStrategy)

        suite = MonitorSuite.build(running_example, strategy=result.strategy, strict=False)
        assert isinstance(suite.strategy_monitor, NaturalMemorylessMonitor)
        prescribed = result.strategy.action_for("a", running_example.label("s0"))
        assert suite.observe("s0", (prescribed, "in", "in")) is Verdict.UNKNOWN

    @requires_vitamin
    def test_synthesised_strategy_also_supports_adherence_and_a_goal(self, running_example):
        from strategy_monitor.vitamin import natatl_synthesize

        strategy = natatl_synthesize(running_example, ["a"], "G(p || q)", k=2).strategy
        suite = MonitorSuite.build(
            running_example, strategy=strategy, goal=GOAL, adherence=True, strict=False
        )
        assert isinstance(suite.strategy_monitor, NaturalMemorylessAdherenceMonitor)
        assert suite.goal_monitor is not None


# ======================================================================
# 2. the goal monitor, with or without the model
# ======================================================================


class TestGoalComponent:
    def test_both_flavours_are_available(self, running_example):
        refined = MonitorSuite.build(running_example, goal=GOAL, use_model=True)
        plain = MonitorSuite.build(running_example, goal=GOAL, use_model=False)
        assert refined.goal_monitor.use_model is True
        assert plain.goal_monitor.use_model is False
        assert "refined" in refined.describe()
        assert "plain LTL" in plain.describe()

    def test_the_two_disagree_exactly_as_the_paper_says(self, running_example):
        trace = replay(running_example, [("in", "in", "out"), ("in", "in", "in")])
        refined = MonitorSuite.build(running_example, goal=GOAL, use_model=True)
        plain = MonitorSuite.build(running_example, goal=GOAL, use_model=False)
        assert refined.run(trace) is Verdict.TOP_G
        assert plain.run(trace) is Verdict.UNKNOWN

    def test_only_the_refined_one_detects_model_violations(self, running_example):
        word = [frozenset({"p"})]  # the first label must be pi(s_I) = {p,q}
        assert GoalMonitor(running_example, GOAL, use_model=True).evaluate(word) is Verdict.BOT_M
        assert GoalMonitor(running_example, GOAL, use_model=False).evaluate(word) is not Verdict.BOT_M


# ======================================================================
# 3. mix and match
# ======================================================================


class TestMixAndMatch:
    def test_strategy_only(self, running_example, paper_natural_strategy):
        suite = MonitorSuite.build(running_example, strategy=paper_natural_strategy)
        assert suite.goal_monitor is None
        assert set(suite.component_verdicts) == {"strategy"}
        assert suite.observe("s0", ("out", "in", "in")) is Verdict.BOT

    def test_goal_only(self, running_example):
        suite = MonitorSuite.build(running_example, goal=GOAL)
        assert suite.strategy_monitor is None
        assert set(suite.component_verdicts) == {"goal"}
        assert suite.violations == []
        # actions are simply ignored
        suite.observe("s0", ("out", "out", "out"))
        assert suite.verdict is Verdict.UNKNOWN

    def test_both(self, running_example, paper_natural_strategy):
        suite = MonitorSuite.build(running_example, strategy=paper_natural_strategy, goal=GOAL)
        assert set(suite.component_verdicts) == {"strategy", "goal"}

    def test_neither_is_refused(self, running_example):
        with pytest.raises(ValueError, match="at least one component"):
            MonitorSuite.build(running_example)

    def test_a_component_verdict_is_not_lost_in_the_combination(
        self, running_example, paper_natural_strategy
    ):
        suite = MonitorSuite.build(running_example, strategy=paper_natural_strategy, goal=GOAL)
        trace = replay(running_example, [("in", "in", "out"), ("out", "in", "in")])
        suite.run(trace)
        assert suite.component_verdicts["strategy"] is Verdict.BOT
        assert suite.component_verdicts["goal"] is Verdict.TOP_G
        # the violation wins the combination, but both are still readable
        assert suite.verdict is Verdict.BOT

    def test_precedence_is_total_over_the_conclusive_verdicts(self):
        assert set(PRECEDENCE) == {v for v in Verdict if v is not Verdict.UNKNOWN}
        assert PRECEDENCE[0] is Verdict.BOT_M

    def test_unknown_when_no_component_concludes(self, running_example, paper_natural_strategy):
        suite = MonitorSuite.build(running_example, strategy=paper_natural_strategy, goal=GOAL)
        assert suite.verdict is Verdict.UNKNOWN


# ======================================================================
# 3b. the repair pipeline follows the components
# ======================================================================


class TestRepairFollowsTheComponents:
    def test_goal_only_pipeline_repairs_the_model_without_synthesis(self, running_example):
        """No strategy means no coalition branch, but Section 7.2 still applies."""
        pipeline = RepairPipeline(cgs=running_example, goal=GOAL)
        assert pipeline.monitor is None
        assert pipeline.goal_monitor is not None
        assert pipeline.observe("s0", ("in", "in", "out")) is RepairOutcome.NONE
        # delta(s0,(in,in,out)) = s1, but the system goes to s3
        assert pipeline.observe("s3", ("in", "in", "in")) is RepairOutcome.MODEL_REPAIRED
        assert pipeline.cgs.step("s0", ("in", "in", "out")) == "s3"
        assert not pipeline.stopped
        assert pipeline.strategy is None

    def test_strategy_only_pipeline_has_no_goal_component(
        self, running_example, paper_natural_strategy
    ):
        pipeline = RepairPipeline(
            cgs=running_example,
            strategy=paper_natural_strategy,
            synthesiser=fixed_synthesiser(None),
        )
        assert pipeline.goal_monitor is None
        assert set(pipeline.component_verdicts) == {"strategy"}

    def test_coalition_defaults_to_the_strategy_coalition(
        self, running_example, paper_natural_strategy
    ):
        pipeline = RepairPipeline(cgs=running_example, strategy=paper_natural_strategy)
        assert pipeline.coalition == paper_natural_strategy.coalition

    def test_a_k_bounded_strategy_can_drive_the_pipeline(
        self, running_example, paper_memoryless_strategy
    ):
        """The pipeline is no longer tied to natural memoryless strategies."""
        replacement = KBoundedStrategy.memoryless(["b"], {s: {"b": "idle"} for s in running_example.states})
        pipeline = RepairPipeline(
            cgs=running_example,
            strategy=paper_memoryless_strategy,
            synthesiser=fixed_synthesiser(replacement),
        )
        assert isinstance(pipeline.monitor, KBoundedMonitor)
        assert pipeline.observe("s0", ("out", "in", "in")) is RepairOutcome.COALITION_REPAIRED
        assert pipeline.coalition == ("b",)
        assert isinstance(pipeline.monitor, KBoundedMonitor)

    def test_a_recall_strategy_can_drive_the_pipeline(self, running_example, recall_strategy):
        pipeline = RepairPipeline(
            cgs=running_example, strategy=recall_strategy, synthesiser=fixed_synthesiser(None)
        )
        assert isinstance(pipeline.monitor, NaturalRecallMonitor)
        # s0 satisfies q, so 'out' is prescribed and 'in' is a deviation
        assert pipeline.observe("s0", ("in", "in", "in")) is RepairOutcome.FAILED

    def test_adherence_and_plain_ltl_are_passed_through(
        self, revised_example, adherence_strategy
    ):
        pipeline = RepairPipeline(
            cgs=revised_example,
            strategy=adherence_strategy,
            goal=GOAL,
            adherence=True,
            use_model=False,
        )
        assert isinstance(pipeline.monitor, AdherenceMonitor)
        assert pipeline.goal_monitor.use_model is False

    def test_adherence_verdict_reaches_the_pipeline(self, revised_example, adherence_strategy):
        pipeline = RepairPipeline(
            cgs=revised_example, strategy=adherence_strategy, adherence=True
        )
        trace = replay(
            revised_example,
            [("in", "in", "out"), ("out", "in", "in"), ("out", "out", "in"), ("in", "in", "in")],
        )
        pipeline.run(trace)
        assert pipeline.verdict is Verdict.TOP_S
        assert pipeline.events == []

    def test_pipeline_with_nothing_to_monitor_is_refused(self, running_example):
        with pytest.raises(ValueError, match="something to monitor"):
            RepairPipeline(cgs=running_example)

    def test_no_synthesiser_means_a_violation_stops_monitoring(
        self, running_example, paper_natural_strategy
    ):
        pipeline = RepairPipeline(cgs=running_example, strategy=paper_natural_strategy)
        assert pipeline.observe("s0", ("out", "in", "in")) is RepairOutcome.FAILED
        assert pipeline.stopped

    @requires_vitamin
    def test_a_synthesised_strategy_can_seed_the_pipeline(self, running_example):
        from strategy_monitor.repair import vitamin_synthesiser
        from strategy_monitor.vitamin import natatl_synthesize

        seed = natatl_synthesize(running_example, ["a", "b"], "G(p || q)", k=2).strategy
        pipeline = RepairPipeline(
            cgs=running_example,
            strategy=seed,
            synthesiser=vitamin_synthesiser("G(p || q)", k=2),
            goal=GOAL,
        )
        assert set(pipeline.component_verdicts) == {"strategy", "goal"}
        deviation = next(
            action
            for action in ("in", "out", "idle")
            if action != seed.action_for("a", running_example.label("s0"))
        )
        outcome = pipeline.observe("s0", (deviation, "in", "in"))
        assert outcome is RepairOutcome.COALITION_REPAIRED
        assert pipeline.coalition == ("b",)
