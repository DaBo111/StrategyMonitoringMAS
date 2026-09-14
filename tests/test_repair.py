"""The repair pipeline of Section 7 and the VITAMIN bridge."""

import pytest

from conftest import requires_vitamin

from strategy_monitor.repair import (
    RepairOutcome,
    RepairPipeline,
    ViolationKind,
    fixed_synthesiser,
)
from strategy_monitor.cgs import CGS
from strategy_monitor.strategies import NaturalMemorylessStrategy
from strategy_monitor.trace import replay
from strategy_monitor.verdict import Verdict


@pytest.fixture
def play_in_when_p():
    return NaturalMemorylessStrategy.build(
        ["a", "b"],
        {"a": [("p", "in"), ("true", "idle")], "b": [("p", "in"), ("true", "idle")]},
    )


@pytest.fixture
def solo_b():
    return NaturalMemorylessStrategy.build(["b"], {"b": [("true", "idle")]})


# ======================================================================
# Section 7.1 -- coalition strategy violation
# ======================================================================


class TestCoalitionRepair:
    def test_deviating_agent_is_excluded_and_a_new_strategy_adopted(
        self, running_example, play_in_when_p, solo_b
    ):
        pipeline = RepairPipeline(
            cgs=running_example,
            coalition=("a", "b"),
            strategy=play_in_when_p,
            synthesiser=fixed_synthesiser(solo_b),
        )
        outcome = pipeline.observe("s0", ("out", "in", "in"))
        assert outcome is RepairOutcome.COALITION_REPAIRED
        assert pipeline.coalition == ("b",)
        assert pipeline.strategy is solo_b
        assert not pipeline.stopped
        event = pipeline.events[0]
        assert event.kind is ViolationKind.COALITION
        assert event.excluded_agent == "a"

    def test_execution_resumes_under_the_new_strategy(
        self, running_example, play_in_when_p, solo_b
    ):
        pipeline = RepairPipeline(
            cgs=running_example,
            coalition=("a", "b"),
            strategy=play_in_when_p,
            synthesiser=fixed_synthesiser(solo_b),
        )
        pipeline.observe("s0", ("out", "in", "in"))
        # b now idles everywhere; a is no longer monitored
        assert pipeline.observe("s0", ("out", "idle", "in")) is RepairOutcome.NONE
        assert pipeline.verdict is Verdict.UNKNOWN
        assert len(pipeline.events) == 1

    def test_repair_fails_when_nothing_can_be_synthesised(
        self, running_example, play_in_when_p
    ):
        pipeline = RepairPipeline(
            cgs=running_example,
            coalition=("a", "b"),
            strategy=play_in_when_p,
            synthesiser=fixed_synthesiser(None),
        )
        assert pipeline.observe("s0", ("out", "in", "in")) is RepairOutcome.FAILED
        assert pipeline.stopped
        assert pipeline.events[0].outcome is RepairOutcome.FAILED
        assert "monitoring stops" in pipeline.events[0].detail
        # further observations are refused
        assert pipeline.observe("s0", ("in", "in", "in")) is RepairOutcome.STOPPED

    def test_repeated_deviation_shrinks_the_coalition_to_nothing(
        self, running_example, play_in_when_p, solo_b
    ):
        pipeline = RepairPipeline(
            cgs=running_example,
            coalition=("a", "b"),
            strategy=play_in_when_p,
            synthesiser=fixed_synthesiser(solo_b),
        )
        pipeline.observe("s0", ("out", "in", "in"))  # a is excluded
        assert pipeline.coalition == ("b",)
        # b now deviates from its own strategy; A' is empty, so repair fails
        assert pipeline.observe("s0", ("in", "in", "in")) is RepairOutcome.FAILED
        assert pipeline.stopped
        assert pipeline.events[-1].new_coalition == ()


# ======================================================================
# Section 7.2 -- model violation
# ======================================================================


class TestModelRepair:
    def test_unexpected_successor_updates_delta(self, running_example, play_in_when_p):
        pipeline = RepairPipeline(
            cgs=running_example,
            coalition=("a", "b"),
            strategy=play_in_when_p,
            synthesiser=fixed_synthesiser(play_in_when_p),
        )
        assert pipeline.observe("s0", ("in", "in", "out")) is RepairOutcome.NONE
        # delta(s0, (in,in,out)) = s1, but the system goes to s3
        assert pipeline.observe("s3", ("in", "in", "in")) is RepairOutcome.MODEL_REPAIRED
        assert pipeline.cgs.step("s0", ("in", "in", "out")) == "s3"
        event = pipeline.events[0]
        assert event.kind is ViolationKind.MODEL
        assert event.added_transition == ("s0", ("in", "in", "out"), "s3")
        assert not pipeline.stopped

    def test_the_rest_of_delta_is_unchanged(self, running_example, play_in_when_p):
        pipeline = RepairPipeline(
            cgs=running_example,
            coalition=("a", "b"),
            strategy=play_in_when_p,
            synthesiser=fixed_synthesiser(play_in_when_p),
        )
        pipeline.observe("s0", ("in", "in", "out"))
        pipeline.observe("s3", ("in", "in", "in"))
        for state in running_example.states:
            for profile in running_example.available_profiles(state):
                if (state, profile) == ("s0", ("in", "in", "out")):
                    continue
                assert pipeline.cgs.step(state, profile) == running_example.step(state, profile)

    def test_repaired_transition_is_not_flagged_again(self, running_example, play_in_when_p):
        pipeline = RepairPipeline(
            cgs=running_example,
            coalition=("a", "b"),
            strategy=play_in_when_p,
            synthesiser=fixed_synthesiser(play_in_when_p),
        )
        pipeline.observe("s0", ("in", "in", "out"))
        pipeline.observe("s3", ("in", "in", "in"))
        assert pipeline.observe("s3", ("in", "in", "in")) is RepairOutcome.NONE
        assert len(pipeline.events) == 1

    def test_model_repair_can_also_fail(self, running_example, play_in_when_p):
        pipeline = RepairPipeline(
            cgs=running_example,
            coalition=("a", "b"),
            strategy=play_in_when_p,
            synthesiser=fixed_synthesiser(None),
        )
        pipeline.observe("s0", ("in", "in", "out"))
        assert pipeline.observe("s3", ("in", "in", "in")) is RepairOutcome.FAILED
        assert pipeline.stopped

    def test_compliant_trace_triggers_nothing(self, running_example, play_in_when_p):
        pipeline = RepairPipeline(
            cgs=running_example,
            coalition=("a", "b"),
            strategy=play_in_when_p,
            synthesiser=fixed_synthesiser(None),
            goal="G(p | (q & X p))",
        )
        trace = replay(running_example, [("in", "in", "out"), ("in", "in", "in")])
        assert pipeline.run(trace) == []
        assert pipeline.verdict is Verdict.TOP_G


# ======================================================================
# VITAMIN
# ======================================================================


@requires_vitamin
class TestVitaminBridge:
    def test_export_round_trips_through_vitamin_own_parser(self, running_example, tmp_path):
        from model_checker.parsers.game_structures.cgs.cgs import CGS as VitaminCGS

        from strategy_monitor.vitamin import write_vitamin_model

        path = str(tmp_path / "model.txt")
        write_vitamin_model(running_example, path)
        parsed = VitaminCGS()
        parsed.read_file(path)

        assert list(parsed.states) == list(running_example.states)
        assert parsed.initial_state == running_example.initial_state
        assert parsed.get_number_of_agents() == 3
        assert parsed.get_agent_labels() == ["a", "b", "c"]
        assert list(parsed.atomic_propositions) == list(running_example.ap)
        for index, state in enumerate(running_example.states):
            label = running_example.label(state)
            expected = [1 if prop in label else 0 for prop in running_example.ap]
            assert list(parsed.matrix_prop[index]) == expected

    def test_every_profile_survives_the_export(self, running_example, tmp_path):
        from model_checker.parsers.game_structures.cgs.cgs import CGS as VitaminCGS

        from strategy_monitor.vitamin import action_token, write_vitamin_model

        path = str(tmp_path / "model.txt")
        write_vitamin_model(running_example, path)
        parsed = VitaminCGS()
        parsed.read_file(path)

        for row, source in enumerate(running_example.states):
            recovered = {}
            for column, target in enumerate(running_example.states):
                cell = parsed.graph[row][column]
                if cell in (0, "0"):
                    continue
                for profile in parsed.build_action_list(cell):
                    recovered[tuple(profile.split("|"))] = target
            expected = {
                tuple(action_token(a) for a in profile): running_example.step(source, profile)
                for profile in running_example.available_profiles(source)
            }
            assert recovered == expected, source

    def test_atl_model_checking(self, running_example):
        from strategy_monitor.vitamin import atl_model_check

        # a and b together can keep p: play in at s0, which reaches s0 or s1
        both = atl_model_check(running_example, ["a", "b"], "G p")
        assert both["satisfied"] is True
        assert both["states"] == {"s0", "s1", "s3"}

        # a alone cannot: b can idle and force s2, where p fails
        alone = atl_model_check(running_example, ["a"], "G p")
        assert alone["satisfied"] is False

        # p or q holds everywhere
        weak = atl_model_check(running_example, ["a"], "G(p || q)")
        assert weak["satisfied"] is True

    def test_coalition_is_translated_to_vitamin_numbering(self, running_example):
        from strategy_monitor.vitamin import atl_formula, natatl_formula

        assert atl_formula(running_example, ["a", "c"], "G p") == "<1,3>G p"
        assert natatl_formula(running_example, ["b"], "G p", 2) == "<{2}, 2>G p"

    def test_natatl_synthesis_yields_a_monitorable_strategy(self, running_example):
        from strategy_monitor.monitors import NaturalMemorylessMonitor
        from strategy_monitor.vitamin import natatl_synthesize

        result = natatl_synthesize(running_example, ["a"], "G(p || q)", k=2)
        assert result.satisfiable
        assert result.strategy is not None
        assert result.strategy.coalition == ("a",)

        # the synthesised strategy is total over the model, so it drives a monitor
        table = result.strategy.to_kbounded(running_example)
        assert set(table.table) == {(s,) for s in running_example.states}
        monitor = NaturalMemorylessMonitor(running_example, result.strategy)
        compliant = table.table[("s0",)]["a"]
        monitor.observe("s0", (compliant, "in", "in"))
        assert monitor.verdict is Verdict.UNKNOWN

    def test_agent_c_alone_can_hold_p(self, running_example):
        """c controls the s0 self-loop: (*, *, in) keeps the system in s0."""
        from strategy_monitor.vitamin import atl_model_check, natatl_synthesize

        assert atl_model_check(running_example, ["c"], "G p")["satisfied"] is True
        result = natatl_synthesize(running_example, ["c"], "G p", k=1)
        assert result.satisfiable
        assert result.strategy.action_for("c", running_example.label("s0")) == "in"

    def test_unsatisfiable_synthesis_reports_failure(self, running_example):
        from strategy_monitor.vitamin import natatl_synthesize

        # p holds in s_I, so G !p is unrealisable whatever anyone plays
        result = natatl_synthesize(running_example, ["c"], "G !p", k=1)
        assert result.satisfiable is False
        assert result.strategy is None
        assert bool(result) is False

    def test_pipeline_with_the_vitamin_synthesiser(self, running_example, play_in_when_p):
        from strategy_monitor.repair import vitamin_synthesiser

        pipeline = RepairPipeline(
            cgs=running_example,
            coalition=("a", "b"),
            strategy=play_in_when_p,
            synthesiser=vitamin_synthesiser("G(p || q)", k=2),
        )
        assert pipeline.observe("s0", ("out", "in", "in")) is RepairOutcome.COALITION_REPAIRED
        assert pipeline.coalition == ("b",)
        assert pipeline.strategy.coalition == ("b",)
        assert not pipeline.stopped

    def test_pipeline_stops_when_the_objective_is_unrealisable_alone(
        self, running_example, play_in_when_p
    ):
        from strategy_monitor.repair import vitamin_synthesiser

        pipeline = RepairPipeline(
            cgs=running_example,
            coalition=("a", "b"),
            strategy=play_in_when_p,
            synthesiser=vitamin_synthesiser("G p", k=2),
        )
        assert pipeline.observe("s0", ("out", "in", "in")) is RepairOutcome.FAILED
        assert pipeline.stopped


# ======================================================================
# VITAMIN: what the bridge can and cannot carry
# ======================================================================


@requires_vitamin
class TestVitaminEncoding:
    """Regressions for the ways a model can be mangled on the way out."""

    @staticmethod
    def _roundtrip(cgs):
        """Export, reparse with VITAMIN, and recover delta from the matrix."""
        import os
        import tempfile

        from model_checker.parsers.game_structures.cgs.cgs import CGS as VitaminCGS

        from strategy_monitor.vitamin import action_token, write_vitamin_model

        handle, path = tempfile.mkstemp(suffix=".txt")
        os.close(handle)
        try:
            write_vitamin_model(cgs, path)
            parsed = VitaminCGS()
            parsed.read_file(path)
            recovered = {}
            for row, source in enumerate(cgs.states):
                for column, target in enumerate(cgs.states):
                    cell = parsed.graph[row][column]
                    if cell in (0, "0"):
                        continue
                    for profile in parsed.build_action_list(cell):
                        recovered[(source, tuple(profile.split("|")))] = target
            expected = {
                (source, tuple(action_token(a) for a in profile)): cgs.step(source, profile)
                for source in cgs.states
                for profile in cgs.available_profiles(source)
            }
            return recovered, expected
        finally:
            if os.path.exists(path):
                os.unlink(path)

    @staticmethod
    def _single_agent_model(actions):
        return CGS.from_dict(
            {
                "ap": ["p"],
                "agents": ["a"],
                "actions": {"a": list(actions)},
                "initial_state": "s0",
                "states": [
                    {
                        "id": "s0",
                        "labels": ["p"],
                        "transitions": [
                            {"to": "s0", "profiles": [[actions[0]]]},
                            {"to": "s1", "profiles": [["*"]]},
                        ],
                    },
                    {"id": "s1", "labels": [], "transitions": [{"to": "s1", "profiles": [["*"]]}]},
                ],
            }
        )

    def test_single_agent_multi_character_actions_survive(self):
        """A lone agent's profile has no '|', which VITAMIN would split per character.

        Without the trailing separator, ``stay`` comes back as ``s`` and the
        whole action set is silently corrupted.
        """
        model = self._single_agent_model(["stay", "leave"])
        recovered, expected = self._roundtrip(model)
        assert recovered == expected
        assert ("s0", ("stay",)) in recovered

    def test_the_encoding_forces_the_explicit_form_for_one_agent(self):
        from strategy_monitor.vitamin import encode_profile

        assert encode_profile(("stay",), 1) == "stay|"
        assert encode_profile(("stay", "hold"), 2) == "stay|hold"

    def test_single_agent_atl_sees_the_real_actions(self):
        from strategy_monitor.vitamin import atl_model_check

        model = self._single_agent_model(["stay", "leave"])
        # 'stay' self-loops in the p-state, everything else falls into !p
        assert atl_model_check(model, ["a"], "G p")["satisfied"] is True
        assert atl_model_check(model, ["a"], "G !p")["satisfied"] is False

    def test_multi_agent_models_are_unaffected(self, running_example):
        recovered, expected = self._roundtrip(running_example)
        assert recovered == expected


class TestVitaminExportValidation:
    """Names the syntax cannot carry are refused, not silently torn apart."""

    @staticmethod
    def _model(**overrides):
        data = {
            "ap": ["p"],
            "agents": ["a"],
            "actions": {"a": ["x"]},
            "initial_state": "s0",
            "states": [
                {"id": "s0", "labels": ["p"], "transitions": [{"to": "s0", "profiles": [["*"]]}]}
            ],
        }
        data.update(overrides)
        return CGS.from_dict(data)

    @pytest.mark.parametrize(
        "overrides,expected",
        [
            ({"ap": ["p-1"], "states": [{"id": "s0", "labels": ["p-1"],
              "transitions": [{"to": "s0", "profiles": [["*"]]}]}]}, "identifier"),
            ({"agents": ["robot 1"], "actions": {"robot 1": ["x"]}}, "whitespace"),
            ({"actions": {"a": ["a|b"]}}, "'|'"),
            ({"actions": {"a": ["a,b"]}}, "','"),
            ({"actions": {"a": ["*"]}}, "wildcard"),
            ({"initial_state": "s 0", "states": [{"id": "s 0", "labels": ["p"],
              "transitions": [{"to": "s 0", "profiles": [["*"]]}]}]}, "whitespace"),
        ],
    )
    def test_unrepresentable_names_are_refused(self, overrides, expected):
        from strategy_monitor.vitamin import VitaminExportError, to_vitamin_text

        with pytest.raises(VitaminExportError, match=expected):
            to_vitamin_text(self._model(**overrides))

    def test_ordinary_names_pass(self, running_example):
        from strategy_monitor.vitamin import check_exportable

        check_exportable(running_example)  # does not raise
        check_exportable(self._model(actions={"a": ["move_fast", "MOVE", "x-1"]}))

    def test_repaired_models_stay_exportable(self, running_example):
        """Section 7.2 can add states and actions; the result must still export."""
        from strategy_monitor.vitamin import check_exportable

        repaired = running_example.with_transition("s0", ("panic", "in", "out"), "s4")
        check_exportable(repaired)
        recovered, expected = TestVitaminEncoding._roundtrip(repaired)
        assert recovered == expected


@requires_vitamin
class TestNatATLIdleSemantics:
    """NatATL and ATL can disagree; the bridge says so instead of hiding it."""

    @staticmethod
    def _idle_unsafe_model(with_idle):
        actions = ["stay", "leave"] + (["IDLE"] if with_idle else [])
        return CGS.from_dict(
            {
                "ap": ["p"],
                "agents": ["a"],
                "actions": {"a": actions},
                "initial_state": "s0",
                "states": [
                    {
                        "id": "s0",
                        "labels": ["p"],
                        "transitions": [
                            {"to": "s0", "profiles": [["stay"]]},
                            {"to": "s1", "profiles": [["*"]]},
                        ],
                    },
                    {"id": "s1", "labels": [], "transitions": [{"to": "s1", "profiles": [["*"]]}]},
                ],
            }
        )

    def test_natatl_is_defeated_by_an_idle_action(self):
        """VITAMIN prunes to 'prescribed action or idle', so idling survives."""
        from strategy_monitor.vitamin import atl_model_check, natatl_synthesize

        with_idle = self._idle_unsafe_model(True)
        without = self._idle_unsafe_model(False)

        # the coalition can enforce G p either way
        assert atl_model_check(with_idle, ["a"], "G p")["satisfied"] is True
        assert atl_model_check(without, ["a"], "G p")["satisfied"] is True

        # but NatATL, run natively, only finds it when the agent cannot idle
        assert natatl_synthesize(without, ["a"], "G p", k=2, rename_idle=False).satisfiable is True
        assert (
            natatl_synthesize(with_idle, ["a"], "G p", k=2, rename_idle=False).satisfiable is False
        )
        # renaming the idle action -- the default -- recovers it
        assert natatl_synthesize(with_idle, ["a"], "G p", k=2).satisfiable is True

    def test_the_disagreement_is_reported(self):
        from strategy_monitor.vitamin import natatl_synthesize

        result = natatl_synthesize(
            self._idle_unsafe_model(True), ["a"], "G p", k=2, rename_idle=False
        )
        assert result.satisfiable is False
        assert result.atl_realisable is True
        assert "NatATL" in result.note and "idl" in result.note

    def test_genuine_unrealisability_is_reported_as_such(self, running_example):
        from strategy_monitor.vitamin import natatl_synthesize

        # p holds in s_I, so no coalition can enforce G !p
        result = natatl_synthesize(running_example, ["a", "b"], "G !p", k=1)
        assert result.satisfiable is False
        assert result.atl_realisable is False
        assert "ATL agrees" in result.note

    def test_cross_check_can_be_switched_off(self, running_example):
        from strategy_monitor.vitamin import natatl_synthesize

        result = natatl_synthesize(
            running_example, ["a", "b"], "G !p", k=1, cross_check=False
        )
        assert result.atl_realisable is None
        assert result.note == ""
