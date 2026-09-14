"""Exact strategy verification, and the VITAMIN idle workaround it makes safe.

``strategy_monitor.verify.enforces`` restricts the model to the strategy and
model-checks the goal on the result.  It needs no VITAMIN and takes the full LTL
grammar, so it can check the paper's own goal directly.
"""

import builtins

import pytest

from conftest import requires_vitamin

from strategy_monitor.automata import buchi_is_empty, buchi_lasso
from strategy_monitor.cgs import CGS
from strategy_monitor.ltl import alphabet_of, ltl_to_buchi, parse_ltl, satisfies
from strategy_monitor.strategies import (
    KBoundedStrategy,
    NaturalMemorylessStrategy,
    NaturalRecallRegexStrategy,
    StrategyError,
)
from strategy_monitor.verify import enforces, restrict

GOAL = "G(p | (q & X p))"


def constant(x, y):
    return NaturalMemorylessStrategy.build(
        ["a", "b"], {"a": [("true", x)], "b": [("true", y)]}
    )


@pytest.fixture
def hard_model():
    """s0 needs x, s1 needs y, and idling anywhere falls into the !p sink."""
    return CGS.from_dict(
        {
            "ap": ["p", "q"],
            "agents": ["a"],
            "actions": {"a": ["x", "y", "idle"]},
            "initial_state": "s0",
            "states": [
                {
                    "id": "s0",
                    "labels": ["p", "q"],
                    "transitions": [
                        {"to": "s1", "profiles": [["x"]]},
                        {"to": "s2", "profiles": [["*"]]},
                    ],
                },
                {
                    "id": "s1",
                    "labels": ["p"],
                    "transitions": [
                        {"to": "s1", "profiles": [["y"]]},
                        {"to": "s2", "profiles": [["*"]]},
                    ],
                },
                {"id": "s2", "labels": [], "transitions": [{"to": "s2", "profiles": [["*"]]}]},
            ],
        }
    )


# ======================================================================
# the emptiness check the verifier rests on
# ======================================================================


class TestBuchiEmptiness:
    def test_a_lasso_is_a_word_the_automaton_accepts(self):
        letters = alphabet_of(["p", "q"])
        for text in ["G p", "F q", "G F p", "p U q", "G(p -> X q)"]:
            formula = parse_ltl(text)
            lasso = buchi_lasso(ltl_to_buchi(formula, letters))
            assert lasso is not None, text
            prefix, loop = lasso.word()
            assert loop, text  # a lasso needs a non-empty cycle
            assert satisfies(prefix + loop, formula, lasso_from=len(prefix)), text

    def test_an_unsatisfiable_formula_is_empty(self):
        letters = alphabet_of(["p"])
        assert buchi_is_empty(ltl_to_buchi(parse_ltl("false"), letters))
        assert buchi_is_empty(ltl_to_buchi(parse_ltl("p & !p"), letters))

    def test_a_satisfiable_formula_is_not(self):
        letters = alphabet_of(["p"])
        assert not buchi_is_empty(ltl_to_buchi(parse_ltl("G p"), letters))


# ======================================================================
# restriction and verification
# ======================================================================


class TestRestrict:
    def test_the_coalition_is_pinned_and_the_others_are_not(self, running_example):
        restricted = restrict(running_example, constant("in", "in"))
        for state in restricted.states:
            assert restricted.available(state, "a") == frozenset({"in"})
            assert restricted.available(state, "b") == frozenset({"in"})
            assert restricted.available(state, "c") == running_example.available(state, "c")

    def test_no_state_becomes_a_dead_end(self, running_example):
        """Unlike VITAMIN's matrix prune, narrowing d(s,i) keeps delta total."""
        restricted = restrict(running_example, constant("in", "in"))
        for state in restricted.states:
            assert restricted.successors(state)

    def test_every_run_of_the_restriction_is_a_complying_run(self, running_example):
        restricted = restrict(running_example, constant("in", "in"))
        for state in restricted.states:
            for profile in restricted.available_profiles(state):
                assert restricted.step(state, profile) == running_example.step(state, profile)

    def test_partial_strategies_are_refused(self, running_example):
        partial = NaturalMemorylessStrategy.build(["a"], {"a": [("p & !q", "in")]})
        with pytest.raises(StrategyError, match="prescribes nothing|no gate"):
            restrict(running_example, partial)

    def test_memory_is_out_of_scope_and_says_so(self, running_example):
        two_bounded = KBoundedStrategy.from_function(
            running_example, ["a"], 2, lambda window, agent: "in"
        )
        with pytest.raises(StrategyError, match="memoryless"):
            restrict(running_example, two_bounded)
        recall = NaturalRecallRegexStrategy.build(["a"], {"a": [(".*", "in")]})
        with pytest.raises(StrategyError, match="memoryless"):
            restrict(running_example, recall)


class TestEnforces:
    def test_needs_no_vitamin(self, running_example, monkeypatch):
        real = builtins.__import__

        def blocked(name, *args, **kwargs):
            if name == "model_checker" or name.startswith("model_checker."):
                raise ImportError("blocked")
            return real(name, *args, **kwargs)

        monkeypatch.setattr(builtins, "__import__", blocked)
        assert enforces(running_example, constant("in", "in"), "G p").holds

    def test_a_winning_strategy_is_accepted(self, running_example):
        verdict = enforces(running_example, constant("in", "in"), "G p")
        assert verdict.holds and bool(verdict)
        # playing 'in' keeps the system in the p-states
        assert set(verdict.reachable) == {"s0", "s1"}

    def test_a_losing_strategy_gives_a_counterexample(self, running_example):
        verdict = enforces(running_example, constant("out", "out"), "G p")
        assert not verdict.holds
        prefix, loop = verdict.counterexample
        run = prefix + loop
        assert run[0] == running_example.initial_state
        # the witness must really violate the goal
        assert any("p" not in running_example.label(state) for state in run)

    def test_the_full_ltl_goal_of_the_paper(self, running_example):
        """Nested X, which VITAMIN's ATL parser cannot even accept."""
        assert enforces(running_example, constant("in", "in"), GOAL).holds
        # out/out goes s0 -> s2 -> s3, and q & Xp holds at s2
        assert enforces(running_example, constant("out", "out"), GOAL).holds
        # idling stays in s2, where q holds but p never follows
        assert not enforces(running_example, constant("idle", "idle"), GOAL).holds

    def test_agrees_with_a_direct_check_on_every_constant_strategy(self, running_example):
        """Cross-check against enumerating the restricted model's own lassos."""
        for x in ("in", "out", "idle"):
            for y in ("in", "out", "idle"):
                strategy = constant(x, y)
                restricted = restrict(running_example, strategy)
                formula = parse_ltl("G p")
                expected = True
                for start, path in _lassos(restricted):
                    word = [restricted.label(s) for s in path]
                    if not satisfies(word, formula, lasso_from=start):
                        expected = False
                        break
                assert enforces(running_example, strategy, "G p").holds is expected, (x, y)

    def test_k_bounded_memoryless_works_too(self, running_example):
        strategy = KBoundedStrategy.memoryless(
            ["a", "b"], {s: {"a": "in", "b": "in"} for s in running_example.states}
        )
        assert enforces(running_example, strategy, "G p").holds


def _lassos(cgs, depth=6):
    """Every (loop start, state path) lasso of the model, up to a bounded depth."""
    found = []
    stack = [[cgs.initial_state]]
    while stack:
        path = stack.pop()
        current = path[-1]
        for position in range(len(path) - 1):
            if path[position] == current:
                found.append((position, path[:-1]))
        if len(path) > depth:
            continue
        for successor in cgs.successors(current):
            stack.append(path + [successor])
    return found


# ======================================================================
# the VITAMIN idle workaround
# ======================================================================


@requires_vitamin
class TestRenameIdle:
    def test_renaming_recovers_the_strategy_vitamin_wrongly_rejects(self, running_example):
        from strategy_monitor.vitamin import atl_model_check, natatl_synthesize

        assert atl_model_check(running_example, ["a", "b"], "G p")["satisfied"] is True
        plain = natatl_synthesize(running_example, ["a", "b"], "G p", k=2, rename_idle=False)
        renamed = natatl_synthesize(running_example, ["a", "b"], "G p", k=2)
        assert plain.satisfiable is False
        assert renamed.satisfiable is True
        assert renamed.verified is True
        assert enforces(running_example, renamed.strategy, "G p").holds

    def test_renaming_alone_can_be_wrong_and_verification_catches_it(self, hard_model):
        """Uncovered states lose their idle self-loop and become dead ends.

        At k = 1 the only gates are single atoms, so no *total* natural strategy
        wins: 'p' cannot tell s0 from s1, and 'q' leaves s1 uncovered.  With idle
        renamed, VITAMIN empties s1's row and AG p holds there vacuously, so it
        reports the partial strategy as winning.  The exact check rejects it.
        """
        from strategy_monitor.vitamin import natatl_synthesize

        unverified = natatl_synthesize(
            hard_model, ["a"], "G p", k=1, rename_idle=True, verify=False
        )
        assert unverified.satisfiable is True  # VITAMIN is fooled
        assert not enforces(hard_model, unverified.strategy, "G p").holds

        guarded = natatl_synthesize(hard_model, ["a"], "G p", k=1, rename_idle=True)
        assert guarded.satisfiable is False  # and we do not pass it on
        assert guarded.verified is False
        assert "counterexample" in guarded.note

    def test_verification_is_on_by_default(self, running_example):
        from strategy_monitor.vitamin import natatl_synthesize

        result = natatl_synthesize(running_example, ["a"], "G(p || q)", k=2)
        assert result.satisfiable is True
        assert result.verified is True

    def test_renaming_is_refused_when_it_would_change_nothing(self, running_example):
        from strategy_monitor.vitamin import VitaminExportError, build_token_map

        with pytest.raises(VitaminExportError, match="changes nothing"):
            build_token_map(running_example, rename_idle="IDLE")
        with pytest.raises(VitaminExportError, match="changes nothing"):
            build_token_map(running_example, rename_idle="I")

    def test_renaming_is_refused_when_the_name_is_taken(self, running_example):
        from strategy_monitor.vitamin import VitaminExportError, build_token_map

        with pytest.raises(VitaminExportError, match="already has an action"):
            build_token_map(running_example, rename_idle="in")

    def test_the_exported_token_actually_changes(self, running_example):
        from strategy_monitor.vitamin import to_vitamin_text

        default = to_vitamin_text(running_example)
        renamed = to_vitamin_text(running_example, rename_idle=True)
        assert "IDLE" in default
        assert "IDLE" not in renamed
        assert "NOOP" in renamed

    def test_the_witness_comes_back_in_the_models_own_action_names(self, running_example):
        from strategy_monitor.vitamin import natatl_synthesize

        result = natatl_synthesize(running_example, ["a", "b"], "G p", k=2, rename_idle=True)
        assert result.strategy is not None
        for pairs in result.strategy.rules.values():
            for _, action in pairs:
                assert action in running_example.actions["a"], action
                assert action != "NOOP"


    def test_renaming_can_empty_the_pruned_model_entirely(self, running_example):
        """The sharpest form: renaming can leave VITAMIN nothing to check.

        VITAMIN matches the prescribed action against the *exported* token.  A
        strategy that prescribes idle no longer matches once idle is renamed, so
        even a covered state's row is emptied -- and an empty model satisfies
        every universally quantified CTL formula vacuously.  Pinned here because
        it is the reason renaming is a candidate-generator, not a verdict.
        """
        import copy
        import os
        import tempfile

        from model_checker.algorithms.explicit.CTL.CTL import model_checking as ctl
        from model_checker.algorithms.explicit.NatATL.Memoryless.pruning import (
            process_transition_matrix_data_fixed,
        )
        from model_checker.parsers.game_structures.cgs.cgs import CGS as VitaminCGS

        from strategy_monitor.vitamin import write_vitamin_model

        def prune(pairs, rename):
            handle, path = tempfile.mkstemp(suffix=".txt")
            os.close(handle)
            try:
                write_vitamin_model(running_example, path, rename_idle=rename)
                parsed = VitaminCGS()
                parsed.read_file(path)
                pruned = process_transition_matrix_data_fixed(
                    parsed, path, [1, 2],
                    {"condition_action_pairs": pairs},
                    {"condition_action_pairs": pairs},
                )
                surviving = sum(1 for row in pruned for cell in row if cell not in (0, "0"))
                model = copy.deepcopy(parsed)
                model.graph = pruned
                verdict = ctl("A G p", path, preloaded_model=model).get("initial_state", "")
                return surviving, "True" in verdict
            finally:
                if os.path.exists(path):
                    os.unlink(path)

        # a strategy that never prescribes idle: renaming does what it promises
        surviving, holds = prune([("p", "in")], True)
        assert surviving > 0
        assert holds is True

        # a strategy that prescribes idle: every row is emptied ...
        surviving, holds = prune([("p", "idle")], True)
        assert surviving == 0
        # ... and VITAMIN still says the objective holds, on nothing at all
        assert holds is True

    def test_renaming_without_verification_is_warned_about(self, running_example, caplog):
        import logging

        from strategy_monitor.vitamin import natatl_synthesize

        with caplog.at_level(logging.WARNING, logger="strategy_monitor.vitamin"):
            natatl_synthesize(
                running_example, ["a"], "G(p || q)", k=1, rename_idle=True, verify=False
            )
        assert any("not trustworthy" in record.message for record in caplog.records)

    def test_the_repair_synthesiser_accepts_the_option(self, running_example):
        from strategy_monitor.repair import RepairOutcome, RepairPipeline, vitamin_synthesiser

        strategy = NaturalMemorylessStrategy.build(
            ["a", "b"], {"a": [("true", "in")], "b": [("true", "in")]}
        )
        pipeline = RepairPipeline(
            cgs=running_example,
            strategy=strategy,
            synthesiser=vitamin_synthesiser("G p", k=2, rename_idle=True),
        )
        # a deviates; {b} alone cannot hold G p, so repair still fails -- but for
        # the right reason, having actually searched
        outcome = pipeline.observe("s0", ("out", "in", "in"))
        assert outcome in (RepairOutcome.COALITION_REPAIRED, RepairOutcome.FAILED)


@requires_vitamin
class TestNoIdleAction:
    """A model with no idle action at all -- the other way to dodge the prune."""

    @staticmethod
    def _no_idle_running(running_example):
        import itertools

        return CGS.from_dict(
            {
                "ap": list(running_example.ap),
                "agents": list(running_example.agents),
                "actions": {a: ["in", "out"] for a in running_example.agents},
                "initial_state": running_example.initial_state,
                "states": [
                    {
                        "id": state,
                        "labels": sorted(running_example.label(state)),
                        "transitions": [
                            {"to": running_example.step(state, profile), "profiles": [list(profile)]}
                            for profile in itertools.product(["in", "out"], repeat=3)
                        ],
                    }
                    for state in running_example.states
                ],
            }
        )

    @staticmethod
    def _partial_and_reachable():
        """s0 needs x, s1 needs y; at k=1 only the partial '(q, x)' is left."""
        return CGS.from_dict(
            {
                "ap": ["p", "q"],
                "agents": ["a"],
                "actions": {"a": ["x", "y"]},
                "initial_state": "s0",
                "states": [
                    {
                        "id": "s0",
                        "labels": ["p", "q"],
                        "transitions": [
                            {"to": "s1", "profiles": [["x"]]},
                            {"to": "s2", "profiles": [["y"]]},
                        ],
                    },
                    {
                        "id": "s1",
                        "labels": ["p"],
                        "transitions": [
                            {"to": "s1", "profiles": [["y"]]},
                            {"to": "s2", "profiles": [["x"]]},
                        ],
                    },
                    {"id": "s2", "labels": [], "transitions": [{"to": "s2", "profiles": [["*"]]}]},
                ],
            }
        )

    def test_removing_idle_fixes_the_false_negatives(self, running_example):
        """With no idle token in the matrix, the prune on covered states is exact."""
        from strategy_monitor.vitamin import atl_model_check, natatl_synthesize

        model = self._no_idle_running(running_example)
        assert atl_model_check(model, ["a", "b"], "G p")["satisfied"] is True
        # run natively the original model reports unsatisfiable; this one does not
        assert (
            natatl_synthesize(
                running_example, ["a", "b"], "G p", k=2, rename_idle=False
            ).satisfiable
            is False
        )
        recovered = natatl_synthesize(model, ["a", "b"], "G p", k=2)
        assert recovered.satisfiable is True
        assert recovered.verified is True
        assert enforces(model, recovered.strategy, "G p").holds

    def test_but_uncovered_states_are_still_read_as_dead_ends(self):
        """Removing idle does not fix the other direction: the prune keeps too little.

        VITAMIN prunes an uncovered state with action "I"; with no idle token
        that row empties, the state becomes a dead end, and the objective holds
        there vacuously.  The exact check rejects the witness.
        """
        from strategy_monitor.vitamin import atl_model_check, natatl_synthesize

        model = self._partial_and_reachable()
        assert atl_model_check(model, ["a"], "G p")["satisfied"] is True
        result = natatl_synthesize(model, ["a"], "G p", k=1)
        assert result.satisfiable is False
        assert result.verified is False
        assert "not a total strategy" in result.note

        # unguarded, VITAMIN does accept the partial witness
        unguarded = natatl_synthesize(model, ["a"], "G p", k=1, verify=False)
        assert unguarded.satisfiable is True
        assert unguarded.strategy.action_for("a", frozenset({"p"})) is None  # silent at s1


class TestPartialStrategies:
    """A gate list silent only where the strategy cannot go is still usable."""

    def test_unreachable_gaps_are_accepted(self, running_example):
        """'(p, in)' says nothing about s2, but playing 'in' never reaches s2."""
        strategy = NaturalMemorylessStrategy.build(["c"], {"c": [("p", "in")]})
        assert strategy.action_for("c", running_example.label("s2")) is None
        verdict = enforces(running_example, strategy, "G p")
        assert verdict.holds
        assert "s2" not in verdict.reachable

    def test_reachable_gaps_are_refused(self, running_example):
        """'(q, in)' says nothing about s1, which playing 'in' does reach."""
        strategy = NaturalMemorylessStrategy.build(["a", "b"], {
            "a": [("q", "in")], "b": [("q", "in")]
        })
        with pytest.raises(StrategyError, match="prescribes nothing in 's1'"):
            enforces(running_example, strategy, "G p")

    def test_unreachable_entries_are_filled_so_delta_stays_total(self, running_example):
        from strategy_monitor.verify import prescribed_actions

        strategy = NaturalMemorylessStrategy.build(["c"], {"c": [("p", "in")]})
        table = prescribed_actions(running_example, strategy)
        assert set(table) == set(running_example.states)
        assert table["s2"]["c"] in running_example.available("s2", "c")
        restricted = restrict(running_example, strategy)
        for state in restricted.states:
            assert restricted.successors(state)
