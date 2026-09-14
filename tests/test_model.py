"""The CGS of Definition 1, traces, Boolean gates and regular expressions."""

import itertools

import pytest

from strategy_monitor.boolean import Top, parse_gate
from strategy_monitor.cgs import CGS, CGSError
from strategy_monitor.ltl import alphabet_of
from strategy_monitor.regex import complexity as regex_complexity
from strategy_monitor.regex import compile_regex_to_dfa, parse_regex
from strategy_monitor.trace import Trace, replay


# -- CGS -----------------------------------------------------------------


class TestCGS:
    def test_running_example_matches_figure_1(self, running_example):
        cgs = running_example
        assert set(cgs.ap) == {"p", "q"}
        assert cgs.agents == ("a", "b", "c")
        assert cgs.states == ("s0", "s1", "s2", "s3")
        assert cgs.initial_state == "s0"
        assert cgs.actions["c"] == ("in", "out")
        assert cgs.label("s0") == frozenset({"p", "q"})
        assert cgs.label("s1") == frozenset({"p"})
        assert cgs.label("s2") == frozenset({"q"})
        assert cgs.label("s3") == frozenset({"p"})

    def test_delta_is_total_and_deterministic(self, running_example):
        cgs = running_example
        for state in cgs.states:
            profiles = list(cgs.available_profiles(state))
            # |act_a| * |act_b| * |act_c| = 3 * 3 * 2
            assert len(profiles) == 18
            for profile in profiles:
                assert cgs.step(state, profile) in cgs.states

    def test_transitions_match_the_drawn_edges(self, running_example):
        cgs = running_example
        # s0: (*,*,in) self-loops; c = out splits between s1 and s2
        assert cgs.step("s0", ("in", "in", "in")) == "s0"
        assert cgs.step("s0", ("idle", "idle", "in")) == "s0"
        for profile in [("in", "in", "out"), ("in", "out", "out"), ("out", "in", "out")]:
            assert cgs.step("s0", profile) == "s1"
        for profile in [("out", "out", "out"), ("idle", "in", "out"), ("in", "idle", "out")]:
            assert cgs.step("s0", profile) == "s2"
        # s1 and s3 are absorbing
        for profile in cgs.available_profiles("s1"):
            assert cgs.step("s1", profile) == "s1"
        for profile in cgs.available_profiles("s3"):
            assert cgs.step("s3", profile) == "s3"
        # s2 leaves only when neither a nor b idles and they do not both play in
        assert cgs.step("s2", ("in", "in", "in")) == "s2"
        assert cgs.step("s2", ("idle", "out", "in")) == "s2"
        assert cgs.step("s2", ("out", "out", "in")) == "s3"
        assert cgs.step("s2", ("in", "out", "out")) == "s3"

    def test_successor_relation_matches_the_kripke_view(self, running_example):
        cgs = running_example
        assert cgs.successors("s0") == frozenset({"s0", "s1", "s2"})
        assert cgs.successors("s1") == frozenset({"s1"})
        assert cgs.successors("s2") == frozenset({"s2", "s3"})
        assert cgs.successors("s3") == frozenset({"s3"})
        assert cgs.reachable_states() == frozenset({"s0", "s1", "s2", "s3"})

    def test_revised_example_only_differs_at_s1(self, running_example, revised_example):
        assert revised_example.successors("s1") == frozenset({"s1", "s2"})
        assert revised_example.step("s1", ("out", "in", "in")) == "s2"
        assert revised_example.step("s1", ("in", "in", "in")) == "s1"
        for state in ("s0", "s2", "s3"):
            for profile in running_example.available_profiles(state):
                assert running_example.step(state, profile) == revised_example.step(state, profile)

    def test_first_matching_rule_wins(self):
        cgs = CGS.from_dict(
            {
                "ap": ["p"],
                "agents": ["a"],
                "actions": {"a": ["x", "y"]},
                "initial_state": "s0",
                "states": [
                    {
                        "id": "s0",
                        "labels": ["p"],
                        "transitions": [
                            {"to": "s0", "profiles": [["x"]]},
                            {"to": "s1", "profiles": [["*"]]},
                        ],
                    },
                    {"id": "s1", "labels": [], "transitions": [{"to": "s1", "profiles": [["*"]]}]},
                ],
            }
        )
        assert cgs.step("s0", ("x",)) == "s0"
        assert cgs.step("s0", ("y",)) == "s1"

    def test_partial_delta_is_rejected(self):
        with pytest.raises(CGSError, match="not total"):
            CGS.from_dict(
                {
                    "ap": [],
                    "agents": ["a"],
                    "actions": {"a": ["x", "y"]},
                    "initial_state": "s0",
                    "states": [
                        {"id": "s0", "labels": [], "transitions": [{"to": "s0", "profiles": [["x"]]}]}
                    ],
                }
            )

    def test_json_round_trip(self, running_example, tmp_path):
        path = tmp_path / "model.json"
        running_example.to_json(str(path))
        reloaded = CGS.from_json(str(path))
        assert reloaded.states == running_example.states
        assert reloaded.initial_state == running_example.initial_state
        for state in running_example.states:
            assert reloaded.label(state) == running_example.label(state)
            for profile in running_example.available_profiles(state):
                assert reloaded.step(state, profile) == running_example.step(state, profile)

    def test_alphabet_is_the_powerset_of_ap(self, running_example):
        letters = running_example.alphabet()
        assert len(letters) == 4
        assert set(letters) == {
            frozenset(),
            frozenset({"p"}),
            frozenset({"q"}),
            frozenset({"p", "q"}),
        }


class TestModelRepairPrimitive:
    """``delta'`` of Section 7.2."""

    def test_redirecting_one_pair_leaves_the_rest_alone(self, running_example):
        updated = running_example.with_transition("s0", ("in", "in", "out"), "s3")
        assert updated.step("s0", ("in", "in", "out")) == "s3"
        for state in running_example.states:
            for profile in running_example.available_profiles(state):
                if (state, profile) == ("s0", ("in", "in", "out")):
                    continue
                assert updated.step(state, profile) == running_example.step(state, profile)
        # the original is untouched
        assert running_example.step("s0", ("in", "in", "out")) == "s1"

    def test_absorbing_an_unknown_state_keeps_delta_total(self, running_example):
        updated = running_example.with_transition("s0", ("in", "in", "out"), "s4")
        assert "s4" in updated.states
        updated.validate()
        assert updated.step("s0", ("in", "in", "out")) == "s4"

    def test_absorbing_an_unknown_action_keeps_delta_total(self, running_example):
        updated = running_example.with_transition("s0", ("panic", "in", "out"), "s2")
        assert "panic" in updated.actions["a"]
        updated.validate()
        assert updated.step("s0", ("panic", "in", "out")) == "s2"


# -- traces ---------------------------------------------------------------


class TestTrace:
    def test_length_follows_the_paper(self, running_example):
        trace = replay(running_example, [("in", "in", "in"), ("in", "in", "out")])
        assert trace.state_projection == ("s0", "s0", "s1")
        assert len(trace.action_projection) == 2
        # |omega| = 2 |omega_alpha| + 1
        assert len(trace) == 2 * len(trace.action_projection) + 1

    def test_a_replayed_trace_conforms_to_the_model(self, running_example):
        trace = replay(running_example, [("in", "in", "out"), ("out", "out", "in")])
        assert trace.check_against(running_example) == []

    def test_wrong_successor_is_reported(self, running_example):
        trace = Trace(states=["s0", "s3"], actions=[("in", "in", "out")])
        problems = trace.check_against(running_example)
        assert len(problems) == 1
        assert "s1" in problems[0] and "s3" in problems[0]

    def test_wrong_initial_state_is_reported(self, running_example):
        assert Trace(states=["s1"]).check_against(running_example)

    def test_action_outside_the_protocol_is_reported(self, running_example):
        trace = Trace(states=["s0"], actions=[("in", "in", "idle")])
        problems = trace.check_against(running_example)
        assert any("d('s0'" in p for p in problems)

    def test_word_is_the_labelling_of_the_states(self, running_example):
        trace = replay(running_example, [("in", "in", "out")])
        assert trace.word(running_example) == (frozenset({"p", "q"}), frozenset({"p"}))


# -- Boolean gates ---------------------------------------------------------


class TestGates:
    @pytest.mark.parametrize(
        "text,valuation,expected",
        [
            ("p", {"p"}, True),
            ("p", {"q"}, False),
            ("!p", {"q"}, True),
            ("p & q", {"p", "q"}, True),
            ("p && q", {"p"}, False),
            ("p | q", {"q"}, True),
            ("p or q", set(), False),
            ("p -> q", {"p"}, False),
            ("p -> q", {"p", "q"}, True),
            ("p -> q", set(), True),
            ("true", set(), True),
            ("false", {"p"}, False),
            ("(p & !q) | r", {"r"}, True),
            ("(p & !q) | r", {"p", "q"}, False),
        ],
    )
    def test_evaluation(self, text, valuation, expected):
        assert parse_gate(text).evaluate(frozenset(valuation)) is expected

    def test_empty_and_star_are_top(self):
        assert isinstance(parse_gate(""), Top)
        assert isinstance(parse_gate("*"), Top)

    def test_complexity_counts_variable_occurrences(self):
        # |phi| of Section 5.3
        assert parse_gate("p").complexity == 1
        assert parse_gate("!p").complexity == 1
        assert parse_gate("p & q").complexity == 2
        assert parse_gate("p & p").complexity == 2
        assert parse_gate("true").complexity == 0

    def test_and_binds_tighter_than_or(self):
        gate = parse_gate("p | q & r")
        assert gate.evaluate(frozenset({"p"})) is True
        assert gate.evaluate(frozenset({"q"})) is False
        assert gate.evaluate(frozenset({"q", "r"})) is True


# -- regular expressions over Bool(Ap) ------------------------------------


class TestDeepGates:
    """Gates deeper than the interpreter's stack.

    A gate is a binary tree, so a wide conjunction is a deep tree: past roughly
    800 terms every recursive traversal overflows.  These pin the three that a
    caller can reach.
    """

    @staticmethod
    def wide(width):
        return parse_gate(" & ".join("(p0 | !p1)" for _ in range(width)))

    @pytest.mark.parametrize("width", [1, 8, 800, 4096])
    def test_every_traversal_survives(self, width):
        gate = self.wide(width)
        assert gate.evaluate(frozenset(["p0"])) is True
        assert gate.evaluate(frozenset(["p1"])) is False
        assert gate.complexity == 2 * width
        assert len(str(gate)) > width

    def test_fallback_agrees_with_recursion(self):
        """The iterative walkers must not merely avoid crashing."""
        from strategy_monitor.boolean import _evaluate_iteratively, _render_iteratively

        for width in (1, 3, 17):
            gate = self.wide(width)
            for valuation in (frozenset(), frozenset(["p0"]), frozenset(["p0", "p1"])):
                assert _evaluate_iteratively(gate, valuation) == gate.evaluate(valuation)
            assert _render_iteratively(gate) == str(gate)

    def test_variables_keeps_left_to_right_order(self):
        gate = parse_gate("(a & b) | !c")
        assert gate.variables() == ["a", "b", "c"]

    def test_fallback_stays_linear(self):
        """Disjoint subtrees, so the deep path must not become quadratic."""
        import time

        timings = []
        for width in (4000, 8000, 16000):
            gate = self.wide(width)
            start = time.perf_counter()
            gate.evaluate(frozenset(["p0"]))
            timings.append(time.perf_counter() - start)
        # doubling the width must not quadruple the time
        assert timings[2] / timings[1] < 3.0, timings


class TestRegex:
    def test_complexity_follows_the_paper(self):
        # ||top* r|| = ||r||, ||top*|| = 1, ||r|| = |r|
        assert regex_complexity(".*") == 1
        assert regex_complexity(".*[p]") == 1
        assert regex_complexity(".*[p][q]") == 2
        assert regex_complexity("[p][q]") == 2

    def test_dot_star_matches_everything(self):
        letters = alphabet_of(["p"])
        dfa = compile_regex_to_dfa(".*", letters)
        for length in range(4):
            for word in itertools.product(letters, repeat=length):
                assert dfa.accepts(word)

    def test_gate_atoms_constrain_letters(self):
        letters = alphabet_of(["p", "q"])
        dfa = compile_regex_to_dfa(".*[q & !p]", letters)
        assert dfa.accepts([frozenset({"q"})])
        assert not dfa.accepts([frozenset({"p", "q"})])
        assert dfa.accepts([frozenset({"p"}), frozenset({"q"})])
        assert not dfa.accepts([frozenset({"q"}), frozenset({"p"})])

    def test_alternation_and_closures(self):
        letters = alphabet_of(["p"])
        empty, p = frozenset(), frozenset({"p"})
        dfa = compile_regex_to_dfa("([p]|[!p])+", letters)
        assert not dfa.accepts([])
        assert dfa.accepts([p])
        assert dfa.accepts([empty, p, empty])

        optional = compile_regex_to_dfa("[p]?[p]", letters)
        assert optional.accepts([p])
        assert optional.accepts([p, p])
        assert not optional.accepts([p, p, p])

    def test_ever_seen_q_idiom(self):
        letters = alphabet_of(["p", "q"])
        dfa = compile_regex_to_dfa(".*[q].*", letters)
        assert not dfa.accepts([frozenset({"p"})])
        assert dfa.accepts([frozenset({"q"})])
        assert dfa.accepts([frozenset({"p"}), frozenset({"q"}), frozenset({"p"})])

    def test_parse_round_trip_is_stable(self):
        for text in [".*", "[p][q]", "([p]|[q])*", ".*[p & q].*"]:
            once = parse_regex(text)
            assert parse_regex(str(once)) == parse_regex(str(parse_regex(str(once))))
