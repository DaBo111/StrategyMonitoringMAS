"""The monitors of Sections 5.2, 5.4, 5.5, 6.1 and 6.2."""

import itertools
import random

import pytest

from strategy_monitor.cgs import CGS
from strategy_monitor.goal import GoalMonitor
from strategy_monitor.ltl import alphabet_of, parse_ltl, satisfies
from strategy_monitor.monitors import (
    AdherenceMonitor,
    KBoundedMonitor,
    NaturalMemorylessMonitor,
    NaturalRecallMonitor,
    WindowIndex,
    model_windows,
    observable_windows,
    reachable_from,
)
from strategy_monitor.strategies import (
    KBoundedStrategy,
    NaturalMemorylessStrategy,
    NaturalRecallStrategy,
    StrategyError,
)
from strategy_monitor.trace import Trace, replay
from strategy_monitor.verdict import Verdict


# ======================================================================
# Section 5.2 -- k-bounded monitors
# ======================================================================


class TestWindowIndex:
    """Proposition 2: the sliding index must agree with direct addressing."""

    @pytest.mark.parametrize("k", [1, 2, 3])
    def test_sliding_matches_direct_address(self, running_example, k):
        index = WindowIndex(running_example, k)
        random.seed(k)
        for _ in range(200):
            index.push(random.choice(running_example.states))
            assert index.value == index.index_of(index.window)
            assert len(index.window) == min(index.length, k)

    @pytest.mark.parametrize("k", [1, 2, 3])
    def test_capacity_is_the_sum_of_powers(self, running_example, k):
        index = WindowIndex(running_example, k)
        size = len(running_example.states)
        assert index.capacity == sum(size ** m for m in range(k + 1))

    def test_offsets_follow_the_paper(self, running_example):
        index = WindowIndex(running_example, 2)
        # o_m = sum_{m' < m} |S|^{m'} with |S| = 4
        assert index.offsets[0] == 0
        assert index.offsets[1] == 1
        assert index.offsets[2] == 5
        assert index.offsets[3] == 21

    @pytest.mark.parametrize("k", [1, 2, 3])
    def test_addresses_are_injective(self, running_example, k):
        index = WindowIndex(running_example, k)
        seen = {}
        for length in range(1, k + 1):
            for window in itertools.product(running_example.states, repeat=length):
                address = index.index_of(window)
                assert address not in seen, (window, seen.get(address))
                assert 0 <= address < index.capacity
                seen[address] = window


class TestKBoundedMonitor:
    def test_paper_example_table(self, running_example, paper_memoryless_strategy):
        paper_memoryless_strategy.validate(running_example)
        assert paper_memoryless_strategy.prescribe(("s0",)) == {"a": "in", "b": "in"}
        assert paper_memoryless_strategy.prescribe(("s3",)) == {"a": "out", "b": "out"}

    def test_compliant_traces_stay_inconclusive(self, running_example, paper_memoryless_strategy):
        # prefixes of {(s0 (in,in,any))^+ (s1 (out,out,any))^*}
        for actions in [
            [("in", "in", "in")],
            [("in", "in", "in"), ("in", "in", "in")],
            [("in", "in", "out"), ("out", "out", "in")],
            [("in", "in", "in"), ("in", "in", "out"), ("out", "out", "out"), ("out", "out", "in")],
        ]:
            monitor = KBoundedMonitor(running_example, paper_memoryless_strategy)
            trace = replay(running_example, actions)
            assert monitor.run(trace) is Verdict.UNKNOWN, trace
            assert monitor.violations == []

    def test_deviation_is_detected_and_attributed(self, running_example, paper_memoryless_strategy):
        monitor = KBoundedMonitor(running_example, paper_memoryless_strategy)
        trace = replay(running_example, [("out", "in", "out")])
        assert monitor.run(trace) is Verdict.BOT
        assert len(monitor.violations) == 1
        violation = monitor.violations[0]
        assert violation.agent == "a"
        assert violation.observed == "out"
        assert violation.prescribed == "in"
        assert violation.state == "s0"

    def test_both_agents_are_reported(self, running_example, paper_memoryless_strategy):
        monitor = KBoundedMonitor(running_example, paper_memoryless_strategy)
        monitor.run(replay(running_example, [("out", "out", "out")]))
        assert {v.agent for v in monitor.violations} == {"a", "b"}

    def test_agents_outside_the_coalition_are_ignored(
        self, running_example, paper_memoryless_strategy
    ):
        monitor = KBoundedMonitor(running_example, paper_memoryless_strategy)
        # c plays whatever it likes
        for c_action in ["in", "out"]:
            monitor = KBoundedMonitor(running_example, paper_memoryless_strategy)
            trace = replay(running_example, [("in", "in", c_action)])
            assert monitor.run(trace) is Verdict.UNKNOWN

    def test_verdict_is_sticky(self, running_example, paper_memoryless_strategy):
        monitor = KBoundedMonitor(running_example, paper_memoryless_strategy)
        monitor.observe("s0", ("out", "out", "out"))
        assert monitor.verdict is Verdict.BOT
        monitor.observe("s2", ("out", "out", "in"))
        assert monitor.verdict is Verdict.BOT

    def test_two_bounded_strategy_uses_the_window(self, running_example):
        # play 'in' iff the previous state was s0
        strategy = KBoundedStrategy.from_function(
            running_example,
            ["a"],
            2,
            lambda window, agent: "in" if window[0] == "s0" else "out",
        )
        monitor = KBoundedMonitor(running_example, strategy)
        monitor.observe("s0", ("in", "in", "out"))  # window (s0,)   -> in
        assert monitor.verdict is Verdict.UNKNOWN
        monitor.observe("s1", ("in", "in", "in"))  # window (s0,s1) -> in
        assert monitor.verdict is Verdict.UNKNOWN
        monitor.observe("s1", ("in", "in", "in"))  # window (s1,s1) -> out
        assert monitor.verdict is Verdict.BOT

    def test_dense_and_sparse_tables_agree(self, running_example):
        strategy = KBoundedStrategy.from_function(
            running_example, ["a"], 2, lambda window, agent: "in"
        )
        actions = [("in", "in", "out"), ("in", "in", "in")]
        dense = KBoundedMonitor(running_example, strategy, dense=True)
        sparse = KBoundedMonitor(running_example, strategy, dense=False)
        trace = replay(running_example, actions)
        assert dense.run(trace) is sparse.run(Trace(list(trace.states), list(trace.actions)))
        assert dense.dense and not sparse.dense

    def test_invalid_strategy_is_rejected(self, running_example):
        bad = KBoundedStrategy.memoryless(["c"], {"s0": {"c": "idle"}})
        with pytest.raises(StrategyError, match="not in d"):
            bad.validate(running_example)


# ======================================================================
# Sections 5.3-5.4 -- natural memoryless
# ======================================================================


class TestNaturalMemoryless:
    def test_algorithm_1_reproduces_the_paper_table(self, running_example, paper_natural_strategy):
        table = paper_natural_strategy.to_kbounded(running_example)
        assert {w[0]: (a["a"], a["b"]) for w, a in table.table.items()} == {
            "s0": ("in", "in"),
            "s1": ("in", "in"),
            "s2": ("out", "out"),
            "s3": ("in", "in"),
        }

    def test_gate_priority(self, paper_natural_strategy):
        # s0 satisfies both p and q, but (p, in) comes first
        assert paper_natural_strategy.action_for("a", frozenset({"p", "q"})) == "in"
        assert paper_natural_strategy.action_for("a", frozenset({"q"})) == "out"
        assert paper_natural_strategy.action_for("a", frozenset()) == "idle"

    def test_complexity_is_the_sum_of_gate_sizes(self, paper_natural_strategy):
        # |p| + |q| + |true| = 1 + 1 + 0
        assert paper_natural_strategy.complexity("a") == 2
        assert paper_natural_strategy.complexity() == 2

    def test_monitor_matches_the_reduced_table(self, running_example, paper_natural_strategy):
        monitor = NaturalMemorylessMonitor(running_example, paper_natural_strategy)
        trace = replay(running_example, [("in", "in", "out"), ("in", "in", "in")])
        assert monitor.run(trace) is Verdict.UNKNOWN

        monitor = NaturalMemorylessMonitor(running_example, paper_natural_strategy)
        trace = replay(running_example, [("in", "in", "out"), ("out", "in", "in")])
        assert monitor.run(trace) is Verdict.BOT
        assert monitor.violations[0].agent == "a"
        assert monitor.violations[0].state == "s1"

    def test_gate_prescribing_an_unavailable_action_is_rejected(self, running_example):
        strategy = NaturalMemorylessStrategy.build(["c"], {"c": [("true", "idle")]})
        with pytest.raises(StrategyError, match="does not allow"):
            strategy.to_kbounded(running_example)

    def test_uncovered_state_is_rejected_in_strict_mode(self, running_example):
        strategy = NaturalMemorylessStrategy.build(["a"], {"a": [("p & !q", "in")]})
        with pytest.raises(StrategyError, match="no gate"):
            strategy.to_kbounded(running_example)
        # non-strict leaves the entry empty, which the monitor reports as a deviation
        table = strategy.to_kbounded(running_example, strict=False)
        assert table.table[("s2",)] == {}


# ======================================================================
# Section 5.5 -- natural strategies with recall
# ======================================================================


class TestNaturalRecall:
    @pytest.fixture
    def ever_seen_q(self, running_example):
        return NaturalRecallStrategy.from_regex_sequences(
            ["a", "b"],
            {
                "a": [(".*[q].*", "out"), (".*", "in")],
                "b": [(".*[q].*", "out"), (".*", "in")],
            },
            alphabet_of(running_example.ap),
        )

    def test_product_dfst_is_deterministic_and_total(self, running_example, ever_seen_q):
        product = ever_seen_q.product(alphabet_of(running_example.ap))
        for state in product.states:
            for letter in product.input_alphabet:
                assert (state, letter) in product.transition
                assert (state, letter) in product.output

    def test_product_state_count_is_within_the_bound(self, running_example, ever_seen_q):
        letters = alphabet_of(running_example.ap)
        product = ever_seen_q.product(letters)
        m = ever_seen_q.complexity()
        # Proposition 5: |S| = prod_a |S^a| <= m^{|A|}
        assert len(product.states) <= m ** len(ever_seen_q.coalition)

    def test_history_changes_the_prescription(self, running_example, ever_seen_q):
        # s0 satisfies q, so 'out' is prescribed from the very first step
        monitor = NaturalRecallMonitor(running_example, ever_seen_q)
        assert monitor.run(replay(running_example, [("in", "in", "in")])) is Verdict.BOT

        monitor = NaturalRecallMonitor(running_example, ever_seen_q)
        assert monitor.run(replay(running_example, [("out", "out", "out")])) is Verdict.UNKNOWN

    def test_recall_really_recalls(self, running_example):
        letters = alphabet_of(running_example.ap)
        strategy = NaturalRecallStrategy.from_regex_sequences(
            ["a"],
            # 'in' only on the very first observation, 'out' afterwards
            {"a": [("[true]", "in"), (".*", "out")]},
            letters,
        )
        monitor = NaturalRecallMonitor(running_example, strategy)
        monitor.observe("s0", ("in", "in", "out"))
        assert monitor.verdict is Verdict.UNKNOWN
        monitor.observe("s1", ("out", "in", "in"))
        assert monitor.verdict is Verdict.UNKNOWN

        monitor = NaturalRecallMonitor(running_example, strategy)
        monitor.observe("s0", ("in", "in", "out"))
        monitor.observe("s1", ("in", "in", "in"))  # 'in' is no longer prescribed
        assert monitor.verdict is Verdict.BOT

    def test_missing_catch_all_is_reported(self, running_example):
        with pytest.raises(StrategyError, match="catch-all"):
            NaturalRecallStrategy.from_regex_sequences(
                ["a"], {"a": [("[p & !q]", "in")]}, alphabet_of(running_example.ap)
            )


# ======================================================================
# Section 6.1 -- strategy-adherence truth
# ======================================================================


class TestAdherenceMonitor:
    """Section 6.1: ``top^S_G`` is relativised to what is still observable."""

    def test_paper_example_reaches_top_s(self, revised_example, adherence_strategy):
        monitor = AdherenceMonitor(revised_example, adherence_strategy)
        trace = replay(
            revised_example,
            [("in", "in", "out"), ("out", "in", "in"), ("out", "out", "in"), ("in", "in", "in")],
        )
        assert trace.state_projection == ("s0", "s1", "s2", "s3", "s3")
        assert monitor.run(trace) is Verdict.TOP_S
        assert monitor.outstanding() == 0

    def test_not_before_everything_reachable_is_validated(self, revised_example, adherence_strategy):
        monitor = AdherenceMonitor(revised_example, adherence_strategy)
        trace = replay(revised_example, [("in", "in", "out"), ("out", "in", "in")])
        assert monitor.run(trace) is Verdict.UNKNOWN
        # s_cur = s2, and W_G(s2) still contains the unvalidated (s2,) and (s3,)
        assert monitor.current_state == "s2"
        assert monitor.pending_from() == [("s2",), ("s3",)]

    def test_absorbing_state_validates_early(self, running_example, paper_memoryless_strategy):
        """A run that enters an absorbing region need not visit the rest.

        In the running example s1 is absorbing, so once s0 and s1 have been
        validated nothing observable is left and the verdict is top^S_G, even
        though s2 and s3 were never seen.  Under an unrelativised reading this
        run could never conclude.
        """
        monitor = AdherenceMonitor(running_example, paper_memoryless_strategy)
        trace = replay(running_example, [("in", "in", "out"), ("out", "out", "in")])
        assert trace.state_projection == ("s0", "s1", "s1")
        assert monitor.run(trace) is Verdict.TOP_S
        assert {w[0] for w in monitor.pending_configurations()} == {"s2", "s3"}
        assert monitor.pending_from("s1") == []

    def test_staying_in_s0_stays_inconclusive(self, running_example, paper_memoryless_strategy):
        monitor = AdherenceMonitor(running_example, paper_memoryless_strategy)
        trace = replay(running_example, [("in", "in", "in")] * 3)
        assert monitor.run(trace) is Verdict.UNKNOWN
        # every state is still reachable from s0
        assert monitor.pending_from("s0") == [("s1",), ("s2",), ("s3",)]

    def test_deviation_beats_adherence(self, revised_example, adherence_strategy):
        monitor = AdherenceMonitor(revised_example, adherence_strategy)
        monitor.observe("s0", ("out", "in", "out"))
        assert monitor.verdict is Verdict.BOT
        # the offending window is not ticked off
        assert ("s0",) in monitor.pending_configurations()

    def test_verdict_test_is_the_counter(self, running_example, paper_memoryless_strategy):
        """The O(1) test of the proof: n[s_cur] == 0."""
        monitor = AdherenceMonitor(running_example, paper_memoryless_strategy)
        assert monitor.outstanding() == len(running_example.states)
        monitor.observe("s0", ("in", "in", "out"))
        assert monitor.outstanding() == 3  # s1, s2, s3 still reachable and unvalidated
        monitor.observe("s1", ("out", "out", "in"))
        assert monitor.outstanding() == 0
        assert monitor.verdict is Verdict.TOP_S

    def test_two_bounded_windows(self, revised_example):
        """With k = 2 the obligations are the length-2 paths of the model."""
        strategy = KBoundedStrategy.from_function(
            revised_example,
            ["a"],
            2,
            lambda window, agent: "in" if window[-1] in ("s0", "s3") else "out",
        )
        monitor = AdherenceMonitor(revised_example, strategy)
        assert monitor.total_obligations == len(model_windows(revised_example, 2))
        trace = replay(
            revised_example,
            [
                ("in", "in", "out"),
                ("out", "in", "in"),
                ("out", "out", "in"),
                ("in", "in", "in"),
                ("in", "in", "in"),
            ],
        )
        assert trace.state_projection == ("s0", "s1", "s2", "s3", "s3", "s3")
        verdicts = []
        for state, action in trace.steps():
            monitor.observe_state(state)
            if action is not None:
                verdicts.append(monitor.observe_action(action))
        # s3 is absorbing, so only (s3,s3) is observable there; it is the last
        # window validated, and the verdict flips exactly then
        assert verdicts[-2] is Verdict.UNKNOWN
        assert verdicts[-1] is Verdict.TOP_S

    def test_shorter_prefixes_are_checked_but_not_obligations(self, revised_example):
        """A run has one prefix of each length l < k, so those cannot be enumerated."""
        strategy = KBoundedStrategy.from_function(
            revised_example, ["a"], 2, lambda window, agent: "in"
        )
        monitor = AdherenceMonitor(revised_example, strategy)
        assert all(len(window) == 2 for window in monitor.obligations)
        # the length-1 prefix is still checked for compliance
        monitor.observe("s0", ("out", "in", "in"))
        assert monitor.verdict is Verdict.BOT


class TestModelWindows:
    def test_only_paths_of_the_model_count(self, running_example):
        """The paper's remark: 7 of the 16 elements of S^2 are paths of G_E."""
        windows = model_windows(running_example, 2)
        assert len(windows) == 7
        assert len(running_example.states) ** 2 == 16
        assert ("s0", "s1") in windows
        assert ("s1", "s0") not in windows  # s1 is absorbing

    def test_length_one_windows_are_the_states(self, running_example):
        assert model_windows(running_example, 1) == {(s,) for s in running_example.states}

    def test_reach_is_reflexive(self, running_example):
        reach = reachable_from(running_example)
        for state in running_example.states:
            assert state in reach[state]
        assert reach["s1"] == frozenset({"s1"})
        assert reach["s2"] == frozenset({"s2", "s3"})
        assert reach["s0"] == frozenset(running_example.states)

    def test_observable_windows_shrink_along_a_run(self, running_example):
        big = observable_windows(running_example, "s0", 2)
        small = observable_windows(running_example, "s1", 2)
        assert small < big
        assert small == {("s1", "s1")}


# ======================================================================
# Section 6.2 -- goal-oriented truth
# ======================================================================


class TestGoalMonitor:
    GOAL = "G(p | (q & X p))"

    def test_paper_example_refines_the_plain_monitor(self, running_example):
        refined = GoalMonitor(running_example, self.GOAL, use_model=True)
        plain = GoalMonitor(running_example, self.GOAL, use_model=False)
        trace = replay(running_example, [("in", "in", "out"), ("in", "in", "in")])
        word = trace.word(running_example)
        assert word == (frozenset({"p", "q"}), frozenset({"p"}), frozenset({"p"}))
        assert plain.evaluate(word) is Verdict.UNKNOWN
        assert refined.evaluate(word) is Verdict.TOP_G

    def test_model_violation_is_detected(self, running_example):
        monitor = GoalMonitor(running_example, self.GOAL)
        # the first letter must be pi(s_I) = {p, q}
        assert monitor.evaluate([frozenset({"p"})]) is Verdict.BOT_M
        # s1 only self-loops in the running example, so {q} cannot follow {p}
        assert (
            monitor.evaluate([frozenset({"p", "q"}), frozenset({"p"}), frozenset({"q"})])
            is Verdict.BOT_M
        )

    def test_goal_violation_is_detected(self, running_example):
        monitor = GoalMonitor(running_example, self.GOAL)
        # s0 -> s2 -> s2: q holds but p does not follow
        assert (
            monitor.evaluate([frozenset({"p", "q"}), frozenset({"q"}), frozenset({"q"})])
            is Verdict.BOT_G
        )

    def test_empty_word_is_inconclusive(self, running_example):
        monitor = GoalMonitor(running_example, self.GOAL)
        assert monitor.evaluate([]) is Verdict.UNKNOWN

    def test_plain_monitor_never_reports_a_model_violation(self, running_example):
        """Without the model product, bot^M is unreachable -- the paper's 'for free'."""
        plain = GoalMonitor(running_example, self.GOAL, use_model=False)
        letters = plain.alphabet
        for length in range(1, 4):
            for word in itertools.product(letters, repeat=length):
                assert plain.evaluate(word) is not Verdict.BOT_M

    def test_verdict_evolution_respects_the_lattice(self, running_example):
        """top^G and bot^G are final except that a model violation supersedes them.

        Both prefix DFAs are monotone: a subset with no accepting member has no
        accepting successor, because "can reach an accepting SCC" is closed
        under predecessors.  So each component of lambda only ever flips from
        in-F to out-of-F, which allows ? -> anything, top^G -> bot^M and
        bot^G -> bot^M, and nothing else.  In particular top^G is *not*
        permanent in the sense of Bauer et al.: it says the goal holds along
        every continuation the model allows, and the system can still leave the
        model afterwards.
        """
        allowed = {
            Verdict.UNKNOWN: {Verdict.UNKNOWN, Verdict.TOP_G, Verdict.BOT_G, Verdict.BOT_M},
            Verdict.TOP_G: {Verdict.TOP_G, Verdict.BOT_M},
            Verdict.BOT_G: {Verdict.BOT_G, Verdict.BOT_M},
            Verdict.BOT_M: {Verdict.BOT_M},
        }
        monitor = GoalMonitor(running_example, self.GOAL)
        letters = monitor.alphabet
        for length in range(1, 5):
            for word in itertools.product(letters, repeat=length):
                monitor.reset()
                seen = [monitor.verdict]
                for letter in word:
                    seen.append(monitor.observe_letter(letter))
                for earlier, later in zip(seen, seen[1:]):
                    assert later in allowed[earlier], (word, seen)

    def test_top_g_can_be_superseded_by_a_model_violation(self, running_example):
        monitor = GoalMonitor(running_example, self.GOAL)
        monitor.reset()
        assert monitor.observe_letter(frozenset({"p", "q"})) is Verdict.UNKNOWN
        assert monitor.observe_letter(frozenset({"p"})) is Verdict.TOP_G
        # s1 only self-loops on {p}; the empty label is not a model behaviour
        assert monitor.observe_letter(frozenset()) is Verdict.BOT_M

    @pytest.mark.parametrize("model_name", ["running_example", "revised_example"])
    def test_semantics_against_a_brute_force_oracle(self, request, model_name):
        """Check lambda against continuations enumerated directly in the model.

        For every word of length <= 3, enumerate the ultimately periodic
        continuations of the model (bounded prefix and loop) and compare the
        verdict with what those continuations say about the goal.
        """
        cgs = request.getfixturevalue(model_name)
        monitor = GoalMonitor(cgs, self.GOAL)
        formula = parse_ltl(self.GOAL)
        letters = monitor.alphabet

        def paths_for(word):
            """States the model can be in after emitting ``word``."""
            current = {cgs.initial_state}
            for letter in word:
                nxt = set()
                for state in current:
                    if cgs.label(state) == letter:
                        nxt |= set(cgs.successors(state))
                current = nxt
                if not current:
                    return set()
            return current

        def continuations(state, depth=5):
            """Lasso continuations from ``state``: (path, loop) label sequences."""
            found = []
            stack = [(state, [])]
            while stack:
                current, path = stack.pop()
                if len(path) > depth:
                    continue
                for loop_start in range(len(path)):
                    if path[loop_start] == current:
                        found.append((path[:loop_start], path[loop_start:]))
                if len(path) < depth:
                    for successor in cgs.successors(current):
                        stack.append((successor, path + [current]))
            return found

        for length in range(0, 4):
            for word in itertools.product(letters, repeat=length):
                reached = paths_for(word)
                verdict = monitor.evaluate(word)
                if not reached:
                    assert verdict is Verdict.BOT_M, word
                    continue
                results = set()
                for state in reached:
                    for path, loop in continuations(state):
                        full = list(word) + [cgs.label(s) for s in path + loop]
                        if not loop:
                            continue
                        results.add(
                            satisfies(full, formula, lasso_from=len(word) + len(path))
                        )
                assert results, (word, reached)
                if results == {True}:
                    assert verdict is Verdict.TOP_G, (word, verdict)
                elif results == {False}:
                    assert verdict is Verdict.BOT_G, (word, verdict)
                else:
                    assert verdict is Verdict.UNKNOWN, (word, verdict)
