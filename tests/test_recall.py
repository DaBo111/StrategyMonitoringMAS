"""Natural strategies with recall: the regex form and the two monitor engines.

Section 5.3 specifies a recall strategy as a priority-ordered sequence of
``(regex, action)`` pairs; Section 5.5 monitors it after translating to DFSTs.
Both representations are first class here, and the monitor may either

* determinise at construction, giving the product DFST of Proposition 5 and an
  ``O(|A|)`` step, at the cost of a table that can be exponential;
* keep the Thompson NFAs and simulate them, paying per step instead; or
* determinise lazily, materialising only the product states the run reaches.

The central property is that the three engines are indistinguishable: on every
history they prescribe the same actions, and all agree with the direct matching
semantics of :func:`strategy_monitor.regex.matches`.
"""

import itertools
import random

import pytest

from strategy_monitor.automata import NFASimulator, determinize
from strategy_monitor.cgs import CGS
from strategy_monitor.ltl import alphabet_of
from strategy_monitor.monitors import (
    RECALL_ENGINES,
    LazyProductEngine,
    NaturalRecallMonitor,
    ProductDFSTEngine,
    RegexNFAEngine,
    resolve_recall_engine,
)
from strategy_monitor.regex import matches, regex_to_nfa
from strategy_monitor.strategies import (
    NaturalRecallRegexStrategy,
    NaturalRecallStrategy,
    StrategyError,
    strategy_from_dict,
    strategy_to_dict,
)
from strategy_monitor.suite import MonitorSuite
from strategy_monitor.trace import replay
from strategy_monitor.verdict import Verdict

SEQUENCES = {
    "ever seen q": [(".*[q].*", "out"), (".*", "in")],
    "first step only": [("[true]", "in"), (".*", "out")],
    "p then q": [(".*[p][q]", "out"), (".*", "in")],
    "alternating": [("([p][!p])*", "in"), (".*", "out")],
    "two ago": [(".*[q]..", "out"), (".*[p]", "in"), (".*", "idle")],
    "odd length": [("(..)*[true]", "in"), (".*", "out")],
    # The first regex matches only at step 1, and the second can only answer
    # correctly if it consumed step 1 too -- so this family distinguishes an
    # engine that stops advancing automata once one has matched.
    "prefix sensitive": [("[p]", "one"), ("[p][q]", "two"), (".*", "three")],
}


@pytest.fixture(scope="module")
def letters():
    return alphabet_of(["p", "q"])


ENGINES = (ProductDFSTEngine, RegexNFAEngine, LazyProductEngine)
"""The three ways a recall strategy can be run; they must be indistinguishable."""


def strategy_for(pairs, agents=("a",)):
    return NaturalRecallRegexStrategy.build(list(agents), {a: pairs for a in agents})


# ======================================================================
# the regex-sequence representation
# ======================================================================


class TestRegexSequenceStrategy:
    def test_least_index_match_wins(self):
        strategy = strategy_for([(".*[q].*", "out"), (".*", "in")])
        assert strategy.action_for("a", [frozenset({"p", "q"})]) == "out"
        assert strategy.action_for("a", [frozenset({"p"})]) == "in"
        # once q has been seen the first regex keeps matching
        assert strategy.action_for("a", [frozenset({"q"}), frozenset({"p"})]) == "out"

    def test_default_action_when_nothing_matches(self):
        strategy = NaturalRecallRegexStrategy.build(
            ["a"], {"a": [("[p]", "in")]}, default_action={"a": "idle"}
        )
        assert strategy.action_for("a", [frozenset({"p"})]) == "in"
        assert strategy.action_for("a", [frozenset({"q"})]) == "idle"

    def test_no_match_and_no_default_is_undefined(self):
        strategy = strategy_for([("[p]", "in")])
        assert strategy.action_for("a", [frozenset({"q"})]) is None

    def test_complexity_sums_the_regex_measures(self):
        # ||top* r|| = ||r||, so .*[q].* costs 2 and .* costs 1
        strategy = strategy_for([(".*[q].*", "out"), (".*", "in")])
        assert strategy.complexity("a") == 3
        assert strategy.complexity() == 3

    def test_empty_sequence_is_refused(self):
        with pytest.raises(StrategyError, match="empty strategy"):
            NaturalRecallRegexStrategy.build(["a"], {"a": []})

    def test_translation_to_dfsts_is_available(self, letters):
        strategy = strategy_for([(".*[q].*", "out"), (".*", "in")])
        translated = strategy.to_dfst_strategy(letters)
        assert isinstance(translated, NaturalRecallStrategy)
        assert translated.coalition == strategy.coalition
        assert set(translated.transducers) == {"a"}


class TestSerialisation:
    def test_natural_recall_loads_as_the_regex_form(self):
        data = {
            "type": "natural_recall",
            "coalition": ["a"],
            "regexes": {"a": [[".*[q].*", "out"], [".*", "in"]]},
        }
        strategy = strategy_from_dict(data)
        assert isinstance(strategy, NaturalRecallRegexStrategy)
        # no alphabet is needed any more: the regexes are kept, not compiled
        assert strategy.action_for("a", [frozenset({"q"})]) == "out"

    def test_round_trip(self):
        data = {
            "type": "natural_recall",
            "coalition": ["a", "b"],
            "regexes": {
                "a": [[".*[q].*", "out"], [".*", "in"]],
                "b": [[".*", "idle"]],
            },
            "default_action": {"a": "idle"},
        }
        once = strategy_from_dict(data)
        twice = strategy_from_dict(strategy_to_dict(once))
        for word in [[], [frozenset({"q"})], [frozenset({"p"}), frozenset({"q"})]]:
            for agent in ("a", "b"):
                assert once.action_for(agent, word) == twice.action_for(agent, word), (agent, word)

    def test_dfst_form_can_still_be_asked_for(self, letters):
        data = {
            "type": "natural_recall_dfst",
            "coalition": ["a"],
            "regexes": {"a": [[".*[q].*", "out"], [".*", "in"]]},
        }
        assert isinstance(strategy_from_dict(data, letters), NaturalRecallStrategy)


# ======================================================================
# the NFA runtime
# ======================================================================


class TestNFASimulator:
    def test_active_set_is_the_subset_construction_state(self, letters):
        nfa = regex_to_nfa(".*[q].*", letters)
        dfa = determinize(nfa)
        simulator = NFASimulator(nfa)
        state = dfa.initial
        random.seed(11)
        for _ in range(60):
            letter = random.choice(letters)
            accepted = simulator.step(letter)
            state = dfa.step(state, letter)
            assert simulator.live_states == state
            assert accepted is (state in dfa.accepting)

    def test_reset_returns_to_the_initial_set(self, letters):
        simulator = NFASimulator(regex_to_nfa("[p][q]", letters))
        simulator.step(frozenset({"p"}))
        simulator.reset()
        assert simulator.live_states == frozenset(regex_to_nfa("[p][q]", letters).initial)

    def test_a_dead_word_empties_the_active_set(self, letters):
        simulator = NFASimulator(regex_to_nfa("[p][q]", letters))
        assert simulator.step(frozenset({"q"})) is False
        assert simulator.active == 0
        assert simulator.step(frozenset({"q"})) is False


# ======================================================================
# the two engines agree
# ======================================================================


class TestEngineEquivalence:
    @pytest.mark.parametrize("name", sorted(SEQUENCES))
    def test_exhaustively_on_short_words(self, running_example, letters, name):
        """Both engines, and the direct matcher, prescribe the same action."""
        pairs = SEQUENCES[name]
        strategy = strategy_for(pairs)
        for length in range(1, 5):
            for word in itertools.product(letters, repeat=length):
                engines = [build(strategy, letters) for build in ENGINES]
                prescribed = None
                for letter in word:
                    answers = [engine.step(letter) for engine in engines]
                    assert answers[0] == answers[1] == answers[2], (name, word)
                    prescribed = answers[0]
                # ... and all match the reference semantics of Section 5.3
                assert prescribed["a"] == strategy.action_for("a", list(word)), (name, word)

    @pytest.mark.parametrize("name", sorted(SEQUENCES))
    def test_on_random_longer_words(self, letters, name):
        strategy = strategy_for(SEQUENCES[name], agents=("a", "b"))
        random.seed(hash(name) % 9973)
        engines = [build(strategy, letters) for build in ENGINES]
        for step in range(200):
            letter = random.choice(letters)
            answers = [engine.step(letter) for engine in engines]
            assert answers[0] == answers[1] == answers[2], (name, step)

    def test_priority_is_respected_by_both(self, letters):
        """A later regex must not win while an earlier one still matches."""
        strategy = strategy_for([(".*", "first"), (".*", "second")])
        for build in ENGINES:
            assert build(strategy, letters).step(frozenset({"p"}))["a"] == "first"

    def test_lower_priority_automata_keep_consuming(self, letters):
        """The NFA engine must advance every simulator, not stop at the first hit.

        ``[p]`` matches the one-letter word ``{p}`` and wins step 1.  At step 2
        it no longer matches, and the answer is ``two`` only if ``[p][q]`` also
        consumed step 1.  An engine that stopped advancing automata as soon as
        one matched would still be at the start of ``[p][q]``, see only ``{q}``,
        and fall through to ``three``.
        """
        strategy = strategy_for([("[p]", "one"), ("[p][q]", "two"), (".*", "three")])
        word = [frozenset({"p"}), frozenset({"q"})]
        assert strategy.action_for("a", word[:1]) == "one"
        assert strategy.action_for("a", word) == "two"
        for build in ENGINES:
            engine = build(strategy, letters)
            assert engine.step(word[0])["a"] == "one"
            assert engine.step(word[1])["a"] == "two", build.__name__


# ======================================================================
# the monitor
# ======================================================================


class TestRecallMonitorEngines:
    def test_both_engines_give_the_same_verdicts(self, running_example):
        strategy = NaturalRecallRegexStrategy.build(
            ["a", "b"],
            {"a": [(".*[q].*", "out"), (".*", "in")], "b": [(".*[q].*", "out"), (".*", "in")]},
        )
        traces = [
            [("out", "out", "out"), ("out", "out", "in")],
            [("in", "in", "in")],
            [("out", "out", "out"), ("in", "out", "in")],
            [("idle", "idle", "in"), ("out", "out", "in"), ("out", "out", "in")],
        ]
        for actions in traces:
            trace = replay(running_example, actions)
            verdicts = []
            for engine in RECALL_ENGINES:
                monitor = NaturalRecallMonitor(running_example, strategy, determinize=engine)
                verdicts.append(monitor.verdicts(trace))
            assert verdicts[0] == verdicts[1] == verdicts[2], actions

    def test_violations_are_attributed_identically(self, running_example):
        strategy = NaturalRecallRegexStrategy.build(
            ["a", "b"],
            {"a": [(".*[q].*", "out"), (".*", "in")], "b": [(".*", "in")]},
        )
        reports = []
        for engine in RECALL_ENGINES:
            monitor = NaturalRecallMonitor(running_example, strategy, determinize=engine)
            monitor.run(replay(running_example, [("in", "out", "in")]))
            reports.append([(v.agent, v.prescribed, v.observed) for v in monitor.violations])
        assert reports[0] == reports[1] == reports[2]
        assert reports[0] == [("a", "out", "in"), ("b", "in", "out")]

    def test_engine_is_reported(self, running_example):
        strategy = strategy_for([(".*", "in")])
        expected = {
            "dfa": "product DFST",
            "nfa": "NFA simulation",
            "lazy": "lazy determinisation",
        }
        for engine, text in expected.items():
            monitor = NaturalRecallMonitor(running_example, strategy, determinize=engine)
            assert text in monitor.describe(), engine
            assert monitor.engine_name == engine

    def test_boolean_aliases(self, running_example):
        strategy = strategy_for([(".*", "in")])
        assert NaturalRecallMonitor(running_example, strategy, determinize=True).engine_name == "dfa"
        assert (
            NaturalRecallMonitor(running_example, strategy, determinize=False).engine_name == "nfa"
        )
        assert resolve_recall_engine(True) == "dfa"
        assert resolve_recall_engine("lazy") == "lazy"
        with pytest.raises(StrategyError, match="unknown recall engine"):
            resolve_recall_engine("subset")

    def test_dfst_strategy_refuses_the_nfa_engine(self, running_example, letters):
        """There is no NFA left to simulate once the strategy is a transducer."""
        dfst_strategy = strategy_for([(".*", "in")]).to_dfst_strategy(letters)
        NaturalRecallMonitor(running_example, dfst_strategy, determinize="dfa")  # fine
        for engine in ("nfa", "lazy"):
            with pytest.raises(StrategyError, match="no NFA left to simulate"):
                NaturalRecallMonitor(running_example, dfst_strategy, determinize=engine)

    def test_missing_catch_all_fails_eagerly_when_determinised(self, running_example):
        """The two engines differ in *when* an incomplete strategy is reported."""
        strategy = strategy_for([("[p & !q]", "in")])
        # determinising explores every reachable product state, so it raises now
        with pytest.raises(StrategyError, match="no regex"):
            NaturalRecallMonitor(running_example, strategy, determinize=True)
        # the other two only discover it when such a history actually occurs
        for engine in ("nfa", "lazy"):
            monitor = NaturalRecallMonitor(running_example, strategy, determinize=engine)
            with pytest.raises(StrategyError, match="no regex"):
                monitor.observe_state("s0")  # pi(s0) = {p,q}, which no regex matches


class TestConstructionCost:
    """The trade the two engines make, on a family that forces the blow-up."""

    @staticmethod
    def family(n):
        # "the (n+1)-th letter from the end satisfies p"
        return strategy_for([(".*[p]" + "." * n, "out"), (".*", "in")])

    @pytest.mark.parametrize("n", [0, 1, 2, 3, 4, 5, 6])
    def test_determinised_is_exponential_and_the_others_are_linear(self, running_example, n):
        strategy = self.family(n)
        determinised = NaturalRecallMonitor(running_example, strategy, determinize="dfa")
        simulated = NaturalRecallMonitor(running_example, strategy, determinize="nfa")
        lazy = NaturalRecallMonitor(running_example, strategy, determinize="lazy")
        assert determinised.size >= 2 ** (n + 1)
        assert simulated.size <= 4 * n + 16
        # lazy builds nothing up front, so its construction cost is the NFAs'
        assert lazy.size == simulated.size
        assert lazy.engine.materialised == 1  # just the initial state

    def test_the_engines_still_agree_on_the_hard_family(self, running_example, letters):
        strategy = self.family(3)
        engines = [build(strategy, letters) for build in ENGINES]
        random.seed(5)
        for _ in range(150):
            letter = random.choice(letters)
            answers = [engine.step(letter) for engine in engines]
            assert answers[0] == answers[1] == answers[2]


class TestLazyDeterminisation:
    """The cache is the fragment of the eager table the run actually visits."""

    def test_only_the_visited_states_are_built(self, letters):
        strategy = strategy_for([(".*[p]..", "out"), (".*", "in")])
        eager = ProductDFSTEngine(strategy, letters)
        lazy = LazyProductEngine(strategy, letters)
        assert lazy.materialised == 1  # nothing built before the run

        # a short run can only reach as many states as it takes steps
        random.seed(3)
        steps = 5
        for _ in range(steps):
            lazy.step(random.choice(letters))
        assert lazy.materialised <= steps + 1
        assert lazy.materialised < eager.size

    def test_the_cache_converges_to_the_eager_automaton(self, letters):
        """Given enough of the language, lazy discovers exactly the eager states."""
        strategy = strategy_for([(".*[p]..", "out"), (".*", "in")])
        eager = ProductDFSTEngine(strategy, letters)
        lazy = LazyProductEngine(strategy, letters)
        random.seed(7)
        for _ in range(400):
            lazy.step(random.choice(letters))
        assert lazy.materialised == eager.size
        # and by then almost every step is a hit rather than fresh work
        assert lazy.hits > lazy.misses * 5

    def test_a_revisited_state_costs_a_lookup(self, letters):
        """Once the run settles into states it has seen, nothing new is computed."""
        strategy = strategy_for([(".*[q].*", "out"), (".*", "in")])
        lazy = LazyProductEngine(strategy, letters)
        letter = frozenset({"q"})
        # a few steps to reach the fixpoint of this letter (the .* prefix
        # saturates after a bounded number of them)
        for _ in range(50):
            lazy.step(letter)
        settled = lazy.misses
        assert settled < 50, "the run should reach a fixpoint, not keep discovering"
        for _ in range(50):
            lazy.step(letter)
        assert lazy.misses == settled  # every further step is served from the cache
        assert lazy.hits >= 50

    def test_cache_entries_agree_with_the_eager_transition(self, letters):
        """Every memoised entry is the transition the eager construction gives."""
        strategy = strategy_for([(".*[p].", "out"), (".*", "in")])
        lazy = LazyProductEngine(strategy, letters)
        eager = ProductDFSTEngine(strategy, letters)
        random.seed(13)
        word = [random.choice(letters) for _ in range(80)]
        for letter in word:
            assert lazy.step(letter) == eager.step(letter)
        # replaying the same word must now be served entirely from the cache
        misses_before = lazy.misses
        lazy.reset()
        for letter in word:
            lazy.step(letter)
        assert lazy.misses == misses_before

    def test_reset_keeps_the_cache(self, letters):
        """The cache is knowledge about the automaton, not about the run."""
        strategy = strategy_for([(".*[q].*", "out"), (".*", "in")])
        lazy = LazyProductEngine(strategy, letters)
        lazy.step(frozenset({"q"}))
        lazy.reset()
        assert lazy.state == lazy.initial
        assert lazy.cache  # not cleared
        assert lazy.materialised >= 2

    def test_summary_is_only_reported_by_the_lazy_engine(self, letters):
        strategy = strategy_for([(".*", "in")])
        assert ProductDFSTEngine(strategy, letters).summary() is None
        assert RegexNFAEngine(strategy, letters).summary() is None
        assert "materialised" in LazyProductEngine(strategy, letters).summary()


# ======================================================================
# composition
# ======================================================================


class TestCompositionAndRepair:
    def test_the_suite_threads_the_engine_choice(self, running_example):
        strategy = strategy_for([(".*", "in")], agents=("a",))
        expected = {
            "dfa": "product DFST",
            "nfa": "NFA simulation",
            "lazy": "lazy determinisation",
            True: "product DFST",
            False: "NFA simulation",
        }
        for determinize, text in expected.items():
            suite = MonitorSuite.build(
                running_example, strategy=strategy, determinize=determinize
            )
            assert text in suite.strategy_monitor.describe(), determinize

    def test_the_suite_accepts_both_representations(self, running_example, letters):
        for strategy in (
            strategy_for([(".*", "in")]),
            strategy_for([(".*", "in")]).to_dfst_strategy(letters),
        ):
            suite = MonitorSuite.build(running_example, strategy=strategy, goal="G(p | q)")
            assert isinstance(suite.strategy_monitor, NaturalRecallMonitor)
            assert suite.goal_monitor is not None

    def test_adherence_is_still_refused_for_recall(self, running_example):
        with pytest.raises(StrategyError, match="recall is left for future work"):
            MonitorSuite.build(
                running_example, strategy=strategy_for([(".*", "in")]), adherence=True
            )

    def test_repair_drives_either_engine(self, running_example):
        from strategy_monitor.repair import RepairOutcome, RepairPipeline, fixed_synthesiser

        strategy = strategy_for([(".*[q].*", "out"), (".*", "in")])
        for engine in RECALL_ENGINES:
            pipeline = RepairPipeline(
                cgs=running_example,
                strategy=strategy,
                synthesiser=fixed_synthesiser(None),
                determinize=engine,
            )
            assert isinstance(pipeline.monitor, NaturalRecallMonitor)
            assert pipeline.monitor.engine_name == engine
            # s0 satisfies q, so 'out' is prescribed and 'in' deviates
            assert pipeline.observe("s0", ("in", "in", "in")) is RepairOutcome.FAILED
