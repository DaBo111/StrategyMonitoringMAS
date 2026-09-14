"""The optional Spot backend.

Spot is not installable on every platform -- it is not on PyPI and has no
Windows build -- so the tests come in two halves:

* :class:`TestSyntax` and :class:`TestConversion` always run.  They drive the
  conversion with a fake Spot whose BDDs are DNF cubes over AP names, which is
  enough to reproduce the two operations the backend performs on a condition:
  conjunction with a minterm, and the test against ``bddfalse``.
* :class:`TestAgainstGPVW` runs only where Spot really is installed, and is the
  point of the whole exercise: an independent check on the GPVW tableau, which
  is otherwise validated only against this package's own ``satisfies`` oracle.
"""

import itertools
import sys

import pytest

from strategy_monitor.automata import Buchi, buchi_is_empty, buchi_product
from strategy_monitor.ltl import alphabet_of, ltl_to_buchi, parse_ltl, satisfies
from strategy_monitor.spot_backend import (
    SpotUnavailable,
    resolve_ltl_backend,
    spot_available,
    spot_ltl_to_buchi,
    to_spot_syntax,
)


# -- a fake Spot ---------------------------------------------------------


class FakeBdd:
    """A condition in DNF: a set of cubes, each ``(positive, negative)``.

    Every cube is kept contradiction-free, so the formula is unsatisfiable
    exactly when there are no cubes -- which is what ``!= bddfalse`` asks.
    Unlike a set of models this needs no fixed variable universe, so the test
    can build conditions before the backend registers its atoms.
    """

    def __init__(self, cubes):
        self.cubes = frozenset(cubes)

    def __and__(self, other):
        product = set()
        for positive, negative in self.cubes:
            for other_positive, other_negative in other.cubes:
                merged_positive = positive | other_positive
                merged_negative = negative | other_negative
                if not (merged_positive & merged_negative):
                    product.add((frozenset(merged_positive), frozenset(merged_negative)))
        return FakeBdd(product)

    def __eq__(self, other):
        return isinstance(other, FakeBdd) and self.cubes == other.cubes

    def __ne__(self, other):
        return not self.__eq__(other)

    def __hash__(self):
        return hash(self.cubes)


def cube(positive=(), negative=()):
    return FakeBdd({(frozenset(positive), frozenset(negative))})


BDD_TRUE = FakeBdd({(frozenset(), frozenset())})
BDD_FALSE = FakeBdd(set())


class FakeBuddy:
    """Stands in for the ``buddy`` module."""

    bddtrue = BDD_TRUE
    bddfalse = BDD_FALSE

    def __init__(self):
        self.names = {}  # index -> AP name, filled in by register_ap

    def bdd_ithvar(self, index):
        return cube(positive=[self.names[index]])

    def bdd_nithvar(self, index):
        return cube(negative=[self.names[index]])


class FakeEdge:
    def __init__(self, src, dst, cond):
        self.src, self.dst, self.cond = src, dst, cond


class FakeAp:
    def __init__(self, name):
        self.name = name

    def ap_name(self):
        return self.name


class FakeAutomaton:
    def __init__(self, states, initial, edges, accepting, ap_names, buddy):
        self._states = states
        self._initial = initial
        self._edges = [FakeEdge(*edge) for edge in edges]
        self._accepting = set(accepting)
        self._ap = list(ap_names)
        self._buddy = buddy
        self._vars = {}
        for name in self._ap:
            self.register_ap(name)

    def num_states(self):
        return self._states

    def get_init_state_number(self):
        return self._initial

    def out(self, source):
        return [edge for edge in self._edges if edge.src == source]

    def state_is_accepting(self, state):
        return state in self._accepting

    def prop_state_acc(self):
        return True

    def ap(self):
        return [FakeAp(name) for name in self._ap]

    def register_ap(self, name):
        if name not in self._vars:
            index = len(self._buddy.names)
            self._vars[name] = index
            self._buddy.names[index] = name
        return self._vars[name]


class FakeSpot:
    """Stands in for the ``spot`` module; hands back a prepared automaton."""

    def __init__(self, automaton):
        self._automaton = automaton
        self.translated = []

    def translate(self, text, *options):
        self.translated.append((text, options))
        return self._automaton

    def sbacc(self, automaton):  # pragma: no cover - prop_state_acc is True
        return automaton

    def version(self):
        return "fake-2.14"


@pytest.fixture
def fake_spot(monkeypatch):
    """Install a fake ``spot``/``buddy`` pair and build automata against it."""

    buddy = FakeBuddy()

    def install(states, initial, edges, accepting, ap_names):
        automaton = FakeAutomaton(states, initial, edges, accepting, ap_names, buddy)
        spot = FakeSpot(automaton)
        monkeypatch.setitem(sys.modules, "spot", spot)
        monkeypatch.setitem(sys.modules, "buddy", buddy)
        return spot

    install.buddy = buddy
    return install


# -- syntax --------------------------------------------------------------


class TestSyntax:
    def test_operators_render(self):
        assert to_spot_syntax(parse_ltl("G p")) == 'G("p")'
        assert to_spot_syntax(parse_ltl("p U q")) == '("p" U "q")'
        assert to_spot_syntax(parse_ltl("p R q")) == '("p" R "q")'
        assert to_spot_syntax(parse_ltl("X p & F q")) == '(X("p") & F("q"))'
        assert to_spot_syntax(parse_ltl("true")) == "1"
        assert to_spot_syntax(parse_ltl("false")) == "0"

    def test_implication_is_already_desugared(self):
        # our parser rewrites -> so Spot never sees it
        assert to_spot_syntax(parse_ltl("p -> q")) == '(!("p") | "q")'

    def test_atoms_are_quoted(self):
        """An atom named like an operator must not reparse as one."""
        assert to_spot_syntax(parse_ltl("G p")) == 'G("p")'
        text = to_spot_syntax(parse_ltl("G untilish"))
        assert text == 'G("untilish")'

    def test_quotes_in_an_atom_are_escaped(self):
        from strategy_monitor.ltl import Atom, Globally

        quote, backslash = chr(34), chr(92)
        rendered = to_spot_syntax(Globally(Atom("a" + quote + "b")))
        assert rendered == "G(" + quote + "a" + backslash + quote + "b" + quote + ")"


# -- conversion ----------------------------------------------------------


class TestConversion:
    def test_self_loop_becomes_one_transition_per_satisfying_letter(self, fake_spot):
        """G p: one accepting state looping on every letter containing p."""
        spot = fake_spot(
            states=1, initial=0, edges=[(0, 0, cube(positive=["p"]))],
            accepting=[0], ap_names=["p"],
        )
        alphabet = alphabet_of(["p", "q"])
        buchi = spot_ltl_to_buchi(parse_ltl("G p"), alphabet)

        assert buchi.states == [0]
        assert buchi.initial == frozenset({0})
        assert buchi.accepting == frozenset({0})
        assert buchi.alphabet == alphabet
        # exactly the two letters containing p, and no others
        assert set(buchi.transitions) == {
            (0, frozenset({"p"})),
            (0, frozenset({"p", "q"})),
        }
        assert buchi.successors(0, frozenset({"p"})) == frozenset({0})
        assert buchi.successors(0, frozenset()) == frozenset()

    def test_negative_literal_selects_the_complement(self, fake_spot):
        fake_spot(
            states=1, initial=0, edges=[(0, 0, cube(negative=["p"]))],
            accepting=[0], ap_names=["p"],
        )
        buchi = spot_ltl_to_buchi(parse_ltl("G !p"), alphabet_of(["p", "q"]))
        assert set(buchi.transitions) == {(0, frozenset()), (0, frozenset({"q"}))}

    def test_true_condition_reaches_every_letter(self, fake_spot):
        fake_spot(states=1, initial=0, edges=[(0, 0, BDD_TRUE)], accepting=[0], ap_names=[])
        alphabet = alphabet_of(["p", "q"])
        buchi = spot_ltl_to_buchi(parse_ltl("true"), alphabet)
        assert len(buchi.transitions) == len(alphabet)

    def test_nondeterminism_is_preserved(self, fake_spot):
        """Two edges on the same letter must merge into one target set."""
        fake_spot(
            states=2, initial=0,
            edges=[(0, 0, cube(positive=["p"])), (0, 1, cube(positive=["p"]))],
            accepting=[1], ap_names=["p"],
        )
        buchi = spot_ltl_to_buchi(parse_ltl("F p"), alphabet_of(["p"]))
        assert buchi.successors(0, frozenset({"p"})) == frozenset({0, 1})

    def test_atom_outside_the_alphabet_is_pinned_false(self, fake_spot):
        """An atom no letter can carry must behave as false, as GPVW does.

        ``ltl_to_buchi("G r", alphabet_of(["p"]))`` is empty under GPVW because
        no letter of ``2^Ap`` contains ``r``; the backend has to agree, or the
        two would differ on formulas mentioning an atom outside ``Ap``.
        """
        fake_spot(
            states=1, initial=0, edges=[(0, 0, cube(positive=["r"]))],
            accepting=[0], ap_names=["r"],
        )
        buchi = spot_ltl_to_buchi(parse_ltl("G r"), alphabet_of(["p"]))
        assert buchi.transitions == {}
        assert buchi_is_empty(buchi)
        # ... which is what the GPVW backend does with the same input
        assert buchi_is_empty(ltl_to_buchi("G r", alphabet_of(["p"])))

    def test_non_accepting_states_stay_non_accepting(self, fake_spot):
        fake_spot(
            states=2, initial=0,
            edges=[(0, 1, BDD_TRUE), (1, 1, BDD_TRUE)],
            accepting=[1], ap_names=[],
        )
        buchi = spot_ltl_to_buchi(parse_ltl("true"), alphabet_of(["p"]))
        assert buchi.accepting == frozenset({1})

    def test_translate_is_asked_for_a_state_based_buchi(self, fake_spot):
        spot = fake_spot(states=1, initial=0, edges=[], accepting=[], ap_names=[])
        spot_ltl_to_buchi(parse_ltl("G p"), alphabet_of(["p"]))
        text, options = spot.translated[0]
        assert text == 'G("p")'
        assert "BA" in options  # state-based acceptance, not transition-based


# -- backend selection ---------------------------------------------------


class TestSelection:
    def test_default_is_gpvw(self, monkeypatch):
        monkeypatch.delenv("STRATEGY_MONITOR_LTL_BACKEND", raising=False)
        assert resolve_ltl_backend() == "gpvw"

    def test_environment_selects(self, monkeypatch):
        monkeypatch.setenv("STRATEGY_MONITOR_LTL_BACKEND", "gpvw")
        assert resolve_ltl_backend() == "gpvw"

    def test_argument_beats_environment(self, monkeypatch):
        monkeypatch.setenv("STRATEGY_MONITOR_LTL_BACKEND", "auto")
        assert resolve_ltl_backend("gpvw") == "gpvw"

    def test_auto_falls_back_quietly(self, monkeypatch):
        monkeypatch.delenv("STRATEGY_MONITOR_LTL_BACKEND", raising=False)
        assert resolve_ltl_backend("auto") in ("gpvw", "spot")

    def test_unknown_backend_is_rejected(self):
        with pytest.raises(ValueError, match="unknown LTL backend"):
            resolve_ltl_backend("spotlight")

    @pytest.mark.skipif(spot_available(), reason="Spot is installed here")
    def test_naming_spot_raises_rather_than_falling_back(self):
        """Asking for Spot by name must never silently give you GPVW."""
        with pytest.raises(SpotUnavailable, match="not on PyPI"):
            resolve_ltl_backend("spot")

    def test_ltl_to_buchi_routes_through_the_fake(self, fake_spot):
        spot = fake_spot(
            states=1, initial=0, edges=[(0, 0, cube(positive=["p"]))],
            accepting=[0], ap_names=["p"],
        )
        buchi = ltl_to_buchi("G p", alphabet_of(["p"]), backend="spot")
        assert spot.translated  # it really went to Spot
        assert buchi.states == [0]


# -- the real thing ------------------------------------------------------

FORMULAS = [
    "G p",
    "F p",
    "p U q",
    "p R q",
    "G(p -> X q)",
    "G F p",
    "F G p",
    "G(p | (q & X p))",
    "!(p U q)",
    "X X p",
    "(G F p) -> (G F q)",
]


def _word_buchi(prefix, cycle, alphabet):
    """A Buchi automaton accepting exactly ``prefix . cycle^omega``."""
    word = list(prefix) + list(cycle)
    transitions = {}
    for index, letter in enumerate(word):
        following = index + 1 if index + 1 < len(word) else len(prefix)
        transitions[(index, letter)] = frozenset({following})
    return Buchi(
        states=list(range(len(word))),
        alphabet=tuple(alphabet),
        transitions=transitions,
        initial=frozenset({0}),
        accepting=frozenset(range(len(word))),
    )


def _accepts(automaton, prefix, cycle, alphabet):
    product = buchi_product(
        automaton, _word_buchi(prefix, cycle, alphabet), right_all_accepting=True
    )
    return not buchi_is_empty(product)


@pytest.mark.skipif(not spot_available(), reason="Spot is not installed")
class TestAgainstGPVW:
    """Differential test: GPVW and Spot must agree, and both must match the oracle."""

    @pytest.mark.parametrize("text", FORMULAS)
    def test_same_language_on_ultimately_periodic_words(self, text):
        alphabet = alphabet_of(["p", "q"])
        formula = parse_ltl(text)
        gpvw = ltl_to_buchi(formula, alphabet, backend="gpvw")
        spot = ltl_to_buchi(formula, alphabet, backend="spot")
        for prefix_length in range(3):
            for prefix in itertools.product(alphabet, repeat=prefix_length):
                for cycle_length in (1, 2):
                    for cycle in itertools.product(alphabet, repeat=cycle_length):
                        expected = satisfies(
                            list(prefix) + list(cycle), formula, lasso_from=len(prefix)
                        )
                        assert _accepts(gpvw, prefix, cycle, alphabet) == expected, (
                            text, prefix, cycle, "gpvw",
                        )
                        assert _accepts(spot, prefix, cycle, alphabet) == expected, (
                            text, prefix, cycle, "spot",
                        )

    @pytest.mark.parametrize("text", FORMULAS)
    def test_spot_is_not_larger(self, text):
        """Not a correctness property -- it records why the backend is worth having."""
        alphabet = alphabet_of(["p", "q"])
        gpvw = ltl_to_buchi(text, alphabet, backend="gpvw")
        spot = ltl_to_buchi(text, alphabet, backend="spot")
        print(
            "{0:<18} gpvw {1:>3} states   spot {2:>3} states".format(
                text, len(gpvw.states), len(spot.states)
            )
        )
        assert len(spot.states) <= len(gpvw.states)

    def test_monitors_agree_verdict_for_verdict(self, running_example, monkeypatch):
        """End to end: the same trace must give the same verdicts either way."""
        from strategy_monitor.goal import GoalMonitor

        traces = [
            # a genuine path of the CGS, so the refined monitor reaches real
            # top^G / bot^G verdicts instead of stopping at bot^M
            ["s0", "s0", "s0", "s2", "s3"],
            # and one that leaves the model at step 2, which is what bot^M is for
            ["s0", "s1", "s0", "s2", "s2"],
        ]
        for trace in traces:
            for use_model in (False, True):
                for text in ("G p", "G(p | (q & X p))", "F q"):
                    runs = []
                    for backend in ("gpvw", "spot"):
                        # GoalMonitor builds its own automata, so the environment
                        # variable is the only way to steer which backend it takes.
                        monkeypatch.setenv("STRATEGY_MONITOR_LTL_BACKEND", backend)
                        monitor = GoalMonitor(running_example, text, use_model=use_model)
                        runs.append([str(monitor.observe_state(st)) for st in trace])
                    assert runs[0] == runs[1], (trace, text, use_model, runs)
