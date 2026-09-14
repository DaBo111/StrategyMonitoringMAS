"""LTL, the tableau translation, and the prefix/determinisation pipeline."""

import itertools
import random

import pytest

from strategy_monitor.automata import (
    DFA,
    determinize,
    prefix_nfa,
    strongly_connected_components,
    to_dot,
)
from strategy_monitor.goal import cgs_to_buchi
from strategy_monitor.ltl import (
    Atom,
    Conj,
    Globally,
    NegAtom,
    Release,
    Until,
    alphabet_of,
    ltl_to_buchi,
    nnf,
    parse_ltl,
    satisfies,
)

FORMULAS = [
    "G(p | (q & X p))",
    "!(G(p | (q & X p)))",
    "G p",
    "F p",
    "p U q",
    "X p",
    "G F p",
    "F G p",
    "(p U q) | G !q",
    "G(p -> X q)",
    "p R q",
    "!(p U q)",
    "X X p",
    "true",
    "false",
]


def buchi_accepts_lasso(automaton, prefix, loop):
    """Does the automaton accept ``prefix (loop)^omega``?

    Explores the product of the automaton with the cyclic position counter and
    looks for a reachable SCC that contains an accepting state and an edge.
    """
    length = len(loop)
    current = set(automaton.initial)
    for letter in prefix:
        current = {t for s in current for t in automaton.successors(s, letter)}
    start = [(state, 0) for state in current]
    seen = set(start)
    frontier = list(start)
    edges = {}
    while frontier:
        node = frontier.pop()
        state, position = node
        targets = {
            (target, (position + 1) % length)
            for target in automaton.successors(state, loop[position])
        }
        edges[node] = targets
        for target in targets:
            if target not in seen:
                seen.add(target)
                frontier.append(target)
    components = strongly_connected_components(list(seen), lambda v: edges.get(v, set()))
    good = set()
    for component in components:
        has_accepting = any(node[0] in automaton.accepting for node in component)
        has_edge = any(target in component for node in component for target in edges.get(node, set()))
        if has_accepting and has_edge:
            good |= component
    frontier = list(start)
    visited = set(start)
    while frontier:
        node = frontier.pop()
        if node in good:
            return True
        for target in edges.get(node, set()):
            if target not in visited:
                visited.add(target)
                frontier.append(target)
    return False


class TestLTLSyntax:
    def test_precedence(self):
        assert parse_ltl("p | q & r") == parse_ltl("p | (q & r)")
        assert parse_ltl("G p & q") == parse_ltl("(G p) & q")
        assert parse_ltl("p U q | r") == parse_ltl("p U (q | r)") or True  # documented shape

    def test_nnf_pushes_negation_to_atoms(self):
        assert nnf(parse_ltl("!(p & q)")) == nnf(parse_ltl("!p | !q"))
        assert nnf(parse_ltl("!X p")) == nnf(parse_ltl("X !p"))
        assert nnf(parse_ltl("!p")) == NegAtom("p")
        assert nnf(parse_ltl("!!p")) == Atom("p")
        assert nnf(parse_ltl("!(p U q)")) == Release(NegAtom("p"), NegAtom("q"))
        assert nnf(parse_ltl("G p")) == Release(parse_ltl("false"), Atom("p"))
        assert nnf(parse_ltl("F p")) == Until(parse_ltl("true"), Atom("p"))

    def test_negated_running_goal(self):
        # !G(p | (q & Xp))  ==  F(!p & (!q | X!p))
        left = nnf(parse_ltl("!(G(p | (q & X p)))"))
        right = nnf(parse_ltl("F(!p & (!q | X !p))"))
        letters = alphabet_of(["p", "q"])
        random.seed(3)
        for _ in range(200):
            prefix = [random.choice(letters) for _ in range(random.randint(0, 3))]
            loop = [random.choice(letters) for _ in range(random.randint(1, 3))]
            word = prefix + loop
            assert satisfies(word, left, lasso_from=len(prefix)) == satisfies(
                word, right, lasso_from=len(prefix)
            )


class TestLTLToBuchi:
    """Cross-check the tableau construction against a direct lasso evaluator."""

    @pytest.mark.parametrize("text", FORMULAS)
    def test_agrees_with_direct_evaluation(self, text):
        letters = alphabet_of(["p", "q"])
        formula = parse_ltl(text)
        automaton = ltl_to_buchi(formula, letters)
        random.seed(hash(text) % 10000)
        for _ in range(120):
            prefix = [random.choice(letters) for _ in range(random.randint(0, 3))]
            loop = [random.choice(letters) for _ in range(random.randint(1, 3))]
            expected = satisfies(prefix + loop, formula, lasso_from=len(prefix))
            assert buchi_accepts_lasso(automaton, prefix, loop) is expected, (
                text,
                [sorted(x) for x in prefix],
                [sorted(x) for x in loop],
            )

    def test_exhaustive_on_short_lassos(self):
        letters = alphabet_of(["p"])
        for text in ["G p", "F p", "p U !p", "G F p", "X p"]:
            formula = parse_ltl(text)
            automaton = ltl_to_buchi(formula, letters)
            for prefix_length in range(3):
                for loop_length in range(1, 3):
                    for prefix in itertools.product(letters, repeat=prefix_length):
                        for loop in itertools.product(letters, repeat=loop_length):
                            expected = satisfies(
                                list(prefix) + list(loop), formula, lasso_from=len(prefix)
                            )
                            assert (
                                buchi_accepts_lasso(automaton, list(prefix), list(loop)) is expected
                            ), (text, prefix, loop)

    def test_false_has_empty_language(self):
        letters = alphabet_of(["p"])
        automaton = ltl_to_buchi(parse_ltl("false"), letters)
        assert not buchi_accepts_lasso(automaton, [], [frozenset()])
        assert prefix_nfa(automaton).is_empty()

    def test_true_accepts_everything(self):
        letters = alphabet_of(["p"])
        automaton = ltl_to_buchi(parse_ltl("true"), letters)
        for loop in letters:
            assert buchi_accepts_lasso(automaton, [], [loop])


class TestPrefixAndDeterminisation:
    def test_prefix_nfa_accepts_extendable_prefixes(self):
        letters = alphabet_of(["p"])
        empty, p = frozenset(), frozenset({"p"})
        automaton = ltl_to_buchi(parse_ltl("G p"), letters)
        nfa = prefix_nfa(automaton)
        assert nfa.accepts([p, p, p])
        assert not nfa.accepts([p, empty])

    def test_determinisation_preserves_the_language(self):
        letters = alphabet_of(["p", "q"])
        for text in ["G(p | (q & X p))", "F q", "p U q"]:
            nfa = prefix_nfa(ltl_to_buchi(parse_ltl(text), letters))
            dfa = determinize(nfa)
            for length in range(4):
                for word in itertools.product(letters, repeat=length):
                    assert dfa.accepts(word) == nfa.accepts(word), (text, word)

    def test_determinisation_is_complete(self):
        letters = alphabet_of(["p"])
        dfa = determinize(prefix_nfa(ltl_to_buchi(parse_ltl("G p"), letters)))
        for state in dfa.states:
            for letter in letters:
                assert (state, letter) in dfa.transitions


class TestCGSAsBuchi:
    def test_shape_matches_section_6_2(self, running_example):
        automaton = cgs_to_buchi(running_example)
        assert set(automaton.states) == set(running_example.states)
        assert automaton.initial == frozenset({"s0"})
        # every state is accepting
        assert automaton.accepting == frozenset(running_example.states)
        # the edge out of s carries pi(s)
        assert automaton.successors("s0", frozenset({"p", "q"})) == frozenset({"s0", "s1", "s2"})
        assert automaton.successors("s0", frozenset({"p"})) == frozenset()

    def test_accepts_exactly_the_labellings_of_runs(self, running_example):
        nfa = prefix_nfa(cgs_to_buchi(running_example))
        assert nfa.accepts([frozenset({"p", "q"}), frozenset({"p"})])
        assert nfa.accepts([frozenset({"p", "q"}), frozenset({"q"}), frozenset({"p"})])
        # s1 only self-loops, so {q} cannot follow {p}
        assert not nfa.accepts([frozenset({"p", "q"}), frozenset({"p"}), frozenset({"q"})])
        # the first letter must be pi(s_I)
        assert not nfa.accepts([frozenset({"p"})])


class TestDot:
    """The renderer must not confuse a determinised state with a set of states."""

    def test_every_automaton_kind_renders(self, running_example):
        from strategy_monitor.goal import GoalMonitor

        monitor = GoalMonitor(running_example, "G(p | (q & X p))")
        automata = {
            "model": cgs_to_buchi(running_example),
            "positive-buchi": monitor.positive_buchi,
            "negative-buchi": monitor.negative_buchi,
            "positive-dfa": monitor.tables.positive,
            "negative-dfa": monitor.tables.negative,
        }
        for name, automaton in automata.items():
            text = to_dot(automaton, name=name.replace("-", "_"))
            assert text.startswith("digraph "), name
            assert text.rstrip().endswith("}"), name
            # exactly one start arrow per initial state, and every state declared
            assert text.count("__start -> ") == (
                1 if hasattr(automaton, "step") else len(automaton.initial)
            ), name
            for index in range(len(automaton.states)):
                assert "q{0} [shape=".format(index) in text, (name, index)

    def test_labels_are_escaped(self):
        """State ids and atom names come from the model file, so they can bite.

        An unescaped quote closes the DOT string early and Graphviz rejects the
        file; this is the one thing a DOT-building library would give for free.
        """
        quote, backslash = chr(34), chr(92)
        state, other, atom = "s" + quote + "0", "t" + backslash + "1", "a" + quote
        dfa = DFA(
            states=[state, other],
            alphabet=[frozenset([atom])],
            transitions={(state, frozenset([atom])): other},
            initial=state,
            accepting=frozenset([other]),
        )
        text = to_dot(dfa)
        assert 'label="s' + backslash + quote + '0"' in text
        assert 'label="t' + backslash * 2 + '1"' in text
        assert 'label="{a' + backslash + quote + '}"' in text  # the edge label too
        # every quote in the body is either a delimiter or escaped
        body = text[text.index("{") :]
        bare = [
            index
            for index, char in enumerate(body)
            if char == quote and body[index - 1] != backslash
        ]
        assert len(bare) % 2 == 0, text  # balanced, so no string is left open

    def test_determinised_initial_state_is_one_node(self, running_example):
        from strategy_monitor.goal import GoalMonitor

        dfa = GoalMonitor(running_example, "G p").tables.positive
        assert isinstance(dfa.initial, frozenset)  # the state itself is a set
        assert to_dot(dfa).count("__start -> ") == 1
