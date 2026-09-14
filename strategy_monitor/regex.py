"""Regular expressions over ``Bool(Ap)`` -- ``Regex(Bool(Ap))`` of Section 5.3.

A natural strategy with recall is a priority-ordered list of
``(regex, action)`` pairs, the regexes ranging over Boolean formulas rather than
plain letters.  This module parses that language and compiles it, via Thompson
construction and the subset construction, into a DFA over ``2^Ap``.

Concrete syntax::

    p                  a one-variable gate
    [p & !q]           any Boolean gate, in brackets
    .                  top -- matches every letter
    r s                concatenation
    r | s              alternation
    r*   r+   r?       the usual closures
    (r)                grouping

So ``.*[q & !p]`` is the paper's ``top^* (q & !p)``: "any history so far, whose
last state satisfies q and not p".

``complexity`` implements ``||r||`` of Section 5.3: ``||top^* r|| = ||r||``,
``||top^*|| = 1``, and ``||r|| = |r|`` otherwise.
"""

from __future__ import annotations

import re
from dataclasses import dataclass
from typing import Dict, FrozenSet, List, Sequence, Set, Tuple

from .automata import DFA, NFA, Letter, determinize
from .boolean import Gate, GateError, Top, parse_gate


class RegexError(ValueError):
    """Raised on a malformed regular expression."""


# -- abstract syntax -----------------------------------------------------


class Regex:
    """A regular expression over ``Bool(Ap)``."""


@dataclass(frozen=True)
class Empty(Regex):
    """The empty word."""

    def __str__(self) -> str:
        return "eps"


@dataclass(frozen=True)
class Symbol(Regex):
    """One letter satisfying a Boolean gate."""

    gate: Gate

    def __str__(self) -> str:
        return "[{0}]".format(self.gate)


@dataclass(frozen=True)
class Concat(Regex):
    left: Regex
    right: Regex

    def __str__(self) -> str:
        return "{0}{1}".format(self.left, self.right)


@dataclass(frozen=True)
class Alt(Regex):
    left: Regex
    right: Regex

    def __str__(self) -> str:
        return "({0}|{1})".format(self.left, self.right)


@dataclass(frozen=True)
class Star(Regex):
    operand: Regex

    def __str__(self) -> str:
        return "{0}*".format(self.operand)


# -- concrete syntax -----------------------------------------------------

_TOKEN = re.compile(
    r"""\s*(?:
          (?P<lparen>\()
        | (?P<rparen>\))
        | (?P<bracket>\[[^\]]*\])
        | (?P<star>\*)
        | (?P<plus>\+)
        | (?P<opt>\?)
        | (?P<alt>\|)
        | (?P<dot>\.)
        | (?P<var>[A-Za-z_][A-Za-z_0-9]*)
        )""",
    re.VERBOSE,
)


def _tokenize(text: str) -> List[Tuple[str, str]]:
    tokens: List[Tuple[str, str]] = []
    position = 0
    while position < len(text):
        if text[position].isspace():
            position += 1
            continue
        match = _TOKEN.match(text, position)
        if match is None or match.end() == position:
            raise RegexError("cannot parse regex {0!r} at offset {1}".format(text, position))
        kind = match.lastgroup
        tokens.append((kind, match.group(kind)))
        position = match.end()
    return tokens


_TOP_WORDS = {"true", "True", "TRUE", "top", "Top", "T"}


class _Parser:
    """alternation < concatenation < postfix < atom."""

    def __init__(self, tokens: Sequence[Tuple[str, str]], source: str) -> None:
        self.tokens = list(tokens)
        self.position = 0
        self.source = source

    def peek(self):
        return self.tokens[self.position] if self.position < len(self.tokens) else None

    def take(self):
        token = self.peek()
        if token is not None:
            self.position += 1
        return token

    def parse(self) -> Regex:
        node = self.alternation()
        if self.position != len(self.tokens):
            raise RegexError("trailing input in regex {0!r}".format(self.source))
        return node

    def alternation(self) -> Regex:
        node = self.concatenation()
        while True:
            token = self.peek()
            if token is None or token[0] != "alt":
                return node
            self.take()
            node = Alt(node, self.concatenation())

    def concatenation(self) -> Regex:
        parts: List[Regex] = []
        while True:
            token = self.peek()
            if token is None or token[0] in ("alt", "rparen"):
                break
            parts.append(self.postfix())
        if not parts:
            return Empty()
        node = parts[0]
        for part in parts[1:]:
            node = Concat(node, part)
        return node

    def postfix(self) -> Regex:
        node = self.atom()
        while True:
            token = self.peek()
            if token is None:
                return node
            if token[0] == "star":
                self.take()
                node = Star(node)
            elif token[0] == "plus":
                self.take()
                node = Concat(node, Star(node))
            elif token[0] == "opt":
                self.take()
                node = Alt(node, Empty())
            else:
                return node

    def atom(self) -> Regex:
        token = self.take()
        if token is None:
            raise RegexError("unexpected end of regex {0!r}".format(self.source))
        kind, text = token
        if kind == "lparen":
            node = self.alternation()
            closing = self.take()
            if closing is None or closing[0] != "rparen":
                raise RegexError("missing ')' in regex {0!r}".format(self.source))
            return node
        if kind == "dot":
            return Symbol(Top())
        if kind == "bracket":
            try:
                return Symbol(parse_gate(text[1:-1]))
            except GateError as error:
                raise RegexError("bad gate in regex {0!r}: {1}".format(self.source, error)) from None
        if kind == "var":
            if text in _TOP_WORDS:
                return Symbol(Top())
            return Symbol(parse_gate(text))
        raise RegexError("unexpected token {0!r} in regex {1!r}".format(text, self.source))


def parse_regex(text: str) -> Regex:
    """Parse a regular expression over ``Bool(Ap)``."""
    return _Parser(_tokenize(text.strip()), text.strip()).parse()


def complexity(pattern) -> int:
    """``||r||`` of Section 5.3.

    ``top^* r`` costs what ``r`` costs -- the "any prefix" idiom is free -- a
    bare ``top^*`` costs 1, and anything else costs its number of symbols.
    """
    node = pattern if isinstance(pattern, Regex) else parse_regex(str(pattern))
    factors = _flatten_concat(node)
    if factors and _is_top_star(factors[0]):
        rest = factors[1:]
        # ||top^*|| = 1, and the "any prefix" idiom is free in front of anything else
        return sum(_symbol_count(f) for f in rest) if rest else 1
    return _symbol_count(node)


def _flatten_concat(node: Regex) -> list:
    """Left-associated concatenation as a flat list of factors."""
    if isinstance(node, Concat):
        return _flatten_concat(node.left) + _flatten_concat(node.right)
    return [node]


def _is_top_star(node: Regex) -> bool:
    return isinstance(node, Star) and isinstance(node.operand, Symbol) and isinstance(
        node.operand.gate, Top
    )


def _symbol_count(node: Regex) -> int:
    if isinstance(node, Symbol):
        return 1
    if isinstance(node, Empty):
        return 0
    if isinstance(node, Star):
        return _symbol_count(node.operand)
    if isinstance(node, (Concat, Alt)):
        return _symbol_count(node.left) + _symbol_count(node.right)
    raise RegexError("unsupported regex node {0!r}".format(node))


# -- compilation ---------------------------------------------------------


class _Thompson:
    """Thompson construction with explicit epsilon edges."""

    def __init__(self, letters: Sequence[Letter]) -> None:
        self.letters = tuple(letters)
        self.counter = 0
        self.moves: Dict[Tuple[int, Letter], Set[int]] = {}
        self.epsilon: Dict[int, Set[int]] = {}
        # Gate-guarded edges, kept alongside the alphabet-expanded moves so the
        # automaton can also be simulated without enumerating 2^Ap.
        self.guards: List[Tuple[int, Gate, int]] = []

    def fresh(self) -> int:
        self.counter += 1
        return self.counter - 1

    def add_move(self, source: int, letter: Letter, target: int) -> None:
        self.moves.setdefault((source, letter), set()).add(target)

    def add_epsilon(self, source: int, target: int) -> None:
        self.epsilon.setdefault(source, set()).add(target)

    def build(self, node: Regex) -> Tuple[int, int]:
        if isinstance(node, Empty):
            start, end = self.fresh(), self.fresh()
            self.add_epsilon(start, end)
            return start, end
        if isinstance(node, Symbol):
            start, end = self.fresh(), self.fresh()
            self.guards.append((start, node.gate, end))
            for letter in self.letters:
                if node.gate.evaluate(letter):
                    self.add_move(start, letter, end)
            return start, end
        if isinstance(node, Concat):
            left_start, left_end = self.build(node.left)
            right_start, right_end = self.build(node.right)
            self.add_epsilon(left_end, right_start)
            return left_start, right_end
        if isinstance(node, Alt):
            start, end = self.fresh(), self.fresh()
            for branch in (node.left, node.right):
                branch_start, branch_end = self.build(branch)
                self.add_epsilon(start, branch_start)
                self.add_epsilon(branch_end, end)
            return start, end
        if isinstance(node, Star):
            start, end = self.fresh(), self.fresh()
            inner_start, inner_end = self.build(node.operand)
            self.add_epsilon(start, inner_start)
            self.add_epsilon(inner_end, end)
            self.add_epsilon(start, end)
            self.add_epsilon(inner_end, inner_start)
            return start, end
        raise RegexError("unsupported regex node {0!r}".format(node))

    def closure(self, states) -> FrozenSet[int]:
        stack = list(states)
        seen = set(states)
        while stack:
            state = stack.pop()
            for target in self.epsilon.get(state, ()):
                if target not in seen:
                    seen.add(target)
                    stack.append(target)
        return frozenset(seen)


def regex_to_nfa(pattern, letters: Sequence[Letter]) -> NFA:
    """Compile a regex over ``Bool(Ap)`` to an epsilon-free NFA over ``2^Ap``."""
    node = pattern if isinstance(pattern, Regex) else parse_regex(str(pattern))
    builder = _Thompson(letters)
    start, end = builder.build(node)
    states = list(range(builder.counter))
    transitions: Dict[Tuple[int, Letter], FrozenSet[int]] = {}
    for state in states:
        for letter in builder.letters:
            targets: Set[int] = set()
            for source in builder.closure({state}):
                targets |= builder.moves.get((source, letter), set())
            if targets:
                transitions[(state, letter)] = builder.closure(targets)
    accepting = frozenset(state for state in states if end in builder.closure({state}))
    return NFA(
        states=states,
        alphabet=tuple(builder.letters),
        transitions=transitions,
        initial=frozenset(builder.closure({start})),
        accepting=accepting,
    )


def compile_regex_to_dfa(pattern, letters: Sequence[Letter]) -> DFA:
    """Compile a regex over ``Bool(Ap)`` to a complete DFA over ``2^Ap``."""
    return determinize(regex_to_nfa(pattern, letters))


def matches(pattern, word: Sequence[Letter]) -> bool:
    """Does ``word`` match the regex?  The reference semantics of Section 5.3.

    Alphabet-free: the Thompson automaton is built with the Boolean gates left
    on its edges and evaluated against each letter as it is read, so this does
    not go through the ``2^Ap`` enumeration the compiled automata use.  That
    makes it an independent check on both the determinised and the simulated
    monitor engines.
    """
    node = pattern if isinstance(pattern, Regex) else parse_regex(str(pattern))
    builder = _Thompson(())
    start, end = builder.build(node)
    current = builder.closure({start})
    for letter in word:
        reached: Set[int] = set()
        for source, gate, target in builder.guards:
            if source in current and gate.evaluate(letter):
                reached.add(target)
        if not reached:
            return False
        current = builder.closure(reached)
    return end in current
