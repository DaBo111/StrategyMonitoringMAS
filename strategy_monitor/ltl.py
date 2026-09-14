"""Linear Temporal Logic and its translation to Buchi automata.

Section 4.3 of the paper fixes the grammar

    phi ::= top | p | !phi | phi & phi | X phi | phi U phi

with ``F``, ``G`` and ``|`` derived as usual.  This module parses that grammar,
puts formulas in negation normal form, and translates them to Buchi automata
over the explicit alphabet ``2^Ap`` with the classical on-the-fly tableau
construction of Gerth, Peled, Vardi and Wolper.

The translation is implemented here rather than delegated to Spot so that the
goal-oriented monitor of Section 6.2 runs anywhere Python does; Spot has no
Windows build, and VITAMIN's LTL support is CTL-backed and therefore cannot
supply the automata this construction needs.
"""

from __future__ import annotations

import itertools
import re
from dataclasses import dataclass
from typing import Dict, FrozenSet, Iterable, List, Optional, Sequence, Set, Tuple

from .automata import Buchi, GeneralizedBuchi, Letter


class LTLError(ValueError):
    """Raised on a malformed LTL formula."""


# -- abstract syntax -----------------------------------------------------


class LTL:
    """An LTL formula."""

    def atoms(self) -> Set[str]:
        raise NotImplementedError


@dataclass(frozen=True)
class TrueF(LTL):
    def atoms(self) -> Set[str]:
        return set()

    def __str__(self) -> str:
        return "true"


@dataclass(frozen=True)
class FalseF(LTL):
    def atoms(self) -> Set[str]:
        return set()

    def __str__(self) -> str:
        return "false"


@dataclass(frozen=True)
class Atom(LTL):
    name: str

    def atoms(self) -> Set[str]:
        return {self.name}

    def __str__(self) -> str:
        return self.name


@dataclass(frozen=True)
class NegAtom(LTL):
    """A negated atom; only produced by :func:`nnf`."""

    name: str

    def atoms(self) -> Set[str]:
        return {self.name}

    def __str__(self) -> str:
        return "!" + self.name


@dataclass(frozen=True)
class Neg(LTL):
    operand: LTL

    def atoms(self) -> Set[str]:
        return self.operand.atoms()

    def __str__(self) -> str:
        return "!({0})".format(self.operand)


@dataclass(frozen=True)
class Conj(LTL):
    left: LTL
    right: LTL

    def atoms(self) -> Set[str]:
        return self.left.atoms() | self.right.atoms()

    def __str__(self) -> str:
        return "({0} & {1})".format(self.left, self.right)


@dataclass(frozen=True)
class Disj(LTL):
    left: LTL
    right: LTL

    def atoms(self) -> Set[str]:
        return self.left.atoms() | self.right.atoms()

    def __str__(self) -> str:
        return "({0} | {1})".format(self.left, self.right)


@dataclass(frozen=True)
class Next(LTL):
    operand: LTL

    def atoms(self) -> Set[str]:
        return self.operand.atoms()

    def __str__(self) -> str:
        return "X({0})".format(self.operand)


@dataclass(frozen=True)
class Until(LTL):
    left: LTL
    right: LTL

    def atoms(self) -> Set[str]:
        return self.left.atoms() | self.right.atoms()

    def __str__(self) -> str:
        return "({0} U {1})".format(self.left, self.right)


@dataclass(frozen=True)
class Release(LTL):
    """``phi R psi``, the dual of Until; needed to keep NNF closed."""

    left: LTL
    right: LTL

    def atoms(self) -> Set[str]:
        return self.left.atoms() | self.right.atoms()

    def __str__(self) -> str:
        return "({0} R {1})".format(self.left, self.right)


@dataclass(frozen=True)
class Eventually(LTL):
    operand: LTL

    def atoms(self) -> Set[str]:
        return self.operand.atoms()

    def __str__(self) -> str:
        return "F({0})".format(self.operand)


@dataclass(frozen=True)
class Globally(LTL):
    operand: LTL

    def atoms(self) -> Set[str]:
        return self.operand.atoms()

    def __str__(self) -> str:
        return "G({0})".format(self.operand)


# -- concrete syntax -----------------------------------------------------

_TOKEN = re.compile(
    r"""\s*(?:
          (?P<lparen>\()
        | (?P<rparen>\))
        | (?P<implies>->|=>)
        | (?P<andop>&&|&|/\\|\band\b)
        | (?P<orop>\|\||\||\\/|\bor\b)
        | (?P<notop>!|~|\bnot\b)
        | (?P<true>\btrue\b|\bTrue\b|\btop\b|\bTRUE\b)
        | (?P<false>\bfalse\b|\bFalse\b|\bbot\b|\bFALSE\b)
        | (?P<until>\bU\b|\buntil\b)
        | (?P<release>\bR\b|\brelease\b)
        | (?P<nextop>\bX\b|\bnext\b)
        | (?P<eventually>\bF\b|\beventually\b)
        | (?P<globally>\bG\b|\bglobally\b)
        | (?P<var>[A-Za-z_][A-Za-z_0-9]*)
        )""",
    re.VERBOSE,
)

_UNARY_TEMPORAL = {"nextop": Next, "eventually": Eventually, "globally": Globally}


def _tokenize(text: str) -> List[Tuple[str, str]]:
    tokens: List[Tuple[str, str]] = []
    position = 0
    while position < len(text):
        if text[position].isspace():
            position += 1
            continue
        match = _TOKEN.match(text, position)
        if match is None or match.end() == position:
            raise LTLError("cannot parse LTL formula {0!r} at offset {1}".format(text, position))
        kind = match.lastgroup
        tokens.append((kind, match.group(kind)))
        position = match.end()
    return tokens


class _Parser:
    """implies < or < and < until/release < unary < atom."""

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

    def parse(self) -> LTL:
        formula = self.implication()
        if self.position != len(self.tokens):
            raise LTLError("trailing input in LTL formula {0!r}".format(self.source))
        return formula

    def implication(self) -> LTL:
        left = self.disjunction()
        token = self.peek()
        if token is not None and token[0] == "implies":
            self.take()
            return Disj(Neg(left), self.implication())
        return left

    def disjunction(self) -> LTL:
        formula = self.conjunction()
        while True:
            token = self.peek()
            if token is None or token[0] != "orop":
                return formula
            self.take()
            formula = Disj(formula, self.conjunction())

    def conjunction(self) -> LTL:
        formula = self.binary_temporal()
        while True:
            token = self.peek()
            if token is None or token[0] != "andop":
                return formula
            self.take()
            formula = Conj(formula, self.binary_temporal())

    def binary_temporal(self) -> LTL:
        left = self.unary()
        token = self.peek()
        if token is not None and token[0] in ("until", "release"):
            self.take()
            # Right-associative, as usual for U and R.
            right = self.binary_temporal()
            return Until(left, right) if token[0] == "until" else Release(left, right)
        return left

    def unary(self) -> LTL:
        token = self.peek()
        if token is None:
            raise LTLError("unexpected end of LTL formula {0!r}".format(self.source))
        if token[0] == "notop":
            self.take()
            return Neg(self.unary())
        if token[0] in _UNARY_TEMPORAL:
            self.take()
            return _UNARY_TEMPORAL[token[0]](self.unary())
        return self.atom()

    def atom(self) -> LTL:
        token = self.take()
        if token is None:
            raise LTLError("unexpected end of LTL formula {0!r}".format(self.source))
        kind, text = token
        if kind == "lparen":
            formula = self.implication()
            closing = self.take()
            if closing is None or closing[0] != "rparen":
                raise LTLError("missing ')' in LTL formula {0!r}".format(self.source))
            return formula
        if kind == "true":
            return TrueF()
        if kind == "false":
            return FalseF()
        if kind == "var":
            return Atom(text)
        raise LTLError("unexpected token {0!r} in LTL formula {1!r}".format(text, self.source))


def parse_ltl(text: str) -> LTL:
    """Parse an LTL formula, e.g. ``G(p | (q & X p))``."""
    return _Parser(_tokenize(text.strip()), text.strip()).parse()


def formula_of(value) -> LTL:
    return value if isinstance(value, LTL) else parse_ltl(str(value))


# -- negation normal form ------------------------------------------------


def nnf(formula: LTL, negated: bool = False) -> LTL:
    """Push negations to the atoms and eliminate ``F``, ``G`` and ``->``."""
    if isinstance(formula, TrueF):
        return FalseF() if negated else TrueF()
    if isinstance(formula, FalseF):
        return TrueF() if negated else FalseF()
    if isinstance(formula, Atom):
        return NegAtom(formula.name) if negated else formula
    if isinstance(formula, NegAtom):
        return Atom(formula.name) if negated else formula
    if isinstance(formula, Neg):
        return nnf(formula.operand, not negated)
    if isinstance(formula, Conj):
        left, right = nnf(formula.left, negated), nnf(formula.right, negated)
        return Disj(left, right) if negated else Conj(left, right)
    if isinstance(formula, Disj):
        left, right = nnf(formula.left, negated), nnf(formula.right, negated)
        return Conj(left, right) if negated else Disj(left, right)
    if isinstance(formula, Next):
        return Next(nnf(formula.operand, negated))
    if isinstance(formula, Until):
        left, right = nnf(formula.left, negated), nnf(formula.right, negated)
        return Release(left, right) if negated else Until(left, right)
    if isinstance(formula, Release):
        left, right = nnf(formula.left, negated), nnf(formula.right, negated)
        return Until(left, right) if negated else Release(left, right)
    if isinstance(formula, Eventually):
        # F a == true U a ; !F a == false R !a
        inner = nnf(formula.operand, negated)
        return Release(FalseF(), inner) if negated else Until(TrueF(), inner)
    if isinstance(formula, Globally):
        # G a == false R a ; !G a == true U !a
        inner = nnf(formula.operand, negated)
        return Until(TrueF(), inner) if negated else Release(FalseF(), inner)
    raise LTLError("unsupported formula {0!r}".format(formula))


def negate(formula: LTL) -> LTL:
    """``!phi`` -- used to build the negative automaton of Section 6.2."""
    return Neg(formula)


# -- LTL -> Buchi (Gerth, Peled, Vardi, Wolper) --------------------------


def _is_literal(formula: LTL) -> bool:
    return isinstance(formula, (Atom, NegAtom, TrueF, FalseF))


def _contradicts(literal: LTL, old: FrozenSet[LTL]) -> bool:
    if isinstance(literal, FalseF):
        return True
    if isinstance(literal, Atom):
        return NegAtom(literal.name) in old
    if isinstance(literal, NegAtom):
        return Atom(literal.name) in old
    return False


class _Node:
    __slots__ = ("name", "incoming", "new", "old", "next")

    def __init__(self, name: int, incoming: Set[int], new, old, nxt) -> None:
        self.name = name
        self.incoming = set(incoming)
        self.new = list(new)
        self.old = set(old)
        self.next = set(nxt)


_INIT = -1


def ltl_to_generalized_buchi(formula: LTL, alphabet: Sequence[Letter]) -> GeneralizedBuchi:
    """Tableau construction: the automaton accepts exactly the models of ``formula``."""
    formula = nnf(formula)
    counter = itertools.count()
    nodes: List[_Node] = []

    def fresh(incoming, new, old, nxt) -> _Node:
        return _Node(next(counter), incoming, new, old, nxt)

    def expand(node: _Node) -> None:
        while True:
            if not node.new:
                for existing in nodes:
                    if existing.old == node.old and existing.next == node.next:
                        existing.incoming |= node.incoming
                        return
                nodes.append(node)
                expand(fresh({node.name}, list(node.next), set(), set()))
                return

            eta = node.new.pop()
            if _is_literal(eta):
                if _contradicts(eta, frozenset(node.old)):
                    return  # discard this branch
                if not isinstance(eta, TrueF):
                    node.old.add(eta)
                continue
            if isinstance(eta, Conj):
                node.old.add(eta)
                for part in (eta.left, eta.right):
                    if part not in node.old:
                        node.new.append(part)
                continue
            if isinstance(eta, Next):
                node.old.add(eta)
                node.next.add(eta.operand)
                continue
            if isinstance(eta, (Until, Release, Disj)):
                new1, next1, new2 = _split(eta)
                first = fresh(
                    node.incoming,
                    node.new + [f for f in new1 if f not in node.old],
                    node.old | {eta},
                    node.next | set(next1),
                )
                second = fresh(
                    node.incoming,
                    node.new + [f for f in new2 if f not in node.old],
                    node.old | {eta},
                    set(node.next),
                )
                expand(first)
                expand(second)
                return
            raise LTLError("unsupported formula in tableau: {0!r}".format(eta))

    root = fresh({_INIT}, [formula], set(), set())
    expand(root)

    # -- assemble the automaton ------------------------------------------
    letters = tuple(alphabet)
    by_name = {node.name: node for node in nodes}

    def label_letters(node: _Node) -> List[Letter]:
        literals = [f for f in node.old if isinstance(f, (Atom, NegAtom))]
        out = []
        for letter in letters:
            ok = True
            for literal in literals:
                if isinstance(literal, Atom) and literal.name not in letter:
                    ok = False
                    break
                if isinstance(literal, NegAtom) and literal.name in letter:
                    ok = False
                    break
            if ok:
                out.append(letter)
        return out

    letters_of = {node.name: label_letters(node) for node in nodes}

    # A fresh source state so that every letter is matched against the label of
    # the state it moves *into* -- including the first one.
    source_state = "iota"
    states: List = [source_state] + [node.name for node in nodes]
    transitions: Dict[Tuple, FrozenSet] = {}

    def add(source, letter, target) -> None:
        key = (source, letter)
        transitions[key] = transitions.get(key, frozenset()) | {target}

    for node in nodes:
        for predecessor in node.incoming:
            origin = source_state if predecessor == _INIT else predecessor
            if predecessor != _INIT and predecessor not in by_name:
                continue
            for letter in letters_of[node.name]:
                add(origin, letter, node.name)

    accepting_sets: List[FrozenSet] = []
    for sub in _until_subformulas(formula):
        members = {source_state}
        for node in nodes:
            if sub not in node.old or sub.right in node.old:
                members.add(node.name)
        accepting_sets.append(frozenset(members))

    return GeneralizedBuchi(
        states=states,
        alphabet=letters,
        transitions=transitions,
        initial=frozenset({source_state}),
        accepting_sets=accepting_sets,
    )


def _split(eta: LTL):
    """``(New1, Next1, New2)`` of the tableau rules."""
    if isinstance(eta, Until):  # mu U psi
        return [eta.left], [eta], [eta.right]
    if isinstance(eta, Release):  # mu R psi
        return [eta.right], [eta], [eta.left, eta.right]
    if isinstance(eta, Disj):
        return [eta.left], [], [eta.right]
    raise LTLError("not a splitting operator: {0!r}".format(eta))


def _until_subformulas(formula: LTL) -> List[Until]:
    found: List[Until] = []
    seen: Set[LTL] = set()

    def walk(node: LTL) -> None:
        if node in seen:
            return
        seen.add(node)
        if isinstance(node, Until):
            found.append(node)
        for attribute in ("operand", "left", "right"):
            child = getattr(node, attribute, None)
            if isinstance(child, LTL):
                walk(child)

    walk(formula)
    return found


def ltl_to_buchi(
    formula, alphabet: Sequence[Letter], backend: Optional[str] = None
) -> Buchi:
    """Translate an LTL formula (or its concrete syntax) to a Buchi automaton.

    ``backend`` picks the translation: ``"gpvw"`` (the default) uses the tableau
    construction above, ``"spot"`` delegates to Spot, and ``"auto"`` takes Spot
    when it is installed.  ``STRATEGY_MONITOR_LTL_BACKEND`` sets it for a whole
    run.  Both return a state-based Buchi automaton over the same alphabet, so
    nothing downstream can tell which one built it -- see
    :mod:`strategy_monitor.spot_backend`.
    """
    # Imported here because spot_backend imports this module for the AST.
    from .spot_backend import resolve_ltl_backend, spot_ltl_to_buchi

    if resolve_ltl_backend(backend) == "spot":
        return spot_ltl_to_buchi(formula, alphabet)
    return ltl_to_generalized_buchi(formula_of(formula), alphabet).degeneralize()


def alphabet_of(ap: Iterable[str]) -> Tuple[Letter, ...]:
    """``2^Ap`` in a stable order."""
    ap = tuple(ap)
    letters: List[Letter] = []
    for size in range(len(ap) + 1):
        for combo in itertools.combinations(ap, size):
            letters.append(frozenset(combo))
    return tuple(letters)


def satisfies(word: Sequence[Letter], formula, lasso_from: int = None) -> bool:
    """Evaluate an LTL formula on an ultimately periodic word.

    ``word`` is read as ``word[0] ... word[n-1]`` followed by an infinite
    repetition of ``word[lasso_from:]`` (by default the last letter).  The
    temporal operators are evaluated by a fixpoint over the finitely many
    positions of the lasso, so the result is exact rather than an unrolling
    approximation.  Used by the tests to cross-check the automata constructions.
    """
    formula = nnf(formula_of(formula))
    length = len(word)
    if length == 0:
        raise ValueError("cannot evaluate LTL on an empty word")
    loop = length - 1 if lasso_from is None else lasso_from
    if not 0 <= loop < length:
        raise ValueError("lasso_from out of range")

    def successor(position: int) -> int:
        return position + 1 if position + 1 < length else loop

    cache: Dict[LTL, List[bool]] = {}

    def evaluate(node: LTL) -> List[bool]:
        if node in cache:
            return cache[node]
        if isinstance(node, TrueF):
            values = [True] * length
        elif isinstance(node, FalseF):
            values = [False] * length
        elif isinstance(node, Atom):
            values = [node.name in word[i] for i in range(length)]
        elif isinstance(node, NegAtom):
            values = [node.name not in word[i] for i in range(length)]
        elif isinstance(node, Conj):
            left, right = evaluate(node.left), evaluate(node.right)
            values = [left[i] and right[i] for i in range(length)]
        elif isinstance(node, Disj):
            left, right = evaluate(node.left), evaluate(node.right)
            values = [left[i] or right[i] for i in range(length)]
        elif isinstance(node, Next):
            inner = evaluate(node.operand)
            values = [inner[successor(i)] for i in range(length)]
        elif isinstance(node, Until):
            left, right = evaluate(node.left), evaluate(node.right)
            values = [False] * length  # least fixpoint
            changed = True
            while changed:
                changed = False
                for i in range(length):
                    updated = right[i] or (left[i] and values[successor(i)])
                    if updated != values[i]:
                        values[i] = updated
                        changed = True
        elif isinstance(node, Release):
            left, right = evaluate(node.left), evaluate(node.right)
            values = [True] * length  # greatest fixpoint
            changed = True
            while changed:
                changed = False
                for i in range(length):
                    updated = right[i] and (left[i] or values[successor(i)])
                    if updated != values[i]:
                        values[i] = updated
                        changed = True
        else:
            raise LTLError("unsupported formula {0!r}".format(node))
        cache[node] = values
        return values

    return evaluate(formula)[0]
