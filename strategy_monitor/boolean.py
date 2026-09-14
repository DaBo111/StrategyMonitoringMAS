"""Boolean formulas over atomic propositions -- ``Bool(Ap)`` of Section 5.3.

These are the *gates* of a memoryless natural strategy.  The concrete syntax
accepts the usual spellings so that gates can be copied straight out of the
paper, out of a VITAMIN NatATL witness, or typed by hand::

    p            !p           p & q         p && q
    p | q        p or q       p -> q        true / True / top
    (p & !q) | r

``complexity`` implements ``|phi|`` of Section 5.3 -- the number of variable
occurrences in the formula -- which drives the complexity bounds of
Proposition 4.
"""

from __future__ import annotations

import re
from dataclasses import dataclass
from typing import FrozenSet, Iterable, List, Sequence, Set, Tuple


class GateError(ValueError):
    """Raised on a malformed Boolean gate."""


# -- abstract syntax -----------------------------------------------------


class Gate:
    """A Boolean formula over ``Ap``.

    A gate is a binary tree, so every traversal is bounded by the interpreter's
    stack: one conjunction of more than roughly 800 terms is deeper than CPython
    allows.  The traversals handle that differently, because they do not cost
    the same.

    ``evaluate`` stays recursive, and each combining node guards its own
    subtree: on overflow the innermost ``And``/``Or``/``Not`` catches the
    ``RecursionError`` and finishes that subtree with an explicit stack.
    Recursion is worth keeping because it short-circuits ``&`` and ``|`` --
    an explicit stack cannot, and measured 7x slower at every depth -- and
    because this is the one traversal on a hot path, run once per gate per
    state while a monitor is built and once per letter at runtime.  Guarding
    every node costs nothing measurable, since a ``try`` that never fires is
    far cheaper than a call; routing through a single wrapper method instead
    cost 18% of monitor construction, which is why it is done this way.  The
    subtrees caught this way are disjoint, so the fallback stays linear.

    ``variables`` is iterative unconditionally.  The recursive form
    concatenated a fresh list at every node, making it superlinear in the size
    of the gate (measured exponent 1.30, against 0.96 iterative), and nothing
    calls it in a loop.  ``__str__`` is guarded through ``_render`` rather than
    per node, being neither hot nor superlinear.
    """

    def evaluate(self, valuation: FrozenSet[str]) -> bool:
        raise NotImplementedError

    def variables(self) -> List[str]:
        """Every variable *occurrence*, in order (so ``p & p`` yields two)."""
        found: List[str] = []
        stack: List["Gate"] = [self]
        while stack:
            node = stack.pop()
            kind = node.__class__
            if kind is Var:
                found.append(node.name)
            elif kind is Not:
                stack.append(node.operand)
            elif kind is And or kind is Or:
                stack.append(node.right)
                stack.append(node.left)
        return found

    @property
    def complexity(self) -> int:
        """``|phi|``: the number of variables appearing in the formula."""
        return len(self.variables())

    def __str__(self) -> str:
        try:
            return self._render()
        except RecursionError:
            return _render_iteratively(self)

    def _render(self) -> str:
        raise NotImplementedError


@dataclass(frozen=True)
class Top(Gate):
    def evaluate(self, valuation: FrozenSet[str]) -> bool:
        return True

    def _render(self) -> str:
        return "true"


@dataclass(frozen=True)
class Bottom(Gate):
    def evaluate(self, valuation: FrozenSet[str]) -> bool:
        return False

    def _render(self) -> str:
        return "false"


@dataclass(frozen=True)
class Var(Gate):
    name: str

    def evaluate(self, valuation: FrozenSet[str]) -> bool:
        return self.name in valuation

    def _render(self) -> str:
        return self.name


@dataclass(frozen=True)
class Not(Gate):
    operand: Gate

    def evaluate(self, valuation: FrozenSet[str]) -> bool:
        try:
            return not self.operand.evaluate(valuation)
        except RecursionError:
            return _evaluate_iteratively(self, valuation)

    def _render(self) -> str:
        return "!" + self.operand._render()


@dataclass(frozen=True)
class And(Gate):
    left: Gate
    right: Gate

    def evaluate(self, valuation: FrozenSet[str]) -> bool:
        try:
            return self.left.evaluate(valuation) and self.right.evaluate(valuation)
        except RecursionError:
            return _evaluate_iteratively(self, valuation)

    def _render(self) -> str:
        return "({0} & {1})".format(self.left._render(), self.right._render())


@dataclass(frozen=True)
class Or(Gate):
    left: Gate
    right: Gate

    def evaluate(self, valuation: FrozenSet[str]) -> bool:
        try:
            return self.left.evaluate(valuation) or self.right.evaluate(valuation)
        except RecursionError:
            return _evaluate_iteratively(self, valuation)

    def _render(self) -> str:
        return "({0} | {1})".format(self.left._render(), self.right._render())


# -- concrete syntax -----------------------------------------------------

_TOKEN = re.compile(
    r"""\s*(?:
          (?P<lparen>\()
        | (?P<rparen>\))
        | (?P<implies>->|=>)
        | (?P<andop>&&|&|\band\b)
        | (?P<orop>\|\||\||\bor\b)
        | (?P<notop>!|~|\bnot\b)
        | (?P<true>\btrue\b|\bTrue\b|\btop\b|\bTop\b|\bTRUE\b)
        | (?P<false>\bfalse\b|\bFalse\b|\bbot\b|\bBot\b|\bFALSE\b)
        | (?P<var>[A-Za-z_][A-Za-z_0-9]*)
        )""",
    re.VERBOSE,
)



def _evaluate_iteratively(gate: Gate, valuation: FrozenSet[str]) -> bool:
    """``gate.evaluate`` for a tree deeper than the interpreter's stack.

    Post-order over an explicit stack.  It cannot short-circuit, so both
    operands of every ``&`` and ``|`` are evaluated; gates are pure, so only the
    cost differs and not the answer.
    """
    pending = [(gate, False)]
    values: List[bool] = []
    while pending:
        node, expanded = pending.pop()
        kind = node.__class__
        if not expanded:
            if kind is Var:
                values.append(node.name in valuation)
            elif kind is Top:
                values.append(True)
            elif kind is Bottom:
                values.append(False)
            elif kind is Not:
                pending.append((node, True))
                pending.append((node.operand, False))
            else:
                pending.append((node, True))
                pending.append((node.right, False))
                pending.append((node.left, False))
        elif kind is Not:
            values.append(not values.pop())
        elif kind is And:
            right = values.pop()
            values.append(values.pop() and right)
        else:
            right = values.pop()
            values.append(values.pop() or right)
    return values[0]


def _render_iteratively(gate: Gate) -> str:
    """``str(gate)`` for a tree deeper than the interpreter's stack."""
    pending = [(gate, False)]
    parts: List[str] = []
    while pending:
        node, expanded = pending.pop()
        kind = node.__class__
        if not expanded:
            if kind is Var:
                parts.append(node.name)
            elif kind is Top:
                parts.append("true")
            elif kind is Bottom:
                parts.append("false")
            elif kind is Not:
                pending.append((node, True))
                pending.append((node.operand, False))
            else:
                pending.append((node, True))
                pending.append((node.right, False))
                pending.append((node.left, False))
        elif kind is Not:
            parts.append("!" + parts.pop())
        else:
            right = parts.pop()
            parts.append(
                "({0} {1} {2})".format(parts.pop(), "&" if kind is And else "|", right)
            )
    return parts[0]


def _tokenize(text: str) -> List[Tuple[str, str]]:
    tokens: List[Tuple[str, str]] = []
    position = 0
    while position < len(text):
        if text[position].isspace():
            position += 1
            continue
        match = _TOKEN.match(text, position)
        if match is None or match.end() == position:
            raise GateError("cannot parse gate {0!r} at offset {1}".format(text, position))
        kind = match.lastgroup
        tokens.append((kind, match.group(kind)))
        position = match.end()
    return tokens


class _Parser:
    """Recursive descent: implies < or < and < not < atom."""

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

    def parse(self) -> Gate:
        gate = self.implication()
        if self.position != len(self.tokens):
            raise GateError(
                "trailing input in gate {0!r} at token {1}".format(self.source, self.position)
            )
        return gate

    def implication(self) -> Gate:
        left = self.disjunction()
        token = self.peek()
        if token is not None and token[0] == "implies":
            self.take()
            return Or(Not(left), self.implication())
        return left

    def disjunction(self) -> Gate:
        gate = self.conjunction()
        while True:
            token = self.peek()
            if token is None or token[0] != "orop":
                return gate
            self.take()
            gate = Or(gate, self.conjunction())

    def conjunction(self) -> Gate:
        gate = self.negation()
        while True:
            token = self.peek()
            if token is None or token[0] != "andop":
                return gate
            self.take()
            gate = And(gate, self.negation())

    def negation(self) -> Gate:
        token = self.peek()
        if token is not None and token[0] == "notop":
            self.take()
            return Not(self.negation())
        return self.atom()

    def atom(self) -> Gate:
        token = self.take()
        if token is None:
            raise GateError("unexpected end of gate {0!r}".format(self.source))
        kind, text = token
        if kind == "lparen":
            gate = self.implication()
            closing = self.take()
            if closing is None or closing[0] != "rparen":
                raise GateError("missing ')' in gate {0!r}".format(self.source))
            return gate
        if kind == "true":
            return Top()
        if kind == "false":
            return Bottom()
        if kind == "var":
            return Var(text)
        raise GateError("unexpected token {0!r} in gate {1!r}".format(text, self.source))


def parse_gate(text: str) -> Gate:
    """Parse a Boolean gate; ``""`` and ``"*"`` both denote ``top``."""
    stripped = text.strip()
    if stripped in ("", "*"):
        return Top()
    return _Parser(_tokenize(stripped), stripped).parse()


def gate_of(value) -> Gate:
    """Coerce a gate given as a :class:`Gate` or a string."""
    return value if isinstance(value, Gate) else parse_gate(str(value))


def satisfying_letters(gate: Gate, alphabet: Iterable[FrozenSet[str]]) -> Set[FrozenSet[str]]:
    """The letters of ``2^Ap`` that satisfy the gate."""
    return {letter for letter in alphabet if gate.evaluate(letter)}
