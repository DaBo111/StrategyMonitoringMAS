"""Finite and Buchi automata over the explicit alphabet ``2^Ap``.

The paper's Section 4.1 definitions are used verbatim: an NFA is
``(Q, Sigma, delta, Q_0, F)``, a DFA is the deterministic single-initial-state
special case, and a Buchi automaton has the same shape but reads infinite words
and accepts when ``F`` is visited infinitely often.

Letters are ``frozenset`` subsets of ``Ap``, and the alphabet is enumerated
explicitly.  That is quadratic-free and keeps every construction below a plain
graph algorithm, at the price of a ``2^|Ap|`` alphabet -- acceptable for the
model sizes a runtime monitor is built for, and the same trade-off the paper
makes when it writes ``I = 2^Ap``.
"""

from __future__ import annotations

from dataclasses import dataclass, field
from typing import Dict, FrozenSet, Hashable, Iterable, List, Optional, Set, Tuple

Letter = FrozenSet[str]
State = Hashable


@dataclass
class NFA:
    """``A = (Q, Sigma, delta, Q_0, F)`` over finite words."""

    states: List[State]
    alphabet: Tuple[Letter, ...]
    transitions: Dict[Tuple[State, Letter], FrozenSet[State]]
    initial: FrozenSet[State]
    accepting: FrozenSet[State]

    def successors(self, state: State, letter: Letter) -> FrozenSet[State]:
        return self.transitions.get((state, letter), frozenset())

    def accepts(self, word: Iterable[Letter]) -> bool:
        current = set(self.initial)
        for letter in word:
            current = {t for s in current for t in self.successors(s, letter)}
            if not current:
                return False
        return bool(current & self.accepting)

    def is_empty(self) -> bool:
        """True when no finite word is accepted."""
        seen = set(self.initial)
        stack = list(self.initial)
        while stack:
            state = stack.pop()
            if state in self.accepting:
                return False
            for letter in self.alphabet:
                for nxt in self.successors(state, letter):
                    if nxt not in seen:
                        seen.add(nxt)
                        stack.append(nxt)
        return not (seen & self.accepting)


@dataclass
class DFA:
    """``A = (Q, Sigma, delta, q_0, F)`` with a total transition function."""

    states: List[State]
    alphabet: Tuple[Letter, ...]
    transitions: Dict[Tuple[State, Letter], State]
    initial: State
    accepting: FrozenSet[State]

    def step(self, state: State, letter: Letter) -> State:
        return self.transitions[(state, letter)]

    def run(self, word: Iterable[Letter]) -> State:
        state = self.initial
        for letter in word:
            state = self.step(state, letter)
        return state

    def accepts(self, word: Iterable[Letter]) -> bool:
        return self.run(word) in self.accepting


@dataclass
class Buchi:
    """A Buchi automaton; ``accepting`` is a set of states (state-based acceptance)."""

    states: List[State]
    alphabet: Tuple[Letter, ...]
    transitions: Dict[Tuple[State, Letter], FrozenSet[State]]
    initial: FrozenSet[State]
    accepting: FrozenSet[State]

    def successors(self, state: State, letter: Letter) -> FrozenSet[State]:
        return self.transitions.get((state, letter), frozenset())

    def edges(self) -> Iterable[Tuple[State, State]]:
        for (source, _letter), targets in self.transitions.items():
            for target in targets:
                yield source, target


@dataclass
class GeneralizedBuchi:
    """A Buchi automaton with several acceptance sets, all to be visited i.o."""

    states: List[State]
    alphabet: Tuple[Letter, ...]
    transitions: Dict[Tuple[State, Letter], FrozenSet[State]]
    initial: FrozenSet[State]
    accepting_sets: List[FrozenSet[State]] = field(default_factory=list)

    def degeneralize(self) -> Buchi:
        """Standard counting construction turning ``m`` acceptance sets into one."""
        if not self.accepting_sets:
            return Buchi(
                states=list(self.states),
                alphabet=self.alphabet,
                transitions=dict(self.transitions),
                initial=self.initial,
                accepting=frozenset(self.states),
            )
        count = len(self.accepting_sets)
        transitions: Dict[Tuple[State, Letter], FrozenSet[State]] = {}
        states = [(state, layer) for state in self.states for layer in range(count)]
        for (source, letter), targets in self.transitions.items():
            for layer in range(count):
                nxt_layer = (layer + 1) % count if source in self.accepting_sets[layer] else layer
                transitions[((source, layer), letter)] = frozenset(
                    (target, nxt_layer) for target in targets
                )
        return Buchi(
            states=states,
            alphabet=self.alphabet,
            transitions=transitions,
            initial=frozenset((state, 0) for state in self.initial),
            accepting=frozenset(
                (state, 0) for state in self.accepting_sets[0]
            ),
        )


# -- graph algorithms ----------------------------------------------------


def strongly_connected_components(
    states: Iterable[State], successors
) -> List[FrozenSet[State]]:
    """Tarjan's algorithm, iterative so that deep automata do not blow the stack."""
    index: Dict[State, int] = {}
    low: Dict[State, int] = {}
    on_stack: Set[State] = set()
    stack: List[State] = []
    result: List[FrozenSet[State]] = []
    counter = 0

    for root in states:
        if root in index:
            continue
        work: List[Tuple[State, List[State], int]] = [(root, None, 0)]
        while work:
            state, children, position = work.pop()
            if children is None:
                index[state] = low[state] = counter
                counter += 1
                stack.append(state)
                on_stack.add(state)
                children = list(successors(state))
                position = 0
            recurse = False
            while position < len(children):
                child = children[position]
                position += 1
                if child not in index:
                    work.append((state, children, position))
                    work.append((child, None, 0))
                    recurse = True
                    break
                if child in on_stack:
                    low[state] = min(low[state], index[child])
            if recurse:
                continue
            if low[state] == index[state]:
                component = set()
                while True:
                    member = stack.pop()
                    on_stack.discard(member)
                    component.add(member)
                    if member == state:
                        break
                result.append(frozenset(component))
            if work:
                parent = work[-1][0]
                low[parent] = min(low[parent], low[state])
    return result


@dataclass
class Lasso:
    """A witness that a Buchi automaton is non-empty.

    ``prefix (loop)^omega`` is accepted; the ``_states`` fields carry the run
    itself, so a caller can read the witness in terms of whatever the states
    mean to it (product components, model states) instead of re-deriving it
    from the letters.
    """

    prefix_letters: List[Letter]
    loop_letters: List[Letter]
    prefix_states: List[State]
    loop_states: List[State]

    def word(self) -> Tuple[List[Letter], List[Letter]]:
        return self.prefix_letters, self.loop_letters

    def run(self) -> List[State]:
        """The states visited, prefix then one turn of the loop."""
        return self.prefix_states + self.loop_states


def buchi_lasso(buchi: Buchi) -> Optional["Lasso"]:
    """An accepted ultimately periodic word, or ``None`` if the language is empty.

    A Buchi automaton accepts something iff some reachable SCC holds an
    accepting state and at least one internal edge, so this searches the
    reachable part for such an SCC and reads a witness out of it.
    """

    def successors(state: State) -> Set[State]:
        out: Set[State] = set()
        for letter in buchi.alphabet:
            out |= buchi.successors(state, letter)
        return out

    reachable: Set[State] = set(buchi.initial)
    frontier = list(buchi.initial)
    while frontier:
        state = frontier.pop()
        for target in successors(state):
            if target not in reachable:
                reachable.add(target)
                frontier.append(target)

    for component in strongly_connected_components(reachable, successors):
        accepting = component & buchi.accepting
        if not accepting:
            continue
        witness = next(iter(sorted(accepting, key=str)))
        loop = _path_within(buchi, witness, witness, component)
        if loop is None:
            continue
        prefix = _path_to(buchi, witness)
        return Lasso(
            prefix_letters=[letter for letter, _ in prefix],
            loop_letters=[letter for letter, _ in loop],
            prefix_states=[witness if not prefix else prefix[0][1]][:0]
            + _run_states(buchi, prefix, witness),
            loop_states=[state for _, state in loop],
        )
    return None


def _run_states(buchi: Buchi, prefix, witness: State) -> List[State]:
    """States along the prefix, starting from the initial one it left."""
    if not prefix:
        return [witness]
    first = next(iter(sorted(buchi.initial, key=str)))
    for state in buchi.initial:
        if _reaches(buchi, state, prefix):
            first = state
            break
    return [first] + [state for _, state in prefix]


def _reaches(buchi: Buchi, start: State, prefix) -> bool:
    state = start
    for letter, expected in prefix:
        if expected not in buchi.successors(state, letter):
            return False
        state = expected
    return True


def buchi_is_empty(buchi: Buchi) -> bool:
    """True when the automaton accepts no infinite word."""
    return buchi_lasso(buchi) is None


def _trace_back(seen, target) -> List[Tuple[Letter, State]]:
    """Rebuild a path as (letter, state-entered) steps from a BFS parent map."""
    steps: List[Tuple[Letter, State]] = []
    cursor = target
    while seen[cursor] is not None:
        previous, letter = seen[cursor]
        steps.append((letter, cursor))
        cursor = previous
    steps.reverse()
    return steps


def _path_to(buchi: Buchi, target: State) -> List[Tuple[Letter, State]]:
    """A shortest path from an initial state to ``target``, as (letter, state)."""
    if target in buchi.initial:
        return []
    seen = {state: None for state in buchi.initial}
    queue = list(buchi.initial)
    while queue:
        state = queue.pop(0)
        for letter in buchi.alphabet:
            for nxt in buchi.successors(state, letter):
                if nxt in seen:
                    continue
                seen[nxt] = (state, letter)
                if nxt == target:
                    return _trace_back(seen, nxt)
                queue.append(nxt)
    return []


def _path_within(buchi: Buchi, start: State, target: State, component):
    """A non-empty path from ``start`` back to ``target`` inside one SCC."""
    for letter in buchi.alphabet:
        for nxt in sorted(buchi.successors(start, letter) & component, key=str):
            if nxt == target:
                return [(letter, nxt)]
            seen = {nxt: None}
            queue = [nxt]
            while queue:
                state = queue.pop(0)
                for step in buchi.alphabet:
                    for following in buchi.successors(state, step):
                        if following not in component or following in seen:
                            continue
                        seen[following] = (state, step)
                        if following == target:
                            return [(letter, nxt)] + _trace_back(seen, following)
                        queue.append(following)
    return None


def prefix_nfa(buchi: Buchi) -> NFA:
    """The *prefix automaton* of a Buchi automaton (Bauer et al., 2011).

    A finite word is accepted exactly when it can be extended to an infinite
    word accepted by ``buchi``.  Structurally the automaton is unchanged; a
    state becomes accepting iff it can reach an accepting SCC, that is, an SCC
    that contains an accepting state and at least one internal edge.
    """

    def successors(state: State) -> Set[State]:
        out: Set[State] = set()
        for letter in buchi.alphabet:
            out |= buchi.successors(state, letter)
        return out

    components = strongly_connected_components(buchi.states, successors)
    component_of: Dict[State, int] = {}
    for identifier, component in enumerate(components):
        for state in component:
            component_of[state] = identifier

    accepting_components = set()
    for identifier, component in enumerate(components):
        if not (component & buchi.accepting):
            continue
        # A single state with no self-loop cannot be visited infinitely often.
        has_internal_edge = any(
            target in component
            for state in component
            for letter in buchi.alphabet
            for target in buchi.successors(state, letter)
        )
        if has_internal_edge:
            accepting_components.add(identifier)

    # Backward reachability over the condensation.
    reverse: Dict[int, Set[int]] = {identifier: set() for identifier in range(len(components))}
    for source, target in buchi.edges():
        if component_of[source] != component_of[target]:
            reverse[component_of[target]].add(component_of[source])

    can_reach = set(accepting_components)
    frontier = list(accepting_components)
    while frontier:
        current = frontier.pop()
        for predecessor in reverse[current]:
            if predecessor not in can_reach:
                can_reach.add(predecessor)
                frontier.append(predecessor)

    accepting = frozenset(state for state in buchi.states if component_of[state] in can_reach)
    return NFA(
        states=list(buchi.states),
        alphabet=buchi.alphabet,
        transitions=dict(buchi.transitions),
        initial=buchi.initial,
        accepting=accepting,
    )


def determinize(nfa: NFA) -> DFA:
    """Subset construction; the empty subset is the (rejecting) sink."""
    initial = frozenset(nfa.initial)
    states: List[FrozenSet[State]] = [initial]
    seen = {initial}
    transitions: Dict[Tuple[State, Letter], State] = {}
    frontier = [initial]
    while frontier:
        current = frontier.pop()
        for letter in nfa.alphabet:
            target = frozenset(
                nxt for state in current for nxt in nfa.successors(state, letter)
            )
            transitions[(current, letter)] = target
            if target not in seen:
                seen.add(target)
                states.append(target)
                frontier.append(target)
    accepting = frozenset(subset for subset in states if subset & nfa.accepting)
    return DFA(
        states=states,
        alphabet=nfa.alphabet,
        transitions=transitions,
        initial=initial,
        accepting=accepting,
    )


class NFASimulator:
    """Runs an NFA on-the-fly, carrying the active state set as a bitmask.

    This is the subset construction done *lazily*: the set of states reachable
    on the word read so far is exactly the state a determinised automaton would
    be in, but it is recomputed each step instead of tabulated in advance.  The
    trade is the standard one -- construction stays linear in the automaton and
    no exponential table is ever built, at the cost of ``O(|Q|)`` set-union work
    per letter instead of one array lookup.

    States are numbered by their position in ``nfa.states``; the active set is
    an integer whose bit ``i`` says that state ``i`` is live.
    """

    __slots__ = ("nfa", "order", "index", "initial_mask", "accepting_mask", "_moves", "active")

    def __init__(self, nfa: NFA) -> None:
        self.nfa = nfa
        self.order = list(nfa.states)
        self.index = {state: position for position, state in enumerate(self.order)}
        self.initial_mask = self._mask(nfa.initial)
        self.accepting_mask = self._mask(nfa.accepting)
        # moves[letter][i] is the set of states reachable from state i on letter
        self._moves: Dict[Letter, List[int]] = {}
        for letter in nfa.alphabet:
            self._moves[letter] = [
                self._mask(nfa.successors(state, letter)) for state in self.order
            ]
        self.active = self.initial_mask

    def _mask(self, states: Iterable[State]) -> int:
        mask = 0
        for state in states:
            position = self.index.get(state)
            if position is not None:
                mask |= 1 << position
        return mask

    def reset(self) -> None:
        self.active = self.initial_mask

    def advance(self, active: int, letter: Letter) -> int:
        """The successor of an arbitrary active set -- one subset-construction step.

        Pure: it does not touch :attr:`active`, so a caller can drive the
        automaton from a state it is holding elsewhere (which is what the lazy
        determinisation engine does when it fills its cache).
        """
        table = self._moves.get(letter)
        if table is None:
            return 0
        nxt = 0
        while active:
            lowest = active & -active
            nxt |= table[lowest.bit_length() - 1]
            active ^= lowest
        return nxt

    def step(self, letter: Letter) -> bool:
        """Consume one letter; return whether the word read so far is accepted."""
        self.active = self.advance(self.active, letter)
        return bool(self.active & self.accepting_mask)

    @property
    def accepting(self) -> bool:
        """Whether the word read so far is accepted."""
        return bool(self.active & self.accepting_mask)

    @property
    def live_states(self) -> FrozenSet[State]:
        """The active set, as states -- the subset a DFA would have tabulated."""
        return frozenset(
            state for position, state in enumerate(self.order) if self.active >> position & 1
        )

    def __len__(self) -> int:
        return len(self.order)


def buchi_product(left: Buchi, right: Buchi, right_all_accepting: bool = False) -> Buchi:
    """Synchronous product accepting ``L(left) & L(right)``.

    When ``right`` has every state accepting -- which is the case for the Buchi
    automaton read off a CGS in Section 6.2 -- the interleaving counter of the
    general construction is unnecessary and the acceptance condition of the
    product is simply that of ``left``.  Pass ``right_all_accepting=True`` to
    take that shortcut; otherwise the standard two-copy construction is used.
    """
    if right_all_accepting:
        return _plain_product(left, right)
    return _counting_product(left, right)


def _plain_product(left: Buchi, right: Buchi) -> Buchi:
    alphabet = left.alphabet
    initial = frozenset((a, b) for a in left.initial for b in right.initial)
    states: List[State] = list(initial)
    seen = set(initial)
    transitions: Dict[Tuple[State, Letter], FrozenSet[State]] = {}
    frontier = list(initial)
    while frontier:
        source = frontier.pop()
        a, b = source
        for letter in alphabet:
            targets = frozenset(
                (x, y) for x in left.successors(a, letter) for y in right.successors(b, letter)
            )
            if targets:
                transitions[(source, letter)] = targets
            for target in targets:
                if target not in seen:
                    seen.add(target)
                    states.append(target)
                    frontier.append(target)
    accepting = frozenset(state for state in states if state[0] in left.accepting)
    return Buchi(
        states=states,
        alphabet=alphabet,
        transitions=transitions,
        initial=initial,
        accepting=accepting,
    )


def _counting_product(left: Buchi, right: Buchi) -> Buchi:
    alphabet = left.alphabet
    initial = frozenset((a, b, 0) for a in left.initial for b in right.initial)
    states: List[State] = list(initial)
    seen = set(initial)
    transitions: Dict[Tuple[State, Letter], FrozenSet[State]] = {}
    frontier = list(initial)
    while frontier:
        source = frontier.pop()
        a, b, turn = source
        if turn == 0:
            nxt_turn = 1 if a in left.accepting else 0
        else:
            nxt_turn = 0 if b in right.accepting else 1
        for letter in alphabet:
            targets = frozenset(
                (x, y, nxt_turn)
                for x in left.successors(a, letter)
                for y in right.successors(b, letter)
            )
            if targets:
                transitions[(source, letter)] = targets
            for target in targets:
                if target not in seen:
                    seen.add(target)
                    states.append(target)
                    frontier.append(target)
    accepting = frozenset(
        state for state in states if state[2] == 1 and state[0] in left.accepting
    )
    return Buchi(
        states=states,
        alphabet=alphabet,
        transitions=transitions,
        initial=initial,
        accepting=accepting,
    )


def dfa_product(left: DFA, right: DFA) -> DFA:
    """Reachable product transition structure; acceptance is left to the caller."""
    alphabet = left.alphabet
    initial = (left.initial, right.initial)
    states: List[State] = [initial]
    seen = {initial}
    transitions: Dict[Tuple[State, Letter], State] = {}
    frontier = [initial]
    while frontier:
        source = frontier.pop()
        a, b = source
        for letter in alphabet:
            target = (left.step(a, letter), right.step(b, letter))
            transitions[(source, letter)] = target
            if target not in seen:
                seen.add(target)
                states.append(target)
                frontier.append(target)
    return DFA(
        states=states,
        alphabet=alphabet,
        transitions=transitions,
        initial=initial,
        accepting=frozenset(),
    )


def to_dot(automaton, name: str = "A", accepting_shape: str = "doublecircle") -> str:
    """Render an NFA/DFA/Buchi as Graphviz DOT for inspection.

    Whether a state is a set is decided by the automaton's type, not by the
    runtime type of the value: a determinised automaton's states are themselves
    frozensets, so testing ``isinstance(..., frozenset)`` would take one state
    for a set of states.
    """
    deterministic = isinstance(automaton, DFA)
    lines = ["digraph {0} {{".format(name), "  rankdir=LR;", '  __start [shape=point];']
    identifiers = {state: "q{0}".format(i) for i, state in enumerate(automaton.states)}
    for state, identifier in identifiers.items():
        shape = accepting_shape if state in automaton.accepting else "circle"
        lines.append(
            '  {0} [shape={1}, label="{2}"];'.format(identifier, shape, _quote(_short(state)))
        )

    initial_states = [automaton.initial] if deterministic else list(automaton.initial)
    for state in initial_states:
        if state in identifiers:
            lines.append("  __start -> {0};".format(identifiers[state]))

    merged: Dict[Tuple[str, str], List[str]] = {}
    for (source, letter), target in automaton.transitions.items():
        targets = [target] if deterministic else list(target)
        for one in targets:
            if source in identifiers and one in identifiers:
                merged.setdefault((identifiers[source], identifiers[one]), []).append(
                    _letter_label(letter)
                )
    for (source, target), labels in merged.items():
        label = _quote(" | ".join(sorted(labels)))
        lines.append('  {0} -> {1} [label="{2}"];'.format(source, target, label))
    lines.append("}")
    return chr(10).join(lines)


def _quote(text: str) -> str:
    """Escape a label for a DOT quoted string.

    State identifiers and atom names are read from the model file, so a stray
    quote or backslash in one would otherwise emit DOT that does not parse.
    """
    return text.replace(chr(92), chr(92) * 2).replace('"', chr(92) + '"')


def _letter_label(letter: Letter) -> str:
    return "{" + ",".join(sorted(letter)) + "}" if letter else "{}"


def _short(state: State) -> str:
    """A compact label; determinised states are sets and print verbosely."""
    if isinstance(state, frozenset):
        text = "{" + ",".join(sorted(_short(member) for member in state)) + "}"
    elif isinstance(state, tuple):
        text = "(" + ",".join(_short(member) for member in state) + ")"
    else:
        text = str(state)
    return text if len(text) <= 28 else text[:25] + "..."
