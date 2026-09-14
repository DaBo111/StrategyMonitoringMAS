"""The three classes of coalition strategy the paper monitors.

* :class:`KBoundedStrategy` -- Section 5.2.  ``gamma_i(h) = gamma_i(h^{>=k})``:
  the prescribed action depends only on the last ``k`` observed states.
  ``k = 1`` is the memoryless case.
* :class:`NaturalMemorylessStrategy` -- Section 5.3, ``NatS`` without recall: a
  priority-ordered list of ``(gate, action)`` pairs per agent, the agent playing
  the action of the first gate the current state satisfies.
* ``NatS`` with recall comes in two representations, both of Section 5.3/5.5:
  :class:`NaturalRecallRegexStrategy` is the regular-expression-sequence form a
  strategy is *specified* in, and :class:`NaturalRecallStrategy` is the
  deterministic finite-state transducer form Section 5.5 monitors.
  :meth:`NaturalRecallRegexStrategy.to_dfst_strategy` translates between them,
  and the monitor may instead simulate the regexes' NFAs directly.
"""

from __future__ import annotations

import itertools
from dataclasses import dataclass, field
from typing import Dict, FrozenSet, List, Mapping, Optional, Sequence, Tuple

from .automata import DFA, NFA, Letter
from .boolean import Gate, gate_of, parse_gate
from .cgs import CGS, JointAction
from .regex import Regex, compile_regex_to_dfa, parse_regex, regex_to_nfa
from .regex import complexity as regex_complexity
from .regex import matches as regex_matches

Window = Tuple[str, ...]
"""A memory configuration: a history of at most ``k`` states, most recent last."""


class StrategyError(ValueError):
    """Raised when a strategy is inconsistent with the model it is written for."""


# ======================================================================
# k-bounded memory strategies (Section 5.2)
# ======================================================================


@dataclass
class KBoundedStrategy:
    """``Gamma_A = {gamma_i}_{i in A}`` with ``k``-bounded memory.

    ``table`` maps a memory configuration (a tuple of at most ``k`` states,
    most recent last) to the action each coalition member is told to play.
    """

    coalition: Tuple[str, ...]
    k: int
    table: Dict[Window, Dict[str, str]] = field(default_factory=dict)

    def prescribe(self, window: Window) -> Optional[Dict[str, str]]:
        """``alpha^A_h`` for the memory configuration ``h``; ``None`` if undefined."""
        return self.table.get(tuple(window))

    def profile(self, window: Window) -> Optional[JointAction]:
        """The prescribed coalition action profile, ordered like ``coalition``."""
        prescribed = self.prescribe(window)
        if prescribed is None:
            return None
        return tuple(prescribed[agent] for agent in self.coalition)

    def configurations(self) -> List[Window]:
        return list(self.table)

    # -- constructors ----------------------------------------------------

    @classmethod
    def memoryless(
        cls, coalition: Sequence[str], assignment: Mapping[str, Mapping[str, str]]
    ) -> "KBoundedStrategy":
        """Build a 1-bounded strategy from a plain ``state -> {agent: action}`` map."""
        coalition = tuple(coalition)
        table = {(state,): dict(actions) for state, actions in assignment.items()}
        return cls(coalition=coalition, k=1, table=table)

    @classmethod
    def from_function(
        cls, cgs: CGS, coalition: Sequence[str], k: int, function
    ) -> "KBoundedStrategy":
        """Tabulate ``function(window, agent) -> action`` over every window of length <= k.

        This materialises ``H_{Gamma_A}`` of Section 5.2, whose size is the
        ``O(|S|^k)`` of Proposition 2.
        """
        coalition = tuple(coalition)
        table: Dict[Window, Dict[str, str]] = {}
        for length in range(1, k + 1):
            for window in itertools.product(cgs.states, repeat=length):
                table[window] = {agent: function(window, agent) for agent in coalition}
        return cls(coalition=coalition, k=k, table=table)

    def validate(self, cgs: CGS) -> None:
        """Check ``gamma_i(h) in d(h^{>=1}, i)`` for every tabulated configuration."""
        problems: List[str] = []
        for window, actions in self.table.items():
            current = window[-1]
            for agent, action in actions.items():
                if agent not in cgs.agents:
                    problems.append("unknown agent {0!r}".format(agent))
                elif current in cgs.states and action not in cgs.available(current, agent):
                    problems.append(
                        "gamma_{0}({1}) = {2!r} is not in d({3!r}, {0!r})".format(
                            agent, window, action, current
                        )
                    )
        if problems:
            raise StrategyError("invalid strategy:\n" + "\n".join("  - " + p for p in problems))

    def __str__(self) -> str:  # pragma: no cover - display helper
        rows = []
        for window in sorted(self.table):
            actions = self.table[window]
            rows.append(
                "  ({0}, ({1}))".format(
                    "".join(window), ", ".join(actions[a] for a in self.coalition)
                )
            )
        return "K-bounded strategy (k={0}) for {1}:\n".format(self.k, list(self.coalition)) + "\n".join(rows)


# ======================================================================
# natural memoryless strategies (Sections 5.3 and 5.4)
# ======================================================================


@dataclass
class NaturalMemorylessStrategy:
    """``Gamma_A^{Natr}``: one priority-ordered gate list per coalition member."""

    coalition: Tuple[str, ...]
    rules: Dict[str, List[Tuple[Gate, str]]] = field(default_factory=dict)

    @classmethod
    def build(cls, coalition: Sequence[str], rules: Mapping[str, Sequence]) -> "NaturalMemorylessStrategy":
        """``rules[agent]`` is an ordered sequence of ``(gate, action)`` pairs.

        The gate may be a :class:`~strategy_monitor.boolean.Gate` or its concrete
        syntax, so a strategy can be written exactly as in the paper::

            NaturalMemorylessStrategy.build(
                ["a", "b"],
                {"a": [("p", "in"), ("q", "out"), ("true", "idle")],
                 "b": [("p", "in"), ("q", "out"), ("true", "idle")]})
        """
        coalition = tuple(coalition)
        compiled = {
            agent: [(gate_of(gate), action) for gate, action in rules[agent]] for agent in coalition
        }
        return cls(coalition=coalition, rules=compiled)

    def action_for(self, agent: str, valuation: FrozenSet[str]) -> Optional[str]:
        """``argmin_i {act^a_i | s |= gate^a_i}`` -- the first gate that fires."""
        for gate, action in self.rules[agent]:
            if gate.evaluate(valuation):
                return action
        return None

    def complexity(self, agent: Optional[str] = None) -> int:
        """``compl(gamma_a^{Natr}) = sum |gate|`` over the agent's pairs.

        Without an agent, the maximum over the coalition -- the ``k`` of
        Proposition 4.
        """
        if agent is not None:
            return sum(gate.complexity for gate, _ in self.rules[agent])
        return max(
            (sum(gate.complexity for gate, _ in pairs) for pairs in self.rules.values()),
            default=0,
        )

    def to_kbounded(self, cgs: CGS, strict: bool = True) -> KBoundedStrategy:
        """Algorithm 1 of the paper: reduce to the 1-bounded table of Section 5.2.

        Iterates over the states and, for each, over the coalition members,
        taking the action of the first gate the state satisfies -- the
        ``O(|A| x |S| x k^2)`` construction of Proposition 4.
        """
        table: Dict[Window, Dict[str, str]] = {}
        problems: List[str] = []
        for state in cgs.states:
            valuation = cgs.label(state)
            actions: Dict[str, str] = {}
            for agent in self.coalition:
                action = self.action_for(agent, valuation)
                if action is None:
                    problems.append("no gate of agent {0!r} fires in {1!r}".format(agent, state))
                    continue
                if action not in cgs.available(state, agent):
                    problems.append(
                        "gate of agent {0!r} prescribes {1!r} in {2!r}, "
                        "which d({2!r}, {0!r}) does not allow".format(agent, action, state)
                    )
                actions[agent] = action
            table[(state,)] = actions
        if problems and strict:
            raise StrategyError(
                "natural strategy does not fit the model:\n"
                + "\n".join("  - " + p for p in problems)
            )
        return KBoundedStrategy(coalition=self.coalition, k=1, table=table)

    @classmethod
    def from_vitamin_witness(
        cls, coalition: Sequence[str], witness: Sequence[Mapping]
    ) -> "NaturalMemorylessStrategy":
        """Adopt the strategy VITAMIN's NatATL memoryless checker returns.

        ``witness`` is the ``"Winning Strategy per agent"`` value: one entry per
        coalition member, each a mapping with a ``condition_action_pairs`` list.
        """
        coalition = tuple(coalition)
        if len(witness) != len(coalition):
            raise StrategyError(
                "witness has {0} entries for a coalition of {1}".format(len(witness), len(coalition))
            )
        rules = {}
        for agent, entry in zip(coalition, witness):
            pairs = entry["condition_action_pairs"] if isinstance(entry, Mapping) else entry
            rules[agent] = [(parse_gate(condition), action) for condition, action in pairs]
        return cls(coalition=coalition, rules=rules)

    def __str__(self) -> str:  # pragma: no cover - display helper
        lines = ["Natural memoryless strategy for {0}:".format(list(self.coalition))]
        for agent in self.coalition:
            body = ", ".join(
                "({0}, {1})".format(gate, action) for gate, action in self.rules[agent]
            )
            lines.append("  gamma_{0}^Natr = ({1})   compl = {2}".format(agent, body, self.complexity(agent)))
        return "\n".join(lines)


# ======================================================================
# natural strategies with recall (Section 5.5)
# ======================================================================


@dataclass
class DFST:
    """A deterministic finite-state transducer ``(S, s_0, I, O, F_I, F_O)``.

    ``F_I: S x I -> S`` is the state transition function and
    ``F_O: S x I -> O`` the output function.  A *NatDFST* is a DFST with
    ``I = 2^Ap`` and ``O = Act`` implementing a natural strategy with recall.
    """

    states: List
    initial: object
    input_alphabet: Tuple[Letter, ...]
    output_alphabet: Tuple[str, ...]
    transition: Dict[Tuple[object, Letter], object]
    output: Dict[Tuple[object, Letter], str]

    def step(self, state, letter: Letter):
        """``(F_I(s, p), F_O(s, p))``."""
        key = (state, letter)
        if key not in self.transition:
            raise StrategyError("DFST has no transition for {0!r}".format(key))
        return self.transition[key], self.output[key]

    def run(self, word: Sequence[Letter]) -> List[str]:
        """The output the transducer emits on the given input word."""
        state = self.initial
        emitted = []
        for letter in word:
            state, out = self.step(state, letter)
            emitted.append(out)
        return emitted

    def validate(self) -> None:
        missing = [
            (state, letter)
            for state in self.states
            for letter in self.input_alphabet
            if (state, letter) not in self.transition
        ]
        if missing:
            raise StrategyError(
                "DFST transition function is partial; missing {0} entries "
                "(first: {1})".format(len(missing), missing[0])
            )


def product_dfst(transducers: Sequence[DFST], alphabet: Sequence[Letter]) -> DFST:
    """The product DFST of Proposition 5.

    ``S = prod_a S^a``, ``F_I`` and ``F_O`` applied componentwise, giving the
    ``O(m^{|A|} x 2^{Ap} x |A|)`` construction of the proposition.  Only the
    reachable part of the product is built, which never exceeds that bound.
    """
    if not transducers:
        raise StrategyError("cannot take the product of an empty coalition")
    letters = tuple(alphabet)
    initial = tuple(t.initial for t in transducers)
    states = [initial]
    seen = {initial}
    transition: Dict[Tuple[object, Letter], object] = {}
    output: Dict[Tuple[object, Letter], str] = {}
    frontier = [initial]
    while frontier:
        source = frontier.pop()
        for letter in letters:
            target = []
            emitted = []
            for component, transducer in zip(source, transducers):
                nxt, out = transducer.step(component, letter)
                target.append(nxt)
                emitted.append(out)
            target = tuple(target)
            transition[(source, letter)] = target
            output[(source, letter)] = tuple(emitted)
            if target not in seen:
                seen.add(target)
                states.append(target)
                frontier.append(target)
    outputs = tuple(sorted({o for o in output.values()}, key=str))
    return DFST(
        states=states,
        initial=initial,
        input_alphabet=letters,
        output_alphabet=outputs,
        transition=transition,
        output=output,
    )


@dataclass
class NaturalRecallStrategy:
    """``Gamma_A^{NatR}`` given as one NatDFST per coalition member."""

    coalition: Tuple[str, ...]
    transducers: Dict[str, DFST]

    @classmethod
    def build(cls, coalition: Sequence[str], transducers: Mapping[str, DFST]) -> "NaturalRecallStrategy":
        coalition = tuple(coalition)
        return cls(coalition=coalition, transducers={a: transducers[a] for a in coalition})

    @classmethod
    def from_regex_sequences(
        cls,
        coalition: Sequence[str],
        sequences: Mapping[str, Sequence[Tuple[str, str]]],
        alphabet: Sequence[Letter],
        default_action: Optional[Mapping[str, str]] = None,
    ) -> "NaturalRecallStrategy":
        """Compile the regular-expression-sequence form into NatDFSTs.

        ``sequences[agent]`` is the priority-ordered list of ``(regex, action)``
        pairs of Section 5.3; the agent plays the action of the first regex the
        observed history matches.  Each regex over ``Bool(Ap)`` is compiled to a
        DFA over ``2^Ap`` and the DFAs are producted, the output of a product
        state being the action of the least-index accepting component.  This is
        the translation Section 5.5 refers to; the monitor itself is built from
        the resulting transducers.
        """
        coalition = tuple(coalition)
        letters = tuple(alphabet)
        transducers: Dict[str, DFST] = {}
        for agent in coalition:
            pairs = list(sequences[agent])
            if not pairs:
                raise StrategyError("agent {0!r} has an empty strategy".format(agent))
            dfas = [compile_regex_to_dfa(pattern, letters) for pattern, _ in pairs]
            actions = [action for _, action in pairs]
            fallback = (default_action or {}).get(agent)
            transducers[agent] = _combine_dfas(dfas, actions, letters, fallback)
        return cls(coalition=coalition, transducers=transducers)

    def product(self, alphabet: Sequence[Letter]) -> DFST:
        """The product DFST driving the monitor of Proposition 5."""
        return product_dfst([self.transducers[a] for a in self.coalition], alphabet)

    def complexity(self, agent: Optional[str] = None) -> int:
        """Number of DFST states -- the ``m`` of Proposition 5 when maximised."""
        if agent is not None:
            return len(self.transducers[agent].states)
        return max((len(t.states) for t in self.transducers.values()), default=0)


@dataclass
class NaturalRecallRegexStrategy:
    """``Gamma_A^{NatR}`` in the regular-expression-sequence form of Section 5.3.

    ``gamma_a^{NatR} = ((regex_1, act_1), ..., (regex_n, act_n))`` and, given a
    history ``h``, agent ``a`` plays ``act_i`` for the least ``i`` with
    ``h |= regex_i``.  This is the representation the strategies are *specified*
    in; Section 5.5 builds its monitor from DFSTs instead, and proves the bounds
    for that form.  Keeping the regexes as the strategy lets the monitor choose
    between the two:

    * :meth:`to_dfst_strategy` performs the translation Section 5.5 refers to --
      each regex becomes a DFA, and the prioritised DFAs are producted into one
      transducer.  Construction can be exponential in the regexes; a step is
      then a single table lookup.
    * :meth:`nfas` hands back the Thompson automata untouched, for a monitor
      that simulates them.  Construction is linear; a step costs an NFA
      transition per regex.

    Neither choice changes what is prescribed -- see :meth:`action_for`, which
    defines the semantics directly.
    """

    coalition: Tuple[str, ...]
    sequences: Dict[str, List[Tuple[Regex, str]]] = field(default_factory=dict)
    default_action: Dict[str, Optional[str]] = field(default_factory=dict)

    @classmethod
    def build(
        cls,
        coalition: Sequence[str],
        sequences: Mapping[str, Sequence],
        default_action: Optional[Mapping[str, str]] = None,
    ) -> "NaturalRecallRegexStrategy":
        """``sequences[agent]`` is the ordered list of ``(regex, action)`` pairs.

        A regex may be given as a :class:`~strategy_monitor.regex.Regex` or in
        the concrete syntax, so a strategy reads as it is written in the paper::

            NaturalRecallRegexStrategy.build(
                ["a"], {"a": [(".*[q].*", "out"), (".*", "in")]})
        """
        coalition = tuple(coalition)
        compiled: Dict[str, List[Tuple[Regex, str]]] = {}
        for agent in coalition:
            pairs = list(sequences[agent])
            if not pairs:
                raise StrategyError("agent {0!r} has an empty strategy".format(agent))
            compiled[agent] = [
                (pattern if isinstance(pattern, Regex) else parse_regex(str(pattern)), action)
                for pattern, action in pairs
            ]
        fallback = {agent: (default_action or {}).get(agent) for agent in coalition}
        return cls(coalition=coalition, sequences=compiled, default_action=fallback)

    # -- semantics -------------------------------------------------------

    def action_for(self, agent: str, word: Sequence[Letter]) -> Optional[str]:
        """``argmin_i {act_i | h |= regex_i}`` for the history labelled ``word``.

        The reference semantics, evaluated by matching directly; the monitors
        must agree with it whichever engine they use.
        """
        for pattern, action in self.sequences[agent]:
            if regex_matches(pattern, word):
                return action
        return self.default_action.get(agent)

    def complexity(self, agent: Optional[str] = None) -> int:
        """``compl(gamma_a^{NatR}) = sum ||regex||`` over the agent's pairs.

        Without an agent, the maximum over the coalition.  ``||r||`` is the
        measure of Section 5.3, in which a leading ``top^*`` is free.
        """
        if agent is not None:
            return sum(regex_complexity(pattern) for pattern, _ in self.sequences[agent])
        return max(
            (
                sum(regex_complexity(pattern) for pattern, _ in pairs)
                for pairs in self.sequences.values()
            ),
            default=0,
        )

    # -- the two compilations --------------------------------------------

    def nfas(self, alphabet: Sequence[Letter]) -> Dict[str, List[NFA]]:
        """The Thompson automaton of each regex, in priority order."""
        letters = tuple(alphabet)
        return {
            agent: [regex_to_nfa(pattern, letters) for pattern, _ in pairs]
            for agent, pairs in self.sequences.items()
        }

    def actions(self, agent: str) -> List[str]:
        return [action for _, action in self.sequences[agent]]

    def to_dfsts(self, alphabet: Sequence[Letter]) -> Dict[str, DFST]:
        """Determinise: one NatDFST per agent, as Section 5.5 assumes."""
        letters = tuple(alphabet)
        transducers: Dict[str, DFST] = {}
        for agent in self.coalition:
            dfas = [compile_regex_to_dfa(pattern, letters) for pattern, _ in self.sequences[agent]]
            transducers[agent] = _combine_dfas(
                dfas, self.actions(agent), letters, self.default_action.get(agent)
            )
        return transducers

    def to_dfst_strategy(self, alphabet: Sequence[Letter]) -> "NaturalRecallStrategy":
        """The Section 5.5 form of this strategy."""
        return NaturalRecallStrategy(
            coalition=self.coalition, transducers=self.to_dfsts(alphabet)
        )

    def __str__(self) -> str:  # pragma: no cover - display helper
        lines = ["Natural recall strategy (regex sequences) for {0}:".format(list(self.coalition))]
        for agent in self.coalition:
            body = ", ".join(
                "({0}, {1})".format(pattern, action) for pattern, action in self.sequences[agent]
            )
            lines.append(
                "  gamma_{0}^NatR = ({1})   compl = {2}".format(agent, body, self.complexity(agent))
            )
            fallback = self.default_action.get(agent)
            if fallback is not None:
                lines.append("      default action: {0}".format(fallback))
        return "\n".join(lines)


def _combine_dfas(
    dfas: Sequence[DFA],
    actions: Sequence[str],
    letters: Sequence[Letter],
    fallback: Optional[str],
) -> DFST:
    """Product of prioritised DFAs into a transducer emitting the winning action."""
    initial = tuple(dfa.initial for dfa in dfas)
    states = [initial]
    seen = {initial}
    transition: Dict[Tuple[object, Letter], object] = {}
    output: Dict[Tuple[object, Letter], str] = {}
    frontier = [initial]
    while frontier:
        source = frontier.pop()
        for letter in letters:
            target = tuple(dfa.step(component, letter) for dfa, component in zip(dfas, source))
            transition[(source, letter)] = target
            emitted = fallback
            for position, dfa in enumerate(dfas):
                if target[position] in dfa.accepting:
                    emitted = actions[position]
                    break
            if emitted is None:
                raise StrategyError(
                    "no regex of the sequence matches every history and no default "
                    "action was given; add a 'true*' catch-all or pass default_action"
                )
            output[(source, letter)] = emitted
            if target not in seen:
                seen.add(target)
                states.append(target)
                frontier.append(target)
    return DFST(
        states=states,
        initial=initial,
        input_alphabet=tuple(letters),
        output_alphabet=tuple(sorted(set(output.values()))),
        transition=transition,
        output=output,
    )


# ======================================================================
# strategy files
# ======================================================================


def strategy_from_dict(data: Mapping, alphabet: Optional[Sequence[Letter]] = None):
    """Load a strategy from its JSON form.

    Three shapes are recognised, keyed by ``"type"``::

        {"type": "natural_memoryless", "coalition": ["a", "b"],
         "rules": {"a": [["p", "in"], ["q", "out"], ["true", "idle"]], ...}}

        {"type": "k_bounded", "coalition": ["a", "b"], "k": 1,
         "table": {"s0": {"a": "in", "b": "in"}, ...}}

        {"type": "k_bounded", "coalition": ["a"], "k": 2,
         "table": [{"window": ["s0", "s1"], "actions": {"a": "in"}}, ...]}

        {"type": "natural_recall", "coalition": ["a"],
         "regexes": {"a": [[".*[q].*", "out"], [".*", "in"]]}}

    ``natural_recall`` yields a :class:`NaturalRecallRegexStrategy`: the regexes
    are kept, and the monitor decides whether to determinise them.  ``alphabet``
    is therefore no longer needed for it, and is accepted only so that older
    callers keep working.
    """
    kind = data.get("type", "natural_memoryless")
    coalition = tuple(data["coalition"])

    if kind == "natural_memoryless":
        return NaturalMemorylessStrategy.build(
            coalition, {agent: [tuple(pair) for pair in data["rules"][agent]] for agent in coalition}
        )

    if kind == "k_bounded":
        k = int(data.get("k", 1))
        raw = data["table"]
        table: Dict[Window, Dict[str, str]] = {}
        if isinstance(raw, Mapping):
            if k != 1:
                raise StrategyError("the dict form of a k-bounded table is only valid for k = 1")
            for state, actions in raw.items():
                table[(state,)] = dict(actions)
        else:
            for entry in raw:
                table[tuple(entry["window"])] = dict(entry["actions"])
        return KBoundedStrategy(coalition=coalition, k=k, table=table)

    if kind == "natural_recall":
        return NaturalRecallRegexStrategy.build(
            coalition,
            {agent: [tuple(pair) for pair in data["regexes"][agent]] for agent in coalition},
            default_action=data.get("default_action"),
        )

    if kind == "natural_recall_dfst":
        if alphabet is None:
            raise StrategyError("the DFST form needs the model alphabet 2^Ap")
        return NaturalRecallRegexStrategy.build(
            coalition,
            {agent: [tuple(pair) for pair in data["regexes"][agent]] for agent in coalition},
            default_action=data.get("default_action"),
        ).to_dfst_strategy(alphabet)

    raise StrategyError("unknown strategy type {0!r}".format(kind))


def load_strategy(path: str, alphabet: Optional[Sequence[Letter]] = None):
    """Read a strategy JSON file."""
    import json

    with open(path, encoding="utf-8") as handle:
        return strategy_from_dict(json.load(handle), alphabet)


def strategy_to_dict(strategy) -> Dict:
    """Serialise a strategy back to the JSON form :func:`strategy_from_dict` reads."""
    if isinstance(strategy, NaturalMemorylessStrategy):
        return {
            "type": "natural_memoryless",
            "coalition": list(strategy.coalition),
            "rules": {
                agent: [[str(gate), action] for gate, action in pairs]
                for agent, pairs in strategy.rules.items()
            },
        }
    if isinstance(strategy, NaturalRecallRegexStrategy):
        entry = {
            "type": "natural_recall",
            "coalition": list(strategy.coalition),
            "regexes": {
                agent: [[str(pattern), action] for pattern, action in pairs]
                for agent, pairs in strategy.sequences.items()
            },
        }
        fallbacks = {a: v for a, v in strategy.default_action.items() if v is not None}
        if fallbacks:
            entry["default_action"] = fallbacks
        return entry
    if isinstance(strategy, KBoundedStrategy):
        if strategy.k == 1:
            return {
                "type": "k_bounded",
                "coalition": list(strategy.coalition),
                "k": 1,
                "table": {window[0]: dict(actions) for window, actions in strategy.table.items()},
            }
        return {
            "type": "k_bounded",
            "coalition": list(strategy.coalition),
            "k": strategy.k,
            "table": [
                {"window": list(window), "actions": dict(actions)}
                for window, actions in sorted(strategy.table.items())
            ],
        }
    raise StrategyError("cannot serialise {0!r}".format(type(strategy).__name__))
