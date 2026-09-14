"""Strategy monitors -- Sections 5.2, 5.4, 5.5 and 6.1.

Every monitor consumes a trace ``s_0 alpha_0 s_1 alpha_1 ...`` incrementally
through :meth:`StrategyMonitor.observe` and reports a :class:`Verdict` after
each step.  All of them are *sticky*: once a conclusive verdict is reached it is
kept, since the paper's monitors never retract a decision.
"""

from __future__ import annotations

import itertools
from typing import Dict, FrozenSet, Iterable, List, Mapping, Optional, Sequence, Set, Tuple

from .automata import NFASimulator
from .cgs import CGS, JointAction
from .strategies import (
    KBoundedStrategy,
    NaturalMemorylessStrategy,
    NaturalRecallRegexStrategy,
    StrategyError,
    Window,
)
from .trace import Trace
from .verdict import Verdict, Violation

DEFAULT_MAX_DENSE_TABLE = 1 << 22
"""Above this many entries the direct-address table is replaced by a dict."""


# ======================================================================
# the sliding memory-configuration index of Proposition 2
# ======================================================================


class WindowIndex:
    """Direct-address index over ``union_{k' <= k} S^{k'}``.

    Implements the addressing scheme of Proposition 2: the block for histories
    of length ``m`` starts at ``o_m = sum_{m' < m} |S|^{m'}`` and a history ``h``
    sits at ``o_{|h|} + sum_{t < |h|} id(h[t]) * |S|^{|h|-1-t}``.  The index is
    *maintained* rather than recomputed, in a constant number of arithmetic
    operations per observation:

    * while the window is shorter than ``k`` it is extended by
      ``idx' = o_{m+1} + (idx - o_m) * |S| + id(s)``;
    * once full it slides by
      ``idx' = o_k + ((idx - o_k) mod |S|^{k-1}) * |S| + id(s)``.
    """

    def __init__(self, cgs: CGS, k: int) -> None:
        if k < 1:
            raise ValueError("k must be at least 1")
        self.cgs = cgs
        self.k = k
        self.size = len(cgs.states)
        # o_m for m = 0 .. k
        self.offsets: List[int] = [0]
        total = 0
        for m in range(k + 1):
            total += self.size ** m
            self.offsets.append(total)
        # offsets[m] is o_m = sum_{m' < m} |S|^{m'}
        self.offsets = [sum(self.size ** m_prime for m_prime in range(m)) for m in range(k + 2)]
        self.capacity = self.offsets[k + 1]
        self.stride = self.size ** (k - 1)
        self.reset()

    def reset(self) -> None:
        self.length = 0
        self.value = self.offsets[0]  # the empty history sits at index 0
        self.window: Tuple[str, ...] = ()

    def push(self, state: str) -> int:
        """Slide the window over one more state and return the new index."""
        identifier = self.cgs.index(state)
        if self.length < self.k:
            self.value = self.offsets[self.length + 1] + (self.value - self.offsets[self.length]) * self.size + identifier
            self.length += 1
            self.window = self.window + (state,)
        else:
            self.value = (
                self.offsets[self.k]
                + ((self.value - self.offsets[self.k]) % self.stride) * self.size
                + identifier
            )
            self.window = self.window[1:] + (state,)
        return self.value

    def index_of(self, window: Sequence[str]) -> int:
        """Non-incremental address of a window, used when building the table."""
        length = len(window)
        if length > self.k:
            raise ValueError("window longer than k")
        value = self.offsets[length]
        for position, state in enumerate(window):
            value += self.cgs.index(state) * self.size ** (length - 1 - position)
        return value

    def windows(self, min_length: int = 1) -> Iterable[Window]:
        """Every memory configuration of length between ``min_length`` and ``k``."""
        for length in range(min_length, self.k + 1):
            for combination in itertools.product(self.cgs.states, repeat=length):
                yield combination


# ======================================================================
# base class
# ======================================================================


class StrategyMonitor:
    """Common incremental interface: ``observe`` state, then action."""

    def __init__(self, cgs: CGS, coalition: Sequence[str]) -> None:
        self.cgs = cgs
        self.coalition = tuple(coalition)
        self.step_count = 0
        self.violations: List[Violation] = []
        self._verdict = Verdict.UNKNOWN
        self._awaiting_action = False
        self.current_state: Optional[str] = None

    # -- interface -------------------------------------------------------

    @property
    def verdict(self) -> Verdict:
        return self._verdict

    def observe_state(self, state: str) -> Verdict:
        if self._awaiting_action:
            raise StrategyError("the previous state has no observed action yet")
        self.current_state = state
        self._awaiting_action = True
        self._on_state(state)
        return self._verdict

    def observe_action(self, profile: JointAction) -> Verdict:
        if not self._awaiting_action:
            raise StrategyError("no state is pending; call observe_state first")
        self._awaiting_action = False
        self._on_action(tuple(profile))
        self.step_count += 1
        return self._verdict

    def observe(self, state: str, profile: Optional[JointAction] = None) -> Verdict:
        """Observe ``s_j`` and, if given, the action ``alpha_j`` taken in it."""
        self.observe_state(state)
        if profile is not None:
            self.observe_action(profile)
        return self._verdict

    def resume_at(self, state: str) -> Verdict:
        """Restart observation at ``state`` with no action outstanding.

        Used when the repair procedure of Section 7 pauses the system, replaces
        the strategy, and resumes from ``q_curr``: the action that triggered the
        repair has already been dealt with, so the monitor takes ``q_curr`` as
        its new starting point rather than waiting for that action again.
        """
        self._awaiting_action = False
        self.current_state = state
        self._on_state(state)
        return self._verdict

    def run(self, trace: Trace) -> Verdict:
        """Feed a whole trace; returns the final verdict."""
        for state, action in trace.steps():
            self.observe(state, action)
        return self._verdict

    def verdicts(self, trace: Trace) -> List[Verdict]:
        """The verdict after each observation -- useful for tables and plots."""
        out: List[Verdict] = []
        for state, action in trace.steps():
            self.observe_state(state)
            out.append(self._verdict)
            if action is not None:
                self.observe_action(action)
                out.append(self._verdict)
        return out

    # -- hooks -----------------------------------------------------------

    def _on_state(self, state: str) -> None:
        raise NotImplementedError

    def _on_action(self, profile: JointAction) -> None:
        raise NotImplementedError

    def _fail(self, violation: Violation) -> None:
        self.violations.append(violation)
        if self._verdict is Verdict.UNKNOWN:
            self._verdict = Verdict.BOT

    def _check_agents(
        self, profile: JointAction, prescribed: Optional[Mapping[str, str]], window: Window
    ) -> None:
        """Compare the observed profile with the prescription, agent by agent.

        Attribution per agent is what makes the coalition repair of Section 7.1
        possible; the loop is the ``O(|A|)`` per-step cost of Propositions 1--5.
        """
        state = self.current_state
        for agent in self.coalition:
            observed = profile[self.cgs.agent_index(agent)]
            expected = None if prescribed is None else prescribed.get(agent)
            if expected is None or observed != expected:
                self._fail(
                    Violation(
                        step=self.step_count,
                        state=state,
                        agent=agent,
                        prescribed=expected,
                        observed=observed,
                        window=tuple(window),
                    )
                )


# ======================================================================
# k-bounded monitor (Section 5.2, Propositions 1 and 2)
# ======================================================================


class KBoundedMonitor(StrategyMonitor):
    """``M_{Gamma_A}`` of Eq. (4).

    The monitor is the direct-address table ``H_{Gamma_A}`` of Section 5.2,
    addressed by the sliding index of Proposition 2.  Construction is
    ``O(|S|^k x |A|)`` time and space; each observation costs ``O(|A|)``.
    """

    def __init__(
        self,
        cgs: CGS,
        strategy: KBoundedStrategy,
        dense: Optional[bool] = None,
        max_dense_table: int = DEFAULT_MAX_DENSE_TABLE,
    ) -> None:
        super().__init__(cgs, strategy.coalition)
        self.strategy = strategy
        self.k = strategy.k
        self.index = WindowIndex(cgs, strategy.k)
        if dense is None:
            dense = self.index.capacity <= max_dense_table
        self.dense = dense
        # Build the table: one pass over the configurations, one over the agents.
        if dense:
            self.table: List[Optional[Dict[str, str]]] = [None] * self.index.capacity
            for window, actions in strategy.table.items():
                self.table[self.index.index_of(window)] = dict(actions)
        else:
            self.table = {}
            for window, actions in strategy.table.items():
                self.table[self.index.index_of(window)] = dict(actions)
        self._current_index = self.index.value

    def _lookup(self, address: int) -> Optional[Dict[str, str]]:
        if self.dense:
            return self.table[address] if 0 <= address < len(self.table) else None
        return self.table.get(address)

    def _on_state(self, state: str) -> None:
        self._current_index = self.index.push(state)

    def _on_action(self, profile: JointAction) -> None:
        prescribed = self._lookup(self._current_index)
        self._check_agents(profile, prescribed, self.index.window)

    # -- introspection ---------------------------------------------------

    @property
    def window(self) -> Window:
        """``(omega_s^{<=j})^{>=k}`` -- the memory configuration currently held."""
        return self.index.window

    def table_size(self) -> int:
        return self.index.capacity if self.dense else len(self.table)


class NaturalMemorylessMonitor(KBoundedMonitor):
    """``M_{Gamma_A^{Natr}}`` of Section 5.4.

    Proposition 4 shows a natural memoryless strategy induces a state-indexed
    table, making this monitor equivalent to the 1-bounded monitor above; the
    reduction is Algorithm 1, run by
    :meth:`~strategy_monitor.strategies.NaturalMemorylessStrategy.to_kbounded`.
    """

    def __init__(self, cgs: CGS, strategy: NaturalMemorylessStrategy, strict: bool = True, **kwargs) -> None:
        self.natural_strategy = strategy
        super().__init__(cgs, strategy.to_kbounded(cgs, strict=strict), **kwargs)


# ======================================================================
# natural strategy with recall (Section 5.5, Proposition 5)
# ======================================================================


_NO_NFA_MESSAGE = (
    "this engine needs the regular-expression-sequence form; the DFST form of "
    "Section 5.5 has no NFA left to simulate. Build the strategy with "
    "NaturalRecallRegexStrategy, or monitor with determinize='dfa'."
)


def _no_match_message(agent: str) -> str:
    return (
        "no regex of agent {0!r} matches the observed history and no default action "
        "was given; add a 'true*' catch-all or pass default_action".format(agent)
    )


class RecallEngine:
    """How a recall monitor turns the observed labelling into a prescription.

    Two engines implement the same function ``history -> action per agent``;
    they differ only in where the cost is paid.  See
    :class:`ProductDFSTEngine` and :class:`RegexNFAEngine`.
    """

    coalition: Tuple[str, ...] = ()

    def reset(self) -> None:
        raise NotImplementedError

    def step(self, letter) -> Dict[str, str]:
        """Consume ``pi(s_j)`` and return the action each agent ought to play."""
        raise NotImplementedError

    @property
    def size(self) -> int:
        """The number of automaton states the engine carries."""
        raise NotImplementedError

    def describe(self) -> str:
        """What the engine is, in construction terms; fixed before the run."""
        raise NotImplementedError

    def summary(self) -> Optional[str]:
        """What the run has cost so far, when the engine has anything to report."""
        return None


class ProductDFSTEngine(RecallEngine):
    """Determinise at construction: the product DFST of Proposition 5.

    Each regex becomes a DFA, the prioritised DFAs of one agent are producted
    into a NatDFST, and the agents' transducers are producted again.  A step is
    then a single table lookup, ``O(|A|)`` for the coalition; the price is that
    the table can be exponential in the regexes, on top of the ``O(m^{|A|})``
    of the proposition.
    """

    def __init__(self, strategy, alphabet) -> None:
        if isinstance(strategy, NaturalRecallRegexStrategy):
            strategy = strategy.to_dfst_strategy(alphabet)
        self.strategy = strategy
        self.coalition = tuple(strategy.coalition)
        self.product = strategy.product(alphabet)
        self.state = self.product.initial

    def reset(self) -> None:
        self.state = self.product.initial

    def step(self, letter) -> Dict[str, str]:
        self.state, emitted = self.product.step(self.state, letter)
        return dict(zip(self.coalition, emitted))

    @property
    def size(self) -> int:
        return len(self.product.states)

    def describe(self) -> str:
        return "product DFST, {0} states".format(self.size)


class RegexNFAEngine(RecallEngine):
    """Keep the NFAs and simulate them, paying per step instead.

    Every regex of every agent is compiled by Thompson's construction only --
    linear in the regex -- and simulated with
    :class:`~strategy_monitor.automata.NFASimulator`, which carries the active
    state set as a bitmask.  A step advances each regex's active set and takes
    the action of the least-index accepting one, so the runtime cost is
    ``O(sum_i |N_i|)`` per agent rather than a lookup, and no exponential table
    is ever built.

    Every simulator must consume every letter, so the loop advances them all and
    only then picks the winner: stopping at the first match would leave the
    lower-priority automata behind on the word.
    """

    def __init__(self, strategy: NaturalRecallRegexStrategy, alphabet) -> None:
        if not isinstance(strategy, NaturalRecallRegexStrategy):
            raise StrategyError(_NO_NFA_MESSAGE)
        self.strategy = strategy
        self.coalition = tuple(strategy.coalition)
        letters = tuple(alphabet)
        automata = strategy.nfas(letters)
        self.simulators: Dict[str, List[NFASimulator]] = {
            agent: [NFASimulator(nfa) for nfa in automata[agent]] for agent in self.coalition
        }
        self.actions: Dict[str, List[str]] = {
            agent: strategy.actions(agent) for agent in self.coalition
        }
        self.fallback = dict(strategy.default_action)

    def reset(self) -> None:
        for simulators in self.simulators.values():
            for simulator in simulators:
                simulator.reset()

    def step(self, letter) -> Dict[str, str]:
        prescribed: Dict[str, str] = {}
        for agent in self.coalition:
            # Advance every regex; only then take the least-index match.
            matched = [simulator.step(letter) for simulator in self.simulators[agent]]
            chosen = self.fallback.get(agent)
            for hit, action in zip(matched, self.actions[agent]):
                if hit:
                    chosen = action
                    break
            if chosen is None:
                raise StrategyError(_no_match_message(agent))
            prescribed[agent] = chosen
        return prescribed

    @property
    def size(self) -> int:
        return sum(len(sim) for sims in self.simulators.values() for sim in sims)

    def describe(self) -> str:
        return "NFA simulation, {0} states".format(self.size)


class LazyProductEngine(RecallEngine):
    """Determinise on the fly: memoise the subset transition as the run meets it.

    The active sets of the regexes' NFAs, taken together across the coalition,
    *are* a state of the determinised product -- the engine simply never
    enumerates them in advance.  A step looks up
    ``(state, letter) -> (next state, prescription)``; on a miss it does the NFA
    work once, resolves the priority scan once, and stores the answer.  The
    cache it accumulates is exactly the fragment of :class:`ProductDFSTEngine`'s
    table that the run actually visits.

    So construction is linear like :class:`RegexNFAEngine`, and a warmed-up step
    is a single dictionary lookup for the whole coalition like
    :class:`ProductDFSTEngine`.  Memory is bounded by the states materialised,
    at most the full product but in practice by the length of the run: a run of
    ``n`` steps can reach at most ``n + 1`` distinct states.
    """

    def __init__(self, strategy: NaturalRecallRegexStrategy, alphabet) -> None:
        if not isinstance(strategy, NaturalRecallRegexStrategy):
            raise StrategyError(_NO_NFA_MESSAGE)
        self.strategy = strategy
        self.coalition = tuple(strategy.coalition)
        letters = tuple(alphabet)
        automata = strategy.nfas(letters)
        self.simulators: Dict[str, List[NFASimulator]] = {
            agent: [NFASimulator(nfa) for nfa in automata[agent]] for agent in self.coalition
        }
        self.actions: Dict[str, List[str]] = {
            agent: strategy.actions(agent) for agent in self.coalition
        }
        self.fallback = dict(strategy.default_action)

        # One flat vector of active sets, so a product state is a tuple of ints.
        self._flat: List[NFASimulator] = [
            simulator for agent in self.coalition for simulator in self.simulators[agent]
        ]
        self._blocks: List[Tuple[str, int, int]] = []
        offset = 0
        for agent in self.coalition:
            width = len(self.simulators[agent])
            self._blocks.append((agent, offset, width))
            offset += width

        self.initial = tuple(simulator.initial_mask for simulator in self._flat)
        self.state = self.initial
        self.cache: Dict[Tuple, Tuple] = {}
        self.discovered = {self.initial}
        self.hits = 0
        self.misses = 0

    def reset(self) -> None:
        """Rewind the run; the cache is knowledge about the automaton, so it stays."""
        self.state = self.initial

    def _transition(self, state: Tuple, letter) -> Tuple:
        """One subset step for every regex, then the priority scan per agent."""
        nxt = tuple(
            simulator.advance(mask, letter) for simulator, mask in zip(self._flat, state)
        )
        prescribed: Dict[str, str] = {}
        for agent, offset, width in self._blocks:
            chosen = self.fallback.get(agent)
            for position in range(width):
                simulator = self._flat[offset + position]
                if nxt[offset + position] & simulator.accepting_mask:
                    chosen = self.actions[agent][position]
                    break
            if chosen is None:
                raise StrategyError(_no_match_message(agent))
            prescribed[agent] = chosen
        return nxt, prescribed

    def step(self, letter) -> Dict[str, str]:
        key = (self.state, letter)
        entry = self.cache.get(key)
        if entry is None:
            self.misses += 1
            entry = self._transition(self.state, letter)
            self.cache[key] = entry
            self.discovered.add(entry[0])
        else:
            self.hits += 1
        self.state, prescribed = entry
        return dict(prescribed)

    @property
    def size(self) -> int:
        """NFA states carried -- the construction cost, as for the NFA engine."""
        return sum(len(simulator) for simulator in self._flat)

    @property
    def materialised(self) -> int:
        """Product states discovered so far -- how much of the DFA got built."""
        return len(self.discovered)

    def describe(self) -> str:
        return "lazy determinisation, {0} NFA states".format(self.size)

    def summary(self) -> str:
        lookups = self.hits + self.misses
        return (
            "{0} product state(s) materialised from {1} step(s): "
            "{2} cache hit(s), {3} miss(es)".format(
                self.materialised, lookups, self.hits, self.misses
            )
        )


RECALL_ENGINES = ("dfa", "nfa", "lazy")
"""The three ways :class:`NaturalRecallMonitor` can run a recall strategy."""

_ENGINE_ALIASES = {True: "dfa", False: "nfa"}


def resolve_recall_engine(determinize) -> str:
    """Normalise the ``determinize`` argument to one of :data:`RECALL_ENGINES`.

    ``True``/``False`` are kept as aliases for ``"dfa"``/``"nfa"`` so that the
    two-way form still reads naturally.
    """
    if isinstance(determinize, bool):
        return _ENGINE_ALIASES[determinize]
    if determinize in RECALL_ENGINES:
        return determinize
    raise StrategyError(
        "unknown recall engine {0!r}; expected one of {1} (or True/False for "
        "dfa/nfa)".format(determinize, ", ".join(RECALL_ENGINES))
    )


class NaturalRecallMonitor(StrategyMonitor):
    """``M_{Gamma_A^{NatR}}``: the recall monitor of Section 5.5, run online.

    The engine reads ``pi(s_j)`` at every step and yields the action profile the
    coalition ought to play; the monitor compares it, agent by agent, with what
    was observed.  ``determinize`` chooses where the work happens:

    * ``"dfa"`` (or ``True``, the default) -- Proposition 5's construction.  The
      regexes are determinised into DFSTs and producted up front, which can be
      exponential, and each step is then one lookup.
    * ``"nfa"`` (or ``False``) -- the automata are kept as NFAs and simulated.
      Construction is linear in the strategy, and each step advances one active
      set per regex.
    * ``"lazy"`` -- the same subset construction as ``"dfa"``, but materialised
      on demand.  Construction is linear like ``"nfa"``, and a step is a lookup
      like ``"dfa"`` once the state has been seen; only the states the run
      visits are ever built.

    All three prescribe the same actions on every history; only the cost profile
    differs.  A strategy already given as DFSTs
    (:class:`~strategy_monitor.strategies.NaturalRecallStrategy`) has no NFA to
    simulate, so it accepts ``"dfa"`` alone.
    """

    def __init__(self, cgs: CGS, strategy, determinize=True) -> None:
        super().__init__(cgs, strategy.coalition)
        self.strategy = strategy
        self.engine_name = resolve_recall_engine(determinize)
        self.determinize = self.engine_name == "dfa"
        alphabet = cgs.alphabet()
        builders = {
            "dfa": ProductDFSTEngine,
            "nfa": RegexNFAEngine,
            "lazy": LazyProductEngine,
        }
        self.engine: RecallEngine = builders[self.engine_name](strategy, alphabet)
        self._prescribed: Optional[Dict[str, str]] = None

    def _on_state(self, state: str) -> None:
        self._prescribed = self.engine.step(self.cgs.label(state))

    def _on_action(self, profile: JointAction) -> None:
        self._check_agents(profile, self._prescribed, (self.current_state,))

    # -- introspection ---------------------------------------------------

    @property
    def size(self) -> int:
        """Automaton states carried by the engine -- the construction cost."""
        return self.engine.size

    def describe(self) -> str:
        return self.engine.describe()

    def summary(self) -> Optional[str]:
        """Run-dependent cost, if the engine tracks any (the lazy one does)."""
        return self.engine.summary()


# ======================================================================
# strategy-adherence truth (Section 6.1)
# ======================================================================


class AdherenceMonitor(KBoundedMonitor):
    """``M^S_{Gamma_A}``: the ``k``-bounded monitor with the ``top^S_G`` verdict.

    Section 6.1 relativises strategy-adherence to the model.  Write
    ``W_G(s)`` for the windows still observable from ``s`` -- the length-``k``
    *paths of the CGS* whose first state is reachable from ``s`` -- and
    ``s_cur`` for the last observed state.  Then

        M^S(omega) = top^S_G   if W_G(s_cur) is contained in the windows
                               observed (and validated) so far,
                     M(omega)  otherwise.

    Only length-``k`` windows are obligations: a run has exactly one prefix of
    each length ``l < k``, so the shorter histories are checked for compliance
    as they arise but can never be enumerated.

    The data structure is the one of the proposition's proof, so the verdict
    test stays worst-case ``O(1)``:

    * ``Reach(s)`` for every state, precomputed by a traversal in
      ``O(|S| . |E|)``;
    * a bit-array over the length-``k`` block of the strategy table, ``O(|S|^k)``
      bits, marking the windows not yet validated;
    * ``c[t]``, the number of unvalidated windows beginning at ``t``;
    * ``n[s]``, the number of states in ``Reach(s)`` whose ``c`` is still
      positive.

    Validating a window clears its bit and decrements ``c`` at its first state,
    both ``O(1)``.  When some ``c[t]`` falls to zero, ``n[s]`` is decremented
    for every ``s`` that can reach ``t``: ``O(|S|)``, and at most ``|S|`` times
    over a whole run.  The verdict is then the test ``n[s_cur] == 0``.
    """

    def __init__(self, cgs: CGS, strategy: KBoundedStrategy, **kwargs) -> None:
        super().__init__(cgs, strategy, **kwargs)
        self.reach = reachable_from(cgs)
        self.obligations = model_windows(cgs, self.k)
        self.total_obligations = len(self.obligations)
        self.remaining = self.total_obligations

        self._pending = bytearray(self.index.capacity)
        self._c: Dict[str, int] = {state: 0 for state in cgs.states}
        for window in self.obligations:
            address = self.index.index_of(window)
            if not self._pending[address]:
                self._pending[address] = 1
                self._c[window[0]] += 1
        self._n: Dict[str, int] = {
            state: sum(1 for target in self.reach[state] if self._c[target] > 0)
            for state in cgs.states
        }

    # -- verdict ---------------------------------------------------------

    def _test_verdict(self) -> None:
        """``n[s_cur] == 0``: nothing still reachable is left unvalidated."""
        if self._verdict is not Verdict.UNKNOWN:
            return
        state = self.current_state
        if state is not None and self._n.get(state, 1) == 0:
            self._verdict = Verdict.TOP_S

    def _on_state(self, state: str) -> None:
        super()._on_state(state)
        self._test_verdict()

    def _on_action(self, profile: JointAction) -> None:
        before = len(self.violations)
        super()._on_action(profile)
        if len(self.violations) != before:
            return  # a deviation was found; do not validate this window
        window = self.index.window
        if len(window) == self.k:
            self._validate(window, self._current_index)
        self._test_verdict()

    def _validate(self, window: Window, address: int) -> None:
        if not (0 <= address < len(self._pending)) or not self._pending[address]:
            return
        self._pending[address] = 0
        self.remaining -= 1
        first = window[0]
        self._c[first] -= 1
        if self._c[first] == 0:
            for state in self.cgs.states:
                if first in self.reach[state]:
                    self._n[state] -= 1

    # -- diagnostics -----------------------------------------------------

    def outstanding(self) -> int:
        """``n[s_cur]`` -- how many still-reachable start states remain."""
        return self._n.get(self.current_state, 0) if self.current_state else self.total_obligations

    def pending_configurations(self) -> List[Window]:
        """Every window not yet validated. ``O(|S|^k)``; for reporting only."""
        return sorted(w for w in self.obligations if self._pending[self.index.index_of(w)])

    def pending_from(self, state: Optional[str] = None) -> List[Window]:
        """``W_G(state)`` minus what has been validated -- the real obligation."""
        state = state if state is not None else self.current_state
        if state is None:
            return self.pending_configurations()
        reachable = self.reach[state]
        return sorted(window for window in self.pending_configurations() if window[0] in reachable)


class NaturalMemorylessAdherenceMonitor(AdherenceMonitor):
    """``M^S`` for a natural memoryless strategy, via the Algorithm 1 reduction."""

    def __init__(self, cgs: CGS, strategy: NaturalMemorylessStrategy, strict: bool = True, **kwargs) -> None:
        self.natural_strategy = strategy
        super().__init__(cgs, strategy.to_kbounded(cgs, strict=strict), **kwargs)


def reachable_from(cgs: CGS) -> Dict[str, FrozenSet[str]]:
    """``Reach(s)`` for every state: the reflexive-transitive successor closure.

    Reflexive because the window beginning at the current state is certainly
    still observable.  One traversal per state, so ``O(|S| . |E|)`` in total.
    """
    reach: Dict[str, FrozenSet[str]] = {}
    for state in cgs.states:
        seen = {state}
        stack = [state]
        while stack:
            current = stack.pop()
            for successor in cgs.successors(current):
                if successor not in seen:
                    seen.add(successor)
                    stack.append(successor)
        reach[state] = frozenset(seen)
    return reach


def model_windows(cgs: CGS, k: int) -> Set[Window]:
    """The length-``k`` paths of the CGS -- the universe ``W_G`` ranges over.

    Most of ``S^k`` is not a path: in the running example only 7 of the 16
    elements of ``S^2`` are, which is why relativising the verdict matters.
    """
    windows: Set[Window] = {(state,) for state in cgs.states}
    for _ in range(k - 1):
        windows = {
            window + (successor,)
            for window in windows
            for successor in cgs.successors(window[-1])
        }
    return windows


def observable_windows(cgs: CGS, state: str, k: int) -> Set[Window]:
    """``W_G(s)``: length-``k`` paths of the CGS starting in ``Reach(s)``."""
    reachable = reachable_from(cgs)[state]
    return {window for window in model_windows(cgs, k) if window[0] in reachable}
