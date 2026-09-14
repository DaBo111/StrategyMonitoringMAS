"""The goal-oriented monitor ``M^G`` of Section 6.2.

The construction follows the paper step by step:

1. translate the goal ``phi`` and its negation into Buchi automata
   ``A^phi`` and ``A^{!phi}``;
2. read the pointed CGS as a Buchi automaton ``A_T = (S, 2^Ap, delta_hat, s_I, S)``
   in which every state is accepting and the edge ``s -> s'`` carries ``pi(s)``;
3. intersect, giving ``A_T^phi`` and ``A_T^{!phi}``;
4. take prefix NFAs and determinise them into ``DFA^phi`` and ``DFA^{!phi}``;
5. run the product finite-state machine, labelled by

       lambda(q, q') = top^G  if q in F^phi  and q' not in F^{!phi}
                       bot^G  if q not in F^phi and q' in F^{!phi}
                       bot^M  if q not in F^phi and q' not in F^{!phi}
                       ?      otherwise

Because the automata are intersected with the model, a state pair in which
*neither* component can be extended is reachable exactly when the observed word
is not the labelling of any run of the CGS -- so model violation detection comes
for free, as the paper notes.
"""

from __future__ import annotations

from dataclasses import dataclass
from typing import Dict, FrozenSet, List, Sequence, Tuple

from .automata import (
    Buchi,
    DFA,
    Letter,
    buchi_product,
    determinize,
    prefix_nfa,
)
from .cgs import CGS
from .ltl import LTL, Neg, formula_of, ltl_to_buchi
from .trace import Trace
from .verdict import Verdict


def cgs_to_buchi(cgs: CGS) -> Buchi:
    """``A_T`` of Section 6.2: the CGS read as a Buchi automaton.

    One state per state of the CGS, every state accepting, and an edge
    ``s -> s'`` labelled ``pi(s)`` for every ``s'`` the model can reach from
    ``s`` in one step.  The automaton therefore accepts exactly the labellings
    ``pi(s_0) pi(s_1) ...`` of the infinite runs of the model.
    """
    letters = cgs.alphabet()
    transitions: Dict[Tuple[str, Letter], FrozenSet[str]] = {}
    for state in cgs.states:
        successors = cgs.successors(state)
        if successors:
            transitions[(state, cgs.label(state))] = frozenset(successors)
    return Buchi(
        states=list(cgs.states),
        alphabet=letters,
        transitions=transitions,
        initial=frozenset({cgs.initial_state}),
        accepting=frozenset(cgs.states),
    )


@dataclass
class GoalMonitorTables:
    """The two determinised prefix automata the monitor runs on."""

    positive: DFA
    negative: DFA
    alphabet: Tuple[Letter, ...]


class GoalMonitor:
    """``M^G``: a four-valued monitor for an LTL goal, refined by the model.

    Set ``use_model=False`` to obtain the plain LTL monitor of Bauer et al.,
    built from ``A^phi`` and ``A^{!phi}`` alone.  Comparing the two is what the
    example of Section 6.2 does: on the running example the unrefined monitor
    can never answer ``top``, while the refined one does.
    """

    def __init__(self, cgs: CGS, goal, use_model: bool = True) -> None:
        self.cgs = cgs
        self.goal: LTL = formula_of(goal)
        self.use_model = use_model
        self.alphabet = cgs.alphabet()

        positive_buchi = ltl_to_buchi(self.goal, self.alphabet)
        negative_buchi = ltl_to_buchi(Neg(self.goal), self.alphabet)
        self.model_buchi = cgs_to_buchi(cgs) if use_model else None
        if use_model:
            positive_buchi = buchi_product(positive_buchi, self.model_buchi, right_all_accepting=True)
            negative_buchi = buchi_product(negative_buchi, self.model_buchi, right_all_accepting=True)
        self.positive_buchi = positive_buchi
        self.negative_buchi = negative_buchi

        self.tables = GoalMonitorTables(
            positive=determinize(prefix_nfa(positive_buchi)),
            negative=determinize(prefix_nfa(negative_buchi)),
            alphabet=self.alphabet,
        )
        self.reset()

    # -- running ---------------------------------------------------------

    def reset(self) -> None:
        self.positive_state = self.tables.positive.initial
        self.negative_state = self.tables.negative.initial
        self.step_count = 0
        self._verdict = self._label(self.positive_state, self.negative_state)

    @property
    def verdict(self) -> Verdict:
        return self._verdict

    def _label(self, positive, negative) -> Verdict:
        """``lambda`` of Section 6.2."""
        in_positive = positive in self.tables.positive.accepting
        in_negative = negative in self.tables.negative.accepting
        if in_positive and not in_negative:
            return Verdict.TOP_G
        if not in_positive and in_negative:
            return Verdict.BOT_G
        if not in_positive and not in_negative:
            return Verdict.BOT_M
        return Verdict.UNKNOWN

    def observe_letter(self, letter: Letter) -> Verdict:
        """Read one letter of ``pi(omega_s)``."""
        self.positive_state = self.tables.positive.step(self.positive_state, letter)
        self.negative_state = self.tables.negative.step(self.negative_state, letter)
        self.step_count += 1
        self._verdict = self._label(self.positive_state, self.negative_state)
        return self._verdict

    def observe_state(self, state: str) -> Verdict:
        """Read ``pi(s)`` for an observed state of the system."""
        return self.observe_letter(self.cgs.label(state))

    def observe(self, state: str, profile=None) -> Verdict:
        """Signature-compatible with the strategy monitors; the action is ignored."""
        return self.observe_state(state)

    def run(self, trace: Trace) -> Verdict:
        for state in trace.states:
            self.observe_state(state)
        return self._verdict

    def evaluate(self, word: Sequence[Letter]) -> Verdict:
        """``M^G(w) = lambda(delta(q_0, pi(w_s)))`` on a complete word."""
        self.reset()
        for letter in word:
            self.observe_letter(letter)
        return self._verdict

    def verdicts(self, trace: Trace) -> List[Verdict]:
        """The verdict after each state of the trace, starting from the empty word."""
        self.reset()
        out = [self._verdict]
        for state in trace.states:
            out.append(self.observe_state(state))
        return out

    # -- reporting -------------------------------------------------------

    def sizes(self) -> Dict[str, int]:
        return {
            "positive_buchi": len(self.positive_buchi.states),
            "negative_buchi": len(self.negative_buchi.states),
            "positive_dfa": len(self.tables.positive.states),
            "negative_dfa": len(self.tables.negative.states),
            "product_states": len(self.tables.positive.states) * len(self.tables.negative.states),
        }
