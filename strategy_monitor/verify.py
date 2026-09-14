"""Checking that a strategy actually enforces a goal.

Given a coalition strategy and an LTL goal, this answers: does *every* run in
which the coalition follows the strategy satisfy the goal, whatever the other
agents do?  That is the question strategy synthesis is supposed to answer, and
the one the repair procedure of Section 7 asks before adopting a replacement.

The check restricts the CGS to the strategy -- ``d(s, a)`` becomes exactly the
prescribed action for each coalition member, and is left alone for everyone
else -- and then model-checks the goal on the result.  It reuses the automata of
Section 6.2, so it needs nothing beyond this package:

* the restricted model becomes a Buchi automaton (every state accepting);
* the *negated* goal becomes a Buchi automaton;
* the goal holds on every run iff their product is empty, and a non-empty
  product yields a counterexample lasso.

Two consequences are worth stating.  It is exact -- no idling is smuggled in, so
it neither over- nor under-approximates the strategy -- and it takes the full
LTL grammar, including the nested ``X`` that VITAMIN's ATL parser rejects.  So
the paper's own goal ``G(p | (q & X p))`` can be checked directly, rather than
being weakened to something ATL can express.
"""

from __future__ import annotations

import itertools
from dataclasses import dataclass
from typing import Dict, List, Optional, Tuple

from .automata import buchi_lasso, buchi_product
from .cgs import CGS
from .goal import cgs_to_buchi
from .ltl import Neg, formula_of, ltl_to_buchi
from .strategies import (
    KBoundedStrategy,
    NaturalMemorylessStrategy,
    NaturalRecallRegexStrategy,
    NaturalRecallStrategy,
    StrategyError,
)


@dataclass
class Verdict:
    """Whether a strategy enforces a goal, and a counterexample if it does not."""

    holds: bool
    goal: str
    coalition: Tuple[str, ...]
    counterexample: Optional[Tuple[List[str], List[str]]] = None
    """``(prefix, loop)`` states of a run that follows the strategy and fails the goal."""

    reachable: Tuple[str, ...] = ()
    """States the strategy can still reach -- usually far fewer than ``S``."""

    def __bool__(self) -> bool:
        return self.holds

    def __str__(self) -> str:
        if self.holds:
            return "{0} enforces {1} (reachable under it: {2})".format(
                list(self.coalition), self.goal, list(self.reachable)
            )
        prefix, loop = self.counterexample or ([], [])
        return "{0} does NOT enforce {1}; counterexample {2}({3})^omega".format(
            list(self.coalition), self.goal, " ".join(prefix), " ".join(loop)
        )


def prescribed_actions(cgs: CGS, strategy) -> Dict[str, Dict[str, str]]:
    """``state -> agent -> action`` for a memoryless strategy.

    Raises when the strategy has memory, or leaves a *reachable* state
    unprescribed.  Section 5.3 defines a strategy as a function, but a gate list
    that is silent on states no compliant run ever visits still determines every
    run there is, so it is accepted and the unreachable entries are filled in.
    """
    if isinstance(strategy, NaturalMemorylessStrategy):
        # Not strict: a gate list that is silent somewhere is only a problem if
        # the strategy can actually reach that state, which the walk below decides.
        table = strategy.to_kbounded(cgs, strict=False)
    elif isinstance(strategy, KBoundedStrategy):
        if strategy.k != 1:
            raise StrategyError(
                "exact verification is implemented for memoryless strategies; this one "
                "has k = {0}, whose restricted system is a product with the strategy's "
                "memory".format(strategy.k)
            )
        table = strategy
    elif isinstance(strategy, (NaturalRecallStrategy, NaturalRecallRegexStrategy)):
        raise StrategyError(
            "exact verification is implemented for memoryless strategies; a recall "
            "strategy would have to be producted with its transducer first"
        )
    else:
        raise StrategyError("cannot verify {0!r}".format(type(strategy).__name__))

    # Walk from s_I through the prescribed actions only.  A state the strategy
    # does not prescribe matters exactly when the strategy can reach it: an
    # unprescribed state that no compliant run visits cannot affect any run, so
    # a witness that is silent there is still usable.
    out: Dict[str, Dict[str, str]] = {}
    reached = {cgs.initial_state}
    frontier = [cgs.initial_state]
    while frontier:
        state = frontier.pop()
        prescription = table.prescribe((state,))
        if not prescription or any(
            prescription.get(agent) is None for agent in strategy.coalition
        ):
            raise StrategyError(
                "the strategy prescribes nothing in {0!r}, which it can reach; a "
                "strategy undefined on a state it visits is not a function".format(state)
            )
        out[state] = dict(prescription)
        for profile in _compliant_profiles(cgs, state, strategy.coalition, out[state]):
            successor = cgs.step(state, profile)
            if successor not in reached:
                reached.add(successor)
                frontier.append(successor)

    # Unreachable states still need an entry so that delta stays total; any
    # available action will do, since no compliant run ever gets there.
    for state in cgs.states:
        if state in out:
            continue
        prescription = table.prescribe((state,)) or {}
        out[state] = {
            agent: prescription.get(agent) or sorted(cgs.available(state, agent))[0]
            for agent in strategy.coalition
        }
    return out


def _compliant_profiles(cgs: CGS, state: str, coalition, prescription):
    """Profiles in which the coalition plays its prescription and others are free."""
    per_agent = [
        [prescription[agent]] if agent in coalition else sorted(cgs.available(state, agent))
        for agent in cgs.agents
    ]
    return itertools.product(*per_agent)


def restrict(cgs: CGS, strategy) -> CGS:
    """The model in which the coalition plays exactly its strategy.

    ``d(s, a)`` is narrowed to the single prescribed action for each coalition
    member and left untouched for the others, so every run of the result is a
    run of ``cgs`` in which the coalition complies -- and every such run of
    ``cgs`` is a run of the result.  ``delta`` stays total, so no state becomes
    a dead end.
    """
    table = prescribed_actions(cgs, strategy)
    coalition = set(strategy.coalition)
    entries = []
    for state in cgs.states:
        available = {
            agent: [table[state][agent]] if agent in coalition else sorted(cgs.available(state, agent))
            for agent in cgs.agents
        }
        transitions = [
            {"to": cgs.step(state, profile), "profiles": [list(profile)]}
            for profile in itertools.product(*[available[a] for a in cgs.agents])
        ]
        entries.append(
            {
                "id": state,
                "labels": sorted(cgs.label(state)),
                "available": available,
                "transitions": transitions,
            }
        )
    return CGS.from_dict(
        {
            "ap": list(cgs.ap),
            "agents": list(cgs.agents),
            "actions": {a: list(v) for a, v in cgs.actions.items()},
            "initial_state": cgs.initial_state,
            "states": entries,
        }
    )


def enforces(cgs: CGS, strategy, goal) -> Verdict:
    """Does every run following ``strategy`` satisfy the LTL ``goal``?

    Exact: the coalition is held to the strategy and nothing else is assumed.
    The other agents keep every move the protocol allows, so a positive answer
    means the goal is enforced against any behaviour of theirs.
    """
    restricted = restrict(cgs, strategy)
    formula = formula_of(goal)
    alphabet = restricted.alphabet()
    counterexamples = buchi_product(
        ltl_to_buchi(Neg(formula), alphabet),
        cgs_to_buchi(restricted),
        right_all_accepting=True,
    )
    lasso = buchi_lasso(counterexamples)
    coalition = tuple(strategy.coalition)
    reachable = tuple(sorted(restricted.reachable_states()))
    if lasso is None:
        return Verdict(True, str(formula), coalition, None, reachable)
    # Product states are (formula state, model state); the run names itself.
    prefix = [state[1] for state in lasso.prefix_states]
    loop = [state[1] for state in lasso.loop_states]
    return Verdict(False, str(formula), coalition, (prefix, loop), reachable)

