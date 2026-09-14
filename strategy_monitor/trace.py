"""Observed system evolutions.

Section 5.2 fixes the trace semantics used throughout the paper::

    omega = s_0 alpha_0 s_1 alpha_1 ...

the system starts in ``s_0``, all agents play ``alpha_0``, the system moves to
``s_1``, and so on.  ``omega_s`` is the state projection and ``omega_alpha`` the
action projection, with ``|omega| = 2 |omega_alpha| + 1``.
"""

from __future__ import annotations

import json
from dataclasses import dataclass, field
from typing import Iterator, List, Optional, Sequence, Tuple

from .cgs import CGS, CGSError, JointAction


@dataclass
class Trace:
    """A finite observation ``s_0 alpha_0 s_1 alpha_1 ...``.

    A trace holds ``n`` states and either ``n - 1`` or ``n`` action profiles; the
    latter is a trace whose last action has been observed but whose resulting
    state has not (the form used in the example of Section 6.2).
    """

    states: List[str] = field(default_factory=list)
    actions: List[JointAction] = field(default_factory=list)

    def __post_init__(self) -> None:
        if self.actions and not self.states:
            raise ValueError("a trace with actions must have at least one state")
        if not (len(self.states) - 1 <= len(self.actions) <= len(self.states)):
            raise ValueError(
                "a trace has |states| - 1 or |states| actions, got {0} states and {1} actions".format(
                    len(self.states), len(self.actions)
                )
            )

    # -- paper notation --------------------------------------------------

    def __len__(self) -> int:
        """``|omega| = |omega_s| + |omega_alpha|``."""
        return len(self.states) + len(self.actions)

    @property
    def state_projection(self) -> Tuple[str, ...]:
        """``omega_s``."""
        return tuple(self.states)

    @property
    def action_projection(self) -> Tuple[JointAction, ...]:
        """``omega_alpha``."""
        return tuple(self.actions)

    def steps(self) -> Iterator[Tuple[str, Optional[JointAction]]]:
        """Yield ``(s_j, alpha_j)`` pairs; the action is ``None`` for a dangling state."""
        for position, state in enumerate(self.states):
            yield state, self.actions[position] if position < len(self.actions) else None

    def word(self, cgs: CGS) -> Tuple[frozenset, ...]:
        """``pi(omega_s) = pi(s_0) pi(s_1) ...`` -- the input of the goal monitor."""
        return tuple(cgs.label(s) for s in self.states)

    # -- construction ----------------------------------------------------

    def extend(self, state: str, action: Optional[JointAction] = None) -> "Trace":
        """Append one observation, in place, and return self."""
        if len(self.actions) < len(self.states):
            raise ValueError("the previous step has no action yet; call act() first")
        self.states.append(state)
        if action is not None:
            self.actions.append(tuple(action))
        return self

    def act(self, action: JointAction) -> "Trace":
        """Record the action taken in the current (last) state."""
        if len(self.actions) >= len(self.states):
            raise ValueError("the current state already has an action")
        self.actions.append(tuple(action))
        return self

    # -- model conformance -----------------------------------------------

    def check_against(self, cgs: CGS) -> List[str]:
        """Return the ways this trace violates the CGS (Eq. 3 of Section 5.2).

        An empty list means the trace is a legal evolution of the model: it
        starts in ``s_I``, only uses actions the protocol allows, and follows
        ``delta`` at every step.  A non-empty list is a *model violation*, which
        Section 7.2 repairs.
        """
        problems: List[str] = []
        if not self.states:
            return problems
        if self.states[0] != cgs.initial_state:
            problems.append(
                "omega_s[0] = {0!r} but s_I = {1!r}".format(self.states[0], cgs.initial_state)
            )
        for position, action in enumerate(self.actions):
            state = self.states[position]
            if state not in cgs.states:
                problems.append("omega_s[{0}] = {1!r} is not a state".format(position, state))
                continue
            if len(action) != len(cgs.agents):
                problems.append(
                    "omega_alpha[{0}] has {1} actions for {2} agents".format(
                        position, len(action), len(cgs.agents)
                    )
                )
                continue
            for agent, chosen in zip(cgs.agents, action):
                if chosen not in cgs.available(state, agent):
                    problems.append(
                        "omega_alpha[{0}][{1}] = {2!r} is not in d({3!r}, {1!r})".format(
                            position, agent, chosen, state
                        )
                    )
            if position + 1 < len(self.states):
                try:
                    expected = cgs.step(state, action)
                except CGSError:
                    problems.append(
                        "delta({0!r}, {1}) is not in the model".format(state, tuple(action))
                    )
                    continue
                observed = self.states[position + 1]
                if expected != observed:
                    problems.append(
                        "delta({0!r}, {1}) = {2!r} but omega_s[{3}] = {4!r}".format(
                            state, tuple(action), expected, position + 1, observed
                        )
                    )
        return problems

    # -- serialisation ---------------------------------------------------

    @classmethod
    def from_dict(cls, data) -> "Trace":
        return cls(
            states=list(data.get("states", [])),
            actions=[tuple(a) for a in data.get("actions", [])],
        )

    @classmethod
    def from_json(cls, path: str) -> "Trace":
        with open(path, encoding="utf-8") as handle:
            return cls.from_dict(json.load(handle))

    def to_dict(self):
        return {"states": list(self.states), "actions": [list(a) for a in self.actions]}

    def __str__(self) -> str:  # pragma: no cover - display helper
        chunks: List[str] = []
        for state, action in self.steps():
            chunks.append(state)
            if action is not None:
                chunks.append("(" + ",".join(action) + ")")
        return " ".join(chunks)


def replay(cgs: CGS, actions: Sequence[JointAction], start: Optional[str] = None) -> Trace:
    """Run a sequence of joint actions through the model and record the trace."""
    current = start if start is not None else cgs.initial_state
    trace = Trace(states=[current])
    for action in actions:
        trace.act(action)
        current = cgs.step(current, action)
        trace.states.append(current)
    return trace
