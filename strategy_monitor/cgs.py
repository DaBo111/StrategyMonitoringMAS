"""Concurrent Game Structures.

Implements Definition 1 of *Runtime Strategy Monitoring of Multi-agent Systems*:
a CGS is a tuple ``(Ap, Ag, S, {act_i}, d, delta, pi)`` in which the agents act
simultaneously and the joint action profile determines a unique successor.

The transition function is stored fully expanded (one entry per
``(state, joint action profile)`` pair), because the definition requires delta
to be a total deterministic function.  Model files may nonetheless be written
compactly with wildcard rules -- see :meth:`CGS.from_dict` -- which is how the
figures of the paper label their edges.
"""

from __future__ import annotations

import itertools
import json
from dataclasses import dataclass, field
from typing import Dict, FrozenSet, Iterator, List, Mapping, Sequence, Tuple

JointAction = Tuple[str, ...]
"""An action profile: one action per agent, in the order of ``CGS.agents``."""

WILDCARD = "*"


class CGSError(ValueError):
    """Raised when a model is not a well-formed concurrent game structure."""


@dataclass(frozen=True)
class TransitionRule:
    """One labelled edge of the drawn game structure.

    ``profiles`` lists action patterns; a pattern entry may be :data:`WILDCARD`,
    standing for any action available to that agent.  Rules are resolved in the
    order they are given (first match wins), which is what the figures mean when
    a state carries both a ``(*, *, in)`` and an ``(idle, *, *)`` edge.
    """

    target: str
    profiles: Tuple[Tuple[str, ...], ...]

    def matches(self, profile: JointAction) -> bool:
        for pattern in self.profiles:
            if len(pattern) != len(profile):
                continue
            if all(pat == WILDCARD or pat == act for pat, act in zip(pattern, profile)):
                return True
        return False


@dataclass(frozen=True)
class CGS:
    """A pointed concurrent game structure ``(G, s_I)``."""

    ap: Tuple[str, ...]
    agents: Tuple[str, ...]
    states: Tuple[str, ...]
    actions: Mapping[str, Tuple[str, ...]]
    protocol: Mapping[Tuple[str, str], FrozenSet[str]]
    transitions: Mapping[Tuple[str, JointAction], str]
    labelling: Mapping[str, FrozenSet[str]]
    initial_state: str
    _state_index: Dict[str, int] = field(default_factory=dict, repr=False, compare=False)

    # -- construction ----------------------------------------------------

    def __post_init__(self) -> None:
        object.__setattr__(self, "_state_index", {s: i for i, s in enumerate(self.states)})
        self.validate()

    def validate(self) -> None:
        """Check the structural requirements of Definition 1."""
        errors: List[str] = []
        if self.initial_state not in self._state_index:
            errors.append("initial state {0!r} is not a state".format(self.initial_state))
        if len(set(self.states)) != len(self.states):
            errors.append("duplicate state names")
        for agent in self.agents:
            if agent not in self.actions or not self.actions[agent]:
                errors.append("agent {0!r} has no actions".format(agent))
        for state in self.states:
            if state not in self.labelling:
                errors.append("state {0!r} has no labelling".format(state))
                continue
            unknown = set(self.labelling[state]) - set(self.ap)
            if unknown:
                errors.append(
                    "state {0!r} labelled with unknown propositions {1}".format(state, sorted(unknown))
                )
            for agent in self.agents:
                available = self.protocol.get((state, agent))
                # d(s, i) must be a non-empty subset of act_i.
                if not available:
                    errors.append("d({0!r}, {1!r}) is empty".format(state, agent))
                elif not set(available) <= set(self.actions.get(agent, ())):
                    errors.append("d({0!r}, {1!r}) is not a subset of act_{1}".format(state, agent))

        if not errors:
            # delta must be total and deterministic over the available profiles.
            for state in self.states:
                for profile in self.available_profiles(state):
                    target = self.transitions.get((state, profile))
                    if target is None:
                        errors.append("delta({0!r}, {1}) is undefined".format(state, profile))
                    elif target not in self._state_index:
                        errors.append(
                            "delta({0!r}, {1}) = {2!r} is not a state".format(state, profile, target)
                        )
        if errors:
            raise CGSError("invalid CGS:\n" + "\n".join("  - " + e for e in errors))

    # -- basic accessors -------------------------------------------------

    def index(self, state: str) -> int:
        """``id(s)`` of the paper: the direct-address index of a state."""
        try:
            return self._state_index[state]
        except KeyError:
            raise CGSError("unknown state {0!r}".format(state)) from None

    def label(self, state: str) -> FrozenSet[str]:
        """``pi(s)``."""
        return self.labelling[state]

    def available(self, state: str, agent: str) -> FrozenSet[str]:
        """``d(s, i)``."""
        return self.protocol[(state, agent)]

    def available_profiles(self, state: str) -> Iterator[JointAction]:
        """Every joint action allowed by the protocol in ``state``."""
        per_agent = [sorted(self.available(state, a)) for a in self.agents]
        return itertools.product(*per_agent)

    def step(self, state: str, profile: JointAction) -> str:
        """``delta(s, alpha)``; raises when the profile is not in the model."""
        try:
            return self.transitions[(state, tuple(profile))]
        except KeyError:
            raise CGSError(
                "delta({0!r}, {1}) is not defined in the model".format(state, tuple(profile))
            ) from None

    def successors(self, state: str) -> FrozenSet[str]:
        """States reachable in one step, forgetting which profile got there."""
        return frozenset(self.transitions[(state, p)] for p in self.available_profiles(state))

    def reachable_states(self) -> FrozenSet[str]:
        """States reachable from ``s_I``."""
        seen = {self.initial_state}
        stack = [self.initial_state]
        while stack:
            current = stack.pop()
            for nxt in self.successors(current):
                if nxt not in seen:
                    seen.add(nxt)
                    stack.append(nxt)
        return frozenset(seen)

    def agent_index(self, agent: str) -> int:
        return self.agents.index(agent)

    def project(self, profile: JointAction, coalition: Sequence[str]) -> JointAction:
        """``alpha^A``: the profile restricted to the agents of the coalition."""
        return tuple(profile[self.agent_index(a)] for a in coalition)

    def alphabet(self) -> Tuple[FrozenSet[str], ...]:
        """``2^Ap`` -- the input alphabet of the automata of Section 6.2."""
        letters = []
        for size in range(len(self.ap) + 1):
            for combo in itertools.combinations(self.ap, size):
                letters.append(frozenset(combo))
        return tuple(letters)

    # -- model repair (Section 7.2) --------------------------------------

    def with_transition(self, state: str, profile: JointAction, target: str) -> "CGS":
        """``delta'`` of Section 7.2: redirect one state/profile pair.

        Returns a new CGS; the receiver is untouched.  ``target`` and any action
        of ``profile`` the protocol did not allow are added to the model, so an
        observed-but-unmodelled transition can always be absorbed.
        """
        profile = tuple(profile)
        states = self.states if target in self._state_index else self.states + (target,)
        labelling = dict(self.labelling)
        labelling.setdefault(target, frozenset())

        actions = {a: tuple(v) for a, v in self.actions.items()}
        protocol = {k: frozenset(v) for k, v in self.protocol.items()}
        for agent, action in zip(self.agents, profile):
            if action not in actions[agent]:
                actions[agent] = actions[agent] + (action,)
            key = (state, agent)
            protocol[key] = protocol.get(key, frozenset()) | {action}

        transitions = dict(self.transitions)
        # A new state, or newly permitted actions, leave delta partial; complete
        # it with self-loops so the result is still a total function.
        for new_state in set(states) - set(self.states):
            for agent in self.agents:
                protocol.setdefault((new_state, agent), frozenset(actions[agent]))
        for candidate in states:
            per_agent = [sorted(protocol[(candidate, a)]) for a in self.agents]
            for prof in itertools.product(*per_agent):
                transitions.setdefault((candidate, prof), candidate)
        transitions[(state, profile)] = target

        return CGS(
            ap=self.ap,
            agents=self.agents,
            states=states,
            actions=actions,
            protocol=protocol,
            transitions=transitions,
            labelling=labelling,
            initial_state=self.initial_state,
        )

    def with_initial_state(self, state: str) -> "CGS":
        """Re-point the structure at ``q_curr`` (used before re-synthesis)."""
        if state not in self._state_index:
            raise CGSError("unknown state {0!r}".format(state))
        return CGS(
            ap=self.ap,
            agents=self.agents,
            states=self.states,
            actions=self.actions,
            protocol=self.protocol,
            transitions=self.transitions,
            labelling=self.labelling,
            initial_state=state,
        )

    # -- serialisation ---------------------------------------------------

    @classmethod
    def from_dict(cls, data: Mapping) -> "CGS":
        """Build a CGS from the compact JSON form.

        ``states[i]["transitions"]`` is an ordered list of rules; the first rule
        whose pattern matches a profile fixes the successor for that profile, so
        a state can be described the way it is drawn::

            {"id": "s0", "labels": ["p", "q"], "transitions": [
                {"to": "s0", "profiles": [["*", "*", "in"]]},
                {"to": "s1", "profiles": [["in", "in", "out"],
                                          ["in", "out", "out"],
                                          ["out", "in", "out"]]},
                {"to": "s2", "profiles": [["*", "*", "*"]]}]}
        """
        ap = tuple(data["ap"])
        agents = tuple(data["agents"])
        actions = {a: tuple(data["actions"][a]) for a in agents}
        state_entries = list(data["states"])
        states = tuple(entry["id"] for entry in state_entries)

        labelling: Dict[str, FrozenSet[str]] = {}
        protocol: Dict[Tuple[str, str], FrozenSet[str]] = {}
        transitions: Dict[Tuple[str, JointAction], str] = {}
        unmatched: List[str] = []
        shadowed: List[str] = []

        for entry in state_entries:
            state = entry["id"]
            labelling[state] = frozenset(entry.get("labels", []))
            per_agent_available = entry.get("available", {})
            for agent in agents:
                protocol[(state, agent)] = frozenset(per_agent_available.get(agent, actions[agent]))

            rules = [
                TransitionRule(target=rule["to"], profiles=tuple(tuple(p) for p in rule["profiles"]))
                for rule in entry.get("transitions", [])
            ]
            used = [False] * len(rules)
            per_agent = [sorted(protocol[(state, a)]) for a in agents]
            for profile in itertools.product(*per_agent):
                for position, rule in enumerate(rules):
                    if rule.matches(profile):
                        transitions[(state, profile)] = rule.target
                        used[position] = True
                        break
                else:
                    unmatched.append("{0}: {1}".format(state, profile))
            for position, was_used in enumerate(used):
                if not was_used:
                    shadowed.append(
                        "{0} -> {1} (rule {2})".format(state, rules[position].target, position)
                    )

        if unmatched:
            raise CGSError(
                "delta is not total; no rule covers:\n"
                + "\n".join("  - " + u for u in unmatched[:20])
                + ("\n  ..." if len(unmatched) > 20 else "")
            )
        cgs = cls(
            ap=ap,
            agents=agents,
            states=states,
            actions=actions,
            protocol=protocol,
            transitions=transitions,
            labelling=labelling,
            initial_state=data["initial_state"],
        )
        object.__setattr__(cgs, "shadowed_rules", tuple(shadowed))
        return cgs

    @classmethod
    def from_json(cls, path: str) -> "CGS":
        with open(path, encoding="utf-8") as handle:
            return cls.from_dict(json.load(handle))

    def to_dict(self) -> Dict:
        """Serialise with one rule per (target, profile) -- lossless, not compact."""
        entries = []
        for state in self.states:
            by_target: Dict[str, List[List[str]]] = {}
            for profile in self.available_profiles(state):
                by_target.setdefault(self.step(state, profile), []).append(list(profile))
            entries.append(
                {
                    "id": state,
                    "labels": sorted(self.labelling[state]),
                    "available": {a: sorted(self.available(state, a)) for a in self.agents},
                    "transitions": [
                        {"to": target, "profiles": profiles} for target, profiles in by_target.items()
                    ],
                }
            )
        return {
            "ap": list(self.ap),
            "agents": list(self.agents),
            "actions": {a: list(v) for a, v in self.actions.items()},
            "initial_state": self.initial_state,
            "states": entries,
        }

    def to_json(self, path: str) -> None:
        with open(path, "w", encoding="utf-8") as handle:
            json.dump(self.to_dict(), handle, indent=2)

    def __str__(self) -> str:  # pragma: no cover - display helper
        lines = [
            "CGS  Ap={0}  Ag={1}  |S|={2}  s_I={3}".format(
                set(self.ap), list(self.agents), len(self.states), self.initial_state
            )
        ]
        for state in self.states:
            label = "{" + ", ".join(sorted(self.labelling[state])) + "}"
            targets = ", ".join(sorted(self.successors(state)))
            lines.append("  {0}  pi={1:<10} -> {2}".format(state, label, targets))
        return "\n".join(lines)
