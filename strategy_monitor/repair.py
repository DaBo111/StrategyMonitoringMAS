"""Strategy repair -- Section 7.

The monitoring framework detects two kinds of failure, and each gets its own
repair branch:

* a **coalition strategy violation** (verdict ``bot``): some agent ``i in A``
  deviated.  The system is paused, ``i`` is excluded giving ``A' = A \\ {i}``,
  and synthesis is re-run for ``A'`` with the current state ``q_curr`` as the
  new initial state (Section 7.1).
* a **model violation** (the trace took a transition the CGS does not contain,
  which the goal monitor reports as ``bot^M``): the offending pair
  ``(s, alpha)`` and its actual successor ``s'`` are recorded, ``delta`` is
  replaced by ``delta'`` agreeing with ``delta`` everywhere except at
  ``(s, alpha)``, and synthesis is re-run on the updated model ``G'`` from
  ``q_curr`` (Section 7.2).

After either repair the monitors are rebuilt on the current model re-pointed at
``q_curr`` and execution resumes under them, which is the loop of Figure 7.
Both branches assume the system can be paused while re-synthesis runs; the
remark of Section 7 flags this as an assumption, and it is made explicit here as
the :attr:`RepairPipeline.paused` flag.  When no winning strategy remains there
is nothing left for the monitor to check, so monitoring stops and the failure is
reported.
"""

from __future__ import annotations

import logging

from dataclasses import dataclass
from enum import Enum
from typing import Callable, List, Optional, Sequence, Tuple

from .cgs import CGS, CGSError, JointAction
from .goal import GoalMonitor
from .monitors import StrategyMonitor
from .strategies import NaturalMemorylessStrategy
from .suite import MonitorSuite
from .trace import Trace
from .verdict import ModelDeviation, Verdict, Violation

logger = logging.getLogger(__name__)


class ViolationKind(Enum):
    COALITION = "coalition"
    MODEL = "model"


class RepairOutcome(Enum):
    NONE = "none"
    """No violation at this step."""

    COALITION_REPAIRED = "coalition-repaired"
    MODEL_REPAIRED = "model-repaired"
    FAILED = "failed"
    """No winning strategy remains; monitoring stops (Sections 7.1, 7.2)."""

    STOPPED = "stopped"
    """The pipeline had already given up before this step."""


@dataclass
class RepairEvent:
    """One pass through the repair pipeline of Figure 7."""

    step: int
    kind: ViolationKind
    outcome: RepairOutcome
    state: str
    detail: str
    excluded_agent: Optional[str] = None
    added_transition: Optional[Tuple[str, JointAction, str]] = None
    new_coalition: Optional[Tuple[str, ...]] = None
    new_strategy: Optional[NaturalMemorylessStrategy] = None

    def __str__(self) -> str:
        head = "step {0}: {1} violation at {2} -> {3}".format(
            self.step, self.kind.value, self.state, self.outcome.value
        )
        return head + ("\n    " + self.detail if self.detail else "")


Synthesiser = Callable[[CGS, Sequence[str], str], Optional[NaturalMemorylessStrategy]]
"""``(model, coalition, q_curr) -> strategy or None``."""


def vitamin_synthesiser(objective: str, k: int = 2, rename_idle: bool = True) -> Synthesiser:
    """A synthesiser backed by VITAMIN's NatATL memoryless model checker.

    ``objective`` is the ATL path formula the coalition must enforce, e.g.
    ``G(p || q)``.  It is deliberately separate from the LTL goal handed to the
    goal-oriented monitor: VITAMIN's ATL parser accepts only one temporal
    operator directly under the coalition modality, so the paper's
    ``G(p | (q & X p))`` cannot be used for synthesis even though it is exactly
    what ``M^G`` monitors.

    ``rename_idle`` (on by default) takes the idle action out of VITAMIN's prune
    allowance, so the search agrees with the truth over total natural memoryless
    strategies; see :func:`~strategy_monitor.vitamin.natatl_synthesize`.  The
    strategy is verified exactly either way, so one that does not really win is
    never adopted.
    """

    def synthesise(model: CGS, coalition: Sequence[str], q_curr: str):
        from .vitamin import natatl_synthesize

        if not coalition:
            return None
        result = natatl_synthesize(
            model.with_initial_state(q_curr),
            coalition,
            objective,
            k=k,
            rename_idle=rename_idle,
        )
        if result.satisfiable:
            return result.strategy
        if result.note:
            # A negative NatATL result does not always mean the coalition has
            # lost; say so rather than let the pipeline stop for the wrong reason.
            logger.warning("synthesis for %s from %s: %s", list(coalition), q_curr, result.note)
        return None

    return synthesise


def fixed_synthesiser(strategy: Optional[NaturalMemorylessStrategy]) -> Synthesiser:
    """A stub synthesiser returning a fixed strategy -- handy in tests and demos."""

    def synthesise(model: CGS, coalition: Sequence[str], q_curr: str):
        if strategy is None or tuple(coalition) != tuple(strategy.coalition):
            return None
        return strategy

    return synthesise


class RepairPipeline:
    """The loop of Figure 7: run, monitor, classify, repair, resume.

    The pipeline owns the model, the coalition and the current strategy, and
    rebuilds its :class:`~strategy_monitor.suite.MonitorSuite` whenever either
    changes.  Feed it the observed trace one step at a time with
    :meth:`observe`, or all at once with :meth:`run`.

    Both monitor components are optional, and the two repair branches follow
    whichever are present:

    * with a strategy, a deviation is attributed to an agent and the coalition
      branch of Section 7.1 runs;
    * with or without one, an observed transition the CGS does not contain
      triggers the model branch of Section 7.2 -- that check compares the
      successor against ``delta`` directly, so it needs neither the strategy
      monitor nor the goal monitor.

    A strategy of any of the three classes may be given; ``adherence`` and
    ``use_model`` are passed through to the suite, so the monitor being repaired
    is exactly the one the deployment wants.
    """

    def __init__(
        self,
        cgs: CGS,
        coalition: Optional[Sequence[str]] = None,
        strategy=None,
        synthesiser: Optional[Synthesiser] = None,
        goal: Optional[str] = None,
        adherence: bool = False,
        use_model: bool = True,
        strict: bool = False,
        determinize: bool = True,
    ) -> None:
        if strategy is None and goal is None:
            raise ValueError(
                "a repair pipeline needs something to monitor: a strategy, a goal, or both"
            )
        self.cgs = cgs
        self.strategy = strategy
        if coalition is not None:
            self.coalition = tuple(coalition)
        elif strategy is not None:
            self.coalition = tuple(strategy.coalition)
        else:
            self.coalition = ()
        self.synthesiser = synthesiser if synthesiser is not None else fixed_synthesiser(None)
        self.goal = goal
        self.adherence = adherence
        self.use_model = use_model
        self.strict = strict
        self.determinize = determinize

        self.events: List[RepairEvent] = []
        self.stopped = False
        self.paused = False
        self.step = 0
        self.current_state: Optional[str] = None
        self._previous_state: Optional[str] = None
        self._previous_action: Optional[JointAction] = None
        self._started = False

        self.suite: MonitorSuite = None
        self._rebuild()

    # -- monitor lifecycle ------------------------------------------------

    def _rebuild(self, restart_at: Optional[str] = None) -> None:
        """Re-derive the monitor suite from the current model, strategy and state."""
        model = self.cgs if restart_at is None else self.cgs.with_initial_state(restart_at)
        self.cgs = model
        self.suite = MonitorSuite.build(
            model,
            strategy=self.strategy,
            goal=self.goal,
            adherence=self.adherence,
            use_model=self.use_model,
            strict=self.strict,
            determinize=self.determinize,
        )
        self._started = False

    @property
    def monitor(self) -> Optional[StrategyMonitor]:
        """The strategy monitor component, or ``None`` when monitoring is goal-only."""
        return self.suite.strategy_monitor

    @property
    def goal_monitor(self) -> Optional[GoalMonitor]:
        """The goal monitor component, or ``None`` when monitoring is strategy-only."""
        return self.suite.goal_monitor

    # -- driving ----------------------------------------------------------

    def observe(self, state: str, profile: Optional[JointAction] = None) -> RepairOutcome:
        """Observe ``s_j``, then the action ``alpha_j`` played in it.

        A step is checked twice: first that the transition that produced
        ``state`` is one the model contains (Section 7.2), then that the action
        played in it follows the strategy (Section 7.1).  Both checks can fire
        in the same step -- a model repair leaves the system paused at
        ``q_curr``, so the action observed there is judged against whatever
        strategy the repair adopted.
        """
        if self.stopped:
            return RepairOutcome.STOPPED

        self.current_state = state
        outcome = RepairOutcome.NONE
        deviation = self._classify_transition(state)
        self._previous_state, self._previous_action = state, profile

        if deviation is not None:
            self.step += 1
            outcome = self._repair_model(deviation)
            if outcome is not RepairOutcome.MODEL_REPAIRED:
                return outcome
        self._feed_state(state)

        if profile is None:
            return outcome

        monitor = self.monitor
        before = len(monitor.violations) if monitor is not None else 0
        self.suite.observe_action(profile)
        if outcome is RepairOutcome.NONE:
            self.step += 1
        if monitor is not None and monitor.violations[before:]:
            return self._repair_coalition(monitor.violations[before:])
        return outcome

    def _feed_state(self, state: str) -> None:
        self.suite.observe_state(state)
        self._started = True

    def _resume_at(self, state: str) -> None:
        """Restart the rebuilt monitors at ``q_curr`` after a coalition repair.

        The deviating action has already been observed and acted on, so the
        monitor resumes with ``q_curr`` as its starting configuration and waits
        for the *next* step rather than for that action again.
        """
        self.suite.resume_at(state)
        self._started = True

    def run(self, trace: Trace) -> List[RepairEvent]:
        for state, action in trace.steps():
            self.observe(state, action)
        return self.events

    # -- violation classification ----------------------------------------

    def _classify_transition(self, state: str) -> Optional[ModelDeviation]:
        """Is the step that led to ``state`` a transition of the current model?"""
        if not self._started:
            if state != self.cgs.initial_state:
                return ModelDeviation(
                    step=self.step,
                    state=state,
                    profile=(),
                    observed_successor=state,
                    expected_successor=self.cgs.initial_state,
                    detail="the trace does not start in s_I",
                )
            return None
        if self._previous_action is None:
            return None
        try:
            expected = self.cgs.step(self._previous_state, self._previous_action)
        except CGSError:
            return ModelDeviation(
                step=self.step,
                state=self._previous_state,
                profile=tuple(self._previous_action),
                observed_successor=state,
                expected_successor=None,
                detail="the action profile is outside the protocol d",
            )
        if expected != state:
            return ModelDeviation(
                step=self.step,
                state=self._previous_state,
                profile=tuple(self._previous_action),
                observed_successor=state,
                expected_successor=expected,
                detail="the observed successor differs from delta",
            )
        return None

    # -- repair branches ---------------------------------------------------

    def _repair_coalition(self, violations: Sequence[Violation]) -> RepairOutcome:
        """Section 7.1: exclude the deviating agent and re-synthesise for ``A'``."""
        self.paused = True
        culprit = violations[0].agent
        detail = "; ".join(str(v) for v in violations)
        reduced = tuple(a for a in self.coalition if a != culprit)
        strategy = self._synthesise(reduced)
        if strategy is None:
            return self._give_up(
                ViolationKind.COALITION,
                self.current_state,
                detail
                + "\n    no winning strategy for {0} from {1}; monitoring stops".format(
                    list(reduced), self.current_state
                ),
                excluded_agent=culprit,
                new_coalition=reduced,
            )

        self.coalition = reduced
        self.strategy = strategy
        self._rebuild(restart_at=self.current_state)
        self.paused = False
        self._record(
            RepairEvent(
                step=self.step,
                kind=ViolationKind.COALITION,
                outcome=RepairOutcome.COALITION_REPAIRED,
                state=self.current_state,
                detail=detail,
                excluded_agent=culprit,
                new_coalition=reduced,
                new_strategy=strategy,
            )
        )
        self._resume_at(self.current_state)
        return RepairOutcome.COALITION_REPAIRED

    def _repair_model(self, deviation: ModelDeviation) -> RepairOutcome:
        """Section 7.2: absorb the observed transition into ``delta'``, then re-synthesise."""
        self.paused = True
        added = None
        if deviation.profile:
            self.cgs = self.cgs.with_transition(
                deviation.state, deviation.profile, deviation.observed_successor
            )
            added = (deviation.state, tuple(deviation.profile), deviation.observed_successor)

        if self.strategy is not None:
            strategy = self._synthesise(self.coalition)
            if strategy is None:
                return self._give_up(
                    ViolationKind.MODEL,
                    deviation.state,
                    str(deviation)
                    + "\n    no winning strategy on the updated model; monitoring stops",
                    added_transition=added,
                )
            self.strategy = strategy
        else:
            # Goal-only monitoring: there is no strategy to re-synthesise, so the
            # corrected model is simply adopted and the goal monitor rebuilt on it.
            strategy = None
        self._rebuild(restart_at=self.current_state)
        self.paused = False
        self._record(
            RepairEvent(
                step=self.step,
                kind=ViolationKind.MODEL,
                outcome=RepairOutcome.MODEL_REPAIRED,
                state=deviation.state,
                detail=str(deviation),
                added_transition=added,
                new_coalition=self.coalition,
                new_strategy=strategy,
            )
        )
        return RepairOutcome.MODEL_REPAIRED

    def _give_up(self, kind: ViolationKind, state: str, detail: str, **extra) -> RepairOutcome:
        self.stopped = True
        self.paused = False
        self._record(
            RepairEvent(
                step=self.step,
                kind=kind,
                outcome=RepairOutcome.FAILED,
                state=state,
                detail=detail,
                **extra,
            )
        )
        return RepairOutcome.FAILED

    def _synthesise(self, coalition: Sequence[str]) -> Optional[NaturalMemorylessStrategy]:
        if not coalition:
            return None
        return self.synthesiser(self.cgs, tuple(coalition), self.current_state)

    def _record(self, event: RepairEvent) -> None:
        self.events.append(event)

    # -- reporting ---------------------------------------------------------

    @property
    def verdict(self) -> Verdict:
        """The combined verdict of the monitor suite."""
        return self.suite.verdict

    @property
    def component_verdicts(self):
        """What each monitor component says separately."""
        return self.suite.component_verdicts

    def report(self) -> str:
        lines = ["Repair log ({0} event(s)):".format(len(self.events))]
        for event in self.events:
            lines.append("  " + str(event).replace("\n", "\n  "))
        lines.append(
            "  {0}; final coalition {1}; monitoring {2}".format(
                self.suite.describe(),
                list(self.coalition),
                "stopped" if self.stopped else "active",
            )
        )
        return "\n".join(lines)
