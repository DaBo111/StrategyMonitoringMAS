"""Composing a runtime monitor from the paper's components.

The paper's monitors are independent pieces, and a deployment may want any
subset of them:

* a **strategy monitor** over a ``k``-bounded, natural memoryless, or natural
  recall strategy (Sections 5.2, 5.4, 5.5), optionally with the
  strategy-adherence verdict ``top^S_G`` of Section 6.1;
* a **goal monitor** for an LTL goal (Section 6.2), either the plain monitor of
  Bauer et al. or the one refined by intersecting with the CGS.

:class:`MonitorSuite` runs whichever components it is given and reports one
verdict.  Both are optional, so the suite covers strategy-only monitoring,
goal-only monitoring (which still detects model violations when refined), and
any combination.  The repair pipeline of Section 7 is built on top of it, which
is what lets repair run with only one of the two branches active.
"""

from __future__ import annotations

from typing import Dict, List, Optional, Sequence

from .cgs import CGS, JointAction
from .goal import GoalMonitor
from .monitors import (
    AdherenceMonitor,
    KBoundedMonitor,
    NaturalMemorylessAdherenceMonitor,
    NaturalMemorylessMonitor,
    NaturalRecallMonitor,
    StrategyMonitor,
)
from .strategies import (
    KBoundedStrategy,
    NaturalMemorylessStrategy,
    NaturalRecallRegexStrategy,
    NaturalRecallStrategy,
    StrategyError,
)
from .trace import Trace
from .verdict import Verdict, Violation

PRECEDENCE = (
    Verdict.BOT_M,
    Verdict.BOT,
    Verdict.BOT_G,
    Verdict.TOP_G,
    Verdict.TOP_S,
)
"""Order in which a single verdict is chosen from the components.

Model violation first: if the observation is not a run of the CGS at all, the
strategy monitor's memory bookkeeping and the goal automata are both reasoning
about something the system is no longer doing.  Then the strategy violation,
which Section 7.1 can act on, then the goal violation.  Among the positive
verdicts the goal guarantee is reported ahead of strategy adherence.  Use
:attr:`MonitorSuite.component_verdicts` when the full picture is wanted.
"""


def build_strategy_monitor(
    cgs: CGS,
    strategy,
    adherence: bool = False,
    strict: bool = True,
    determinize: bool = True,
    **kwargs,
) -> StrategyMonitor:
    """Pick the monitor construction that fits the strategy class.

    ``adherence`` selects the ``top^S_G`` variant of Section 6.1, which is
    defined for ``k``-bounded and natural memoryless strategies; the paper
    leaves the recall case for future work, so asking for it raises.

    ``determinize`` only reaches the recall monitor, where it chooses between
    building the product DFST up front and simulating the regexes' NFAs at
    runtime.
    """
    if isinstance(strategy, (NaturalRecallStrategy, NaturalRecallRegexStrategy)):
        if adherence:
            raise StrategyError(
                "the strategy-adherence verdict is defined for k-bounded and natural "
                "memoryless strategies only (Section 6.1); recall is left for future work"
            )
        return NaturalRecallMonitor(cgs, strategy, determinize=determinize)
    if isinstance(strategy, NaturalMemorylessStrategy):
        if adherence:
            return NaturalMemorylessAdherenceMonitor(cgs, strategy, strict=strict, **kwargs)
        return NaturalMemorylessMonitor(cgs, strategy, strict=strict, **kwargs)
    if isinstance(strategy, KBoundedStrategy):
        if adherence:
            return AdherenceMonitor(cgs, strategy, **kwargs)
        return KBoundedMonitor(cgs, strategy, **kwargs)
    raise StrategyError("cannot monitor {0!r}".format(type(strategy).__name__))


class MonitorSuite:
    """A runtime monitor assembled from any subset of the paper's components."""

    def __init__(
        self,
        strategy_monitor: Optional[StrategyMonitor] = None,
        goal_monitor: Optional[GoalMonitor] = None,
    ) -> None:
        if strategy_monitor is None and goal_monitor is None:
            raise ValueError(
                "a monitor suite needs at least one component: a strategy monitor, "
                "a goal monitor, or both"
            )
        self.strategy_monitor = strategy_monitor
        self.goal_monitor = goal_monitor
        self.step_count = 0

    # -- construction ----------------------------------------------------

    @classmethod
    def build(
        cls,
        cgs: CGS,
        strategy=None,
        goal=None,
        adherence: bool = False,
        use_model: bool = True,
        strict: bool = True,
        determinize: bool = True,
        **kwargs,
    ) -> "MonitorSuite":
        """Assemble a suite from a model and whichever ingredients are supplied.

        ``strategy`` may be any of the three strategy classes -- written by
        hand, loaded from a file, or synthesised by VITAMIN, since
        :func:`~strategy_monitor.vitamin.natatl_synthesize` returns an ordinary
        :class:`~strategy_monitor.strategies.NaturalMemorylessStrategy`.
        ``goal`` is an LTL formula; ``use_model`` chooses between the refined
        monitor of Section 6.2 and the plain LTL monitor.  ``determinize``
        chooses the recall engine.  Passing ``None`` for either component leaves
        it out.
        """
        strategy_monitor = (
            build_strategy_monitor(
                cgs,
                strategy,
                adherence=adherence,
                strict=strict,
                determinize=determinize,
                **kwargs,
            )
            if strategy is not None
            else None
        )
        goal_monitor = GoalMonitor(cgs, goal, use_model=use_model) if goal is not None else None
        return cls(strategy_monitor, goal_monitor)

    # -- running ---------------------------------------------------------

    def observe_state(self, state: str) -> Verdict:
        if self.strategy_monitor is not None:
            self.strategy_monitor.observe_state(state)
        if self.goal_monitor is not None:
            self.goal_monitor.observe_state(state)
        return self.verdict

    def observe_action(self, profile: JointAction) -> Verdict:
        """Only the strategy monitor reads actions; the goal monitor ignores them."""
        if self.strategy_monitor is not None:
            self.strategy_monitor.observe_action(profile)
        self.step_count += 1
        return self.verdict

    def observe(self, state: str, profile: Optional[JointAction] = None) -> Verdict:
        self.observe_state(state)
        if profile is not None:
            self.observe_action(profile)
        return self.verdict

    def resume_at(self, state: str) -> Verdict:
        """Restart at ``state`` with no action outstanding (used after a repair)."""
        if self.strategy_monitor is not None:
            self.strategy_monitor.resume_at(state)
        if self.goal_monitor is not None:
            self.goal_monitor.observe_state(state)
        return self.verdict

    def run(self, trace: Trace) -> Verdict:
        for state, action in trace.steps():
            self.observe(state, action)
        return self.verdict

    def verdicts(self, trace: Trace) -> List[Verdict]:
        """The combined verdict after each observation."""
        out: List[Verdict] = []
        for state, action in trace.steps():
            out.append(self.observe_state(state))
            if action is not None:
                out.append(self.observe_action(action))
        return out

    # -- reporting -------------------------------------------------------

    @property
    def component_verdicts(self) -> Dict[str, Verdict]:
        """What each component says, keyed by ``"strategy"`` and ``"goal"``."""
        out: Dict[str, Verdict] = {}
        if self.strategy_monitor is not None:
            out["strategy"] = self.strategy_monitor.verdict
        if self.goal_monitor is not None:
            out["goal"] = self.goal_monitor.verdict
        return out

    @property
    def verdict(self) -> Verdict:
        """One verdict, chosen from the components by :data:`PRECEDENCE`."""
        held = set(self.component_verdicts.values())
        for candidate in PRECEDENCE:
            if candidate in held:
                return candidate
        return Verdict.UNKNOWN

    @property
    def violations(self) -> List[Violation]:
        """Strategy deviations, empty when no strategy monitor is present."""
        return list(self.strategy_monitor.violations) if self.strategy_monitor else []

    @property
    def components(self) -> Sequence[str]:
        names = []
        if self.strategy_monitor is not None:
            label = type(self.strategy_monitor).__name__
            describe = getattr(self.strategy_monitor, "describe", None)
            if describe is not None:
                # the recall monitor reports which engine it is running
                label = "{0}({1})".format(label, describe())
            names.append(label)
        if self.goal_monitor is not None:
            names.append(
                "GoalMonitor(refined)" if self.goal_monitor.use_model else "GoalMonitor(plain LTL)"
            )
        return tuple(names)

    def describe(self) -> str:
        return "MonitorSuite[{0}]".format(", ".join(self.components))

    def __str__(self) -> str:  # pragma: no cover - display helper
        parts = [
            "{0}={1}".format(name, verdict) for name, verdict in self.component_verdicts.items()
        ]
        return "{0} -> {1}   ({2})".format(self.describe(), self.verdict, ", ".join(parts))
