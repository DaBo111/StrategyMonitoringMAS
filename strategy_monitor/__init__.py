"""Runtime strategy monitoring of multi-agent systems.

An implementation of *Runtime Strategy Monitoring of Multi-agent Systems*:
monitors that watch a multi-agent system modelled as a concurrent game structure
and report, at runtime, whether the agents are following a prescribed coalition
strategy.

Section map
-----------

===========================================  =====================================
Paper                                        Module
===========================================  =====================================
Definition 1, CGS                            :mod:`strategy_monitor.cgs`
Section 5.2, trace semantics                 :mod:`strategy_monitor.trace`
Section 5.2, k-bounded monitor               :class:`~strategy_monitor.monitors.KBoundedMonitor`
Sections 5.3-5.4, natural memoryless         :class:`~strategy_monitor.monitors.NaturalMemorylessMonitor`
Sections 5.3/5.5, natural with recall        :class:`~strategy_monitor.monitors.NaturalRecallMonitor`
Section 6.1, strategy-adherence truth        :class:`~strategy_monitor.monitors.AdherenceMonitor`
Section 6.2, goal-oriented truth             :class:`~strategy_monitor.goal.GoalMonitor`
Section 7, strategy repair                   :class:`~strategy_monitor.repair.RepairPipeline`
composing any subset of the above            :class:`~strategy_monitor.suite.MonitorSuite`
checking a strategy really wins              :func:`~strategy_monitor.verify.enforces`
===========================================  =====================================

VITAMIN (``pip install vitamin-model-checker``) supplies ATL model checking and
NatATL strategy synthesis through :mod:`strategy_monitor.vitamin`; everything
else, including the LTL-to-Buchi translation and the exact strategy verifier, is
self-contained.
"""

from .automata import (
    NFA,
    DFA,
    Buchi,
    Lasso,
    NFASimulator,
    buchi_is_empty,
    buchi_lasso,
    determinize,
    prefix_nfa,
)
from .boolean import Gate, parse_gate
from .cgs import CGS, CGSError, JointAction
from .goal import GoalMonitor, cgs_to_buchi
from .ltl import alphabet_of, ltl_to_buchi, parse_ltl
from .spot_backend import resolve_ltl_backend, spot_available
from .monitors import (
    AdherenceMonitor,
    LazyProductEngine,
    ProductDFSTEngine,
    RECALL_ENGINES,
    RegexNFAEngine,
    resolve_recall_engine,
    KBoundedMonitor,
    NaturalMemorylessAdherenceMonitor,
    NaturalMemorylessMonitor,
    NaturalRecallMonitor,
    StrategyMonitor,
    WindowIndex,
    model_windows,
    observable_windows,
    reachable_from,
)
from .regex import parse_regex
from .repair import RepairPipeline, RepairOutcome, fixed_synthesiser, vitamin_synthesiser
from .suite import MonitorSuite, build_strategy_monitor
from .strategies import (
    DFST,
    KBoundedStrategy,
    NaturalMemorylessStrategy,
    NaturalRecallRegexStrategy,
    NaturalRecallStrategy,
    StrategyError,
    product_dfst,
)
from .trace import Trace, replay
from .verify import enforces, restrict
from .verdict import ModelDeviation, Verdict, Violation

__version__ = "1.0.0"

__all__ = [
    "CGS",
    "CGSError",
    "JointAction",
    "Trace",
    "replay",
    "Gate",
    "parse_gate",
    "parse_regex",
    "parse_ltl",
    "alphabet_of",
    "ltl_to_buchi",
    "resolve_ltl_backend",
    "spot_available",
    "NFA",
    "DFA",
    "Buchi",
    "determinize",
    "prefix_nfa",
    "Lasso",
    "buchi_lasso",
    "buchi_is_empty",
    "enforces",
    "restrict",
    "KBoundedStrategy",
    "NaturalMemorylessStrategy",
    "NaturalRecallStrategy",
    "NaturalRecallRegexStrategy",
    "DFST",
    "product_dfst",
    "StrategyError",
    "StrategyMonitor",
    "KBoundedMonitor",
    "NaturalMemorylessMonitor",
    "NaturalRecallMonitor",
    "ProductDFSTEngine",
    "RegexNFAEngine",
    "LazyProductEngine",
    "RECALL_ENGINES",
    "resolve_recall_engine",
    "NFASimulator",
    "AdherenceMonitor",
    "NaturalMemorylessAdherenceMonitor",
    "WindowIndex",
    "model_windows",
    "observable_windows",
    "reachable_from",
    "GoalMonitor",
    "MonitorSuite",
    "build_strategy_monitor",
    "cgs_to_buchi",
    "Verdict",
    "Violation",
    "ModelDeviation",
    "RepairPipeline",
    "RepairOutcome",
    "vitamin_synthesiser",
    "fixed_synthesiser",
    "__version__",
]
