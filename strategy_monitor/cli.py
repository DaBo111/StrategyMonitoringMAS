"""Command line interface.

    python -m strategy_monitor <command> [options]

Commands
--------
``monitor``    run a monitor over a trace; the strategy component, the goal
               component, or both, with the strategy given or synthesised
``goal``       inspect the goal monitor ``M^G`` alone (sizes, optional trace)
``repair``     run the repair pipeline of Section 7 over a trace
``check``      ATL model checking through VITAMIN
``synthesize`` NatATL strategy synthesis through VITAMIN
``export``     write the model in VITAMIN's model-file syntax
``dot``        emit an automaton as Graphviz DOT
``backend``    report which LTL translation backend is in use
``demo``       reproduce every worked example of the paper
"""

from __future__ import annotations

import argparse
import json
import sys
from typing import List, Optional

from .automata import to_dot
from .cgs import CGS
from .goal import GoalMonitor, cgs_to_buchi
from .ltl import alphabet_of
from .spot_backend import diagnose
from .strategies import load_strategy
from .suite import MonitorSuite
from .trace import Trace, replay


def _load_trace(path: str, cgs: CGS) -> Trace:
    with open(path, encoding="utf-8") as handle:
        data = json.load(handle)
    if "actions" in data and "states" not in data:
        return replay(cgs, [tuple(a) for a in data["actions"]])
    return Trace.from_dict(data)


def _resolve_strategy(cgs: CGS, args):
    """Load the strategy from a file, synthesise one with VITAMIN, or use none."""
    if getattr(args, "strategy", None) and getattr(args, "synthesize", None):
        raise SystemExit("--strategy and --synthesize are alternatives; give at most one")
    if getattr(args, "strategy", None):
        return load_strategy(args.strategy, alphabet_of(cgs.ap))
    objective = getattr(args, "synthesize", None)
    if not objective:
        return None
    from .vitamin import natatl_synthesize

    coalition = args.coalition.split(",") if getattr(args, "coalition", None) else list(cgs.agents)
    result = natatl_synthesize(
        cgs,
        coalition,
        objective,
        k=getattr(args, "k", 2),
        rename_idle=getattr(args, "rename_idle", False),
    )
    print("synthesis : {0}".format(result.formula))
    if result.note:
        print("note      : {0}".format(result.note))
    if not result.satisfiable:
        raise SystemExit(
            "VITAMIN found no winning strategy for {0}; nothing to monitor".format(coalition)
        )
    if result.verified:
        print("verified  : the strategy enforces the objective under exact semantics")
    print("synthesised strategy:")
    print("  " + str(result.strategy).replace(chr(10), chr(10) + "  "))
    return result.strategy


# -- commands ------------------------------------------------------------


def cmd_monitor(args) -> int:
    cgs = CGS.from_json(args.model)
    strategy = _resolve_strategy(cgs, args)
    if strategy is None and not args.goal:
        raise SystemExit(
            "nothing to monitor: give --strategy, --synthesize, or --goal (or any combination)"
        )
    suite = MonitorSuite.build(
        cgs,
        strategy=strategy,
        goal=args.goal,
        adherence=args.adherence,
        use_model=not args.no_model,
        strict=False,
        determinize=args.recall_engine,
    )
    trace = _load_trace(args.trace, cgs)

    print("model     : {0} states, agents {1}".format(len(cgs.states), list(cgs.agents)))
    print("monitor   : {0}".format(suite.describe()))
    if strategy is not None:
        print("coalition : {0}".format(list(strategy.coalition)))
    print("trace     : {0}".format(trace))
    problems = trace.check_against(cgs)
    if problems:
        print("model conformance: VIOLATED")
        for problem in problems:
            print("  - {0}".format(problem))
    else:
        print("model conformance: ok")
    print()

    columns = ["j", "state", "action"] + list(suite.component_verdicts) + ["verdict"]
    widths = [3, 5, 22] + [9] * len(suite.component_verdicts) + [9]
    header = "  " + "  ".join(
        "{0:<{1}}".format(name, width) for name, width in zip(columns, widths)
    )
    print(header)
    for step, (state, action) in enumerate(trace.steps()):
        suite.observe_state(state)
        rendered = "(" + ",".join(action) + ")" if action else "(none observed yet)"
        if action is not None:
            suite.observe_action(action)
        cells = [str(step), state, rendered]
        cells += [str(v) for v in suite.component_verdicts.values()]
        cells.append(str(suite.verdict))
        print("  " + "  ".join("{0:<{1}}".format(c, w) for c, w in zip(cells, widths)))
        if action is None:
            break
    print()
    summary = getattr(suite.strategy_monitor, "summary", lambda: None)()
    if summary:
        print("engine  : {0}".format(summary))
    print("verdict: {0}".format(suite.verdict))
    for violation in suite.violations:
        print("  {0}".format(violation))
    return 1 if suite.verdict.is_violation else 0


def cmd_goal(args) -> int:
    cgs = CGS.from_json(args.model)
    refined = GoalMonitor(cgs, args.formula, use_model=not args.no_model)
    print("goal    : {0}".format(refined.goal))
    print("automata: {0}".format(refined.sizes()))
    if args.trace:
        trace = _load_trace(args.trace, cgs)
        print("trace   : {0}".format(trace))
        print()
        refined.reset()
        print("  {0:>3}  {1:<5} {2:<12} {3}".format("j", "state", "pi(s)", "verdict"))
        for step, state in enumerate(trace.states):
            verdict = refined.observe_state(state)
            label = "{" + ",".join(sorted(cgs.label(state))) + "}"
            print("  {0:>3}  {1:<5} {2:<12} {3}".format(step, state, label, verdict))
        print()
        print("verdict: {0}".format(refined.verdict))
        if not args.no_model:
            plain = GoalMonitor(cgs, args.formula, use_model=False)
            print("plain LTL monitor (no model refinement): {0}".format(plain.run(trace)))
        return 1 if refined.verdict.is_violation else 0
    return 0


def cmd_repair(args) -> int:
    from .repair import RepairPipeline, vitamin_synthesiser

    cgs = CGS.from_json(args.model)
    strategy = _resolve_strategy(cgs, args)
    if strategy is None and not args.goal:
        raise SystemExit(
            "nothing to monitor: give --strategy, --synthesize, or --goal (or any combination)"
        )
    trace = _load_trace(args.trace, cgs)
    pipeline = RepairPipeline(
        cgs=cgs,
        strategy=strategy,
        synthesiser=vitamin_synthesiser(args.objective, k=args.k) if args.objective else None,
        goal=args.goal,
        adherence=args.adherence,
        use_model=not args.no_model,
        determinize=args.recall_engine,
    )
    print("monitor   : {0}".format(pipeline.suite.describe()))
    if args.objective:
        print("objective (ATL, for re-synthesis): {0}".format(args.objective))
    if args.goal:
        print("goal      (LTL, for M^G)         : {0}".format(args.goal))
    print()
    for state, action in trace.steps():
        outcome = pipeline.observe(state, action)
        print(
            "  {0:<5} {1:<22} {2:<20} {3}".format(
                state,
                "(" + ",".join(action) + ")" if action else "(-)",
                outcome.value,
                pipeline.verdict,
            )
        )
    print()
    print(pipeline.report())
    return 1 if pipeline.stopped else 0


def cmd_check(args) -> int:
    from .vitamin import atl_model_check

    cgs = CGS.from_json(args.model)
    result = atl_model_check(cgs, args.coalition.split(","), args.objective)
    print("formula  : {0}".format(result["formula"]))
    print("satisfied: {0}".format(result["satisfied"]))
    print("states   : {0}".format(sorted(result["states"]) if result["states"] else result.get("res")))
    return 0 if result["satisfied"] else 1


def cmd_synthesize(args) -> int:
    from .vitamin import natatl_synthesize
    from .strategies import strategy_to_dict

    cgs = CGS.from_json(args.model)
    result = natatl_synthesize(
        cgs,
        args.coalition.split(","),
        args.objective,
        k=args.k,
        rename_idle=args.rename_idle,
    )
    print("formula      : {0}".format(result.formula))
    print("satisfiable  : {0}".format(result.satisfiable))
    print("verified     : {0}".format(result.verified))
    if result.atl_realisable is not None:
        print("atl says     : {0}".format(result.atl_realisable))
    if result.note:
        print("note         : {0}".format(result.note))
    if result.strategy is None:
        return 1
    print("bound reached: {0}".format(result.complexity_bound))
    print(result.strategy)
    if args.out:
        with open(args.out, "w", encoding="utf-8") as handle:
            json.dump(strategy_to_dict(result.strategy), handle, indent=2)
        print("written to {0}".format(args.out))
    return 0


def cmd_export(args) -> int:
    from .vitamin import to_vitamin_text

    cgs = CGS.from_json(args.model)
    text = to_vitamin_text(cgs)
    if args.out:
        with open(args.out, "w", encoding="utf-8") as handle:
            handle.write(text)
        print("written to {0}".format(args.out))
    else:
        sys.stdout.write(text)
    return 0


def cmd_backend(args) -> int:
    """Say what is installed and which translation a run would take."""
    print(diagnose())
    return 0


def cmd_dot(args) -> int:
    cgs = CGS.from_json(args.model)
    letters = alphabet_of(cgs.ap)
    if args.which == "model":
        automaton = cgs_to_buchi(cgs)
    else:
        monitor = GoalMonitor(cgs, args.formula, use_model=not args.no_model)
        automaton = {
            "positive-buchi": monitor.positive_buchi,
            "negative-buchi": monitor.negative_buchi,
            "positive-dfa": monitor.tables.positive,
            "negative-dfa": monitor.tables.negative,
        }[args.which]
    text = to_dot(automaton, name=args.which.replace("-", "_"))
    if args.out:
        with open(args.out, "w", encoding="utf-8") as handle:
            handle.write(text)
        print("written to {0}".format(args.out))
    else:
        sys.stdout.write(text + "\n")
    return 0


def cmd_demo(args) -> int:
    from .demo import main as demo_main

    return demo_main(skip_vitamin=args.no_vitamin)


# -- argument parsing ----------------------------------------------------


def build_parser() -> argparse.ArgumentParser:
    parser = argparse.ArgumentParser(
        prog="strategy_monitor",
        description="Runtime strategy monitoring of multi-agent systems.",
    )
    subparsers = parser.add_subparsers(dest="command", required=True)

    monitor = subparsers.add_parser(
        "monitor", help="run a monitor over a trace; components are mix-and-match"
    )
    monitor.add_argument("model", help="CGS JSON file")
    monitor.add_argument("trace", help="trace JSON file")
    monitor.add_argument("--strategy", help="strategy JSON file")
    monitor.add_argument(
        "--synthesize", metavar="OBJECTIVE", help="synthesise the strategy with VITAMIN instead"
    )
    monitor.add_argument("--coalition", help="coalition for --synthesize, e.g. a,b")
    monitor.add_argument("--k", type=int, default=2, help="NatATL complexity bound")
    monitor.add_argument(
        "--native-idle",
        dest="rename_idle",
        action="store_false",
        default=True,
        help="with --synthesize: keep VITAMIN's idle semantics (see the README)",
    )
    monitor.add_argument(
        "--adherence", action="store_true", help="use M^S, the relativised verdict of Section 6.1"
    )
    monitor.add_argument("--goal", help="LTL goal, adding the M^G component")
    monitor.add_argument(
        "--no-model", action="store_true", help="plain LTL goal monitor, no CGS intersection"
    )
    monitor.add_argument(
        "--recall-engine",
        choices=["dfa", "nfa", "lazy"],
        default="dfa",
        help="recall strategies: determinise up front (dfa), simulate the NFAs (nfa), "
        "or determinise on demand (lazy)",
    )
    monitor.set_defaults(func=cmd_monitor)

    goal = subparsers.add_parser("goal", help="run the goal-oriented monitor M^G")
    goal.add_argument("model", help="CGS JSON file")
    goal.add_argument("formula", help="LTL goal, e.g. 'G(p | (q & X p))'")
    goal.add_argument("--trace", help="trace JSON file")
    goal.add_argument("--no-model", action="store_true", help="plain LTL monitor, no CGS product")
    goal.set_defaults(func=cmd_goal)

    repair = subparsers.add_parser("repair", help="run the repair pipeline of Section 7")
    repair.add_argument("model", help="CGS JSON file")
    repair.add_argument("trace", help="trace JSON file")
    repair.add_argument("--strategy", help="strategy JSON file")
    repair.add_argument(
        "--synthesize", metavar="OBJECTIVE", help="synthesise the initial strategy with VITAMIN"
    )
    repair.add_argument("--coalition", help="coalition for --synthesize, e.g. a,b")
    repair.add_argument(
        "--objective", help="ATL objective for re-synthesis; omit to detect without repairing"
    )
    repair.add_argument("--goal", help="LTL goal, adding the M^G component")
    repair.add_argument(
        "--no-model", action="store_true", help="plain LTL goal monitor, no CGS intersection"
    )
    repair.add_argument("--adherence", action="store_true", help="use M^S (Section 6.1)")
    repair.add_argument(
        "--recall-engine",
        choices=["dfa", "nfa", "lazy"],
        default="dfa",
        help="recall strategies: determinise up front (dfa), simulate the NFAs (nfa), "
        "or determinise on demand (lazy)",
    )
    repair.add_argument("--k", type=int, default=2, help="NatATL complexity bound")
    repair.set_defaults(func=cmd_repair)

    check = subparsers.add_parser("check", help="ATL model checking via VITAMIN")
    check.add_argument("model")
    check.add_argument("coalition", help="comma-separated agent names, e.g. a,b")
    check.add_argument("objective", help="ATL path formula, e.g. 'G(p || q)'")
    check.set_defaults(func=cmd_check)

    synth = subparsers.add_parser("synthesize", help="NatATL synthesis via VITAMIN")
    synth.add_argument("model")
    synth.add_argument("coalition")
    synth.add_argument("objective")
    synth.add_argument("--k", type=int, default=2)
    synth.add_argument(
        "--native-idle",
        dest="rename_idle",
        action="store_false",
        default=True,
        help="keep VITAMIN's idle semantics, in which the prune admits idling "
        "alongside the prescribed action (off by default; see the README)",
    )
    synth.add_argument("--out", help="write the strategy to this JSON file")
    synth.set_defaults(func=cmd_synthesize)

    export = subparsers.add_parser("export", help="write the model in VITAMIN syntax")
    export.add_argument("model")
    export.add_argument("--out")
    export.set_defaults(func=cmd_export)

    dot = subparsers.add_parser("dot", help="emit an automaton as Graphviz DOT")
    dot.add_argument("model")
    dot.add_argument(
        "which",
        choices=["model", "positive-buchi", "negative-buchi", "positive-dfa", "negative-dfa"],
    )
    dot.add_argument("--formula", default="G(p | (q & X p))")
    dot.add_argument("--no-model", action="store_true")
    dot.add_argument("--out")
    dot.set_defaults(func=cmd_dot)

    backend = subparsers.add_parser(
        "backend", help="report which LTL translation backend is in use"
    )
    backend.set_defaults(func=cmd_backend)

    demo = subparsers.add_parser("demo", help="reproduce the worked examples of the paper")
    demo.add_argument("--no-vitamin", action="store_true", help="skip the VITAMIN-backed sections")
    demo.set_defaults(func=cmd_demo)

    return parser


def main(argv: Optional[List[str]] = None) -> int:
    parser = build_parser()
    args = parser.parse_args(argv)
    return args.func(args)


if __name__ == "__main__":  # pragma: no cover
    raise SystemExit(main())
