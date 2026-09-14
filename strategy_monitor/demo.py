"""Reproduce every worked example of the paper.

    python -m strategy_monitor demo

Each section prints what the paper claims and what the implementation produces,
so the two can be compared directly.
"""

from __future__ import annotations

import os

from .cgs import CGS
from .goal import GoalMonitor
from .ltl import alphabet_of
from .monitors import (
    RECALL_ENGINES,
    AdherenceMonitor,
    KBoundedMonitor,
    NaturalMemorylessMonitor,
    NaturalRecallMonitor,
    WindowIndex,
    model_windows,
)
from .strategies import (
    KBoundedStrategy,
    NaturalMemorylessStrategy,
    NaturalRecallRegexStrategy,
    NaturalRecallStrategy,
)
from .suite import MonitorSuite
from .trace import replay

EXAMPLES = os.path.join(os.path.dirname(os.path.dirname(os.path.abspath(__file__))), "examples")


def _rule(title: str) -> None:
    print()
    print("=" * 78)
    print(title)
    print("=" * 78)


def _letters(cgs: CGS, states) -> str:
    return " ".join("{" + ",".join(sorted(cgs.label(s))) + "}" for s in states)


def demo_running_example() -> CGS:
    _rule("Section 5.1 -- the running example G_E")
    cgs = CGS.from_json(os.path.join(EXAMPLES, "running_example.json"))
    print(cgs)
    print()
    print("delta is total and deterministic over {0} profiles per state".format(
        len(list(cgs.available_profiles(cgs.initial_state)))
    ))
    print("reachable states: {0}".format(sorted(cgs.reachable_states())))
    return cgs


def demo_kbounded(cgs: CGS) -> None:
    _rule("Section 5.2 -- k-bounded (memoryless) strategy monitor")
    strategy = KBoundedStrategy.memoryless(
        ["a", "b"],
        {
            "s0": {"a": "in", "b": "in"},
            "s1": {"a": "out", "b": "out"},
            "s2": {"a": "out", "b": "out"},
            "s3": {"a": "out", "b": "out"},
        },
    )
    strategy.validate(cgs)
    print(strategy)
    print()
    print("paper: M = {(s0,(in,in)), (s1,(out,out)), (s2,(out,out)), (s3,(out,out))}")
    print()

    print("The paper says traces with prefixes in")
    print("  {(s0 (in,in,any))^+ (s1 (out,out,any))^*}")
    print("get '?' and every other trace gets 'bot'.")
    print()
    for label, actions in [
        ("compliant, stays in s0", [("in", "in", "in"), ("in", "in", "in")]),
        ("compliant, s0 -> s1", [("in", "in", "in"), ("in", "in", "out"), ("out", "out", "in")]),
        ("agent a deviates in s0", [("out", "in", "out")]),
        ("both deviate in s0", [("out", "out", "out")]),
    ]:
        monitor = KBoundedMonitor(cgs, strategy)
        trace = replay(cgs, actions)
        verdict = monitor.run(trace)
        print("  {0:<26} {1:<46} {2}".format(label, str(trace), verdict))
        for violation in monitor.violations:
            print("      {0}".format(violation))

    print()
    print("Proposition 2 -- the direct-address table for k = 2:")
    index = WindowIndex(cgs, 2)
    print("  offsets o_m        : {0}".format(index.offsets[: index.k + 2]))
    print("  table capacity     : {0} entries  (sum_{{k' <= 2}} |S|^k' = 1 + 4 + 16)".format(index.capacity))
    index.reset()
    for state in ["s0", "s1", "s2"]:
        index.push(state)
        print(
            "  push {0} -> window {1:<16} index {2:>3}  (direct address {3})".format(
                state, str(index.window), index.value, index.index_of(index.window)
            )
        )


def demo_natural_memoryless(cgs: CGS) -> None:
    _rule("Sections 5.3-5.4 -- natural memoryless strategy monitor (Algorithm 1)")
    strategy = NaturalMemorylessStrategy.build(
        ["a", "b"],
        {
            "a": [("p", "in"), ("q", "out"), ("true", "idle")],
            "b": [("p", "in"), ("q", "out"), ("true", "idle")],
        },
    )
    print(strategy)
    print()
    table = strategy.to_kbounded(cgs)
    print("Algorithm 1 gives:")
    for window in sorted(table.table):
        actions = table.table[window]
        state = window[0]
        print(
            "  {0}  pi = {1:<8} -> ({2}, {3})".format(
                state,
                "{" + ",".join(sorted(cgs.label(state))) + "}",
                actions["a"],
                actions["b"],
            )
        )
    print()
    print("paper: M = {(s0,(in,in)), (s1,(in,in)), (s2,(out,out)), (s3,(in,in))}")
    print()
    monitor = NaturalMemorylessMonitor(cgs, strategy)
    trace = replay(cgs, [("in", "in", "out"), ("in", "in", "in")])
    print("  trace {0} -> {1}".format(trace, monitor.run(trace)))
    monitor = NaturalMemorylessMonitor(cgs, strategy)
    trace = replay(cgs, [("in", "in", "out"), ("out", "in", "in")])
    print("  trace {0} -> {1}".format(trace, monitor.run(trace)))
    for violation in monitor.violations:
        print("      {0}".format(violation))


def demo_natural_recall(cgs: CGS) -> None:
    _rule("Section 5.5 -- natural strategy with recall")
    letters = alphabet_of(cgs.ap)

    print("A recall strategy is specified as a priority-ordered sequence of")
    print("(regex, action) pairs (Section 5.3); the agent plays the action of the")
    print("first regex the observed history matches.")
    print()
    strategy = NaturalRecallRegexStrategy.build(
        ["a", "b"],
        # once q has been seen, play out forever; before that, play in
        {
            "a": [(".*[q].*", "out"), (".*", "in")],
            "b": [(".*[q].*", "out"), (".*", "in")],
        },
    )
    print(strategy)
    print()

    print("Three engines monitor it, and they prescribe the same actions:")
    print()
    print("  {0:<7} {1:<36} {2}".format("engine", "construction", "cost per step"))
    for name, construction, per_step in [
        ("dfa", "determinise to the product DFST", "one lookup, O(|A|)"),
        ("nfa", "Thompson automata, kept as they are", "advance one active set per regex"),
        ("lazy", "nothing; the table is built on demand", "a lookup once the state is known"),
    ]:
        print("  {0:<7} {1:<36} {2}".format(name, construction, per_step))
    print()
    for engine in RECALL_ENGINES:
        monitor = NaturalRecallMonitor(cgs, strategy, determinize=engine)
        trace = replay(cgs, [("out", "out", "out"), ("out", "out", "in")])
        verdict = monitor.run(trace)
        deviating = NaturalRecallMonitor(cgs, strategy, determinize=engine)
        deviating.run(replay(cgs, [("in", "in", "in")]))
        print(
            "  {0:<40} complying -> {1:<5} deviating -> {2}".format(
                monitor.describe(), str(verdict), str(deviating.verdict)
            )
        )
    print("  (s0 satisfies q, so 'out' is prescribed from the very first step)")

    print()
    print("The choice matters when the regexes force the subset construction open.")
    print("For '.*[p]' followed by n wildcards -- the (n+1)-th letter from the end")
    print("satisfies p -- determinising is exponential while the NFAs stay linear:")
    print()
    print(
        "  {0:<18} {1:>12} {2:>11} {3:>22}".format(
            "regex", "DFST states", "NFA states", "lazy, after 12 steps"
        )
    )
    import random as _random

    for n in range(0, 7):
        pattern = ".*[p]" + "." * n
        family = NaturalRecallRegexStrategy.build(
            ["a"], {"a": [(pattern, "out"), (".*", "in")]}
        )
        determinised = NaturalRecallMonitor(cgs, family, determinize="dfa")
        simulated = NaturalRecallMonitor(cgs, family, determinize="nfa")
        lazy = NaturalRecallMonitor(cgs, family, determinize="lazy")
        _random.seed(4)
        for _ in range(12):
            lazy.engine.step(_random.choice(letters))
        print(
            "  {0:<18} {1:>12} {2:>11} {3:>22}".format(
                pattern, determinised.size, simulated.size, lazy.engine.materialised
            )
        )
    print()
    print("  For small regexes the determinised table is the smaller of the two;")
    print("  the NFA engine is there for the cases where it is not.  The lazy")
    print("  engine builds only the states a run reaches -- at most one per step --")
    print("  so it pays the DFA's per-step cost without its construction cost.")

    print()
    print("Section 5.5 monitors the DFST form, which is also available directly:")
    dfst_form = strategy.to_dfst_strategy(letters)
    print(
        "  to_dfst_strategy -> {0} NatDFSTs, {1} states each at most".format(
            len(dfst_form.transducers), dfst_form.complexity()
        )
    )
    product = dfst_form.product(letters)
    print(
        "  product DFST: {0} states over I = 2^Ap ({1} letters), O = prod_a act_a".format(
            len(product.states), len(letters)
        )
    )


def demo_adherence(running: CGS) -> None:
    _rule("Section 6.1 -- strategy-adherence truth M^S, relativised to the model")
    cgs = CGS.from_json(os.path.join(EXAMPLES, "revised_example.json"))
    print(cgs)
    print()
    strategy = KBoundedStrategy.memoryless(
        ["a"], {"s0": {"a": "in"}, "s1": {"a": "out"}, "s2": {"a": "out"}, "s3": {"a": "in"}}
    )
    strategy.validate(cgs)
    print(strategy)
    print()
    print("The verdict is top^S_G once W_G(s_cur) -- the windows still observable")
    print("from the current state -- have all been observed and validated.")
    print()
    print("paper: M^S returns top^S_G for any trace with prefix")
    print("       s0 (in,*,*) s1 (out,*,*) s2 (out,*,*) s3 (in,*,*)")
    print()
    monitor = AdherenceMonitor(cgs, strategy)
    trace = replay(
        cgs,
        [("in", "in", "out"), ("out", "in", "in"), ("out", "out", "in"), ("in", "in", "in")],
    )
    print("  {0:<4} {1:<6} {2:<16} {3:<8} {4}".format("step", "state", "action", "verdict", "W_G(s_cur) still to validate"))
    for step, (state, action) in enumerate(trace.steps()):
        monitor.observe_state(state)
        if action is None:
            break
        verdict = monitor.observe_action(action)
        print(
            "  {0:<4} {1:<6} {2:<16} {3:<8} {4}".format(
                step,
                state,
                "(" + ",".join(action) + ")",
                str(verdict),
                [w[0] for w in monitor.pending_from()],
            )
        )

    print()
    print("Relativising is what makes the verdict attainable at all.")
    print("Most of S^k is not a path of the model, and absorbing states cut the rest off:")
    for k in (1, 2, 3):
        print(
            "  k = {0}: {1:>3} of {2:>3} elements of S^k are paths of G_E".format(
                k, len(model_windows(running, k)), len(running.states) ** k
            )
        )
    print()
    print("In G_E, s1 is absorbing.  A run that enters it validates everything")
    print("still observable without ever seeing s2 or s3:")
    absorbing = KBoundedStrategy.memoryless(
        ["a", "b"],
        {
            "s0": {"a": "in", "b": "in"},
            "s1": {"a": "out", "b": "out"},
            "s2": {"a": "out", "b": "out"},
            "s3": {"a": "out", "b": "out"},
        },
    )
    monitor = AdherenceMonitor(running, absorbing)
    trace = replay(running, [("in", "in", "out"), ("out", "out", "in")])
    print("  {0} -> {1}".format(trace, monitor.run(trace)))
    print(
        "  never observed: {0}   still observable from s1: {1}".format(
            [w[0] for w in monitor.pending_configurations()], monitor.pending_from("s1")
        )
    )
    print()
    print("A run that stays in s0 keeps every state reachable, so it stays inconclusive:")
    monitor = AdherenceMonitor(running, absorbing)
    trace = replay(running, [("in", "in", "in")] * 3)
    print(
        "  {0} -> {1}, still to validate {2}".format(
            trace, monitor.run(trace), [w[0] for w in monitor.pending_from()]
        )
    )


def demo_goal(cgs: CGS) -> None:
    _rule("Section 6.2 -- goal-oriented truth M^G")
    goal = "G(p | (q & X p))"
    refined = GoalMonitor(cgs, goal, use_model=True)
    plain = GoalMonitor(cgs, goal, use_model=False)
    print("goal phi = {0}".format(goal))
    print("refined (intersected with the CGS): {0}".format(refined.sizes()))
    print("plain   (from the formula alone)  : {0}".format(plain.sizes()))
    print()
    print("The paper's example: omega = s0 (in,in,out) s1 (in,in,in)")
    trace = replay(cgs, [("in", "in", "out"), ("in", "in", "in")])
    word = trace.word(cgs)
    print("  pi(omega_s) = {0}".format(_letters(cgs, trace.states)))
    print("  plain LTL monitor : {0}".format(plain.evaluate(word)))
    print("  refined M^G       : {0}   <- the paper's claim".format(refined.evaluate(word)))
    print()
    print("top^G_G is relativised too: it certifies phi on every continuation that")
    print("respects the CGS, and is superseded by bot^M should the system leave it:")
    refined.reset()
    for letter in [frozenset({"p", "q"}), frozenset({"p"}), frozenset()]:
        rendered = "{" + ",".join(sorted(letter)) + "}"
        print("    read {0:<8} -> {1}".format(rendered, refined.observe_letter(letter)))
    print()
    print("Model violation detection comes for free:")
    for description, states in [
        ("first label is not pi(s_I)", [frozenset({"p"})]),
        ("s0 -> s2 -> s2 violates phi", [frozenset({"p", "q"}), frozenset({"q"}), frozenset({"q"})]),
        ("s1 only self-loops, so {q} cannot follow", [frozenset({"p", "q"}), frozenset({"p"}), frozenset({"q"})]),
    ]:
        verdict = refined.evaluate(states)
        rendered = " ".join("{" + ",".join(sorted(s)) + "}" for s in states)
        print("  {0:<44} {1:<22} {2}".format(description, rendered, verdict))


def demo_modularity(cgs: CGS) -> None:
    _rule("Composing a monitor -- the components are mix-and-match")
    letters = alphabet_of(cgs.ap)
    goal = "G(p | (q & X p))"

    strategies = {
        "k-bounded": KBoundedStrategy.memoryless(
            ["a", "b"], {s: {"a": "in", "b": "in"} for s in cgs.states}
        ),
        "natural memoryless": NaturalMemorylessStrategy.build(
            ["a", "b"], {"a": [("p", "in"), ("true", "idle")], "b": [("p", "in"), ("true", "idle")]}
        ),
        "natural recall": NaturalRecallStrategy.from_regex_sequences(
            ["a", "b"],
            {"a": [(".*[q].*", "out"), (".*", "in")], "b": [(".*[q].*", "out"), (".*", "in")]},
            letters,
        ),
    }

    print("A suite is assembled from whichever parts a deployment wants;")
    print("both components are optional and either may be left out.")
    print()
    print("  {0:<22} {1:<10} {2:<7} {3}".format("strategy", "adherence", "goal", "assembled monitor"))
    rows = [
        ("k-bounded", False, None, True),
        ("k-bounded", True, None, True),
        ("natural memoryless", False, goal, True),
        ("natural memoryless", True, goal, False),
        ("natural recall", False, goal, True),
        (None, False, goal, True),
        (None, False, goal, False),
    ]
    for name, adherence, formula, use_model in rows:
        suite = MonitorSuite.build(
            cgs,
            strategy=strategies[name] if name else None,
            goal=formula,
            adherence=adherence,
            use_model=use_model,
        )
        print(
            "  {0:<22} {1:<10} {2:<7} {3}".format(
                name or "(none)",
                "yes" if adherence else "no",
                ("refined" if use_model else "plain") if formula else "(none)",
                suite.describe(),
            )
        )

    print()
    print("Each component keeps its own verdict; the suite reports one by precedence.")
    suite = MonitorSuite.build(cgs, strategy=strategies["natural memoryless"], goal=goal)
    trace = replay(cgs, [("in", "in", "out"), ("out", "in", "in")])
    suite.run(trace)
    print("  trace {0}".format(trace))
    for component, verdict in suite.component_verdicts.items():
        print("    {0:<10} {1}".format(component, verdict))
    print("    {0:<10} {1}".format("combined", suite.verdict))


def demo_repair(cgs: CGS, skip_vitamin: bool) -> None:
    _rule("Section 7 -- strategy repair")
    if skip_vitamin:
        print("skipped (--no-vitamin)")
        return
    try:
        from .vitamin import require_vitamin

        require_vitamin()
    except Exception as error:  # pragma: no cover - environment dependent
        print("skipped: {0}".format(error))
        return

    from .repair import RepairPipeline, fixed_synthesiser, vitamin_synthesiser

    strategy = NaturalMemorylessStrategy.build(
        ["a", "b"],
        {"a": [("p", "in"), ("true", "idle")], "b": [("p", "in"), ("true", "idle")]},
    )

    def show(pipeline, steps):
        print("  {0:<5} {1:<18} {2:<20} {3}".format("state", "action", "outcome", "verdict"))
        for state, action in steps:
            outcome = pipeline.observe(state, action)
            print(
                "  {0:<5} {1:<18} {2:<20} {3}".format(
                    state,
                    "(" + ",".join(action) + ")" if action else "(none)",
                    outcome.value,
                    pipeline.verdict,
                )
            )
        print(pipeline.report())

    print("7.1  Coalition strategy violation, repaired")
    print("     objective G(p || q), which {b} alone can still enforce")
    print()
    pipeline = RepairPipeline(
        cgs=cgs,
        coalition=("a", "b"),
        strategy=strategy,
        synthesiser=vitamin_synthesiser("G(p || q)", k=2),
        goal="G(p | (q & X p))",
    )
    show(pipeline, [("s0", ("out", "in", "in"))])
    if pipeline.events and pipeline.events[0].new_strategy is not None:
        print("  re-synthesised for {0}:".format(list(pipeline.coalition)))
        print("  " + str(pipeline.events[0].new_strategy).replace(chr(10), chr(10) + "  "))
        print("  execution resumes from q_curr = s0 under that strategy:")
        prescribed = pipeline.strategy.action_for("b", cgs.label("s0"))
        show(pipeline, [("s0", (prescribed, prescribed, "in"))])

    print()
    print("7.1  Coalition strategy violation, repair fails")
    print("     objective G p, which neither agent can enforce alone")
    print()
    pipeline = RepairPipeline(
        cgs=cgs,
        coalition=("a", "b"),
        strategy=strategy,
        synthesiser=vitamin_synthesiser("G p", k=2),
    )
    show(pipeline, [("s0", ("out", "in", "in"))])

    print()
    print("7.2  Model violation: delta(s0, (in,in,out)) = s1, but the system goes to s3")
    print("     the same strategy is kept here so the model repair shows in isolation")
    print()
    pipeline = RepairPipeline(
        cgs=cgs,
        coalition=("a", "b"),
        strategy=strategy,
        synthesiser=fixed_synthesiser(strategy),
    )
    show(pipeline, [("s0", ("in", "in", "out")), ("s3", ("in", "in", "in"))])
    for event in pipeline.events:
        if event.added_transition:
            source, profile, target = event.added_transition
            print("  delta' now maps ({0}, {1}) to {2}".format(source, list(profile), target))
            print(
                "  and the monitor now runs on G', where delta({0}, {1}) = {2}".format(
                    source, list(profile), pipeline.cgs.step(source, profile)
                )
            )

    print()
    print("7.2  Model violation followed by re-synthesis on G'")
    print()
    pipeline = RepairPipeline(
        cgs=cgs,
        coalition=("a", "b"),
        strategy=strategy,
        synthesiser=vitamin_synthesiser("G(p || q)", k=2),
    )
    show(pipeline, [("s0", ("in", "in", "out")), ("s3", None)])
    print("  strategy in force after the repair:")
    print("  " + str(pipeline.strategy).replace(chr(10), chr(10) + "  "))


def demo_vitamin(cgs: CGS, skip_vitamin: bool) -> None:
    _rule("VITAMIN -- ATL model checking and NatATL synthesis")
    if skip_vitamin:
        print("skipped (--no-vitamin)")
        return
    try:
        from .vitamin import atl_model_check, natatl_synthesize, require_vitamin

        require_vitamin()
    except Exception as error:  # pragma: no cover - environment dependent
        print("skipped: {0}".format(error))
        return

    for coalition, objective in [(["a", "b"], "G p"), (["a"], "G p"), (["a", "b"], "G(p || q)")]:
        result = atl_model_check(cgs, coalition, objective)
        print(
            "  {0:<24} satisfied at s_I: {1:<6} holds in {2}".format(
                result["formula"], str(result["satisfied"]), sorted(result["states"] or [])
            )
        )
    print()
    result = natatl_synthesize(cgs, ["a"], "G(p || q)", k=2)
    print("  NatATL {0} -> satisfiable {1}".format(result.formula, result.satisfiable))
    if result.strategy is not None:
        print("  " + str(result.strategy).replace("\n", "\n  "))
        print()
        print("  The witness is an ordinary NaturalMemorylessStrategy, so it goes")
        print("  straight into a monitor suite with no adapter:")
        suite = MonitorSuite.build(
            cgs, strategy=result.strategy, goal="G(p | (q & X p))", strict=False
        )
        print("    {0}".format(suite.describe()))
        prescribed = result.strategy.action_for("a", cgs.label("s0"))
        deviation = next(a for a in cgs.actions["a"] if a != prescribed)
        for label, action in [("complying", prescribed), ("deviating ", deviation)]:
            fresh = MonitorSuite.build(
                cgs, strategy=result.strategy, goal="G(p | (q & X p))", strict=False
            )
            trace = replay(cgs, [(action, "in", "in")])
            fresh.run(trace)
            print(
                "    {0} with a = {1:<5} -> {2:<8} {3}".format(
                    label,
                    action,
                    str(fresh.verdict),
                    dict((k, str(v)) for k, v in fresh.component_verdicts.items()),
                )
            )
        print()
        print("  Note: VITAMIN enumerates strategies over unordered sets, so the witness")
        print("  it returns is stable within a process but can differ between runs;")
        print("  every one of them is winning.")


def main(skip_vitamin: bool = False) -> int:
    cgs = demo_running_example()
    demo_kbounded(cgs)
    demo_natural_memoryless(cgs)
    demo_natural_recall(cgs)
    demo_adherence(cgs)
    demo_goal(cgs)
    demo_modularity(cgs)
    demo_vitamin(cgs, skip_vitamin)
    demo_repair(cgs, skip_vitamin)
    print()
    return 0


if __name__ == "__main__":  # pragma: no cover
    raise SystemExit(main())
