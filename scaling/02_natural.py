"""Proposition 4: the natural memoryless monitor.

    construction O(|A| x |S| x k^2),  k = max_a compl(gamma_a^Natr)
    runtime      O(|A| x |omega|) time, O(|S| x |A|) space

with ``compl(gamma_a) = sum over (gate, act) of |gate|``, the *total* number of
variable occurrences across the agent's gates.

That definition is what makes the k^2 term worth probing.  Building the table
evaluates every gate at every state, costing the sum of the gate sizes -- which
is k itself, not k^2.  The proof reaches k^2 by bounding the number of gates by
k and the cost of each by k separately, but under this definition the two cannot
both be extremal: g gates of size s give k = g*s and work g*s = k.  So the bound
should hold and be loose by a factor of k.  Sweeps A and B grow k the two
opposite ways to check that neither shape reaches k^2.
"""

import bench
from strategy_monitor.boolean import parse_gate
from strategy_monitor.monitors import NaturalMemorylessMonitor
from strategy_monitor.strategies import NaturalMemorylessStrategy

STATES = 400


def strategy_many_small_gates(cgs, coalition, n_gates):
    """k grown by gate count: ``n_gates`` gates of one variable each."""
    ap = cgs.ap
    rules = {}
    for agent in coalition:
        pairs = [
            ("{0} & !{0}".format(ap[i % len(ap)]), cgs.actions[agent][0])
            for i in range(n_gates - 1)
        ]
        rules[agent] = pairs + [("true", cgs.actions[agent][0])]
    return NaturalMemorylessStrategy.build(coalition, rules)


def strategy_one_big_gate(cgs, coalition, width):
    """k grown by gate size: a single conjunction of ``width`` variables."""
    ap = cgs.ap
    conjunction = " & ".join(
        "({0} | !{0})".format(ap[i % len(ap)]) for i in range(width)
    )
    return NaturalMemorylessStrategy.build(
        coalition,
        {agent: [(conjunction, cgs.actions[agent][0])] for agent in coalition},
    )


def sweep(build, values, label):
    cgs = bench.random_cgs(STATES, n_ap=4)
    rows, times, ks = [], [], []
    for value in values:
        strategy = build(cgs, ["a0"], value)
        k = strategy.complexity()
        seconds = bench.timed(
            lambda s=strategy: NaturalMemorylessMonitor(cgs, s, strict=False), 5
        )
        rows.append([value, k, "{0:.6f}".format(seconds)])
        times.append(seconds)
        ks.append(k)
    bench.table([label, "compl = k", "seconds"], rows)
    return ks, times


bench.rule("A.  construction against k, grown by GATE COUNT   (claim: O(k^2))")
ks, times = sweep(strategy_many_small_gates, [16, 64, 256, 1024, 4096], "gates")
slope_a, r2_a = bench.fit_power(ks, times)
print()
print("  fitted exponent {0:.2f}   claimed <= 2.00   R^2 {1:.3f}".format(slope_a, r2_a))
ok_a = slope_a <= 2.0 + 0.25


bench.rule("B.  construction against k, grown by GATE SIZE   (claim: O(k^2))")
# Capped at 800 conjuncts, for the same reason the k sweep stops below 2^22
# table entries: past that depth Gate.evaluate hands the subtree to an explicit
# stack, which is a different algorithm with different constants, so a sweep
# crossing the boundary would fit a curve made of two pieces. Deeper gates work
# -- see tests/test_model.py::TestDeepGates -- they are just not the same
# measurement. Growing k by gate COUNT (sweep A) has no such boundary, since it
# is depth and not size that binds.
ks_b, times_b = sweep(strategy_one_big_gate, [16, 64, 200, 400, 800], "width")
slope_b, r2_b = bench.fit_power(ks_b, times_b)
print()
print("  fitted exponent {0:.2f}   claimed <= 2.00   R^2 {1:.3f}".format(slope_b, r2_b))
ok_b = slope_b <= 2.0 + 0.25


bench.rule("C.  construction against |S|, k fixed   (claim: linear in |S|)")
SIZES = [500, 1000, 2000, 4000, 8000, 16000, 32000, 64000]
rows, times_c = [], []
for n in SIZES:
    cgs = bench.random_cgs(n, n_ap=4)
    strategy = strategy_many_small_gates(cgs, ["a0"], 16)
    seconds = bench.timed(
        lambda c=cgs, s=strategy: NaturalMemorylessMonitor(c, s, strict=False), 5
    )
    rows.append([n, "{0:.6f}".format(seconds)])
    times_c.append(seconds)
bench.table(["|S|", "seconds"], rows)
slope_c, r2_c = bench.fit_power(SIZES, times_c)
ok_c = bench.verdict(slope_c, 1.0, r2_c)


bench.rule("D.  construction against |A|   (claim: linear in |A|)")
COALITIONS = list(range(1, 13))
cgs_d = bench.random_cgs(200, n_agents=12, n_ap=4)
rows, times_d = [], []
for size in COALITIONS:
    coalition = list(cgs_d.agents[:size])
    strategy = strategy_many_small_gates(cgs_d, coalition, 16)
    seconds = bench.timed(
        lambda s=strategy: NaturalMemorylessMonitor(cgs_d, s, strict=False), 5
    )
    rows.append([size, "{0:.6f}".format(seconds)])
    times_d.append(seconds)
bench.table(["|A|", "seconds"], rows)
ok_d = bench.verdict_affine(COALITIONS, times_d, what="agent (microseconds)")


bench.rule("Summary")
print("  A  k by gate count : exponent {0:.2f}  (bound 2.00) -> {1}".format(
    slope_a, "within the bound" if ok_a else "EXCEEDS the bound"))
print("  B  k by gate size  : exponent {0:.2f}  (bound 2.00) -> {1}".format(
    slope_b, "within the bound" if ok_b else "EXCEEDS the bound"))
print("  C  |S|             : {0}".format("ok" if ok_c else "OFF"))
print("  D  |A|             : {0}".format("ok" if ok_d else "OFF"))
print()
if ok_a and ok_b and max(slope_a, slope_b) < 1.5:
    print("  Both shapes of k come out near-linear, so O(|A| x |S| x k^2) holds")
    print("  but is loose: the measured cost is O(|A| x |S| x k).")
