"""Proposition 6: the strategy-adherence monitor M^S.

    construction O(|S|^k x |A| + |S|.|E|) time, O(|S|^k) space
    runtime      O(|A| x |omega|), the verdict test n[s_cur] = 0 worst-case O(1)

The generated models branch two ways, so |E| = 2|S| and the second construction
term is 2|S|^2 -- which dominates the first at k = 1.  Sweep A therefore expects
an exponent of 2 in |S|, not 1.

The coalition is agent 1, never agent 0.  Agent 0's action fixes the successor,
so a compliant walk by a coalition containing it is deterministic: it settles
into a short cycle, visits a handful of states, and never validates enough
windows for a counter to reach zero -- the cascade and the positive verdict
would both go unmeasured.

The runtime claim has two parts that have to be separated.  The verdict test is
O(1), but clearing a counter can cascade over Reach(s) at O(|S|) a time, at most
|S| times, so O(|S|^2) across the whole run.  Sweep B fixes |S| and grows the
trace, where that fixed total is amortised away; sweep C keeps |S|^2 well below
the trace length so the per-step cost is dominated by the O(1) test.
"""

import bench
from strategy_monitor.monitors import AdherenceMonitor

# -- A: construction against |S| -----------------------------------------

bench.rule("A.  construction against |S|, k = 1   (claim: |S|.|E| = 2|S|^2, exponent 2)")
SIZES_A = [64, 96, 144, 216, 324, 486, 729, 1024]
rows, times = [], []
for n in SIZES_A:
    cgs = bench.random_cgs(n)
    strategy = bench.kbounded_strategy(cgs, ["a1"], 1)
    seconds = bench.timed(lambda c=cgs, s=strategy: AdherenceMonitor(c, s), 3)
    rows.append([n, len(cgs.transitions), "{0:.6f}".format(seconds)])
    times.append(seconds)
bench.table(["|S|", "delta entries", "seconds"], rows)
slope_a, r2_a = bench.fit_power(SIZES_A, times)
ok_a = bench.verdict(slope_a, 2.0, r2_a, tolerance=0.30)


# -- B: runtime against trace length -------------------------------------

bench.rule("B.  runtime against |omega|, |S| = 100   (claim: linear)")
LENGTHS = [40000, 80000, 160000, 320000, 640000]
cgs_b = bench.random_cgs(100)
strategy_b = bench.kbounded_strategy(cgs_b, ["a1"], 1)
rows, times_b = [], []
for length in LENGTHS:
    monitor = AdherenceMonitor(cgs_b, strategy_b)
    steps = bench.compliant_walk(cgs_b, ["a1"], length)

    def run(monitor=monitor, steps=steps):
        for state, profile in steps:
            monitor.observe(state, profile)

    seconds = bench.timed(run, 3)
    rows.append([length, "{0:.4f}".format(seconds), str(monitor.verdict)])
    times_b.append(seconds)
bench.table(["|omega|", "seconds", "verdict"], rows)
slope_b, r2_b = bench.fit_power(LENGTHS, times_b)
ok_b = bench.verdict(slope_b, 1.0, r2_b)


# -- C: per-step runtime against |S| -------------------------------------

bench.rule("C.  per-step runtime against |S|   (claim: O(1) verdict test)")
SIZES_C = [25, 50, 100, 200, 400, 800]
STEPS = 400000
rows, times_c = [], []
for n in SIZES_C:
    cgs = bench.random_cgs(n)
    strategy = bench.kbounded_strategy(cgs, ["a1"], 1)
    monitor = AdherenceMonitor(cgs, strategy)
    steps = bench.compliant_walk(cgs, ["a1"], STEPS)

    def run(monitor=monitor, steps=steps):
        for state, profile in steps:
            monitor.observe(state, profile)

    seconds = bench.timed(run, 3)
    per_step = seconds / STEPS
    rows.append([n, n * n, "{0:.3f}".format(per_step * 1e6), str(monitor.verdict)])
    times_c.append(per_step)
bench.table(["|S|", "|S|^2 cascade budget", "microseconds/step", "verdict"], rows)
ok_c = bench.verdict_flat(SIZES_C, times_c, ratio_tolerance=1.5)
print("  (the trace is {0} steps, so the O(|S|^2) cascade is at most".format(STEPS))
print("   {0:.2f} operations per step at the largest |S| tried.)".format(
    SIZES_C[-1] ** 2 / STEPS))


bench.rule("Summary")
for name, ok in [("A |S| construction", ok_a), ("B |omega|", ok_b),
                 ("C O(1) verdict", ok_c)]:
    print("  {0:<20} {1}".format(name, "ok" if ok else "OFF"))
