"""Propositions 1 and 2: the k-bounded (and memoryless) monitor.

    Prop 1  memoryless:  construction O(|S| x |A|) time and space,
                         runtime O(|A| x |omega|), lookup worst-case O(1)
    Prop 2  k-bounded:   construction O(|S|^k x |A|), runtime O(|A| x |omega|)

Six sweeps, one parameter each.  The interesting pair is (D) against (A): the
table is built in |S|^k, but a lookup into it must not depend on |S| at all --
that is the whole point of addressing it directly instead of hashing.
"""

import bench
from strategy_monitor.monitors import KBoundedMonitor

REPEATS = 5


def construction(sizes, k, coalition_size=1):
    rows, times = [], []
    for n in sizes:
        cgs = bench.random_cgs(n, n_agents=max(2, coalition_size))
        coalition = list(cgs.agents[:coalition_size])
        strategy = bench.kbounded_strategy(cgs, coalition, k)
        seconds = bench.timed(lambda: KBoundedMonitor(cgs, strategy), REPEATS)
        monitor = KBoundedMonitor(cgs, strategy)
        rows.append([n, len(strategy.table), monitor.index.capacity, "{0:.6f}".format(seconds)])
        times.append(seconds)
    return rows, times


# -- A: construction against |S|, k = 1 ----------------------------------

bench.rule("A.  Prop 1 -- construction against |S|, k = 1, |A| = 1   (claim: linear)")
SIZES_A = [1000, 2000, 4000, 8000, 16000, 32000, 64000, 128000, 256000]
rows, times = construction(SIZES_A, k=1)
bench.table(["|S|", "windows", "capacity", "seconds"], rows)
slope_a, r2_a = bench.fit_power(SIZES_A, times)
ok_a = bench.verdict(slope_a, 1.0, r2_a)


# -- B: construction against |S|, k = 2 ----------------------------------

bench.rule("B.  Prop 2 -- construction against |S|, k = 2, |A| = 1   (claim: |S|^2)")
SIZES_B = [64, 96, 144, 216, 324, 486, 729, 1024]
rows, times = construction(SIZES_B, k=2)
bench.table(["|S|", "windows", "capacity", "seconds"], rows)
slope_b, r2_b = bench.fit_power(SIZES_B, times)
ok_b = bench.verdict(slope_b, 2.0, r2_b)


# -- C: construction against k, |S| fixed --------------------------------

bench.rule("C.  Prop 2 -- construction against k, |S| = 5   (claim: |S|^k, so ln|S| per step)")
import math

# |S| = 5 rather than 8: it buys three more points on the k axis before the
# table would pass 2^22 entries, above which the implementation switches to
# a dict -- a different data structure with different asymptotics.
K_VALUES = [2, 3, 4, 5, 6, 7, 8, 9]
cgs_c = bench.random_cgs(5)
rows, times = [], []
for k in K_VALUES:
    strategy = bench.kbounded_strategy(cgs_c, ["a0"], k)
    seconds = bench.timed(lambda: KBoundedMonitor(cgs_c, strategy), 3)
    monitor = KBoundedMonitor(cgs_c, strategy)
    rows.append([k, monitor.index.capacity, monitor.dense, "{0:.6f}".format(seconds)])
    times.append(seconds)
bench.table(["k", "capacity", "dense", "seconds"], rows)
rate_c, r2_c = bench.fit_exponential(K_VALUES, times)
ok_c = bench.verdict(rate_c, math.log(5), r2_c, tolerance=0.25, what="ln-rate")


# -- D: per-step runtime against |S| -------------------------------------

bench.rule("D.  Prop 1 -- per-step runtime against |S|   (claim: O(1) lookup, so flat)")
SIZES_D = [1000, 4000, 16000, 64000, 256000, 1024000]
STEPS = 20000
rows, times = [], []
for n in SIZES_D:
    cgs = bench.random_cgs(n)
    strategy = bench.kbounded_strategy(cgs, ["a0"], 1)
    monitor = KBoundedMonitor(cgs, strategy)
    steps = bench.compliant_walk(cgs, ["a0"], STEPS)

    def run(monitor=monitor, steps=steps):
        # no reset needed: the walk is compliant, so nothing accumulates and
        # repeats simply keep sliding the window
        for state, profile in steps:
            monitor.observe(state, profile)

    seconds = bench.timed(run, 3)
    per_step = seconds / STEPS
    rows.append([n, "{0:.4f}".format(seconds), "{0:.3f}".format(per_step * 1e6)])
    times.append(per_step)
bench.table(["|S|", "seconds/20k", "microseconds/step"], rows)
ok_d = bench.verdict_flat(SIZES_D, times)
print("  (the residual drift is the memory hierarchy: a 128k-entry list no")
print("   longer fits in cache. The claim is about operation count.)")


# -- E: per-step runtime against |A| -------------------------------------

bench.rule("E.  Props 1-2 -- per-step runtime against |A|   (claim: linear in |A|)")
AGENTS = 12
COALITIONS = list(range(1, AGENTS + 1))
# |S| kept small: delta holds n_actions^|Ag| entries per state, so widening
# the agent axis is what costs here, not the state axis.
cgs_e = bench.random_cgs(20, n_agents=AGENTS)
rows, times = [], []
for size in COALITIONS:
    coalition = list(cgs_e.agents[:size])
    strategy = bench.kbounded_strategy(cgs_e, coalition, 1)
    monitor = KBoundedMonitor(cgs_e, strategy)
    steps = bench.compliant_walk(cgs_e, coalition, STEPS)

    def run(monitor=monitor, steps=steps):
        # no reset needed: the walk is compliant, so nothing accumulates and
        # repeats simply keep sliding the window
        for state, profile in steps:
            monitor.observe(state, profile)

    seconds = bench.timed(run, 3)
    per_step = seconds / STEPS
    rows.append([size, "{0:.3f}".format(per_step * 1e6)])
    times.append(per_step)
bench.table(["|A|", "microseconds/step"], rows)
ok_e = bench.verdict_affine(COALITIONS, times, what="agent (microseconds)")


# -- F: total runtime against |omega| ------------------------------------

bench.rule("F.  Props 1-2 -- total runtime against trace length   (claim: linear)")
LENGTHS = [16000, 32000, 64000, 128000, 256000, 512000, 1024000]
cgs_f = bench.random_cgs(500)
strategy_f = bench.kbounded_strategy(cgs_f, ["a0"], 1)
rows, times = [], []
for length in LENGTHS:
    monitor = KBoundedMonitor(cgs_f, strategy_f)
    steps = bench.compliant_walk(cgs_f, ["a0"], length)

    def run(monitor=monitor, steps=steps):
        # no reset needed: the walk is compliant, so nothing accumulates and
        # repeats simply keep sliding the window
        for state, profile in steps:
            monitor.observe(state, profile)

    seconds = bench.timed(run, 3)
    rows.append([length, "{0:.4f}".format(seconds)])
    times.append(seconds)
bench.table(["|omega|", "seconds"], rows)
slope_f, r2_f = bench.fit_power(LENGTHS, times)
ok_f = bench.verdict(slope_f, 1.0, r2_f)


bench.rule("Summary")
for name, ok in [("A |S|, k=1", ok_a), ("B |S|, k=2", ok_b), ("C k", ok_c),
                 ("D O(1) lookup", ok_d), ("E |A|", ok_e), ("F |omega|", ok_f)]:
    print("  {0:<16} {1}".format(name, "ok" if ok else "OFF"))
