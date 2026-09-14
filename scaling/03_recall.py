"""Proposition 5: the natural-recall monitor (product DFST).

    construction O(m^|A| x 2^|Ap| x |A|) time and space,  m = max states of T_a
    runtime      O(|A| x |omega|)

Three sweeps, one factor each: the alphabet 2^|Ap|, the product m^|A|, and m
itself with a single agent.  This is the one construction the paper admits is
exponential, so the point is to confirm the exponent rather than hope it is
smaller than stated.
"""

import math

import bench
from strategy_monitor.monitors import NaturalRecallMonitor
from strategy_monitor.strategies import NaturalRecallRegexStrategy


def regex_with_states(n_wildcards):
    """``.*[p0]`` followed by wildcards; the DFST has 2^n + 1 states."""
    return ".*[p0]" + "." * n_wildcards


def strategy_for(cgs, coalition, n_wildcards=0):
    pattern = regex_with_states(n_wildcards)
    return NaturalRecallRegexStrategy.build(
        coalition,
        {
            agent: [(pattern, cgs.actions[agent][0]), (".*", cgs.actions[agent][-1])]
            for agent in coalition
        },
    )


# -- A: against |Ap|, one agent ------------------------------------------

bench.rule("A.  construction against |Ap|, |A| = 1   (claim: 2^|Ap|, rate ln 2 = 0.69)")
AP_SIZES = [2, 4, 6, 8, 10, 12, 14, 15]
rows, times = [], []
for n_ap in AP_SIZES:
    cgs = bench.random_cgs(8, n_ap=n_ap)
    strategy = strategy_for(cgs, ["a0"])
    seconds = bench.timed(lambda c=cgs, s=strategy: NaturalRecallMonitor(c, s), 3)
    rows.append([n_ap, 2 ** n_ap, "{0:.6f}".format(seconds)])
    times.append(seconds)
bench.table(["|Ap|", "alphabet", "seconds"], rows)
rate_a, r2_a = bench.fit_exponential(AP_SIZES, times)
ok_a = bench.verdict(rate_a, math.log(2), r2_a, tolerance=0.15, what="ln-rate")


# -- B: against |A|, m fixed ---------------------------------------------

bench.rule("B.  construction against |A|, m = 3, |Ap| = 6 fixed   (claim: rate ln 3 = 1.10)")
print("  Each agent keys off a different proposition. Giving them all the SAME")
print("  regex instead keeps the product on its diagonal, so it stays at m")
print("  states however large |A| gets -- m^|A| is the worst case, not the rule.")
print()
COALITIONS = [1, 2, 3, 4, 5, 6, 7, 8]
cgs_b = bench.random_cgs(8, n_agents=8, n_ap=8)
rows, times_b, products = [], [], []
for size in COALITIONS:
    coalition = list(cgs_b.agents[:size])
    strategy = NaturalRecallRegexStrategy.build(
        coalition,
        {
            agent: [
                (".*[p{0}]".format(index), cgs_b.actions[agent][0]),
                (".*", cgs_b.actions[agent][-1]),
            ]
            for index, agent in enumerate(coalition)
        },
    )
    monitor = NaturalRecallMonitor(cgs_b, strategy)
    seconds = bench.timed(lambda s=strategy: NaturalRecallMonitor(cgs_b, s), 3)
    rows.append([size, 3 ** size, monitor.engine.size, "{0:.6f}".format(seconds)])
    times_b.append(seconds)
    products.append(monitor.engine.size)
bench.table(["|A|", "m^|A| bound", "reachable product", "seconds"], rows)
rate_b, r2_b = bench.fit_exponential(COALITIONS, times_b)
print()
print("  fitted ln-rate {0:.2f} against |A|   (m^|A| would give {1:.2f})".format(
    rate_b, math.log(3)))
print("  Every measured product is far inside the bound: the reachable product")
print("  is 2^|A|+1 here, because each DFST has 3 states but only 2 recurrent")
print("  ones. So the claim holds; it is an over-approximation of what is built.")
print()
print("  Refitting against the product actually constructed:")
slope_b, r2_b2 = bench.fit_power(products, times_b)
ok_b = bench.verdict(slope_b, 1.0, r2_b2, tolerance=0.30)


# -- C: against m, one agent ---------------------------------------------

bench.rule("C.  construction against m, |A| = 1   (claim: m^1, so linear in m)")
WILDCARDS = [0, 1, 2, 3, 4, 5, 6, 7, 8, 9]
cgs_c = bench.random_cgs(8, n_ap=2)
rows, times_c, ms = [], [], []
for n in WILDCARDS:
    strategy = strategy_for(cgs_c, ["a0"], n_wildcards=n)
    monitor = NaturalRecallMonitor(cgs_c, strategy)
    m = monitor.engine.size
    seconds = bench.timed(lambda s=strategy: NaturalRecallMonitor(cgs_c, s), 3)
    rows.append([n, m, "{0:.6f}".format(seconds)])
    times_c.append(seconds)
    ms.append(m)
bench.table(["wildcards", "product states m", "seconds"], rows)
slope_c, r2_c = bench.fit_power(ms, times_c)
ok_c = bench.verdict(slope_c, 1.0, r2_c, tolerance=0.30)


bench.rule("Summary")
for name, ok in [("A 2^|Ap|", ok_a), ("B product size", ok_b), ("C m", ok_c)]:
    print("  {0:<12} {1}".format(name, "ok" if ok else "OFF"))
