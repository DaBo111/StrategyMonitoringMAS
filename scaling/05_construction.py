"""Construction end to end, and the space half of the claims.

Propositions 1, 2 and 5 each claim their construction bound for "time **and
space**", and 4 claims O(|S| x |A|) space at runtime.  Scripts 01-04 measure
only time, and they time the monitor with its strategy already tabulated.  This
script closes both gaps:

  A, B   the whole pipeline -- tabulate the strategy, then build the monitor --
         reported as a split, since tabulation is itself O(|S|^k) and is the
         larger half
  C, D   monitor space against |S| at k = 1 and k = 2
  E      product DFST space against |Ap|

Space is peak Python allocation during the build, via ``tracemalloc``.  It is
measured in a separate pass from time because tracing slows the build enough to
distort timings.
"""

import math

import bench
from strategy_monitor.monitors import KBoundedMonitor, NaturalRecallMonitor
from strategy_monitor.strategies import NaturalRecallRegexStrategy

REPEATS = 3


def pipeline(sizes, k):
    """Tabulation, monitor build, and the total, against |S|."""
    rows, totals = [], []
    for n in sizes:
        cgs = bench.random_cgs(n)
        tabulate = bench.timed(lambda c=cgs: bench.kbounded_strategy(c, ["a1"], k), REPEATS)
        strategy = bench.kbounded_strategy(cgs, ["a1"], k)
        build = bench.timed(lambda c=cgs, s=strategy: KBoundedMonitor(c, s), REPEATS)
        rows.append(
            [
                n,
                len(strategy.table),
                "{0:.4f}".format(tabulate),
                "{0:.4f}".format(build),
                "{0:.4f}".format(tabulate + build),
                "{0:.0f}%".format(100 * tabulate / (tabulate + build)),
            ]
        )
        totals.append(tabulate + build)
    bench.table(
        ["|S|", "windows", "tabulate", "monitor", "total", "tabulate share"], rows
    )
    return totals


bench.rule("A.  end-to-end construction against |S|, k = 1   (claim: linear)")
SIZES_A = [2000, 4000, 8000, 16000, 32000, 64000, 128000]
totals_a = pipeline(SIZES_A, k=1)
slope_a, r2_a = bench.fit_power(SIZES_A, totals_a)
ok_a = bench.verdict(slope_a, 1.0, r2_a)


bench.rule("B.  end-to-end construction against |S|, k = 2   (claim: |S|^2)")
SIZES_B = [64, 128, 256, 512, 1024]
totals_b = pipeline(SIZES_B, k=2)
slope_b, r2_b = bench.fit_power(SIZES_B, totals_b)
ok_b = bench.verdict(slope_b, 2.0, r2_b)


bench.rule("C.  monitor SPACE against |S|, k = 1   (claim: O(|S| x |A|) space)")
SIZES_C = [2000, 4000, 8000, 16000, 32000, 64000]
rows, peaks_c = [], []
for n in SIZES_C:
    cgs = bench.random_cgs(n)
    strategy = bench.kbounded_strategy(cgs, ["a1"], 1)
    peak, monitor = bench.measure_space(lambda c=cgs, s=strategy: KBoundedMonitor(c, s))
    rows.append([n, monitor.index.capacity, "{0:.2f}".format(peak / 2 ** 20),
                 "{0:.0f}".format(peak / n)])
    peaks_c.append(peak)
bench.table(["|S|", "capacity", "peak MB", "bytes per state"], rows)
slope_c, r2_c = bench.fit_power(SIZES_C, peaks_c)
ok_c = bench.verdict(slope_c, 1.0, r2_c, tolerance=0.15)


bench.rule("D.  monitor SPACE against |S|, k = 2   (claim: O(|S|^k) space)")
SIZES_D = [64, 128, 256, 512, 1024]
rows, peaks_d = [], []
for n in SIZES_D:
    cgs = bench.random_cgs(n)
    strategy = bench.kbounded_strategy(cgs, ["a1"], 2)
    peak, monitor = bench.measure_space(lambda c=cgs, s=strategy: KBoundedMonitor(c, s))
    rows.append([n, monitor.index.capacity, "{0:.2f}".format(peak / 2 ** 20)])
    peaks_d.append(peak)
bench.table(["|S|", "capacity", "peak MB"], rows)
slope_d, r2_d = bench.fit_power(SIZES_D, peaks_d)
ok_d = bench.verdict(slope_d, 2.0, r2_d, tolerance=0.20)


bench.rule("E.  product DFST SPACE against |Ap|   (claim: 2^|Ap| space, rate ln 2)")
AP_SIZES = [4, 6, 8, 10, 12, 14]
rows, peaks_e = [], []
for n_ap in AP_SIZES:
    cgs = bench.random_cgs(8, n_ap=n_ap)
    strategy = NaturalRecallRegexStrategy.build(
        ["a1"],
        {"a1": [(".*[p0]", cgs.actions["a1"][0]), (".*", cgs.actions["a1"][-1])]},
    )
    peak, _monitor = bench.measure_space(
        lambda c=cgs, s=strategy: NaturalRecallMonitor(c, s)
    )
    rows.append([n_ap, 2 ** n_ap, "{0:.2f}".format(peak / 2 ** 20)])
    peaks_e.append(peak)
bench.table(["|Ap|", "alphabet", "peak MB"], rows)
rate_e, r2_e = bench.fit_exponential(AP_SIZES, peaks_e)
ok_e = bench.verdict(rate_e, math.log(2), r2_e, tolerance=0.15, what="ln-rate")


bench.rule("Summary")
for name, ok in [
    ("A end-to-end k=1", ok_a),
    ("B end-to-end k=2", ok_b),
    ("C space k=1", ok_c),
    ("D space k=2", ok_d),
    ("E space 2^|Ap|", ok_e),
]:
    print("  {0:<20} {1}".format(name, "ok" if ok else "OFF"))
