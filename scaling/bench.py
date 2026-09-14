"""Model generators and the timing harness shared by the experiments.

Method.  Each experiment varies one parameter, holds the rest fixed, and fits a
straight line through the measurements in log space.  For a claim of the form
``T = O(n^c)`` the fit is ``log T`` against ``log n`` and the slope estimates
``c``; for a claim exponential in a parameter (``|S|^k`` as ``k`` varies) the
fit is ``log T`` against ``k`` and the slope estimates ``ln |S|``.  A verdict is
reported when the measured slope lands within a tolerance of the predicted one
and the fit is tight.

What this can and cannot show.  A measured fit over a finite range corroborates
an asymptotic claim; it does not prove one, and it cannot rule out behaviour
past the largest size tried.  Constant factors dominate at small sizes, so every
sweep is chosen wide enough that the leading term shows.  Timings are the
minimum of several repeats with the garbage collector off, because timing noise
is one-sided: the fastest run is the one least disturbed.
"""

import gc
import itertools
import math
import os
import random
import sys
import time
import tracemalloc

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
if ROOT not in sys.path:
    sys.path.insert(0, ROOT)

from strategy_monitor import CGS  # noqa: E402
from strategy_monitor.strategies import (  # noqa: E402
    KBoundedStrategy,
    NaturalMemorylessStrategy,
    NaturalRecallRegexStrategy,
)


# -- models --------------------------------------------------------------


def random_cgs(n_states, n_agents=2, n_ap=2, n_actions=2, seed=0):
    """A total CGS of the requested shape.

    Agent 0's action picks the successor, so the transition relation branches
    ``n_actions`` ways and stays total whatever the other agents do.  The
    remaining agents are wildcards, which keeps the model file small; the loader
    still expands it to the full ``delta`` of ``n_actions ** n_agents`` entries
    per state, so ``n_agents`` is the parameter to keep small.
    """
    states = ["s{0}".format(i) for i in range(n_states)]
    agents = ["a{0}".format(i) for i in range(n_agents)]
    actions = ["m{0}".format(j) for j in range(n_actions)]
    ap = ["p{0}".format(i) for i in range(n_ap)]
    rng = random.Random(seed)
    return CGS.from_dict(
        {
            "ap": ap,
            "agents": agents,
            "actions": {agent: list(actions) for agent in agents},
            "initial_state": states[0],
            "states": [
                {
                    "id": state,
                    "labels": [name for name in ap if rng.random() < 0.5],
                    "transitions": [
                        {
                            "to": states[(index * 7 + offset + 1) % n_states],
                            "profiles": [[actions[offset]] + ["*"] * (n_agents - 1)],
                        }
                        for offset in range(n_actions)
                    ],
                }
                for index, state in enumerate(states)
            ],
        }
    )


def kbounded_strategy(cgs, coalition, k):
    """A total ``k``-bounded strategy: every window of length <= k is prescribed."""
    action = {agent: cgs.actions[agent][0] for agent in coalition}
    return KBoundedStrategy.from_function(
        cgs, coalition, k, lambda window, agent: action[agent]
    )


def natural_strategy(coalition, cgs, n_gates):
    """A natural memoryless strategy whose gates are ``n_gates`` long.

    The gates are unsatisfiable until the last, so the monitor builder has to
    evaluate all of them at every state -- the worst case the ``k^2`` bound in
    Proposition 4 is about.
    """
    ap = cgs.ap
    gates = [
        ("{0} & !{0}".format(ap[index % len(ap)]), cgs.actions[coalition[0]][0])
        for index in range(n_gates - 1)
    ]
    rules = {
        agent: gates + [("true", cgs.actions[agent][0])] for agent in coalition
    }
    return NaturalMemorylessStrategy.build(coalition, rules)


def recall_strategy(coalition, cgs, n_regexes=2):
    """A natural recall strategy over the model's own propositions."""
    first = cgs.ap[0]
    rules = {
        agent: [
            (".*[{0}].*".format(first), cgs.actions[agent][0]),
            (".*", cgs.actions[agent][-1]),
        ][:n_regexes]
        + ([] if n_regexes >= 2 else [(".*", cgs.actions[agent][-1])])
        for agent in coalition
    }
    return NaturalRecallRegexStrategy.build(coalition, rules)


def walk(cgs, length, seed=0):
    """A run of the CGS: a list of ``(state, profile)`` pairs."""
    rng = random.Random(seed)
    state = cgs.initial_state
    steps = []
    for _ in range(length):
        profile = tuple(rng.choice(cgs.actions[agent]) for agent in cgs.agents)
        steps.append((state, profile))
        state = cgs.step(state, profile)
    return steps


def compliant_walk(cgs, coalition, length, seed=0):
    """A run in which the coalition plays what the generated strategies prescribe.

    Timing the compliant path matters: a deviating step additionally builds and
    appends a violation record, which is work the runtime bound is not about and
    which grows with the trace.
    """
    rng = random.Random(seed)
    state = cgs.initial_state
    steps = []
    members = set(coalition)
    for _ in range(length):
        profile = tuple(
            cgs.actions[agent][0] if agent in members else rng.choice(cgs.actions[agent])
            for agent in cgs.agents
        )
        steps.append((state, profile))
        state = cgs.step(state, profile)
    return steps


# -- timing --------------------------------------------------------------


def timed(work, repeats=5):
    """Minimum wall time of ``work`` over ``repeats`` runs, garbage collector off."""
    enabled = gc.isenabled()
    gc.disable()
    try:
        best = float("inf")
        for _ in range(repeats):
            start = time.perf_counter()
            work()
            best = min(best, time.perf_counter() - start)
        return best
    finally:
        if enabled:
            gc.enable()


def measure_space(build):
    """Peak bytes allocated while ``build()`` runs, and its result.

    ``tracemalloc`` counts Python allocations only, which is what the space
    bounds are about: the table, its entries, and the automaton states.  It
    slows the build considerably, so space is never measured in the same pass as
    time.
    """
    gc.collect()
    tracemalloc.start()
    try:
        value = build()
        _current, peak = tracemalloc.get_traced_memory()
    finally:
        tracemalloc.stop()
    return peak, value


def _slope(xs, ys):
    """Least-squares slope and R^2 of ``ys`` against ``xs``."""
    n = len(xs)
    mean_x = sum(xs) / n
    mean_y = sum(ys) / n
    sxx = sum((x - mean_x) ** 2 for x in xs)
    sxy = sum((x - mean_x) * (y - mean_y) for x, y in zip(xs, ys))
    slope = sxy / sxx
    intercept = mean_y - slope * mean_x
    ss_res = sum((y - (slope * x + intercept)) ** 2 for x, y in zip(xs, ys))
    ss_tot = sum((y - mean_y) ** 2 for y in ys)
    r2 = 1.0 if ss_tot == 0 else 1 - ss_res / ss_tot
    return slope, r2


def fit_power(sizes, times):
    """Exponent ``c`` in ``T ~ n^c``, from log T against log n."""
    return _slope([math.log(x) for x in sizes], [math.log(t) for t in times])


def fit_exponential(params, times):
    """Base-e growth rate ``r`` in ``T ~ e^(r*x)``, from log T against x."""
    return _slope(list(params), [math.log(t) for t in times])


def fit_affine(xs, ys):
    """Slope, intercept and R^2 of ``y = a + b*x``, fitted in linear space."""
    slope, r2 = _slope(list(xs), list(ys))
    n = len(xs)
    intercept = sum(ys) / n - slope * (sum(xs) / n)
    return slope, intercept, r2


# -- reporting -----------------------------------------------------------


def rule(title):
    print()
    print("=" * 78)
    print(title)
    print("=" * 78)


def table(header, rows):
    widths = [max(len(str(row[i])) for row in [header] + rows) for i in range(len(header))]
    line = "  " + "  ".join(str(h).ljust(w) for h, w in zip(header, widths))
    print(line)
    print("  " + "-" * (len(line) - 2))
    for row in rows:
        print("  " + "  ".join(str(c).ljust(w) for c, w in zip(row, widths)))


def verdict_flat(xs, times, ratio_tolerance=1.5, what="per-step time"):
    """A claim of ``O(1)`` in ``x``: the measurement must not trend with ``x``.

    R^2 is the wrong test here.  It reports the share of variance the fit
    explains, so for a genuinely flat line -- where the residual is all noise --
    it is near zero exactly when the claim holds.  What matters instead is that
    the spread stays small while ``x`` ranges over orders of magnitude.
    """
    ratio = max(times) / min(times)
    span = max(xs) / min(xs)
    slope, _r2 = fit_power(xs, times)
    ok = ratio <= ratio_tolerance
    print()
    print(
        "  {0} varies {1:.2f}x while the parameter varies {2:.0f}x".format(
            what, ratio, span
        )
    )
    print(
        "  fitted exponent {0:.3f}   claimed 0.00   -> {1}".format(
            slope, "MATCHES the claim" if ok else "OFF"
        )
    )
    return ok


def verdict_affine(xs, times, what="parameter"):
    """A claim linear in ``x``, measured where a fixed per-call cost is present.

    Every measured step carries interpreter overhead that ``O(.)`` abstracts
    away, so the truth is ``t = a + b*x`` with ``a > 0``.  Fitting a power law
    to that returns an exponent below 1 however linear the marginal cost is; the
    claim is about ``b`` being constant, so fit ``a + b*x`` directly.
    """
    slope, intercept, r2 = fit_affine(xs, times)
    ok = r2 >= 0.98 and slope > 0
    print()
    print(
        "  marginal cost {0:.3f} per unit of {1}, fixed overhead {2:.3f}".format(
            slope * 1e6, what, intercept * 1e6
        )
    )
    print(
        "  linear fit R^2 {0:.4f}   -> {1}".format(
            r2, "MATCHES the claim" if ok else "OFF"
        )
    )
    return ok


def verdict(measured, predicted, r2, tolerance=0.25, what="exponent"):
    """Print the fit against the claim and say whether it holds."""
    ok = abs(measured - predicted) <= tolerance and r2 >= 0.90
    print()
    print(
        "  fitted {0} {1:.2f}   claimed {2:.2f}   R^2 {3:.3f}   -> {4}".format(
            what, measured, predicted, r2, "MATCHES the claim" if ok else "OFF"
        )
    )
    return ok
