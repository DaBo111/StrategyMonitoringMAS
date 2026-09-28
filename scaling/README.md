# Measuring the asymptotic claims

Tests against the complexity claims - time and space, construction
and runtime. Each varies one parameter, holds the rest fixed, and fits the
measurements in log space; the fitted exponent is compared against the claimed
one.

```bash
python 01_kbounded.py       # k-bounded and memoryless
python 02_natural.py        # natural memoryless
python 03_recall.py         # natural recall, product DFST
python 04_adherence.py      # strategy-adherence M^S
python 05_construction.py   # end-to-end construction, and space
```

Measured on CPython 3.10.0, Windows 11, AMD64.

## Result

**Every claim holds.**

| | Claim | Varied | Range | Predicted | Measured | R² |
| --- | --- | --- | --- | --- | --- | --- |
| 1A | `O(\|S\|^k·\|A\|)` time | `\|S\|`, k=1 | →256 000 | 1.00 | **1.03** | 0.997 |
| 1B | same | `\|S\|`, k=2 | →1024 | 2.00 | **2.10** | 1.000 |
| 1C | same | k, `\|S\|`=5 | k→9 | ln 5 = 1.61 | **1.59** | 0.997 |
| 1D | lookup `O(1)` | `\|S\|` ×1024 | →1 024 000 | 0.00 | **0.038** | — |
| 1E | `O(\|A\|·\|ω\|)` | `\|A\|` | →12 | linear | **0.425 µs/agent** | 0.999 |
| 1F | same | `\|ω\|` | →1 024 000 | 1.00 | **1.00** | 1.000 |
| 2A | `O(\|A\|·\|S\|·k)` | k by gate count | k→16 381 | 1.00 | **0.98** | 0.999 |
| 2B | same | k by gate size | k→3999 | 1.00 | **0.98** | 0.999 |
| 2C | same | `\|S\|` | →64 000 | 1.00 | **0.98** | 1.000 |
| 2D | same | `\|A\|` | →12 | linear | linear | 1.000 |
| 2E | same | k both ways at once | k→799 601 | 1.00 | **0.96** | 0.994 |
| 3A | `O(m^{\|A\|}·2^{\|Ap\|}·\|A\|)` | `\|Ap\|` | →15 | ln 2 = 0.69 | **0.68** | 0.999 |
| 3B | same | product size | →257 | 1.00 | **0.87** | 0.992 |
| 3C | same | m | →1025 | 1.00 | **0.90** | 0.991 |
| 4A | `O(\|S\|^k·\|A\| + \|S\|·\|E\|)` | `\|S\|`, k=1 | →1024 | 2.00 | **1.96** | 1.000 |
| 4B | `O(\|A\|·\|ω\|)` | `\|ω\|` | →640 000 | 1.00 | **1.00** | 1.000 |
| 4C | verdict test `O(1)` | `\|S\|` ×32 | →800 | 0.00 | **0.005** | — |
| 5A | construction, end to end | `\|S\|`, k=1 | →128 000 | 1.00 | **1.03** | 0.991 |
| 5B | construction, end to end | `\|S\|`, k=2 | →1024 | 2.00 | **2.13** | 1.000 |
| 5C | **space** `O(\|S\|·\|A\|)` | `\|S\|`, k=1 | →64 000 | 1.00 | **1.00** | 1.000 |
| 5D | **space** `O(\|S\|^k)` | `\|S\|`, k=2 | →1024 | 2.00 | **1.99** | 1.000 |
| 5E | **space** `2^{\|Ap\|}` | `\|Ap\|` | →14 | ln 2 = 0.69 | **0.68** | 0.998 |

The fits above their claim, at `k = 2`, are the memory hierarchy, not extra work — see
[Construction counts addresses](#construction-counts-addresses).

### The direct-address table gives constant time

The sharpest result is 1A against 1D. The table is built in `|S|^k`, but a
lookup into it must not depend on `|S|` at all, which is why the implementation
addresses it directly rather than hashing:

```
  |S|         microseconds/step
  1000        2.855
  4000        2.870
  16000       2.874
  64000       2.956
  256000      3.433
  1024000     3.702
```

`|S|` grows **1024×** and the per-step cost grows **1.30×**. The residual is *probably* the
memory hierarchy: a million-entry list probably got cache missed.

### Space is also as claimed

```
  |S|     capacity  peak MB  bytes per state
  2000    2001      0.46     241
  4000    4001      0.92     241
  8000    8001      1.83     240
  16000   16001     3.66     240
  32000   32001     7.33     240
  64000   64001     14.65    240
```

Flat at 240 bytes per state over a 32× range (exponent 1.00, R² 1.000). At
`k = 2` the same measurement gives 1.99, and the product DFST grows at ln 2 in
`|Ap|` - so the "and space" half holds as stated.

### Construction: tabulation is the larger share

Tests 1A–1B time the monitor with its strategy already tabulated, but
tabulation is itself `Θ(|S|^k)`. Timing the whole pipeline:

| `\|S\|`, k=2 | windows | tabulate | monitor | total | tabulate share |
| --- | --- | --- | --- | --- | --- |
| 64 | 4 160 | 0.0024 | 0.0015 | 0.0039 | 62% |
| 256 | 65 792 | 0.0480 | 0.0295 | 0.0774 | 62% |
| 1024 | 1 049 600 | 0.9215 | 0.4891 | 1.4106 | 65% |

It was the smaller, at 33% for `|S| = 1024`, until construction stopped
recomputing addresses.

### Construction counts addresses

1C used to fit **1.79** against ln 5 = 1.61. The monitor was built by computing
each window's address from its `k` states with `index_of` — a factor `k` the
claim does not have. Construction now walks the windows in address order and
takes each address as a running count; `index_of` is left for tables not
tabulated in that order, and `M^S` addresses its obligations by extending their
prefixes. 1C now fits **1.59**, and the `k = 2` monitor at `|S| = 1024` builds
in 0.49 s instead of 1.82 s.

What excess remains at `k = 2` (1B, 5B) is the memory hierarchy, not operation
count. Per window, construction costs 0.35–0.39 µs up to 20 880 windows and
0.45–0.47 µs from 46 872 to 1 049 600, flat over the last 22×; fitting
`|S| ≥ 216` alone gives **2.02**. Tabulation, 65% of 5B, climbs from 0.58 to
0.88 µs per window as its dict outgrows the cache.


## A CPython technicality on recursion depth

Test 2B originally crashed. A gate is a binary tree, so a wide conjunction is a
deep tree, and every recursive traversal - `evaluate`, `variables`, `__str__` —
overflowed CPython's 1000-frame stack past roughly 800 terms. It is depth that
binds, not size: growing `k` by gate *count* (2A) has no such ceiling and ran to
`k = 16 381`. `complexity` is iterative for the same reason.

Fixing it needed no rewriting of the formula, so there is no blowup to trade
against. Measuring the two
traversals separately:

| | recursive | iterative | |
| --- | --- | --- | --- |
| `variables()` | exponent **1.30** | exponent **0.96** | recursion concatenated a fresh list per node |
| `evaluate()` | — | **7–9.5× slower** at every depth | an explicit stack cannot short-circuit `&` and `\|` |

So `variables()` is now iterative unconditionally, while `evaluate()` keeps recursion and each
`And`/`Or`/`Not` guards its own subtree, falling back only on overflow. Where
the guard sits matters more than whether it is there:

| | construction, `\|S\|`=2000 | |
| --- | --- | --- |
| before the fix | 0.01775 s | crashes past ~800 terms |
| single wrapper method | 0.02103 s | **+18%** |
| guard on each node | 0.01752 s | **no measurable cost** |

A `try` that never gets invoked is far cheaper than an extra Python call. The caught
subtrees are disjoint, so the fallback stays linear - measured 2.30× per
doubling of width, against 4× for a quadratic one. Gates now work to at least
20 000 terms; `tests/test_model.py::TestDeepGates` pins all three traversals.

Sweep 2B stays capped at 800 anyway, for the reason the `k` test stops below
`2^22` entries: past the boundary a different algorithm runs, and a fit across
it would be a curve made of two pieces.

## Method

Timings are the **minimum** of several repeats with the garbage collector
disabled, since timing noise is one-sided — the fastest run is the least
disturbed. Space is peak Python allocation under `tracemalloc`, measured in a
separate pass because tracing distorts timings. Sizes are capped by two limits
rather than by wall time: peak memory stays a few hundred MB, and no `k`-bounded
sweep crosses `2^22` table entries, above which the implementation switches from
a list to a dict - a different data structure with different asymptotics, so a
test crossing it wouldn't make sense.

Three tests were used:

| Claim shape | Fit | |
| --- | --- | --- |
| `T = O(n^c)` | `log T` vs `log n` | slope estimates `c` |
| `T = O(b^x)` | `log T` vs `x` | slope estimates `ln b` |
| `T = O(1)` in `n` | spread of `T` | R² is meaningless here |
| linear with overhead | `T = a + b·n` | a power law under-reads it |


| File | |
| --- | --- |
| `bench.py` | model and strategy generators, timing, space, the three fits |
| `01_kbounded.py` | k-bounded and memoryless, six sweeps |
| `02_natural.py` | natural memoryless, four sweeps |
| `03_recall.py` | natural recall, three sweeps |
| `04_adherence.py` | strategy adherence, three sweeps |
| `05_construction.py` | end-to-end construction and space, five sweeps |
