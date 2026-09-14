# Measuring the asymptotic claims

Twenty-one sweeps against the complexity claims of Propositions 1, 2, 4, 5 and
6 — time and space, construction and runtime. Each varies one parameter, holds
the rest fixed, and fits the measurements in log space; the fitted exponent is
compared against the claimed one.

```bash
python 01_kbounded.py       # Props 1, 2  -- k-bounded and memoryless
python 02_natural.py        # Prop 4      -- natural memoryless
python 03_recall.py         # Prop 5      -- natural recall, product DFST
python 04_adherence.py      # Prop 6      -- strategy-adherence M^S
python 05_construction.py   # end-to-end construction, and space
```

Measured on CPython 3.10.0, Windows 11, AMD64. Absolute times are not the
point; the exponents are, and those are machine-independent.

## Result

**Every claim holds.** No sweep exceeded its bound.

| | Claim | Varied | Range | Predicted | Measured | R² |
| --- | --- | --- | --- | --- | --- | --- |
| 1A | `O(\|S\|^k·\|A\|)` time | `\|S\|`, k=1 | →256 000 | 1.00 | **1.04** | 1.000 |
| 1B | same | `\|S\|`, k=2 | →1024 | 2.00 | **2.02** | 1.000 |
| 1C | same | k, `\|S\|`=5 | k→9 | ln 5 = 1.61 | **1.79** | 1.000 |
| 1D | lookup `O(1)` | `\|S\|` ×1024 | →1 024 000 | 0.00 | **0.046** | — |
| 1E | `O(\|A\|·\|ω\|)` | `\|A\|` | →12 | linear | **0.422 µs/agent** | 0.999 |
| 1F | same | `\|ω\|` | →1 024 000 | 1.00 | **1.00** | 1.000 |
| 2A | `O(\|A\|·\|S\|·k²)` | k by gate count | k→8190 | ≤ 2.00 | **0.95** | 0.999 |
| 2B | same | k by gate size | k→1600 | ≤ 2.00 | **0.97** | 0.999 |
| 2C | same | `\|S\|` | →64 000 | 1.00 | **1.02** | 1.000 |
| 2D | same | `\|A\|` | →12 | linear | linear | 1.000 |
| 3A | `O(m^{\|A\|}·2^{\|Ap\|}·\|A\|)` | `\|Ap\|` | →15 | ln 2 = 0.69 | **0.69** | 0.999 |
| 3B | same | product size | →257 | 1.00 | **0.89** | 0.994 |
| 3C | same | m | →1025 | 1.00 | **0.90** | 0.991 |
| 4A | `O(\|S\|^k·\|A\| + \|S\|·\|E\|)` | `\|S\|`, k=1 | →1024 | 2.00 | **2.03** | 1.000 |
| 4B | `O(\|A\|·\|ω\|)` | `\|ω\|` | →640 000 | 1.00 | **1.00** | 1.000 |
| 4C | verdict test `O(1)` | `\|S\|` ×32 | →800 | 0.00 | **0.008** | — |
| 5A | construction, end to end | `\|S\|`, k=1 | →128 000 | 1.00 | **1.05** | 1.000 |
| 5B | construction, end to end | `\|S\|`, k=2 | →1024 | 2.00 | **2.06** | 1.000 |
| 5C | **space** `O(\|S\|·\|A\|)` | `\|S\|`, k=1 | →64 000 | 1.00 | **1.00** | 1.000 |
| 5D | **space** `O(\|S\|^k)` | `\|S\|`, k=2 | →1024 | 2.00 | **1.99** | 1.000 |
| 5E | **space** `2^{\|Ap\|}` | `\|Ap\|` | →14 | ln 2 = 0.69 | **0.68** | 0.998 |

### The direct-address table earns its place

The sharpest result is 1A against 1D. The table is built in `|S|^k`, but a
lookup into it must not depend on `|S|` at all — which is why the paper
addresses it directly rather than hashing:

```
  |S|         microseconds/step
  1000        2.98
  4000        3.00
  16000       2.97
  64000       3.06
  256000      3.28
  1024000     4.02
```

`|S|` grows **1024×** and the per-step cost grows **1.35×**. The residual is the
memory hierarchy — a million-entry list is nowhere near cache — not the
algorithm.

### Space is as claimed, and remarkably regular

```
  |S|     capacity  peak MB  bytes per state
  2000    2001      0.46     241
  4000    4001      0.92     240
  8000    8001      1.83     240
  16000   16001     3.66     240
  32000   32001     7.33     240
  64000   64001     14.65    240
```

Flat at 240 bytes per state over a 32× range (exponent 1.00, R² 1.000). At
`k = 2` the same measurement gives 1.99, and the product DFST grows at ln 2 in
`|Ap|` — so the "and space" half of Propositions 1, 2 and 5 holds as stated.

### Construction: tabulation is the smaller half

Sweeps 1A–1B time the monitor with its strategy already tabulated, but
tabulation is itself `Θ(|S|^k)`. Timing the whole pipeline:

| `\|S\|`, k=2 | windows | tabulate | monitor | total | tabulate share |
| --- | --- | --- | --- | --- | --- |
| 64 | 4 160 | 0.0024 | 0.0068 | 0.0092 | 26% |
| 256 | 65 792 | 0.0448 | 0.1105 | 0.1553 | 29% |
| 1024 | 1 049 600 | 0.9105 | 1.8225 | 2.7330 | 33% |

Both halves carry the same exponent, so the claim is unaffected; the split is
worth knowing only because it says where the time goes.

## Two bounds that hold but are not tight

**Proposition 4's `k²` is loose; the cost is `Θ(k)`.** Since
`compl(γ) = Σ_{(gate,act)} |gate|`, evaluating every gate at a state costs the
sum of the gate sizes, which *is* `k`. The proof reaches `k²` by bounding the
number of gates by `k` and the cost of each by `k` separately, but under this
definition the two cannot both be extremal: `g` gates of size `s` give
`k = g·s` and work `g·s = k`. Growing `k` by gate count and by gate size gives
0.95 and 0.97 over `k` up to 8190, so the bound can be tightened to
`O(|A| · |S| · k)`.

**Proposition 5's `m^{|A|}` is a worst case rarely approached.** The product is
built over *reachable* combinations, and two things keep it small:

- identical strategies stay on the diagonal — give every agent the same regex
  and the product has `m` states however large `|A|` gets;
- `m` counts all DFST states, including non-recurrent ones. With distinct
  regexes of `m = 3`, the reachable product came to `2^{|A|}+1`, not `3^{|A|}` —
  257 states where the bound allows 6561.

Refitting against the product actually constructed gives 0.89, so the
construction is linear in what it builds. The bound is correct; it
over-approximates.

## One implementation limit found, and fixed

Sweep 2B originally crashed. A gate is a binary tree, so a wide conjunction is a
deep tree, and every recursive traversal — `evaluate`, `variables`, `__str__` —
overflowed CPython's 1000-frame stack past roughly 800 terms. It is depth that
binds, not size: growing `k` by gate *count* (2A) has no such ceiling and ran to
`k = 8190`.

Fixing it needed no rewriting of the formula, so there is no blowup to trade
against: the tree is untouched and only the traversal changes. Measuring the two
traversals separately is what decided the design:

| | recursive | iterative | |
| --- | --- | --- | --- |
| `variables()` | exponent **1.30** | exponent **0.96** | recursion concatenated a fresh list per node |
| `evaluate()` | — | **7–9.5× slower** at every depth | an explicit stack cannot short-circuit `&` and `\|` |

So `variables()` is now iterative unconditionally — it was superlinear, and
nothing calls it in a loop — while `evaluate()` keeps recursion and each
`And`/`Or`/`Not` guards its own subtree, falling back only on overflow. Where
the guard sits matters more than whether it is there:

| | construction, `\|S\|`=2000 | |
| --- | --- | --- |
| before the fix | 0.01775 s | crashes past ~800 terms |
| single wrapper method | 0.02103 s | **+18%** |
| guard on each node | 0.01752 s | **no measurable cost** |

A `try` that never fires is far cheaper than an extra Python call. The caught
subtrees are disjoint, so the fallback stays linear — measured 2.30× per
doubling of width, against 4× for a quadratic one. Gates now work to at least
20 000 terms; `tests/test_model.py::TestDeepGates` pins all three traversals.

Sweep 2B stays capped at 800 anyway, for the reason the `k` sweep stops below
`2^22` entries: past the boundary a different algorithm runs, and a fit across
it would be a curve made of two pieces.

## Method

Timings are the **minimum** of several repeats with the garbage collector
disabled, since timing noise is one-sided — the fastest run is the least
disturbed. Space is peak Python allocation under `tracemalloc`, measured in a
separate pass because tracing distorts timings. Sizes are capped by two limits
rather than by wall time: peak memory stays a few hundred MB, and no `k`-bounded
sweep crosses `2^22` table entries, above which the implementation switches from
a list to a dict — a different data structure with different asymptotics, so a
sweep crossing it would silently stop measuring the claim.

Three fits are used, and choosing the wrong one produces false failures:

| Claim shape | Fit | |
| --- | --- | --- |
| `T = O(n^c)` | `log T` vs `log n` | slope estimates `c` |
| `T = O(b^x)` | `log T` vs `x` | slope estimates `ln b` |
| `T = O(1)` in `n` | spread of `T` | R² is meaningless here |
| linear with overhead | `T = a + b·n` | a power law under-reads it |

**R² is the wrong test for a flat claim.** It reports the share of variance the
fit explains, so where the claim holds and the residual is all noise, R² is near
zero. Sweeps 1D and 4C are judged on whether the spread stays small while the
parameter ranges over orders of magnitude.

**A power law is the wrong fit for a measured linear cost.** Every step carries
interpreter overhead that `O(·)` abstracts away, so the truth is `a + b·x` with
`a > 0`; fitting `x^c` returns `c < 1` however constant the marginal cost is.
Sweep 1E fits the affine model and recovers 0.422 µs per agent on 2.357 µs of
fixed overhead, R² 0.999.

**A benchmark can silently not run the code it claims to measure.** In the
generated models agent 0's action fixes the successor, so a compliant walk by a
coalition containing it is deterministic: it settles into a short cycle, visits
4 of 25 states, and never validates enough windows for a counter to reach zero.
Proposition 6's cascade and its positive verdict both went unmeasured until the
coalition was moved to agent 1 — with the fix, every run in 4B and 4C reaches
`⊤ˢ_𝒢`, which is the evidence that the path executed.

## What this does and does not establish

A fit over a finite range corroborates an asymptotic claim; it does not prove
one, and says nothing past the largest size tried. Constant factors dominate at
small sizes, so each sweep spans enough orders of magnitude for the leading term
to show. The models are generated (`bench.py`), so these are the claims'
behaviour on synthetic structure, not on any particular application.

| File | |
| --- | --- |
| `bench.py` | model and strategy generators, timing, space, the three fits |
| `01_kbounded.py` | Propositions 1 and 2, six sweeps |
| `02_natural.py` | Proposition 4, four sweeps |
| `03_recall.py` | Proposition 5, three sweeps |
| `04_adherence.py` | Proposition 6, three sweeps |
| `05_construction.py` | end-to-end construction and space, five sweeps |
