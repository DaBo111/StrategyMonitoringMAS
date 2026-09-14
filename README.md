# `strategy_monitor`

Runtime monitors for multi-agent systems modelled as a **concurrent game
structure** (CGS). Given a coalition and the strategy it was told to play, they
report at each observed step whether the agents are still following that
strategy, and whether the goal it was meant to secure is still guaranteed. When
either fails, a repair pipeline can re-synthesise the strategy or correct the
model and carry on.

```bash
python -m strategy_monitor demo
```

| Module | For |
| --- | --- |
| [`cgs.py`](strategy_monitor/cgs.py) | `CGS` — the model |
| [`trace.py`](strategy_monitor/trace.py) | `Trace`, `replay` |
| [`strategies.py`](strategy_monitor/strategies.py) | `KBoundedStrategy`, `NaturalMemorylessStrategy`, `NaturalRecallRegexStrategy` |
| [`monitors.py`](strategy_monitor/monitors.py) | the strategy monitors and `AdherenceMonitor` |
| [`goal.py`](strategy_monitor/goal.py) | `GoalMonitor` — four-valued LTL monitoring |
| [`suite.py`](strategy_monitor/suite.py) | `MonitorSuite` — compose any subset |
| [`repair.py`](strategy_monitor/repair.py) | `RepairPipeline` |
| [`verify.py`](strategy_monitor/verify.py) | `enforces` — does a strategy really win? |
| [`vitamin.py`](strategy_monitor/vitamin.py) | ATL checking, NatATL synthesis (optional) |
| [`spot_backend.py`](strategy_monitor/spot_backend.py) | alternative LTL→Büchi translation (optional) |
| [`verdict.py`](strategy_monitor/verdict.py) | `Verdict` — the four-valued domain below |
| [`ltl.py`](strategy_monitor/ltl.py), [`automata.py`](strategy_monitor/automata.py), [`regex.py`](strategy_monitor/regex.py), [`boolean.py`](strategy_monitor/boolean.py) | the LTL, automaton, regex and Boolean-gate machinery the rest is built on |

## Install

No dependencies beyond Python 3.10+.

```bash
pip install -e .
```

Two optional: **VITAMIN** adds ATL model checking and NatATL strategy
synthesis.

```bash
pip install vitamin-model-checker
```

Use 1.6+ — the `1.5` sdist has a packaging bug pip refuses. 1.6+ declares
`requires-python >= 3.11` although it runs on 3.10, where you need
`pip install --ignore-requires-python vitamin-model-checker`. Doesn't run on
3.9.

**Spot** supplies an alternative LTL→Büchi translation. It is not on PyPI; see
[Installing Spot](#installing-spot).

```bash
conda install conda-forge::spot
```

## Quick start

```python
from strategy_monitor import CGS, KBoundedStrategy, KBoundedMonitor

cgs = CGS.from_json("examples/running_example.json")
strategy = KBoundedStrategy.memoryless(
    ["a", "b"],
    {"s0": {"a": "in",  "b": "in"},
     "s1": {"a": "out", "b": "out"},
     "s2": {"a": "out", "b": "out"},
     "s3": {"a": "out", "b": "out"}},
)

monitor = KBoundedMonitor(cgs, strategy)
monitor.observe("s0", ("in", "in", "in"))     # ?
monitor.observe("s0", ("out", "in", "out"))   # ⊥
print(monitor.violations[0])
# step 1: agent 'a' played 'out' in 's0', strategy prescribes 'in' ...
```

Folding the model into the goal monitor allows verdicts where the plain LTL
monitor cannot:

```python
from strategy_monitor import GoalMonitor, replay

trace = replay(cgs, [("in", "in", "out"), ("in", "in", "in")])
word = trace.word(cgs)                                     # {p,q} {p} {p}

GoalMonitor(cgs, "G(p | (q & X p))", use_model=False).evaluate(word)   # ?
GoalMonitor(cgs, "G(p | (q & X p))", use_model=True ).evaluate(word)   # ⊤ᴳ_𝒢
```

## Verdicts

| Verdict | `str()` | Meaning |
| --- | --- | --- |
| `?` | `?` | nothing can be concluded yet |
| `⊥` | `bot` | strategy violation: some coalition member deviated |
| `⊥ᴳ` | `bot^G` | goal violation: the goal fails however the system continues |
| `⊥ᴹ` | `bot^M` | model violation: the trace is not a run of the CGS |
| `⊤ᴳ_𝒢` | `top^G_G` | the goal holds on every continuation the CGS permits |
| `⊤ˢ_𝒢` | `top^S_G` | adherence can no longer be refuted |

The positive verdicts are claims about the continuations the CGS permits, not
about arbitrary futures, so `⊥ᴹ` supersedes them: once the system leaves the
model, they no longer say anything.

## Composing a monitor

`MonitorSuite` runs whichever components you give it and reports one verdict:

```python
from strategy_monitor import MonitorSuite

MonitorSuite.build(cgs, strategy=strategy)                      # strategy only
MonitorSuite.build(cgs, strategy=strategy, adherence=True)      # ... with ⊤ˢ_𝒢
MonitorSuite.build(cgs, goal="G(p | (q & X p))")                # goal only, refined
MonitorSuite.build(cgs, goal="G p", use_model=False)            # goal only, plain LTL
MonitorSuite.build(cgs, strategy=strategy, goal="G p")          # both
```

| Option | Choices |
| --- | --- |
| `strategy=` | any strategy class, or none - by hand, from JSON, or synthesised by VITAMIN |
| `adherence=` | `False` → `?`/`⊥`; `True` adds `⊤ˢ_𝒢`. Not available for recall strategies |
| `goal=`, `use_model=` | no goal; `use_model=False` for plain LTL; `True` for the CGS-refined monitor |
| `determinize=` | recall engine: `"dfa"`, `"nfa"` or `"lazy"` |

`component_verdicts` exposes each component's own verdict; `verdict` combines
them by precedence:

```
⊥ᴹ  >  ⊥  >  ⊥ᴳ  >  ⊤ᴳ_𝒢  >  ⊤ˢ_𝒢
```

### Repair

`RepairPipeline` takes the same options, and each branch runs when its inputs
are present:

```python
RepairPipeline(cgs, strategy=strategy, synthesiser=vitamin_synthesiser("G(p || q)"))
RepairPipeline(cgs, goal="G(p | (q & X p))")     # model repair only
RepairPipeline(cgs, strategy=strategy, goal="G p", adherence=True, use_model=False)
```

* A deviation from the strategy re-synthesises from the current state and
  resumes.
* A transition the CGS does not contain corrects the model and continues; this
  needs no strategy and no monitor.
* Without a `synthesiser` there is nothing to re-synthesise, so a strategy
  violation ends in `FAILED` and monitoring stops.

## Strategies

Three types, all accepted anywhere a strategy is taken:

```python
KBoundedStrategy.memoryless(["a"], {"s0": {"a": "in"}})     # or k > 1, keyed by window
NaturalMemorylessStrategy.build(["a"], {"a": [("p", "in"), ("true", "idle")]})
NaturalRecallRegexStrategy.build(["a"], {"a": [(".*[q].*", "out"), (".*", "in")]})
```

A recall strategy is a priority-ordered list of `(regex, action)` pairs: the
agent plays the action of the first regex its observed history matches.

```python
strategy.action_for("a", [{"p"}, {"q"}])   # what it prescribes
strategy.complexity()
```

### Recall engines

All three prescribe the same actions; `determinize` only chooses where the cost
falls.

| | `"dfa"` (default) | `"nfa"` | `"lazy"` |
| --- | --- | --- | --- |
| Construction | product transducer — can be exponential | linear | linear |
| Per step | one table lookup | advance one active set per regex | one lookup once the state has been seen |
| Memory | the whole product | none beyond the NFAs | the states the run reaches |

`"lazy"` is the general-purpose choice: it builds only the states the run
actually reaches. `"dfa"` wins on small regexes, where the determinised table is
smaller than the Thompson automata; `"nfa"` is for when determinisation blows
up.

If no regex matches some history and no `default_action` was given, `"dfa"`
raises during **construction**, while `"nfa"` and `"lazy"` raise only when such
a history occurs. Add a `.*` catch-all or a default action.

## Command line

```bash
python -m strategy_monitor monitor MODEL TRACE [--strategy FILE | --synthesize OBJ]
                                               [--coalition a,b] [--adherence]
                                               [--goal LTL] [--no-model] [--k N]
                                               [--recall-engine dfa|nfa|lazy]
python -m strategy_monitor repair  MODEL TRACE [--strategy FILE | --synthesize OBJ]
                                               [--objective ATL] [--goal LTL]
                                               [--adherence] [--no-model] [--k N]
                                               [--recall-engine dfa|nfa|lazy]
python -m strategy_monitor goal   MODEL FORMULA [--trace TRACE] [--no-model]
python -m strategy_monitor check      MODEL a,b "G p"          # VITAMIN, ATL
python -m strategy_monitor synthesize MODEL a   "G(p || q)"    # VITAMIN, NatATL
python -m strategy_monitor export MODEL                        # VITAMIN model file
python -m strategy_monitor dot    MODEL positive-dfa           # Graphviz
python -m strategy_monitor backend                             # which LTL backend
python -m strategy_monitor demo
```

`monitor` needs at least one of `--strategy`, `--synthesize` or `--goal`, and
accepts any combination. One column is printed per component:

```bash
python -m strategy_monitor monitor examples/running_example.json examples/trace_goal_example.json \
    --strategy examples/strategy_natural.json --goal "G(p | (q & X p))"
```

```
monitor   : MonitorSuite[NaturalMemorylessMonitor, GoalMonitor(refined)]

  j    state  action                  strategy   goal       verdict
  0    s0     (in,in,out)             ?          ?          ?
  1    s1     (in,in,in)              ?          ⊤^G_G      ⊤^G_G
```

## File formats

### Models

Transitions are an **ordered** list of rules, first match wins; `*` is a
per-agent wildcard:

```json
{
  "ap": ["p", "q"],
  "agents": ["a", "b", "c"],
  "actions": {"a": ["in", "out", "idle"], "b": ["in", "out", "idle"], "c": ["in", "out"]},
  "initial_state": "s0",
  "states": [
    {"id": "s0", "labels": ["p", "q"], "transitions": [
        {"to": "s0", "profiles": [["*", "*", "in"]]},
        {"to": "s1", "profiles": [["in", "in", "out"], ["in", "out", "out"], ["out", "in", "out"]]},
        {"to": "s2", "profiles": [["out", "out", "out"], ["idle", "*", "*"], ["*", "idle", "*"]]}]}
  ]
}
```

Rules are expanded into the full `δ` at load time and **checked for totality** —
a model whose rules do not cover every action profile is rejected, not silently
under-specified. Add a per-state `"available"` map to narrow the protocol
`d(s, i)` where an agent cannot play everything.

### Strategies

```json
{"type": "k_bounded", "coalition": ["a", "b"], "k": 1,
 "table": {"s0": {"a": "in", "b": "in"}, "s1": {"a": "out", "b": "out"}}}

{"type": "natural_memoryless", "coalition": ["a"],
 "rules": {"a": [["p", "in"], ["q", "out"], ["true", "idle"]]}}

{"type": "natural_recall", "coalition": ["a"],
 "regexes": {"a": [[".*[q].*", "out"], [".*", "in"]]},
 "default_action": {"a": "idle"}}
```

For `k > 1` the table is a list of `{"window": [...], "actions": {...}}` entries.

Gates are Boolean formulas over `Ap` (`p & !q`, `p -> q`, `true`, …). Regexes
range over gates: atoms are bare identifiers or `[...]` gates, `.` matches any
letter, and `*`, `+`, `?`, `|` and grouping work as usual. Use
`"natural_recall_dfst"` to compile to the transducer form at load time.

### Traces

```json
{"actions": [["in", "in", "out"], ["out", "out", "in"]]}
{"states": ["s0", "s3"], "actions": [["in", "in", "out"]]}
```

Giving only actions replays them through `δ`. Giving states as well lets a trace
disagree with the model, which is what model repair acts on.

## Verifying a strategy

Does every run in which the coalition follows the strategy satisfy the goal,
whatever the other agents do?

```python
from strategy_monitor.verify import enforces

enforces(cgs, strategy, "G(p | (q & X p))")
# ['a', 'b'] enforces G((p | (q & X(p)))) (reachable under it: ['s0', 's1'])
```

Exact, doesnt need VITAMIN, and takes the full LTL grammar. A failure comes with a
counterexample in the model's own states:

```
['a'] does NOT enforce G(p); counterexample s0 s1 s2 s2(s2)^omega
```

Memoryless strategies only (`k = 1` and natural memoryless); the error says so
for the others. A strategy silent about states it cannot reach is accepted.

## LTL backend

The LTL→Büchi translation is swappable.
[Spot](https://spot.lre.epita.fr/) produces smaller automata where it is
installed.

```bash
python -m strategy_monitor backend        # what is installed, what will be used
```

| Backend | |
| --- | --- |
| `gpvw` | the built-in translation. The default |
| `spot` | delegate to Spot; **raises** if it is missing rather than falling back |
| `auto` | Spot when it imports, `gpvw` otherwise |

```bash
STRATEGY_MONITOR_LTL_BACKEND=auto python -m strategy_monitor demo
```

```python
ltl_to_buchi("G p", alphabet_of(["p"]), backend="spot")
```

Only that step is delegated, and the two are cross-checked against each other in
the test suite. Take Spot mainly for the second opinion — smaller Büchi automata
do not translate into proportionally smaller monitor tables.

### Installing Spot

Not on PyPI, and no route ships a Windows build — on Windows requires WSL.

| Route | Command |
| --- | --- |
| conda | `conda install conda-forge::spot` — linux-64 and macOS-arm64 |
| source | `pip install http://www.lre.epita.fr/dload/spot/spot-2.16.tar.gz` — needs a C++ toolchain |

For apt, add the repository first (packages target Debian Trixie, so they can
mismatch an Ubuntu release):

```bash
sudo install -d /etc/apt/keyrings \
  && sudo wget -qO /etc/apt/keyrings/lre-epita.gpg https://www.lre.epita.fr/repo/debian.gpg \
  && echo "deb [signed-by=/etc/apt/keyrings/lre-epita.gpg] http://www.lre.epita.fr/repo/debian/ stable/" \
     | sudo tee /etc/apt/sources.list.d/lre-epita.list \
  && sudo apt update \
  && sudo apt install -y spot libspot-dev python3-spot
```

## VITAMIN

Only two features requires it, and each raises a `VitaminUnavailable` naming the
install command:

| | Needs VITAMIN |
| --- | --- |
| `atl_model_check`, `natatl_synthesize`, `vitamin_synthesiser(...)` | yes |
| `check`, `synthesize`, `monitor --synthesize`, `repair --objective` | yes |
| everything else, including export and `enforces` | no |

Three things to know when using synthesis:

* **The objective is not the goal.** VITAMIN's parsers accept only one temporal
  operator under the coalition modality (ATL and not ATL*), so `G(p ∨ (q ∧ X p))` cannot be
  synthesised for. Pass the strongest ATL-expressible objective to
  `--objective` and keep the full LTL goal for `--goal`.
<!-- * **Only natural memoryless strategies come back.** VITAMIN has no notion of
  `k`-bounded or recall strategies; those can be monitored and repaired, but not
  synthesised. -->
* **Results vary across processes.** Candidates are enumerated over unordered
  sets, so hash randomisation can return a different winning witness each run.
  Every witness is winning; pin `PYTHONHASHSEED` or save the strategy with
  `strategy_to_dict` if you need a fixed one.

`natatl_synthesize` defaults to `rename_idle=True` and `verify=True`, which work
around a quirk in VITAMIN's NatATL that would otherwise reject winning
strategies. Leave them on. Details in
[`vitamin-idle-semantics/`](vitamin-idle-semantics/README.md).

Export (`to_vitamin_text`, `write_vitamin_model`) refuses names containing
whitespace, `,` or `|`, propositions that are not VITAMIN identifiers, and an
action named `*`.

## Limits

* `Σ = 2^Ap` is enumerated explicitly, so cost grows exponentially in `|Ap|`.
* The `k`-bounded index is a direct-address table; above 2²² entries it falls
  back to a dict, reported by `.dense`.
* A Boolean gate is a binary tree, so a conjunction of more than roughly 800
  terms is deeper than the interpreter's stack. Such gates work — evaluation
  hands the subtree to an explicit stack — but that path is several times
  slower, so a very wide gate costs more per state than its size suggests.
* `⊤ˢ_𝒢` is not defined for recall strategies.
* `enforces` handles memoryless strategies only.

## Tests

```bash
python -m pytest tests -q
```

310 tests, about a minute. 287 need no optional dependency; the rest skip when
VITAMIN or Spot is absent.

[`scaling/`](scaling/README.md) measures the implementation against the
complexity claims it is built from: 21 sweeps over time and space,
construction and runtime, each varying one parameter and fitting the exponent.

[`paper-figures/`](paper-figures/README.md) is for reproducing the figures in the paper.
