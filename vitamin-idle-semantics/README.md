# VITAMIN's NatATL idle semantics

A finding about [VITAMIN](https://github.com/VITAMIN-organisation/vitamin-model-checker)
1.6.3, uncovered while wiring its NatATL synthesis into this project's strategy
repair. It made repair stop for the wrong reason on this package's own running
example.

**Summary.** VITAMIN's NatATL prunes each coalition agent's moves to *the
prescribed action **or** idling*. An agent that owns an idle action is therefore
never held to its strategy, and where idling is unsafe NatATL reports
unsatisfiable although the coalition can enforce the objective. Because an
action's name is arbitrary, exporting the idle action under a different name
removes it from that allowance and the prune becomes exact — this is what
`strategy_monitor` does by default.

Everything below is reproducible with the scripts in this folder.

```bash
python 01_false_negative.py     # the winner VITAMIN rejects
python 02_false_positive.py     # what taking IDLE away costs
python 03_ground_truth.py       # both settings against exhaustive ground truth
```

They need VITAMIN installed and add the package root to `sys.path` themselves.

---

## 1. What the algorithm does

`solve_natatl_memoryless` enumerates candidate natural strategies of complexity
≤ k; for each it **prunes** the transition matrix to the moves the strategy
allows, then model-checks the objective on the pruned model with a universal
path quantifier (`<{A},k>G p` becomes `A G p`). Everything turns on the prune.

```python
# model_checker/algorithms/explicit/NatATL/Memoryless/matrix_utils.py:65-66
required_token = normalize_action_token(action)
allowed_tokens = {CANONICAL_IDLE_TOKEN, required_token}
```

`CANONICAL_IDLE_TOKEN` is `"IDLE"`, and `normalize_action_token` maps both `"I"`
and `"IDLE"` to it. So for every state the gate covers, idling survives the
prune alongside the prescribed action.

States no gate covers are handled by a *separate* branch:

```python
# .../Memoryless/pruning.py:71-75
remaining = all_states - covered_states
if remaining:
    graph = modify_matrix(graph, remaining, "I", ...)   # -> allowed_tokens = {"IDLE"}
```

Since that branch already implements "the strategy is silent here, so idle", the
`IDLE` on line 66 is not needed for it. That is what makes it look like an
oversight rather than a design decision — though intent cannot be read off the
code.

## 2. It rejects strategies that win

On the bundled running example (`examples/running_example.json`), agents `a`
and `b` own `idle`, and
`δ(s0, (idle,*,*)) = s2`, the only state where `p` fails.

Candidate "play `in` wherever `p` holds", which genuinely enforces `G p`:

```
surviving edges: ['s0->s0', 's0->s1', 's0->s2', 's1->s1', 's2->s2', 's3->s3']
CTL A G p      : False   -> rejected
```

`s0->s2` survives *only* because idling was kept; the strategy never idles. And
this is not about that candidate: `IDLE` is re-added regardless of the gate, so
**no** natural strategy can remove that edge. The enumeration is correct; the
acceptance test is not.

What VITAMIN decides is

> ∃γ such that ∀ paths where the coalition plays γ **or idles**, φ

which is strictly stronger than `⟨A⟩φ` — a robustness property, "γ wins even if
its own members idle at will". A stronger requirement can only reject more, so
the native setting is **sound but incomplete**.

## 3. Taking `IDLE` away costs something

The obvious repair — rename the idle action, or drop it from the model — makes
covered states exact. But the prune then keeps *too little*, in two ways, and
both end in an emptied row:

| Cause | Why the row empties |
| --- | --- |
| a state no gate covers | pruned with the literal action `"I"` → `allowed = {IDLE}`, and no cell carries `IDLE` any more |
| the witness prescribes idle | the prescribed action is matched against the **exported** token, which is no longer `IDLE` |

An emptied row is a dead end, and a universally quantified CTL formula holds
there vacuously:

```
candidate (q, x), which is silent about s1
  rename_idle=False  edges ['s0->s1','s0->s2','s1->s2','s2->s2']   A G p: False
  rename_idle=True   edges ['s0->s1']                              A G p: True

candidate (p, idle) on the running example
  rename_idle=True   0 surviving cells                             A G p: True
```

In the second case the pruned model is **empty**, and VITAMIN validates the
objective against nothing at all.

Both cases involve a candidate that is **not a total strategy**: a strategy is
a function, so it must prescribe an action wherever it can be asked for one.
Rejecting them is correct, and the package does so by verifying every returned
strategy exactly.

## 4. Measured against ground truth

A memoryless natural strategy is a gate list over `Ap`, so it induces a map from
each labelling the model exhibits to an action; conversely any such map is a
natural strategy. So "some **total** natural memoryless strategy enforces φ" can
be decided by enumerating every such map and checking it exactly. That is the
ground truth in `03_ground_truth.py`:

```
model     coalition  objective    truth   native   renamed  verdict
running   a          G p          False   False    False    ok
running   a          G(p || q)    True    True     True     ok
running   c          G p          True    True     True     ok
running   a          F q          True    True     True     ok
revised   a          G p          False   False    False    ok
revised   a          G(p || q)    True    True     True     ok
running   a,b        G p          True    False    True     <- native is wrong

native  (rename_idle=False) disagreed with ground truth: 1/7
renamed (rename_idle=True)  disagreed with ground truth: 0/7
```

At `k = 3`, over a wider set including two-agent coalitions on both models
(`python 03_ground_truth.py 3`, a few minutes):

```
native  disagreed with the truth in 2 of 9 cases
renamed disagreed with the truth in 0 of 9 cases
```

Both failures are two-agent coalitions enforcing `G p`, where idling is unsafe.
Sixteen case-checks across two models and two complexity bounds — measured, not
proved.

## 5. What the package does

`natatl_synthesize` composes two things, and they are complementary:

1. **`rename_idle=True` (default)** exports the idle action as `NOOP`, so the
   prune is exact for covered states and no *total* winning candidate is
   missed. All four aliases get the same treatment —
   `IDLE_ALIASES = ("idle", "Idle", "IDLE", "I")` — so an action literally named
   `I` is renamed too. On a model with no idle action the export is
   byte-identical either way, so the setting can never hurt.
2. **`verify=True` (default)** checks whatever comes back with
   `strategy_monitor.verify.enforces`, which restricts `d(s,i)` to exactly the
   prescribed action and model-checks the goal. It is exact, needs no VITAMIN,
   and takes the full LTL grammar. A strategy that fails is not returned.

Together: **sound, and complete over the total natural memoryless strategies** —
the only ones the definition admits.

```python
result = natatl_synthesize(cgs, ["a", "b"], "G p", k=2)
result.satisfiable    # True
result.verified       # True  -- confirmed under exact semantics

result = natatl_synthesize(cgs, ["a"], "G p", k=1)   # only a partial witness exists
result.satisfiable    # False -- VITAMIN accepted it, the exact check did not
result.note           # "not a total strategy: prescribes nothing in 's1',
                      #  which it can reach"
```

A gate list silent only about states the strategy *cannot reach* is fine and is
accepted: `enforces` walks from `s_I` through the prescribed actions and objects
only if it lands somewhere unprescribed.

When NatATL still finds nothing, `cross_check=True` runs plain ATL and records
`atl_realisable` plus a note, so a negative result can be told apart from
genuine unrealisability.

### Escape hatches

| | Effect |
| --- | --- |
| `rename_idle=False` (`--native-idle`) | VITAMIN's native semantics: sound, incomplete |
| `verify=False` | skips the exact check; warns when combined with renaming, because positive results then mean nothing |
| no idle action in the model | fixes the false negatives and removes one emptying cause, but uncovered states still empty — and it changes the model being verified, which renaming does not |

### What is still not fixed

Nothing here can recover a strategy VITAMIN never offers. Verification rejects
bad candidates; it cannot invent missing ones. Closing that would mean doing the
enumeration ourselves and checking each candidate with `enforces` —
`Synthesiser` is just `(model, coalition, q_curr) -> strategy or None`, so it is
a drop-in. On the cases measured above, renaming already agrees with ground
truth, so this has not been needed.

## 6. Files

| | |
| --- | --- |
| `models.py` | the models and the prune/CTL helper the scripts share |
| `01_false_negative.py` | the winning strategy VITAMIN rejects, with the surviving edges |
| `02_false_positive.py` | both emptying causes, and why verification makes them harmless |
| `03_ground_truth.py` | exhaustive comparison, plus the "remove idle instead" variant |

The behaviour is pinned by regression tests in
[`../tests/test_verify.py`](../tests/test_verify.py) (`TestRenameIdle`,
`TestNoIdleAction`, `TestPartialStrategies`) and
[`../tests/test_repair.py`](../tests/test_repair.py)
(`TestNatATLIdleSemantics`), so a change in VITAMIN's behaviour will show up as
a test failure rather than silently.
