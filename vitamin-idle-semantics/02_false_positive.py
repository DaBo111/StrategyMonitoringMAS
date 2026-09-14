"""Taking IDLE away makes the prune keep too little, and CTL accepts vacuously.

Two separate causes, both ending in an emptied row:

  * pruning.py:71-75 prunes states no gate covers with the literal action "I",
    i.e. to IDLE only -- with no IDLE token that row empties;
  * matrix_utils.py compares the prescribed action against the *exported*
    token, so a witness that prescribes idle stops matching once idle is
    renamed, and its row empties too even though the gate covers it.

An emptied row is a dead end, and a universally quantified CTL formula holds
there vacuously.
"""

from models import pruned_edges, rule, two_labellings_one_agent

from strategy_monitor.strategies import NaturalMemorylessStrategy
from strategy_monitor.verify import enforces
from strategy_monitor.vitamin import atl_model_check, natatl_synthesize

rule("Cause 1: a state no gate covers")
model = two_labellings_one_agent(with_idle=True)
print("  s0|=p,q needs x    s1|=p needs y    s2|=nothing is the sink")
print("  candidate (q, x): gate q fires at s0 only, so s1 is UNCOVERED")
print("  ATL <a>G p:", atl_model_check(model, ["a"], "G p")["satisfied"])
print()
for rename in (False, True):
    edges, holds = pruned_edges(model, [[("q", "x")]], [1], rename_idle=rename)
    print("  rename_idle={0!s:<6} edges {1:<44} A G p: {2}".format(rename, str(edges), holds))
print()
print("  Renamed, s1 is a dead end: 'every successor satisfies p' is vacuously")
print("  true, and the check never sees what happens after s1.")
candidate = NaturalMemorylessStrategy.build(["a"], {"a": [("q", "x"), ("true", "idle")]})
print("  exact check:", enforces(model, candidate, "G p"))

rule("Cause 2: the witness prescribes the idle action")
running = __import__("models").running_example()
for pairs, label in ([("p", "in")], "never prescribes idle"), ([("p", "idle")], "prescribes idle"):
    edges, holds = pruned_edges(running, [pairs, pairs], [1, 2], rename_idle=True)
    print("  {0:<24} {1:>2} surviving cell(s)   A G p: {2}".format(label, len(edges), holds))
print()
print("  With the idle action renamed, the prescribed token no longer matches, so")
print("  even a covered state's row empties.  An empty model satisfies every")
print("  universally quantified formula -- VITAMIN's acceptance carries no information.")

rule("Why this is harmless in practice")
guarded = natatl_synthesize(model, ["a"], "G p", k=1)
unguarded = natatl_synthesize(model, ["a"], "G p", k=1, verify=False)
print("  verify=False -> satisfiable:", unguarded.satisfiable, " (VITAMIN is fooled)")
print("  verify=True  -> satisfiable:", guarded.satisfiable, " verified:", guarded.verified)
print("  note:", guarded.note[:150])
print()
print("  Both causes involve a candidate that is not a TOTAL strategy, and")
print("  Section 5.3 defines a strategy as a function.  Rejecting them is correct.")
