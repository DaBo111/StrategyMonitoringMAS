"""VITAMIN rejects a strategy that wins: the prune keeps too much.

    matrix_utils.py:66   allowed_tokens = {CANONICAL_IDLE_TOKEN, required_token}

Whatever the gate prescribes, IDLE stays available, so the pruned model keeps
paths in which a coalition agent ignores its own strategy and idles.
"""

from models import pruned_edges, rule, running_example

from strategy_monitor.strategies import NaturalMemorylessStrategy
from strategy_monitor.verify import enforces
from strategy_monitor.vitamin import atl_model_check, natatl_synthesize

model = running_example()

rule("The paper's running example, coalition {a, b}, objective G p")
print("  s0 --(*,*,in)--> s0      s0 --(in,in,out)...--> s1")
print("  s0 --(idle,*,*)--> s2    and s2 is the only !p state")
print()
print("  ATL   <a,b>G p :", atl_model_check(model, ["a", "b"], "G p")["satisfied"])
winner = NaturalMemorylessStrategy.build(
    ["a", "b"], {"a": [("true", "in")], "b": [("true", "in")]}
)
print("  a winning strategy, checked exactly:")
print("   ", enforces(model, winner, "G p"))

rule("What VITAMIN's prune does to the candidate 'play in where p holds'")
edges, holds = pruned_edges(model, [[("p", "in")], [("p", "in")]], [1, 2], rename_idle=False)
print("  surviving edges:", edges)
print("  CTL A G p      :", holds, "-> candidate rejected")
print()
print("  s0->s2 survives only because idling was kept; the strategy never idles.")
print("  IDLE is re-added regardless of the gate, so NO natural strategy can")
print("  remove that edge.  The enumeration is fine; the acceptance test is not.")

rule("Consequence")
native = natatl_synthesize(model, ["a", "b"], "G p", k=2, rename_idle=False)
print("  natatl_synthesize(rename_idle=False) -> satisfiable:", native.satisfiable)
print("  cross-check, atl_realisable          :", native.atl_realisable)
print()
print("  What VITAMIN decides is:")
print("     exists gamma such that FORALL paths where the coalition plays gamma OR IDLES, phi")
print("  which is strictly stronger than <A>phi.  Sound, but incomplete.")
