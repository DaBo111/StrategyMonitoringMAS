"""Measure both settings against an exhaustive ground truth.

    python 03_ground_truth.py [k]        # complexity bound, default 2

k = 3 explores many more candidates and takes a few minutes.

A memoryless natural strategy is a gate list over ``Ap``, so it induces a map
from each labelling the model exhibits to an action -- and conversely any such
map is a natural strategy (one gate per labelling).  So

    "some TOTAL natural memoryless strategy enforces phi"

can be decided by enumerating every such map and checking it exactly with
``strategy_monitor.verify.enforces``.  That is the ground truth below.
"""

import itertools
import os
import sys

from models import (
    ROOT,
    rule,
    running_example,
    running_example_without_idle,
    two_labellings_one_agent,
)

from strategy_monitor import CGS
from strategy_monitor.automata import buchi_lasso, buchi_product
from strategy_monitor.boolean import Gate
from strategy_monitor.goal import cgs_to_buchi
from strategy_monitor.ltl import Neg, formula_of, ltl_to_buchi
from strategy_monitor.strategies import NaturalMemorylessStrategy
from strategy_monitor.verify import restrict
from strategy_monitor.vitamin import natatl_synthesize


class Exactly(Gate):
    """True of exactly one labelling, so any total map can be named."""

    def __init__(self, labelling, ap):
        self.labelling = frozenset(labelling)
        self.ap = tuple(ap)

    def evaluate(self, valuation):
        return frozenset(valuation) == self.labelling

    def variables(self):
        return list(self.ap)

    def __str__(self):
        return "={" + ",".join(sorted(self.labelling)) + "}"


def some_total_strategy_wins(cgs, coalition, goal):
    """Ground truth, by exhaustive enumeration; the goal automaton is reused."""
    labellings = sorted({cgs.label(s) for s in cgs.states}, key=lambda x: sorted(x))
    negated = ltl_to_buchi(Neg(formula_of(goal)), cgs.alphabet())
    per_agent = [
        [
            dict(zip(labellings, combination))
            for combination in itertools.product(
                *[sorted(cgs.actions[agent])] * len(labellings)
            )
        ]
        for agent in coalition
    ]
    for profile in itertools.product(*per_agent):
        rules = {
            agent: [(Exactly(labelling, cgs.ap), action) for labelling, action in mapping.items()]
            for agent, mapping in zip(coalition, profile)
        }
        strategy = NaturalMemorylessStrategy(coalition=tuple(coalition), rules=rules)
        product = buchi_product(
            negated, cgs_to_buchi(restrict(cgs, strategy)), right_all_accepting=True
        )
        if buchi_lasso(product) is None:
            return True, strategy
    return False, None


revised = CGS.from_json(os.path.join(ROOT, "examples", "revised_example.json"))
running = running_example()

CASES = [
    ("running", running, ["a"], "G p"),
    ("running", running, ["a"], "G(p || q)"),
    ("running", running, ["c"], "G p"),
    ("running", running, ["a"], "F q"),
    ("revised", revised, ["a"], "G p"),
    ("revised", revised, ["a"], "G(p || q)"),
    ("running", running, ["a", "b"], "G p"),
]

BOUND = int(sys.argv[1]) if len(sys.argv) > 1 else 2

rule("Ground truth vs. VITAMIN at k = {0}, over TOTAL natural memoryless strategies".format(BOUND))
print(
    "  {0:<9} {1:<10} {2:<12} {3:<7} {4:<8} {5:<8} {6}".format(
        "model", "coalition", "objective", "truth", "native", "renamed", "verdict"
    )
)
print("  " + "-" * 70)
wrong_native = wrong_renamed = 0
for name, model, coalition, goal in CASES:
    truth, _ = some_total_strategy_wins(model, coalition, goal)
    native = natatl_synthesize(model, coalition, goal, k=BOUND, rename_idle=False).satisfiable
    renamed = natatl_synthesize(model, coalition, goal, k=BOUND, rename_idle=True).satisfiable
    wrong_native += native != truth
    wrong_renamed += renamed != truth
    print(
        "  {0:<9} {1:<10} {2:<12} {3:<7} {4:<8} {5:<8} {6}".format(
            name,
            ",".join(coalition),
            goal,
            str(truth),
            str(native),
            str(renamed),
            "ok" if renamed == truth else "RENAMED WRONG",
        )
    )
print()
print("  native  (rename_idle=False) disagreed with ground truth: {0}/{1}".format(
    wrong_native, len(CASES)))
print("  renamed (rename_idle=True)  disagreed with ground truth: {0}/{1}".format(
    wrong_renamed, len(CASES)))

rule("Removing the idle action instead")
without = running_example_without_idle()
print("  running example, coalition {a,b}, objective G p")
print("    with idle, native  :", natatl_synthesize(
    running, ["a", "b"], "G p", k=2, rename_idle=False).satisfiable)
print("    idle removed       :", natatl_synthesize(
    without, ["a", "b"], "G p", k=2, rename_idle=False).satisfiable)
print()
print("  Removing idle also fixes the false negatives, and it removes one of the")
print("  two emptying causes -- no witness can prescribe an action that is gone.")
print("  But uncovered states are still pruned with the literal action 'I':")
partial = two_labellings_one_agent(with_idle=False)
result = natatl_synthesize(partial, ["a"], "G p", k=1, verify=False, rename_idle=False)
print("    partial witness still accepted (verify=False):", result.satisfiable)
print("  ... and it changes the model being verified, which renaming does not.")
