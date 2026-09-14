"""Models and helpers shared by the demonstration scripts.

Run any script from this directory; they add the package root to ``sys.path``
themselves.
"""

import copy
import itertools
import os
import sys
import tempfile

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
if ROOT not in sys.path:
    sys.path.insert(0, ROOT)

from strategy_monitor import CGS  # noqa: E402
from strategy_monitor.vitamin import write_vitamin_model  # noqa: E402

EXAMPLES = os.path.join(ROOT, "examples")


def running_example():
    """The paper's running example G_E (Section 5.1, Figure 1).

    Agents a and b own an idle action; idling from s0 reaches s2, the only
    state where p fails.  That is what makes it a natural witness for the
    problem.
    """
    return CGS.from_json(os.path.join(EXAMPLES, "running_example.json"))


def running_example_without_idle():
    """The same structure with 'idle' removed from every agent."""
    base = running_example()
    return CGS.from_dict(
        {
            "ap": list(base.ap),
            "agents": list(base.agents),
            "actions": {agent: ["in", "out"] for agent in base.agents},
            "initial_state": base.initial_state,
            "states": [
                {
                    "id": state,
                    "labels": sorted(base.label(state)),
                    "transitions": [
                        {"to": base.step(state, profile), "profiles": [list(profile)]}
                        for profile in itertools.product(["in", "out"], repeat=3)
                    ],
                }
                for state in base.states
            ],
        }
    )


def two_labellings_one_agent(with_idle=True):
    """A model where only a *partial* gate list survives at complexity 1.

        s0 |= p,q   needs x      s1 |= p   needs y      s2 |= nothing  is the sink

    At k = 1 the gates are single atoms.  ``p`` holds in both s0 and s1, which
    need different actions, so no *total* natural strategy of that complexity
    wins.  ``q`` holds only in s0, so the one remaining candidate is silent
    about s1 -- which is precisely the state VITAMIN's prune turns into a dead
    end.  ATL says the objective G p *is* enforceable (play x, then y forever).
    """
    actions = ["x", "y"] + (["idle"] if with_idle else [])
    return CGS.from_dict(
        {
            "ap": ["p", "q"],
            "agents": ["a"],
            "actions": {"a": actions},
            "initial_state": "s0",
            "states": [
                {
                    "id": "s0",
                    "labels": ["p", "q"],
                    "transitions": [
                        {"to": "s1", "profiles": [["x"]]},
                        {"to": "s2", "profiles": [["*"]]},
                    ],
                },
                {
                    "id": "s1",
                    "labels": ["p"],
                    "transitions": [
                        {"to": "s1", "profiles": [["y"]]},
                        {"to": "s2", "profiles": [["*"]]},
                    ],
                },
                {"id": "s2", "labels": [], "transitions": [{"to": "s2", "profiles": [["*"]]}]},
            ],
        }
    )


def pruned_edges(model, pairs_per_agent, agents, rename_idle, formula="A G p"):
    """Run VITAMIN's own prune and CTL check; report the surviving edges.

    This calls the library functions directly rather than the whole NatATL
    entry point, so that the intermediate matrix can be inspected.
    """
    from model_checker.algorithms.explicit.CTL.CTL import model_checking as ctl
    from model_checker.algorithms.explicit.NatATL.Memoryless.pruning import (
        process_transition_matrix_data_fixed,
    )
    from model_checker.parsers.game_structures.cgs.cgs import CGS as VitaminCGS

    handle, path = tempfile.mkstemp(suffix=".txt")
    os.close(handle)
    try:
        write_vitamin_model(model, path, rename_idle=rename_idle)
        parsed = VitaminCGS()
        parsed.read_file(path)
        pruned = process_transition_matrix_data_fixed(
            parsed, path, agents, *[{"condition_action_pairs": p} for p in pairs_per_agent]
        )
        edges = [
            "{0}->{1}".format(source, target)
            for row, source in enumerate(model.states)
            for column, target in enumerate(model.states)
            if pruned[row][column] not in (0, "0")
        ]
        checked = copy.deepcopy(parsed)
        checked.graph = pruned
        holds = "True" in ctl(formula, path, preloaded_model=checked).get("initial_state", "")
        return edges, holds
    finally:
        if os.path.exists(path):
            os.unlink(path)


def rule(title):
    print()
    print("=" * 76)
    print(title)
    print("=" * 76)
