"""Shared fixtures: the two worked examples."""

import os
import sys

import pytest

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
if ROOT not in sys.path:
    sys.path.insert(0, ROOT)

EXAMPLES = os.path.join(ROOT, "examples")

from strategy_monitor.cgs import CGS  # noqa: E402
from strategy_monitor.strategies import (  # noqa: E402
    KBoundedStrategy,
    NaturalMemorylessStrategy,
)


@pytest.fixture(scope="session")
def running_example():
    """``G_E``, the running example."""
    return CGS.from_json(os.path.join(EXAMPLES, "running_example.json"))


@pytest.fixture(scope="session")
def revised_example():
    """The revised structure."""
    return CGS.from_json(os.path.join(EXAMPLES, "revised_example.json"))


@pytest.fixture
def example_memoryless_strategy():
    """The 1-bounded strategy of the k-bounded example."""
    return KBoundedStrategy.memoryless(
        ["a", "b"],
        {
            "s0": {"a": "in", "b": "in"},
            "s1": {"a": "out", "b": "out"},
            "s2": {"a": "out", "b": "out"},
            "s3": {"a": "out", "b": "out"},
        },
    )


@pytest.fixture
def example_natural_strategy():
    """``gamma^Natr`` of the natural memoryless example."""
    return NaturalMemorylessStrategy.build(
        ["a", "b"],
        {
            "a": [("p", "in"), ("q", "out"), ("true", "idle")],
            "b": [("p", "in"), ("q", "out"), ("true", "idle")],
        },
    )


@pytest.fixture
def adherence_strategy():
    """``Gamma_{a}`` of the strategy-adherence example."""
    return KBoundedStrategy.memoryless(
        ["a"], {"s0": {"a": "in"}, "s1": {"a": "out"}, "s2": {"a": "out"}, "s3": {"a": "in"}}
    )


def vitamin_available():
    try:
        import model_checker  # noqa: F401
    except Exception:
        return False
    return True


requires_vitamin = pytest.mark.skipif(
    not vitamin_available(), reason="VITAMIN (vitamin-model-checker) is not installed"
)
