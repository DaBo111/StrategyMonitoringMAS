"""Optional Spot backend for the LTL-to-Buchi step.

`Spot <https://spot.lre.epita.fr/>`_ is a C++ omega-automata library with
Python bindings.  It is not on PyPI and has no Windows build, so it cannot be a
dependency of this package; where it *is* available two things make it worth
using:

* its translation produces far smaller automata than the textbook GPVW tableau
  in :mod:`strategy_monitor.ltl`, and automaton size drives the cost of every
  construction downstream, and
* it is an independent implementation, so the two can be cross-checked --
  ``tests/test_spot_backend.py`` does exactly that.

Only the LTL-to-Buchi step is delegated.  Everything after it -- the prefix
NFA, the determinised monitor tables, the products with the CGS -- keeps
running on this package's own automata, because the monitors of Sections 5 and
6 consume letters from ``2^Ap`` one at a time.

The conversion is where the two models meet.  Spot labels an edge with a BDD
over atomic propositions; we expand each edge into one transition per letter of
our alphabet satisfying that BDD.  So we keep Spot's win on state count and
give back its win on alphabet compactness -- an unavoidable trade, since a
monitor has to be indexed by concrete letters.
"""

from __future__ import annotations

import os
from typing import Dict, FrozenSet, List, Optional, Sequence, Set, Tuple

from .automata import Buchi, Letter, State
from .ltl import (
    Atom,
    Conj,
    Disj,
    Eventually,
    FalseF,
    Globally,
    Neg,
    NegAtom,
    Next,
    Release,
    TrueF,
    Until,
    formula_of,
)

ENV_VAR = "STRATEGY_MONITOR_LTL_BACKEND"
LTL_BACKENDS = ("gpvw", "spot", "auto")
DEFAULT_BACKEND = "gpvw"

INSTALL_HINT = (
    "Spot is not on PyPI and has no Windows build, so on Windows it needs WSL."
    " Neither 'pip install spot' nor a plain 'apt install spot' will find it:"
    " use 'conda install conda-forge::spot' (linux-64 or macOS-arm64), or add"
    " the LRE apt repository first -- see the README section 'Installing Spot'."
    " The default 'gpvw' backend needs nothing."
)


class SpotUnavailable(RuntimeError):
    """Spot was asked for by name but could not be imported."""


# -- availability --------------------------------------------------------


def _import_spot():
    """Import Spot and BuDDy, or raise :class:`SpotUnavailable`.

    BuDDy ships with Spot and carries the BDD operations; edge conditions are
    BDDs, so both are needed.
    """
    try:
        import buddy
        import spot
    except ImportError as exc:
        raise SpotUnavailable("Spot is not importable ({0}). {1}".format(exc, INSTALL_HINT))
    return spot, buddy


def spot_available() -> bool:
    """Whether the Spot backend can run in this interpreter."""
    try:
        _import_spot()
    except SpotUnavailable:
        return False
    return True


def spot_version() -> Optional[str]:
    """Spot's version string, or ``None`` when it is not installed."""
    try:
        spot, _buddy = _import_spot()
    except SpotUnavailable:
        return None
    return str(spot.version())


def resolve_ltl_backend(backend: Optional[str] = None) -> str:
    """Pick a backend from an argument, then the environment, then the default.

    ``auto`` takes Spot when it imports and falls back quietly.  ``spot`` raises
    when it does not, so a run that asks for Spot by name can never silently get
    something else -- which matters when the point of the run is to compare the
    two.
    """
    name = (backend or os.environ.get(ENV_VAR) or DEFAULT_BACKEND).strip().lower()
    if name not in LTL_BACKENDS:
        raise ValueError(
            "unknown LTL backend {0!r}; expected one of {1}".format(
                name, ", ".join(LTL_BACKENDS)
            )
        )
    if name == "auto":
        return "spot" if spot_available() else "gpvw"
    if name == "spot":
        _import_spot()  # raise here, with the installation hint attached
    return name


# -- our syntax -> Spot's ------------------------------------------------


def _quote_ap(name: str) -> str:
    """Spot's double-quoted atomic proposition.

    Always quoting sidesteps the names Spot reads as operators: an atom called
    ``U`` or ``X`` is legal in a CGS but would otherwise reparse as a temporal
    operator.
    """
    backslash = chr(92)
    escaped = name.replace(backslash, backslash * 2).replace(chr(34), backslash + chr(34))
    return chr(34) + escaped + chr(34)


def to_spot_syntax(formula) -> str:
    """Render an LTL formula in Spot's concrete syntax."""
    return _render(formula_of(formula))


def _render(node) -> str:
    if isinstance(node, TrueF):
        return "1"
    if isinstance(node, FalseF):
        return "0"
    if isinstance(node, Atom):
        return _quote_ap(node.name)
    if isinstance(node, NegAtom):
        return "!" + _quote_ap(node.name)
    if isinstance(node, Neg):
        return "!(" + _render(node.operand) + ")"
    if isinstance(node, Next):
        return "X(" + _render(node.operand) + ")"
    if isinstance(node, Eventually):
        return "F(" + _render(node.operand) + ")"
    if isinstance(node, Globally):
        return "G(" + _render(node.operand) + ")"
    for kind, operator in ((Conj, "&"), (Disj, "|"), (Until, "U"), (Release, "R")):
        if isinstance(node, kind):
            return "(" + _render(node.left) + " " + operator + " " + _render(node.right) + ")"
    raise TypeError("cannot render {0!r} in Spot syntax".format(node))


# -- Spot's automaton -> ours --------------------------------------------


def _ap_name(proposition) -> str:
    """The bare name of a Spot atomic proposition."""
    getter = getattr(proposition, "ap_name", None)
    return getter() if getter is not None else str(proposition)


def spot_ltl_to_buchi(formula, alphabet: Sequence[Letter]) -> Buchi:
    """Translate with Spot and convert to this package's :class:`Buchi`.

    The result is interchangeable with :func:`strategy_monitor.ltl.ltl_to_buchi`
    -- same alphabet, same state-based acceptance, generally far fewer states.
    """
    spot, buddy = _import_spot()
    letters: Tuple[Letter, ...] = tuple(alphabet)

    automaton = spot.translate(to_spot_syntax(formula), "BA", "complete")
    if automaton.prop_state_acc() is not True:
        # 'BA' should already be state-based; convert rather than misread the
        # acceptance if some future Spot returns otherwise.
        automaton = spot.sbacc(automaton)

    ours: List[str] = sorted(set().union(*letters)) if letters else []
    theirs = [_ap_name(proposition) for proposition in automaton.ap()]
    # An atom the alphabet does not mention is pinned false below, which is what
    # the GPVW backend does with it: no letter of 2^Ap contains it.
    names = list(dict.fromkeys(ours + [name for name in theirs if name not in ours]))
    variables = {name: automaton.register_ap(name) for name in names}

    def minterm(letter: Letter):
        assignment = buddy.bddtrue
        for name in names:
            index = variables[name]
            literal = buddy.bdd_ithvar(index) if name in letter else buddy.bdd_nithvar(index)
            assignment = assignment & literal
        return assignment

    minterms = [(letter, minterm(letter)) for letter in letters]

    states: List[State] = list(range(automaton.num_states()))
    collected: Dict[Tuple[State, Letter], Set[State]] = {}
    for source in states:
        for edge in automaton.out(source):
            for letter, assignment in minterms:
                if (assignment & edge.cond) != buddy.bddfalse:
                    collected.setdefault((source, letter), set()).add(edge.dst)

    transitions: Dict[Tuple[State, Letter], FrozenSet[State]] = {
        key: frozenset(targets) for key, targets in collected.items()
    }
    accepting = frozenset(state for state in states if automaton.state_is_accepting(state))
    return Buchi(
        states=states,
        alphabet=letters,
        transitions=transitions,
        initial=frozenset({automaton.get_init_state_number()}),
        accepting=accepting,
    )


# -- what to tell the user -----------------------------------------------


def diagnose() -> str:
    """A human-readable report of what is installed and what will be used."""
    configured = os.environ.get(ENV_VAR)
    version = spot_version()
    lines = ["LTL backend"]
    if version is None:
        lines.append("  spot            not importable")
    else:
        lines.append("  spot            {0}".format(version))
    lines.append("  {0}  {1}".format(ENV_VAR, configured if configured else "(unset)"))
    lines.append("  resolves to     {0}".format(resolve_ltl_backend()))
    lines.append(
        "  with 'auto'     {0}".format(resolve_ltl_backend("auto"))
    )
    lines.append(
        "  default         {0} (set {1}=auto to prefer Spot whenever present)".format(
            DEFAULT_BACKEND, ENV_VAR
        )
    )
    if version is None:
        lines.append("  " + INSTALL_HINT)
    return chr(10).join(lines)
