"""Bridge to the VITAMIN model checker.

VITAMIN (``pip install vitamin-model-checker``) speaks the same concurrent game
structures this package monitors, and brings the two things the monitoring
framework itself does not provide:

* **ATL model checking**, used to ask whether a coalition can still enforce the
  goal from the current state -- the realisability question both branches of the
  repair procedure of Section 7 have to answer;
* **NatATL strategy synthesis**, which returns an actual winning *natural
  memoryless* strategy as a list of guarded actions -- exactly the
  ``((gate_i, act_i))`` shape of Section 5.3, so its output can be handed
  straight to :class:`~strategy_monitor.monitors.NaturalMemorylessMonitor`.

Two representation details have to be bridged:

* VITAMIN writes a transition matrix whose cells enumerate joint action
  profiles, so wildcards are expanded on export;
* VITAMIN normalises the tokens ``I`` and ``IDLE`` to a canonical idle action,
  which its NatATL checker requires each agent to have.  Action names are
  therefore mapped on the way out and back on the way in.
"""

from __future__ import annotations

import logging
import os
import tempfile
from dataclasses import dataclass
from typing import Dict, List, Mapping, Optional, Sequence, Tuple

import re

from .boolean import parse_gate
from .cgs import CGS
from .strategies import NaturalMemorylessStrategy

VITAMIN_IDLE = "IDLE"
IDLE_ALIASES = ("idle", "Idle", "IDLE", "I")

JOINT_SEPARATOR = ","
"""Separates joint action profiles inside one transition-matrix cell."""

AGENT_SEPARATOR = "|"
"""Separates the per-agent actions inside one profile."""

_PROPOSITION_RE = re.compile(r"^[A-Za-z][A-Za-z0-9_]*$")
_AGENT_LABEL_RE = re.compile(r"^[A-Za-z0-9_-]+$")


logger = logging.getLogger(__name__)


class VitaminExportError(ValueError):
    """Raised when a model cannot be written in VITAMIN's syntax without loss."""


class VitaminUnavailable(RuntimeError):
    """Raised when VITAMIN is not importable."""


def require_vitamin():
    """Import VITAMIN, with an actionable message when it is missing."""
    try:
        import model_checker  # noqa: F401
    except ImportError as error:  # pragma: no cover - environment dependent
        raise VitaminUnavailable(
            "VITAMIN is not installed in this interpreter.\n"
            "  pip install vitamin-model-checker\n"
            "VITAMIN 1.6+ declares Python >= 3.11; on 3.10 install the wheel with\n"
            "  pip install --ignore-requires-python vitamin_model_checker-<v>-py3-none-any.whl"
        ) from error
    return model_checker


# ======================================================================
# export
# ======================================================================


DEFAULT_IDLE_ALIAS = "NOOP"
"""Token an idle action is renamed to when the caller asks to dodge the prune."""


def action_token(action: str, idle_as: str = VITAMIN_IDLE) -> str:
    """Map a model action name to the token VITAMIN expects.

    ``idle_as`` chooses what an idle action is called on the way out.  The
    default is VITAMIN's canonical ``IDLE``; passing anything else makes the
    NatATL prune exact -- see :func:`build_token_map`.
    """
    return idle_as if action in IDLE_ALIASES else action


def build_token_map(cgs: CGS, rename_idle=False) -> Tuple[Dict[str, str], Dict[str, str], str]:
    """Return ``(model -> token, token -> model, idle_as)`` for one export.

    VITAMIN's NatATL prunes each coalition agent's moves to *the prescribed
    action or the canonical idle token*, so an agent that owns an idle action is
    never actually held to its strategy (see :func:`natatl_synthesize`).
    Exporting the idle action under a different name removes it from that
    allowance, and the prune becomes exact.

    ``rename_idle`` may be ``False`` (keep ``IDLE``), ``True`` (use
    :data:`DEFAULT_IDLE_ALIAS`), or an explicit token.
    """
    if rename_idle is False or rename_idle is None:
        idle_as = VITAMIN_IDLE
    elif rename_idle is True:
        idle_as = DEFAULT_IDLE_ALIAS
    else:
        idle_as = str(rename_idle)
        if idle_as in IDLE_ALIASES:
            raise VitaminExportError(
                "renaming idle to {0!r} changes nothing: VITAMIN normalises {1} to "
                "{2!r} and treats it specially in the NatATL prune".format(
                    idle_as, list(IDLE_ALIASES), VITAMIN_IDLE
                )
            )

    if idle_as != VITAMIN_IDLE:
        clashes = sorted(
            {a for actions in cgs.actions.values() for a in actions if a == idle_as}
        )
        if clashes:
            raise VitaminExportError(
                "cannot rename idle to {0!r}: the model already has an action of that "
                "name".format(idle_as)
            )

    forward: Dict[str, str] = {}
    backward: Dict[str, str] = {}
    for actions in cgs.actions.values():
        for action in actions:
            token = action_token(action, idle_as)
            forward[action] = token
            backward[token] = action
    return forward, backward, idle_as


def encode_profile(profile, agent_count: int, tokens: Optional[Mapping[str, str]] = None) -> str:
    """Encode one joint action profile as a VITAMIN cell entry.

    VITAMIN reads a profile containing ``|`` as an explicit per-agent token
    list, and one without it as *one character per agent*.  For a coalition of
    two or more the separator is always present, but a single agent's profile
    would otherwise be split into characters -- ``move`` would be read as the
    action ``m``.  A trailing separator forces the explicit branch; VITAMIN
    keeps only the first ``agent_count`` tokens, so the empty tail is dropped.
    """
    lookup = tokens if tokens is not None else {}
    encoded = AGENT_SEPARATOR.join(lookup.get(a, action_token(a)) for a in profile)
    return encoded + AGENT_SEPARATOR if agent_count == 1 else encoded


def check_exportable(cgs: CGS) -> None:
    """Reject names VITAMIN's syntax cannot carry, before anything is written.

    The transition matrix is whitespace-separated into cells, cells are split on
    ``,`` and profiles on ``|``, so a name containing any of those would be
    silently torn apart rather than rejected.  Propositions additionally have to
    satisfy VITAMIN's identifier rule, since formulas must be able to name them.
    """
    problems: List[str] = []

    def check_delimiters(kind: str, name: str) -> None:
        text = str(name)
        if not text:
            problems.append("{0} name is empty".format(kind))
            return
        if any(character.isspace() for character in text):
            problems.append("{0} {1!r} contains whitespace".format(kind, name))
        for delimiter, role in ((AGENT_SEPARATOR, "per-agent"), (JOINT_SEPARATOR, "joint")):
            if delimiter in text:
                problems.append(
                    "{0} {1!r} contains {2!r}, which separates {3} actions".format(
                        kind, name, delimiter, role
                    )
                )

    for proposition in cgs.ap:
        check_delimiters("proposition", proposition)
        if not _PROPOSITION_RE.match(str(proposition)):
            problems.append(
                "proposition {0!r} is not a VITAMIN identifier "
                "(letter followed by letters, digits or underscores)".format(proposition)
            )
    for state in cgs.states:
        check_delimiters("state", state)
    for agent in cgs.agents:
        check_delimiters("agent", agent)
        if not _AGENT_LABEL_RE.match(str(agent)):
            problems.append(
                "agent label {0!r} must match [A-Za-z0-9_-]+".format(agent)
            )
    for agent, actions in cgs.actions.items():
        for action in actions:
            check_delimiters("action", action)
            if action_token(action) == "*":
                problems.append("action {0!r} clashes with the cell wildcard '*'".format(action))

    if problems:
        raise VitaminExportError(
            "this model cannot be written in VITAMIN's syntax:\n"
            + "\n".join("  - " + problem for problem in problems)
        )


def to_vitamin_text(cgs: CGS, rename_idle=False) -> str:
    """Render the CGS in VITAMIN's model-file syntax.

    Every joint action profile is written out explicitly: VITAMIN reads a cell
    as a list of concrete profiles, and a per-agent ``*`` inside a profile would
    be taken as an action literally named ``*``.  Names that the syntax cannot
    carry are rejected up front by :func:`check_exportable` rather than silently
    mangled.
    """
    check_exportable(cgs)
    tokens, _, _ = build_token_map(cgs, rename_idle)
    agent_count = len(cgs.agents)
    order = list(cgs.states)
    position = {state: i for i, state in enumerate(order)}
    rows: List[List[str]] = []
    for source in order:
        cells: List[List[str]] = [[] for _ in order]
        for profile in cgs.available_profiles(source):
            target = cgs.step(source, profile)
            cells[position[target]].append(encode_profile(profile, agent_count, tokens))
        rows.append([JOINT_SEPARATOR.join(cell) if cell else "0" for cell in cells])

    lines = ["Transition"]
    lines.extend(" ".join(row) for row in rows)
    lines.append("Unknown_Transition_by")
    lines.append("Name_State")
    lines.append(" ".join(order))
    lines.append("Initial_State")
    lines.append(cgs.initial_state)
    lines.append("Atomic_propositions")
    lines.append(" ".join(cgs.ap))
    lines.append("Labelling")
    for state in order:
        label = cgs.label(state)
        lines.append(" ".join("1" if prop in label else "0" for prop in cgs.ap))
    lines.append("Number_of_agents")
    lines.append(str(len(cgs.agents)))
    lines.append("Agent_labels")
    lines.append(" ".join(cgs.agents))
    return "\n".join(lines) + "\n"


def write_vitamin_model(cgs: CGS, path: str, rename_idle=False) -> str:
    with open(path, "w", encoding="utf-8") as handle:
        handle.write(to_vitamin_text(cgs, rename_idle))
    return path


class _TemporaryModel:
    """Write the CGS to a temp file for VITAMIN's file-based entry points."""

    def __init__(self, cgs: CGS, rename_idle=False) -> None:
        self.cgs = cgs
        self.rename_idle = rename_idle
        self.path: Optional[str] = None

    def __enter__(self) -> str:
        handle, path = tempfile.mkstemp(suffix=".txt", prefix="sm_cgs_")
        os.close(handle)
        self.path = write_vitamin_model(self.cgs, path, self.rename_idle)
        return self.path

    def __exit__(self, *exc) -> None:
        if self.path and os.path.exists(self.path):
            try:
                os.unlink(self.path)
            except OSError:  # pragma: no cover - best effort
                pass


# ======================================================================
# model checking and synthesis
# ======================================================================


def coalition_indices(cgs: CGS, coalition: Sequence[str]) -> List[int]:
    """VITAMIN numbers agents from 1 in the order they are declared."""
    return [cgs.agent_index(agent) + 1 for agent in coalition]


def atl_formula(cgs: CGS, coalition: Sequence[str], objective: str) -> str:
    """``<A>objective`` with the coalition rendered as VITAMIN agent numbers."""
    return "<{0}>{1}".format(",".join(str(i) for i in coalition_indices(cgs, coalition)), objective)


def natatl_formula(cgs: CGS, coalition: Sequence[str], objective: str, k: int) -> str:
    """``<{A}, k>objective``."""
    return "<{{{0}}}, {1}>{2}".format(
        ",".join(str(i) for i in coalition_indices(cgs, coalition)), k, objective
    )


def atl_model_check(cgs: CGS, coalition: Sequence[str], objective: str) -> Dict:
    """Can ``coalition`` enforce ``objective`` from ``s_I``?

    ``objective`` is an ATL path formula such as ``G(p || q)`` or ``F p``.
    Returns VITAMIN's result dictionary, with ``satisfied`` and ``states``
    added for convenience.
    """
    require_vitamin()
    from model_checker.algorithms.explicit.ATL.ATL import model_checking

    formula = atl_formula(cgs, coalition, objective)
    with _TemporaryModel(cgs) as path:
        result = dict(model_checking(formula, path))
    result["formula"] = formula
    result["satisfied"] = "True" in str(result.get("initial_state", ""))
    result["states"] = _parse_state_set(result.get("res", ""))
    return result


@dataclass
class SynthesisResult:
    """Outcome of a NatATL synthesis call."""

    satisfiable: bool
    strategy: Optional[NaturalMemorylessStrategy]
    complexity_bound: Optional[int]
    formula: str
    raw: Dict
    verified: Optional[bool] = None
    """Whether the returned strategy was independently confirmed to win.

    ``True`` means :func:`strategy_monitor.verify.enforces` -- which holds the
    coalition to the strategy exactly, with no idling smuggled in -- agrees.
    ``None`` means the check could not be run (a partial strategy, or an
    objective that is not an LTL formula).
    """

    atl_realisable: Optional[bool] = None
    """Whether plain ATL says the objective is enforceable, when cross-checked.

    ``True`` alongside ``satisfiable=False`` means NatATL found no *natural*
    strategy although the coalition can enforce the objective -- see
    :attr:`note`.
    """

    note: str = ""
    """Why a negative result may not mean what it appears to."""

    def __bool__(self) -> bool:
        return self.satisfiable


def natatl_synthesize(
    cgs: CGS,
    coalition: Sequence[str],
    objective: str,
    k: int = 2,
    add_idle_default: bool = True,
    cross_check: bool = True,
    rename_idle: bool = True,
    verify: bool = True,
) -> SynthesisResult:
    """Synthesise a winning natural memoryless strategy with VITAMIN's NatATL.

    ``objective`` is the path formula under the coalition modality, e.g.
    ``G(p || q)``.  Note that VITAMIN's ATL and NatATL parsers accept only a
    single temporal operator directly under the modality, so a goal such as the
    paper's ``G(p | (q & X p))`` cannot be passed here; give the strongest
    ATL-expressible objective instead and keep the full LTL goal for the
    goal-oriented monitor.

    When ``add_idle_default`` is set, an idle catch-all is appended to each
    agent's gate list for the states no synthesised gate covers.  This mirrors
    VITAMIN's own pruning, which lets an agent idle wherever its strategy is
    silent, and makes the returned strategy total -- as Section 5.3 requires.

    ``rename_idle`` (on by default) exports the idle action under another name.
    An action's name is arbitrary, and VITAMIN gives ``I``/``IDLE`` a special
    role: the prune admits it *alongside* whatever the strategy prescribes, so
    an agent owning an idle action is never held to its strategy.  Renaming
    takes it out of that allowance, and the prune on covered states becomes
    exact.  Measured against an exhaustive enumeration of the total natural
    memoryless strategies, this is what makes the search agree with the truth.

    It is not a fix on its own.  VITAMIN prunes states no gate covers to *idle
    only*, and matches the prescribed action against the exported token, so with
    the idle token renamed those rows can empty -- and an empty model satisfies
    every universally quantified CTL formula vacuously.  Both cases involve a
    candidate that is not a total strategy, and ``verify`` rejects them.
    Together the two give a search that is sound, and complete over the *total*
    natural memoryless strategies -- which are the only ones Section 5.3 admits.

    Pass ``rename_idle=False`` to reproduce VITAMIN's native behaviour.  For a
    model with no idle action the setting makes no difference: the export is
    byte-identical either way.

    ``verify`` checks the returned strategy with
    :func:`strategy_monitor.verify.enforces`, which holds the coalition to the
    strategy exactly and needs no VITAMIN.  A strategy that fails the check is
    *not* returned, so a positive answer is trustworthy however the prune
    behaved.

    ``cross_check`` runs plain ATL when NatATL finds nothing, and records the
    answer in :attr:`SynthesisResult.atl_realisable`.  The two can legitimately
    disagree: VITAMIN's NatATL prunes the model to *the prescribed action or
    idling*, so an agent that owns an idle action is never actually held to its
    strategy.  Where idling is unsafe, NatATL reports unsatisfiable although the
    coalition can enforce the objective.  The extra check costs one ATL run, and
    only on the failing path.
    """
    require_vitamin()
    from model_checker.algorithms.explicit.NatATL.Memoryless.NatATL import model_checking

    coalition = tuple(coalition)
    if rename_idle and not verify:
        logger.warning(
            "natatl_synthesize(rename_idle=True, verify=False): VITAMIN's prune can "
            "empty the model under renaming, in which case it accepts any candidate "
            "vacuously. Positive results from this combination are not trustworthy."
        )
    formula = natatl_formula(cgs, coalition, objective, k)
    _, tokens, _ = build_token_map(cgs, rename_idle)
    with _TemporaryModel(cgs, rename_idle) as path:
        raw = dict(model_checking(formula, path))

    if raw.get("error") or not raw.get("Satisfiability"):
        realisable, note = (None, "")
        if cross_check:
            realisable, note = _explain_failure(cgs, coalition, objective, rename_idle)
        return SynthesisResult(
            satisfiable=False,
            strategy=None,
            complexity_bound=raw.get("Complexity Bound"),
            formula=formula,
            raw=raw,
            atl_realisable=realisable,
            note=note,
        )

    witness = raw.get("Winning Strategy per agent") or []
    rules: Dict[str, List[Tuple[object, str]]] = {}
    for agent, entry in zip(coalition, witness):
        pairs = entry["condition_action_pairs"] if isinstance(entry, Mapping) else entry
        compiled = [(parse_gate(condition), tokens.get(action, action)) for condition, action in pairs]
        if add_idle_default:
            fallback = _idle_action(cgs, agent)
            if fallback is not None:
                compiled.append((parse_gate("true"), fallback))
        rules[agent] = compiled
    strategy = NaturalMemorylessStrategy(coalition=coalition, rules=rules)
    confirmed, verify_note = (None, "")
    if verify:
        confirmed, verify_note = _verify_strategy(cgs, strategy, objective)
        if confirmed is False:
            return SynthesisResult(
                False,
                None,
                raw.get("Complexity Bound"),
                formula,
                raw,
                verified=False,
                note=verify_note,
            )
    return SynthesisResult(
        True,
        strategy,
        raw.get("Complexity Bound"),
        formula,
        raw,
        verified=confirmed,
        note=verify_note,
    )


def _verify_strategy(cgs: CGS, strategy, objective: str):
    """Confirm a synthesised strategy really enforces the objective.

    ATL path formulas are LTL path formulas, so the objective can be handed
    straight to the exact checker.  Returns ``(None, "")`` when the check does
    not apply.
    """
    from .strategies import StrategyError
    from .verify import enforces

    try:
        verdict = enforces(cgs, strategy, objective)
    except StrategyError as error:
        # The witness is not a strategy in the sense of Section 5.3: it leaves a
        # state unprescribed, or prescribes something the protocol forbids.
        # VITAMIN completes such a witness with idling, which is only available
        # when the model has an idle action -- and its own prune reads an
        # uncovered state as a dead end, where the objective holds vacuously.
        # Neither is a reason to accept it.
        return False, (
            "VITAMIN reported this strategy as winning, but it is not a total "
            "strategy: {0}. Section 5.3 defines a strategy as a function, and "
            "VITAMIN's prune treats the unprescribed states as dead ends, where the "
            "objective holds vacuously.".format(str(error).splitlines()[0].rstrip(":"))
        )
    except Exception as error:  # e.g. an objective that is not an LTL formula
        return None, "could not verify the synthesised strategy: {0}".format(
            str(error).splitlines()[0]
        )
    if verdict.holds:
        return True, ""
    prefix, loop = verdict.counterexample or ([], [])
    return False, (
        "VITAMIN reported this strategy as winning, but holding the coalition to it "
        "exactly gives the counterexample {0}({1})^omega. Under rename_idle this is "
        "expected: emptied rows make universally quantified formulas hold vacuously, "
        "so VITAMIN's acceptance carries no information and only this check does."
        .format(" ".join(prefix), " ".join(loop))
    )


def _explain_failure(cgs: CGS, coalition: Sequence[str], objective: str, rename_idle=False):
    """Ask ATL whether the objective was enforceable after all, and say so."""
    try:
        realisable = bool(atl_model_check(cgs, coalition, objective)["satisfied"])
    except Exception:  # ATL cannot parse every NatATL objective
        return None, ""
    if not realisable:
        return False, "ATL agrees the objective is not enforceable by this coalition."
    idlers = [agent for agent in coalition if _idle_action(cgs, agent) is not None]
    note = (
        "ATL says {0} CAN enforce this objective, so the negative result is "
        "NatATL's, not the model's.".format(list(coalition))
    )
    if idlers and not rename_idle:
        note += (
            " VITAMIN's NatATL prunes each agent's moves to the prescribed action"
            " or idling, so {0} are never held to their strategy; where idling is"
            " unsafe this reports unsatisfiable. This run passed rename_idle=False;"
            " the default renames the idle action on export, which makes the prune"
            " exact and avoids exactly this.".format(idlers)
        )
    elif idlers:
        note += (
            " The idle allowance is not the cause: this ran with the idle action"
            " renamed. The objective may simply be unrealisable by a *natural*"
            " strategy of this complexity, even though some strategy enforces it."
        )
    return True, note


def _idle_action(cgs: CGS, agent: str) -> Optional[str]:
    for candidate in IDLE_ALIASES:
        if candidate in cgs.actions[agent]:
            return candidate
    return None


def _parse_state_set(text: str):
    """Pull the state tuple out of VITAMIN's ``"Result: ('s0', 's1')"`` string."""
    if "Result:" not in text:
        return None
    payload = text.split("Result:", 1)[1].strip()
    try:
        import ast

        value = ast.literal_eval(payload)
    except (ValueError, SyntaxError):
        return None
    if isinstance(value, (set, list, tuple)):
        return set(value)
    return None
