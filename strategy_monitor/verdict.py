"""Monitor verdicts.

The verdict domain starts from the three-valued domain ``B_3 = {top, bot, ?}`` of
Bauer et al.  This package refines the positive verdict into two, and the goal
monitor additionally reports model violations, giving the
four-valued domain ``{top^G_G, bot^G, bot^M, ?}``.  All of them live in the single
enumeration below so that a composite monitor can report one value.
"""

from __future__ import annotations

import sys

from dataclasses import dataclass
from enum import Enum
from typing import Optional, Tuple


class Verdict(Enum):
    """Every verdict the monitors can emit."""

    UNKNOWN = "?"
    """No conclusion can yet be drawn."""

    BOT = "bot"
    """A coalition strategy violation: some agent deviated."""

    TOP_S = "top^S_G"
    """Strategy-adherence truth, relativised to the model: every window still
    observable from the current state has been validated."""

    TOP_G = "top^G_G"
    """Goal-oriented truth, relativised to the model: the goal holds on every
    continuation that respects the CGS, and is superseded by ``BOT_M`` should
    the system leave it."""

    BOT_G = "bot^G"
    """Goal violation: the goal fails however the system continues."""

    BOT_M = "bot^M"
    """Model violation: the observed trace is not a run of the given CGS."""

    @property
    def is_violation(self) -> bool:
        return self in (Verdict.BOT, Verdict.BOT_G, Verdict.BOT_M)

    @property
    def is_conclusive(self) -> bool:
        return self is not Verdict.UNKNOWN

    @property
    def symbol(self) -> str:
        """The mathematical glyph for this verdict."""
        return _SYMBOLS[self]

    def __str__(self) -> str:
        """The glyph where the terminal can print it, the ASCII name otherwise."""
        return _SYMBOLS[self] if _UNICODE_OUTPUT else self.value


_SYMBOLS = {
    Verdict.UNKNOWN: "?",
    Verdict.BOT: "⊥",
    Verdict.TOP_S: "⊤^S_G",
    Verdict.TOP_G: "⊤^G_G",
    Verdict.BOT_G: "⊥^G",
    Verdict.BOT_M: "⊥^M",
}


def _terminal_supports_unicode() -> bool:
    encoding = getattr(sys.stdout, "encoding", None) or "ascii"
    try:
        "⊥⊤".encode(encoding)
    except (UnicodeEncodeError, LookupError):
        return False
    return True


_UNICODE_OUTPUT = _terminal_supports_unicode()


@dataclass(frozen=True)
class Violation:
    """A strategy deviation, attributed to one agent.

    Attribution is what coalition repair needs to know which agent to exclude from
    the coalition; it holds by construction for the ``k``-bounded and natural
    memoryless monitors, which check compliance per agent.
    """

    step: int
    """Index ``j`` in the trace at which the deviation was observed."""

    state: str
    """``omega_s[j]``, the state the deviation happened in."""

    agent: str
    prescribed: Optional[str]
    observed: str
    window: Tuple[str, ...] = ()
    """The memory configuration ``(omega_s^{<=j})^{>=k}`` consulted."""

    def __str__(self) -> str:
        expected = self.prescribed if self.prescribed is not None else "<undefined>"
        return (
            "step {0}: agent {1!r} played {2!r} in {3!r}, strategy prescribes {4!r} "
            "for memory configuration {5}".format(
                self.step, self.agent, self.observed, self.state, expected, list(self.window)
            )
        )


@dataclass(frozen=True)
class ModelDeviation:
    """An observed transition the CGS does not contain -- input to model repair."""

    step: int
    state: str
    profile: Tuple[str, ...]
    observed_successor: Optional[str]
    expected_successor: Optional[str]
    detail: str = ""

    def __str__(self) -> str:
        return "step {0}: delta({1!r}, {2}) should be {3!r} but the system went to {4!r}{5}".format(
            self.step,
            self.state,
            list(self.profile),
            self.expected_successor,
            self.observed_successor,
            " ({0})".format(self.detail) if self.detail else "",
        )
