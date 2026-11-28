"""SymPy polynomial identity check for `ctx.ring()` (interop-spec §5.4).

SymPy only decides and explains: a wrong answer can make the tactic fail but
never produces a proof, which `axiomweave.language.ring` rebuilds from the
`arith` theorems for the kernel to check. SymPy is an optional dependency
(`symbolic` extra) imported on first use.
"""

import importlib
from dataclasses import dataclass
from typing import Any

from axiomweave.core.expressions import Term
from axiomweave.errors import BackendUnavailableError
from axiomweave.language.ring import atom_key, classify


@dataclass(frozen=True)
class IdentityCheck:
    identity: bool
    difference: str  # lhs - rhs, expanded, with atoms shown as terms


def _sympy() -> Any:
    try:
        return importlib.import_module("sympy")
    except ImportError as exc:
        raise BackendUnavailableError(
            "ring needs SymPy; install it with `uv sync --extra symbolic`"
        ) from exc


def check_identity(lhs: Term, rhs: Term) -> IdentityCheck:
    """Whether lhs and rhs are equal as polynomials over their atoms."""
    sympy = _sympy()
    symbols: dict[str, Any] = {}
    shown: dict[str, str] = {}

    def convert(term: Term) -> Any:
        kind, args = classify(term)
        if kind == "zero":
            return sympy.Integer(0)
        if kind == "succ":
            return convert(args[0]) + 1
        if kind == "add":
            return convert(args[0]) + convert(args[1])
        if kind == "mul":
            return convert(args[0]) * convert(args[1])
        key = atom_key(term)
        if key not in symbols:
            symbols[key] = sympy.Symbol(f"a{len(symbols)}", integer=True, nonnegative=True)
            shown[key] = str(term)
        return symbols[key]

    difference = sympy.expand(convert(lhs) - convert(rhs))
    names = _display_names(shown)
    readable = difference.xreplace({symbols[k]: sympy.Symbol(names[k]) for k in symbols})
    return IdentityCheck(difference == 0, str(readable))


def _display_names(shown: dict[str, str]) -> dict[str, str]:
    """Atom display names, made unique when two atoms print alike."""
    names: dict[str, str] = {}
    used: set[str] = set()
    for key, text in shown.items():
        name, i = text, 1
        while name in used:
            i += 1
            name = f"{text}#{i}"
        used.add(name)
        names[key] = name
    return names
