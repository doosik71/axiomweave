"""Standard axiom allow list (kernel-spec §9.2, §15)."""

from collections.abc import Mapping
from types import MappingProxyType
from typing import Any

from axiomweave.kernel.certificate import declaration_hash

CLASSICAL_EM = {
    "kind": "axiom",
    "name": "classical.em",
    "statement": ["or", ["atom", "P"], ["imp", ["atom", "P"], ["false"]]],
}

# Standard arithmetic (kernel-spec §15.2). Bound variables are de Bruijn indices.
_N = "arith.Nat"
_Z: list[Any] = ["app", "arith.zero", []]
_V0: list[Any] = ["var", 0]
_V1: list[Any] = ["var", 1]


def _s(t: list[Any]) -> list[Any]:
    return ["app", "arith.succ", [t]]


def _add(a: list[Any], b: list[Any]) -> list[Any]:
    return ["app", "arith.add", [a, b]]


def _mul(a: list[Any], b: list[Any]) -> list[Any]:
    return ["app", "arith.mul", [a, b]]


def _p(t: list[Any]) -> list[Any]:
    return ["pvar", "P", [t]]


ARITH_STATEMENTS: dict[str, list[Any]] = {
    "arith.succ_ne_zero": ["forall", _N, ["imp", ["eq", _s(_V0), _Z], ["false"]]],
    "arith.succ_inj": [
        "forall",
        _N,
        ["forall", _N, ["imp", ["eq", _s(_V1), _s(_V0)], ["eq", _V1, _V0]]],
    ],
    "arith.add_zero": ["forall", _N, ["eq", _add(_V0, _Z), _V0]],
    "arith.add_succ": [
        "forall",
        _N,
        ["forall", _N, ["eq", _add(_V1, _s(_V0)), _s(_add(_V1, _V0))]],
    ],
    "arith.mul_zero": ["forall", _N, ["eq", _mul(_V0, _Z), _Z]],
    "arith.mul_succ": [
        "forall",
        _N,
        ["forall", _N, ["eq", _mul(_V1, _s(_V0)), _add(_mul(_V1, _V0), _V1)]],
    ],
    "arith.induction": [
        "imp",
        _p(_Z),
        ["imp", ["forall", _N, ["imp", _p(_V0), _p(_s(_V0))]], ["forall", _N, _p(_V0)]],
    ],
}

STANDARD_AXIOMS: Mapping[str, str] = MappingProxyType(
    {
        "classical.em": declaration_hash(CLASSICAL_EM),
        **{
            name: declaration_hash({"kind": "axiom", "name": name, "statement": statement})
            for name, statement in ARITH_STATEMENTS.items()
        },
    }
)
