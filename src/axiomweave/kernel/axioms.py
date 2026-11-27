"""Standard axiom allow list (kernel-spec §9.2)."""

from collections.abc import Mapping
from types import MappingProxyType

from axiomweave.kernel.certificate import declaration_hash

CLASSICAL_EM = {
    "kind": "axiom",
    "name": "classical.em",
    "statement": ["or", ["atom", "P"], ["imp", ["atom", "P"], ["false"]]],
}

STANDARD_AXIOMS: Mapping[str, str] = MappingProxyType(
    {"classical.em": declaration_hash(CLASSICAL_EM)}
)
