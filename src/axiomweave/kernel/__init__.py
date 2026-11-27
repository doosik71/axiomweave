"""AxiomCore: the trusted L0 proof-checking kernel (docs/kernel-spec.md).

This package may import only the Python standard library and its own modules.
"""

from axiomweave.kernel.axioms import STANDARD_AXIOMS
from axiomweave.kernel.certificate import (
    DEFAULT_LIMITS,
    Limits,
    bundle_hash,
    canonical_json,
    declaration_hash,
)
from axiomweave.kernel.checker import (
    ACCEPTED,
    REJECTED,
    VERIFIED,
    DeclarationResult,
    KernelReport,
    check_bundle,
)
from axiomweave.kernel.errors import Diagnostic

__all__ = [
    "ACCEPTED",
    "DEFAULT_LIMITS",
    "REJECTED",
    "STANDARD_AXIOMS",
    "VERIFIED",
    "DeclarationResult",
    "Diagnostic",
    "KernelReport",
    "Limits",
    "bundle_hash",
    "canonical_json",
    "check_bundle",
    "declaration_hash",
]
