"""Kernel error codes and the internal rejection exception (kernel-spec §10.2)."""

from dataclasses import dataclass

E_FORMAT = "E_FORMAT"
E_VERSION = "E_VERSION"
E_NAME = "E_NAME"
E_FRAGMENT = "E_FRAGMENT"
E_DUPLICATE_DECL = "E_DUPLICATE_DECL"
E_AXIOM_NOT_ALLOWED = "E_AXIOM_NOT_ALLOWED"
E_HASH_MISMATCH = "E_HASH_MISMATCH"
E_HYP_UNKNOWN = "E_HYP_UNKNOWN"
E_HYP_NOT_FRESH = "E_HYP_NOT_FRESH"
E_RULE_MISMATCH = "E_RULE_MISMATCH"
E_SUBST_DOMAIN = "E_SUBST_DOMAIN"
E_UNKNOWN_DECL = "E_UNKNOWN_DECL"
E_CONCLUSION_MISMATCH = "E_CONCLUSION_MISMATCH"
E_AXIOMS_MISMATCH = "E_AXIOMS_MISMATCH"
E_LIMIT = "E_LIMIT"
E_INTERNAL = "E_INTERNAL"


@dataclass(frozen=True)
class Diagnostic:
    """A rejection reason: error code, location path and human-readable message."""

    code: str
    path: str
    message: str


class KernelError(Exception):
    """Raised inside the kernel to reject input; converted to a Diagnostic at the entry point."""

    def __init__(self, code: str, path: str, message: str) -> None:
        super().__init__(f"{code} at {path}: {message}")
        self.diagnostic = Diagnostic(code, path, message)
