"""AxiomWeave: a Python-based formal proof language (v0.1, fragment L0).

See docs/language-spec.md for the DSL and docs/kernel-spec.md for the kernel.
"""

from axiomweave.core.expressions import And, Falsehood, Iff, Implies, Not, Or, Prop, Truth
from axiomweave.errors import AxwError, AxwTypeError, DeclarationError, ScopeError, TacticError
from axiomweave.kernel import STANDARD_AXIOMS
from axiomweave.language.proof import Fact, GoalView, ProofContext
from axiomweave.language.theory import (
    Axiom,
    CheckReport,
    Diagnostic,
    Status,
    Theorem,
    TheoremResult,
    Theory,
)

__all__ = [
    "STANDARD_AXIOMS",
    "And",
    "Axiom",
    "AxwError",
    "AxwTypeError",
    "CheckReport",
    "DeclarationError",
    "Diagnostic",
    "Fact",
    "Falsehood",
    "GoalView",
    "Iff",
    "Implies",
    "Not",
    "Or",
    "ProofContext",
    "Prop",
    "ScopeError",
    "Status",
    "TacticError",
    "Theorem",
    "TheoremResult",
    "Theory",
    "Truth",
]
