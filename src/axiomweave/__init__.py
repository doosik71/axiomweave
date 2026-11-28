"""AxiomWeave: a Python-based formal proof language (v0.1, fragments L0, L1 and L2).

See docs/language-spec.md for the DSL and docs/kernel-spec.md for the kernel.
"""

from axiomweave.core.expressions import (
    And,
    Const,
    Eq,
    Exists,
    Falsehood,
    ForAll,
    Iff,
    Implies,
    Ne,
    Not,
    Or,
    PredicateSymbol,
    Prop,
    Sort,
    Term,
    Truth,
    Var,
)
from axiomweave.errors import (
    AxwError,
    AxwTypeError,
    BackendUnavailableError,
    DeclarationError,
    ScopeError,
    TacticError,
)
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
    "BackendUnavailableError",
    "CheckReport",
    "Const",
    "DeclarationError",
    "Diagnostic",
    "Eq",
    "Exists",
    "Fact",
    "Falsehood",
    "ForAll",
    "GoalView",
    "Iff",
    "Implies",
    "Ne",
    "Not",
    "Or",
    "PredicateSymbol",
    "ProofContext",
    "Prop",
    "ScopeError",
    "Sort",
    "Status",
    "TacticError",
    "Term",
    "Theorem",
    "TheoremResult",
    "Theory",
    "Truth",
    "Var",
]
