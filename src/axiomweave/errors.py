"""Exceptions raised by the AxiomWeave DSL (language-spec §9, interop-spec §4.2)."""


class AxwError(Exception):
    """Base class of all AxiomWeave errors."""


class AxwTypeError(AxwError, TypeError):
    """Invalid proposition construction or truth-value conversion of a `Prop`."""


class DeclarationError(AxwError):
    """Invalid declaration, duplicate name or proof, or declaration-order violation."""


class TacticError(AxwError):
    """A tactic does not apply to the current goal or its arguments."""


class ScopeError(AxwError):
    """A `Fact` is used outside the hypotheses it depends on."""


class BackendUnavailableError(AxwError):
    """An optional external tool (such as Z3) is not installed (interop-spec §4.2)."""
