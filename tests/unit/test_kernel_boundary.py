"""The kernel imports only the standard library and itself (kernel-spec §11.1)."""

import ast
import sys
from pathlib import Path

import axiomweave.kernel

KERNEL_DIR = Path(axiomweave.kernel.__file__).parent


def _imported_modules(path: Path) -> set[str]:
    tree = ast.parse(path.read_text(encoding="utf-8"))
    names: set[str] = set()
    for node in ast.walk(tree):
        if isinstance(node, ast.Import):
            names.update(alias.name for alias in node.names)
        elif isinstance(node, ast.ImportFrom):
            assert node.level == 0, f"relative import in {path.name}"
            assert node.module is not None
            names.add(node.module)
    return names


def test_kernel_imports_only_stdlib_and_kernel() -> None:
    files = sorted(KERNEL_DIR.glob("*.py"))
    assert files
    for path in files:
        for module in _imported_modules(path):
            top = module.split(".")[0]
            allowed = top in sys.stdlib_module_names or module.startswith("axiomweave.kernel")
            assert allowed, f"{path.name} imports {module}"
