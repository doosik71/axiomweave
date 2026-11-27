"""`axw check` and `axw verify` in separate processes (language-spec §8, kernel-spec §11.2)."""

import json
import os
import subprocess
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[2]
EXAMPLE = ROOT / "examples" / "logic" / "implication.py"


def axw(*args: str, cwd: Path = ROOT) -> subprocess.CompletedProcess[str]:
    env = {**os.environ, "PYTHONIOENCODING": "utf-8"}
    return subprocess.run(
        [sys.executable, "-m", "axiomweave.cli", *args],
        capture_output=True,
        text=True,
        encoding="utf-8",
        cwd=cwd,
        env=env,
        check=False,
    )


def test_check_readme_example() -> None:
    result = axw("check", str(EXAMPLE))
    assert result.returncode == 0, result.stdout + result.stderr
    assert "VERIFIED  examples.implication.imp_trans" in result.stdout


def test_check_fails_on_bad_proof(tmp_path: Path) -> None:
    source = tmp_path / "bad.py"
    source.write_text(
        "from axiomweave import Prop, Theory\n"
        "P = Prop.symbol('P')\n"
        "thy = Theory('demo.bad')\n"
        "@thy.theorem\n"
        "def t():\n"
        "    return P\n"
        "@thy.proof(t)\n"
        "def _(ctx):\n"
        "    ctx.intro()\n",
        encoding="utf-8",
    )
    result = axw("check", str(source))
    assert result.returncode == 1
    assert "REJECTED" in result.stdout


def export_example(tmp_path: Path) -> Path:
    script = tmp_path / "export.py"
    target = tmp_path / "implication.axwp"
    script.write_text(
        "import runpy, sys\n"
        f"module = runpy.run_path({str(EXAMPLE)!r})\n"
        "thy = module['thy']\n"
        "assert thy.check().ok\n"
        f"thy.export({str(target)!r})\n",
        encoding="utf-8",
    )
    subprocess.run([sys.executable, str(script)], check=True, cwd=ROOT)
    return target


def test_verify_exported_certificate(tmp_path: Path) -> None:
    certificate = export_example(tmp_path)
    result = axw("verify", str(certificate))
    assert result.returncode == 0, result.stdout + result.stderr
    assert result.stdout.strip().endswith("ok")


def test_verify_rejects_tampered_certificate(tmp_path: Path) -> None:
    certificate = export_example(tmp_path)
    bundle = json.loads(certificate.read_text(encoding="utf-8"))
    bundle["declarations"][0]["statement"] = ["imp", ["atom", "Q"], ["atom", "Q"]]
    certificate.write_text(json.dumps(bundle), encoding="utf-8")
    result = axw("verify", str(certificate))
    assert result.returncode == 1
    assert "E_HASH_MISMATCH" in result.stdout


def test_verify_allow_option_format(tmp_path: Path) -> None:
    certificate = export_example(tmp_path)
    assert axw("verify", str(certificate), "--allow", "no-equals-sign").returncode == 2
