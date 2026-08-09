"""Subprocess wrappers around ast_driver/voblint for the property tests.

Every call is timeout-bounded: a parser hang is exactly the kind of defect
mutation fuzzing exists to catch, so a hang must fail the test, not stall
the run.
"""

import subprocess
import tempfile
from pathlib import Path

from strategies import sexp

PROPERTY_DIR = Path(__file__).resolve().parent
REPO_ROOT = PROPERTY_DIR.parent.parent
AST_DRIVER = PROPERTY_DIR / "ast_driver"
VOBLINT = REPO_ROOT / "cli" / "voblint"

TIMEOUT = 5.0


class Hung(AssertionError):
    def __init__(self, label, input_text):
        super().__init__(f"{label} did not terminate within {TIMEOUT}s on:\n{input_text}")


def run_ast_driver(program) -> subprocess.CompletedProcess:
    text = sexp(program)
    try:
        return subprocess.run(
            [str(AST_DRIVER)], input=text, capture_output=True, text=True, timeout=TIMEOUT
        )
    except subprocess.TimeoutExpired:
        raise Hung("ast_driver", text) from None


def _dump(program, flag: str) -> str:
    text = sexp(program)
    try:
        result = subprocess.run(
            [str(AST_DRIVER), flag], input=text, capture_output=True, text=True, timeout=TIMEOUT
        )
    except subprocess.TimeoutExpired:
        raise Hung(f"ast_driver {flag}", text) from None
    assert result.returncode == 0, f"ast_driver {flag} failed on {text}:\n{result.stdout}"
    return result.stdout


def dump_source(program) -> str:
    """pretty_string_of_program(program) -- the printer's direct output."""
    return _dump(program, "--print-source")


def dump_reprinted(program) -> str:
    """pretty_string_of_program(parse(pretty_string_of_program(program))) --
    only meaningful (and only guaranteed to succeed) for a program that
    round-trips; callers should assert that separately."""
    return _dump(program, "--print-reprinted")


def run_parse_only(source: str) -> subprocess.CompletedProcess:
    with tempfile.NamedTemporaryFile(
        mode="w", suffix=".vimp", dir=PROPERTY_DIR, delete=True
    ) as f:
        f.write(source)
        f.flush()
        try:
            return subprocess.run(
                [str(VOBLINT), "--parse-only", f.name],
                capture_output=True,
                text=True,
                timeout=TIMEOUT,
            )
        except subprocess.TimeoutExpired:
            raise Hung("voblint --parse-only", source) from None
