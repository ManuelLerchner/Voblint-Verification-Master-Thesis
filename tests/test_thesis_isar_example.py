"""The locale-check example the Tooling chapter prints must still be flagged."""

import subprocess
from pathlib import Path

EXAMPLE = Path(__file__).resolve().parents[1] / "thesis/shared/code/isar-locale"


def test_locale_check_flags_the_misspelled_constant():
    proc = subprocess.run(
        ["isar", "check", "locales", ".", "--color", "never"],
        cwd=EXAMPLE,
        capture_output=True,
        text=True,
        check=False,
    )
    assert proc.stdout == (EXAMPLE / "expected.txt").read_text()
