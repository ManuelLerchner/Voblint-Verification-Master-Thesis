"""A flag written without its dashes must not be swallowed.

Every bare word used to overwrite the input file, so the last one won and the
strays vanished: `--analysis interval context entry-state F.vimp` ran a
context-INSENSITIVE analysis on F.vimp and its report read as a precision
regression rather than a typo. Silent argument loss is the worst failure mode
for a tool whose output is verdicts.

This lives here rather than in the .vimp corpus because tests/run.py classifies
a rejection as a parse error, a well-formedness error or a timeout -- argument
handling is none of those, and is not analysis behaviour at all.
"""

from __future__ import annotations

import subprocess
from pathlib import Path

import pytest

ROOT = Path(__file__).resolve().parent.parent
VOBLINT = ROOT / "cli" / "voblint"
FIXTURE = ROOT / "tests/regression/00-sanity/precision/01-straight_line_proved.vimp"


def run(*args):
    return subprocess.run([str(VOBLINT), *args], capture_output=True, text=True)


def test_flag_without_dashes_is_rejected():
    r = run("--analysis", "interval", "context", "entry-state", str(FIXTURE))
    assert r.returncode != 0, (
        "a flag written without dashes was accepted; the run silently ignored "
        f"it:\n{r.stdout}"
    )
    assert "unexpected argument" in r.stderr, r.stderr
    assert "--context" in r.stderr, (
        f"the message does not name the flag the word was meant to be:\n{r.stderr}"
    )


def test_stray_word_is_rejected():
    r = run("--analysis", "interval", "junk", str(FIXTURE))
    assert r.returncode != 0, f"a stray positional argument was accepted:\n{r.stdout}"
    assert "unexpected argument" in r.stderr, r.stderr


def test_the_correct_spelling_still_runs():
    r = run("--analysis", "interval", "--context", "entry-state", str(FIXTURE))
    assert r.returncode == 0, r.stderr
    assert "PROVED" in r.stdout, r.stdout


@pytest.mark.parametrize("flag", ["--analysis", "--context", "--timeout"])
def test_a_value_flag_still_takes_its_value(flag):
    """The rejection must not fire on a flag's own argument."""
    args = {"--analysis": ["--analysis", "interval"],
            "--context": ["--analysis", "interval", "--context", "none"],
            "--timeout": ["--analysis", "interval", "--timeout", "20"]}[flag]
    r = run(*args, str(FIXTURE))
    assert r.returncode == 0, r.stderr
