"""The playground's solver trace: the WebAssembly analyzer run under Node with
tracing on and off, several runs in one process as in a page session.

Run after `pixi run browser-build`; a missing bundle is a failed prerequisite.
"""

import json
import os
import re
import shutil
import subprocess
from pathlib import Path

import pytest

REPO_ROOT = Path(__file__).resolve().parent.parent
BUNDLE = Path(
    os.environ.get(
        "VOBLINT_WEB_BUNDLE", REPO_ROOT / "build/browser/voblint_web.bc.wasm.js"
    )
)
HARNESS = REPO_ROOT / "tests/voblint_web_calls.cjs"
PROGRAM = REPO_ROOT / "docs/readme-figures/contexts.vimp"
# The settings of tests/solver-trace/contexts.compact.expected.
SETTINGS = ["interval", "warrow", "entry-state", 0, "fixpoint"]


def voblint_web(*traces):
    """One answer per entry of [traces], all from one loaded module."""
    node = shutil.which("node")
    assert node, "node not on PATH"
    assert BUNDLE.is_file(), f"{BUNDLE} missing -- run `pixi run browser-build`"
    source = PROGRAM.read_text()
    calls = [[*SETTINGS, source, trace] for trace in traces]
    proc = subprocess.run(
        [node, "--require", str(HARNESS), str(BUNDLE)],
        capture_output=True,
        text=True,
        cwd=REPO_ROOT,
        env={**os.environ, "VOBLINT_WEB_CALLS": json.dumps(calls)},
        timeout=120,
    )
    assert proc.returncode == 0, proc.stderr
    return [json.loads(answer) for answer in json.loads(proc.stdout)]


def without_timing(answer):
    return {key: value for key, value in answer.items() if key != "timing"}


@pytest.fixture(scope="module")
def runs():
    # off, on, on again, off again: what a reader toggling the option produces.
    return voblint_web(False, True, True, False)


def test_trace_is_the_cli_compact_trace(runs):
    trace = runs[1]["trace"]
    assert re.search(r"^FLUSH ", trace, re.M)
    assert "CHECK    a == 6 at pp4: PROVED\n" in trace
    assert "CHECK    b == 5 at pp5: PROVED\n" in trace
    expected = (REPO_ROOT / "tests/solver-trace/contexts.compact.expected").read_text()
    assert trace == expected.replace(
        "program:  docs/readme-figures/contexts.vimp", "program:  browser.vimp"
    )


def test_repeated_runs_do_not_accumulate(runs):
    assert runs[2]["trace"] == runs[1]["trace"]


def test_tracing_off_adds_nothing(runs):
    off, on, _, off_again = runs
    assert off["status"] == "ok"
    assert "trace" not in off and "trace" not in off_again
    assert without_timing(off_again) == without_timing(off)
    assert without_timing({k: v for k, v in on.items() if k != "trace"}) == (
        without_timing(off)
    )
