"""The playground's solver trace: the WebAssembly analyzer run under Node in
every trace mode, several runs in one process as in a page session. Each mode's
trace must be the CLI's, checked against tests/solver-trace/.

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
# The settings of the traces in tests/solver-trace/.
SETTINGS = ["interval", "warrow", "entry-state", 0, "fixpoint"]
EXPECT_DIR = REPO_ROOT / "tests/solver-trace"


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


def expected(name):
    """The CLI's trace of the same run, under the browser's program name."""
    text = (EXPECT_DIR / f"{name}.expected").read_text()
    return text.replace("docs/readme-figures/contexts.vimp", "browser.vimp")


# What a reader switching the option produces: off, each form, a form again,
# off again.
MODES = ["off", "compact", "compact", "verbose", "jsonl", "off"]


@pytest.fixture(scope="module")
def runs():
    return dict(enumerate(voblint_web(*MODES)))


def test_compact_is_the_cli_trace(runs):
    trace = runs[1]["trace"]
    assert re.search(r"^FLUSH ", trace, re.M)
    assert "CHECK    a == 6 at pp4: PROVED\n" in trace
    assert "CHECK    b == 5 at pp5: PROVED\n" in trace
    assert trace == expected("contexts.compact")


def test_verbose_is_the_cli_trace(runs):
    assert runs[3]["trace"] == expected("contexts.verbose")


def test_jsonl_is_the_cli_trace(runs):
    trace = runs[4]["trace"]
    assert trace == expected("contexts.jsonl")
    assert json.loads(trace.splitlines()[0])["program"] == "browser.vimp"


def test_repeated_runs_do_not_accumulate(runs):
    assert runs[2]["trace"] == runs[1]["trace"]


def test_tracing_off_adds_nothing(runs):
    off, off_again = runs[0], runs[5]
    assert off["status"] == "ok"
    assert "trace" not in off and "trace" not in off_again
    assert without_timing(off_again) == without_timing(off)
    for traced in (runs[1], runs[3], runs[4]):
        assert without_timing({k: v for k, v in traced.items() if k != "trace"}) == (
            without_timing(off)
        )


def test_unknown_mode_is_an_error():
    (answer,) = voblint_web("yes")
    assert answer == {"status": "error", "message": "Unknown trace mode: yes"}
