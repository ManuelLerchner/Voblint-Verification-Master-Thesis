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
SETTINGS = ["interval", "warrow", "entry-state", 0, "fixpoint", "local"]
EXPECT_DIR = REPO_ROOT / "tests/solver-trace"


def voblint_web(*traces, settings=SETTINGS, program=PROGRAM):
    """One answer per entry of [traces], all from one loaded module."""
    node = shutil.which("node")
    assert node, "node not on PATH"
    assert BUNDLE.is_file(), f"{BUNDLE} missing -- run `pixi run browser-build`"
    source = program.read_text()
    calls = [[*settings, source, trace] for trace in traces]
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


# One origin of this program narrows in two steps, so its first check needs a
# bound of at least 2; the CLI regression pins the same verdicts.
TWO_STEPS = (
    REPO_ROOT
    / "tests/regression/15-solver-choice/precision/12-bounded_narrowing_two_narrowing_steps.vimp"
)


def verdicts(answer):
    return re.findall(
        r'"condition": "([^"]*)", "verdict": "([A-Za-z_]+)"', json.dumps(answer)
    )


@pytest.mark.parametrize(
    ("rule", "first"),
    [
        ("bounded-narrowing", "PROVED"),
        ("bounded-narrowing:5", "PROVED"),
        ("bounded-narrowing:1", "UNKNOWN"),
        ("bounded-narrowing:0", "UNKNOWN"),
    ],
)
def test_the_narrowing_bound_reaches_the_solver(rule, first):
    settings = ["interval", rule, "none", 0, "fixpoint", "local"]
    off, traced = voblint_web("off", "compact", settings=settings, program=TWO_STEPS)
    assert set(verdicts(off)) == {("a <= 2", first), ("b <= 2", "PROVED")}
    assert "trace" in traced
    assert without_timing({k: v for k, v in traced.items() if k != "trace"}) == (
        without_timing(off)
    )


@pytest.mark.parametrize(
    "rule", ["bounded-narrowing:", "bounded-narrowing:-1", "warrow:2"]
)
def test_a_malformed_bound_is_an_error(rule):
    settings = ["interval", rule, "none", 0, "fixpoint", "local"]
    (answer,) = voblint_web("off", settings=settings, program=TWO_STEPS)
    assert answer == {"status": "error", "message": f"Unknown globals rule: {rule}"}


# Two writes to one global: flow-sensitively the check sees the last, on the
# shared channel it sees their join with the initial zero.
SHARED_JOIN = (
    REPO_ROOT
    / "tests/regression/04-globals/known-imprecision/03-shared_global_joins_writes.vimp"
)


@pytest.mark.parametrize(
    ("placement", "exact"), [("local", "PROVED"), ("shared", "UNKNOWN")]
)
def test_the_placement_reaches_the_analyzer(placement, exact):
    settings = ["interval", "bounded-narrowing", "none", 0, "fixpoint", placement]
    (answer,) = voblint_web("off", settings=settings, program=SHARED_JOIN)
    assert set(verdicts(answer)) == {("x == 1", exact), ("0 <= x", "PROVED")}
    assert ("shared" in answer) == (placement == "shared")
    assert answer["raw"]["input"]["pg"] == (
        "Program_Globals_Shared" if placement == "shared" else "Program_Globals_Local"
    )
