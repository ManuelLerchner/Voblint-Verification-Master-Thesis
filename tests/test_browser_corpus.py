"""The regression corpus through the WebAssembly analyzer, at a browser's stack size.

The browser runs the analyzer on a much smaller stack than the native CLI, so
code that recurses once per event or per list element can pass every native
test and still stop the playground with "Maximum call stack size exceeded".
Each fixture runs here with its own settings and the compact trace on, the
heaviest path a page session takes, on Node's default stack, about what a
browser gives a worker. The deepest fixtures need over 800 KiB of it, so a
change that deepens the solver's recursion shows up here first. Fixtures that
are meant to diverge, the ones whose header bounds the run with --timeout, are
left out.

Run after `pixi run browser-build`; a missing bundle is a failed prerequisite.
"""

import json
import os
import shutil
import subprocess
import sys
from pathlib import Path

import pytest

REPO_ROOT = Path(__file__).resolve().parent.parent
sys.path.insert(0, str(REPO_ROOT / "scripts"))

from vimp_fixture import analysis_settings, param_args  # noqa: E402

BUNDLE = Path(
    os.environ.get(
        "VOBLINT_WEB_BUNDLE", REPO_ROOT / "build/browser/voblint_web.bc.wasm.js"
    )
)
HARNESS = REPO_ROOT / "tests/voblint_web_calls.cjs"
CORPUS = REPO_ROOT / "tests/regression"
# KiB: Node's default, about the 1 MiB a browser gives a worker.
STACK_KIB = 984
# Seconds per fixture; a run this slow under WebAssembly is a regression.
BUDGET_S = 20
CHUNK = 40

FIXTURES = sorted(
    p for p in CORPUS.rglob("*.vimp") if "--timeout" not in (param_args(p) or [])
)


def web_call(path):
    """The playground's call for a fixture: its PARAM settings, the CLI's
    defaults for the rest."""
    s = analysis_settings(param_args(path) or [])
    placement = s.get("program_globals", "flow-sensitive")
    globals_rule = s.get(
        "globals", "bounded-narrowing" if placement == "flow-insensitive" else "warrow"
    )
    if "narrow_bound" in s:
        globals_rule += f":{s['narrow_bound']}"
    return [
        ",".join(s.get("analyses", ["interval"])),
        globals_rule,
        s.get("context", "none"),
        s.get("context_depth", 0),
        s.get("int_refinement", "fixpoint"),
        placement,
        path.read_text(),
        "compact",
    ]


def run(paths):
    node = shutil.which("node")
    assert node, "node not on PATH"
    assert BUNDLE.is_file(), f"{BUNDLE} missing -- run `pixi run browser-build`"
    return subprocess.run(
        [node, f"--stack-size={STACK_KIB}", "--require", str(HARNESS), str(BUNDLE)],
        capture_output=True,
        text=True,
        cwd=REPO_ROOT,
        env={
            **os.environ,
            "VOBLINT_WEB_CALLS": json.dumps([web_call(p) for p in paths]),
        },
        timeout=BUDGET_S * len(paths),
    )


def failure(path):
    """Why one fixture fails alone: the innermost distinct frames."""
    proc = run([path])
    frames = []
    for line in proc.stderr.splitlines():
        line = line.strip()
        if line.startswith("at "):
            name = line.split(" (")[0]
            if not frames or frames[-1] != name:
                frames.append(name)
    first = next((ln for ln in proc.stderr.splitlines() if "Error" in ln), "")
    return f"{path.relative_to(CORPUS)}: {first.strip()} {frames[:4]}"


@pytest.mark.parametrize(
    "start", range(0, len(FIXTURES), CHUNK), ids=lambda i: f"fixtures-{i}"
)
def test_corpus_runs_in_the_browser_analyzer(start):
    paths = FIXTURES[start : start + CHUNK]
    proc = run(paths)
    if proc.returncode != 0:
        pytest.fail("\n".join(failure(p) for p in paths if run([p]).returncode))
    errors = [
        f"{p.relative_to(CORPUS)}: {answer['message']}"
        for p, answer in zip(
            paths, map(json.loads, json.loads(proc.stdout)), strict=True
        )
        if answer["status"] == "error" and "stack" in answer["message"].lower()
    ]
    assert not errors, "\n".join(errors)
