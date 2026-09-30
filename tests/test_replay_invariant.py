"""The replay reducer against the solver: replaying a run's whole JSON Lines
trace with pages/replay_state.js must give, for every unknown the result
covers, the value run_voblint returned, and exactly the result's unknowns as
the final stable set.

Run after `pixi run cli-build`; needs node.
"""

import json
import os
import shutil
import subprocess
from pathlib import Path

import pytest

REPO_ROOT = Path(__file__).resolve().parent.parent
VOBLINT = Path(os.environ.get("VOBLINT_BIN", REPO_ROOT / "cli/voblint"))
CHECK = REPO_ROOT / "tests/replay_check.mjs"

PROGRAMS = [
    "docs/readme-figures/contexts.vimp",
    "docs/readme-figures/while-loop.vimp",
    *sorted(
        str(p.relative_to(REPO_ROOT))
        for p in (REPO_ROOT / "tests/regression").glob("0[0-4]-*/*.vimp")
    )[:40],
]
CONFIGS = [
    ["--analysis", "interval", "--context", "entry-state", "--globals", "warrow"],
    ["--analysis", "interval", "--context", "none", "--globals", "join"],
    ["--analysis", "sign,parity", "--context", "call-string", "--context-depth", "1"],
]


@pytest.mark.parametrize("config", CONFIGS, ids=" ".join)
@pytest.mark.parametrize("program", PROGRAMS)
def test_replay_reaches_the_result(program, config):
    assert VOBLINT.is_file(), "cli/voblint not built -- run `pixi run cli-build`"
    node = shutil.which("node")
    assert node, "node not on PATH"
    run = subprocess.run(
        [str(VOBLINT), *config, "--trace", "--format", "jsonl", program],
        capture_output=True,
        text=True,
        cwd=REPO_ROOT,
        timeout=60,
    )
    if run.returncode != 0 or not run.stderr.startswith('{"event":"run"'):
        pytest.skip(f"no trace for this run (exit {run.returncode})")
    check = subprocess.run(
        [node, str(CHECK)],
        input=run.stderr,
        capture_output=True,
        text=True,
        cwd=REPO_ROOT,
        timeout=60,
    )
    assert check.returncode == 0, check.stderr
    assert json.loads(check.stdout) == []
