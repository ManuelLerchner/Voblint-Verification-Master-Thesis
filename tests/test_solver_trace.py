"""The solver tracer (`voblint --trace`): the trace calls in the exported
module, option handling, output separation, the order of events on the
context-sensitive running example, the Goblint-style verbose form, and the whole
compact, verbose and JSON Lines traces against tests/solver-trace/.

Run after `pixi run cli-build`; a missing executable is a failed prerequisite.
"""

import json
import os
import re
import subprocess
from pathlib import Path

import pytest

REPO_ROOT = Path(__file__).resolve().parent.parent
VOBLINT = Path(os.environ.get("VOBLINT_BIN", REPO_ROOT / "cli/voblint"))
GENERATED = REPO_ROOT / "codegen/generated/ml/Voblint_CLI.ml"
PROGRAM = "docs/readme-figures/contexts.vimp"
ARGS = ["--analysis", "interval", "--globals", "warrow", "--context", "entry-state"]
EXPECT_DIR = REPO_ROOT / "tests/solver-trace"


def voblint(*args):
    assert VOBLINT.is_file(), "cli/voblint not built -- run `pixi run cli-build`"
    proc = subprocess.run(
        [str(VOBLINT), *args],
        capture_output=True,
        text=True,
        cwd=REPO_ROOT,
        timeout=30,
    )
    assert proc.returncode == 0, proc.stderr
    return proc


@pytest.fixture(scope="module")
def events():
    proc = voblint(*ARGS, "--trace", "--format", "jsonl", PROGRAM)
    return [json.loads(line) for line in proc.stderr.splitlines()]


def is_seed(unknown, procedure, values):
    return (
        unknown.get("kind") == "activation_seed"
        and unknown["procedure"] == procedure
        and unknown["context"].get("values") == values
    )


@pytest.mark.parametrize(
    "trace_args",
    [[], ["--verbose"], ["--format", "jsonl"], ["--compact", "--format", "text"]],
)
def test_stdout_unchanged(trace_args):
    plain = voblint(*ARGS, PROGRAM)
    traced = voblint(*ARGS, "--trace", *trace_args, PROGRAM)
    assert traced.stdout == plain.stdout
    assert plain.stderr == ""
    assert traced.stderr


def test_output_file(tmp_path):
    out = tmp_path / "trace.jsonl"
    proc = voblint(*ARGS, "--trace", "--format", "jsonl", "--output", str(out), PROGRAM)
    assert proc.stderr == ""
    assert out.read_text().startswith('{"event":"run","schema":2')


@pytest.mark.parametrize("flag", [["--compact"], ["--verbose"]])
def test_style_implies_trace(flag):
    assert voblint(*ARGS, *flag, PROGRAM).stderr.startswith("Voblint trace\n")


def test_format_implies_trace():
    first = voblint(*ARGS, "--format", "jsonl", PROGRAM).stderr.splitlines()[0]
    assert json.loads(first)["event"] == "run"


def test_output_implies_trace(tmp_path):
    out = tmp_path / "trace.txt"
    proc = voblint(*ARGS, "--output", str(out), PROGRAM)
    assert proc.stderr == ""
    assert out.read_text().startswith("Voblint trace\n")


@pytest.mark.parametrize(
    "name, trace_args",
    [
        ("contexts.compact", ["--trace"]),
        ("contexts.verbose", ["--trace", "--verbose"]),
        ("contexts.jsonl", ["--format", "jsonl"]),
    ],
)
def test_expected_trace(name, trace_args):
    """Whole-trace expectations. UPDATE_TRACE_EXPECT=1 rewrites them from a live
    run; review the diff before committing."""
    expected = EXPECT_DIR / f"{name}.expected"
    actual = voblint(*ARGS, *trace_args, PROGRAM).stderr
    if os.environ.get("UPDATE_TRACE_EXPECT") == "1":
        expected.write_text(actual)
    assert actual == expected.read_text()


GOBLINT_LINE = re.compile(r"^( *)%%% (\w+): (.*)$")


def verbose_lines(*args):
    """(indent, subsystem, message) per trace line; a message's continuation
    lines start at column 0, as Goblint's printtrace writes them."""
    text = voblint(*args).stderr
    return [
        (len(m[1]), m[2], m[3])
        for m in (GOBLINT_LINE.match(line) for line in text.splitlines())
        if m
    ]


def test_verbose_is_goblint_trace_format():
    lines = verbose_lines(*ARGS, "--trace", "--verbose", PROGRAM)
    assert lines[0] == (0, "multivar", "solving for (exit_main, root)")
    assert lines[1][1:] == (
        "iter",
        "begin iterate (exit_main, root), called: true, stable: false, wpoint: false",
    )
    systems = {sys for _, sys, _ in lines}
    assert {"solver_query", "answer", "iter", "eq", "side", "destab"} <= systems


def test_verbose_indents_between_query_and_answer():
    """Entering a query indents after its line, like Goblint's tracei; the
    answer is printed at the inner level and outdents, like traceu."""
    lines = verbose_lines(
        "--analysis",
        "interval",
        "--trace",
        "--verbose",
        "docs/readme-figures/while-loop.vimp",
    )
    depth = 0
    for indent, sys, msg in lines:
        assert indent == depth, (indent, sys, msg)
        if sys == "solver_query":
            depth += 2
        elif sys == "answer":
            depth -= 2
    assert depth == 0


def test_trace_sys_selects_subsystems():
    lines = verbose_lines(*ARGS, "--trace-sys", "iter,side", PROGRAM)
    assert lines and {sys for _, sys, _ in lines} == {"iter", "side"}
    # An unselected subsystem changes no indentation, as in Goblint.
    assert {indent for indent, _, _ in lines} == {0}


def test_trace_sys_rejects_unknown_subsystem():
    assert VOBLINT.is_file(), "cli/voblint not built -- run `pixi run cli-build`"
    proc = subprocess.run(
        [str(VOBLINT), *ARGS, "--trace-sys", "sol2", PROGRAM],
        capture_output=True,
        text=True,
        cwd=REPO_ROOT,
        timeout=30,
    )
    assert proc.returncode == 1
    assert "unknown --trace-sys subsystem: sol2" in proc.stderr


def test_deterministic():
    runs = [voblint(*ARGS, "--trace", "--format", "jsonl", PROGRAM) for _ in range(2)]
    assert runs[0].stderr == runs[1].stderr


def test_header_and_steps(events):
    run = events[0]
    assert run == {
        "event": "run",
        "schema": 2,
        "analysis": ["interval"],
        "context_policy": "entry-state",
        "update_rule": "warrow",
        "program": PROGRAM,
    }
    steps = [e["step"] for e in events if "step" in e]
    assert steps == list(range(1, len(steps) + 1))
    assert events[-1]["event"] == "end"
    assert [e["verdict"] for e in events if e["event"] == "check"] == [
        "PROVED",
        "PROVED",
    ]


def test_main_reads_its_own_seed(events):
    reads = [
        e
        for e in events
        if e["event"] == "query_global" and is_seed(e["target"], "main", [])
    ]
    assert reads and reads[0]["value"] == "⊥"


@pytest.mark.parametrize("context", ["[5,5]", "[4,4]"])
def test_buffered_publication_is_read_back(events, context):
    """The call routes to its context; the callee's entry first reads its seed
    as bottom, the flushed side effect then changes the seed, and a later
    evaluation reads the published value."""
    order = [e for e in events if "step" in e]
    route = next(
        i
        for i, e in enumerate(order)
        if e["event"] == "route" and e["context"].get("values") == [context]
    )

    def seed(e):
        return is_seed(e.get("target", e.get("unknown", {})), "bump", [context])

    reads = [i for i, e in enumerate(order) if e["event"] == "query_global" and seed(e)]
    sides = [i for i, e in enumerate(order) if e["event"] == "side" and seed(e)]
    updates = [
        i for i, e in enumerate(order) if e["event"] == "update_global" and seed(e)
    ]
    assert route < reads[0] < sides[0]
    assert order[reads[0]]["value"] == "⊥"
    assert updates and sides[0] < updates[0]
    later = [i for i in reads if i > updates[0]]
    assert later and order[later[0]]["value"] != "⊥"
    # The second publication finds the seed unchanged.
    assert len(sides) >= 2 and len(updates) == 1


def test_compact_names_the_story():
    text = voblint(*ARGS, "--trace", PROGRAM).stderr
    assert text.startswith("Voblint trace\n")
    assert "reads Seed(main, root) = ⊥" in text
    assert "-> context [[5,5]]" in text
    assert "reads Seed(bump, [[5,5]]) = ⊥" in text
    assert "FLUSH    Seed(bump, [[5,5]])" in text
    assert "RESTART  (pp3, root)" in text
    assert "Trace complete:" in text


def test_generated_module_carries_trace_calls():
    """The trace calls come from the exported code equations: the solver's
    recursion, the solve, destabilization, routing and the run itself."""
    text = GENERATED.read_text()
    assert "Solver_trace_hook.emit" in text
    solver = text[text.index("let rec tD_side_rule_Interp_solve_rec_c") :]
    solver = solver[: solver.index(";;")]
    assert solver.count('Solver_trace_hook.emit "solver"') >= 15
    for channel in ('"solver"', '"route"', '"run"'):
        assert f"Solver_trace_hook.emit {channel}" in text


def test_schema2_internal_steps(events):
    """Queries nest (the replay's stack), every destabilization is followed by
    its stable removals, and each solve evaluates its right-hand side."""
    steps = [e for e in events if "step" in e]
    depth = 0
    for e in steps:
        if e["event"] == "query_local":
            depth += 1
        elif e["event"] == "value_local":
            depth -= 1
        assert depth >= 0
    assert depth == 0
    kinds = [e["event"] for e in steps]
    assert "destabilize" in kinds and "stable_remove" in kinds and "add_infl" in kinds
    assert kinds.count("eq") >= kinds.count("solve") + kinds.count("resolve")
    first = kinds.index("iterate")
    assert kinds[first + 1] == "solve"
