#!/usr/bin/env python3
"""Regression corpus runner for the voblint CLI.

Cases live under tests/regression/<NN-group>/<name>.vimp, mirroring
https://github.com/goblint/analyzer's tests/regression/<NN-group>/ layout
(their "00-sanity" convention has a direct match here). <NN-group> answers
"what part of the analyzer does this exercise" (globals, widening, the
parser, ...); a case whose result carries a precision guarantee additionally
sits under one of two subdirectories that answer "what kind of guarantee":

  <NN-group>/precision/           exact result is part of the contract.
                                   PROVED/REFUTED are the expected outcomes;
                                   UNKNOWN here generally means a regression,
                                   not a feature.
  <NN-group>/soundness/           the concrete program's result is genuinely
                                   undetermined (e.g. an unconstrained
                                   __voblint_nondet_int() feeds the checked
                                   condition):
                                   both a satisfying and a violating
                                   execution exist, so UNKNOWN is the only
                                   sound answer -- not a limitation to name,
                                   since there is no mechanism losing
                                   information here.
  <NN-group>/known-imprecision/   the concrete result IS fixed, but the
                                   abstraction can't establish it. Every
                                   case's header comment must name the
                                   concrete mechanism -- which component
                                   loses the information and why -- not just
                                   assert that a limitation exists. A
                                   golden-output UNKNOWN with no mechanism
                                   explained is how a real precision bug
                                   (see git history around issue #99) gets
                                   silently locked in as "expected".

A group with no precision claim at all (09-parser, 08-tooling) keeps its
cases directly under <NN-group>/, no subdirectory.

Each case carries its own invocation flags on line 1
("// PARAM: <voblint args>", mirroring Goblint's "// SKIP PARAM: --set ...")
and its own expected verdict inline next to each check:

  // PROVED / REFUTED / UNKNOWN   verdict precision, mirrors Goblint's
                                   bare/FAIL/UNKNOWN!
  // reachable                    accepts any verdict; asserts only that the
                                   check node is present in the report at
                                   all -- a CFG completeness property (the
                                   compiler must never silently drop a
                                   reachable check). Mirrors Goblint's
                                   "__goblint_check(1); // reachable".
  // NOWARN                       asserts the check is ABSENT from the
                                   report entirely. Mirrors Goblint's
                                   "__goblint_check(0); // NOWARN
                                   (unreachable)": voblint detects an
                                   unreachable program point by probing
                                   every in-scope variable's is_bot
                                   (sound_domain class method, exact for
                                   non-relational domains -- see
                                   program_vars/is_bottom_abstract_value in
                                   Example_State_Report_GraphViz.thy) and
                                   suppresses that report entry, so a NOWARN
                                   check contributes zero lines of output,
                                   not a vacuous PROVED.

A case with no verdict annotations at all is a rejection case -- a parse
error (see 00-sanity/02-malformed.vimp), a well-formedness error (e.g. a
wrong-arity special call, rejected before compilation reaches the analyzer),
or a solver that does not terminate on this program's fixpoint dependency
structure (see 15-solver-choice/04-global_self_feedback_join_hangs.vimp,
using --timeout to keep the case fast) -- and is checked for one of those
structured error messages instead of a report.

A case may also carry a canonical CFG snapshot, checked independently of its
verdicts:

  // EXPECT-GRAPH-BEGIN / -END   delimits a `voblint --graph-snapshot`
                                  capture, one output line per "// "-prefixed
                                  source line (see Analysis_GraphViz.thy's
                                  contextual_analysis_canonical_text -- a
                                  DOT-independent, cluster/node/edge textual
                                  rendering of the same solved CFG a --dot
                                  case renders as GraphViz). No block: the
                                  case's graph is not checked. Block present
                                  but stale: FAIL with a diff-able mismatch.
                                  --dot cases (see 08-tooling/01-dot_smoke
                                  .vimp) are DOT renderer-styling
                                  regressions and are exempt: they already
                                  assert their own shape and don't also
                                  carry this block.

Usage (selectors match any path component -- group, precision/
known-imprecision, or file stem -- so a whole group and one precision
subdirectory within it are both one word):
  run.py                              run every case, in parallel
  run.py 02-control-flow              run only that group
  run.py 12-widening/known-imprecision  run only that group's imprecision cases
  run.py known-imprecision            run every known-imprecision case,
                                       across every group
  run.py -known-imprecision           run everything EXCEPT those
  run.py if_else                      run by (sub)name -- matches a case's
                                       stem or any path component
  run.py path/to/case.vimp            run a single case by path
  run.py -s ...                      sequential instead of parallel (for
                                      debugging flaky ordering)
  run.py ... --update-graphs         (re)generate every selected case's
                                      EXPECT-GRAPH block from a live
                                      --graph-snapshot run instead of
                                      checking it; creates the block if the
                                      case doesn't have one yet
  run.py --lint [selectors]          static checks over fixture source, no
                                      CLI build or voblint invocation: every
                                      check has a recognized verdict, every
                                      known-imprecision/ case has a header
                                      comment and an UNKNOWN/NOWARN verdict,
                                      EXPECT-GRAPH blocks are balanced,
                                      filenames follow the NN-name.vimp shape
  run.py --list / --dry-run [sel...] print the reproduction command for
                                      every selected case, run nothing
  run.py ... --slowest N             after running, print the N slowest
                                      cases by wall-clock duration

Each case runs under a DEFAULT_TIMEOUT-second ceiling (subprocess.run's
timeout); a hang -- solver divergence, not slowness -- is reported as
TIMEOUT rather than hanging the whole suite.

Expected results are keyed by real source LINE NUMBER, the same way
Goblint's own harness parses its analyzer's line-tagged warnings and
matches them against the source -- not by check order within the file.
voblint's own report lines carry the check's source "line:col" (see
vimp_parser.ml's check_positions tracking, main.ml's render_text_report),
so this runner reads that back rather than re-deriving position from the
report's row order. Robust to inserting/removing an unrelated check
earlier in the file, unlike order-based matching.

Adding a case is: drop a new .vimp file under an existing (or new)
regression/<NN-group>/ directory, in a precision/, soundness/, or
known-imprecision/ subdirectory if it makes a precision claim -- discovery
is recursive, nothing else to wire up. Pick the subdirectory by what the
CONCRETE program does, not by what the analyzer currently reports:
precision/ only if the concrete result is fixed and PROVED/REFUTED is
actually what the analysis should produce; soundness/ if the concrete
result is genuinely undetermined (unconstrained input reaches the checked
condition), where UNKNOWN is the only sound answer and not a limitation;
known-imprecision/ if the concrete result IS fixed but the domain can't
express it, with a comment naming why.
"""

import os
import re
import subprocess
import sys
import time
from concurrent.futures import ThreadPoolExecutor
from pathlib import Path

# Colorize only when stdout is a real terminal and the user hasn't opted out
# (NO_COLOR, https://no-color.org) -- piped/redirected output (CI logs, a
# diff-review tool) stays plain ANSI-free text either way.
COLOR = sys.stdout.isatty() and "NO_COLOR" not in os.environ

# Piped stdout (a pixi task, `| tee`, CI) is block-buffered by default, so
# per-case results would sit in the buffer instead of streaming as each case
# finishes -- line-buffer unconditionally so progress is visible live, not
# just flushed in one lump when the process exits.
sys.stdout.reconfigure(line_buffering=True)


def _sgr(code: str, text: str) -> str:
    return f"\033[{code}m{text}\033[0m" if COLOR else text


def green(text: str) -> str:
    return _sgr("32", text)


def red(text: str) -> str:
    return _sgr("31", text)


def dim(text: str) -> str:
    return _sgr("2", text)


def bold(text: str) -> str:
    return _sgr("1", text)


TESTS_DIR = Path(__file__).resolve().parent
REPO_ROOT = TESTS_DIR.parent
CLI_DIR = REPO_ROOT / "cli"
REGRESSION_DIR = TESTS_DIR / "regression"
# VOBLINT_BIN lets an alternate binary (e.g. the generated-Menhir prototype's
# voblint2, tests/menhir_prototype/voblint2) run against this corpus and its
# verdict-matching logic without duplicating it -- see
# tests/menhir_prototype/ for why: it has no --dot/--parse-only support, so
# main()'s cli-build step is skipped when this is set.
VOBLINT = Path(os.environ["VOBLINT_BIN"]) if "VOBLINT_BIN" in os.environ else CLI_DIR / "voblint"

REACHABLE = "reachable"
NOWARN = "NOWARN"
KNOWN_VERDICTS = {"PROVED", "REFUTED", "UNKNOWN", NOWARN, REACHABLE}

# A generous ceiling, not a performance budget: this exists to turn a solver
# divergence (the exact failure mode 12-widening/ documents a past instance
# of) into a reported TIMEOUT instead of a hung suite, not to catch slow
# cases -- see --slowest for that.
DEFAULT_TIMEOUT = 30

PARAM_RE = re.compile(r"^// PARAM: (.*)$")
CHECK_LINE_RE = re.compile(r"__voblint_check")
VERDICT_RE = re.compile(r"//\s*(reachable|NOWARN|[A-Z]+)")
REPORT_LINE_RE = re.compile(r"^(\d+):\d+\s+\S+\s+\S+\s+(\S+)")

GRAPH_BEGIN = "// EXPECT-GRAPH-BEGIN"
GRAPH_END = "// EXPECT-GRAPH-END"

# Set from main()'s --update-graphs before the (possibly threaded) case run;
# read-only from then on, so concurrent check_case calls sharing it is safe.
UPDATE_GRAPHS = False


def param_args(path: Path) -> list[str]:
    first_line = path.read_text().splitlines()[0]
    m = PARAM_RE.match(first_line)
    return m.group(1).split() if m else []


def expected_verdicts(path: Path) -> dict[int, str]:
    """Maps source line number -> expected verdict, for every line
    containing __voblint_check with a trailing verdict comment."""
    verdicts = {}
    for line_no, line in enumerate(path.read_text().splitlines(), start=1):
        if CHECK_LINE_RE.search(line):
            m = VERDICT_RE.search(line)
            if m:
                verdicts[line_no] = m.group(1)
    return verdicts


def actual_verdicts(stdout: str) -> dict[int, str]:
    """Maps source line number -> actual verdict, parsed from voblint's
    "line:col  node  condition  VERDICT  state" report rows."""
    verdicts = {}
    for line in stdout.splitlines():
        m = REPORT_LINE_RE.match(line)
        if m:
            verdicts[int(m.group(1))] = m.group(2)
    return verdicts


def find_graph_block(lines: list[str]) -> tuple[int, int] | None:
    """Returns (begin, end) line indices of an existing EXPECT-GRAPH block,
    or None if the fixture doesn't have one."""
    begin = None
    for i, line in enumerate(lines):
        if line.rstrip() == GRAPH_BEGIN:
            begin = i
        elif line.rstrip() == GRAPH_END and begin is not None:
            return begin, i
    return None


def strip_comment_prefix(line: str) -> str:
    assert line.startswith("//"), f"EXPECT-GRAPH body line missing '//': {line!r}"
    rest = line[2:]
    return rest[1:] if rest.startswith(" ") else rest


def add_comment_prefix(line: str) -> str:
    return f"// {line}" if line else "//"


def expected_graph(lines: list[str], block: tuple[int, int]) -> str:
    begin, end = block
    return "\n".join(strip_comment_prefix(l) for l in lines[begin + 1 : end])


def graph_snapshot_args(args: list[str]) -> list[str]:
    """--dot and --graph-snapshot both select voblint's output mode -- swap
    rather than stack, keeping everything else (notably --analysis) as-is."""
    out = [a for a in args if a != "--dot" and a != "--graph-snapshot"]
    out.append("--graph-snapshot")
    return out


def run_graph_snapshot(args: list[str], path: Path) -> str:
    return run_voblint(graph_snapshot_args(args), path).stdout


def update_graph_block(path: Path, lines: list[str], block: tuple[int, int] | None, snapshot: str) -> None:
    """Replaces an existing EXPECT-GRAPH block in place, or inserts a new one
    right after the fixture's leading "//" header (PARAM line plus any
    description comments), before the first line of actual VIMP source."""
    new_block = [GRAPH_BEGIN, *(add_comment_prefix(l) for l in snapshot.splitlines()), GRAPH_END]
    if block is not None:
        begin, end = block
        lines[begin : end + 1] = new_block
    else:
        insert_at = 0
        while insert_at < len(lines) and lines[insert_at].startswith("//"):
            insert_at += 1
        lines[insert_at:insert_at] = [*new_block, ""]
    path.write_text("\n".join(lines) + "\n")


def run_voblint(args: list[str], path: Path) -> subprocess.CompletedProcess:
    return subprocess.run(
        [str(VOBLINT), *args, str(path)],
        capture_output=True,
        text=True,
        timeout=DEFAULT_TIMEOUT,
    )


def voblint_cmd(args: list[str], path: Path) -> str:
    """The `pixi run voblint ...` invocation that reproduces one check --
    used as the case label in every report line so a failure (or any case
    of interest) can be copy-pasted straight into a shell, repo-root-
    relative path and all, instead of hand-assembling it from a bare
    fixture name."""
    rel = path.relative_to(REPO_ROOT)
    return f"pixi run voblint {' '.join(args)} {rel}".strip()


def render_line(line: str) -> str:
    """Colorizes one of check_case's output lines for a terminal: the
    OK/FAIL verdict word, and detail lines (the indented "  expected: ...",
    "  stderr: ..." that follow a FAIL) dimmed so the verdict itself stays
    the eye's first stop."""
    if line.startswith("OK   "):
        return f"{green('OK')}   {line[5:]}"
    if line.startswith("FAIL "):
        return f"{red('FAIL')} {line[5:]}"
    return dim(line)


def check_graph_block(path: Path, args: list[str]) -> tuple[bool, list[str]]:
    """Checks (or, under --update-graphs, regenerates) path's EXPECT-GRAPH
    block, if it has one, against a live --graph-snapshot run under args.
    Shared by both check_case's report-based cases and its --dot/--dot-full
    smoke cases: graph_snapshot_args preserves --dot-full unchanged (it only
    strips --dot/--graph-snapshot), so a --dot-full fixture's block is
    checked against full_state_graph_snapshot_auto and a plain fixture's
    against state_report_graph_snapshot_auto -- entirely decided by args,
    with no separate marker convention needed."""
    lines: list[str] = []
    fixture_lines = path.read_text().splitlines()
    graph_block = find_graph_block(fixture_lines)
    graph_cmd = voblint_cmd(graph_snapshot_args(args), path)
    if UPDATE_GRAPHS:
        update_graph_block(path, fixture_lines, graph_block, run_graph_snapshot(args, path))
        lines.append(f"OK   {graph_cmd}: EXPECT-GRAPH block {'updated' if graph_block else 'created'}")
        return True, lines
    if graph_block is None:
        return True, lines
    snapshot = run_graph_snapshot(args, path).rstrip("\n")
    expected_snapshot = expected_graph(fixture_lines, graph_block)
    if snapshot == expected_snapshot:
        lines.append(f"OK   {graph_cmd}: graph snapshot matches")
        return True, lines
    lines.append(f"FAIL {graph_cmd}: graph snapshot mismatch (rerun with --update-graphs to refresh)")
    lines.append(f"  expected: {expected_snapshot!r}")
    lines.append(f"  actual:   {snapshot!r}")
    return False, lines


def check_case(path: Path) -> tuple[bool, list[str], float]:
    """Runs one case and returns (passed, message_lines, duration_seconds).
    Returns lines rather than printing directly: check_case runs
    concurrently across threads (see main()), and sys.stdout is
    process-global -- there is no thread-safe way to redirect it per-call,
    so the caller is responsible for printing each case's lines together,
    in discovery order."""
    args = param_args(path)
    cmd = voblint_cmd(args, path)
    start = time.monotonic()
    try:
        ok, lines = _check_case_body(path, args, cmd)
    except subprocess.TimeoutExpired:
        ok, lines = False, [f"TIMEOUT {cmd} after {DEFAULT_TIMEOUT}s"]
    return ok, lines, time.monotonic() - start


def _check_case_body(path: Path, args: list[str], cmd: str) -> tuple[bool, list[str]]:
    lines: list[str] = []
    expected = expected_verdicts(path)

    if "--dot" in args or "--dot-full" in args:
        result = run_voblint(args, path)
        if result.returncode != 0 or not result.stdout.startswith("digraph AnalysisCFG"):
            lines.append(f"FAIL {cmd}: expected DOT output starting with 'digraph AnalysisCFG'")
            lines.append(f"  stdout: {result.stdout[:200]!r}")
            lines.append(f"  stderr: {result.stderr.strip()}")
            return False, lines
        graph_ok, graph_lines = check_graph_block(path, args)
        lines.extend(graph_lines)
        if graph_ok:
            lines.append(f"OK   {cmd} (DOT smoke test)")
        return graph_ok, lines

    if not expected:
        # No inline verdicts: this case documents a rejection, not a report.
        result = run_voblint(args, path)
        if result.returncode == 0:
            lines.append(f"FAIL {cmd}: expected a non-zero exit (no verdict annotations present)")
            return False, lines
        if (
            "parse error" in result.stderr
            or "not well-formed" in result.stderr
            or "did not finish within" in result.stderr
        ):
            lines.append(f"OK   {cmd} (rejected: {result.stderr.strip()})")
            return True, lines
        lines.append(
            f"FAIL {cmd}: rejected, but not with a parse error, well-formedness error, "
            "or solver timeout"
        )
        lines.append(f"  stderr: {result.stderr.strip()}")
        return False, lines

    result = run_voblint(args, path)
    if result.returncode != 0:
        lines.append(f"FAIL {cmd}: voblint exited non-zero unexpectedly")
        lines.append(f"  stderr: {result.stderr.strip()}")
        return False, lines

    actual = actual_verdicts(result.stdout)

    ok = True
    for line_no, exp in sorted(expected.items()):
        if exp == NOWARN:
            if line_no in actual:
                lines.append(
                    f"FAIL {cmd}: line {line_no} expected NOWARN (suppressed), "
                    f"but got {actual[line_no]}"
                )
                ok = False
            continue
        if line_no not in actual:
            lines.append(f"FAIL {cmd}: line {line_no} expected {exp}, but missing from the report")
            ok = False
            continue
        # "reachable" only asserts presence (already true, since the line
        # is in the report); any verdict there satisfies it.
        if exp != REACHABLE and exp != actual[line_no]:
            lines.append(f"FAIL {cmd}: line {line_no} expected {exp}, got {actual[line_no]}")
            ok = False

    extra = set(actual) - set(expected)
    if extra:
        lines.append(
            f"FAIL {cmd}: unexpected report line(s) with no annotation: "
            f"{', '.join(str(n) for n in sorted(extra))}"
        )
        ok = False

    graph_ok, graph_lines = check_graph_block(path, args)
    lines.extend(graph_lines)
    ok = ok and graph_ok

    if ok:
        lines.append(f"OK   {cmd} ({len(expected)} check(s))")
    return ok, lines


def lint_case(path: Path) -> list[str]:
    """Static checks over one fixture's source text -- no voblint
    invocation, so --lint runs without a CLI build. Mechanically enforces
    the conventions this module's docstring and AGENTS.md's "Regression
    discipline" section otherwise only state in prose: every check carries
    a recognized verdict, every known-imprecision/ case documents why, every
    soundness/ case asserts only UNKNOWN, and EXPECT-GRAPH blocks are
    balanced."""
    problems: list[str] = []
    src_lines = path.read_text().splitlines()
    args = param_args(path)
    expected = expected_verdicts(path)

    if not src_lines or not PARAM_RE.match(src_lines[0]):
        problems.append("missing or malformed '// PARAM: ...' header on line 1")

    if not re.match(r"^\d\d-[a-z0-9_]+$", path.stem):
        problems.append(f"filename '{path.name}' doesn't follow the NN-name.vimp convention")

    # A case with no verdicts at all is a parse-rejection fixture (checked
    # for a structured error, not a report -- see check_case), and a --dot/
    # --dot-full case checks DOT shape, not verdicts: neither kind's
    # __voblint_check lines are meant to carry one.
    if expected and "--dot" not in args and "--dot-full" not in args:
        for line_no, line in enumerate(src_lines, start=1):
            if not CHECK_LINE_RE.search(line):
                continue
            m = VERDICT_RE.search(line)
            if m is None:
                problems.append(f"line {line_no}: __voblint_check with no verdict annotation")
            elif m.group(1) not in KNOWN_VERDICTS:
                problems.append(f"line {line_no}: unrecognized verdict '{m.group(1)}'")

    parts = path.relative_to(REGRESSION_DIR).parts[:-1]
    header = []
    for line in src_lines[1:]:
        if not line.startswith("//"):
            break
        header.append(line)

    if "known-imprecision" in parts:
        if len(header) < 1:
            problems.append(
                "known-imprecision case has no header comment explaining "
                "why the result is imprecise"
            )
        if not (set(expected.values()) & {"UNKNOWN", NOWARN}):
            problems.append(
                "known-imprecision case asserts no UNKNOWN/NOWARN -- "
                "does it belong in precision/ instead?"
            )

    if "soundness" in parts:
        if len(header) < 1:
            problems.append(
                "soundness case has no header comment naming what's "
                "unconstrained (e.g. an unbounded __voblint_nondet_int())"
            )
        if set(expected.values()) - {"UNKNOWN"}:
            problems.append(
                "soundness case asserts a verdict other than UNKNOWN -- "
                "if the concrete result is actually fixed, this belongs in "
                "precision/ or known-imprecision/ instead"
            )

    begins = sum(1 for line in src_lines if line.rstrip() == GRAPH_BEGIN)
    ends = sum(1 for line in src_lines if line.rstrip() == GRAPH_END)
    if begins != ends:
        problems.append(f"EXPECT-GRAPH block imbalance: {begins} BEGIN vs {ends} END")

    return problems


def matches_selector(path: Path, sel: str) -> bool:
    """A selector matches a case by its stem, by any path component (the
    NN-group, or a precision/known-imprecision subdirectory), or as a
    substring of its group/subdirectory/name path -- so "02-control-flow",
    "known-imprecision", "12-widening/known-imprecision", and "if_else" are
    all one-word selections without needing a fixed nesting depth."""
    rel = path.relative_to(REGRESSION_DIR)
    return sel == path.stem or sel in rel.parts[:-1] or sel in str(rel)


def discover(selectors: list[str]) -> list[Path]:
    all_cases = sorted(REGRESSION_DIR.rglob("*.vimp"))

    file_selectors = [s for s in selectors if s.endswith(".vimp") and Path(s).exists()]
    includes = [s for s in selectors if not s.endswith(".vimp") and not s.startswith("-")]
    excludes = [s[1:] for s in selectors if s.startswith("-") and not s.endswith(".vimp")]

    if includes or file_selectors:
        cases = [p for p in all_cases if any(matches_selector(p, sel) for sel in includes)]
    else:
        cases = list(all_cases)
    if excludes:
        cases = [p for p in cases if not any(matches_selector(p, sel) for sel in excludes)]
    cases += [Path(sel).resolve() for sel in file_selectors]

    seen = set()
    ordered = []
    for p in cases:
        if p not in seen:
            seen.add(p)
            ordered.append(p)
    return ordered


def main() -> int:
    args = sys.argv[1:]

    if "--lint" in args:
        selectors = [a for a in args if a != "--lint"]
        cases = discover(selectors)
        if not cases:
            print(f"no matching .vimp cases found under {REGRESSION_DIR} for {selectors}")
            return 1
        any_problems = False
        for path in cases:
            problems = lint_case(path)
            if problems:
                any_problems = True
                print(bold(red(str(path.relative_to(REGRESSION_DIR)))))
                for problem in problems:
                    print(f"  {problem}")
        if any_problems:
            return 1
        print(bold(green(f"{len(cases)} fixture(s), no lint issues")))
        return 0

    if "--list" in args or "--dry-run" in args:
        selectors = [a for a in args if a not in ("--list", "--dry-run")]
        cases = discover(selectors)
        for path in cases:
            print(voblint_cmd(param_args(path), path))
        return 0

    if "VOBLINT_BIN" not in os.environ:
        subprocess.run(
            ["bash", str(REPO_ROOT / "scripts" / "mk" / "cli-build.sh")],
            check=True,
            capture_output=True,
        )

    sequential = "-s" in args
    global UPDATE_GRAPHS
    UPDATE_GRAPHS = "--update-graphs" in args
    slowest_n = 0
    if "--slowest" in args:
        i = args.index("--slowest")
        slowest_n = int(args[i + 1])
        args = args[:i] + args[i + 2 :]
    args = [a for a in args if a not in ("-s", "--update-graphs")]
    # Regenerating a stale snapshot is inherently sequential per file (each
    # rewrites its own fixture on disk); nothing here prevents different
    # fixtures running concurrently, but forcing -s keeps output order sane.
    sequential = sequential or UPDATE_GRAPHS

    cases = discover(args)
    if not cases:
        print(f"no matching .vimp cases found under {REGRESSION_DIR} for {args}")
        return 1

    start = time.monotonic()
    # Each case is an independent voblint subprocess (like Goblint's own
    # Parallel.map over test projects); check_case returns lines rather than
    # printing (sys.stdout is process-global, unsafe to redirect per-thread).
    # pool.map's iterator yields results in submission (= discovery) order as
    # soon as each one is ready, blocking only on the next-in-order case --
    # not on every case -- so printing straight from that iterator streams
    # output live while keeping it deterministic and diffable. All cases
    # still start running immediately (ThreadPoolExecutor submits eagerly);
    # only the *printing* follows discovery order.
    if sequential or len(cases) == 1:
        outcome_iter = (check_case(path) for path in cases)
        pool_cm = None
    else:
        pool_cm = ThreadPoolExecutor(max_workers=min(8, len(cases)))
        outcome_iter = pool_cm.map(check_case, cases)

    outcomes = []
    results = []
    group = None
    try:
        for path, (ok, lines, duration) in zip(cases, outcome_iter):
            outcomes.append((ok, lines, duration))
            # cases is path-sorted, so its NN-group (the first path component
            # under REGRESSION_DIR) only changes at a group boundary -- a cheap
            # way to print one header per group without a second grouping pass.
            case_group = path.relative_to(REGRESSION_DIR).parts[0]
            if case_group != group:
                if group is not None:
                    print()
                print(bold(f"── {case_group} ──"))
                group = case_group
            # Duration goes on the case's last line (its summary line, e.g.
            # "OK ... (N check(s))" or the terminal FAIL) -- earlier lines from
            # the same case are intermediate detail (a graph-snapshot result,
            # a DOT check), not separate wall-clock measurements.
            for line in lines[:-1]:
                print(render_line(line))
            if lines:
                print(render_line(lines[-1]) + dim(f"  {duration:.2f}s"))
            results.append(ok)
    finally:
        if pool_cm is not None:
            pool_cm.shutdown()
    elapsed = time.monotonic() - start

    passed = sum(results)
    failed = len(results) - passed
    summary = f"{passed} passed" + (f", {failed} failed" if failed else "")
    summary += f" in {elapsed:.2f}s"

    if slowest_n:
        print()
        print(bold(f"slowest {min(slowest_n, len(outcomes))}:"))
        by_duration = sorted(zip(cases, outcomes), key=lambda co: co[1][2], reverse=True)
        for path, (_, _, duration) in by_duration[:slowest_n]:
            print(f"  {duration:6.2f}s  {path.relative_to(REGRESSION_DIR)}")

    print()
    print(bold(green(summary)) if not failed else bold(red(summary)))
    return 0 if not failed else 1


if __name__ == "__main__":
    sys.exit(main())
