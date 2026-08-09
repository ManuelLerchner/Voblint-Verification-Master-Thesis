#!/usr/bin/env python3
"""Regression corpus runner for the voblint CLI, Goblint-style.

Cases live under tests/regression/<NN-topic>/<NN-name>.vimp, mirroring
https://github.com/goblint/analyzer's tests/regression/<NN-group>/ layout
(their "00-sanity" convention has a direct match here).

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

A case with no verdict annotations at all is a parse-rejection case (see
00-sanity/02-malformed.vimp) and is checked for a structured parse error
instead of a report.

Usage (mirrors Goblint's update_suite.rb selection modes):
  run.py                             run every case, in parallel
  run.py 02-control-flow             run only that group (dir basename, with
                                      or without its NN- prefix)
  run.py -02-control-flow            run everything EXCEPT that group
  run.py if_else                     run by (sub)name, like Goblint's
                                      "update_suite.rb simple_rc" -- matches
                                      a case's stem or its group/stem path
  run.py group 02-control-flow       same, "group" keyword accepted and
                                      ignored for readers used to Goblint's
                                      own phrasing
  run.py path/to/case.vimp           run a single case by path
  run.py -s ...                      sequential instead of parallel (for
                                      debugging flaky ordering)

Expected results are keyed by real source LINE NUMBER, the same way
Goblint's own harness parses its analyzer's line-tagged warnings and
matches them against the source -- not by check order within the file.
voblint's own report lines carry the check's source "line:col" (see
vimp_parser.ml's check_positions tracking, main.ml's render_text_report),
so this runner reads that back rather than re-deriving position from the
report's row order. Robust to inserting/removing an unrelated check
earlier in the file, unlike order-based matching.

Adding a case is: drop a new .vimp file under an existing (or new)
regression/<NN-topic>/ directory -- nothing else to wire up.
"""

import re
import subprocess
import sys
from concurrent.futures import ThreadPoolExecutor
from pathlib import Path

TESTS_DIR = Path(__file__).resolve().parent
REPO_ROOT = TESTS_DIR.parent
CLI_DIR = REPO_ROOT / "cli"
REGRESSION_DIR = TESTS_DIR / "regression"
VOBLINT = CLI_DIR / "voblint"

REACHABLE = "reachable"
NOWARN = "NOWARN"

PARAM_RE = re.compile(r"^// PARAM: (.*)$")
CHECK_LINE_RE = re.compile(r"__voblint_check")
VERDICT_RE = re.compile(r"//\s*(reachable|NOWARN|[A-Z]+)")
REPORT_LINE_RE = re.compile(r"^(\d+):\d+\s+\S+\s+\S+\s+(\S+)")


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


def run_voblint(args: list[str], path: Path) -> subprocess.CompletedProcess:
    return subprocess.run(
        [str(VOBLINT), *args, str(path)],
        capture_output=True,
        text=True,
    )


def group_of(path: Path) -> str:
    return path.parent.name


def check_case(path: Path) -> tuple[bool, list[str]]:
    """Runs one case and returns (passed, message_lines). Returns lines
    rather than printing directly: check_case runs concurrently across
    threads (see main()), and sys.stdout is process-global -- there is no
    thread-safe way to redirect it per-call, so the caller is responsible
    for printing each case's lines together, in discovery order."""
    lines: list[str] = []
    name = f"{group_of(path)}/{path.name}"
    args = param_args(path)
    expected = expected_verdicts(path)

    if "--dot" in args:
        result = run_voblint(args, path)
        if result.returncode == 0 and result.stdout.startswith("digraph AnalysisCFG"):
            lines.append(f"OK   {name} (DOT smoke test)")
            return True, lines
        lines.append(f"FAIL {name}: expected DOT output starting with 'digraph AnalysisCFG'")
        lines.append(f"  stdout: {result.stdout[:200]!r}")
        lines.append(f"  stderr: {result.stderr.strip()}")
        return False, lines

    if not expected:
        # No inline verdicts: this case documents a rejection, not a report.
        result = run_voblint(args, path)
        if result.returncode == 0:
            lines.append(f"FAIL {name}: expected a non-zero exit (no verdict annotations present)")
            return False, lines
        if "parse error" in result.stderr:
            lines.append(f"OK   {name} (rejected: {result.stderr.strip()})")
            return True, lines
        lines.append(f"FAIL {name}: rejected, but not with a parse error")
        lines.append(f"  stderr: {result.stderr.strip()}")
        return False, lines

    result = run_voblint(args, path)
    if result.returncode != 0:
        lines.append(f"FAIL {name}: voblint exited non-zero unexpectedly")
        lines.append(f"  stderr: {result.stderr.strip()}")
        return False, lines

    actual = actual_verdicts(result.stdout)

    ok = True
    for line_no, exp in sorted(expected.items()):
        if exp == NOWARN:
            if line_no in actual:
                lines.append(
                    f"FAIL {name}: line {line_no} expected NOWARN (suppressed), "
                    f"but got {actual[line_no]}"
                )
                ok = False
            continue
        if line_no not in actual:
            lines.append(f"FAIL {name}: line {line_no} expected {exp}, but missing from the report")
            ok = False
            continue
        # "reachable" only asserts presence (already true, since the line
        # is in the report); any verdict there satisfies it.
        if exp != REACHABLE and exp != actual[line_no]:
            lines.append(f"FAIL {name}: line {line_no} expected {exp}, got {actual[line_no]}")
            ok = False

    extra = set(actual) - set(expected)
    if extra:
        lines.append(
            f"FAIL {name}: unexpected report line(s) with no annotation: "
            f"{', '.join(str(n) for n in sorted(extra))}"
        )
        ok = False

    if ok:
        lines.append(f"OK   {name} ({len(expected)} check(s), {' '.join(args)})")
    return ok, lines


def matches_selector(path: Path, sel: str) -> bool:
    g = group_of(path)
    g_topic = g.split("-", 1)[-1]
    return sel in (g, g_topic, path.stem, f"{g}/{path.name}") or sel in str(
        path.relative_to(REGRESSION_DIR)
    )


def discover(selectors: list[str]) -> list[Path]:
    all_cases = sorted(REGRESSION_DIR.glob("*/*.vimp"))

    selectors = [s for s in selectors if s != "group"]
    file_selectors = [s for s in selectors if s.endswith(".vimp") and Path(s).exists()]
    includes = [s for s in selectors if not s.endswith(".vimp") and not s.startswith("-")]
    excludes = [s[1:] for s in selectors if s.startswith("-") and not s.endswith(".vimp")]

    if includes:
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
    subprocess.run(["make", "-C", str(CLI_DIR)], check=True, capture_output=True)

    args = sys.argv[1:]
    sequential = "-s" in args
    args = [a for a in args if a != "-s"]

    cases = discover(args)
    if not cases:
        print(f"no matching .vimp cases found under {REGRESSION_DIR} for {args}")
        return 1

    # Each case is an independent voblint subprocess (like Goblint's own
    # Parallel.map over test projects); check_case returns lines rather than
    # printing (sys.stdout is process-global, unsafe to redirect per-thread),
    # so output is replayed here in discovery order regardless of completion
    # order, keeping it deterministic and diffable.
    if sequential or len(cases) == 1:
        outcomes = [check_case(path) for path in cases]
    else:
        with ThreadPoolExecutor(max_workers=min(8, len(cases))) as pool:
            outcomes = list(pool.map(check_case, cases))

    results = []
    for ok, lines in outcomes:
        for line in lines:
            print(line)
        results.append(ok)

    if all(results):
        print("All CLI regression checks passed.")
        return 0
    print("Some CLI regression checks failed.")
    return 1


if __name__ == "__main__":
    sys.exit(main())
