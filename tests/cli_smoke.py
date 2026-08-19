#!/usr/bin/env python3
"""CLI-level smoke tests for voblint -- behavior that isn't a .vimp
fixture's verdict report at all (exit codes, --help, argument errors), the
same reason Goblint keeps a small Cram-test layer alongside its source-
annotated regression corpus (see tests/run.py's module docstring for that
corpus). Kept deliberately small: this is for CLI plumbing that a .vimp
fixture can't exercise, not a place to duplicate analysis-behavior coverage
that already lives in tests/regression/.

Each case is (description, args, expected exit code, required substring in
stdout+stderr). No fixture files, no build-your-own-framework: a flat table
is enough for this few cases, and any growth past that should probably
become its own tests/regression/<NN-group>/ instead of growing this file.
"""

import os
import subprocess
import sys

from run import REPO_ROOT, VOBLINT, bold, green, red

MISSING_FILE = "tests/regression/00-sanity/does-not-exist.vimp"
SANITY_FILE = "tests/regression/00-sanity/precision/01-straight_line_proved.vimp"

CASES = [
    ("--help exits 0 with usage", ["--help"], 0, "voblint --analysis sign|interval"),
    ("unknown --analysis value is rejected", ["--analysis", "bogus", SANITY_FILE], 1, "unknown --analysis value"),
    ("missing --analysis is rejected", [SANITY_FILE], 1, "missing --analysis"),
    ("missing FILE.vimp is rejected", ["--analysis", "sign"], 1, "missing FILE.vimp"),
    ("unrecognized argument is rejected", ["--analysis", "sign", "--bogus-flag", SANITY_FILE], 1, "unrecognized argument"),
    ("unreadable file is reported, not crashed", ["--analysis", "sign", MISSING_FILE], 1, "cannot read"),
    (
        "unknown --context-graph value is rejected",
        ["--analysis", "interval", "--context", "entry-state", "--context-graph", "nonsense", SANITY_FILE],
        1,
        "unknown --context-graph value",
    ),
    (
        "--context-graph expanded without entry-state context is rejected",
        ["--analysis", "interval", "--context-graph", "expanded", SANITY_FILE],
        1,
        "--context-graph expanded requires --context entry-state",
    ),
    (
        "--context call-string without --context-depth is rejected",
        ["--analysis", "interval", "--context", "call-string", SANITY_FILE],
        1,
        "--context call-string requires --context-depth K",
    ),
    (
        "--context-depth without --context call-string is rejected",
        ["--analysis", "interval", "--context-depth", "2", SANITY_FILE],
        1,
        "--context-depth is only valid with --context call-string",
    ),
    (
        "--context-depth with --context entry-state is rejected",
        ["--analysis", "interval", "--context", "entry-state", "--context-depth", "2", SANITY_FILE],
        1,
        "--context-depth is only valid with --context call-string",
    ),
    (
        "--context-depth 0 is rejected",
        ["--analysis", "interval", "--context", "call-string", "--context-depth", "0", SANITY_FILE],
        1,
        "unsupported --analysis/--context/--solver combination",
    ),
    (
        "sign + call-string is rejected",
        ["--analysis", "sign", "--context", "call-string", "--context-depth", "2", SANITY_FILE],
        1,
        "unsupported --analysis/--context/--solver combination",
    ),
    (
        "int + call-string is rejected",
        ["--analysis", "int", "--context", "call-string", "--context-depth", "2", SANITY_FILE],
        1,
        "unsupported --analysis/--context/--solver combination",
    ),
    (
        "explicit --solver with --context call-string is rejected",
        ["--analysis", "interval", "--context", "call-string", "--context-depth", "2", "--solver", "warrow", SANITY_FILE],
        1,
        "unsupported --analysis/--context/--solver combination",
    ),
    (
        "--dot with --context call-string is rejected",
        ["--analysis", "interval", "--context", "call-string", "--context-depth", "2", "--dot", SANITY_FILE],
        1,
        "--context call-string does not support --dot/--dot-full/--graph-snapshot yet",
    ),
]


def run(args: list[str]) -> subprocess.CompletedProcess:
    return subprocess.run([str(VOBLINT), *args], capture_output=True, text=True, cwd=REPO_ROOT, timeout=10)


def main() -> int:
    if "VOBLINT_BIN" not in os.environ:
        subprocess.run(["bash", str(REPO_ROOT / "scripts" / "mk" / "cli-build.sh")], check=True, capture_output=True)

    failed = 0
    for desc, args, expected_code, needle in CASES:
        result = run(args)
        combined = result.stdout + result.stderr
        if result.returncode != expected_code:
            failed += 1
            print(f"{red('FAIL')} {desc}: expected exit {expected_code}, got {result.returncode}")
            print(f"  stdout: {result.stdout[:200]!r}")
            print(f"  stderr: {result.stderr[:200]!r}")
            continue
        if needle not in combined:
            failed += 1
            print(f"{red('FAIL')} {desc}: expected {needle!r} in output")
            print(f"  stdout: {result.stdout[:200]!r}")
            print(f"  stderr: {result.stderr[:200]!r}")
            continue
        print(f"{green('OK')}   {desc}")

    print()
    summary = f"{len(CASES) - failed} passed" + (f", {failed} failed" if failed else "")
    print(bold(green(summary)) if not failed else bold(red(summary)))
    return 0 if not failed else 1


if __name__ == "__main__":
    sys.exit(main())
