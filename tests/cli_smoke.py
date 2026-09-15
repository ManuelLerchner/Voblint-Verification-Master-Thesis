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
    ("--help names the default HTML output", ["--help"], 0, "build/report/"),
    (
        "unknown --analysis value is rejected",
        ["--analysis", "bogus", SANITY_FILE],
        1,
        "unknown --analysis value",
    ),
    ("missing --analysis is rejected", [SANITY_FILE], 1, "missing --analysis"),
    ("missing FILE.vimp is rejected", ["--analysis", "sign"], 1, "missing FILE.vimp"),
    (
        "unrecognized argument is rejected",
        ["--analysis", "sign", "--bogus-flag", SANITY_FILE],
        1,
        "unrecognized argument",
    ),
    (
        "unreadable file is reported, not crashed",
        ["--analysis", "sign", MISSING_FILE],
        1,
        "cannot read",
    ),
    (
        # --context-graph was removed with the collapsed rendering it selected;
        # graphs are always contextual, so the spelling is now just unknown.
        "retired --context-graph is rejected as unrecognized",
        [
            "--analysis",
            "interval",
            "--context",
            "entry-state",
            "--context-graph",
            "expanded",
            SANITY_FILE,
        ],
        1,
        "unrecognized argument",
    ),
    (
        "--context call-string without --context-depth is rejected",
        ["--analysis", "interval", "--context", "call-string", SANITY_FILE],
        1,
        "--context call-string requires --context-depth K",
    ),
    (
        "entry-state with sign runs",
        [
            "--analysis",
            "sign",
            "--context",
            "entry-state",
            "--graph-snapshot",
            SANITY_FILE,
        ],
        0,
        "",
    ),
    (
        "several domains without --html is rejected",
        ["--analysis", "int,interval", SANITY_FILE],
        1,
        "only supported by --html",
    ),
    (
        # Node identifiers are built from the CFG and the context, so they only
        # agree across domains when the context is the same for all of them.
        "several domains with a context is rejected",
        [
            "--analysis",
            "int,interval",
            "--context",
            "entry-state",
            "--html",
            SANITY_FILE,
        ],
        1,
        "requires --context none",
    ),
    (
        "an unknown domain inside a list is rejected",
        ["--analysis", "int,bogus", "--html", SANITY_FILE],
        1,
        "unknown --analysis value: bogus",
    ),
    (
        "--html-out without a directory is rejected",
        ["--analysis", "sign", "--html-out"],
        1,
        "--html-out expects a directory",
    ),
    (
        # --html takes no argument, so the program is still read as the
        # positional rather than mistaken for an output directory.
        "--html after FILE.vimp still finds the file",
        [
            "--analysis",
            "sign",
            SANITY_FILE,
            "--html-out",
            "/tmp/voblint-smoke-html",
            "--html",
        ],
        0,
        "node(s)",
    ),
    (
        # --html writes a directory, the other renderings write one document to
        # stdout; asking for both is a contradiction about where output goes.
        "--html combined with --dot is rejected",
        ["--analysis", "sign", "--html", "--dot", SANITY_FILE],
        1,
        "--html cannot be combined with",
    ),
    (
        "--html with an explicit --globals is accepted",
        [
            "--analysis",
            "interval",
            "--globals",
            "warrow",
            "--html-out",
            "/tmp/voblint-smoke-solver",
            SANITY_FILE,
        ],
        0,
        "node(s)",
    ),
    (
        "--context-depth without --context call-string is rejected",
        ["--analysis", "interval", "--context-depth", "2", SANITY_FILE],
        1,
        "--context-depth is only valid with --context call-string",
    ),
    (
        "--context-depth with --context entry-state is rejected",
        [
            "--analysis",
            "interval",
            "--context",
            "entry-state",
            "--context-depth",
            "2",
            SANITY_FILE,
        ],
        1,
        "--context-depth is only valid with --context call-string",
    ),
    (
        # A call string that keeps no call site is one shared context per callee.
        "--context-depth 0 is accepted",
        [
            "--analysis",
            "interval",
            "--context",
            "call-string",
            "--context-depth",
            "0",
            SANITY_FILE,
        ],
        0,
        "",
    ),
    (
        "negative --context-depth is rejected",
        [
            "--analysis",
            "interval",
            "--context",
            "call-string",
            "--context-depth",
            "-1",
            SANITY_FILE,
        ],
        1,
        "--context-depth must not be negative",
    ),
    (
        "unknown --globals value is rejected",
        ["--analysis", "sign", "--globals", "bogus", SANITY_FILE],
        1,
        "unknown --globals value",
    ),
    (
        "retired --solver is rejected as unrecognized",
        ["--analysis", "sign", "--solver", "join", SANITY_FILE],
        1,
        "unrecognized argument",
    ),
    (
        "sign + call-string is accepted",
        [
            "--analysis",
            "sign",
            "--context",
            "call-string",
            "--context-depth",
            "2",
            SANITY_FILE,
        ],
        0,
        "",
    ),
    (
        "int + call-string is accepted",
        [
            "--analysis",
            "int",
            "--context",
            "call-string",
            "--context-depth",
            "2",
            SANITY_FILE,
        ],
        0,
        "",
    ),
    (
        "explicit --globals warrow with --context call-string is accepted",
        [
            "--analysis",
            "interval",
            "--context",
            "call-string",
            "--context-depth",
            "2",
            "--globals",
            "warrow",
            SANITY_FILE,
        ],
        0,
        "",
    ),
    (
        "explicit --globals join with --context call-string is accepted",
        [
            "--analysis",
            "interval",
            "--context",
            "call-string",
            "--context-depth",
            "2",
            "--globals",
            "join",
            SANITY_FILE,
        ],
        0,
        "",
    ),
    (
        "explicit --globals per-origin with --context entry-state is accepted",
        [
            "--analysis",
            "interval",
            "--context",
            "entry-state",
            "--globals",
            "per-origin",
            SANITY_FILE,
        ],
        0,
        "",
    ),
    (
        "sign + explicit --globals join with --context call-string is accepted",
        [
            "--analysis",
            "sign",
            "--context",
            "call-string",
            "--context-depth",
            "2",
            "--globals",
            "join",
            SANITY_FILE,
        ],
        0,
        "",
    ),
    (
        "sign + explicit --globals warrow-per-origin with --context call-string is accepted",
        [
            "--analysis",
            "sign",
            "--context",
            "call-string",
            "--context-depth",
            "2",
            "--globals",
            "warrow-per-origin",
            SANITY_FILE,
        ],
        0,
        "",
    ),
    (
        "sign + --globals warrow is accepted",
        ["--analysis", "sign", "--globals", "warrow", SANITY_FILE],
        0,
        "",
    ),
    (
        "sign + --globals join is accepted",
        ["--analysis", "sign", "--globals", "join", SANITY_FILE],
        0,
        "",
    ),
    (
        "parity is a recognized --analysis value",
        ["--analysis", "parity", SANITY_FILE],
        0,
        "",
    ),
    (
        "parity + explicit --globals per-origin is accepted",
        ["--analysis", "parity", "--globals", "per-origin", SANITY_FILE],
        0,
        "",
    ),
    (
        "parity + --globals warrow is accepted",
        ["--analysis", "parity", "--globals", "warrow", SANITY_FILE],
        0,
        "",
    ),
    (
        "parity + entry-state is accepted",
        ["--analysis", "parity", "--context", "entry-state", SANITY_FILE],
        0,
        "",
    ),
    (
        "parity + call-string is accepted",
        [
            "--analysis",
            "parity",
            "--context",
            "call-string",
            "--context-depth",
            "2",
            SANITY_FILE,
        ],
        0,
        "",
    ),
    (
        "sign + entry-state + --dot renders sign, not interval",
        ["--analysis", "sign", "--context", "entry-state", "--dot", SANITY_FILE],
        0,
        "digraph",
    ),
    (
        "--dot with --context call-string is accepted",
        [
            "--analysis",
            "interval",
            "--context",
            "call-string",
            "--context-depth",
            "2",
            "--dot",
            SANITY_FILE,
        ],
        0,
        "digraph",
    ),
    (
        "--graph-snapshot with --context call-string is accepted",
        [
            "--analysis",
            "interval",
            "--context",
            "call-string",
            "--context-depth",
            "2",
            "--graph-snapshot",
            SANITY_FILE,
        ],
        0,
        "clusters:",
    ),
    (
        "sign --dot with --context call-string is accepted",
        [
            "--analysis",
            "sign",
            "--context",
            "call-string",
            "--context-depth",
            "2",
            "--dot",
            SANITY_FILE,
        ],
        0,
        "digraph",
    ),
]


def run(args: list[str]) -> subprocess.CompletedProcess:
    return subprocess.run(
        [str(VOBLINT), *args], capture_output=True, text=True, cwd=REPO_ROOT, timeout=10
    )


def main() -> int:
    if "VOBLINT_BIN" not in os.environ:
        subprocess.run(
            ["bash", str(REPO_ROOT / "scripts" / "mk" / "cli-build.sh")], check=True
        )

    failed = 0
    for desc, args, expected_code, needle in CASES:
        result = run(args)
        combined = result.stdout + result.stderr
        if result.returncode != expected_code:
            failed += 1
            print(
                f"{red('FAIL')} {desc}: expected exit {expected_code}, got {result.returncode}"
            )
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
