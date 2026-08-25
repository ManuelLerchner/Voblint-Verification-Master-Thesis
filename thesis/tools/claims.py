#!/usr/bin/env python3
"""Keep thesis figures honest about what the analyzer actually prints.

A thesis that quotes tool output has two copies of the same fact: the one in
the chapter and the one the tool produces. They agree on the day the sentence
is written and drift silently afterwards. This removes the second copy: the
chapter includes a generated file, and CI re-runs the command to check that
file is still what the CLI prints.

The mechanism is the one this repository already uses for the two grammar
generators -- generate, then fail if the working tree is dirty -- so a claim
that has gone stale shows up as a diff on the file that carries it, with the
`why` line naming the sentence that is now wrong.

    thesis/tools/claims.py --write    regenerate thesis/shared/generated/
    thesis/tools/claims.py --check    re-run and diff; non-zero on drift
    thesis/tools/claims.py --list     show declared claims

The thesis reads a generated file by name:

    #listing(read("/shared/generated/<name>.txt"))
"""

from __future__ import annotations

import argparse
import difflib
import subprocess
import sys
import tomllib
from pathlib import Path

THESIS = Path(__file__).resolve().parent.parent
REPO = THESIS.parent
MANIFEST = THESIS / "shared" / "claims.toml"
OUTDIR = THESIS / "shared" / "generated"
CLI = REPO / "cli" / "voblint"


def load() -> dict[str, dict]:
    if not MANIFEST.is_file():
        sys.exit(f"claims: no manifest at {MANIFEST}")
    return tomllib.loads(MANIFEST.read_text()).get("claims", {})


def run(name: str, claim: dict) -> str:
    """Run one claim and return exactly what a reader of the figure sees."""
    if not CLI.is_file():
        sys.exit("claims: cli/voblint is not built -- run `pixi run cli-build`")
    proc = subprocess.run([str(CLI), *claim["argv"]], cwd=REPO,
                          capture_output=True, text=True)
    expected = claim.get("expect_status", 0)
    if proc.returncode != expected:
        sys.exit(f"claims: {name} exited {proc.returncode}, expected {expected}\n"
                 f"{proc.stdout}{proc.stderr}")
    # stderr carries the frontend's diagnostics, which some figures are about.
    return (proc.stdout + proc.stderr).rstrip("\n") + "\n"


def main() -> int:
    ap = argparse.ArgumentParser()
    mode = ap.add_mutually_exclusive_group(required=True)
    mode.add_argument("--write", action="store_true")
    mode.add_argument("--check", action="store_true")
    mode.add_argument("--list", action="store_true")
    args = ap.parse_args()

    claims = load()
    if args.list:
        for name, claim in sorted(claims.items()):
            print(f"{name}\n    {' '.join(claim['argv'])}\n    {claim.get('why', '')}")
        return 0

    OUTDIR.mkdir(parents=True, exist_ok=True)
    stale: list[str] = []

    for name, claim in sorted(claims.items()):
        actual = run(name, claim)
        path = OUTDIR / f"{name}.txt"
        if args.write:
            path.write_text(actual)
            print(f"claims: wrote {path.relative_to(REPO)}")
            continue
        stored = path.read_text() if path.is_file() else ""
        if stored != actual:
            diff = "".join(difflib.unified_diff(
                stored.splitlines(True), actual.splitlines(True),
                fromfile=f"{name}.txt (in the thesis)",
                tofile=f"{name}.txt (what the CLI prints now)"))
            stale.append(f"{name}\n  claim: {claim.get('why', '(no why line)')}\n"
                         f"  command: voblint {' '.join(claim['argv'])}\n{diff}")

    if stale:
        print(f"claims: {len(stale)} thesis claim(s) no longer match the CLI:\n")
        print("\n".join(stale))
        print("If the new output is correct, run thesis/tools/claims.py --write "
              "and update the surrounding prose in the same change.")
        return 1

    print(f"claims: {len(claims)} claim(s) still match the CLI")
    return 0


if __name__ == "__main__":
    sys.exit(main())
