#!/usr/bin/env python3
"""Fail when the OCaml export emits a module nobody asked for.

The export in ``src/Executable_Surface/Codegen/Export/Voblint_Codegen.thy`` declares
``module_name Generated``, which puts the whole reachable program into one
OCaml module instead of one module per contributing Isabelle theory. Two more
modules come along regardless: HOL injects ``Bit_Shifts`` and ``Str_Literal``
as literal target code rather than generating them from constants here.

So the emitted module set is fixed, and any change to it is a change to the
API the handwritten OCaml under ``cli/`` links against -- either because
``module_name`` was dropped (the serializer then splits by theory, and those
modules can and do form dependency cycles it cannot express) or because it was
renamed. This check reads the generated OCaml, lists the modules it declares,
and fails on anything but the three below.

It reads the *checked-in* export, so on its own it is green whenever a theory
lands without a regeneration. It therefore also reports theories that appeared
since the export was last regenerated; that half is advisory, since whether
their constants are reachable from an export root cannot be decided without
running Isabelle.
"""

from __future__ import annotations

import re
import subprocess
import sys
from pathlib import Path

REPO = Path(__file__).resolve().parent.parent
GENERATED = REPO / "codegen" / "generated" / "ml" / "Voblint_CLI.ml"
EXPORT_SOURCE = REPO / "src" / "Executable_Surface" / "Codegen" / "Export" / "Voblint_Codegen.thy"

MODULE_RE = re.compile(r"^module ([A-Za-z_][A-Za-z0-9_]*) : sig", re.MULTILINE)

EXPECTED = {
    "Generated",
    "Bit_Shifts",
    "Str_Literal",
}


def _git(*args: str) -> str:
    """Run git in the repo, returning stdout; empty string on any failure."""
    try:
        out = subprocess.run(
            ["git", *args], cwd=REPO, capture_output=True, text=True, check=False
        )
    except OSError:
        return ""
    return out.stdout.strip() if out.returncode == 0 else ""


def theories_newer_than_export() -> list[str]:
    """Theories added or changed since the export was last regenerated.

    Uses git, not mtimes: a fresh clone has no useful mtimes, and a rebase
    rewrites them all. Uncommitted theories count as newer.
    """
    export_rev = _git("log", "-1", "--format=%H", "--", str(GENERATED.relative_to(REPO)))
    if not export_rev:
        return []

    changed: set[str] = set()
    committed = _git("diff", "--name-only", f"{export_rev}..HEAD", "--", "src")
    if committed:
        changed.update(committed.splitlines())
    dirty = _git("status", "--porcelain", "--", "src")
    for line in dirty.splitlines():
        path = line[3:].strip()
        if path:
            changed.add(path)
    return sorted(p for p in changed if p.endswith(".thy"))


def report_staleness() -> None:
    """Say so when a green result does not cover everything in the tree."""
    newer = theories_newer_than_export()
    if not newer:
        return

    print(
        f"check_codegen_modules: note -- {len(newer)} theory file(s) changed since "
        "the export was last regenerated, so the result above does not cover them. "
        "Run `pixi run codegen` to refresh it."
    )


def main() -> int:
    if not GENERATED.exists():
        print(f"check_codegen_modules: {GENERATED} not found; run `pixi run codegen`")
        return 1

    emitted = set(MODULE_RE.findall(GENERATED.read_text(errors="ignore")))
    unexpected = sorted(emitted - EXPECTED)
    missing = sorted(EXPECTED - emitted)

    if missing:
        print("check_codegen_modules: expected modules absent from the export:")
        for name in missing:
            print(f"  {name}")

    if unexpected:
        print("check_codegen_modules: the export emits modules of its own:")
        for name in unexpected:
            print(f"  {name}")
        print()
        print(
            f"A module per theory means {EXPORT_SOURCE.name} lost its "
            "`module_name Generated`; those modules can form a dependency cycle "
            "the OCaml serializer cannot express."
        )

    if unexpected or missing:
        return 1

    print(f"check_codegen_modules: {len(emitted)} modules, all expected")
    report_staleness()
    return 0


if __name__ == "__main__":
    sys.exit(main())
