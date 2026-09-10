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


def export_is_stale() -> bool:
    """Whether the checked-in export no longer corresponds to the sources.

    Delegates to codegen-hash.sh, the one definition of "codegen's inputs"
    that regenerate-codegen.sh writes and cli-build.sh checks. Defining it a
    third way here is what the hash script's own header warns against: a git
    heuristic over "commits touching codegen/generated/" cannot advance when a
    proof-only change leaves the emitted OCaml byte-identical, so it reports
    stale forever after the first such commit.
    """
    stamp = REPO / "codegen" / "generated" / ".source-hash"
    if not stamp.exists():
        return True
    try:
        out = subprocess.run(
            [str(REPO / "scripts" / "mk" / "codegen-hash.sh")],
            capture_output=True, text=True, cwd=REPO, check=False,
        )
    except OSError:
        return False
    if out.returncode != 0:
        return False
    return out.stdout.strip() != stamp.read_text().strip()


def report_staleness() -> None:
    """Say so when a green result does not cover everything in the tree."""
    if not export_is_stale():
        return

    print(
        "check_codegen_modules: note -- the export no longer matches the sources, "
        "so the result above does not cover them. Run `pixi run codegen` to refresh it."
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
