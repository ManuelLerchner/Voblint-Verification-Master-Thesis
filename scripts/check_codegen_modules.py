#!/usr/bin/env python3
"""Fail when the OCaml export emits a module nobody asked for.

Isabelle's OCaml serializer puts one module per contributing theory unless a
``code_identifier`` block in ``src/CLI/Analyse_Dispatch.thy`` says otherwise.
Adding a theory whose constants are reachable from an export root and
forgetting that block does not fail the build: the new theory quietly gets its
own module, and the next edit that makes ``Core`` depend on it fails with a
module dependency cycle naming two constants and no theory.

This check turns that latent breakage into an immediate one. It reads the
generated OCaml, lists the modules it declares, and compares them against the
set below. A new name means either the ``code_identifier`` block is missing an
entry, or the module is genuinely intended and belongs here.

It reads the *checked-in* export, so on its own it is green whenever a theory
lands without a regeneration -- exactly the case it exists to catch. So it also
reports theories that appeared since the export was last regenerated and are
absent from the ``code_identifier`` block. That half is advisory: such a theory
is only a problem if its constants are reachable from an export root, which
this check cannot decide without running Isabelle.
"""

from __future__ import annotations

import re
import subprocess
import sys
from pathlib import Path

REPO = Path(__file__).resolve().parent.parent
GENERATED = REPO / "codegen" / "generated" / "ml" / "Voblint_CLI.ml"
MAP_SOURCE = REPO / "src" / "CLI" / "Analyse_Dispatch.thy"

MODULE_RE = re.compile(r"^module ([A-Za-z_][A-Za-z0-9_]*) : sig", re.MULTILINE)
CODE_MODULE_RE = re.compile(r"code_module\s+([A-Za-z_][A-Za-z0-9_.]*)")

# Modules the export is meant to emit: the four the handwritten OCaml in cli/
# names, plus HOL's own runtime support. Everything else is a theory that
# escaped the code_identifier block.
#
# Core                    everything remapped onto one module, because the
#                         unsplit theories have real mutual code-level
#                         dependencies
# Analysis_Config         mk_analysis_config, valid_analysis_config
# Analyse_Dispatch        analyse_config, analyse_config_ctx,
#                         analyse_config_with_state, abstract_value
# State_Report_GraphViz   the twelve *_dot_auto / *_graph_snapshot_auto
# Bit_Shifts, Str_Literal HOL runtime support, not project theories
EXPECTED = {
    "Core",
    "Analysis_Config",
    "Analyse_Dispatch",
    "State_Report_GraphViz",
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

    mapped = set(CODE_MODULE_RE.findall(MAP_SOURCE.read_text(errors="ignore")))
    unmapped = [
        p for p in newer if Path(p).stem not in {m.split(".")[-1] for m in mapped}
    ]

    print(
        f"check_codegen_modules: note -- {len(newer)} theory file(s) changed since "
        "the export was last regenerated, so the result above does not cover them."
    )
    if unmapped:
        print("  not named in the code_identifier block:")
        for path in unmapped:
            print(f"    {path}")
        print(
            "  Harmless if none of their constants is reachable from an export "
            "root. Run `pixi run codegen` to decide."
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
        mapped = set(CODE_MODULE_RE.findall(MAP_SOURCE.read_text(errors="ignore")))
        print("check_codegen_modules: the export emits modules of its own:")
        for name in unexpected:
            hint = (
                "already in the code_identifier block -- the mapping did not fire"
                if name in mapped or f"Voblint_CLI.{name}" in mapped
                else f"add `code_module {name} \\<rightharpoonup> (OCaml) Core`"
            )
            print(f"  {name}: {hint}")
        print()
        print(f"See the code-export module map section of {MAP_SOURCE.name}.")

    if unexpected or missing:
        return 1

    print(f"check_codegen_modules: {len(emitted)} modules, all expected")
    report_staleness()
    return 0


if __name__ == "__main__":
    sys.exit(main())
