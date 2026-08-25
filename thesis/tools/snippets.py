#!/usr/bin/env python3
"""Lift declarations out of the theories so the thesis never retypes one.

A snippet pasted into a chapter is a copy, and a copy drifts. Line-range
inclusion (`firstline=12, lastline=28`) is barely better: it silently starts
quoting the wrong thing as soon as anything above it grows.

So snippets are cited by *name*. `thesis/shared/snippets.toml` lists the
declarations the thesis shows; this extracts each one's source text, verbatim
and in ASCII symbol form, into thesis/shared/generated/snippets/. The name has
to resolve, so a rename fails the build instead of silently quoting a stale
definition -- and because the extracted text is committed, a change to a shown
definition surfaces as a diff on the file that carries it.

    thesis/tools/snippets.py --write    regenerate
    thesis/tools/snippets.py --check    re-extract and diff; non-zero on drift
    thesis/tools/snippets.py --list     show what is cited

The thesis reads them with #thy("name").
"""

from __future__ import annotations

import argparse
import difflib
import re
import sys
import tomllib
from pathlib import Path

THESIS = Path(__file__).resolve().parent.parent
REPO = THESIS.parent
MANIFEST = THESIS / "shared" / "snippets.toml"
OUTDIR = THESIS / "shared" / "generated" / "snippets"

# Commands that open a top-level declaration. A snippet runs from the command
# that declares the requested name up to the next one at column 0, minus
# trailing blank lines -- which is what a reader means by "show me sound_state".
COMMANDS = (
    "definition", "fun", "primrec", "abbreviation", "inductive", "inductive_set",
    "function", "partial_function", "lift_definition", "datatype",
    "type_synonym", "record", "typedef", "locale", "class", "instantiation",
    "lemma", "theorem", "corollary", "proposition", "interpretation",
    "sublocale", "text", "section", "subsection", "subsubsection", "context",
    "instance", "declare", "notation", "export_code", "code_identifier", "end",
)
NEXT_COMMAND = re.compile(r"^(?:" + "|".join(COMMANDS) + r")\b", re.M)


# `sublocale sound_dg_spec \<subseteq> ...` mentions the name but does not
# declare it. Defining commands are tried across every theory first, so a later
# extension never shadows the declaration a reader is being shown.
DEFINING = (
    "definition", "fun", "primrec", "abbreviation", "inductive", "inductive_set",
    "function", "partial_function", "lift_definition", "datatype",
    "type_synonym", "record", "typedef", "locale", "class",
    "lemma", "theorem", "corollary", "proposition",
)


def declaration_re(name: str, commands: tuple[str, ...]) -> re.Pattern:
    """Match the command that declares `name`, allowing type parameters."""
    return re.compile(
        r"^(?:" + "|".join(commands) + r")\b[ \t]+"
        r"(?:(?:\([^)]*\)|'[A-Za-z][A-Za-z0-9_']*)[ \t]+)*"
        + re.escape(name) + r"(?![A-Za-z0-9_'])",
        re.M,
    )


def extract(name: str, files: list[Path],
            pin: str | None = None) -> tuple[str, Path] | None:
    if pin:
        files = [p for p in files if str(p.relative_to(REPO)) == pin] or files
    for commands in (DEFINING, COMMANDS):
        for path in files:
            text = path.read_text(errors="ignore")
            m = declaration_re(name, commands).search(text)
            if not m:
                continue
            nxt = NEXT_COMMAND.search(text, m.end())
            body = text[m.start(): nxt.start() if nxt else len(text)]
            return body.rstrip() + "\n", path
    return None


def theory_files() -> list[Path]:
    return sorted(p for root in ("src", "vendor")
                  for p in (REPO / root).rglob("*.thy"))


def main() -> int:
    ap = argparse.ArgumentParser()
    mode = ap.add_mutually_exclusive_group(required=True)
    mode.add_argument("--write", action="store_true")
    mode.add_argument("--check", action="store_true")
    mode.add_argument("--list", action="store_true")
    args = ap.parse_args()

    if not MANIFEST.is_file():
        sys.exit(f"snippets: no manifest at {MANIFEST}")
    wanted = tomllib.loads(MANIFEST.read_text()).get("snippets", {})

    if args.list:
        for name, meta in sorted(wanted.items()):
            print(f"{name}\n    {meta.get('why', '')}")
        return 0

    files = theory_files()
    if not files:
        sys.exit("snippets: no .thy files -- is vendor/td-verification checked out?")

    OUTDIR.mkdir(parents=True, exist_ok=True)
    missing: list[str] = []
    stale: list[str] = []

    for name, meta in sorted(wanted.items()):
        found = extract(name, files, meta.get("file"))
        if found is None:
            missing.append(f"  {name}: no declaration found in any theory")
            continue
        body, path = found
        header = f"(* {path.relative_to(REPO)} *)\n"
        text = header + body
        out = OUTDIR / f"{name}.thy"
        if args.write:
            out.write_text(text)
            print(f"snippets: wrote {out.relative_to(REPO)} from {path.relative_to(REPO)}")
            continue
        stored = out.read_text() if out.is_file() else ""
        if stored != text:
            diff = "".join(difflib.unified_diff(
                stored.splitlines(True), text.splitlines(True),
                fromfile=f"{name} (in the thesis)",
                tofile=f"{name} (in the theories)"))
            stale.append(f"{name}\n  shown because: {meta.get('why', '(no why line)')}\n{diff}")

    if missing or stale:
        if missing:
            print(f"snippets: {len(missing)} cited declaration(s) do not exist:")
            print("\n".join(missing))
        if stale:
            print(f"snippets: {len(stale)} snippet(s) differ from the theories:\n")
            print("\n".join(stale))
            print("If the new text is correct, run thesis/tools/snippets.py --write "
                  "and check the surrounding prose still describes it.")
        return 1

    print(f"snippets: {len(wanted)} snippet(s) match the theories")
    return 0


if __name__ == "__main__":
    sys.exit(main())
