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
import subprocess
import sys
from functools import cache
from pathlib import Path

import tomllib

THESIS = Path(__file__).resolve().parent.parent
REPO = THESIS.parent
MANIFEST = THESIS / "shared" / "snippets.toml"
OUTDIR = THESIS / "shared" / "generated" / "snippets"

# Commands that open a top-level declaration. A snippet runs from the command
# that declares the requested name up to the next one at column 0, minus
# trailing blank lines -- which is what a reader means by "show me sound_state".
COMMANDS = (
    "definition",
    "fun",
    "primrec",
    "abbreviation",
    "inductive",
    "inductive_set",
    "inductive_cases",
    "function",
    "partial_function",
    "lift_definition",
    "datatype",
    "type_synonym",
    "record",
    "typedef",
    "quotient_type",
    "locale",
    "class",
    "instantiation",
    "lemma",
    "theorem",
    "corollary",
    "proposition",
    "interpretation",
    "sublocale",
    "text",
    "section",
    "subsection",
    "subsubsection",
    "context",
    "instance",
    "declare",
    "notation",
    "export_code",
    "code_identifier",
    "end",
)
NEXT_COMMAND = re.compile(r"^(?:" + "|".join(COMMANDS) + r")\b", re.M)


# `sublocale sound_dg_spec \<subseteq> ...` mentions the name but does not
# declare it. Defining commands are tried across every theory first, so a later
# extension never shadows the declaration a reader is being shown.
DEFINING = (
    "definition",
    "fun",
    "primrec",
    "abbreviation",
    "inductive",
    "inductive_set",
    "function",
    "partial_function",
    "lift_definition",
    "datatype",
    "type_synonym",
    "record",
    "typedef",
    "quotient_type",
    "locale",
    "class",
    "lemma",
    "theorem",
    "corollary",
    "proposition",
)


# A theorem is shown as its statement. The proof is the theory's business, and
# the thesis cites it rather than reproducing it.
THEOREMS = ("lemma", "theorem", "corollary", "proposition")
PROOF_START = re.compile(
    r"(?<![A-Za-z0-9_'.])"
    r"(?:proof|by|using|unfolding|apply|including|supply|sorry|oops)"
    r"(?![A-Za-z0-9_'])"
)
# Terms and cartouches may contain any of those words; skip over them.
QUOTED = re.compile(r'"[^"]*"|\\<open>|\(\*.*?\*\)', re.S)
CARTOUCHE = re.compile(r"\\<open>|\\<close>")


def statement_only(body: str) -> str:
    """Cut a theorem declaration at the first proof command outside its terms."""
    pos, depth = 0, 0
    while pos < len(body):
        if depth:
            nxt = CARTOUCHE.search(body, pos)
            if nxt is None:
                break
            depth += 1 if nxt.group(0) == "\\<open>" else -1
            pos = nxt.end()
            continue
        proof = PROOF_START.search(body, pos)
        quoted = QUOTED.search(body, pos)
        if proof is None:
            break
        if quoted is None or proof.start() < quoted.start():
            return body[: proof.start()]
        if quoted.group(0) == "\\<open>":
            depth = 1
        pos = quoted.end()
    sys.exit(f"snippets: no proof found after the statement:\n{body}")


def declaration_re(name: str, commands: tuple[str, ...]) -> re.Pattern:
    """Match the command that declares `name`, allowing type parameters.

    The name may sit on the line after the command (`inductive\n  pstep ::`).
    """
    return re.compile(
        r"^(?:" + "|".join(commands) + r")\b\s+"
        r"(?:(?:\([^)]*\)|'[A-Za-z][A-Za-z0-9_']*)[ \t]+)*"
        + re.escape(name)
        + r"(?![A-Za-z0-9_'])",
        re.M,
    )


# Isabelle writes its own sources as `~~/src/HOL/...`. A snippet pinned there
# is lifted from the installed distribution, so HOL classes the thesis builds on
# are quoted from the same text the session was checked against.
ISABELLE_PREFIX = "~~/"


@cache
def isabelle_home() -> Path:
    out = subprocess.run(
        ["isabelle", "getenv", "-b", "ISABELLE_HOME"],
        capture_output=True,
        text=True,
        check=True,
    )
    return Path(out.stdout.strip())


def display_path(path: Path) -> str:
    if path.is_relative_to(REPO):
        return str(path.relative_to(REPO))
    return ISABELLE_PREFIX + str(path.relative_to(isabelle_home()))


def extract(
    name: str, files: list[Path], pin: str | None = None, with_proof: bool = False
) -> tuple[str, Path] | None:
    if pin and pin.startswith(ISABELLE_PREFIX):
        files = [isabelle_home() / pin.removeprefix(ISABELLE_PREFIX)]
    elif pin:
        files = [p for p in files if str(p.relative_to(REPO)) == pin] or files
    for commands in (DEFINING, COMMANDS):
        for path in files:
            text = path.read_text(errors="ignore")
            m = declaration_re(name, commands).search(text)
            if not m:
                continue
            nxt = NEXT_COMMAND.search(text, m.end())
            body = text[m.start() : nxt.start() if nxt else len(text)]
            command = m.group(0).split(None, 1)[0]
            # A snippet may keep a short proof when the proof is the point,
            # such as a lemma derived in one step from a class's laws.
            if command in THEOREMS and not with_proof:
                body = statement_only(body)
            # A locale or class opens its context with `begin`; the reader is
            # shown the interface, not the context it opens.
            if command in ("locale", "class"):
                body = re.split(r"\s*^begin\b", body, maxsplit=1, flags=re.M)[0]
            return body.rstrip() + "\n", path
    return None


def theory_files() -> list[Path]:
    return sorted(p for root in ("src", "vendor") for p in (REPO / root).rglob("*.thy"))


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
        found = extract(name, files, meta.get("file"), meta.get("proof", False))
        if found is None:
            missing.append(f"  {name}: no declaration found in any theory")
            continue
        body, path = found
        header = f"(* {display_path(path)} *)\n"
        text = header + body
        out = OUTDIR / f"{name}.thy"
        if args.write:
            out.write_text(text)
            print(f"snippets: wrote {out.relative_to(REPO)} from {display_path(path)}")
            continue
        stored = out.read_text() if out.is_file() else ""
        if stored != text:
            diff = "".join(
                difflib.unified_diff(
                    stored.splitlines(True),
                    text.splitlines(True),
                    fromfile=f"{name} (in the thesis)",
                    tofile=f"{name} (in the theories)",
                )
            )
            stale.append(
                f"{name}\n  shown because: {meta.get('why', '(no why line)')}\n{diff}"
            )

    if missing or stale:
        if missing:
            print(f"snippets: {len(missing)} cited declaration(s) do not exist:")
            print("\n".join(missing))
        if stale:
            print(f"snippets: {len(stale)} snippet(s) differ from the theories:\n")
            print("\n".join(stale))
            print(
                "If the new text is correct, run thesis/tools/snippets.py --write "
                "and check the surrounding prose still describes it."
            )
        return 1

    print(f"snippets: {len(wanted)} snippet(s) match the theories")
    return 0


if __name__ == "__main__":
    sys.exit(main())
