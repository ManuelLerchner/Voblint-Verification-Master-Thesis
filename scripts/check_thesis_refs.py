#!/usr/bin/env python3
"""Fail when the thesis names something the formalization does not define.

The thesis marks every reference to a real entity with a function that also
declares what kind of entity it is -- ``isathm``, ``isaconst``, ``isatype``,
``isalocale``, ``isasession``, ``isacmd``. That declaration is what makes
checking worth anything: a plain "does this identifier occur somewhere" test passes when a
lemma is downgraded to a definition or a locale is replaced by a class, which
is exactly the drift a reader would be misled by.

So each reference is resolved against the declaring command in the sources:

  isathm("X")      lemma / theorem / corollary / proposition named X
  isaconst("X")    definition / fun / abbreviation / primrec / inductive X
  isatype("X")     datatype / type_synonym / record X
  isalocale("X")   locale / class X
  isasession("X")  a session declared in some ROOT
  isacmd("X")      an Isabelle outer-syntax command (checked when
                   ISABELLE_HOME is reachable, skipped otherwise)

Three outcomes: resolved, missing (with a spelling suggestion), or -- the
interesting one -- found under a different command, reported as a deviation.

Usage: python3 scripts/check_thesis_refs.py [--thesis DIR]
"""

from __future__ import annotations

import argparse
import difflib
import os
import re
import shutil
import subprocess
import sys
from collections import defaultdict
from pathlib import Path

REPO = Path(__file__).resolve().parent.parent

# One kind per declaring command. A name may legitimately hold several kinds
# (an inductive predicate brings a constant and an induction rule), so the
# inventory maps name -> set of kinds.
KIND_COMMANDS = {
    "thm": ("lemma", "theorem", "corollary", "proposition", "schematic_goal"),
    "const": ("definition", "fun", "primrec", "abbreviation", "inductive",
              "inductive_set", "function", "partial_function",
              "lift_definition"),
    "type": ("datatype", "type_synonym", "record", "typedef"),
    "locale": ("locale", "class"),
}
COMMAND_KIND = {cmd: kind for kind, cmds in KIND_COMMANDS.items() for cmd in cmds}

# `record 'a domain_transfer =` and `datatype ('a, 'b) t = ...` put type
# parameters between the command and the name, so those are skipped first.
DECL = re.compile(
    r"^\s*(?:qualified\s+)?(" + "|".join(sorted(COMMAND_KIND, key=len, reverse=True))
    + r")\b\s+(?:(?:\([^)]*\)|'[A-Za-z][A-Za-z0-9_']*)\s+)*"
    + r"([A-Za-z][A-Za-z0-9_']*)",
    re.M,
)
# `lemma foo:` and `lemma foo [simp]:` both declare foo; `lemma "..."` does not.
ANON = re.compile(r'^\s*(?:lemma|theorem|corollary)\s+["\\]')
# `  field :: "type"` lines inside a record / datatype body.
FIELD = re.compile(r"^\s+([a-z][A-Za-z0-9_']*)\s*::", re.M)

TYPST_REF = re.compile(r"\bisa(thm|const|type|locale|session|cmd)\(\"([^\"]*)\"\)")

# Names that deliberately do not resolve, with the reason.
ALLOWED = {
    # Goblint's own vocabulary, cited for comparison rather than claimed.
    "Spec", "assign", "ctx", "combine_env",
}


COMMAND_DECL = re.compile(r"command_keyword>\\<open>([A-Za-z0-9_']+)\\<close>")


def isabelle_commands() -> set[str] | None:
    """Outer-syntax command names, or None when Isabelle is not reachable."""
    home = os.environ.get("ISABELLE_HOME")
    if not home:
        exe = shutil.which("isabelle")
        if exe:
            try:
                home = subprocess.run([exe, "getenv", "-b", "ISABELLE_HOME"],
                                      capture_output=True, text=True,
                                      check=True).stdout.strip()
            except (subprocess.CalledProcessError, OSError):
                home = None
    if not home or not Path(home).is_dir():
        return None
    names: set[str] = set()
    for sub in ("src/Pure", "src/HOL/Tools", "src/Tools"):
        for path in (Path(home) / sub).rglob("*"):
            if path.suffix in (".ML", ".thy") and path.is_file():
                names |= set(COMMAND_DECL.findall(path.read_text(errors="ignore")))
    return names or None


def build_inventory() -> tuple[dict[str, set[str]], set[str]]:
    """Map every declared name to the kinds it is declared with."""
    kinds: dict[str, set[str]] = defaultdict(set)
    for root in ("src", "vendor"):
        for path in (REPO / root).rglob("*.thy"):
            text = path.read_text(errors="ignore")
            text = re.sub(r"\(\*.*?\*\)", "", text, flags=re.S)
            for m in DECL.finditer(text):
                line_start = text.rfind("\n", 0, m.start()) + 1
                if ANON.match(text, line_start):
                    continue
                kinds[m.group(2)].add(COMMAND_KIND[m.group(1)])
                # A record's fields and a datatype's selectors are constants;
                # prose cites them (`intra`, `calls`) as often as it cites the
                # type they belong to.
                if m.group(1) in ("record", "datatype"):
                    for f in FIELD.finditer(text, m.end()):
                        if f.group(0).lstrip().startswith(("record", "datatype")):
                            break
                        kinds[f.group(1)].add("const")

    sessions: set[str] = set()
    for roots in REPO.rglob("ROOT"):
        for m in re.finditer(r"^\s*session\s+\"?([A-Za-z0-9_]+)\"?", 
                             roots.read_text(errors="ignore"), re.M):
            sessions.add(m.group(1))
    return kinds, sessions


def collect_refs(thesis: Path) -> list[tuple[Path, int, str, str]]:
    refs = []
    for path in sorted(thesis.rglob("*")):
        if path.suffix != ".typ" or not path.is_file():
            continue
        text = path.read_text(errors="ignore")
        for m in TYPST_REF.finditer(text):
            line = text.count("\n", 0, m.start()) + 1
            refs.append((path, line, m.group(1), m.group(2)))
    return refs


def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("--thesis", default="thesis", type=Path)
    args = ap.parse_args()

    thesis = (REPO / args.thesis) if not args.thesis.is_absolute() else args.thesis
    if not thesis.is_dir():
        print(f"check_thesis_refs: no such directory: {thesis}", file=sys.stderr)
        return 1

    kinds, sessions = build_inventory()
    commands = isabelle_commands()
    if not kinds:
        print("check_thesis_refs: no declarations found -- is the tree checked "
              "out, including vendor/td-verification?", file=sys.stderr)
        return 1

    refs = collect_refs(thesis)
    missing: list[str] = []
    deviated: list[str] = []
    skipped_cmds: list[str] = []

    for path, line, kind, name in refs:
        if name in ALLOWED:
            continue
        site = f"{path.relative_to(REPO)}:{line}"
        if kind == "cmd":
            if commands is None:
                skipped_cmds.append(name)
            elif name not in commands:
                near = difflib.get_close_matches(name, sorted(commands), 1, 0.75)
                hint = f" -- did you mean {near[0]}?" if near else ""
                missing.append(f"  {site}: {name} is not an Isabelle command{hint}")
            continue
        if kind == "session":
            if name not in sessions:
                near = difflib.get_close_matches(name, sorted(sessions), 1, 0.7)
                hint = f" -- did you mean {near[0]}?" if near else ""
                missing.append(f"  {site}: session {name} is not declared in any ROOT{hint}")
            continue
        have = kinds.get(name)
        if have is None:
            near = difflib.get_close_matches(name, sorted(kinds), 1, 0.75)
            hint = f" -- did you mean {near[0]}?" if near else ""
            missing.append(f"  {site}: isa{kind}(\"{name}\") does not exist{hint}")
        elif kind not in have:
            deviated.append(
                f"  {site}: {name} is cited as a {kind}, but the sources declare "
                f"it as {'/'.join(sorted(have))}")

    if missing or deviated:
        if missing:
            print(f"check_thesis_refs: {len(missing)} reference(s) name something "
                  "that does not exist:")
            print("\n".join(missing))
        if deviated:
            if missing:
                print()
            print(f"check_thesis_refs: {len(deviated)} reference(s) have deviated "
                  "from what the sources declare:")
            print("\n".join(deviated))
        print("\nFix the reference, or add it to ALLOWED with a reason if it "
              "deliberately names something outside this tree.")
        return 1

    print(f"check_thesis_refs: {len(refs)} reference(s) resolve against the sources")
    if skipped_cmds:
        print(f"  ({len(set(skipped_cmds))} \\isacmd reference(s) unchecked: "
              "Isabelle is not on PATH)")
    return 0


if __name__ == "__main__":
    sys.exit(main())
