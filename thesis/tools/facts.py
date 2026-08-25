#!/usr/bin/env python3
"""Put the proved statement itself in the thesis, not a retyped copy of it.

Isabelle's own document preparation gives this away for free -- `@{thm foo}`
typesets the statement it actually proved, and the build fails if `foo` is
gone -- but only to a document written inside a theory file. This gets the same
guarantee from outside one: it asks a built session for each fact the thesis
cites, stores the result, and the template renders it. A missing key is a
compile error, and a changed statement is a diff here.

Statements come back in ASCII symbol form (`\\<Longrightarrow>`), which is what
the Typst side already knows how to decode.

    thesis/tools/facts.py --write [--session Voblint_CFG]
    thesis/tools/facts.py --check
    thesis/tools/facts.py --list

Coverage is bounded by what is built: a fact in a session with no heap is
reported as unresolved, naming the session to build.
"""

from __future__ import annotations

import argparse
import difflib
import json
import os
import re
import subprocess
import sys
import tempfile
import tomllib
from pathlib import Path

THESIS = Path(__file__).resolve().parent.parent
REPO = THESIS.parent
MANIFEST = THESIS / "shared" / "facts.toml"
OUT = THESIS / "shared" / "generated" / "facts.json"
MARGIN = 76      # characters; matches what fits a framed block on A4
SEP = "\x1f"      # field separator
REC = "\x1e"      # record separator: statements contain pretty-printed newlines

ML_TEMPLATE = r'''
val thy = Thy_Info.get_theory "{theory}";
(* Type and sort annotations on schematic variables double the length of a
   statement without telling a reader anything they cannot infer, so the page
   shows the statement, not the elaborated term. *)
(* `?B` is how a stored theorem writes a variable that is implicitly
   universally quantified and ready for instantiation. That is a fact about
   Isabelle's representation, not about the mathematics, so the page drops the
   marker -- the same choice Concrete Semantics makes. *)
val ctxt =
  Config.put show_question_marks false
    (Config.put show_sorts false (Config.put show_types false
      (Proof_Context.init_global thy)));
(* Isabelle's own line breaks at a fixed margin: they land at the connectives,
   which is exactly where a reader wants a long statement to break. Letting the
   template re-wrap instead produces a wall of text. *)
val ops = Pretty.pure_output_ops (SOME {margin});
fun plain p = Pretty.string_of_ops ops p;
fun statement name =
  Print_Mode.setmp [] (fn () =>
    plain (Thm.pretty_thm ctxt (Global_Theory.get_thm thy name))) ();
val out = TextIO.openOut "{outfile}";
val sep = str (Char.chr 31) and rec_sep = str (Char.chr 30);
fun emit name =
  (TextIO.output (out, name ^ sep ^ statement name ^ rec_sep)
   handle _ => TextIO.output (out, name ^ sep ^ "!MISSING" ^ rec_sep));
val _ = List.app emit [{names}];
val _ = TextIO.closeOut out;
'''


def wanted() -> tuple[dict, str, str]:
    if not MANIFEST.is_file():
        sys.exit(f"facts: no manifest at {MANIFEST}")
    data = tomllib.loads(MANIFEST.read_text())
    return (data.get("facts", {}),
            data.get("session", "Voblint_CFG"),
            data.get("theory", "Main"))


def ask_isabelle(names: list[str], session: str, theory: str) -> dict[str, str]:
    """Run one Isabelle ML session and collect `name -> statement`."""
    with tempfile.TemporaryDirectory() as tmp:
        outfile = Path(tmp) / "facts.txt"
        script = Path(tmp) / "facts.ML"
        script.write_text(ML_TEMPLATE.format(
            theory=theory, outfile=outfile, margin=MARGIN,
            names=", ".join(f'"{n}"' for n in names)))
        # Session directories come from the repository's ROOTS, plus the
        # vendored solver and the AFP, exactly as the build script passes them.
        cmd = ["isabelle", "console", "-l", session, "-d", str(REPO)]
        for extra in (os.environ.get("AFP"), REPO / "vendor" / "td-verification"):
            if extra and Path(extra).is_dir():
                cmd += ["-d", str(extra)]
        proc = subprocess.run(cmd, input=f'use "{script}";\n',
                              capture_output=True, text=True, cwd=REPO)
        if not outfile.is_file():
            sys.exit(f"facts: Isabelle produced nothing for session {session}.\n"
                     f"Build it first: pixi run build\n{proc.stdout[-2000:]}"
                     f"{proc.stderr[-2000:]}")
        result = {}
        for record in outfile.read_text().split(REC):
            if not record.strip():
                continue
            name, _, stmt = record.partition(SEP)
            result[name.strip()] = stmt
        return result


def main() -> int:
    ap = argparse.ArgumentParser()
    mode = ap.add_mutually_exclusive_group(required=True)
    mode.add_argument("--write", action="store_true")
    mode.add_argument("--check", action="store_true")
    mode.add_argument("--list", action="store_true")
    ap.add_argument("--session")
    args = ap.parse_args()

    facts, session, theory = wanted()
    session = args.session or session

    if args.list:
        for name, meta in sorted(facts.items()):
            print(f"{name}\n    {meta.get('why', '')}")
        return 0

    names = sorted(facts)
    if not names:
        print("facts: nothing cited")
        return 0

    got = ask_isabelle(names, session, theory)
    unresolved = [n for n in names if got.get(n, "!MISSING") == "!MISSING"]
    if unresolved:
        print(f"facts: {len(unresolved)} cited fact(s) did not resolve in "
              f"session {session}:")
        for n in unresolved:
            print(f"  {n} -- expected in {facts[n].get('session', '(unknown session)')}")
        print("Either the fact was renamed, or its session is not built.")
        return 1

    payload = json.dumps(
        {"session": session, "theory": theory,
         "facts": {n: {"statement": got[n], "why": facts[n].get("why", "")}
                   for n in names}},
        indent=2, sort_keys=True) + "\n"

    if args.write:
        OUT.parent.mkdir(parents=True, exist_ok=True)
        OUT.write_text(payload)
        print(f"facts: wrote {OUT.relative_to(REPO)} ({len(names)} fact(s))")
        return 0

    stored = OUT.read_text() if OUT.is_file() else ""
    if stored != payload:
        print("facts: the stored statements no longer match what Isabelle proves:\n")
        print("".join(difflib.unified_diff(
            stored.splitlines(True), payload.splitlines(True),
            fromfile="facts.json (in the thesis)",
            tofile="facts.json (what Isabelle proves now)")))
        print("If the new statement is correct, run thesis/tools/facts.py --write "
              "and check the surrounding prose still describes it.")
        return 1

    print(f"facts: {len(names)} statement(s) still match what Isabelle proves")
    return 0


if __name__ == "__main__":
    sys.exit(main())
