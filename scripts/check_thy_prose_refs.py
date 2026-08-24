#!/usr/bin/env python3
"""Fail when a .thy comment names a constant or lemma that no longer exists.

Isabelle checks ``\\<^const>`` and ``@{thm ...}`` antiquotations against the
theory context, so a rename breaks the build. It does not check a plain
``\\<open>name\\<close>`` cartouche, which is how most prose in this tree cites a
constant or a lemma -- and there is no short checked antiquotation for a fact
name that does not also print the whole statement. So plain cartouches are the
right thing to write, and this is what keeps them honest.

A reference is reported when the identifier appears nowhere in any .thy under
src/ or vendor/ outside prose. That is deliberately conservative: locale-local
names, ML identifiers and metavariables all resolve somewhere, so the false
positives are few and the ones that remain are listed in ALLOWED below.
"""

from __future__ import annotations

import re
import sys
from pathlib import Path

REPO = Path(__file__).resolve().parent.parent
OPEN, CLOSE = r"\<open>", r"\<close>"

# Names that are deliberately not Voblint constants.
ALLOWED = {
    # Goblint's own vocabulary, cited for comparison.
    "id_binary_log", "id_binary_pred", "id_unary_log",
    # Metavariable placeholders: X stands for a domain name.
    "bfilter_X_st", "branch_X_st_for",
    # A naming-convention prefix, cited as "the <prefix> family" -- the family
    # members exist (analyse_interval_td_result, _report, ...), the bare prefix
    # is not itself a constant.
    "analyse_interval_td",
    # A solver-menu label: `STR ''warrow_per_origin''` in Solver_Menu's table,
    # a string literal rather than an identifier.
    "warrow_per_origin",
    # Deliberately names something that does *not* exist -- Parity_Exec explains
    # that its branch transfer is the identity, so there is no such constant to
    # generalize.
    "branch_parity_st_for",
    # Deliberately name lemmas that no longer exist -- the Interval flagship
    # examples explain *why* they were deleted (EA_Ret's unconditional top
    # fallback breaks action_reduces's ret_some conjunct).
    "ivl_tf_st_for_reduces", "sign_tf_st_for_reduces",
}

PROSE_KW = re.compile(r"\b(text|txt|section|subsection|subsubsection|paragraph|chapter)\b\s*")
REF = re.compile(re.escape(OPEN) + r"([a-z][A-Za-z0-9_']*)" + re.escape(CLOSE))
IDENT = re.compile(r"[A-Za-z][A-Za-z0-9_']*")


def strip_prose(text: str) -> str:
    """Return `text` with comments and prose blocks removed."""
    text = re.sub(r"\(\*.*?\*\)", "", text, flags=re.S)
    out, i, n = [], 0, len(text)
    while i < n:
        m = PROSE_KW.match(text, i)
        if m and text.startswith(OPEN, m.end()):
            depth, k = 0, m.end()
            while k < n:
                if text.startswith(OPEN, k):
                    depth += 1
                    k += len(OPEN)
                elif text.startswith(CLOSE, k):
                    depth -= 1
                    k += len(CLOSE)
                else:
                    k += 1
                if depth == 0:
                    break
            i = k
            continue
        out.append(text[i])
        i += 1
    return "".join(out)


def main() -> int:
    sources = {p: p.read_text(errors="ignore")
               for root in ("src", "vendor")
               for p in (REPO / root).rglob("*.thy")}
    if not sources:
        print("check_thy_prose_refs: no .thy files found", file=sys.stderr)
        return 1

    # A name defined only in the vendored solver resolves nowhere when the
    # submodule is absent, so every prose reference to one is reported as
    # dangling. That looks like a dozen broken renames rather than a missing
    # checkout, so say which it is.
    if not any(str(p).startswith(str(REPO / "vendor" / "td-verification"))
               for p in sources):
        print("check_thy_prose_refs: vendor/td-verification has no .thy "
              "files -- the submodule is not checked out.\n"
              "Prose naming a vendored constant would be reported as dangling. "
              "Run: git submodule update --init --depth 1 vendor/td-verification",
              file=sys.stderr)
        return 1

    defined: set[str] = set()
    for path, text in sources.items():
        body = strip_prose(text) if str(path).startswith(str(REPO / "src")) else text
        defined |= set(IDENT.findall(body))

    dangling: dict[str, list[str]] = {}
    for path, text in sources.items():
        if not str(path).startswith(str(REPO / "src")):
            continue
        for m in REF.finditer(text):
            name = m.group(1)
            if name.count("_") < 2 or name in defined or name in ALLOWED:
                continue
            if name.endswith(("_def", "_defs", "_simps")):
                continue
            line = text.count("\n", 0, m.start()) + 1
            dangling.setdefault(name, []).append(
                f"{path.relative_to(REPO)}:{line}")

    if dangling:
        print(f"check_thy_prose_refs: {len(dangling)} prose reference(s) name "
              "something that no longer exists:")
        for name in sorted(dangling):
            print(f"  {name}")
            for site in sorted(set(dangling[name])):
                print(f"      {site}")
        print()
        print("Rename the reference, or add it to ALLOWED if it deliberately "
              "names something outside this tree.")
        return 1

    print("check_thy_prose_refs: no dangling prose references")
    return 0


if __name__ == "__main__":
    sys.exit(main())
