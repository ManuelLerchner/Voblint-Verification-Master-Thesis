#!/usr/bin/env python3
"""Fail when a locale assumption names something that is not a real constant.

Inside `assumes`, an unknown lowercase identifier is not an error: Isabelle
reads it as a free variable and generalizes the assumption over it. So a
locale whose assumption cites a deleted constant keeps building, while that
assumption quietly stops constraining anything -- it now holds for an
arbitrary function of that name. Every session stays green; the defect
surfaces only much later, where some consumer has to discharge the assumption
and cannot.

That is what happened when `DG_Transfer_Combinators.thy` was deleted: three
`call_fwd_ok` assumptions kept mentioning `enter_local`, which by then named
nothing, and `Voblint_Analysis` built clean for several sessions afterwards.

The check: inside every `locale`/`context` header, each identifier occurring
in a quoted term must be a parameter fixed by that header, a variable bound
there, or a name defined somewhere in a theory body. Anything else is a free
variable, and almost certainly a mistake.

Deliberately conservative -- identifiers shorter than four characters and
those without an underscore are skipped, since single-letter and short
variable names are legitimately free in these headers.
"""

from __future__ import annotations

import re
import sys
from pathlib import Path

REPO = Path(__file__).resolve().parent.parent
OPEN, CLOSE = r"\<open>", r"\<close>"

# Names that are legitimately not defined in this tree.
ALLOWED = {
    # A HOL type class, cited in a sort constraint inside a quoted type.
    "complete_lattice",
}

PROSE_KW = re.compile(
    r"\b(text|txt|section|subsection|subsubsection|paragraph|chapter)\b\s*")
IDENT = re.compile(r"[a-z][A-Za-z0-9_']*")
HEADER = re.compile(r"^(locale|context)\b(.*?)^begin", re.S | re.M)
QUOTED = re.compile(r'"([^"]*)"', re.S)
FIXED = re.compile(r"(?:fixes|and|for)\s+([a-z][A-Za-z0-9_']*)\s*::")
BOUND = re.compile(r"\\<(?:And|forall|exists|lambda)>([^.]{0,120}?)\.")


def strip_prose(text: str) -> str:
    """Return `text` with `(* *)` comments and prose cartouches removed."""
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
    bodies = {p: strip_prose(p.read_text(errors="ignore"))
              for p in (REPO / "src").rglob("*.thy")}
    vendor = REPO / "vendor"
    if vendor.is_dir():
        bodies.update({p: p.read_text(errors="ignore")
                       for p in vendor.rglob("*.thy")})
    if not bodies:
        print("check_locale_parameters: no .thy files found", file=sys.stderr)
        return 1

    headers = [(p, m.group(0))
               for p, body in bodies.items()
               for m in HEADER.finditer(body)]

    # Every name introduced outside a locale header. A name that occurs only
    # inside headers is exactly the free-variable case this checks for.
    defined: set[str] = set()
    for path, body in bodies.items():
        rest = body
        for owner, header in headers:
            if owner == path:
                rest = rest.replace(header, " ")
        defined |= set(IDENT.findall(rest))

    free: dict[str, list[str]] = {}
    for path, header in headers:
        if not str(path).startswith(str(REPO / "src")):
            continue
        local = {m.group(1) for m in FIXED.finditer(header)}
        for m in BOUND.finditer(header):
            local |= set(IDENT.findall(m.group(1)))
        for term in QUOTED.findall(header):
            for name in set(IDENT.findall(term)):
                if name in local or name in defined or name in ALLOWED:
                    continue
                if len(name) < 4 or "_" not in name:
                    continue
                free.setdefault(name, []).append(
                    str(path.relative_to(REPO)))

    if free:
        print(f"check_locale_parameters: {len(free)} identifier(s) occur free "
              "in a locale assumption:")
        for name in sorted(free):
            print(f"  {name}")
            for site in sorted(set(free[name])):
                print(f"      {site}")
        print()
        print("Isabelle reads these as free variables, so the assumptions "
              "naming them hold for an arbitrary function and constrain "
              "nothing. Use the real constant, or add the name to ALLOWED if "
              "it is deliberately not defined in this tree.")
        return 1

    print(f"check_locale_parameters: {len(headers)} locale/context headers, "
          "no free identifiers in assumptions")
    return 0


if __name__ == "__main__":
    sys.exit(main())
