#!/usr/bin/env python3
"""Fail when a relational theory reaches the pointwise-store machinery.

`Voblint_Analysis_Relational` exists to show that nothing below the domain
layer needs an abstract state to be one value per variable. `Rel_Order_Domain`
makes that claim by supplying an order carrier that is not an `abs_state` and
running it through the same generator, routed spine and solver as every other
domain. The claim is only worth stating while it stays true.

Nothing in the session graph protects it. `Voblint_Analysis_Base` is the parent
session of `Voblint_Analysis_Relational`, so every theory under
`Base/Nonrelational/` is already *available* to a relational theory; what keeps
it out is only that `Rel_Order_Domain` does not import it. Session membership
never forced that, and neither does the directory name -- an import added
tomorrow would build green and quietly retire the claim.

So the boundary is checked here instead: no theory under `src/Analyses/
Relational/` may reach, directly or transitively, a theory whose file lives in
`src/Analyses/Base/Nonrelational/`. Those are exactly the theories that fix a
pointwise store -- `ev`/`n_aval` of type `exp => (vname => 'a) => 'a`, or a
`gs :: vname => bool` classifier over textual names.

The closure is computed over every theory in `src/`, so an indirect route
through a third theory fails too, and a project import naming no theory here is
a failure rather than a skip -- an unfollowed edge would let the walk report
success for a route it never looked at.

The scope is deliberately narrow: this is a dependency check against one
directory, not a proof that relational code makes no pointwise assumptions.
Keeping `Base/Nonrelational/` the one place those assumptions live is what
gives it force, and that part is convention.
"""

from __future__ import annotations

import re
import sys
from pathlib import Path

REPO = Path(__file__).resolve().parent.parent
SRC = REPO / "src"

RELATIONAL = SRC / "Analyses" / "Relational"
FORBIDDEN = SRC / "Analyses" / "Base" / "Nonrelational"

# `theory Name imports A B.C "D.E" ... begin`
HEADER = re.compile(r"^\s*theory\s+(\S+)(.*?)^\s*begin\s*$", re.S | re.M)
NAME = re.compile(r'"([^"]+)"|([A-Za-z_][\w.\']*)')

# Every session defined in this repository is named `Voblint_<Session>`, so a
# qualified import outside that namespace is someone else's theory (HOL, the
# AFP, the vendored TD solver) and is not ours to resolve.
PROJECT_SESSION = "Voblint_"
EXTERNAL_BARE = {"Main", "Complex_Main", "Pure"}


def theories() -> dict[str, tuple[Path, list[str]]]:
    """Map bare theory name -> (file, imported theory names, unqualified)."""
    out: dict[str, tuple[Path, list[str]]] = {}
    for path in sorted(SRC.rglob("*.thy")):
        m = HEADER.search(path.read_text(encoding="utf-8"))
        if not m:
            continue
        name = m.group(1).split(".")[-1]
        body = m.group(2)
        body = body[body.index("imports") + len("imports"):] if "imports" in body else ""
        imports = []
        for quoted, bare in NAME.findall(body):
            token = quoted or bare
            if token in ("imports", "keywords", "abbrevs"):
                continue
            imports.append(token)
        out[name] = (path, imports)
    return out


def unresolved(index: dict[str, tuple[Path, list[str]]]) -> list[str]:
    """Project imports naming no theory in `src/`.

    Silently skipping these would make the reachability walk below stop early
    and report success for a route it never actually followed, so they are a
    hard failure rather than a gap. Imports from HOL, the AFP and the vendored
    `TD` solver are outside this tree and are not checked.
    """
    out = []
    for name, (path, imports) in sorted(index.items()):
        for token in imports:
            session, _, bare = token.rpartition(".")
            if session and not session.startswith(PROJECT_SESSION):
                continue
            if bare in EXTERNAL_BARE or bare in index:
                continue
            out.append(f"{path.relative_to(REPO)}: import {token!r} names no theory under src/")
    return out


def main() -> int:
    index = theories()
    forbidden = {n for n, (p, _) in index.items() if FORBIDDEN in p.parents}
    if not forbidden:
        print(f"check_relational_boundary: no theories under {FORBIDDEN.relative_to(REPO)}")
        return 1

    dangling = unresolved(index)
    if dangling:
        print("check_relational_boundary: unresolved project imports (reachability is unreliable)")
        for d in dangling:
            print(f"  {d}")
        return 1

    failures: list[str] = []
    for name, (path, _) in sorted(index.items()):
        if RELATIONAL not in path.parents:
            continue
        seen: set[str] = set()
        stack = [(name, [])]
        while stack:
            current, trail = stack.pop()
            if current in seen:
                continue
            seen.add(current)
            if current in forbidden and current != name:
                route = " -> ".join(trail + [current])
                failures.append(f"{path.relative_to(REPO)}: reaches {current} via {route}")
                continue
            entry = index.get(current)
            if entry:
                stack.extend((i.rpartition(".")[2], trail + [current]) for i in entry[1])

    if failures:
        print("check_relational_boundary: relational theories reach pointwise-store theories")
        for f in failures:
            print(f"  {f}")
        print(
            "\nA relational carrier cannot be decomposed variable by variable, so a theory\n"
            "fixing a 'vname => 'a' store has no meaning for it. Either the import is a\n"
            "mistake, or the theory it reaches is not actually non-relational and belongs\n"
            "outside Base/Nonrelational/."
        )
        return 1

    checked = sum(1 for _, (p, _) in index.items() if RELATIONAL in p.parents)
    noun = "theory reaches" if checked == 1 else "theories reach"
    print(
        f"check_relational_boundary: {checked} relational {noun} "
        f"none of the {len(forbidden)} pointwise-store theories"
    )
    return 0


if __name__ == "__main__":
    sys.exit(main())
