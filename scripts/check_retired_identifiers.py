#!/usr/bin/env python3
"""Fail when a `.thy` file still names an identifier this tree has retired.

Isabelle rejects an unknown constant in a term, but not everywhere. Inside
`assumes`, `fixes`, and theorem statements an unknown lowercase identifier is
a legal free variable, so a locale whose assumption cites a deleted constant
keeps building -- while that assumption silently stops constraining anything.
That is invisible to the batch build, and it is what `scripts/` cannot infer
by scanning declarations, because the name is gone from the tree by then.

So the retired names are listed explicitly, in `retired_identifiers.txt`, and
this checks that none of them came back. Matching is whole-word: a retired
`caller_cont` would not match a live `dgs_caller_cont`.

Run over the whole tree, or over the paths given as arguments (the pre-commit
hook passes staged files).
"""

from __future__ import annotations

import re
import sys
from pathlib import Path

REPO = Path(__file__).resolve().parent.parent
LIST = Path(__file__).resolve().parent / "retired_identifiers.txt"


def retired() -> list[str]:
    names = []
    for line in LIST.read_text().splitlines():
        line = line.strip()
        if line and not line.startswith("#"):
            names.append(line)
    return names


def main(argv: list[str]) -> int:
    names = retired()
    if not names:
        print(f"check_retired_identifiers: {LIST.name} lists no names",
              file=sys.stderr)
        return 1

    if argv:
        paths = [Path(a) for a in argv if a.endswith(".thy")]
    else:
        paths = sorted((REPO / "src").rglob("*.thy"))
    if not paths:
        print("check_retired_identifiers: no .thy files to check")
        return 0

    pattern = re.compile(
        r"(?<![A-Za-z0-9_'])(" + "|".join(map(re.escape, names)) + r")(?![A-Za-z0-9_'])")

    found: dict[str, list[str]] = {}
    for path in paths:
        try:
            text = path.read_text(errors="ignore")
        except OSError:
            continue
        for m in pattern.finditer(text):
            line = text.count("\n", 0, m.start()) + 1
            try:
                rel = path.relative_to(REPO)
            except ValueError:
                rel = path
            found.setdefault(m.group(1), []).append(f"{rel}:{line}")

    if found:
        print(f"check_retired_identifiers: {len(found)} retired identifier(s) "
              "are still referenced:")
        for name in sorted(found):
            print(f"  {name}")
            for site in sorted(set(found[name])):
                print(f"      {site}")
        print()
        print(f"These names were deliberately removed (see {LIST.name}). Use the "
              "replacement, or -- if the name is being reused on purpose -- "
              "delete its line from that list in the same commit.")
        return 1

    print(f"check_retired_identifiers: none of the {len(names)} retired "
          "identifiers is referenced")
    return 0


if __name__ == "__main__":
    sys.exit(main(sys.argv[1:]))
