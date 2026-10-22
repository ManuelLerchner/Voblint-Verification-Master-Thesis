"""Fail when the paper body exceeds the venue's page limit.

main.tex places \\label{paper:body-end} just before the bibliography, so the
page LaTeX records for it in the .aux file is the last page that counts.

  python paper/tools/pages.py   after a build into paper/_build/
"""

from __future__ import annotations

import re
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[2]
AUX = ROOT / "paper" / "_build" / "main.aux"
LABEL = "paper:body-end"
# ITP 2027: 16 pages excluding references.
LIMIT = 16


def main() -> int:
    if not AUX.exists():
        print(
            f"missing {AUX.relative_to(ROOT)}; build the paper first", file=sys.stderr
        )
        return 1
    match = re.search(
        rf"\\newlabel\{{{re.escape(LABEL)}\}}\{{\{{[^}}]*\}}\{{(\d+)\}}",
        AUX.read_text(),
    )
    if not match:
        print(f"no \\label{{{LABEL}}} in {AUX.relative_to(ROOT)}", file=sys.stderr)
        return 1
    last = int(match.group(1))
    if last > LIMIT:
        print(f"paper body ends on page {last}, limit is {LIMIT}", file=sys.stderr)
        return 1
    print(f"paper body ends on page {last} of {LIMIT}")
    return 0


if __name__ == "__main__":
    sys.exit(main())
