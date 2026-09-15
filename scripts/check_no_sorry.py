#!/usr/bin/env python3
"""Reject unfinished proofs in the project and vendored TD theories.

The check is intentionally independent of Isabelle so it can fail before a
session build.  It scans only ``*.thy`` files below ``src`` and
``vendor/td-verification``; editor backups such as ``Foo.thy~`` are therefore
outside its input.  Comments, strings, and document prose are masked before
matching, so a discussion of ``sorry`` is not mistaken for a proof command.
"""

from __future__ import annotations

import re
import sys
from dataclasses import dataclass
from pathlib import Path

from extract_definitions import mask_comments_and_strings
from thy_stats import mask_docs

REPO = Path(__file__).resolve().parent.parent
SOURCE_ROOTS = (REPO / "src", REPO / "vendor" / "td-verification")
PROOF_HOLE_RE = re.compile(r"(?<![A-Za-z0-9_'])(sorry|oops)(?![A-Za-z0-9_'])")


@dataclass(frozen=True)
class ProofHole:
    path: Path
    line: int
    command: str


def theory_paths(roots: tuple[Path, ...] = SOURCE_ROOTS) -> list[Path]:
    """Return theory sources, excluding backup files by exact suffix."""
    return sorted(path for root in roots for path in root.rglob("*.thy"))


def scan(path: Path) -> list[ProofHole]:
    text = path.read_text(encoding="utf-8", errors="replace")
    source = mask_docs(text, mask_comments_and_strings(text))
    holes = []
    for match in PROOF_HOLE_RE.finditer(source):
        holes.append(
            ProofHole(path, source.count("\n", 0, match.start()) + 1, match.group(1))
        )
    return holes


def display_path(path: Path) -> Path:
    try:
        return path.relative_to(REPO)
    except ValueError:
        return path


def main(argv: list[str]) -> int:
    paths = [Path(arg) for arg in argv] if argv else theory_paths()
    holes = [hole for path in paths if path.suffix == ".thy" for hole in scan(path)]
    if holes:
        print("check_no_sorry: unfinished proof commands found:")
        for hole in holes:
            print(f"{display_path(hole.path)}:{hole.line}: {hole.command}")
        return 1

    print(f"check_no_sorry: {len(paths)} theory files, no sorry/oops commands")
    return 0


if __name__ == "__main__":
    sys.exit(main(sys.argv[1:]))
