#!/usr/bin/env python3
"""Repository figures for the thesis, measured rather than typed.

The thesis cites the size of the development and of the regression corpus.
``scripts/pages_stats.py`` already measures both for the site, so this reads
the same collection and writes its stable part, flattened to dotted keys, to
``thesis/shared/generated/stats.json``. Typst reads it through ``stat(key)``
(``thesis/lib/stats.typ``), which fails the build on an unknown key.

``--check`` fails when

  * the committed JSON no longer matches what the repository measures, or
  * a line of ``thesis/content`` mentions lines, theories, files, sessions,
    fixtures, cases, lemmas or the like next to a hand-typed number that does
    not go through ``stat()`` and is not in ``ALLOW`` below.

    python3 thesis/tools/stats.py --write
    python3 thesis/tools/stats.py --check
"""

from __future__ import annotations

import argparse
import json
import re
import sys
from pathlib import Path

REPO = Path(__file__).resolve().parents[2]
sys.path.insert(0, str(REPO / "scripts"))

import pages_stats  # noqa: E402

OUT = REPO / "thesis" / "shared" / "generated" / "stats.json"
CONTENT = REPO / "thesis" / "content"

# Figures that change with every commit or every day would make the committed
# JSON stale by construction; the thesis cites none of them.
VOLATILE = {"commit", "commit_sha", "date", "commits"}

# The gallery holds sample figures, not thesis content, and goes before submission.
SKIP_FILES = {"03-gallery.typ"}

# Nouns that make a nearby number a repository statistic.
STAT_NOUNS = re.compile(
    r"\b(lines?|theor(?:y|ies)|files?|sessions?|fixtures?|cases?|lemmas?|"
    r"definitions?|proofs?|groups?|directories|commits?|witnesses)\b",
    re.I,
)
# Two or more digits, a thousands-grouped numeral, or a percentage. Single
# digits are left out: they are parameters of examples (`length 2`), not counts.
NUMBER = re.compile(r"(?<![\w.,-])(?:\d{1,3}(?:,\d{3})+|\d{2,}|\d+%)(?![\w,]|\.\d)")

# Numbers on statistic-sounding lines that are not repository statistics.
# Keyed by (file, literal); each entry says what the number is. An entry that
# no longer matches anything is reported, so the list cannot outlive its text.
ALLOW: dict[tuple[str, str], str] = {
    # Goblint pull request and issue numbers, not counts.
    ("12-evaluation.typ", "1161"): "Goblint pull request number",
    # Figures quoted from cited external work, not repository counts.
    ("01-introduction.typ", "85,000"): "line count reported by bryant26munkres",
}


def measure() -> dict[str, int]:
    """The stable, flattened part of the site's stats collection."""
    stats = {k: v for k, v in pages_stats.collect().items() if k not in VOLATILE}
    return dict(sorted(pages_stats.flatten(stats)))


def render(stats: dict[str, int]) -> str:
    return json.dumps({"stats": stats}, indent=2) + "\n"


def _blank(match: re.Match) -> str:
    return " " * len(match.group(0))


def strip_line(line: str) -> str:
    """Blank out spans where a numeral is code, math, a name or a derived figure."""
    line = re.sub(r"//.*", _blank, line)
    line = re.sub(r"#stat[\w-]*\([^)]*\)", _blank, line)
    line = re.sub(r"`[^`]*`", _blank, line)
    line = re.sub(r"\$[^$]*\$", _blank, line)
    line = re.sub(r'"[^"]*"', _blank, line)
    line = re.sub(r"[@<][\w:.-]+>?", _blank, line)
    return line


def hand_typed(content: Path = CONTENT) -> tuple[list[str], set[tuple[str, str]]]:
    """Unallowed hand-typed statistics, and the allowlist entries that matched."""
    problems, used = [], set()
    for path in sorted(content.glob("*.typ")):
        if path.name in SKIP_FILES:
            continue
        lines, in_raw = [], False
        for raw in path.read_text(encoding="utf-8").split("\n"):
            # Fenced raw blocks are program text; their numerals are the program's.
            fences = raw.count("```")
            lines.append("" if in_raw or fences else strip_line(raw))
            if fences % 2:
                in_raw = not in_raw
        for i, line in enumerate(lines):
            # A number and its noun often straddle a line break.
            window = line + " " + (lines[i + 1] if i + 1 < len(lines) else "")
            if not STAT_NOUNS.search(window):
                continue
            for match in NUMBER.finditer(line):
                key = (path.name, match.group(0))
                if key in ALLOW:
                    used.add(key)
                    continue
                problems.append(
                    f"{path.relative_to(REPO)}:{i + 1}: {match.group(0)} looks like a "
                    'repository statistic; use #stat("key") from lib/stats.typ, '
                    "or add it to ALLOW in thesis/tools/stats.py with a reason"
                )
    return problems, used


def main() -> int:
    parser = argparse.ArgumentParser(
        description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter
    )
    mode = parser.add_mutually_exclusive_group(required=True)
    mode.add_argument("--write", action="store_true", help="regenerate stats.json")
    mode.add_argument("--check", action="store_true", help="fail on drift")
    args = parser.parse_args()

    absent = [r for r in pages_stats.VENDOR_SESSIONS if not (r / "ROOT").is_file()]
    if absent:
        for root in absent:
            print(
                f"thesis stats: {root.relative_to(REPO)} is not checked out; "
                "run `pixi run vendor-init` (CI: initialize the submodule)"
            )
        return 1

    stats = measure()
    text = render(stats)
    if args.write:
        OUT.parent.mkdir(parents=True, exist_ok=True)
        OUT.write_text(text, encoding="utf-8")
        print(f"thesis stats: wrote {len(stats)} figure(s) to {OUT.relative_to(REPO)}")
        return 0

    committed = (
        json.loads(OUT.read_text(encoding="utf-8"))["stats"] if OUT.is_file() else {}
    )
    drift = [
        f"{OUT.relative_to(REPO)}: {key} is {committed.get(key)}, "
        f"repository measures {stats.get(key)}"
        for key in sorted(stats.keys() | committed.keys())
        if committed.get(key) != stats.get(key)
    ]
    typed, used = hand_typed()
    problems = drift + typed
    problems += [
        f"thesis/tools/stats.py: ALLOW entry {key} matches nothing; remove it"
        for key in sorted(ALLOW.keys() - used)
    ]

    for problem in problems:
        print(problem)
    print(f"thesis stats: {len(stats)} figure(s), {len(problems)} problem(s)")
    # Last line, so it stays visible under a long drift list in hook output.
    if drift:
        print("thesis stats: stats.json is stale; run `pixi run thesis-stats-write`")
    return 1 if problems else 0


if __name__ == "__main__":
    raise SystemExit(main())
