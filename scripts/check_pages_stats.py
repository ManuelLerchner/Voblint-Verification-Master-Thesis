#!/usr/bin/env python3
"""Check that the site's repository figures are derived, not written by hand.

`scripts/pages_stats.py` measures the repository at site-build time and the page
fills every `[data-stat]` from it. Two ways that goes wrong, both silent:

  * a figure typed straight into the prose, which no build ever refreshes;
  * a `[data-stat]` whose literal fallback -- what a source checkout renders --
    has drifted from what the repository now measures.

This checks both. It needs no Isabelle: pages_stats.py reads the sources.
"""

import argparse
import re
import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))

import pages_stats
import vimp_fixture

REPO = Path(__file__).resolve().parent.parent
PAGES = REPO / "pages"
# Below this, a bare numeral is far more likely to be a coordinate, a year or a
# quantity of the reader's own than one of our measurements.
MIN = 1000


def flatten(node, prefix=""):
    for key, value in node.items():
        if isinstance(value, dict):
            yield from flatten(value, f"{prefix}{key}.")
        elif isinstance(value, int):
            yield f"{prefix}{key}", value


def strip(text):
    """Blank out spans where a numeric match means nothing, keeping offsets."""
    for pattern in (r"<script.*?</script>", r"<svg.*?</svg>", r"<style.*?</style>"):
        text = re.sub(pattern, lambda m: " " * len(m.group(0)), text, flags=re.S)
    return re.sub(r'href="[^"]*"', lambda m: " " * len(m.group(0)), text)


def corpus_problems(stats):
    """Three counts that must agree, and the filenames when they do not.

    `corpus.cases` is a figure on the page, so a silent disagreement between what
    the site reports, what is on disk and what the fixture reader can actually
    read would show up as a number nobody can source. Reporting the set
    difference by name means the next discrepancy explains itself instead of
    being archaeology.
    """
    root = pages_stats.CORPUS_DIR
    discovered = {path.relative_to(root) for path in root.rglob("*.vimp")}
    readable, unreadable = set(), {}
    for name in sorted(discovered):
        try:
            if vimp_fixture.param_args(root / name) is None:
                unreadable[name] = "no // PARAM: header"
            else:
                readable.add(name)
        except Exception as error:  # noqa: BLE001 - reported, not handled
            unreadable[name] = f"{type(error).__name__}: {error}"

    problems = []
    if stats["corpus"]["cases"] != len(discovered):
        problems.append(
            f"corpus.cases reports {stats['corpus']['cases']} but "
            f"{len(discovered)} .vimp file(s) are on disk under {root.relative_to(REPO)}"
        )
    for name, why in sorted(unreadable.items()):
        problems.append(
            f"{(root / name).relative_to(REPO)}: counted but not readable ({why})"
        )
    return problems


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument(
        "--fix",
        action="store_true",
        help="rewrite stale [data-stat] fallbacks in place (hand-written figures are never "
        "rewritten: those need a data-stat around them, which is a judgement about the prose)",
    )
    args = parser.parse_args()
    stats = pages_stats.collect()
    values = {k: v for k, v in flatten(stats) if v >= MIN}
    problems = [] if args.fix else corpus_problems(stats)

    fixed = 0

    for page in sorted(PAGES.glob("*.html")):
        raw = page.read_text(encoding="utf-8")
        text = strip(raw)

        for key, value in values.items():
            grouped = f"{value:,}"
            for match in re.finditer(
                rf"(?<![\d,.]){re.escape(grouped)}(?![\d,.])", text
            ):
                before = text[max(0, match.start() - 120) : match.start()]
                if "data-stat" in before[-90:]:
                    continue
                line = text[: match.start()].count("\n") + 1
                problems.append(
                    f"{page.relative_to(REPO)}:{line}: {grouped} is {key}; "
                    f'write it as <span data-stat="{key}">{grouped}</span>'
                )

        for match in re.finditer(r'data-stat="([^"]+)"[^>]*>([^<]*)<', raw):
            key, literal = match.group(1), match.group(2).strip()
            current = key.split(".")
            value = stats
            for part in current:
                value = value.get(part) if isinstance(value, dict) else None
            if value is None or not isinstance(value, int):
                continue
            if literal and literal.replace(",", "") != str(value):
                line = raw[: match.start()].count("\n") + 1
                if args.fix:
                    raw = raw[: match.start(2)] + f"{value:,}" + raw[match.end(2) :]
                    fixed += 1
                    print(
                        f"{page.relative_to(REPO)}:{line}: {key} {literal} -> {value:,}"
                    )
                    break
                problems.append(
                    f"{page.relative_to(REPO)}:{line}: fallback for {key} reads {literal}, "
                    f"repository measures {value:,}"
                )

        if args.fix and raw != page.read_text(encoding="utf-8"):
            page.write_text(raw, encoding="utf-8")

    for problem in problems:
        print(problem)
    if args.fix:
        print(f"check_pages_stats: {fixed} fallback(s) refreshed; re-run to confirm")
        return 0

    print(
        f"check_pages_stats: {len(values)} derived figure(s), "
        f"{stats['corpus']['cases']} corpus case(s), {len(problems)} problem(s)"
    )
    return 1 if problems else 0


if __name__ == "__main__":
    raise SystemExit(main())
