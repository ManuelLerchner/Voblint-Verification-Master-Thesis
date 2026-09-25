#!/usr/bin/env python3
"""Check that the site's repository figures are derived, not written by hand.

`scripts/pages_stats.py` measures the repository, and the site build writes
every `[data-stat]` figure into the published HTML from that measurement
(`--fill`). The source keeps only the neutral fallback, which cannot drift.

This checks that no figure is typed straight into the prose, where no build
refreshes it; that every `[data-stat]` names a measured figure and holds the
fallback; and that the corpus counts agree. It needs no Isabelle:
pages_stats.py reads the sources.
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
    argparse.ArgumentParser(description=__doc__).parse_args()

    # collect() reads the vendored solver, so without the submodule it dies deep
    # inside session_graph with a FileNotFoundError. pages_stats.py refuses to
    # guess a solver count rather than publish a wrong one; say the same thing
    # here, in one line, instead of a traceback.
    absent = [
        root for root in pages_stats.VENDOR_SESSIONS if not (root / "ROOT").is_file()
    ]
    if absent:
        for root in absent:
            print(
                f"check_pages_stats: {root.relative_to(REPO)} is not checked out; "
                "run `pixi run vendor-init` (CI: initialize the submodule)"
            )
        return 1

    stats = pages_stats.collect()
    values = {k: v for k, v in pages_stats.flatten(stats) if v >= MIN}
    problems = corpus_problems(stats)

    for page in sorted(PAGES.glob("*.html")):
        raw = page.read_text(encoding="utf-8")
        text = strip(raw)

        for key, value in values.items():
            grouped = f"{value:,}"
            for match in re.finditer(
                rf"(?<![\d,.]){re.escape(grouped)}(?![\d,.])", text
            ):
                line = text[: match.start()].count("\n") + 1
                problems.append(
                    f"{page.relative_to(REPO)}:{line}: {grouped} is {key}; "
                    f'write it as <span data-stat="{key}">{pages_stats.FALLBACK}</span>'
                )

        # The site build writes every figure (pages_stats.py --fill), so the source
        # holds only the neutral fallback: a number here would go stale unnoticed.
        for match in pages_stats.DATA_STAT.finditer(raw):
            key, literal = match.group(2), match.group(3).strip()
            line = raw[: match.start()].count("\n") + 1
            where = f"{page.relative_to(REPO)}:{line}"
            value = pages_stats.lookup(stats, key)
            if value is None or isinstance(value, dict):
                problems.append(f"{where}: data-stat={key!r} names no measured figure")
            elif literal != pages_stats.FALLBACK:
                problems.append(
                    f"{where}: {key} reads {literal!r}; the source keeps the fallback "
                    f"{pages_stats.FALLBACK!r} and the site build writes the figure"
                )

    for problem in problems:
        print(problem)
    print(
        f"check_pages_stats: {len(values)} derived figure(s), "
        f"{stats['corpus']['cases']} corpus case(s), {len(problems)} problem(s)"
    )
    return 1 if problems else 0


if __name__ == "__main__":
    raise SystemExit(main())
