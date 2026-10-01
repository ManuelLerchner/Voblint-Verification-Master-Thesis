#!/usr/bin/env python3
"""Checks the theory anchors the explainer's scripts build, with no build.

An anchor into a rendered theory is `<Theory>.<locale>.<name>|<kind>`, and the
locale part is the trap: a constant declared inside `context dg_analysis` is
`Theory.dg_analysis.name`, not `Theory.name`. Both spellings name something
real, so nothing reading the sources notices; the page loads and the anchor
silently does nothing.

`isar check --group links` decides this for the links written in the HTML
pages (the `theory-anchors-check` task runs it first). The figure scripts
assemble their links at run time, `isaConst("Session", "Theory", "name")`, so
this requires each such link to be the `url` isar-tools gives a constant.

Usage: python3 scripts/check_theory_anchors.py
"""

from __future__ import annotations

import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))
from check_pages_links import collected, split  # noqa: E402
from isar_json import names, project_directories  # noqa: E402


def main() -> int:
    urls = {row["url"] for d in project_directories() for row in names(d) if row["url"]}
    problems, checked = [], 0
    for url, sources in sorted(collected().items()):
        scripts = sorted(s for s in sources if s.endswith(".js"))
        if not scripts or not split(url)[1]:
            continue
        checked += 1
        if url not in urls:
            problems.append(
                f"{url} ({', '.join(scripts)}): no constant has this anchor"
            )
    for p in problems:
        print(p, file=sys.stderr)
    print(f"checked {checked} theory anchors built by the explainer's scripts")
    return 1 if problems else 0


if __name__ == "__main__":
    sys.exit(main())
