#!/usr/bin/env python3
"""Checks a site link's theory anchor against the theory source, with no build.

An anchor into a rendered theory is `<Theory>.<locale>.<name>|<kind>`, and the
locale part is the trap: a fact stated inside `context routed_dg_analysis` is
`Routed_Live_Keys.routed_dg_analysis.entry_state_lookup_sound_of_terminates`,
not `Routed_Live_Keys.entry_state_lookup_sound_of_terminates`. Both spellings
name a real fact in a real file, so nothing reading the sources notices; the
page loads and the anchor silently does nothing.

`check_pages_links.py --sources` cannot decide this. Anchors exist only in
rendered HTML, so it compares against `build/isabelle-html` if a working copy
happens to have one and warns rather than fails, which leaves the deciding check
in `pages-site` -- the last CI job, after the HTML build, both PDFs and site
assembly. Two links reached the deployed site that way.

The qualifier does not need the render. `isar project names` (isar-tools) reads
each declaration's scope off the theory: an `(in loc)` target, else the
innermost open `locale`/`class`/`context NAME` block. This compares that with
what the link claims.

Deliberately narrow, because guessing Isabelle's name space wrongly is worse
than not guessing. A link is checked only when its base name is declared exactly
once in its theory, by a fact command (`lemma`, `theorem`, `lemmas`, ...);
anything else -- a `definition`'s derived `_def`, a name from an
interpretation, a duplicate -- is left to the rendered-site check. It reports
what it skipped.

Usage: python3 scripts/check_theory_anchors.py [--verbose]
"""

from __future__ import annotations

import json
import re
import subprocess
import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))
from check_pages_links import collected, split  # noqa: E402

REPO = Path(__file__).resolve().parent.parent

THEORY_LINK = re.compile(r"^Voblint/(?P<session>[^/]+)/(?P<theory>[^/]+)\.html$")


def declared_facts() -> dict[tuple[str, str], list[str]]:
    """(theory, base name) -> qualified names of the facts declaring it."""
    run = subprocess.run(
        ["isar", "project", "names", "--kind", "fact", "--format", "json", str(REPO)],
        capture_output=True,
        text=True,
        check=False,
    )
    if run.returncode != 0:
        sys.exit(f"isar project names failed:\n{run.stderr}")
    facts: dict[tuple[str, str], list[str]] = {}
    for row in json.loads(run.stdout)["names"]:
        qualified = row["name"]
        theory, _, rest = qualified.partition(".")
        facts.setdefault((theory, rest.rsplit(".", 1)[-1]), []).append(qualified)
    return facts


def main() -> int:
    verbose = "--verbose" in sys.argv
    facts = declared_facts()
    problems, checked, skipped = [], 0, []

    for url, sources in sorted(collected().items()):
        path, fragment = split(url)
        m = THEORY_LINK.match(path)
        if not m or not fragment:
            continue
        # A session-qualified theory (`TD.Update_rules`) renders its ids under the base name.
        theory = m.group("theory").rsplit(".", 1)[-1]
        name = fragment.split("|", 1)[0]
        if not name.startswith(f"{theory}."):
            problems.append(
                f"{url} ({', '.join(sorted(sources))}): anchor does not start with '{theory}.'"
            )
            continue
        base = name.rsplit(".", 1)[-1]
        hits = facts.get((theory, base), [])
        if len(hits) != 1:
            skipped.append(
                f"{theory}.{base}: {len(hits)} fact declarations; left to the site check"
            )
            continue
        checked += 1
        if hits[0] != name:
            problems.append(
                f"{url} ({', '.join(sorted(sources))}): anchor says '{name}', "
                f"but the theory declares it as '{hits[0]}'"
            )

    for p in problems:
        print(p, file=sys.stderr)
    if verbose:
        for s in sorted(set(skipped)):
            print(f"skipped {s}")
    print(f"checked {checked} theory anchors, skipped {len(set(skipped))}")
    return 1 if problems else 0


if __name__ == "__main__":
    sys.exit(main())
