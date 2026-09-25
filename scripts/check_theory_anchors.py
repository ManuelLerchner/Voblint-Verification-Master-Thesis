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

The qualifier does not need the render. It is where the declaration sits:
`context <name>` and `locale <name>` open one, an anonymous `context` opens
none, and `end` closes. This reads that off the theory and compares it with what
the link claims.

Deliberately narrow, because guessing Isabelle's name space wrongly is worse
than not guessing. A link is checked only when its base name is declared exactly
once by a `lemma`/`theorem`/`corollary`/`proposition`/`lemmas` command; anything
else -- a `definition`'s derived `_def`, a name from an interpretation, a
duplicate -- is left to the rendered-site check. It reports what it skipped.

Usage: python3 scripts/check_theory_anchors.py [--verbose]
"""

from __future__ import annotations

import re
import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))
from check_pages_links import collected, split  # noqa: E402

REPO = Path(__file__).resolve().parent.parent
SRC = REPO / "src"

THEORY_LINK = re.compile(r"^Voblint/(?P<session>[^/]+)/(?P<theory>[^/]+)\.html$")
FACT = re.compile(
    r"^\s*(?:lemma|theorem|corollary|proposition|lemmas)\s+([A-Za-z][A-Za-z0-9_']*)\s*[:\[]",
    re.M,
)
# `context <name>` / `locale <name> = ...` open a named scope; a bare `context`
# (fixes/assumes only) opens an anonymous one. Both are closed by `end`.
OPEN_NAMED = re.compile(r"^(?:context|locale|class)\s+([A-Za-z][A-Za-z0-9_']*)")
OPEN_ANON = re.compile(r"^context\b\s*$")
CLOSE = re.compile(r"^end\b")
COMMENT = re.compile(r"\(\*.*?\*\)", re.S)


def strip_comments(text: str) -> str:
    """Blank out comments, keeping every newline so line numbers stay true."""
    return COMMENT.sub(lambda m: "\n" * m.group(0).count("\n"), text)


def theory_files() -> dict[str, Path]:
    out: dict[str, list[Path]] = {}
    for thy in SRC.rglob("*.thy"):
        out.setdefault(thy.stem, []).append(thy)
    return {k: v[0] for k, v in out.items() if len(v) == 1}


def qualifier_of(text: str, line_no: int) -> str | None:
    """The locale prefix a declaration on `line_no` is rendered under."""
    stack: list[str | None] = []
    for i, line in enumerate(text.split("\n"), start=1):
        if i >= line_no:
            break
        if CLOSE.match(line):
            if stack:
                stack.pop()
            continue
        m = OPEN_NAMED.match(line)
        if m:
            stack.append(m.group(1))
            continue
        if OPEN_ANON.match(line):
            stack.append(None)
    named = [s for s in stack if s]
    return ".".join(named) if named else None


def main() -> int:
    verbose = "--verbose" in sys.argv
    files = theory_files()
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
        rest = name[len(theory) + 1 :]
        base = rest.rsplit(".", 1)[-1]
        claimed = rest[: -(len(base) + 1)] if "." in rest else None

        thy = files.get(theory)
        if thy is None:
            skipped.append(f"{theory}: no unique .thy under src/")
            continue
        text = strip_comments(thy.read_text())
        # start(1), not start(): `^\s*` can swallow a preceding blank line.
        hits = [mm.start(1) for mm in FACT.finditer(text) if mm.group(1) == base]
        if len(hits) != 1:
            skipped.append(
                f"{theory}.{base}: {len(hits)} plain declarations; left to the site check"
            )
            continue
        line_no = text.count("\n", 0, hits[0]) + 1
        actual = qualifier_of(text, line_no)
        checked += 1
        if actual != claimed:
            problems.append(
                f"{url} ({', '.join(sorted(sources))}): anchor says "
                f"'{theory}.{rest}', but {base} is declared at {thy.relative_to(REPO)}:{line_no} "
                f"{'inside ' + actual if actual else 'at theory level'}, so the rendered id is "
                f"'{theory}.{(actual + '.' if actual else '')}{base}'"
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
