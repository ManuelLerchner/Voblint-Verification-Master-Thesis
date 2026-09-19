#!/usr/bin/env python3
"""Check that every Isabelle name the site names is also linked from it.

`check_pages_links.py` checks that the links a page carries resolve, and
`check_theory_anchors.py` checks that an anchor's locale qualifier is right.
Neither notices the opposite failure: a theory name set in `<code>`, looking for
all the world like a term of art the reader could look up, that the page never
links anywhere. A reader meeting `classify_proved` has no way to reach it.

A name counts as linked when the page links to its anchor *somewhere* -- the
link often sits beside the `<code>` ("in the formalization"), or on a metro-map
station, rather than wrapping it. Linking the first mention is enough; later
mentions read better bare.

Only names that exist in `src/` or `vendor/` are required to be linked, so
ordinary snake_case prose in a `<code>` costs nothing.

Usage: python3 scripts/check_pages_terms.py [--verbose]
"""

import argparse
import html
import re
import subprocess
import sys
from pathlib import Path

REPO = Path(__file__).resolve().parent.parent
PAGES = REPO / "pages"
IDENT = re.compile(r"[a-z][A-Za-z0-9_']*")
# Isabelle's own commands and HOL names: real in the sources, but the reader is
# not being pointed at a Voblint definition, so a link would mislead.
EXEMPT = {"export_code", "module_name", "code_unfold", "by_eval"}
# Isabelle renders a datatype's selectors on the datatype's own anchor and gives
# them none of their own, so `#LTR_Def.ltr|type` is where `ltr_caller` lives and a
# per-selector anchor would 404. Checked against build/isabelle-html.
SELECTORS_ON_THEIR_DATATYPE = {"ltr_caller", "ltr_callee", "ltr_current"}
EXEMPT |= SELECTORS_ON_THEIR_DATATYPE


def named_in(text):
    """Identifiers the page sets in <code>, which is how it marks a term of art."""
    for match in re.finditer(r"<code[^>]*>(.*?)</code>", text, re.S):
        word = html.unescape(re.sub(r"<[^>]+>", "", match.group(1))).strip()
        if IDENT.fullmatch(word) and "_" in word:
            yield word, text[: match.start()].count("\n") + 1


def linked_in(text):
    """Names the page links to, by theory anchor or by a figure's data-name."""
    names = set()
    for anchor in re.findall(r"#[A-Za-z_0-9]+\.([A-Za-z_0-9'.]+)%7C", text):
        names.add(anchor)
        names.add(anchor.split(".")[-1])
    names.update(re.findall(r'data-name="([A-Za-z_0-9\']+)"', text))
    return names


def declared(name):
    found = subprocess.run(
        ["rg", "-l", "-w", name, "src/", "vendor/"],
        capture_output=True,
        text=True,
        cwd=REPO,
    )
    return bool(found.stdout.strip())


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument(
        "--verbose", action="store_true", help="list every name checked"
    )
    args = parser.parse_args()

    missing, checked = [], 0
    for page in sorted(PAGES.glob("*.html")):
        raw = page.read_text(encoding="utf-8")
        body = re.sub(r"<script.*?</script>", " ", raw, flags=re.S)
        links = linked_in(raw)
        first = {}
        for name, line in named_in(body):
            first.setdefault(name, line)
        for name, line in sorted(first.items()):
            if name in EXEMPT or name in links:
                continue
            checked += 1
            if declared(name):
                missing.append(
                    f"{page.relative_to(REPO)}:{line}: {name} is never linked"
                )
            elif args.verbose:
                print(f"  {page.relative_to(REPO)}:{line}: {name} (not a name in src/)")

    for problem in missing:
        print(problem)
    print(
        f"check_pages_terms: {checked} unlinked name(s) examined, {len(missing)} missing a link"
    )
    return 1 if missing else 0


if __name__ == "__main__":
    sys.exit(main())
