#!/usr/bin/env python3
"""Check that every Isabelle name the site names is also linked from it.

`check_pages_links.py` checks that the links a page carries resolve, and
`check_theory_anchors.py` checks that an anchor's locale qualifier is right.
Neither notices the opposite failure: a theory name set in `<code>`, looking for
all the world like a term of art the reader could look up, that the page never
links anywhere. A reader meeting `classify_proved` has no way to reach it.

Two rules, because a name can go unreachable in two ways.

*Never linked.* A name declared in `src/` or `vendor/`, set in `<code>`, that the
page links nowhere. Ordinary snake_case prose costs nothing, since it is not a
declaration.

*Not linked here.* A name the page does link somewhere, set in `<code>` in a
section that never links it. This is the one a page-wide rule misses: the link
sits ten screens up under a different heading, so the reader in front of the
name still cannot reach it. The first mention in a section must be linked;
later ones read better bare. A name the page links nowhere at all is prose or a
program variable -- `main`, `f`, `interval` -- and is left alone, which is what
keeps this rule free of false positives.

A name counts as linked when the link sits anywhere in the same section, not
necessarily around the `<code>`: it is often beside it ("in the formalization")
or on a metro-map station.

Usage: python3 scripts/check_pages_terms.py [--verbose]
"""

import argparse
import html
import re
import sys
from collections import defaultdict
from pathlib import Path

REPO = Path(__file__).resolve().parent.parent
PAGES = REPO / "pages"
IDENT = re.compile(r"[a-z][A-Za-z0-9_']*")
SECTION = re.compile(r'<section[^>]*\bid="([^"]+)"')
# Isabelle's own commands and HOL names: real in the sources, but the reader is
# not being pointed at a Voblint definition, so a link would mislead.
EXEMPT = {"export_code", "module_name", "code_unfold", "by_eval"}
# Isabelle renders a datatype's selectors on the datatype's own anchor and gives
# them none of their own, so `#LTR_Def.ltr|type` is where `ltr_caller` lives and a
# per-selector anchor would 404. Checked against build/isabelle-html.
SELECTORS_ON_THEIR_DATATYPE = {"ltr_caller", "ltr_callee", "ltr_current"}
EXEMPT |= SELECTORS_ON_THEIR_DATATYPE

COMMAND = (
    r"definition|fun|function|primrec|abbreviation|datatype|codatatype"
    r"|type_synonym|inductive|inductive_set|lemma|theorem|corollary"
    r"|proposition|lemmas|locale|class|record"
)
# A type constructor carries its arguments before its name: `datatype ('a, 'b) t`.
DECLARATION = re.compile(
    rf"^\s*(?:{COMMAND})\s+(?:\([^()\n]*\)\s*|'[A-Za-z][A-Za-z0-9_']*\s*)?"
    r"([a-z][A-Za-z0-9_']*)",
    re.M,
)


def declared_names():
    """Names the theory sources declare, by command, without a build."""
    names = set()
    for root in (REPO / "src", REPO / "vendor"):
        if not root.is_dir():
            continue
        for thy in root.rglob("*.thy"):
            names.update(
                DECLARATION.findall(thy.read_text(encoding="utf-8", errors="replace"))
            )
    return names


def strip_scripts(text):
    """Blank out inline scripts, keeping every newline so line numbers stay true."""
    return re.sub(
        r"<script.*?</script>",
        lambda m: "\n" * m.group(0).count("\n"),
        text,
        flags=re.S,
    )


def section_index(text):
    """A lookup from offset to the id of the section it sits in."""
    starts = [(m.start(), m.group(1)) for m in re.finditer(SECTION, text)]

    def at(offset):
        found = "(page)"
        for start, name in starts:
            if start > offset:
                break
            found = name
        return found

    return at


def named_in(text):
    """Identifiers the page sets in <code>, which is how it marks a term of art."""
    for match in re.finditer(r"<code[^>]*>(.*?)</code>", text, re.S):
        word = html.unescape(re.sub(r"<[^>]+>", "", match.group(1))).strip()
        if IDENT.fullmatch(word):
            yield word, match.start()


def linked_in(text):
    """Names the page links to, by theory anchor or by a figure's data-name, with
    the offset of each link."""
    for match in re.finditer(r"#[A-Za-z_0-9]+\.([A-Za-z_0-9'.]+)%7C", text):
        qualified = match.group(1)
        yield qualified, match.start()
        yield qualified.split(".")[-1], match.start()
    for match in re.finditer(r'data-name="([A-Za-z_0-9\']+)"', text):
        yield match.group(1), match.start()


def at(page, body, offset, name, why):
    """One report line, with the offset resolved against the page's own text."""
    line = body[:offset].count("\n") + 1
    return f"{page.relative_to(REPO)}:{line}: {name} {why}"


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument(
        "--verbose", action="store_true", help="list every name checked"
    )
    args = parser.parse_args()

    # Without the submodule a name declared only in the vendored solver
    # (strategy_tree, eqsT, part_post_solution) reads as ordinary prose. The
    # check still works, it just covers less, so say so.
    if not (REPO / "vendor" / "td-verification" / "ROOT").is_file():
        print(
            "check_pages_terms: vendor/td-verification is not checked out, so names "
            "declared only there are not required to be linked"
        )

    sources = declared_names()
    missing, checked = [], 0
    for page in sorted(PAGES.glob("*.html")):
        raw = page.read_text(encoding="utf-8")
        body = strip_scripts(raw)
        section_at = section_index(body)

        anywhere, here = set(), defaultdict(set)
        for name, offset in linked_in(body):
            anywhere.add(name)
            here[section_at(offset)].add(name)

        first_on_page, first_in_section = {}, {}
        for name, offset in named_in(body):
            first_on_page.setdefault(name, offset)
            first_in_section.setdefault((section_at(offset), name), offset)

        for name, offset in sorted(first_on_page.items(), key=lambda kv: kv[1]):
            if name in EXEMPT or name in anywhere or "_" not in name:
                continue
            checked += 1
            if name in sources:
                missing.append(at(page, body, offset, name, "is never linked"))
            elif args.verbose:
                print("  " + at(page, body, offset, name, "(not a name in src/)"))

        for (section, name), offset in sorted(
            first_in_section.items(), key=lambda kv: kv[1]
        ):
            if name in EXEMPT or name not in anywhere or name in here[section]:
                continue
            checked += 1
            missing.append(
                at(
                    page,
                    body,
                    offset,
                    name,
                    f"is linked elsewhere but not in section '{section}'",
                )
            )

    for problem in missing:
        print(problem)
    print(
        f"check_pages_terms: {checked} unlinked name(s) examined, {len(missing)} missing a link"
    )
    return 1 if missing else 0


if __name__ == "__main__":
    sys.exit(main())
