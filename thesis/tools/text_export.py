#!/usr/bin/env python3
"""Print one section of the thesis as plain text, one paragraph per line.

Grammar checkers flag the source's line wraps and markup, and text copied
from the PDF loses paragraph breaks and hard hyphens. Typst's HTML export
renders the markup (citations, stats, verdicts) and keeps the paragraphs, so
this compiles the thesis to HTML with `text-export` set and reads the section
back from it.

    pixi run thesis-text abstract | pbcopy
    pixi run thesis-text 2.4
    pixi run thesis-text "Widening and narrowing" --captions

A section is chosen by its number, its label id or a substring of its title,
and runs to the next heading of the same or a higher level. Display math,
listings and figures are left out; `--captions` keeps figure captions.
"""

import argparse
import re
import subprocess
import sys
import tempfile
import unicodedata
from html.parser import HTMLParser
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
HEADING = re.compile(r"h([1-6])")
BLOCKS = {"p", "li", "figcaption", "blockquote"}
MATH_SELECTORS = re.compile("[\ufe00-\ufe0f]")


class Sections(HTMLParser):
    """Collects headings and the text blocks under each."""

    def __init__(self, captions: bool):
        super().__init__(convert_charrefs=True)
        self.captions = captions
        self.items: list[
            tuple[str, object]
        ] = []  # ("h", (level, id, title)) | ("p", text)
        self.skip = 0  # depth inside content left out
        self.buf: list[str] | None = None
        self.heading: tuple[int, str] | None = None
        self.math = 0

    def handle_starttag(self, tag, attrs):
        a = dict(attrs)
        if self.skip:
            self.skip += tag not in VOID
            return
        if (
            tag in {"pre", "svg", "nav"}
            or (tag == "math" and a.get("display") == "block")
            or (tag == "figure" and not self.captions)
        ):
            self.skip = 1
            return
        if tag == "math":
            self.math += 1
        if m := HEADING.fullmatch(tag):
            self.heading = (int(m[1]), a.get("id") or "")
            self.buf = []
        elif tag in BLOCKS and self.buf is None:
            self.buf = []

    def handle_endtag(self, tag):
        if self.skip:
            self.skip -= tag not in VOID
            return
        if tag == "math":
            self.math -= 1
        if self.buf is None:
            return
        text = re.sub(r"\s+", " ", "".join(self.buf)).strip()
        if HEADING.fullmatch(tag) and self.heading:
            self.items.append(("h", (*self.heading, text)))
            self.heading, self.buf = None, None
        elif tag in BLOCKS and not self.heading:
            if text:
                self.items.append(("p", text))
            self.buf = None

    def handle_data(self, data):
        if self.buf is not None and not self.skip:
            # Math italics (𝑖, 𝒳) read as misspellings to a grammar checker.
            if self.math:
                data = MATH_SELECTORS.sub("", unicodedata.normalize("NFKC", data))
            self.buf.append(data)


VOID = {"br", "img", "hr", "meta", "link", "input", "col", "wbr"}


def export_html(out: Path) -> None:
    # The build reads uncommitted data these scripts write; their logs must not
    # reach stdout, which is usually piped into the clipboard.
    for script in (["stats.py", "--write"], ["goblint_alignment.py"]):
        subprocess.run(
            [sys.executable, str(ROOT / "tools" / script[0]), *script[1:]],
            check=True,
            cwd=ROOT.parent,
            stdout=subprocess.DEVNULL,
        )
    subprocess.run(
        [
            "typst",
            "compile",
            "--root",
            str(ROOT),
            "--font-path",
            str(ROOT / "assets/fonts"),
            "--features",
            "html",
            "--format",
            "html",
            "--input",
            "text-export=1",
            str(ROOT / "thesis.typ"),
            str(out),
        ],
        check=True,
        stderr=subprocess.DEVNULL,
    )


def matches(query: str, ident: str, title: str) -> bool:
    q = query.lower()
    number = title.split(" ", 1)[0].rstrip(".")
    return q in (ident.lower(), number) or q in title.lower()


def main() -> int:
    ap = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    ap.add_argument(
        "section", help="number (2.4), label id (abstract) or title substring"
    )
    ap.add_argument("--captions", action="store_true", help="keep figure captions")
    args = ap.parse_args()

    with tempfile.TemporaryDirectory() as tmp:
        html = Path(tmp) / "thesis.html"
        export_html(html)
        parser = Sections(args.captions)
        parser.feed(html.read_text())

    out: list[str] = []
    level = None
    for kind, value in parser.items:
        if kind == "h":
            lvl, ident, title = value
            if level is None and matches(args.section, ident, title):
                level = lvl
            elif level is not None and lvl <= level:
                break
            if level is not None:
                out.append(title)
        elif level is not None:
            out.append(value)

    if level is None:
        print(f"text_export: no section matches {args.section!r}", file=sys.stderr)
        return 1
    print("\n\n".join(out))
    return 0


if __name__ == "__main__":
    sys.exit(main())
