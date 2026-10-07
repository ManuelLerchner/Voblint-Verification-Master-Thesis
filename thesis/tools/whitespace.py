#!/usr/bin/env python3
"""Warn about pages of the thesis PDF with a large blank stretch.

A figure or table that does not fit where it is placed moves to the next page
and leaves a gap behind it. Typst reports nothing, and the gap is easy to miss
in a long document. This renders every page, finds the longest run of blank
rows in the text area, and warns when it exceeds a fraction of that area.

The last page of a chapter or part may end early, so its trailing gap is not
reported. Front matter (no arabic page number) and pages with almost no text
(title, part and blank pages) are skipped.

Warnings only: the exit status is 0 unless --strict is given. Under GitHub
Actions each warning is also printed as an annotation.
"""

import argparse
import os
import re
import subprocess
import sys
import tempfile
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
PDF = ROOT / "Lerchner_Master_Thesis.pdf"
DPI = 36
# The text area between the running header and the page number, as fractions
# of the page height (A4, see lib/tum.typ).
BODY = (0.109, 0.891)
# A row is blank when every pixel is at least this light; light figure fills
# stay below it.
WHITE = 245
# A chapter title is set much larger than the running header.
TITLE_HEIGHT = 15.0
MIN_WORDS = 30

WORD = re.compile(
    r'<word xMin="[\d.]+" yMin="([\d.]+)" xMax="[\d.]+" yMax="([\d.]+)">([^<]*)</word>'
)
PAGE = re.compile(r"<page [^>]*>(.*?)</page>", re.S)


def words_per_page(pdf):
    out = subprocess.run(
        ["pdftotext", "-bbox", str(pdf), "-"],
        check=True,
        capture_output=True,
        text=True,
    ).stdout
    return [
        [(float(a), float(b), w) for a, b, w in WORD.findall(body)]
        for body in PAGE.findall(out)
    ]


def starts_chapter(words):
    """A chapter or part opens with a title far larger than body text."""
    return bool(words) and words[0][1] - words[0][0] > TITLE_HEIGHT


def read_pgm(path):
    data = path.read_bytes()
    # Header: magic, width, height, maxval, each separated by whitespace.
    fields, i = [], 0
    while len(fields) < 4:
        while data[i : i + 1].isspace():
            i += 1
        j = i
        while not data[j : j + 1].isspace():
            j += 1
        fields.append(data[i:j])
        i = j
    width, height = int(fields[1]), int(fields[2])
    pixels = data[i + 1 :]
    return width, height, pixels


def longest_blank(path, skip_trailing):
    width, height, pixels = read_pgm(path)
    top, bottom = int(BODY[0] * height), int(BODY[1] * height)
    blank = [
        min(pixels[r * width : (r + 1) * width]) >= WHITE for r in range(top, bottom)
    ]
    if skip_trailing:
        while blank and blank[-1]:
            blank.pop()
    best = run = start = best_start = 0
    for r, b in enumerate(blank):
        if b:
            if run == 0:
                start = r
            run += 1
            if run > best:
                best, best_start = run, start
        else:
            run = 0
    return best / (bottom - top), (best_start + top) / height


def main():
    ap = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    ap.add_argument("pdf", nargs="?", default=PDF, type=Path)
    ap.add_argument("--threshold", type=float, default=0.30)
    ap.add_argument(
        "--strict", action="store_true", help="exit 1 when a page is reported"
    )
    args = ap.parse_args()

    pages = words_per_page(args.pdf)
    gha = os.environ.get("GITHUB_ACTIONS") == "true"
    reported = 0
    with tempfile.TemporaryDirectory() as tmp:
        subprocess.run(
            ["pdftoppm", "-gray", "-r", str(DPI), str(args.pdf), f"{tmp}/p"], check=True
        )
        images = sorted(Path(tmp).glob("p-*.pgm"))
        for n, (img, words) in enumerate(zip(images, pages, strict=True), start=1):
            if len(words) < MIN_WORDS or not words[-1][2].isdigit():
                continue
            nxt = pages[n] if n < len(pages) else []
            last_of_chapter = (
                n == len(pages) or starts_chapter(nxt) or len(nxt) < MIN_WORDS
            )
            frac, at = longest_blank(img, skip_trailing=last_of_chapter)
            if frac <= args.threshold:
                continue
            reported += 1
            msg = (
                f"page {n} (printed {words[-1][2]}): {frac:.0%} of the text area is blank, "
                f"from {at:.0%} of the page height"
            )
            print(
                f"::warning title=thesis whitespace::{msg}"
                if gha
                else f"whitespace: {msg}"
            )
    print(f"whitespace: {reported} page(s) above {args.threshold:.0%} blank")
    return 1 if args.strict and reported else 0


if __name__ == "__main__":
    sys.exit(main())
