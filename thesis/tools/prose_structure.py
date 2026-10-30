#!/usr/bin/env python3
"""Warn about thesis prose patterns that Vale cannot see.

typst2vast drops cross-references and turns Isabelle citations into code, so
these author preferences are checked on the Typst source instead:

- a prose paragraph that cites many Isabelle entities reads as a list of
  constants instead of an argument;
- a long caption repeats the text it sits next to;
- an Isabelle listing (`thy`, `proved`) is embedded without a figure;
- a reference to a later chapter asks the reader to trust material they have
  not seen. The front matter and the introduction are exempt, since their job
  is to point ahead, and so are references into the appendices, which hold
  the formal sources and the tooling.

Warnings only: the exit status is 0 unless --strict is given. Under GitHub
Actions each warning is also printed as an annotation.
"""

import argparse
import os
import re
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
MAIN = ROOT / "thesis.typ"
MAX_ISA_REFS = 3
MAX_CAPTION_WORDS = 60
FORWARD_EXEMPT = {
    "abstract.typ",
    "acknowledgements.typ",
    "ai-use.typ",
    "reading-guide.typ",
    "01-introduction.typ",
}

INCLUDE = re.compile(r'^#?\s*include "(content/[^"]+\.typ)"', re.M)
ISA_REF = re.compile(r"#isa(?:const|thm|type|locale)\(")
LABEL = re.compile(r"<((?:ch|sec):[\w:.-]+)>")
REF = re.compile(r"@((?:ch|sec):[\w:.-]+?)(?=[^\w:.-]|[.:-](?:\s|$))")
LISTING = re.compile(r"\b(?:thy|proved)\(")


def closing(text, i):
    """Index just past the bracket that matches the opening one at i."""
    pairs = {"(": ")", "[": "]", "{": "}"}
    stack = [pairs[text[i]]]
    j = i + 1
    while stack and j < len(text):
        c = text[j]
        if c == "\\":
            j += 2
            continue
        if c in pairs:
            stack.append(pairs[c])
        elif c == stack[-1]:
            stack.pop()
        j += 1
    return j


def figures(text):
    """Yield (start, end) of every #figure(...) call."""
    for m in re.finditer(r"#figure\(", text):
        yield m.start(), closing(text, m.end() - 1)


def caption(text, start, end):
    m = re.compile(r"caption:\s*\[").search(text, start, end)
    if not m:
        return None
    return text[m.end() : closing(text, m.end() - 1) - 1]


def words(markup):
    plain = re.sub(
        r"\$[^$]*\$|#\w+(?:\.\w+)*\([^)]*\)|@[\w:.-]+|<[\w:.-]+>", " x ", markup
    )
    return len(re.findall(r"[A-Za-z][\w'-]*", plain))


def line_of(text, i):
    return text.count("\n", 0, i) + 1


def prose_paragraphs(text):
    """Yield (offset, paragraph) for blank-line separated prose outside figures."""
    masked = list(text)
    for s, e in figures(text):
        for k in range(s, e):
            if masked[k] != "\n":
                masked[k] = " "
    masked = "".join(masked)
    for m in re.finditer(r"(?:[^\n]+\n?)+", masked):
        para = m.group(0)
        if para.lstrip().startswith(("#import", "#let", "#show", "#set", "=", "//")):
            continue
        yield m.start(), para


def chapters():
    return [ROOT / p for p in INCLUDE.findall(MAIN.read_text())]


def check(files):
    texts = {f: f.read_text() for f in files}
    label_at = {}
    for n, f in enumerate(files):
        for m in LABEL.finditer(texts[f]):
            label_at[m.group(1)] = (n, f)

    for n, f in enumerate(files):
        text, name = texts[f], f.name
        for off, para in prose_paragraphs(text):
            refs = len(ISA_REF.findall(para))
            if refs > MAX_ISA_REFS:
                yield (
                    f,
                    line_of(text, off),
                    f"{refs} Isabelle citations in one paragraph: keep the ones "
                    "the argument needs",
                )
            if name in FORWARD_EXEMPT:
                continue
            for m in REF.finditer(para):
                target = label_at.get(m.group(1))
                if (
                    target
                    and target[0] > n
                    and not target[1].name.startswith("appendix-")
                ):
                    yield (
                        f,
                        line_of(text, off + m.start()),
                        f"@{m.group(1)} points ahead to {target[1].name}: drop it "
                        "unless it is the formal source or needed to navigate",
                    )
        for s, e in figures(text):
            body = text[s:e]
            cap = caption(text, s, e)
            if cap is not None and words(cap) > MAX_CAPTION_WORDS:
                yield (
                    f,
                    line_of(text, s),
                    f"caption of {words(cap)} words: keep it under "
                    f"{MAX_CAPTION_WORDS} and move the argument into the text",
                )
            if LISTING.search(body):
                yield (
                    f,
                    line_of(text, s),
                    "Isabelle listing inside a figure: embed it without one",
                )


def main():
    ap = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    ap.add_argument(
        "files", nargs="*", type=Path, help="default: every included chapter"
    )
    ap.add_argument(
        "--strict", action="store_true", help="exit 1 when anything is reported"
    )
    args = ap.parse_args()

    everything = chapters()
    wanted = {p.resolve() for p in args.files} if args.files else None
    gha = os.environ.get("GITHUB_ACTIONS") == "true"
    reported = 0
    for f, line, msg in check(everything):
        if wanted is not None and f.resolve() not in wanted:
            continue
        reported += 1
        rel = f.relative_to(ROOT.parent)
        print(
            f"::warning file={rel},line={line},title=thesis prose structure::{msg}"
            if gha
            else f"{rel}:{line}: {msg}"
        )
    print(f"prose-structure: {reported} warning(s)")
    return 1 if args.strict and reported else 0


if __name__ == "__main__":
    sys.exit(main())
