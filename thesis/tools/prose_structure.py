#!/usr/bin/env python3
"""Warn about thesis prose patterns that Vale cannot see.

typst2vast drops cross-references and turns Isabelle citations into code, so
these author preferences are checked on the Typst source instead:

- a prose paragraph that cites more than three Isabelle entities outside its
  formulas reads as a list of constants instead of an argument;
- a long caption repeats the text it sits next to;
- an Isabelle listing (`thy`, `proved`) is embedded without a figure;
- a reference to a later chapter or section asks the reader to trust material
  they have not seen. The front matter and the introduction are exempt, since
  their job is to point ahead, and so are references into the appendices,
  which hold the formal sources and the tooling;
- a term is emphasized as a definition (`_store_`) in more than one section, or
  used in an earlier section than the one defining it. A reader of the PDF
  alone meets it undefined, or meets the same introduction again.

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

# Navigation and statements about the work rather than its exposition: a term
# used here before its definition is not a gap in the argument.
TERM_USE_EXEMPT = {
    "abstract.typ",
    "acknowledgements.typ",
    "ai-use.typ",
    "reading-guide.typ",
}
# Words the text emphasizes for stress or as values, not as defined terms.
TERM_IGNORE = {
    "true",
    "false",
    "holds",
    "reached",
    "least",
    "independent",
    "observed",
    "local",
    "global",
    "domain",
    "component",
    "report",
    "check",
    "claim",
    "record",
    "inductive",
}

INCLUDE = re.compile(r'^#?\s*include "(content/[^"]+\.typ)"', re.M)
HEADING = re.compile(r"^=+ ", re.M)
TERM_DEF = re.compile(r"(?<![\w*])_([A-Za-z][A-Za-z -]{1,40}?)_(?!\w)")
ISA_REF = re.compile(r"#isa(?:const|thm|type|locale)\(")
LABEL = re.compile(r"<((?:ch|sec):[\w:.-]+)>")
REF = re.compile(r"@((?:ch|sec):[\w:.-]+?)(?=[^\w:.-]|[.:-](?:\s|$))")
MATH = re.compile(r"\$[^$]*\$")
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


def section_of(text, i):
    """Number of headings before offset i: equal values share a section."""
    return len(HEADING.findall(text, 0, i))


def term_findings(files, texts):
    """Repeated and premature uses of emphasized definitions, in document order."""
    first = {}
    for n, f in enumerate(files):
        text = texts[f]
        for off, para in prose_paragraphs(text):
            for m in TERM_DEF.finditer(para):
                term = m.group(1).lower()
                if term in TERM_IGNORE or f.name in TERM_USE_EXEMPT:
                    continue
                at = off + m.start()
                where = (n, section_of(text, at))
                if term not in first:
                    first[term] = (where, at, f)
                elif first[term][0] != where:
                    _, at0, f0 = first[term]
                    yield (
                        f,
                        line_of(text, at),
                        f"'{term}' is defined again; {f0.name}:"
                        f"{line_of(texts[f0], at0)} defines it, refer back instead",
                    )

    for term, ((n0, sec0), at0, f0) in first.items():
        use = re.compile(r"\b" + re.escape(term) + r"s?\b", re.I)
        for n, f in enumerate(files[: n0 + 1]):
            if f.name in TERM_USE_EXEMPT:
                continue
            text = texts[f]
            hit = next(
                (
                    off + m.start()
                    for off, para in prose_paragraphs(text)
                    for m in use.finditer(para)
                    if (n, section_of(text, off + m.start())) < (n0, sec0)
                ),
                None,
            )
            if hit is not None:
                yield (
                    f,
                    line_of(text, hit),
                    f"'{term}' is used before {f0.name}:{line_of(texts[f0], at0)} "
                    "defines it: define it here or say where it is defined",
                )
                break


def check(files):
    texts = {f: f.read_text() for f in files}
    label_at = {}
    for n, f in enumerate(files):
        for m in LABEL.finditer(texts[f]):
            label_at[m.group(1)] = (n, m.start(), f)

    yield from term_findings(files, texts)

    for n, f in enumerate(files):
        text, name = texts[f], f.name
        for off, para in prose_paragraphs(text):
            # Names inside formulas are notation, not citations.
            refs = len(ISA_REF.findall(MATH.sub(" ", para)))
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
                    and target[:2] > (n, off + m.start())
                    and not target[2].name.startswith("appendix-")
                ):
                    yield (
                        f,
                        line_of(text, off + m.start()),
                        f"@{m.group(1)} points ahead to {target[2].name}:"
                        f"{line_of(texts[target[2]], target[1])}: drop it unless "
                        "it is the formal source or needed to navigate",
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
