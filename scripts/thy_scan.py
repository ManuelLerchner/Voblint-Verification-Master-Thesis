"""Line-based scanning helpers shared by the statistics scripts.

`thy_stats.py`, `session_graph.py`, and `pages_stats.py` count what the Pages
explainer and the thesis report, so they share one scanner: comment and string
masking, cartouche matching, declaration keywords, and the theory file list.
This is a regex/line-based scanner, not an Isabelle parser. Documentation
coverage and the definitions overview moved to isar-tools (`isar check docs`,
`isar project names`).
"""

import re
from pathlib import Path

REPO_ROOT = Path(__file__).resolve().parent.parent

SRC_ROOT = REPO_ROOT / "src"

HEADING_KEYWORDS = ["chapter", "section", "subsection", "subsubsection", "paragraph"]

DEF_KEYWORDS = [
    "locale",
    "definition",
    "fun",
    "primrec",
    "inductive",
    "inductive_set",
    "abbreviation",
    "record",
    "datatype",
    "type_synonym",
    "class",
    "fun_cases",
]

THEOREM_KEYWORDS = ["theorem", "lemma", "corollary"]


def mask_comments_and_strings(text: str, strings: bool = True) -> str:
    """Blank out (* ... *) comment bodies and "..." string bodies so command
    keywords appearing in prose or as quoted type names (e.g. instance "fun")
    are not mistaken for actual commands. Preserves length and newlines so
    line numbers and \\<open>/\\<close> cartouche offsets stay valid.

    A cartouche is skipped whole and left unmasked: a quote or comment
    delimiter inside prose (\\"nonzero\\" in a text block) is not one in
    Isabelle, and treating it as one would blank every command up to the
    next stray quote."""
    out = list(text)
    n = len(text)
    i = 0
    while i < n:
        if text.startswith("\\<open>", i):
            i = find_matching_close(text, i)
        elif text.startswith("(*", i):
            depth = 1
            j = i + 2
            while j < n and depth > 0:
                if text.startswith("(*", j):
                    depth += 1
                    j += 2
                elif text.startswith("*)", j):
                    depth -= 1
                    j += 2
                else:
                    j += 1
            for k in range(i, j):
                if out[k] != "\n":
                    out[k] = " "
            i = j
        elif text[i] == '"':
            j = i + 1
            while j < n:
                if text[j] == "\\" and j + 1 < n:
                    j += 2
                    continue
                if text[j] == '"':
                    j += 1
                    break
                j += 1
            if strings:
                for k in range(i, j):
                    if out[k] != "\n":
                        out[k] = " "
            i = j
        else:
            i += 1
    return "".join(out)


def find_matching_close(text: str, open_pos: int) -> int:
    """Return index just past the \\<close> matching \\<open> at open_pos, honoring nesting."""
    depth = 1
    i = open_pos + len("\\<open>")
    while i < len(text) and depth > 0:
        if text.startswith("\\<open>", i):
            depth += 1
            i += len("\\<open>")
        elif text.startswith("\\<close>", i):
            depth -= 1
            i += len("\\<close>")
        else:
            i += 1
    return i


def extract_name(rest_of_line: str) -> str:
    """Best-effort: first identifier token after a declaration keyword,
    skipping type-variable prefixes like 'a or ('a, 'b). Also handles the
    quoted-proposition form `definition "lhs = rhs"` / `abbreviation "n \\<equiv> ..."`
    (no separate `name :: type where` clause), including instantiation-style
    definitions of an operator (e.g. `definition "(s :: ..) < t <-> .."`)."""
    s = rest_of_line.strip()
    if s.startswith('"'):
        s = s[1:].strip()
    if s.startswith("("):
        depth = 0
        for i, ch in enumerate(s):
            if ch == "(":
                depth += 1
            elif ch == ")":
                depth -= 1
                if depth == 0:
                    s = s[i + 1 :].strip()
                    break
    while s.startswith("'"):
        s = s.split(None, 1)[1] if " " in s else ""
    m = re.match(r"[A-Za-z_][A-Za-z0-9_'.]*", s)
    if m:
        return m.group(0)
    m = re.match(r"\S+", s)
    return m.group(0) if m else "?"


# Vendored developments: built as their own session, but not held to this
# project's conventions, so only callers that ask for them scan them.
VENDOR_SESSIONS = {REPO_ROOT / "vendor" / "td-verification": "TD"}


def iter_theory_files(vendor: bool = False):
    yield from sorted(SRC_ROOT.rglob("*.thy"))
    if vendor:
        for root in VENDOR_SESSIONS:
            yield from sorted(root.glob("*.thy"))


def session_of(path: Path) -> str:
    for root, session in VENDOR_SESSIONS.items():
        if path.is_relative_to(root):
            return session
    return path.relative_to(SRC_ROOT).parts[0]
