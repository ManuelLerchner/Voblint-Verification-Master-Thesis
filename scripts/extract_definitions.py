#!/usr/bin/env python3
"""Extract definitional vocabulary and doc coverage from .thy sources.

Two modes sharing one parser:
  --dump   write a markdown overview of every locale/definition/fun/record/
           datatype/... with its nearest preceding `text` docstring, grouped
           by session and file. Intended as a gitignored, regenerable index
           -- not a source of truth (the .thy files are).
  --lint   check documentation coverage: every theory has a header text
           block, and every section/subsection/locale is accompanied by a
           text block. Scoped to headings and locales (not every lemma) to
           match this project's "comment the WHY, not routine definitions"
           convention -- exits 1 on violations.

This is a regex/line-based scanner, not an Isabelle parser. It is good
enough for an overview/lint tool; it is not a substitute for reading the
.thy source.
"""
import argparse
import re
import sys
from dataclasses import dataclass, field
from pathlib import Path

REPO_ROOT = Path(__file__).resolve().parent.parent
SRC_ROOT = REPO_ROOT / "src"

HEADING_KEYWORDS = ["chapter", "section", "subsection", "subsubsection", "paragraph"]
DEF_KEYWORDS = [
    "locale", "definition", "fun", "primrec", "inductive", "inductive_set",
    "abbreviation", "record", "datatype", "type_synonym", "class", "fun_cases",
]
THEOREM_KEYWORDS = ["theorem", "lemma", "corollary"]

COMMAND_START_RE = re.compile(
    r"^\s*(" + "|".join(HEADING_KEYWORDS + DEF_KEYWORDS + THEOREM_KEYWORDS + ["text", "theory"]) + r")\b"
)


@dataclass
class TextBlock:
    start_line: int
    end_line: int
    content: str


@dataclass
class Heading:
    kind: str
    name: str
    line: int
    doc: TextBlock | None = None


MAX_CODE_LINES = 15

@dataclass
class Decl:
    kind: str
    name: str
    line: int
    doc: TextBlock | None = None
    code: str = ""


@dataclass
class ParsedTheory:
    path: Path
    theory_name: str
    header_doc: TextBlock | None
    headings: list = field(default_factory=list)
    decls: list = field(default_factory=list)


def mask_comments_and_strings(text: str) -> str:
    """Blank out (* ... *) comment bodies and "..." string bodies so command
    keywords appearing in prose or as quoted type names (e.g. instance "fun")
    are not mistaken for actual commands. Preserves length and newlines so
    line numbers and \\<open>/\\<close> cartouche offsets stay valid."""
    out = list(text)
    n = len(text)
    i = 0
    while i < n:
        if text.startswith("(*", i):
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
                    s = s[i + 1:].strip()
                    break
    while s.startswith("'"):
        s = s.split(None, 1)[1] if " " in s else ""
    m = re.match(r"[A-Za-z_][A-Za-z0-9_'.]*", s)
    if m:
        return m.group(0)
    m = re.match(r"\S+", s)
    return m.group(0) if m else "?"


COMMAND_RE = re.compile(
    r"(?P<text>\btext\s*)\\<open>|"
    r"\b(?P<heading>" + "|".join(HEADING_KEYWORDS) + r")\s+\\<open>|"
    r"\b(?P<decl>" + "|".join(DEF_KEYWORDS) + r")\b|"
    r"\b(?P<thm>" + "|".join(THEOREM_KEYWORDS) + r")\b"
)


def parse_theory(path: Path) -> ParsedTheory:
    text = path.read_text(encoding="utf-8", errors="replace")
    # Scan a masked copy so "fun"/"lemma"/... inside comments or quoted type
    # names (instance "fun" :: ...) aren't mistaken for commands; content is
    # still pulled from the original `text` at the same offsets.
    masked = mask_comments_and_strings(text)
    lines = text.splitlines()
    line_starts = [0]
    for l in lines:
        line_starts.append(line_starts[-1] + len(l) + 1)

    def line_of(offset: int) -> int:
        lo, hi = 0, len(line_starts) - 1
        while lo < hi:
            mid = (lo + hi + 1) // 2
            if line_starts[mid] <= offset:
                lo = mid
            else:
                hi = mid - 1
        return lo + 1

    theory_name = path.stem
    m = re.search(r"^\s*theory\s+(\S+)", text, re.MULTILINE)
    if m:
        theory_name = m.group(1)

    # Events in source order: ('text', TextBlock, start) | ('heading', kind, name, line, start)
    # | ('decl'/'thm', kind, name, line, start)  -- start is used afterwards to
    # slice each decl's own source: from its keyword up to the next event.
    events = []
    i = 0
    while i < len(masked):
        cm = COMMAND_RE.search(masked, i)
        if not cm:
            break
        if cm.group("text") is not None:
            open_at = masked.index("\\<open>", cm.start())
            end = find_matching_close(masked, open_at)
            content = text[open_at + len("\\<open>"):end - len("\\<close>")]
            events.append(("text", TextBlock(line_of(cm.start()), line_of(end), content.strip()), cm.start()))
            i = end
        elif cm.group("heading") is not None:
            open_at = masked.index("\\<open>", cm.start())
            end = find_matching_close(masked, open_at)
            name = text[open_at + len("\\<open>"):end - len("\\<close>")].strip()
            events.append(("heading", cm.group("heading"), name, line_of(cm.start()), cm.start()))
            i = end
        elif cm.group("decl") is not None:
            eol = masked.find("\n", cm.end())
            eol = eol if eol != -1 else len(masked)
            name = extract_name(text[cm.end():eol])
            events.append(("decl", cm.group("decl"), name, line_of(cm.start()), cm.start()))
            i = cm.end()
        else:
            eol = masked.find("\n", cm.end())
            eol = eol if eol != -1 else len(masked)
            name = extract_name(text[cm.end():eol])
            events.append(("thm", cm.group("thm"), name, line_of(cm.start()), cm.start()))
            i = cm.end()

    trailing_comment_re = re.compile(r"(\s*\(\*(?:[^*]|\*(?!\)))*\*\)\s*)+$", re.DOTALL)

    def code_span(start: int, idx: int) -> str:
        end = events[idx + 1][-1] if idx + 1 < len(events) else len(text)
        snippet = text[start:end].rstrip()
        # A comment right before the next command usually documents *that*
        # next declaration, not this one -- drop it from this snippet.
        snippet = trailing_comment_re.sub("", snippet).rstrip()
        lines = snippet.splitlines()
        if len(lines) > MAX_CODE_LINES:
            lines = lines[:MAX_CODE_LINES] + [f"... ({len(snippet.splitlines()) - MAX_CODE_LINES} more lines)"]
        return "\n".join(lines)

    header_doc = None
    headings = []
    decls = []
    pending_doc = None
    seen_non_header = False
    for idx, ev in enumerate(events):
        if ev[0] == "text":
            pending_doc = ev[1]
            if not seen_non_header and header_doc is None:
                header_doc = ev[1]
            continue
        if ev[0] in ("decl", "thm"):
            seen_non_header = True
        if ev[0] == "heading":
            _, kind, name, line, start = ev
            # A doc may precede the heading, but this project's convention is
            # section/subsection followed by a text block explaining it.
            doc = pending_doc if pending_doc and line - pending_doc.end_line <= 3 else None
            if doc is None and idx + 1 < len(events) and events[idx + 1][0] == "text":
                following = events[idx + 1][1]
                if following.start_line - line <= 3:
                    doc = following
            headings.append(Heading(kind, name, line, doc))
            pending_doc = None
        elif ev[0] == "decl":
            _, kind, name, line, start = ev
            doc = pending_doc if pending_doc and line - pending_doc.end_line <= 3 else None
            decls.append(Decl(kind, name, line, doc, code_span(start, idx)))
            pending_doc = None
        else:
            pending_doc = None

    return ParsedTheory(path, theory_name, header_doc, headings, decls)


def iter_theory_files():
    for p in sorted(SRC_ROOT.rglob("*.thy")):
        yield p


def session_of(path: Path) -> str:
    rel = path.relative_to(SRC_ROOT)
    return rel.parts[0]


SYMBOL_MAP = {
    "\\<Longrightarrow>": "\u27f9", "\\<Rightarrow>": "\u21d2", "\\<And>": "\u22c0",
    "\\<longrightarrow>": "\u27f6", "\\<rightarrow>": "\u2192", "\\<leftarrow>": "\u2190",
    "\\<longleftrightarrow>": "\u2194", "\\<Longleftrightarrow>": "\u27fa",
    "\\<in>": "\u2208", "\\<notin>": "\u2209", "\\<not>": "\u00ac", "\\<noteq>": "\u2260",
    "\\<forall>": "\u2200", "\\<exists>": "\u2203", "\\<le>": "\u2264", "\\<ge>": "\u2265",
    "\\<subseteq>": "\u2286", "\\<subset>": "\u2282", "\\<union>": "\u222a", "\\<inter>": "\u2229",
    "\\<lbrakk>": "\u27e6", "\\<rbrakk>": "\u27e7", "\\<dots>": "\u2026",
    "\\<lambda>": "\u03bb", "\\<equiv>": "\u2261", "\\<and>": "\u2227", "\\<or>": "\u2228",
    "\\<sigma>": "\u03c3", "\\<Sigma>": "\u03a3", "\\<gamma>": "\u03b3", "\\<Gamma>": "\u0393",
    "\\<nabla>": "\u2207", "\\<times>": "\u00d7", "\\<circ>": "\u2218",
    "\\<bottom>": "\u22a5", "\\<top>": "\u22a4", "\\<squnion>": "\u2294", "\\<sqinter>": "\u2293",
    "\\<Longleftarrow>": "\u27f8", "\\<^sub>": "_", "\\<^sup>": "^",
    "\\<Pi>": "\u03a0", "\\<pi>": "\u03c0", "\\<mapsto>": "\u21a6", "\\<pm>": "\u00b1",
    "\\<lparr>": "\u2987", "\\<rparr>": "\u2988", "\\<alpha>": "\u03b1", "\\<beta>": "\u03b2",
    "\\<epsilon>": "\u03b5", "\\<infinity>": "\u221e", "\\<cdot>": "\u00b7",
    "\\<parallel>": "\u2225", "\\<turnstile>": "\u22a2", "\\<Turnstile>": "\u22a8",
    "\\<^item>": "\u2022", "\\<^bold>": "", "\\<^emph>": "",
}
SYMBOL_RE = re.compile("|".join(re.escape(k) for k in sorted(SYMBOL_MAP, key=len, reverse=True)))

# Document markup antiquotations of the form \<^word>\<open>...\<close>: covers
# both semantic references (const/term/typ/class/locale/thm/theory/type/...)
# and typesetting markup (bold/emph/item/verbatim). Rendered generically as
# code, except the typesetting ones get their natural Markdown equivalent.
MARKUP_TEMPLATES = {"bold": "**{0}**", "emph": "*{0}*", "item": "\u2022 {0}", "verbatim": "`{0}`"}
GENERIC_CARTOUCHE_ANTIQ_RE = re.compile(r"\\<\^(\w+)>\\<open>(.*?)\\<close>")
BRACE_ANTIQ_RE = re.compile(
    r"@\{(?:const|term|typ|class|locale)\s+([^}]*)\}"
)
BRACE_THM_RE = re.compile(r"@\{thm\s*(?:\[[^\]]*\])?\s*([^}]*)\}")
BRACE_TEXT_RE = re.compile(r"@\{text\s+\"?([^}\"]*)\"?\}")
CARTOUCHE_RE = re.compile(r"\\<open>(.*?)\\<close>")


def render_symbols(s: str) -> str:
    return SYMBOL_RE.sub(lambda m: SYMBOL_MAP[m.group(0)], s)


def render_markup_antiq(m: re.Match) -> str:
    kind, content = m.group(1), m.group(2).strip()
    return MARKUP_TEMPLATES.get(kind, "`{0}`").format(content)


def render_prose(s: str) -> str:
    """Turn Isabelle antiquotations/cartouches and ASCII symbol escapes into
    readable Markdown: @{const foo} / \\<^const>\\<open>foo\\<close> -> `foo`,
    \\<^bold>\\<open>foo\\<close> -> **foo**, @{text foo} -> *foo*, remaining
    \\<open>x\\<close> -> `x`, then ASCII symbol names -> the actual Unicode symbol."""
    s = GENERIC_CARTOUCHE_ANTIQ_RE.sub(render_markup_antiq, s)
    s = BRACE_ANTIQ_RE.sub(lambda m: f"`{m.group(1).strip()}`", s)
    s = BRACE_THM_RE.sub(lambda m: f"`{m.group(1).strip()}`", s)
    s = BRACE_TEXT_RE.sub(lambda m: f"*{m.group(1).strip()}*", s)
    s = CARTOUCHE_RE.sub(lambda m: f"`{m.group(1).strip()}`", s)
    s = render_symbols(s)
    return s


def table_cell(s: str) -> str:
    """Render Isabelle markup, collapse to one line, escape pipes so it
    survives as a Markdown table cell."""
    return " ".join(render_prose(s).split()).replace("|", "\\|")


def escape_html(s: str) -> str:
    return s.replace("&", "&amp;").replace("<", "&lt;").replace(">", "&gt;")


def code_cell(code: str) -> str:
    """Render a (possibly multi-line) code snippet into a table cell: convert
    ASCII symbol escapes to Unicode, HTML-escape any leftover angle brackets,
    and join lines with <br> since table cells must be single physical lines."""
    lines = [escape_html(render_symbols(line)) for line in code.splitlines()]
    return "<br>".join(lines).replace("|", "\\|")


def cmd_dump(out_path: Path, include_theorems: bool) -> None:
    by_session: dict[str, list[ParsedTheory]] = {}
    for p in iter_theory_files():
        parsed = parse_theory(p)
        by_session.setdefault(session_of(p), []).append(parsed)

    out = ["# Definitions Overview", "", "Generated by `scripts/extract_definitions.py --dump`. Do not edit by hand.", ""]
    for session in sorted(by_session):
        out.append(f"## {session}")
        out.append("")
        for parsed in sorted(by_session[session], key=lambda p: p.path):
            if not parsed.decls:
                continue
            rel = parsed.path.relative_to(REPO_ROOT)
            out.append(f"### {rel}")
            out.append("")
            if parsed.header_doc:
                out.append(f"> {table_cell(parsed.header_doc.content)}")
                out.append("")
            out.append("| Kind | Name | Line | Definition | Docstring |")
            out.append("| --- | --- | --- | --- | --- |")
            for d in parsed.decls:
                doc = table_cell(d.doc.content) if d.doc else ""
                code = code_cell(d.code)
                out.append(f"| {d.kind} | `{d.name}` | {d.line} | {code} | {doc} |")
            out.append("")
    out_path.parent.mkdir(parents=True, exist_ok=True)
    out_path.write_text("\n".join(out) + "\n", encoding="utf-8")
    print(f"wrote {out_path}")


def cmd_lint() -> int:
    violations = []
    for p in iter_theory_files():
        parsed = parse_theory(p)
        rel = parsed.path.relative_to(REPO_ROOT)
        if parsed.header_doc is None:
            violations.append(f"{rel}: theory has no header text block")
        for h in parsed.headings:
            if h.doc is None:
                violations.append(f"{rel}:{h.line}: {h.kind} \"{h.name}\" has no accompanying text block")
        for d in parsed.decls:
            if d.kind == "locale" and d.doc is None:
                violations.append(f"{rel}:{d.line}: locale {d.name} has no accompanying text block")

    if violations:
        print(f"{len(violations)} doc-coverage violation(s):", file=sys.stderr)
        for v in violations:
            print(f"  {v}", file=sys.stderr)
        return 1
    print("doc coverage OK")
    return 0


def main() -> int:
    ap = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument("--dump", action="store_true", help="write markdown overview")
    ap.add_argument("--lint", action="store_true", help="check doc coverage, exit 1 on violations")
    ap.add_argument("--out", type=Path, default=REPO_ROOT / "docs" / "generated" / "DEFINITIONS_OVERVIEW.md")
    ap.add_argument("--include-theorems", action="store_true", help="also list theorem/lemma/corollary in the dump")
    args = ap.parse_args()

    if not args.dump and not args.lint:
        ap.error("pass --dump and/or --lint")

    rc = 0
    if args.dump:
        cmd_dump(args.out, args.include_theorems)
    if args.lint:
        rc = cmd_lint()
    return rc


if __name__ == "__main__":
    sys.exit(main())
