#!/usr/bin/env python3
"""Size and shape statistics over the .thy sources.

Answers the questions a review asks before reading anything: which session
carries the weight, which theory is closest to the 1500-line ceiling, how
long a proof is here on average, and which individual proofs are outliers.

Views (--view, repeatable, default `sessions files`):
  sessions  per-session totals and averages
  files     per-file lines/declarations/proof size, sorted by --sort
  lemmas    the longest individual proofs
  kinds     declaration and proof-method keyword counts per session
  style     lines over the 100-symbol limit, theories over 1500 lines,
            `sorry`/`oops`, and reconstruction methods worth watching

Line-based scanner sharing extract_definitions.py's comment/string masking.
Good enough to rank and compare; not an Isabelle parser, so a proof span is
"keyword to the next top-level command", which over-counts a trailing
comment block and under-counts nothing.
"""
import argparse
import csv
import json
import re
import statistics
import sys
from dataclasses import dataclass, field
from pathlib import Path

from extract_definitions import (
    DEF_KEYWORDS,
    HEADING_KEYWORDS,
    THEOREM_KEYWORDS,
    extract_name,
    find_matching_close,
    iter_theory_files,
    mask_comments_and_strings,
    session_of,
)

MAX_LINE_SYMBOLS = 100
# The limit counts Isabelle symbols, so \<Longrightarrow> is one, not fourteen.
SYMBOL_ESCAPE_RE = re.compile(r"\\<\^?[A-Za-z0-9_]+>")
# The three lines the length rule exempts because they cannot be broken: a URL,
# a mixfix annotation string, and anything in a generated theory.
EXEMPT_LINE_RE = re.compile(r"https?://|\(\s*\"")
GENERATED_THEORIES = {"VIMP_Grammar_Generated"}
MAX_THEORY_LINES = 1500

# Commands that end whatever precedes them. Proof-internal keywords (proof,
# next, qed, by, apply) are deliberately absent: they are flush left in this
# project's style, so a column test cannot separate them from a new command.
BOUNDARY_KEYWORDS = (
    DEF_KEYWORDS + THEOREM_KEYWORDS + HEADING_KEYWORDS + [
        "text", "theory", "end", "declare", "lemmas", "notation", "no_notation",
        "instantiation", "instance", "interpretation", "sublocale", "context",
        "export_code", "code_identifier", "value", "term", "typ", "ML",
        "setup", "translations", "syntax", "bundle", "inductive_cases",
        "termination", "print_translation", "parse_translation",
    ]
)
BOUNDARY_RE = re.compile(
    r"^[ \t]*(?P<kw>" + "|".join(sorted(set(BOUNDARY_KEYWORDS), key=len, reverse=True)) + r")\b",
    re.MULTILINE,
)
PROOF_START_RE = re.compile(r"^[ \t]*(by|proof|apply|\.\.|\.)(\b|[ \t(]|$)")
# Methods whose reconstruction cost the style guide asks to keep an eye on,
# plus the two that must never be checked in.
WATCHED_METHOD_RE = {
    "sorry": re.compile(r"\bsorry\b"),
    "oops": re.compile(r"\boops\b"),
    "metis": re.compile(r"\bmetis\b"),
    "smt": re.compile(r"\bsmt\b"),
    "sledgehammer": re.compile(r"\bsledgehammer\b"),
}


@dataclass
class Proof:
    name: str
    kind: str
    session: str
    theory: str
    line: int
    lines: int
    statement_lines: int
    proof_lines: int


@dataclass
class TheoryStats:
    path: Path
    session: str
    theory: str
    lines: int
    code_lines: int
    doc_lines: int
    blank_lines: int
    decls: dict = field(default_factory=dict)
    proofs: list = field(default_factory=list)
    methods: dict = field(default_factory=dict)
    long_lines: int = 0

    @property
    def n_decls(self) -> int:
        return sum(self.decls.values())

    @property
    def n_proofs(self) -> int:
        return len(self.proofs)

    @property
    def avg_proof(self) -> float:
        return mean_or_zero([p.proof_lines for p in self.proofs])


def mean_or_zero(xs) -> float:
    return statistics.fmean(xs) if xs else 0.0


def median_or_zero(xs) -> float:
    return float(statistics.median(xs)) if xs else 0.0


def percentile(xs, q: float) -> float:
    """Nearest-rank percentile; avoids numpy for a handful of numbers."""
    if not xs:
        return 0.0
    ordered = sorted(xs)
    idx = max(0, min(len(ordered) - 1, round(q / 100 * len(ordered) + 0.5) - 1))
    return float(ordered[idx])


def symbol_length(line: str) -> int:
    return len(SYMBOL_ESCAPE_RE.sub("x", line))


def mask_docs(text: str, masked: str) -> str:
    """Blank the bodies of `text`/`section`/... cartouches in an already
    comment-masked copy, so what survives is the machine-checked source."""
    out = list(masked)
    doc_re = re.compile(r"\b(" + "|".join(["text"] + HEADING_KEYWORDS) + r")\s*\\<open>")
    i = 0
    while True:
        m = doc_re.search(masked, i)
        if not m:
            break
        open_at = masked.index("\\<open>", m.start())
        end = find_matching_close(masked, open_at)
        for k in range(m.start(), min(end, len(out))):
            if out[k] != "\n":
                out[k] = " "
        i = end
    return "".join(out)


def scan_theory(path: Path) -> TheoryStats:
    text = path.read_text(encoding="utf-8", errors="replace")
    masked = mask_comments_and_strings(text)
    code_only = mask_docs(text, masked)

    raw_lines = text.splitlines()
    code_lines = code_only.splitlines()
    masked_lines = masked.splitlines()
    blank = sum(1 for l in raw_lines if not l.strip())
    code = sum(1 for l in code_lines if l.strip())
    # Whatever is neither blank nor machine-checked source is prose: a (* *)
    # comment or a text/section cartouche.
    doc = len(raw_lines) - blank - code
    long_lines = 0 if path.stem in GENERATED_THEORIES else sum(
        1 for l in raw_lines
        if symbol_length(l) > MAX_LINE_SYMBOLS and not EXEMPT_LINE_RE.search(l)
    )

    stats = TheoryStats(
        path=path,
        session=session_of(path),
        theory=path.stem,
        lines=len(raw_lines),
        code_lines=code,
        doc_lines=doc,
        blank_lines=blank,
        long_lines=long_lines,
    )

    for name, pattern in WATCHED_METHOD_RE.items():
        hits = len(pattern.findall(code_only))
        if hits:
            stats.methods[name] = hits

    line_starts = [0]
    for l in raw_lines:
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

    boundaries = []
    for m in BOUNDARY_RE.finditer(code_only):
        eol = code_only.find("\n", m.end())
        eol = eol if eol != -1 else len(code_only)
        boundaries.append((m.start(), m.group("kw"), text[m.end():eol]))

    for idx, (start, kw, rest) in enumerate(boundaries):
        if kw in DEF_KEYWORDS:
            stats.decls[kw] = stats.decls.get(kw, 0) + 1
        if kw not in THEOREM_KEYWORDS:
            continue
        end = boundaries[idx + 1][0] if idx + 1 < len(boundaries) else len(text)
        first, last = line_of(start), line_of(max(start, end - 1))
        body = masked_lines[first - 1:last]
        span = len([l for l in body if l.strip()])
        statement = span
        for offset, l in enumerate(body):
            if PROOF_START_RE.match(l):
                statement = len([x for x in body[:offset] if x.strip()])
                break
        stats.proofs.append(Proof(
            name=extract_name(rest),
            kind=kw,
            session=stats.session,
            theory=stats.theory,
            line=first,
            lines=span,
            statement_lines=statement,
            proof_lines=span - statement,
        ))
    return stats


# --- rendering ---------------------------------------------------------------

@dataclass
class Table:
    title: str
    columns: list
    rows: list
    aligns: list = field(default_factory=list)

    def alignment(self) -> list:
        return self.aligns or ["l"] + ["r"] * (len(self.columns) - 1)


def fmt(v) -> str:
    if isinstance(v, float):
        return f"{v:.1f}"
    return str(v)


def render_text(tables, out) -> None:
    for t in tables:
        cells = [[fmt(v) for v in row] for row in t.rows]
        widths = [len(c) for c in t.columns]
        for row in cells:
            widths = [max(w, len(c)) for w, c in zip(widths, row)]
        aligns = t.alignment()

        def line(row):
            return "  ".join(
                c.rjust(w) if a == "r" else c.ljust(w)
                for c, w, a in zip(row, widths, aligns)
            ).rstrip()

        print(f"\n{t.title}", file=out)
        print("-" * len(t.title), file=out)
        print(line(t.columns), file=out)
        print("  ".join("-" * w for w in widths), file=out)
        for row in cells:
            print(line(row), file=out)


def render_markdown(tables, out) -> None:
    for t in tables:
        aligns = t.alignment()
        print(f"\n### {t.title}\n", file=out)
        print("| " + " | ".join(t.columns) + " |", file=out)
        print("|" + "|".join(" ---: " if a == "r" else " --- " for a in aligns) + "|", file=out)
        for row in t.rows:
            print("| " + " | ".join(fmt(v) for v in row) + " |", file=out)


def render_csv(tables, out) -> None:
    writer = csv.writer(out)
    for t in tables:
        writer.writerow([t.title])
        writer.writerow(t.columns)
        for row in t.rows:
            writer.writerow([fmt(v) for v in row])
        writer.writerow([])


def render_json(tables, out) -> None:
    json.dump(
        [{"title": t.title, "columns": t.columns, "rows": t.rows} for t in tables],
        out, indent=2,
    )
    out.write("\n")


RENDERERS = {"text": render_text, "md": render_markdown, "csv": render_csv, "json": render_json}


# --- views -------------------------------------------------------------------

def session_table(stats) -> Table:
    rows = []
    by_session = {}
    for s in stats:
        by_session.setdefault(s.session, []).append(s)
    for session, group in by_session.items():
        proofs = [p.proof_lines for s in group for p in s.proofs]
        total = sum(s.lines for s in group)
        rows.append([
            session,
            len(group),
            total,
            round(total / len(group)),
            max(s.lines for s in group),
            sum(s.code_lines for s in group),
            sum(s.doc_lines for s in group),
            round(100 * sum(s.doc_lines for s in group) / max(1, total), 1),
            sum(s.n_decls for s in group),
            len(proofs),
            mean_or_zero(proofs),
            median_or_zero(proofs),
        ])
    rows.sort(key=lambda r: -r[2])
    total_row = [
        "TOTAL", sum(r[1] for r in rows), sum(r[2] for r in rows),
        round(sum(r[2] for r in rows) / max(1, sum(r[1] for r in rows))),
        max((r[4] for r in rows), default=0),
        sum(r[5] for r in rows), sum(r[6] for r in rows),
        round(100 * sum(r[6] for r in rows) / max(1, sum(r[2] for r in rows)), 1),
        sum(r[8] for r in rows), sum(r[9] for r in rows),
        mean_or_zero([p.proof_lines for s in stats for p in s.proofs]),
        median_or_zero([p.proof_lines for s in stats for p in s.proofs]),
    ]
    rows.append(total_row)
    return Table(
        "Sessions by total lines",
        ["session", "files", "lines", "avg", "max", "code", "doc", "doc%",
         "defs", "proofs", "avg proof", "med proof"],
        rows,
    )


FILE_SORTS = {
    "lines": lambda s: -s.lines,
    "code": lambda s: -s.code_lines,
    "doc": lambda s: -s.doc_lines,
    "proofs": lambda s: -s.n_proofs,
    "defs": lambda s: -s.n_decls,
    "avg-proof": lambda s: -s.avg_proof,
    "name": lambda s: (s.session, s.theory),
}


def file_table(stats, sort: str, top: int) -> Table:
    ordered = sorted(stats, key=FILE_SORTS[sort])
    shown = ordered[:top] if top else ordered
    rows = [[
        s.session, s.theory, s.lines, s.code_lines, s.doc_lines, s.blank_lines,
        s.n_decls, s.n_proofs, s.avg_proof,
        max((p.proof_lines for p in s.proofs), default=0),
    ] for s in shown]
    suffix = f" (top {len(shown)} of {len(ordered)})" if top and len(ordered) > top else ""
    return Table(
        f"Theories by {sort}{suffix}",
        ["session", "theory", "lines", "code", "doc", "blank", "defs",
         "proofs", "avg proof", "max proof"],
        rows,
        ["l", "l", "r", "r", "r", "r", "r", "r", "r", "r"],
    )


def lemma_table(stats, top: int) -> Table:
    proofs = [p for s in stats for p in s.proofs]
    proofs.sort(key=lambda p: -p.proof_lines)
    shown = proofs[:top] if top else proofs
    rows = [[
        p.session, p.theory, f"{p.name}:{p.line}", p.kind,
        p.statement_lines, p.proof_lines, p.lines,
    ] for p in shown]
    return Table(
        f"Longest proofs (top {len(shown)} of {len(proofs)})",
        ["session", "theory", "name:line", "kind", "stmt", "proof", "total"],
        rows,
        ["l", "l", "l", "l", "r", "r", "r"],
    )


def distribution_table(stats) -> Table:
    rows = []
    by_session = {}
    for s in stats:
        by_session.setdefault(s.session, []).extend(p.proof_lines for p in s.proofs)
    for session, xs in by_session.items():
        rows.append([
            session, len(xs), mean_or_zero(xs), median_or_zero(xs),
            percentile(xs, 90), percentile(xs, 99), max(xs, default=0),
            sum(1 for x in xs if x <= 1),
            sum(1 for x in xs if x > 20),
        ])
    rows.sort(key=lambda r: -r[2])
    allxs = [p.proof_lines for s in stats for p in s.proofs]
    rows.append([
        "TOTAL", len(allxs), mean_or_zero(allxs), median_or_zero(allxs),
        percentile(allxs, 90), percentile(allxs, 99), max(allxs, default=0),
        sum(1 for x in allxs if x <= 1), sum(1 for x in allxs if x > 20),
    ])
    return Table(
        "Proof length distribution (lines after the statement)",
        ["session", "proofs", "mean", "median", "p90", "p99", "max",
         "one-liners", ">20 lines"],
        rows,
    )


def kind_table(stats) -> Table:
    by_session = {}
    kinds = set()
    for s in stats:
        acc = by_session.setdefault(s.session, {})
        for k, n in s.decls.items():
            acc[k] = acc.get(k, 0) + n
            kinds.add(k)
    ordered_kinds = sorted(kinds, key=lambda k: -sum(a.get(k, 0) for a in by_session.values()))
    rows = [[session] + [acc.get(k, 0) for k in ordered_kinds] + [sum(acc.values())]
            for session, acc in by_session.items()]
    rows.sort(key=lambda r: -r[-1])
    rows.append(["TOTAL"] + [sum(r[i] for r in rows) for i in range(1, len(ordered_kinds) + 2)])
    return Table("Declaration kinds per session", ["session"] + ordered_kinds + ["total"], rows)


def style_table(stats) -> Table:
    rows = []
    for s in stats:
        flags = []
        if s.lines > MAX_THEORY_LINES:
            flags.append(f"{s.lines} lines")
        if s.long_lines:
            flags.append(f"{s.long_lines} long lines")
        for name in ("sorry", "oops", "metis", "smt", "sledgehammer"):
            if name in s.methods:
                flags.append(f"{s.methods[name]}x {name}")
        if flags:
            rows.append([s.session, s.theory, s.lines, s.long_lines,
                         s.methods.get("sorry", 0) + s.methods.get("oops", 0),
                         s.methods.get("metis", 0), s.methods.get("smt", 0),
                         ", ".join(flags)])
    rows.sort(key=lambda r: (-r[2] if r[2] > MAX_THEORY_LINES else 0, -r[3]))
    return Table(
        f"Style watchlist (>{MAX_THEORY_LINES} lines, >{MAX_LINE_SYMBOLS} symbols, "
        "unfinished or costly methods)",
        ["session", "theory", "lines", "long lines", "sorry/oops", "metis", "smt", "why"],
        rows,
        ["l", "l", "r", "r", "r", "r", "r", "l"],
    )


VIEWS = ["sessions", "files", "lemmas", "distribution", "kinds", "style"]


def main() -> int:
    ap = argparse.ArgumentParser(description=__doc__,
                                 formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument("--view", action="append", choices=VIEWS + ["all"],
                    help="repeatable; default: sessions files")
    ap.add_argument("--session", action="append",
                    help="restrict to these sessions (src/<name>), repeatable")
    ap.add_argument("--sort", choices=sorted(FILE_SORTS), default="lines",
                    help="ordering for the files view (default: lines)")
    ap.add_argument("--top", type=int, default=20,
                    help="rows in the files and lemmas views; 0 for all (default: 20)")
    ap.add_argument("--format", choices=sorted(RENDERERS), default="text")
    ap.add_argument("--out", type=Path, help="write here instead of stdout")
    args = ap.parse_args()

    views = args.view or ["sessions", "files"]
    if "all" in views:
        views = VIEWS

    stats = [scan_theory(p) for p in iter_theory_files()]
    if args.session:
        wanted = set(args.session)
        stats = [s for s in stats if s.session in wanted]
    if not stats:
        print("no .thy files matched", file=sys.stderr)
        return 1

    builders = {
        "sessions": lambda: session_table(stats),
        "files": lambda: file_table(stats, args.sort, args.top),
        "lemmas": lambda: lemma_table(stats, args.top),
        "distribution": lambda: distribution_table(stats),
        "kinds": lambda: kind_table(stats),
        "style": lambda: style_table(stats),
    }
    tables = [builders[v]() for v in VIEWS if v in views]

    out = args.out.open("w", encoding="utf-8") if args.out else sys.stdout
    try:
        RENDERERS[args.format](tables, out)
    finally:
        if args.out:
            out.close()
    return 0


if __name__ == "__main__":
    sys.exit(main())
