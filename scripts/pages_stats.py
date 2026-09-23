#!/usr/bin/env python3
"""Repository size figures for the Pages explainer.

Writes a classic script assigning `window.VOBLINT_STATS`, which the page reads
at load. A script rather than JSON because the explainer must also open from
file://, where fetch is blocked; a missing file leaves the page's fallback
figures in place.

Isabelle figures reuse thy_stats.py's scanner, so the page and
`pixi run theory-stats` never disagree. The session graph behind the strata
figure comes from session_graph.py, read from ROOT files and theory imports.
The OCaml counts are plain line counts.

The thesis reads the same collection (`thesis/tools/stats.py`), so a figure
means one thing on both: every counting rule lives here.
"""

import argparse
import json
import re
import subprocess
import sys
from datetime import date
from pathlib import Path

import session_graph
from extract_definitions import VENDOR_SESSIONS, iter_theory_files
from thy_stats import scan_theory, statement_kinds

REPO_ROOT = Path(__file__).resolve().parent.parent
GENERATED_ML = REPO_ROOT / "codegen" / "generated" / "ml" / "Voblint_CLI.ml"
CLI_DIR = REPO_ROOT / "cli"
SRC_DIR = REPO_ROOT / "src"
CORPUS_DIR = REPO_ROOT / "tests" / "regression"
EXAMPLES_DIR = REPO_ROOT / "src" / "Examples"
# tests/run.py's placement convention: what the concrete program does.
CORPUS_KINDS = ("precision", "soundness", "known-imprecision")
# Emitted from manifests/vimp-grammar.yaml, so not handwritten.
GENERATED_CLI = {"vimp_printer.ml", "vimp_parser.mly", "vimp_lexer.mll"}
# The theories a reader has to audit to believe the source semantics: everything
# else in the development is checked against them. The explainer cites their size
# and pstep's rule count, so both are derived rather than written down twice.
VIMP_DIR = REPO_ROOT / "src" / "Program_Model" / "VIMP"
SEMANTICS_THEORIES = (
    "VIMP_Syntax",
    "VIMP_Expr",
    "VIMP_Special",
    "VIMP_Globals",
    "VIMP_Program",
    "VIMP_Proc",
)


def count_lines(path: Path) -> int:
    with path.open(encoding="utf-8", errors="replace") as f:
        return sum(1 for _ in f)


def pstep_rules() -> int:
    """Introduction rules of the `pstep` inductive, counted from its source.

    The block runs from `inductive` to the first blank line after the last rule;
    each rule is a named clause at the start of a line (`Assign:` or `| Call:`).
    """
    text = (VIMP_DIR / "VIMP_Proc.thy").read_text(encoding="utf-8")
    lines = text.split("\n")
    start = next(
        i
        for i, line in enumerate(lines)
        if line.startswith("inductive") and "cases" not in line
    )
    where = next(i for i in range(start, len(lines)) if lines[i].strip() == "where")
    rules = 0
    for line in lines[where + 1 :]:
        if not line.strip():
            break
        if re.match(r"(\| )?[A-Z][A-Za-z0-9_]*:", line.strip()):
            rules += 1
    return rules


def flatten(node: dict, prefix: str = ""):
    """(dotted key, int) pairs of a nested stats dict; lists are not addressable."""
    for key, value in node.items():
        if isinstance(value, dict):
            yield from flatten(value, f"{prefix}{key}.")
        elif isinstance(value, int):
            yield f"{prefix}{key}", value


def source_directory(theory) -> str | None:
    """Top-level directory below src/ holding the theory, or None outside src/."""
    try:
        return theory.path.resolve().relative_to(SRC_DIR).parts[0]
    except ValueError:
        return None


def git(*args: str) -> str | None:
    """Output of a git command in the repository, or None outside a git checkout."""
    try:
        return subprocess.run(
            ["git", *args],
            cwd=REPO_ROOT,
            capture_output=True,
            text=True,
            check=True,
        ).stdout.strip()
    except (OSError, subprocess.CalledProcessError):
        return None


def commit() -> str:
    return git("rev-parse", "--short", "HEAD") or ""


def commit_days() -> dict | None:
    """Commits per author day over the whole history, for the site's activity heatmap."""
    log = git("log", "--format=%ad", "--date=short")
    if log is None:
        return None
    days = {}
    for day in log.split():
        days[day] = days.get(day, 0) + 1
    return {"total": sum(days.values()), "days": dict(sorted(days.items()))}


def kind_counts(theories) -> dict:
    """Declaration, statement and structure-command counts, as `theory-stats --view kinds`."""
    declarations, statements = {}, {}
    for t in theories:
        for kind, n in t.decls.items():
            declarations[kind] = declarations.get(kind, 0) + n
        for kind, n in statement_kinds(t).items():
            statements[kind] = statements.get(kind, 0) + n
    return {"declarations": declarations, "statements": statements}


def collect() -> dict:
    scanned = [scan_theory(p) for p in iter_theory_files(vendor=True)]
    vendored = set(VENDOR_SESSIONS.values())
    theories = [t for t in scanned if t.session not in vendored]
    solver = [t for t in scanned if t.session in vendored]
    sessions = {}
    for t in theories:
        s = sessions.setdefault(
            t.session,
            {
                "name": t.session,
                "theories": 0,
                "lines": 0,
                "code": 0,
                "doc": 0,
                "defs": 0,
                "proofs": 0,
            },
        )
        s["theories"] += 1
        s["lines"] += t.lines
        s["code"] += t.code_lines
        s["doc"] += t.doc_lines
        s["defs"] += t.n_decls
        s["proofs"] += t.n_proofs

    # The vendored development holds solver variants Voblint never loads; the page
    # distinguishes the theories Voblint's imports reach from the whole directory.
    solver_used = [scan_theory(p) for p in session_graph.imported_theories("TD")]

    handwritten = [
        p
        for p in sorted(CLI_DIR.rglob("*.ml"))
        if p.name not in GENERATED_CLI and "_build" not in p.parts
    ]

    directories = {}
    for t in theories:
        directory = source_directory(t) or "outside_src"
        directories[directory] = directories.get(directory, 0) + t.lines

    cases = sorted(CORPUS_DIR.rglob("*.vimp"))
    groups = sorted(d.name for d in CORPUS_DIR.iterdir() if d.is_dir())
    by_group = {group: 0 for group in groups}
    kinds = {kind: 0 for kind in CORPUS_KINDS + ("other",)}
    for case in cases:
        parts = case.relative_to(CORPUS_DIR).parts
        kind = next((k for k in CORPUS_KINDS if k in parts), "other")
        kinds[kind] += 1
        if parts[0] in by_group:
            by_group[parts[0]] += 1

    return {
        "commit": commit(),
        "commit_sha": git("rev-parse", "HEAD") or "",
        "date": date.today().isoformat(),
        "commits": commit_days(),
        "isabelle": {
            "theories": len(theories),
            "lines": sum(t.lines for t in theories),
            "code": sum(t.code_lines for t in theories),
            "doc": sum(t.doc_lines for t in theories),
            "defs": sum(t.n_decls for t in theories),
            "proofs": sum(t.n_proofs for t in theories),
            "kinds": kind_counts(theories),
            "sessions": sorted(sessions.values(), key=lambda s: -s["lines"]),
            "directories": dict(sorted(directories.items())),
        },
        "solver": {
            "theories": len(solver),
            "lines": sum(t.lines for t in solver),
            "defs": sum(t.n_decls for t in solver),
            "proofs": sum(t.n_proofs for t in solver),
            "used": {
                "names": [t.theory for t in solver_used],
                "theories": len(solver_used),
                "lines": sum(t.lines for t in solver_used),
                "code": sum(t.code_lines for t in solver_used),
                "doc": sum(t.doc_lines for t in solver_used),
                "defs": sum(t.n_decls for t in solver_used),
                "proofs": sum(t.n_proofs for t in solver_used),
            },
        },
        "sessions": session_graph.collect(),
        "semantics": {
            "theories": len(SEMANTICS_THEORIES),
            "lines": sum(
                count_lines(VIMP_DIR / f"{t}.thy") for t in SEMANTICS_THEORIES
            ),
            "pstep_rules": pstep_rules(),
        },
        "generated_ocaml": count_lines(GENERATED_ML),
        "handwritten_ocaml": sum(count_lines(p) for p in handwritten),
        "corpus": {
            "cases": len(cases),
            "groups": len(groups),
            "lines": sum(count_lines(p) for p in cases),
            "kinds": kinds,
            "by_group": by_group,
        },
        "eval_witnesses": sum(
            p.read_text(encoding="utf-8", errors="replace").count("by eval")
            for p in EXAMPLES_DIR.rglob("*.thy")
        ),
    }


def main() -> int:
    ap = argparse.ArgumentParser(
        description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter
    )
    ap.add_argument("--out", type=Path, help="script to write; stdout when omitted")
    args = ap.parse_args()

    missing = [root for root in VENDOR_SESSIONS if not (root / "ROOT").is_file()]
    if missing:
        # A silent zero would publish a wrong solver count and session graph.
        for root in missing:
            print(
                f"pages_stats: {root.relative_to(REPO_ROOT)} is not checked out; "
                "run `pixi run vendor-init` (CI: initialize the submodule)",
                file=sys.stderr,
            )
        return 1

    if git("rev-parse", "--is-shallow-repository") == "true":
        # A shallow clone would publish a heatmap of the last few commits only.
        print(
            "pages_stats: the checkout is shallow; fetch the full history "
            "(CI: actions/checkout with fetch-depth: 0)",
            file=sys.stderr,
        )
        return 1

    script = f"window.VOBLINT_STATS = {json.dumps(collect(), indent=2)};\n"
    if args.out:
        args.out.parent.mkdir(parents=True, exist_ok=True)
        args.out.write_text(script, encoding="utf-8")
    else:
        sys.stdout.write(script)
    return 0


if __name__ == "__main__":
    sys.exit(main())
