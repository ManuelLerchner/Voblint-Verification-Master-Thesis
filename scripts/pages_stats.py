#!/usr/bin/env python3
"""Repository size figures for the Pages explainer.

Writes a classic script assigning `window.VOBLINT_STATS`, which the page reads
at load. A script rather than JSON because the explainer must also open from
file://, where fetch is blocked; a missing file leaves the page's fallback
figures in place.

Isabelle figures reuse thy_stats.py's scanner, so the page and
`pixi run theory-stats` never disagree. The OCaml counts are plain line
counts.
"""
import argparse
import json
import subprocess
import sys
from datetime import date
from pathlib import Path

from extract_definitions import VENDOR_SESSIONS, iter_theory_files
from thy_stats import scan_theory

REPO_ROOT = Path(__file__).resolve().parent.parent
GENERATED_ML = REPO_ROOT / "codegen" / "generated" / "ml" / "Voblint_CLI.ml"
CLI_DIR = REPO_ROOT / "cli"
CORPUS_DIR = REPO_ROOT / "tests" / "regression"
EXAMPLES_DIR = REPO_ROOT / "src" / "Examples"
# tests/run.py's placement convention: what the concrete program does.
CORPUS_KINDS = ("precision", "soundness", "known-imprecision")
# Emitted from manifests/vimp-grammar.yaml, so not handwritten.
GENERATED_CLI = {"vimp_printer.ml", "vimp_parser.mly", "vimp_lexer.mll"}


def count_lines(path: Path) -> int:
    with path.open(encoding="utf-8", errors="replace") as f:
        return sum(1 for _ in f)


def commit() -> str:
    try:
        return subprocess.run(
            ["git", "rev-parse", "--short", "HEAD"], cwd=REPO_ROOT,
            capture_output=True, text=True, check=True,
        ).stdout.strip()
    except (OSError, subprocess.CalledProcessError):
        return ""


def collect() -> dict:
    scanned = [scan_theory(p) for p in iter_theory_files(vendor=True)]
    vendored = set(VENDOR_SESSIONS.values())
    theories = [t for t in scanned if t.session not in vendored]
    solver = [t for t in scanned if t.session in vendored]
    sessions = {}
    for t in theories:
        s = sessions.setdefault(t.session, {
            "name": t.session, "theories": 0, "lines": 0, "code": 0, "doc": 0,
            "defs": 0, "proofs": 0,
        })
        s["theories"] += 1
        s["lines"] += t.lines
        s["code"] += t.code_lines
        s["doc"] += t.doc_lines
        s["defs"] += t.n_decls
        s["proofs"] += t.n_proofs

    handwritten = [
        p for p in sorted(CLI_DIR.rglob("*.ml"))
        if p.name not in GENERATED_CLI and "_build" not in p.parts
    ]

    cases = sorted(CORPUS_DIR.rglob("*.vimp"))
    kinds = {kind: 0 for kind in CORPUS_KINDS + ("other",)}
    for case in cases:
        parts = case.relative_to(CORPUS_DIR).parts
        kind = next((k for k in CORPUS_KINDS if k in parts), "other")
        kinds[kind] += 1

    return {
        "commit": commit(),
        "date": date.today().isoformat(),
        "isabelle": {
            "theories": len(theories),
            "lines": sum(t.lines for t in theories),
            "code": sum(t.code_lines for t in theories),
            "doc": sum(t.doc_lines for t in theories),
            "defs": sum(t.n_decls for t in theories),
            "proofs": sum(t.n_proofs for t in theories),
            "sessions": sorted(sessions.values(), key=lambda s: -s["lines"]),
        },
        "solver": {
            "theories": len(solver),
            "lines": sum(t.lines for t in solver),
            "defs": sum(t.n_decls for t in solver),
            "proofs": sum(t.n_proofs for t in solver),
        },
        "generated_ocaml": count_lines(GENERATED_ML),
        "handwritten_ocaml": sum(count_lines(p) for p in handwritten),
        "corpus": {
            "cases": len(cases),
            "groups": sum(1 for d in CORPUS_DIR.iterdir() if d.is_dir()),
            "lines": sum(count_lines(p) for p in cases),
            "kinds": kinds,
        },
        "eval_witnesses": sum(
            p.read_text(encoding="utf-8", errors="replace").count("by eval")
            for p in EXAMPLES_DIR.rglob("*.thy")
        ),
    }


def main() -> int:
    ap = argparse.ArgumentParser(description=__doc__,
                                 formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument("--out", type=Path, help="script to write; stdout when omitted")
    args = ap.parse_args()

    script = f"window.VOBLINT_STATS = {json.dumps(collect(), indent=2)};\n"
    if args.out:
        args.out.parent.mkdir(parents=True, exist_ok=True)
        args.out.write_text(script, encoding="utf-8")
    else:
        sys.stdout.write(script)
    return 0


if __name__ == "__main__":
    sys.exit(main())
