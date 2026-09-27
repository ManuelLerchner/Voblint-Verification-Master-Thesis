#!/usr/bin/env python3
"""Repository size figures for the Pages explainer.

Writes a classic script assigning `window.VOBLINT_STATS`, which the page's
figure scripts read at load. A script rather than JSON because the explainer
must also open from file://, where fetch is blocked. With `--fill`, the same
collection also writes every `[data-stat]` figure into the built HTML, so the
published page carries real numbers without running any script. The sources
keep the neutral FALLBACK there, which cannot go stale.

Isabelle figures come from isar-tools (scripts/isar_json.py), which parses the
theories, so the page and `pixi run theory-stats` (`isar stats`) never
disagree; what counts as a definition or a lemma is fixed in isar_json.py. The
session graph behind the strata figure comes from session_graph.py. The OCaml
counts are plain line counts.
"""

import argparse
import json
import re
import subprocess
import sys
from datetime import date
from pathlib import Path

import session_graph
from isar_json import (
    DEFINITION_COMMANDS,
    STRUCTURE_COMMANDS,
    THEOREM_COMMANDS,
    command_counts,
    sessions,
    theory_command_counts,
    theory_sizes,
)

REPO_ROOT = Path(__file__).resolve().parent.parent
TD_DIR = REPO_ROOT / "vendor" / "td-verification"
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


# What a source checkout shows for a figure; the site build replaces it.
FALLBACK = "\u2014"
DATA_STAT = re.compile(r'(data-stat="([^"]+)"[^>]*>)([^<]*)(<)')


def lookup(stats: dict, key: str):
    """The value of a dotted `data-stat` key, or None when nothing is measured under it."""
    value = stats
    for part in key.split("."):
        value = value.get(part) if isinstance(value, dict) else None
    return value


def fill(html: str, stats: dict) -> str:
    """Write every `[data-stat]` figure into `html`; an unknown key is an error."""

    def figure(match: re.Match) -> str:
        value = lookup(stats, match.group(2))
        if value is None or isinstance(value, dict):
            raise KeyError(f"data-stat={match.group(2)!r} names no measured figure")
        text = f"{value:,}" if isinstance(value, int) else str(value)
        return match.group(1) + text + match.group(4)

    return DATA_STAT.sub(figure, html)


def flatten(node: dict, prefix: str = ""):
    """(dotted key, int) pairs of a nested stats dict; lists are not addressable."""
    for key, value in node.items():
        if isinstance(value, dict):
            yield from flatten(value, f"{prefix}{key}.")
        elif isinstance(value, int):
            yield f"{prefix}{key}", value


def source_directory(path: str) -> str | None:
    """Top-level directory below src/ holding the theory, or None outside src/."""
    parts = Path(path).parts
    return parts[1] if len(parts) > 2 and parts[0] == "src" else None


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


def count(counts: dict[str, int], commands) -> int:
    return sum(counts.get(c, 0) for c in commands)


def kind_counts(counts: dict[str, int]) -> dict:
    """Declaration, statement and structure-command counts, as `theory-stats commands`."""
    return {
        "declarations": {c: counts[c] for c in DEFINITION_COMMANDS if counts.get(c)},
        "statements": {
            c: counts[c] for c in THEOREM_COMMANDS + STRUCTURE_COMMANDS if counts.get(c)
        },
    }


def add(total: dict[str, int], counts: dict[str, int]) -> dict[str, int]:
    for command, n in counts.items():
        total[command] = total.get(command, 0) + n
    return total


def collect() -> dict:
    # Sizes per theory and command counts per session, from isar-tools. The
    # project's own theories are those under src/; the vendored TD sessions
    # (vendor/td-verification) are the solver.
    theories = [t for t in theory_sizes(".") if source_directory(t["path"])]
    own_commands = command_counts(".")
    session_directory = {
        s["session"]: source_directory(s["directory"] + "/.") for s in sessions(".")
    }
    solver = theory_sizes("vendor/td-verification") if TD_DIR.is_dir() else []
    solver = [t for t in solver if t["session"] != "-"]
    solver_commands = (
        add(
            {},
            *[
                c
                for n, c in command_counts("vendor/td-verification").items()
                if n != "-"
            ],
        )
        if solver
        else {}
    )

    areas = {}
    for t in theories:
        g = areas.setdefault(
            source_directory(t["path"]),
            {
                "name": source_directory(t["path"]),
                "theories": 0,
                "lines": 0,
                "code": 0,
                "doc": 0,
                "defs": 0,
                "proofs": 0,
            },
        )
        g["theories"] += 1
        g["lines"] += t["lines"]
        g["code"] += t["code_lines"]
        g["doc"] += t["doc_lines"]
    all_commands: dict[str, int] = {}
    for session, counts in own_commands.items():
        directory = session_directory.get(session)
        if directory is None:
            continue
        add(all_commands, counts)
        if directory in areas:
            areas[directory]["defs"] += count(counts, DEFINITION_COMMANDS)
            areas[directory]["proofs"] += count(counts, THEOREM_COMMANDS)

    # The vendored development holds solver variants Voblint never loads; the page
    # distinguishes the theories Voblint's imports reach from the whole directory.
    used_names = (
        [n.split(".", 1)[1] for n in session_graph.imported_theories("TD")]
        if solver
        else []
    )
    solver_used = sorted(
        (t for t in solver if t["theory"] in used_names), key=lambda t: t["theory"]
    )
    per_theory = theory_command_counts("vendor/td-verification") if solver else {}
    used_commands: dict[str, int] = {}
    for t in solver_used:
        add(used_commands, per_theory.get((t["session"], t["theory"]), {}))

    handwritten = [
        p
        for p in sorted(CLI_DIR.rglob("*.ml"))
        if p.name not in GENERATED_CLI and "_build" not in p.parts
    ]

    directories = {}
    for t in theories:
        directory = source_directory(t["path"])
        directories[directory] = directories.get(directory, 0) + t["lines"]

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
            "lines": sum(t["lines"] for t in theories),
            "code": sum(t["code_lines"] for t in theories),
            "doc": sum(t["doc_lines"] for t in theories),
            "defs": count(all_commands, DEFINITION_COMMANDS),
            "proofs": count(all_commands, THEOREM_COMMANDS),
            "kinds": kind_counts(all_commands),
            "sessions": sorted(areas.values(), key=lambda g: -g["lines"]),
            "directories": dict(sorted(directories.items())),
        },
        "solver": {
            "theories": len(solver),
            "lines": sum(t["lines"] for t in solver),
            "defs": count(solver_commands, DEFINITION_COMMANDS),
            "proofs": count(solver_commands, THEOREM_COMMANDS),
            "used": {
                "names": [t["theory"] for t in solver_used],
                "theories": len(solver_used),
                "lines": sum(t["lines"] for t in solver_used),
                "code": sum(t["code_lines"] for t in solver_used),
                "doc": sum(t["doc_lines"] for t in solver_used),
                "defs": count(used_commands, DEFINITION_COMMANDS),
                "proofs": count(used_commands, THEOREM_COMMANDS),
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
    ap.add_argument(
        "--fill",
        type=Path,
        nargs="*",
        default=[],
        help="built HTML files whose [data-stat] figures to write in place",
    )
    args = ap.parse_args()

    if not (TD_DIR / "ROOT").is_file():
        # A silent zero would publish a wrong solver count and session graph.
        print(
            f"pages_stats: {TD_DIR.relative_to(REPO_ROOT)} is not checked out; "
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

    stats = collect()
    for page in args.fill:
        page.write_text(fill(page.read_text(encoding="utf-8"), stats), encoding="utf-8")

    script = f"window.VOBLINT_STATS = {json.dumps(stats, indent=2)};\n"
    if args.out:
        args.out.parent.mkdir(parents=True, exist_ok=True)
        args.out.write_text(script, encoding="utf-8")
    else:
        sys.stdout.write(script)
    return 0


if __name__ == "__main__":
    sys.exit(main())
