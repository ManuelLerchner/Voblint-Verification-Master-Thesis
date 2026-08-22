#!/usr/bin/env python3
"""Emit an HTML report for every regression fixture and check it holds together.

The structural test pins one fixture's report in detail; this sweeps the whole
corpus for the faults that only show up on particular programs -- a graph
referencing a node with no document, a warning pointing past the end of the
file, a state leaking into a node label on a domain that renders wider than the
one the test uses.

Each fixture runs under its own PARAM line, so the sweep exercises the same
domain, context and solver combinations the corpus already covers.

    python3 scripts/audit_html_reports.py            # sweep, report problems
    python3 scripts/audit_html_reports.py --verbose  # list every fixture
    python3 scripts/audit_html_reports.py -k 17-     # only matching fixtures

Exits non-zero if any fixture produced a report with a problem in it.
"""

import argparse
import re
import shutil
import subprocess
import sys
import tempfile
import xml.etree.ElementTree as ET
from pathlib import Path

REPO_ROOT = Path(__file__).resolve().parent.parent
VOBLINT = REPO_ROOT / "cli" / "voblint"
CORPUS = REPO_ROOT / "tests" / "regression"

# The frontend's stylesheet defines exactly these; anything else renders bare.
SHT_TYPES = {"nr", "pp", "tk", "sk", "op", "sp", "cm", "st"}

# Flags that decide what gets written, not how the analysis runs. --html
# replaces them, so they are dropped from the fixture's own PARAM line.
OUTPUT_FLAGS = {"--dot", "--dot-full", "--graph-snapshot", "--parse-only"}

# tests/run.py's own rule: a fixture with no inline verdict documents a
# rejection rather than a report, so there is no report here to audit.
VERDICT_RE = re.compile(r"//\s*(reachable|NOWARN|PROVED|REFUTED|UNKNOWN)")


def param_args(fixture: Path) -> list[str] | None:
    first = fixture.read_text().splitlines()[0]
    if not first.startswith("// PARAM:"):
        return None
    args = first[len("// PARAM:"):].split()
    return [a for a in args if a not in OUTPUT_FLAGS]


def skip_reason(fixture: Path) -> str | None:
    args = param_args(fixture)
    if args is None:
        return "no PARAM line"
    if not VERDICT_RE.search(fixture.read_text()):
        return "documents a rejection, not a report"
    if "--solver" in args and "--context" in args:
        # analyse_config_ctx honours the solver contextually
        # (Plan_Interval_EntryState Solver_Join -> analyse_interval_entry_state_join),
        # but those routes publish verdict reports, not solved state tables, so
        # there is no per-node state to read for that pairing yet.
        return "--solver with --context has no per-node state table yet"
    return None


def audit_one(fixture: Path, out: Path) -> list[str]:
    """Returns a list of problems; empty means the report is coherent."""
    args = param_args(fixture)
    if args is None:
        return []
    proc = subprocess.run(
        [str(VOBLINT), *args, "--html-out", str(out), str(fixture)],
        capture_output=True, text=True,
    )
    if proc.returncode != 0:
        return [f"exit {proc.returncode}: {(proc.stderr or proc.stdout).strip()[:200]}"]

    problems: list[str] = []
    seg = fixture.name

    # 1. Every emitted document must parse. A malformed one renders as nothing,
    #    silently, which is the failure mode this sweep exists to catch.
    docs = list(out.rglob("*.xml"))
    for doc in docs:
        try:
            ET.parse(doc)
        except ET.ParseError as e:
            problems.append(f"malformed XML in {doc.relative_to(out)}: {e}")
    if problems:
        return problems

    # 2. The graph and the node documents have to agree: clicking a node in the
    #    SVG fetches nodes/<id>.xml by name.
    dot_file = out / "dot" / seg / "main.dot"
    if not dot_file.is_file():
        return [f"missing {dot_file.relative_to(out)}"]
    dot = dot_file.read_text()
    drawn = set(re.findall(r"^\s{4}(\S+) \[", dot, re.MULTILINE))
    have = {p.stem for p in (out / "nodes").glob("*.xml")} - {"globals"}
    for node in sorted(drawn - have):
        problems.append(f"graph draws {node} with no nodes/{node}.xml")

    # 3. Edges must not dangle: graphviz would still lay it out, inventing a
    #    node, so this cannot be left to `dot` to notice.
    for src, dst in re.findall(r"^\s{2}(\S+) -> (\S+) \[", dot, re.MULTILINE):
        for end in (src, dst):
            if end not in drawn:
                problems.append(f"edge endpoint {end} is not a drawn node")

    # 4. States belong in node documents. A multi-line label is --dot-full's
    #    failure, and the whole reason this output exists.
    for line in dot.splitlines():
        if "label=" in line and "->" not in line and "subgraph" not in line:
            if "\\n" in line:
                problems.append(f"state leaked into a node label: {line.strip()[:90]}")

    # 5. The graph has to render. A DOT syntax error is invisible until this.
    if shutil.which("dot"):
        svg = subprocess.run(
            ["dot", "-Tsvg", str(dot_file), "-o", str(out / "rendered.svg")],
            capture_output=True, text=True,
        )
        if svg.returncode != 0:
            problems.append(f"dot -Tsvg failed: {svg.stderr.strip()[:200]}")

    # 6. Source view: highlighting present, classes inside the palette, and one
    #    <ln> per source line so line numbers line up with the file.
    src_doc = out / "files" / f"{seg}.xml"
    if not src_doc.is_file():
        problems.append(f"missing files/{seg}.xml")
    else:
        text = src_doc.read_text()
        types = set(re.findall(r'<sht type="([a-z]+)"', text))
        if not types:
            problems.append("source view has no highlighting")
        for bad in sorted(types - SHT_TYPES):
            problems.append(f"highlight class outside the palette: {bad}")
        lines = ET.parse(src_doc).getroot().findall("ln")
        # splitlines, not split("\n"): a trailing newline ends the last line, it
        # does not begin another one.
        expected = len(fixture.read_text().splitlines())
        if len(lines) != expected:
            problems.append(f"source view has {len(lines)} lines, file has {expected}")
        numbers = [int(ln.get("nr")) for ln in lines]
        if numbers != list(range(1, len(lines) + 1)):
            problems.append("source line numbers are not consecutive from 1")

        # 7. Every warning a line references must exist, and point into the file.
        for ref in set(re.findall(r"&quot;(warn\d+)&quot;", text)):
            warn = out / "warn" / f"{ref}.xml"
            if not warn.is_file():
                problems.append(f"line references {ref} with no warn/{ref}.xml")
                continue
            piece = ET.parse(warn).getroot().find("text")
            line = int(piece.get("line"))
            if not 1 <= line <= expected:
                problems.append(f"{ref} points at line {line}, file has {expected}")

    # 8. The frontend itself has to be there, or none of the above is reachable.
    for asset in ("report.xsl", "node.xsl", "file.xsl", "frame.html", "script.js"):
        if not (out / asset).is_file():
            problems.append(f"missing frontend asset {asset}")

    return problems


def main() -> int:
    ap = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    ap.add_argument("-k", dest="filter", default="", help="only fixtures matching this")
    ap.add_argument("--verbose", action="store_true", help="list every fixture")
    args = ap.parse_args()

    if not VOBLINT.exists():
        print("cli/voblint not built -- run `pixi run cli-build`", file=sys.stderr)
        return 2

    fixtures = sorted(
        f for f in CORPUS.rglob("*.vimp") if args.filter in str(f.relative_to(CORPUS))
    )
    failures = 0
    skips: dict[str, int] = {}
    with tempfile.TemporaryDirectory() as tmp:
        for i, fixture in enumerate(fixtures):
            rel = fixture.relative_to(CORPUS)
            reason = skip_reason(fixture)
            if reason is not None:
                skips[reason] = skips.get(reason, 0) + 1
                if args.verbose:
                    print(f"skip {rel} ({reason})")
                continue
            out = Path(tmp) / f"r{i}"
            problems = audit_one(fixture, out)
            shutil.rmtree(out, ignore_errors=True)
            if problems:
                failures += 1
                print(f"FAIL {rel}")
                for p in problems:
                    print(f"       {p}")
            elif args.verbose:
                print(f"ok   {rel}")

    checked = len(fixtures) - sum(skips.values())
    print(f"\n{checked} report(s) audited, {failures} with problems")
    for reason, n in sorted(skips.items()):
        print(f"  {n} skipped: {reason}")
    return 1 if failures else 0


if __name__ == "__main__":
    sys.exit(main())
