#!/usr/bin/env python3
"""The regression corpus as examples for the Pages playground.

Writes JSON the playground fetches when its example browser opens: every fixture
under tests/regression, grouped by folder, with the analysis its PARAM header
selects and the source a reader should see. The header and the graph snapshot
are the runner's bookkeeping, so they are left out of that source; everything
else, verdict comments included, stays.

Headers are read by vimp_fixture.py, the reader tests/run.py uses, so an example
opens with exactly the settings its regression runs under.
"""

from __future__ import annotations

import argparse
import json
import re
import sys
from pathlib import Path

from vimp_fixture import (
    ARITHMETIC_HEADER,
    GRAPH_BEGIN,
    GRAPH_END,
    analysis_settings,
    param_args,
)

REPO_ROOT = Path(__file__).resolve().parent.parent
CORPUS = REPO_ROOT / "tests" / "regression"

# Fixtures picked to show what the analyzer does, one per aspect, with the one-line
# point each makes. They open first in the playground's example browser; a path
# that no longer names a fixture fails the build rather than dropping a card.
SHOWCASE = [
    (
        "20-nested-loops/precision/02-nested2_narrowing_recovers_j.vimp",
        "Widening, then narrowing",
        "Nested loops: the inner head widens j to [0,+inf] and narrows it back, "
        "so the outer counter is proved non-negative.",
    ),
    (
        "07-sign-precision/precision/06-tutorial_negative_join.vimp",
        "Dead code from a sign",
        "Goblint's tutorial in the Sign domain: a guard infeasible on a negative "
        "value leaves its whole arm unreachable.",
    ),
    (
        "21-context-sensitivity/precision/01-mutual_recursion_nonlinear_values.vimp",
        "Recursion, computed exactly",
        "Entry-state contexts evaluate mutual recursion value by value, and refute "
        "a wrong annotation carried over from Goblint.",
    ),
    (
        "17-call-string/precision/02-depth2_separates_shared_callee.vimp",
        "Call strings keep callers apart",
        "At depth 2, two activations of a shared callee no longer merge, so both "
        "results stay exact.",
    ),
    (
        "19-paper-examples/precision/03-per_origin_widening.vimp",
        "Widening per origin",
        "The FM 2026 paper's update rule: widening each call site's contribution "
        "separately recovers the precise bounds.",
    ),
    (
        "16-composite-domain/precision/09-remainder_reduction.vimp",
        "A reduced product",
        "Int combines Interval's bounds with Congruence's residue to pin a "
        "remainder no component decides alone.",
    ),
    (
        "22-congruence/precision/04-crt_narrows_shared_class.vimp",
        "The Chinese remainder theorem",
        "Intersecting x = 1 (mod 4) with y = 3 (mod 6) gives 9 (mod 12), which "
        "proves a branch dead.",
    ),
    (
        "23-arithmetic-diagnostics/precision/04-adc_peripheral.vimp",
        "A possible division by zero",
        "A recursive scan of four ADC channels: the average divides by a count "
        "that may be zero.",
    ),
    (
        "02-control-flow/known-imprecision/02-nonrelational_join.vimp",
        "A limit of the domains",
        "a != b holds on every run, but a non-relational join forgets which "
        "value of a pairs with which b.",
    ),
]

# The playground's own names for a PARAM header's settings.
PLAYGROUND_KEYS = {"context": "context", "context_depth": "k", "globals": "globals"}


def group_title(folder: Path) -> str:
    """A folder's README heading, or its name without the ordering prefix."""
    readme = folder / "README.md"
    if readme.is_file():
        for line in readme.read_text().splitlines():
            if line.startswith("# "):
                return line[2:].strip()
    return re.sub(r"^\d+-", "", folder.name).replace("-", " ").capitalize()


def summary(lines: list[str]) -> str:
    """The first paragraph of the comment block under the header."""
    words: list[str] = []
    for line in lines[1:]:
        text = line.strip()
        if not text.startswith("//") or text.startswith(
            (GRAPH_BEGIN, ARITHMETIC_HEADER)
        ):
            break
        body = text[2:].strip()
        if not body:
            if words:
                break
            continue
        words.append(body)
    return " ".join(words)


def shown_source(lines: list[str]) -> str:
    """The fixture without its header, arithmetic opt-in, and graph snapshot."""
    kept: list[str] = []
    in_graph = False
    for line in lines[1:]:
        text = line.strip()
        if text == GRAPH_BEGIN:
            in_graph = True
        elif text == GRAPH_END:
            in_graph = False
        elif not in_graph and text != ARITHMETIC_HEADER:
            kept.append(line)
    while kept and not kept[0].strip():
        kept.pop(0)
    return "\n".join(kept).rstrip() + "\n"


def example(path: Path) -> dict[str, object]:
    args = param_args(path)
    if args is None:
        raise ValueError(f"{path.relative_to(REPO_ROOT)}: no PARAM header")
    settings = analysis_settings(args)
    lines = path.read_text().splitlines()
    relative = path.relative_to(CORPUS)
    playground = {"analysis": settings["analyses"][0]} if "analyses" in settings else {}
    playground |= {
        name: settings[key] for key, name in PLAYGROUND_KEYS.items() if key in settings
    }
    return {
        "path": relative.as_posix(),
        "name": re.sub(r"^\d+-", "", path.stem).replace("_", " "),
        "category": relative.parts[1] if len(relative.parts) > 2 else None,
        "analyses": settings.get("analyses", []),
        "settings": playground,
        "summary": summary(lines),
        "source": shown_source(lines),
    }


def corpus() -> dict[str, object]:
    groups = []
    for folder in sorted(p for p in CORPUS.iterdir() if p.is_dir()):
        fixtures = [example(path) for path in sorted(folder.rglob("*.vimp"))]
        if fixtures:
            groups.append(
                {"id": folder.name, "title": group_title(folder), "fixtures": fixtures}
            )
    paths = {fixture["path"] for group in groups for fixture in group["fixtures"]}
    showcase = []
    for path, title, note in SHOWCASE:
        if path not in paths:
            raise ValueError(f"showcase fixture {path} is not in {CORPUS.name}")
        showcase.append({"path": path, "title": title, "note": note})
    return {"showcase": showcase, "groups": groups}


def main() -> int:
    ap = argparse.ArgumentParser(
        description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter
    )
    ap.add_argument("--out", type=Path, help="JSON file to write; stdout when omitted")
    args = ap.parse_args()

    try:
        text = json.dumps(corpus(), ensure_ascii=False, separators=(",", ":"))
    except ValueError as error:
        print(f"pages_examples: {error}", file=sys.stderr)
        return 1

    if args.out:
        args.out.parent.mkdir(parents=True, exist_ok=True)
        args.out.write_text(text)
    else:
        print(text)
    return 0


if __name__ == "__main__":
    sys.exit(main())
