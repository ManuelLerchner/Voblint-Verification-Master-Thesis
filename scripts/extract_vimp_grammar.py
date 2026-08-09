#!/usr/bin/env python3
"""Feasibility prototype: extract a normalized grammar IR from
VIMP_Notation.thy's `syntax` block (its Isabelle mixfix productions).

This is read-only and does not touch Isabelle's PIDE/jEdit document state --
it operates on the theory file as plain text, the same way
scripts/normalize_isabelle_ascii.py and scripts/check_isabelle_ascii.py
already do for other purposes.

Answers, empirically: how much of the source grammar can be recovered
automatically from the syntax block alone (nonterminal typing, template,
precedence, associativity), versus what still needs the parse_translation
block (AST-constructor/lowering) or manual authoring (this script only
covers `syntax`, not `parse_translation`).

Usage: python3 scripts/extract_vimp_grammar.py [path/to/VIMP_Notation.thy]
"""

import json
import re
import sys
from pathlib import Path

DEFAULT_PATH = Path(__file__).resolve().parent.parent / "src" / "VIMP" / "VIMP_Notation.thy"

ARROW = r"\\<Rightarrow>"

# One production, after continuation lines have been joined with a single
# space (see `entries()`). The type is either a bare identifier (nullary
# production, e.g. `imp2_stmt`) or a quoted arrow-chain (`"T1 \<Rightarrow> ... \<Rightarrow>
# Tn"`); the mixfix annotation is `("template")`, `("template" prio)`, or
# `("template" [p1, p2, ...] prio)`.
PRODUCTION_RE = re.compile(
    r'^"(?P<name>_\w+)"\s*::\s*'
    r'(?P<type>"[^"]*"|\w+)\s*'
    r'\(\s*"(?P<template>(?:[^"\\]|\\.)*)"'
    r'(?:\s*\[(?P<prios>[^\]]*)\])?'
    r'(?:\s*(?P<result_prio>\d+))?'
    r'\s*\)\s*$'
)


def entries(block_text: str):
    """Joins each production's continuation lines (e.g. _imp2_if, which
    wraps its type and mixfix annotation onto a second physical line) into
    one logical line per production."""
    joined = []
    for line in block_text.splitlines():
        stripped = line.strip()
        if not stripped:
            continue
        if re.match(r'^"_\w+"\s*::', stripped):
            joined.append(stripped)
        elif joined:
            joined[-1] += " " + stripped
    return joined


def parse_type(type_field: str):
    """Splits an arrow-chain type into (arg_types, result_type). A bare
    identifier (no arrows) is a nullary production: no args, that type as
    the result."""
    inner = type_field.strip('"')
    parts = [p.strip() for p in re.split(ARROW, inner)]
    return parts[:-1], parts[-1]


def unescape_template(template: str) -> str:
    """Isabelle mixfix escapes a literal character C that would otherwise be
    read as markup (parens, underscore) as 'C. Un-escaping gives the actual
    surface token sequence, e.g. "_'(')" -> "_()" (an id, then a literal
    "()"), "'_'_voblint'_check '( _ ')" -> "_voblint_check ( _ )"."""
    return re.sub(r"'(.)", r"\1", template)


def parse_production(line: str):
    m = PRODUCTION_RE.match(line)
    if not m:
        return None
    args, result = parse_type(m.group("type"))
    prios = [int(p.strip()) for p in m.group("prios").split(",")] if m.group("prios") else []
    result_prio = int(m.group("result_prio")) if m.group("result_prio") else None
    return {
        "name": m.group("name"),
        "args": args,
        "result": result,
        "template": m.group("template"),
        "surface": unescape_template(m.group("template")),
        "arg_priorities": prios,
        "result_priority": result_prio,
    }


def extract(text: str):
    block = re.search(r"^syntax\n(.*?)^parse_translation", text, re.MULTILINE | re.DOTALL)
    if not block:
        raise SystemExit("could not locate syntax ... parse_translation block")
    productions, unparsed = [], []
    for line in entries(block.group(1)):
        p = parse_production(line)
        (productions if p else unparsed).append(p or line)
    return productions, unparsed


def main():
    path = Path(sys.argv[1]) if len(sys.argv) > 1 else DEFAULT_PATH
    text = path.read_text()
    productions, unparsed = extract(text)
    print(f"# extracted {len(productions)} productions, {len(unparsed)} unparsed lines", file=sys.stderr)
    for line in unparsed:
        print(f"# UNPARSED: {line}", file=sys.stderr)
    print(json.dumps(productions, indent=2))


if __name__ == "__main__":
    main()
