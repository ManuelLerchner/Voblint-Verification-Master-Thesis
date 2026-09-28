#!/usr/bin/env python3
"""Check that the domain trees of chapter 5 list every implementation.

`shared/domain-tree.toml` lists, per figure node, the instances drawn under
"instantiated by" or "proved by". The figure verifies that each listed instance
exists and targets its node, but not that the list is complete. This scans the
theories for every class instantiation and every unconditional lemma stating a
listed node (or a strengthening named `<node>_...`) and fails when one is not
listed, so a new domain cannot silently drop out of the figure.
"""

from __future__ import annotations

import re
import sys
from pathlib import Path

import tomllib

REPO = Path(__file__).resolve().parents[2]
TREES = REPO / "thesis/shared/domain-tree.toml"
SNIPPETS = REPO / "thesis/shared/snippets.toml"

INSTANTIATION = re.compile(
    r"^instantiation\s+(\S+)\s*::\s*(?:\([^)]*\)\s*)?(\w+)", re.M
)
# An unconditional lemma whose statement opens with a locale predicate.
LEMMA = re.compile(r"^lemma\s+(\w+)\s*(?:\[[^\]]*\])?:\s*\n?\s*\"(\w+)\s", re.M)


def main() -> int:
    trees = tomllib.loads(TREES.read_text())
    snippets = tomllib.loads(SNIPPETS.read_text())["snippets"]
    theories = [p for p in (REPO / "src").rglob("*.thy") if "generated" not in p.parts]
    texts = [p.read_text(errors="ignore") for p in theories]

    missing: list[str] = []
    for key, tree in trees.items():
        for node, listed in tree.get("interpreted", {}).items():
            listed_instances = {snippets.get(n, {}).get("instance") for n in listed}
            for text in texts:
                for ty, cls in INSTANTIATION.findall(text):
                    if cls == node and f"{ty} :: {cls}" not in listed_instances:
                        missing.append(f"{key}/{node}: instantiation {ty} :: {cls}")
                for name, locale in LEMMA.findall(text):
                    if (
                        locale == node or locale.startswith(node + "_")
                    ) and name not in listed:
                        missing.append(f"{key}/{node}: lemma {name} ({locale})")

    if missing:
        print("domain_tree: implementations missing from shared/domain-tree.toml:")
        for m in sorted(set(missing)):
            print(f"  {m}")
        print("List each under `interpreted` (with a snippets.toml entry), or drop it.")
        return 1
    print("domain_tree: every implementation of a drawn interface is listed")
    return 0


if __name__ == "__main__":
    sys.exit(main())
