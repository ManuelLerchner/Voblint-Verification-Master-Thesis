#!/usr/bin/env python3
"""Check that the domain trees of chapter 5 list every implementation.

`shared/domain-tree.toml` lists, per figure node, the instances drawn under
"instantiated by" or "proved by". The figure verifies that each listed instance
exists and targets its node, but not that the list is complete. This scans the
theories for every class instantiation and every unconditional lemma stating a
listed node (or a strengthening named `<node>_...`) and fails when one is not
listed, so a new domain cannot silently drop out of the figure. An
interpretation counts for a node when it interprets the node or a locale
declared on top of it.

It also checks the `mono` table: each marked node must have its named
monotone strengthening, a locale that extends the node, directly or through
its parents.
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
LEMMA = re.compile(
    r"^lemma\s+(\w+)\s*(?:\[[^\]]*\])?:\s*\n?\s*\"(\w+)\s+([^\"]*)\"", re.M
)
INTERPRETATION = re.compile(r"^global_interpretation\s+(\w+)\s*:\s*(\w+)\s+(.*)$", re.M)
# A locale's parent expression: up to its `for`, `fixes`, `assumes` or `begin`.
LOCALE = re.compile(
    r"^locale\s+(\w+)\s*=\s*(.*?)(?=\bfor\b|\bfixes\b|\bassumes\b|^begin\b|^\S)",
    re.M | re.S,
)


def locale_parents(texts: list[str]) -> dict[str, list[str]]:
    """Each locale's declared parents, with qualifiers such as `backward:` dropped."""
    parents: dict[str, list[str]] = {}
    for text in texts:
        for name, expr in LOCALE.findall(text):
            names = []
            for part in expr.split("+"):
                words = part.split()
                if words and words[0].endswith(":"):
                    words = words[1:]
                if words:
                    names.append(words[0])
            parents[name] = names
    return parents


def bundle(arg: str) -> str:
    """The instance a certificate is about, with quotes and parentheses dropped."""
    return " ".join(arg.replace('"', " ").replace("(", " ").replace(")", " ").split())


def extends(locale: str, node: str, parents: dict[str, list[str]]) -> bool:
    seen, todo = set(), [locale]
    while todo:
        cur = todo.pop()
        if cur == node:
            return True
        if cur not in seen:
            seen.add(cur)
            todo.extend(parents.get(cur, []))
    return False


def main() -> int:
    trees = tomllib.loads(TREES.read_text())
    snippets = tomllib.loads(SNIPPETS.read_text())["snippets"]
    theories = [p for p in (REPO / "src").rglob("*.thy") if "generated" not in p.parts]
    texts = [p.read_text(errors="ignore") for p in theories]

    parents = locale_parents(texts)

    missing: list[str] = []
    for key, tree in trees.items():
        for node, strengthening in tree.get("mono", {}).items():
            if strengthening not in parents:
                missing.append(f"{key}/{node}: no locale {strengthening}")
            elif not extends(strengthening, node, parents):
                missing.append(f"{key}/{node}: {strengthening} does not extend {node}")
        for node, listed in tree.get("interpreted", {}).items():
            listed_instances = {snippets.get(n, {}).get("instance") for n in listed}
            # A listed interpretation covers the lemma it is built from.
            covered = {
                bundle(arg)
                for text in texts
                for name, _, arg in INTERPRETATION.findall(text)
                if name in listed
            }
            for text in texts:
                for ty, cls in INSTANTIATION.findall(text):
                    if cls == node and f"{ty} :: {cls}" not in listed_instances:
                        missing.append(f"{key}/{node}: instantiation {ty} :: {cls}")
                for name, locale, arg in LEMMA.findall(text):
                    if (
                        (locale == node or locale.startswith(node + "_"))
                        and name not in listed
                        and bundle(arg) not in covered
                    ):
                        missing.append(f"{key}/{node}: lemma {name} ({locale})")
                for name, locale, _ in INTERPRETATION.findall(text):
                    if extends(locale, node, parents) and name not in listed:
                        missing.append(
                            f"{key}/{node}: interpretation {name} ({locale})"
                        )

    if missing:
        print("domain_tree: shared/domain-tree.toml disagrees with the theories:")
        for m in sorted(set(missing)):
            print(f"  {m}")
        print("List each under `interpreted` (with a snippets.toml entry), or drop it.")
        return 1
    print(
        "domain_tree: every implementation of a drawn interface is listed, every M marker checked"
    )
    return 0


if __name__ == "__main__":
    sys.exit(main())
