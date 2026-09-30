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

sys.path.insert(0, str(REPO / "scripts"))
from isar_json import hierarchy, instances, names  # noqa: E402

# A statement whose first proposition is a locale predicate: `lemma n: "loc args"`.
PREDICATE = re.compile(r'^lemma\s+\w+\s*(?:\[[^\]]*\])?:\s*"(\w+)\s+([^"]*)"')


def own(row: dict) -> bool:
    """Declared in a theory of src/, not a generated one."""
    return row["path"].startswith("src/") and "/generated/" not in row["path"]


def instantiations() -> list[tuple[str, str]]:
    """`(type, class)` of every class instantiation."""
    return [
        tuple(i["name"].split(" :: "))
        for i in instances(str(REPO))
        if i["command"] == "instantiation" and own(i)
    ]


def interpretations() -> list[tuple[str, str, str]]:
    """`(qualifier, locale, arguments)` of every global interpretation."""
    return [
        (i["name"], i["target"], i["arguments"])
        for i in instances(str(REPO))
        if i["command"] == "global_interpretation" and own(i)
    ]


def certificates() -> list[tuple[str, str, str]]:
    """`(lemma, locale, arguments)` of every lemma whose statement is a locale
    predicate."""
    found = []
    for row in names(str(REPO), statements=True):
        if row["command"] == "lemma" and own(row):
            m = PREDICATE.match(" ".join(row["statement"].split()))
            if m:
                found.append((row["name"].rsplit(".", 1)[1], m[1], m[2]))
    return found


def locale_parents() -> dict[str, list[str]]:
    """Each locale's declared parents, with qualifiers such as `backward:` dropped."""
    return {
        d["name"]: d["parents"] for d in hierarchy(str(REPO)) if d["kind"] == "locale"
    }


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
    parents = locale_parents()
    instance_rows, lemmas, interps = instantiations(), certificates(), interpretations()

    missing: list[str] = []
    for key, tree in trees.items():
        for node, strengthening in tree.get("mono", {}).items():
            if strengthening not in parents:
                missing.append(f"{key}/{node}: no locale {strengthening}")
            elif not extends(strengthening, node, parents):
                missing.append(f"{key}/{node}: {strengthening} does not extend {node}")
        for node, listed in tree.get("interpreted", {}).items():
            listed_instances = {snippets.get(n, {}).get("name") for n in listed}
            # A listed interpretation covers the lemma it is built from.
            covered = {bundle(arg) for name, _, arg in interps if name in listed}
            for ty, cls in instance_rows:
                if cls == node and f"{ty} :: {cls}" not in listed_instances:
                    missing.append(f"{key}/{node}: instantiation {ty} :: {cls}")
            for name, locale, arg in lemmas:
                if (
                    (locale == node or locale.startswith(node + "_"))
                    and name not in listed
                    and bundle(arg) not in covered
                ):
                    missing.append(f"{key}/{node}: lemma {name} ({locale})")
            for name, locale, _ in interps:
                if extends(locale, node, parents) and name not in listed:
                    missing.append(f"{key}/{node}: interpretation {name} ({locale})")

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
