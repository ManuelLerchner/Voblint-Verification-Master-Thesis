#!/usr/bin/env python3
"""The Isabelle session graph as the ROOT files and theory imports declare it.

A session rests on another when its ROOT names it as the parent, lists it under
`sessions`, or one of its theories imports a theory of it. The Pages explainer
draws the development as strata, one layer above the highest session each
session rests on; computing that from the sources keeps the drawing from
drifting when a session moves or an import is added.

Sessions, their theories, and resolved imports come from isar-tools' project
model (`isar project sessions|graph`), which reads ROOTS and ROOT files as
`isabelle build -D` does; sizes come from `isar stats sessions`, so they agree
with `pixi run theory-stats`. The vendored TD session is included when
vendor/td-verification is checked out.

Run directly to print the layers and any import that leaves what its ROOT makes
available.
"""

import sys

from isar_json import (
    TD_DIR,
    THEOREM_COMMANDS,
    command_counts,
    graph,
    session_sizes,
    sessions,
)


def _directories() -> list[str]:
    return ["."] + (["vendor/td-verification"] if (TD_DIR / "ROOT").is_file() else [])


def collect() -> list[dict]:
    """Every session with its declared relations, imports, depth and size."""
    by_name: dict[str, dict] = {}
    sizes: dict[str, dict] = {}
    commands: dict[str, dict[str, int]] = {}
    for directory in _directories():
        for s in sessions(directory):
            by_name.setdefault(
                s["session"],
                {
                    "name": s["session"],
                    "dir": s["directory"],
                    "parent": s["parent"],
                    "sessions": [],
                    "imports": set(),
                },
            )
        sizes.update(session_sizes(directory))
        commands.update(command_counts(directory))
    # Relations only after every session is known: `.` imports TD's theories.
    for directory in _directories():
        for edge in graph(directory)["edges"]:
            if edge["kind"] == "sessions" and edge["from"] in by_name:
                by_name[edge["from"]]["sessions"].append(edge["to"])
        # A theory edge between two sessions is an import of the other session.
        for edge in graph(directory, theories=True)["edges"]:
            source = edge["from"].split(".", 1)[0]
            target = edge["to"].split(".", 1)[0]
            if source in by_name and target in by_name and target != source:
                by_name[source]["imports"].add(target)

    def rests_on(s: dict) -> set[str]:
        return {n for n in {s["parent"], *s["sessions"], *s["imports"]} if n in by_name}

    depth: dict[str, int] = {}

    def depth_of(name: str) -> int:
        if name not in depth:
            depth[name] = 1 + max(
                (depth_of(n) for n in rests_on(by_name[name])), default=0
            )
        return depth[name]

    def size(name: str, key: str) -> int:
        return sizes.get(name, {}).get(key, 0)

    return [
        {
            "name": s["name"],
            "dir": s["dir"],
            "parent": s["parent"],
            "sessions": s["sessions"],
            "imports": sorted(s["imports"]),
            "rests_on": sorted(rests_on(s)),
            "depth": depth_of(s["name"]),
            "theories": size(s["name"], "theories"),
            "lines": size(s["name"], "lines"),
            "code": size(s["name"], "code_lines"),
            "doc": size(s["name"], "doc_lines"),
            "proofs": sum(
                commands.get(s["name"], {}).get(c, 0) for c in THEOREM_COMMANDS
            ),
        }
        for s in sorted(
            by_name.values(), key=lambda s: (depth_of(s["name"]), s["name"])
        )
    ]


def imported_theories(session: str) -> list[str]:
    """The theories of `session` that other sessions reach: their imports,
    closed under the imports among the session's own theories. Qualified names."""
    own_directory = next(
        d for d in _directories() if any(s["session"] == session for s in sessions(d))
    )
    todo = [
        edge["to"]
        for directory in _directories()
        if directory != own_directory
        for edge in graph(directory, theories=True)["edges"]
        if edge["to"].startswith(session + ".")
        and not edge["from"].startswith(session + ".")
    ]
    local = {}
    for edge in graph(own_directory, theories=True)["edges"]:
        local.setdefault(edge["from"], []).append(edge["to"])
    seen: set[str] = set()
    while todo:
        name = todo.pop()
        if name in seen:
            continue
        seen.add(name)
        todo += [t for t in local.get(name, []) if t.startswith(session + ".")]
    return sorted(seen)


def escaping_imports(sessions: list[dict]) -> list[str]:
    """Imports of sessions that neither the parent chain nor a listed session provides."""
    by_name = {s["name"]: s for s in sessions}
    problems = []
    for s in sessions:
        seen, todo = set(), [s["parent"], *s["sessions"]]
        while todo:
            n = todo.pop()
            if n in seen or n not in by_name:
                continue
            seen.add(n)
            todo += [by_name[n]["parent"], *by_name[n]["sessions"]]
        problems += [f"{s['name']} imports {i}" for i in s["imports"] if i not in seen]
    return problems


def main() -> int:
    sessions = collect()
    for s in sessions:
        print(
            f"{s['depth']:2}  {s['name']:30} {s['lines']:6} lines  rests on {', '.join(s['rests_on']) or '-'}"
        )
    problems = escaping_imports(sessions)
    for p in problems:
        print("escaping import:", p)
    return 1 if problems else 0


if __name__ == "__main__":
    sys.exit(main())
