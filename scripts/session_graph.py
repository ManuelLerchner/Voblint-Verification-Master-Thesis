#!/usr/bin/env python3
"""The Isabelle session graph as the ROOT files and theory imports declare it.

A session rests on another when its ROOT names it as the parent, lists it under
`sessions`, or one of its theories imports a theory of it. The Pages explainer
draws the development as strata, one layer above the highest session each
session rests on; computing that from the sources keeps the drawing from
drifting when a session moves or an import is added.

The strata and relations come from `isar project graph --layers`, which reads
ROOTS and ROOT files as `isabelle build -D` does, with the vendored TD session
the project rests on (isar.toml includes vendor/td-verification); sizes come
from `isar stats sessions`, so they agree with `pixi run theory-stats`.

Run directly to print the layers and any import that leaves what its ROOT makes
available.
"""

import sys

from isar_json import (
    THEOREM_COMMANDS,
    command_counts,
    graph,
    project_directories,
    session_sizes,
    sessions,
)


def collect() -> list[dict]:
    """Every session with its declared relations, imports, layer and size."""
    layered = graph(layers=True)
    info: dict[str, dict] = {}
    sizes: dict[str, dict] = {}
    commands: dict[str, dict[str, int]] = {}
    listed: dict[str, list[str]] = {}
    for directory in project_directories():
        info.update({s["session"]: s for s in sessions(directory)})
        sizes.update(session_sizes(directory))
        commands.update(command_counts(directory))
        # `sessions` entries as the ROOT lists them, also of sessions outside
        # the graph (HOL-Library); the layered graph keeps its own nodes only.
        for edge in graph(directory)["edges"]:
            if edge["kind"] == "sessions":
                listed.setdefault(edge["from"], []).append(edge["to"])
    related: dict[str, dict[str, list[str]]] = {
        n: {"imports": [], "rests_on": []} for n in layered["nodes"]
    }
    for edge in layered["edges"]:
        if edge["from"] not in related:
            continue
        if edge["kind"] == "imports":
            related[edge["from"]]["imports"].append(edge["to"])
        if edge["to"] in related:
            related[edge["from"]]["rests_on"].append(edge["to"])

    def size(name: str, key: str) -> int:
        return sizes.get(name, {}).get(key, 0)

    return [
        {
            "name": name,
            "dir": info[name]["directory"],
            "parent": info[name]["parent"],
            "sessions": listed.get(name, []),
            "imports": sorted(set(related[name]["imports"]) - {name}),
            "rests_on": sorted(set(related[name]["rests_on"]) - {name}),
            "depth": layered["layers"][name],
            "theories": size(name, "theories"),
            "lines": size(name, "lines"),
            "code": size(name, "code_lines"),
            "doc": size(name, "doc_lines"),
            "proofs": sum(commands.get(name, {}).get(c, 0) for c in THEOREM_COMMANDS),
        }
        for name in sorted(layered["nodes"], key=lambda n: (layered["layers"][n], n))
    ]


def imported_theories(session: str) -> list[str]:
    """The theories of `session` that other sessions reach: their imports,
    closed under the imports among the session's own theories. Qualified names."""
    own_directory = next(
        d
        for d in project_directories()
        if any(s["session"] == session for s in sessions(d))
    )
    todo = [
        edge["to"]
        for directory in project_directories()
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
