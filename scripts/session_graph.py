#!/usr/bin/env python3
"""The Isabelle session graph as the ROOT files and theory imports declare it.

A session rests on another when its ROOT names it as the parent, lists it under
`sessions`, or one of its theories imports a theory of it by qualified name. The
Pages explainer draws the development as strata, one layer above the highest
session each session rests on; computing that from the sources keeps the drawing
from drifting when a session moves or an import is added.

Theories count toward the deepest ROOT directory that contains them, which is how
Isabelle assigns them too. Line counts reuse thy_stats.py's scanner, so they agree
with `pixi run theory-stats`.

Run directly to print the layers and any import that leaves what its ROOT makes
available.
"""

import re
import sys
from pathlib import Path

from extract_definitions import REPO_ROOT, VENDOR_SESSIONS
from thy_stats import scan_theory

ROOTS_FILE = REPO_ROOT / "ROOTS"
# A qualified import names another session's theory: "Voblint_CFG.LTR_Def".
QUALIFIED_IMPORT = re.compile(r'"?([A-Za-z][\w\-]*)\.([A-Za-z]\w*)"?')
SESSION_HEADER = re.compile(
    r'session\s+"?([\w\-]+)"?\s*(?:\(.*?\)\s*)?(?:in\s+"?[^"\s]+"?\s*)?=\s*"?([\w\-]+)"?\s*\+(.*?)(?=\nsession\s|\Z)',
    re.S,
)
ROOT_SECTION = re.compile(
    r"\bsessions\b(.*?)(?=\b(?:theories|directories|document_files|description|options|export_files)\b|\Z)",
    re.S,
)


def strip_comments(text: str) -> str:
    return re.sub(r"\(\*.*?\*\)", "", text, flags=re.S)


def root_directories() -> list[Path]:
    listed = [REPO_ROOT / line for line in ROOTS_FILE.read_text().split()]
    return listed + list(VENDOR_SESSIONS)


def parse_root(directory: Path) -> list[dict]:
    text = strip_comments((directory / "ROOT").read_text())
    sessions = []
    for m in SESSION_HEADER.finditer(text):
        name, parent, body = m.groups()
        listed = ROOT_SECTION.search(body)
        sessions.append(
            {
                "name": name,
                "parent": parent,
                "sessions": re.findall(r'"?([A-Za-z][\w\-]*)"?', listed.group(1))
                if listed
                else [],
                "dir": directory,
            }
        )
    return sessions


def collect() -> list[dict]:
    """Every session with its declared relations, imports, depth and size."""
    by_name = {s["name"]: s for d in root_directories() for s in parse_root(d)}
    deepest_first = sorted(by_name.values(), key=lambda s: -len(s["dir"].parts))

    def owner(path: Path) -> str | None:
        return next(
            (s["name"] for s in deepest_first if path.is_relative_to(s["dir"])), None
        )

    for s in by_name.values():
        s.update(imports=set(), theories=0, lines=0, code=0, doc=0, proofs=0)

    for s in deepest_first:
        for thy in sorted(s["dir"].rglob("*.thy")):
            if owner(thy) != s["name"]:
                continue
            stats = scan_theory(thy)
            s["theories"] += 1
            s["lines"] += stats.lines
            s["code"] += stats.code_lines
            s["doc"] += stats.doc_lines
            s["proofs"] += stats.n_proofs
            header = re.search(
                r"\bimports\b(.*?)\bbegin\b",
                strip_comments(thy.read_text(errors="ignore")),
                re.S,
            )
            if header:
                for session, _ in QUALIFIED_IMPORT.findall(header.group(1)):
                    if session in by_name and session != s["name"]:
                        s["imports"].add(session)

    def rests_on(s: dict) -> set[str]:
        return {n for n in {s["parent"], *s["sessions"], *s["imports"]} if n in by_name}

    depth: dict[str, int] = {}

    def depth_of(name: str) -> int:
        if name not in depth:
            depth[name] = 1 + max(
                (depth_of(n) for n in rests_on(by_name[name])), default=0
            )
        return depth[name]

    return [
        {
            "name": s["name"],
            "dir": str(s["dir"].relative_to(REPO_ROOT)),
            "parent": s["parent"],
            "sessions": s["sessions"],
            "imports": sorted(s["imports"]),
            "rests_on": sorted(rests_on(s)),
            "depth": depth_of(s["name"]),
            "theories": s["theories"],
            "lines": s["lines"],
            "code": s["code"],
            "doc": s["doc"],
            "proofs": s["proofs"],
        }
        for s in sorted(
            by_name.values(), key=lambda s: (depth_of(s["name"]), s["name"])
        )
    ]


def imported_theories(session: str) -> list[Path]:
    """The theories of `session` that other sessions reach: their qualified imports,
    closed under the imports among the session's own theories."""
    directory = next(
        d
        for d in root_directories()
        if any(s["name"] == session for s in parse_root(d))
    )
    own = {p.stem: p for p in directory.rglob("*.thy")}

    def header(path: Path) -> str:
        m = re.search(
            r"\bimports\b(.*?)\bbegin\b",
            strip_comments(path.read_text(errors="ignore")),
            re.S,
        )
        return m.group(1) if m else ""

    todo = [
        name
        for d in root_directories()
        if d != directory
        for thy in d.rglob("*.thy")
        for qualifier, name in QUALIFIED_IMPORT.findall(header(thy))
        if qualifier == session and name in own
    ]
    seen = set()
    while todo:
        name = todo.pop()
        if name in seen:
            continue
        seen.add(name)
        for token in re.findall(r'"?([\w.\-]+)"?', header(own[name])):
            local = token.split(".")[-1]
            if local in own and (token == local or token.startswith(session + ".")):
                todo.append(local)
    return [own[n] for n in sorted(seen)]


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
