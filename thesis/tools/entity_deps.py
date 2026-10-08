#!/usr/bin/env python3
"""Warn when the thesis shows an Isabelle entity before what its statement uses.

A definition or theorem displayed with `thy`, `proved` or a theorem
environment (`isa: "..."`) is only readable once the reader has met the
entities its statement is built from. `thesis/tools/entity_deps.ML` exports
those dependencies from the kernel: what each fact's proposition, each
constant's specification and each locale's assumptions mention. This tool
joins them with the citations in the thesis, in reading order.

The predecessors of an entity are the nearest entities the thesis cites: the
search follows dependencies through uncited entities (helpers, function
package internals) and stops at the first cited one on each path. A
predecessor counts as introduced at its first citation of any kind, except in
the overview files (`POINTER_FILES`) and at an embed marked as a preview by a
`// deps: preview` comment on one of the three lines above it: such forward
references only point ahead.

An embed is judged only by the predecessors whose name occurs in the text it
displays (`shared/generated/snippets/`): the rest hide in an expanded type
synonym or a definition body the reader never sees. `--all-deps` drops this
filter.

A predecessor introduced later in the same section is the common
define-then-explain order (the rules of `pstep`, then its helpers). It is
reported only with `--near`; a predecessor introduced in a later section, or
never, is a warning.

    thesis/tools/entity_deps.py --write      reduce build/entity-deps/raw.json
                                             into shared/generated/entity-deps.json
    thesis/tools/entity_deps.py              report embeds shown before a
                                             predecessor (warnings, exit 0)
    thesis/tools/entity_deps.py --mentions   also check inline citations
    thesis/tools/entity_deps.py --near       also report predecessors that
                                             follow later in the same section
    thesis/tools/entity_deps.py --strict     exit 1 on any warning
    thesis/tools/entity_deps.py --all-deps   judge embeds by every predecessor,
                                             not only those their text shows
    thesis/tools/entity_deps.py --max-via N  pass through at most N uncited
                                             entities (default 3)
    thesis/tools/entity_deps.py --html PATH  write the interactive graph

`--write` needs `pixi run thesis-deps-export` first (the built heap); the other
modes read the committed graph only. `--export-theory PATH` writes the theory
that export loads: it imports every theory of every project session, since
`Voblint.thy` leaves out regression and tooling theories the thesis cites.
"""

from __future__ import annotations

import argparse
import json
import re
import sys
from collections import deque
from dataclasses import dataclass
from functools import cache
from pathlib import Path
from urllib.parse import unquote

REPO = Path(__file__).resolve().parents[2]
THESIS = REPO / "thesis"
RAW = REPO / "build" / "entity-deps" / "raw.json"
GRAPH = THESIS / "shared" / "generated" / "entity-deps.json"
SNIPPETS = THESIS / "shared" / "generated" / "snippets"
LINKS = THESIS / "shared" / "generated" / "links.json"
TEMPLATE = Path(__file__).with_name("entity_deps.html")

sys.path.insert(0, str(REPO / "scripts"))
from check_thesis_refs import ISA_ARG, TYPST_REF  # noqa: E402

# Files whose citations point ahead instead of introducing: the overview
# chapters state results with a forward reference to their theorem.
POINTER_FILES = {"abstract", "acknowledgements", "ai-use", "01-introduction"}

PREVIEW = "deps: preview"
HEADING = re.compile(r"(?m)^(=+)\s")
SNIPPET = re.compile(r"\b(thy|proved)\(\s*\"([^\"]+)\"")
INCLUDE = re.compile(r"include\s+\"(content/[^\"]+\.typ)\"")
ANCHOR_KIND = {
    "fact": "thm",
    "thm": "thm",
    "const": "const",
    "type": "type",
    "locale": "locale",
}


# ---------------------------------------------------------------- export

ROOT_KEYWORDS = {
    "chapter", "session", "description", "options", "sessions", "directories",
    "theories", "document_theories", "document_files", "export_files",
    "export_classpath",
}  # fmt: skip


# Outside the Voblint_Examples heap's session closure; it only drives code
# export and declares nothing the thesis cites.
EXCLUDED_SESSIONS = {"Voblint_Codegen"}


def project_theories() -> list[str]:
    """`Session.Theory` for every theory listed in a project ROOT."""
    dirs = [REPO / d for d in (REPO / "ROOTS").read_text().split()]
    dirs.append(REPO / "vendor" / "td-verification")
    out = []
    for root in (d / "ROOT" for d in dirs):
        text = re.sub(r"\(\*.*?\*\)", " ", root.read_text(), flags=re.S)
        text = re.sub(r"\[[^\]]*\]", " ", text)  # theory options
        session, listing = None, False
        tokens = re.findall(r'"[^"]*"|\(global\)|[^\s=+]+', text)
        for i, tok in enumerate(tokens):
            word = tok.strip('"')
            if tok in ROOT_KEYWORDS:
                listing = tok == "theories"
                if tok == "session":
                    session = tokens[i + 1].strip('"')
            elif (
                listing
                and session not in (None, *EXCLUDED_SESSIONS)
                and tok != "(global)"
            ):
                out.append(word if "." in word else f"{session}.{word}")
    return out


def write_export_theory(path: Path) -> None:
    imports = "\n".join(f'    "{t}"' for t in project_theories())
    ml = Path(__file__).with_name("entity_deps.ML")
    out = REPO / "build" / "entity-deps" / "raw.json"
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(
        f"""theory {path.stem}
  imports
{imports}
begin

ML_file "{ml}"

ML \\<open>
  File.write (Path.explode "{out}") (Entity_Deps.json ["Voblint", "TD"] \\<^theory>)
\\<close>

end
"""
    )


# ---------------------------------------------------------------- reduction


def reduce_raw(raw: dict[str, dict]) -> dict[str, list[str]]:
    """Fold locale predicates into their locale and drop edges leaving the project.

    A locale with assumptions is also a constant of the same name, and every
    fact stated inside the locale mentions that constant; both mean the
    locale. Members of a locale (`L.f`, `L.thm`) depend on the locale.
    """
    locales = {k.split(":", 1)[1] for k in raw if k.startswith("locale:")}

    def canon(key: str) -> str:
        kind, name = key.split(":", 1)
        if kind == "const":
            if name in locales:
                return f"locale:{name}"
            if name.endswith("_axioms") and name[: -len("_axioms")] in locales:
                return f"locale:{name[: -len('_axioms')]}"
        return key

    def enclosing_locale(name: str) -> str | None:
        owners = [loc for loc in locales if name.startswith(loc + ".")]
        return max(owners, key=len) if owners else None

    graph: dict[str, set[str]] = {}
    for key, node in raw.items():
        ckey = canon(key)
        deps = graph.setdefault(ckey, set())
        deps.update(canon(d) for d in node["deps"] if d in raw)
        owner = enclosing_locale(key.split(":", 1)[1])
        if owner:
            deps.add(f"locale:{owner}")
        deps.discard(ckey)
    return {k: sorted(v) for k, v in sorted(graph.items())}


def write_graph() -> None:
    if not RAW.is_file():
        sys.exit(f"{RAW.relative_to(REPO)} missing: run `pixi run thesis-deps-export`")
    graph = reduce_raw(json.loads(RAW.read_text()))
    # Only what the linked citations can reach is committed; citing something
    # new means regenerating links.json, and this graph with it.
    cited = set(citation_keys(json.loads(LINKS.read_text())).values()) & set(graph)
    kept, stack = set(cited), list(cited)
    while stack:
        for dep in graph[stack.pop()]:
            if dep not in kept:
                kept.add(dep)
                stack.append(dep)
    lines = [f"{json.dumps(k)}: {json.dumps(graph[k])}" for k in sorted(kept)]
    GRAPH.write_text("{\n" + ",\n".join(lines) + "\n}\n")
    print(f"wrote {GRAPH.relative_to(REPO)}: {len(kept)} entities")


# ---------------------------------------------------------------- citations


def citation_keys(links: dict) -> dict[str, str]:
    """links.json key (`thm:step_sound`) -> graph key (`thm:Theory.loc.step_sound`)."""
    out = {}
    for key, url in links["links"].items():
        kind, _, anchor = key.partition(":")
        if kind in ("theory", "session") or "#" not in url:
            continue
        name, _, akind = unquote(url.split("#", 1)[1]).rpartition("|")
        if akind not in ANCHOR_KIND:
            continue
        # `compile.simps(4)` is one equation of the fact `compile.simps`.
        name = re.sub(r"\(\d+\)$", "", name)
        out[key] = f"{ANCHOR_KIND[akind]}:{name}"
    return out


@dataclass(frozen=True)
class Cite:
    key: str  # graph key
    label: str  # as written in the thesis
    file: str  # content file stem
    line: int
    order: int  # global reading position
    embed: bool  # thy / proved / theorem environment, versus an inline mention
    section: int  # index of the enclosing level-1 or level-2 heading in the file
    preview: bool = False  # an embed marked `// deps: preview`

    @property
    def pointer(self) -> bool:
        return self.preview or self.file in POINTER_FILES


def reading_order() -> list[Path]:
    text = (THESIS / "thesis.typ").read_text()
    return [THESIS / m.group(1) for m in INCLUDE.finditer(text)]


def strip_comments(text: str) -> str:
    """Blank `//` comment lines, keeping offsets and line numbers."""
    return re.sub(r"(?m)^[ \t]*//.*$", lambda m: " " * len(m.group(0)), text)


def collect_cites(links: dict) -> tuple[list[Cite], list[str]]:
    keys = citation_keys(links)
    names = links.get("names", {})
    cites: list[Cite] = []
    unresolved: list[str] = []

    def resolve(kinds: tuple[str, ...], name: str) -> str | None:
        for kind in kinds:
            if f"{kind}:{name}" in keys:
                return keys[f"{kind}:{name}"]
        return None

    for path in reading_order():
        raw = path.read_text()
        raw_lines = raw.splitlines()
        text = strip_comments(raw)
        sections = [m.start() for m in HEADING.finditer(text) if len(m.group(1)) <= 2]
        found = []
        for m in TYPST_REF.finditer(text):
            kind = m.group(1)
            kinds = ("const", "ctor") if kind == "const" else (kind,)
            found.append((m.start(), m.group(2), resolve(kinds, m.group(2)), False))
        for m in ISA_ARG.finditer(text):
            name = m.group(1)
            key = resolve(("thm", "const", "type", "locale", "ctor"), name)
            found.append((m.start(), name, key, True))
        for m in SNIPPET.finditer(text):
            name = m.group(2)
            link = names.get(name)
            found.append((m.start(), name, keys.get(link) if link else None, True))
        for offset, label, key, embed in sorted(found, key=lambda f: f[0]):
            line = text.count("\n", 0, offset) + 1
            if key is None:
                unresolved.append(f"{path.relative_to(REPO)}:{line}: {label}")
                continue
            section = sum(1 for h in sections if h <= offset)
            preview = embed and any(
                PREVIEW in above for above in raw_lines[max(0, line - 4) : line]
            )
            cites.append(
                Cite(key, label, path.stem, line, len(cites), embed, section, preview)
            )
    return cites, unresolved


# ---------------------------------------------------------------- analysis


# Constants and types a definitional package introduces behind a user-facing
# one; passing through them costs no hop.
INTERNAL = re.compile(r"_(sumC|graph|rel|dom|ext|axioms)$")


def nearest_cited(
    graph: dict[str, list[str]], start: str, cited: set[str], max_via: int
) -> dict[str, list[str]]:
    """Cited entities reachable from `start` through at most `max_via` uncited
    ones, with the uncited path to each. A 0-1 BFS, so each path is one with
    the fewest hops."""
    found: dict[str, list[str]] = {}
    best = {start: 0}
    queue = deque([(start, [], 0)])
    while queue:
        node, path, hops = queue.popleft()
        if hops > best.get(node, hops):
            continue
        for dep in graph.get(node, ()):
            if dep in cited:
                if dep != start and (dep not in found or len(path) < len(found[dep])):
                    found[dep] = path
                continue
            internal = bool(INTERNAL.search(dep))
            cost = hops + (0 if internal else 1)
            if cost > max_via or best.get(dep, cost + 1) <= cost:
                continue
            best[dep] = cost
            entry = (dep, path + [dep], cost)
            queue.appendleft(entry) if internal else queue.append(entry)
    return found


@dataclass
class Analysis:
    cites: list[Cite]
    first: dict[str, Cite]  # first citation of each entity anywhere
    introduced: dict[str, Cite]  # first citation outside the overview files
    preds: dict[str, dict[str, list[str]]]
    missing: set[str]  # cited but not in the graph
    all_deps: bool = False  # judge embeds by predecessors their text hides too


IDENT = re.compile(r"[A-Za-z_][A-Za-z0-9_']*")


@cache
def shown_names(label: str) -> set[str] | None:
    """Identifiers in the snippet an embed displays, or None without one."""
    path = SNIPPETS / f"{label}.thy"
    if not path.is_file():
        return None
    return set(IDENT.findall(path.read_text()))


def analyse(
    graph: dict[str, list[str]], cites: list[Cite], max_via: int, all_deps: bool = False
) -> Analysis:
    first: dict[str, Cite] = {}
    introduced: dict[str, Cite] = {}
    for c in cites:
        first.setdefault(c.key, c)
        if not c.pointer:
            introduced.setdefault(c.key, c)
    cited = set(first)
    preds = {k: nearest_cited(graph, k, cited, max_via) for k in cited}
    missing = {k for k in cited if k not in graph and not k.startswith("thm:")}
    missing |= {k for k in cited if k.startswith("thm:") and k not in graph}
    return Analysis(cites, first, introduced, preds, missing, all_deps)


def lateness(a: Analysis, subject: Cite, pred: str) -> str | None:
    """None when `pred` is introduced before `subject`; "near" when it follows
    in the same section; "late" when it follows in a later one, or never.
    An embed's predecessor that its displayed text does not name is None."""
    if subject.embed and not a.all_deps:
        shown = shown_names(subject.label)
        if shown is not None and pred.rsplit(".", 1)[-1] not in shown:
            return None
    intro = a.introduced.get(pred)
    if intro is not None and intro.order < subject.order:
        return None
    if intro is not None and (intro.file, intro.section) == (
        subject.file,
        subject.section,
    ):
        return "near"
    return "late"


def checked_cite(a: Analysis, key: str, mentions: bool) -> Cite | None:
    """The citation the check judges: the first embed outside the overview
    files, or with `mentions` the first citation there of any kind."""
    for c in a.cites:
        if c.key == key and not c.pointer and (c.embed or mentions):
            return c
    return None


def loc(c: Cite) -> str:
    return f"thesis/content/{c.file}.typ:{c.line}"


def short(key: str) -> str:
    return key.split(":", 1)[1].split(".", 1)[-1]


def report(a: Analysis, mentions: bool, near: bool) -> tuple[int, int]:
    """Print one entry per checked citation, listing its late predecessors."""
    counts = {"late": 0, "near": 0}
    subjects = (checked_cite(a, key, mentions) for key in a.first)
    for c in sorted(filter(None, subjects), key=lambda c: c.order):
        found = []
        for pred, via in sorted(a.preds[c.key].items(), key=lambda p: short(p[0])):
            level = lateness(a, c, pred)
            if level is None:
                continue
            counts[level] += 1
            if level == "late" or near:
                found.append((level, pred, via))
        if not found:
            continue
        how = "shows" if c.embed else "cites"
        severity = "warning" if any(f[0] == "late" for f in found) else "note"
        print(
            f"{loc(c)}: {severity}: {how} {c.label} before {len(found)} predecessor(s)"
        )
        for level, pred, via in found:
            intro = a.introduced.get(pred)
            where = f"{intro.file}.typ:{intro.line}" if intro else "never introduced"
            path = f"  via {' -> '.join(short(v) for v in via)}" if via else ""
            mark = "  " if level == "late" else "~ "
            print(f"    {mark}{short(pred):<40} {where}{path}")
    return counts["late"], counts["near"]


# ---------------------------------------------------------------- html


def html_data(a: Analysis, links: dict) -> dict:
    urls = {}
    base = links.get("base", "")
    for key, url in links["links"].items():
        gk = citation_keys({"links": {key: url}}).get(key)
        if gk:
            urls.setdefault(gk, base + url)
    files = [p.stem for p in reading_order()]
    nodes = []
    for key, c in a.first.items():
        intro = a.introduced.get(key, c)
        embeds = [x for x in a.cites if x.key == key and x.embed]
        judged = checked_cite(a, key, mentions=False)
        nodes.append(
            {
                "id": key,
                "label": c.label,
                "kind": key.split(":", 1)[0],
                "full": key.split(":", 1)[1],
                "file": intro.file,
                "line": intro.line,
                "order": intro.order,
                "chapter": files.index(intro.file),
                "embed": bool(embeds),
                "judged": f"{judged.file}:{judged.line}" if judged else None,
                "pointerOnly": key not in a.introduced,
                "inGraph": key not in a.missing,
                "url": urls.get(key),
                "cites": [
                    {"file": x.file, "line": x.line, "embed": x.embed}
                    for x in a.cites
                    if x.key == key
                ],
            }
        )
    # An edge is judged at the entity's first embed, as the report does; an
    # entity only cited inline is judged at its introduction, flagged
    # `mention` since forward inline citations are allowed.
    edges = []
    for key, preds in a.preds.items():
        embed = checked_cite(a, key, mentions=False)
        subject = embed or a.introduced.get(key, a.first[key])
        for pred, via in preds.items():
            edges.append(
                {
                    "source": key,
                    "target": pred,
                    "via": [short(v) for v in via],
                    "late": lateness(a, subject, pred),
                    "mention": embed is None,
                }
            )
    return {"files": files, "nodes": nodes, "edges": edges}


def write_html(a: Analysis, links: dict, out: Path) -> None:
    data = json.dumps(html_data(a, links), separators=(",", ":"))
    page = TEMPLATE.read_text().replace("/*DATA*/null", data)
    out.parent.mkdir(parents=True, exist_ok=True)
    out.write_text(page)
    print(f"wrote {out}")


# ---------------------------------------------------------------- main


def main() -> int:
    ap = argparse.ArgumentParser(description=__doc__.split("\n\n")[0])
    ap.add_argument("--write", action="store_true")
    ap.add_argument("--mentions", action="store_true")
    ap.add_argument("--near", action="store_true")
    ap.add_argument("--all-deps", action="store_true")
    ap.add_argument(
        "--max-via",
        type=int,
        default=3,
        help="uncited entities a dependency may pass through (default 3)",
    )
    ap.add_argument("--strict", action="store_true")
    ap.add_argument("--html", type=Path)
    ap.add_argument("--export-theory", type=Path)
    args = ap.parse_args()

    if args.export_theory:
        write_export_theory(args.export_theory)
        return 0

    if args.write:
        write_graph()
        return 0

    graph = json.loads(GRAPH.read_text())
    links = json.loads(LINKS.read_text())
    cites, _unresolved = collect_cites(links)
    a = analyse(graph, cites, args.max_via, args.all_deps)

    if args.html:
        write_html(a, links, args.html)
        return 0

    warnings, near = report(a, args.mentions, args.near)
    if a.missing:
        print(
            f"note: {len(a.missing)} cited entities have no dependency data "
            "(library entities, or a stale graph: `pixi run thesis-deps-write`): "
            + ", ".join(sorted(short(k) for k in a.missing))
        )
    print(
        f"{warnings} predecessor(s) introduced in a later section or never; "
        f"{near} later in the same section"
        + ("" if args.near else " (--near lists them)")
    )
    return 1 if args.strict and warnings else 0


if __name__ == "__main__":
    sys.exit(main())
