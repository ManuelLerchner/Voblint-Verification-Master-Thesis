#!/usr/bin/env python3
"""Link every entity the thesis names to its definition in the rendered theories.

Concrete Semantics puts a small `thy` marker next to a concept that jumps to
the Isabelle library page for it. We can do better than the theory page:
Isabelle's HTML output carries a per-entity anchor,

    <span class="entity_def" id="CFG_Def.pp|type">

so a citation can land on the definition itself. The catch is that a link that
silently 404s -- or worse, resolves to a page that no longer defines what the
sentence claims -- is more damaging than no link. So the URLs are not guessed
at render time: they are resolved here against the built HTML, verified anchor
by anchor, and written to thesis/shared/generated/links.json for the templates
to read. A name with no verified anchor is a build failure, not a dead link.

    scripts/check_thesis_links.py --write   resolve and store
    scripts/check_thesis_links.py --check   re-resolve and diff
    scripts/check_thesis_links.py --live    fetch the deployed pages and verify
    scripts/check_thesis_links.py --list    show what is linked

`--write` and `--check` read the anchors of the rendered theories under
build/isabelle-html through `isar project anchors` (isar-tools), which a
working copy usually does not have (or has stale). `--lenient` turns that from
a failure into a warning, which is what the local hook and the day-to-day
`make check` use. Even in lenient mode, every citation must have a stored
target. Only verification against unavailable local HTML may be skipped.

`--live` is the check that actually matters, and it can only run in one place:
after the rendered theories are deployed to GitHub Pages, since that is the
first moment the URLs in the PDF exist. It fetches each one and verifies both
the response and that the anchor is present in the served page.
"""

from __future__ import annotations

import argparse
import difflib
import json
import re
import subprocess
import sys
import time
import urllib.error
import urllib.request
from pathlib import Path
from urllib.parse import quote

import tomllib

REPO = Path(__file__).resolve().parent.parent
HTML = REPO / "build" / "isabelle-html"
OUT = REPO / "thesis" / "shared" / "generated" / "links.json"

# Isabelle's anchor kinds, per macro kind the thesis uses.
KIND_ANCHORS = {
    "thm": ("fact", "thm"),
    "const": ("const",),
    "type": ("type",),
    "locale": ("locale",),
    # A theorem environment's `isa:` name: whatever the theories say it is.
    # A class or locale also has an internal constant; the declaration comes first.
    "any": ("fact", "thm", "locale", "const", "type"),
    # A constructor in notation links to its datatype's constant anchor when
    # one exists; notation for things the theories do not define stays plain.
    "ctor": ("const",),
    "session": ("page",),
    "theory": ("page",),
}
# `thy:` qualifies a name that several theories define: isaconst("eq", thy: "Basics_side").
# `display:` changes only the printed text; the link target stays the cited name.
TYPST_REF = re.compile(
    r'\bisa(thm|const|type|locale|session|name)\(\s*"([^\"]*)"'
    r'((?:\s*,\s*(?:thy|display):\s*"[^"]*")*)\s*,?\s*\)'
)
THY_ARG = re.compile(r'\bthy:\s*"([^"]+)"')
GENERATED_REF = re.compile(r'\b(thy|proved|stated)\(\s*"([^\"]+)"')
THEORY_REF = re.compile(r'\bthy-badge\(\s*"([^\"]+)"\s*,\s*"([^\"]+)"\s*\)')
# `isa: "name"` on a theorem environment, and `oblig("NAME")` for a named
# assumption of `activation_coverage`, which the HTML anchors as a fact of the locale.
ISA_ARG = re.compile(r"\bisa:\s*\"([A-Za-z][A-Za-z0-9_.']*)\"")
OBLIG = re.compile(r"\boblig\(\"([A-Z]+)\"(?:,\s*of:\s*\"([A-Za-z_]+)\")?\)")
# `ctor("Root")` sets a constructor in notation; it links when the theories
# define the name, as a `ctor` citation that may stay unlinked.
CTOR = re.compile(
    r'\bctor\(\s*"([A-Za-z][A-Za-z0-9_\']*)"(?:\s*,\s*thy:\s*"([^"]+)")?\s*,?\s*\)'
)
# Subscripts in a name are HTML-escaped in the anchor (dep\&lt;^sub&gt;L).
ANCHOR = re.compile(
    r'id="([A-Za-z](?:[A-Za-z0-9_.\']|\\&lt;\^sub&gt;)*(?:\([0-9]+\))?)\|([a-z]+)"'
)


def pages_base() -> str:
    """GitHub Pages URL for this repository."""
    try:
        url = subprocess.run(
            ["git", "config", "--get", "remote.origin.url"],
            cwd=REPO,
            capture_output=True,
            text=True,
            check=True,
        ).stdout.strip()
    except (subprocess.CalledProcessError, OSError):
        return ""
    m = re.search(r"[:/]([^/:]+)/([^/]+?)(?:\.git)?$", url)
    if not m:
        return ""
    owner, repo = m.groups()
    return f"https://{owner.lower()}.github.io/{repo}/"


# Every definition of a short name in the project and the vendored solver, and
# the locales and classes that scope them, so a citation that could mean two
# different entities is caught instead of silently linked to one of them.
DEFINITIONS: dict[tuple[str, str], set[str]] = {}
SCOPES: set[str] = set()


def _index_rel(index: dict[tuple[str, str], str], rel: str) -> None:
    path = Path(rel)
    if path.name == "index.html":
        index.setdefault((path.parent.name, "page"), rel)
    else:
        index.setdefault((f"{path.parent.name}.{path.stem}", "page"), rel)


def _index_page(index: dict[tuple[str, str], str], rel: str, body: str) -> None:
    """A fetched page's anchors, for the published site, where no build directory exists."""
    _index_rel(index, rel)
    for m in ANCHOR.finditer(body):
        escaped, kind = m.group(1), m.group(2)
        _index_anchor(
            index, rel, escaped.replace("&lt;", "<").replace("&gt;", ">"), kind
        )


def _index_anchor(
    index: dict[tuple[str, str], str], rel: str, qualified: str, kind: str
) -> None:
    if rel.startswith(("Voblint/", "Unsorted/TD/")):
        # A datatype scopes its constructors as a locale scopes its members,
        # so two datatypes with an `Answer` make `Answer` ambiguous.
        if kind in ("locale", "class", "type"):
            SCOPES.add(qualified)
        if kind in ("const", "type", "locale"):
            DEFINITIONS.setdefault((qualified.split(".")[-1], kind), set()).add(
                qualified
            )
    anchor = quote(f"{qualified}|{kind}", safe="._()'")
    parts = qualified.split(".")
    # Every suffix, including the theory-qualified name a `thy:` citation uses.
    # `Theory.name` also reaches a member of a locale or datatype, which is
    # how `thy:` qualifies a constructor: ctor("Answer", thy: "Basics_side").
    keys = [".".join(parts[i:]) for i in range(len(parts))]
    if len(parts) == 3:
        keys.append(f"{parts[0]}.{parts[2]}")
    for dotted in keys:
        key = (dotted, kind)
        target = f"{rel}#{anchor}"

        # Keep current project exports ahead of stale/library duplicates.
        # Per-domain and example sessions interpret the generic locales, so
        # a copy there is an instance, not the definition.
        # Among library pages, the HOL session defines what HOL-IMP and
        # HOL-Library only redefine or interpret (lfp, mono).
        # A named interpretation (`..._Interp`) copies a locale's facts;
        # the generic locale entity is the definition a citation means.
        # The vendored solver's sessions render under Unsorted/, but their
        # owner pages define what the project cites (widen, narrow).
        # A name several project theories define is cited with `thy:`
        # (see definitions_of), so the ranking never has to guess between them.
        def rank(
            value: str,
        ) -> tuple[bool, bool, bool, bool, bool, str]:
            page, _, entity = value.partition("#")
            project = page.startswith(("Voblint/", "Unsorted/TD/"))
            return (
                not page.startswith("Voblint/"),
                not project,
                not (project or page.startswith("HOL/HOL/")),
                "_Interp." in entity,
                "/Voblint_Analysis_" in page or "/Voblint_Examples" in page,
                value,
            )

        if key not in index or rank(target) < rank(index[key]):
            index[key] = target


def index_live(
    base: str, retries: int, sessions: str = "Voblint"
) -> dict[tuple[str, str], str]:
    """Index anchors from the published site, which is what a reader clicks.

    A working copy's build/isabelle-html and the deployed site drift apart in both
    directions, so resolving against the deployment is the only way to produce
    a map whose links are known to work today.
    """
    base = base.rstrip("/") + "/"
    root = fetch(base + "Voblint/index.html", retries)
    if root is None:
        sys.exit(f"check_thesis_links: cannot reach {base}Voblint/index.html")
    names = [
        m.group(1)
        for m in re.finditer(r'href="([^"/]+)/index\.html"', root)
        if sessions in m.group(1)
    ]
    index: dict[tuple[str, str], str] = {}
    pages = 0
    for session in sorted(names):
        listing = fetch(f"{base}Voblint/{session}/index.html", retries)
        if listing is None:
            continue
        _index_page(index, f"Voblint/{session}/index.html", listing)
        for m in re.finditer(r'href="([^"/]+\.html)"', listing):
            page = m.group(1)
            # A session that elaborates another session's theory presents a
            # copy named `<Owner>.<Theory>.html`; cite the owner's page instead.
            if page == "index.html" or "." in page.removesuffix(".html"):
                continue
            rel = f"Voblint/{session}/{page}"
            body = fetch(base + rel, retries)
            if body is None:
                continue
            _index_page(index, rel, body)
            pages += 1
    print(
        f"check_thesis_links: indexed {len(index)} anchor(s) from {pages} "
        f"published page(s)",
        file=sys.stderr,
    )
    return index


def index_anchors() -> dict[tuple[str, str], str]:
    """Map (entity name, anchor kind) -> path#anchor, relative to build/isabelle-html.

    `isar project anchors` reads the build's anchors, HOL and library sessions
    included, and leaves out the copy a session presents of another session's
    theory (`<Owner>.<Theory>.html`), so a citation reaches the owner's page.
    """
    listing = json.loads(
        subprocess.run(
            [
                sys.executable,
                "-m",
                "isar_tools",
                "project",
                "anchors",
                "--browser-info",
                str(HTML),
                "--format",
                "json",
            ],
            capture_output=True,
            text=True,
            check=True,
        ).stdout
    )
    index: dict[tuple[str, str], str] = {}
    # Session and theory pages are cited as pages; an index page carries no anchor.
    # The first page indexed under a name wins: this project's current export
    # before old ungrouped exports that may coexist with it.
    for path in sorted(
        HTML.rglob("*.html"),
        key=lambda p: (
            p.relative_to(HTML).parts[0] != "Voblint",
            p.relative_to(HTML).parts[0] == "Unsorted",
            p.as_posix(),
        ),
    ):
        if "." not in path.stem:
            _index_rel(index, path.relative_to(HTML).as_posix())
    for row in listing["anchors"]:
        rel = row["url"].partition("#")[0]
        _index_anchor(index, rel, row["anchor"].rpartition("|")[0], row["kind"])
    return index


def cited() -> list[tuple[Path, int, str, str]]:
    refs = []
    for path in sorted((REPO / "thesis").rglob("*")):
        if path.suffix != ".typ" or not path.is_file():
            continue
        text = path.read_text(errors="ignore")
        for m in TYPST_REF.finditer(text):
            line = text.count("\n", 0, m.start()) + 1
            kind = "any" if m.group(1) == "name" else m.group(1)
            thy = THY_ARG.search(m.group(3))
            name = m.group(2) if thy is None else f"{thy.group(1)}.{m.group(2)}"
            refs.append((path, line, kind, name))
        for m in GENERATED_REF.finditer(text):
            line = text.count("\n", 0, m.start()) + 1
            kind = "any" if m.group(1) == "thy" else "thm"
            refs.append((path, line, kind, m.group(2)))
        for m in THEORY_REF.finditer(text):
            line = text.count("\n", 0, m.start()) + 1
            refs.append((path, line, "theory", f"{m.group(1)}.{m.group(2)}"))
        for m in ISA_ARG.finditer(text):
            line = text.count("\n", 0, m.start()) + 1
            refs.append((path, line, "any", m.group(1)))
        for m in OBLIG.finditer(text):
            line = text.count("\n", 0, m.start()) + 1
            locale = m.group(2) or "activation_coverage"
            refs.append((path, line, "thm", f"{locale}.{m.group(1)}"))
        for m in CTOR.finditer(text):
            line = text.count("\n", 0, m.start()) + 1
            name = m.group(1) if m.group(2) is None else f"{m.group(2)}.{m.group(1)}"
            refs.append((path, line, "ctor", name))
    # Tables rendered from generated JSON cite through its `citations` list.
    for path in sorted((REPO / "thesis" / "shared" / "generated").glob("*.json")):
        if path == OUT:
            continue
        data = json.loads(path.read_text())
        if isinstance(data, dict):
            refs += [(path, 1, c["kind"], c["name"]) for c in data.get("citations", [])]
    return refs + manifest_citations(REPO / "thesis" / "shared")


def manifest_citations(shared: Path) -> list[tuple[Path, int, str, str]]:
    """Names Typst cites by iterating a manifest, which no source text spells out.

    The anchor index appendix renders every `anchors.toml` item, the oracle
    audit table every `facts.toml` key, and each domain tree every class or
    locale placed in its table of `domain-tree.toml`.
    """
    refs = []
    anchors = shared / "anchors.toml"
    if anchors.is_file():
        refs += [
            (
                anchors,
                1,
                a["kind"],
                f"{a['thy']}.{a['name']}" if "thy" in a else a["name"],
            )
            for a in tomllib.loads(anchors.read_text()).get("anchor", [])
        ]
    facts = shared / "facts.toml"
    if facts.is_file():
        refs += [
            (facts, 1, "thm", name)
            for name in tomllib.loads(facts.read_text()).get("facts", {})
        ]
    tree = shared / "domain-tree.toml"
    if tree.is_file():
        refs += [
            (tree, 1, "locale", name)
            for figure in tomllib.loads(tree.read_text()).values()
            for row in figure["rows"]
            for name in row
        ]
    return refs


def resolve(
    index: dict[tuple[str, str], str] | None = None,
) -> tuple[dict[str, str], list[str]]:
    if index is None:
        index = index_anchors()
    links: dict[str, str] = {}
    unresolved: list[str] = []
    for path, line, kind, name in cited():
        key = f"{kind}:{name}"
        if key in links:
            continue
        rivals = definitions_of(name, kind)
        home = snippet_theory(name) if kind == "any" else None
        if len(rivals) > 1 and home is not None:
            # A shown declaration names its source file; link the definition there.
            scoped = [
                index[(f"{home}.{name}", anchor_kind)]
                for anchor_kind in KIND_ANCHORS[kind]
                if (f"{home}.{name}", anchor_kind) in index
            ]
            if scoped:
                links[key] = scoped[0]
                continue
        if len(rivals) > 1:
            unresolved.append(
                f"  {path.relative_to(REPO)}:{line}: {name} names {len(rivals)} "
                f'definitions ({", ".join(rivals)}); cite it with thy: "<Theory>"'
            )
            continue
        hits = [
            index[(name, anchor_kind)]
            for anchor_kind in KIND_ANCHORS[kind]
            if (name, anchor_kind) in index
        ]
        if hits:
            # An untyped theorem-header citation may name a project datatype
            # while HOL has an unrelated constant with the same short name.
            links[key] = min(
                hits,
                key=lambda hit: (
                    not hit.startswith("Voblint/"),
                    not hit.startswith("Unsorted/TD/"),
                ),
            )
        elif kind != "ctor":
            unresolved.append(
                f"  {path.relative_to(REPO)}:{line}: {name} has no "
                f"{'/'.join(KIND_ANCHORS[kind])} anchor in the rendered theories"
            )
    return links, unresolved


def snippet_theory(name: str) -> str | None:
    """The theory a generated snippet was lifted from, read off its provenance line."""
    path = REPO / "thesis" / "shared" / "generated" / "snippets" / f"{name}.thy"
    if not path.is_file():
        return None
    m = re.match(r"\(\*\s*(\S+)\.thy\s*\*\)", path.read_text(errors="ignore"))
    return Path(m.group(1)).name if m else None


def definitions_of(name: str, kind: str) -> list[str]:
    """The distinct project definitions an unqualified citation could mean.

    An interpretation copies a locale's constants under the interpretation's
    name; only a name scoped by its theory or by a locale or class counts.
    """
    if "." in name or kind not in KIND_ANCHORS:
        return []
    found = {
        q
        for anchor_kind in KIND_ANCHORS[kind]
        if anchor_kind in ("const", "type", "locale")
        for q in DEFINITIONS.get((name, anchor_kind), ())
        if q.count(".") == 1 or q.rsplit(".", 1)[0] in SCOPES
    }
    return sorted(found)


def skip_or_fail(detail: str, lenient: bool) -> int:
    """Fail, or -- locally -- say why the check could not run and move on."""
    if lenient:
        print(f"check_thesis_links: skipped -- {detail.splitlines()[0]}")
        print("  (link validity is checked against the deployed pages on main)")
        return 0
    print(f"check_thesis_links: {detail}", file=sys.stderr)
    return 1


def check_coverage() -> int:
    """Require a usable target even when local HTML has not been built."""
    data = json.loads(OUT.read_text()) if OUT.is_file() else {}
    if not re.match(r"^https?://[^/]+/", data.get("base", "")):
        print("check_thesis_links: missing HTTP(S) base URL", file=sys.stderr)
        return 1
    links = data.get("links", {})
    missing = []
    for path, line, kind, name in cited():
        if kind == "ctor":
            continue
        target = links.get(f"{kind}:{name}", "")
        page, _, anchor = target.partition("#")
        if not page.endswith(".html") or (
            kind not in ("session", "theory") and not anchor
        ):
            missing.append(f"  {path.relative_to(REPO)}:{line}: {kind}:{name}")
    if missing:
        print(
            "check_thesis_links: citations missing HTML targets:\n" + "\n".join(missing)
        )
        print("Regenerate with pixi run thesis-links-write (or --write --from-live).")
        return 1
    print("check_thesis_links: every citation has an HTML target")
    return 0


def fetch(url: str, retries: int) -> str | None:
    """GET `url`, retrying while a fresh Pages deployment propagates."""
    for attempt in range(retries):
        try:
            with urllib.request.urlopen(url, timeout=20) as response:
                if response.status == 200:
                    return response.read().decode("utf-8", "replace")
        except (urllib.error.URLError, urllib.error.HTTPError, OSError):
            pass
        if attempt < retries - 1:
            time.sleep(2**attempt)
    return None


def check_live(base_override: str | None, retries: int) -> int:
    """Verify every stored link against the site a reader will actually click."""
    if check_coverage():
        return 1
    if not OUT.is_file():
        print(
            f"check_thesis_links: no {OUT.relative_to(REPO)} to verify -- "
            "run --write against the rendered theories first",
            file=sys.stderr,
        )
        return 1
    data = json.loads(OUT.read_text())
    base = base_override or data.get("base") or pages_base()
    if not base:
        print("check_thesis_links: no base URL to verify against", file=sys.stderr)
        return 1

    # One fetch per page, not per link: a page carries many anchors.
    by_page: dict[str, list[tuple[str, str]]] = {}
    for key, target in sorted(data.get("links", {}).items()):
        page, _, anchor = target.partition("#")
        by_page.setdefault(page, []).append((key, anchor))

    broken: list[str] = []
    for page, entries in sorted(by_page.items()):
        url = base.rstrip("/") + "/" + page
        body = fetch(url, retries)
        if body is None:
            broken += [f"  {key}: {url} did not respond" for key, _ in entries]
            continue
        for key, anchor in entries:
            if not anchor:
                continue
            # The stored anchor is percent-encoded for the URL; the page holds
            # the raw id.
            raw = anchor.replace("%7C", "|")
            if f'id="{raw}"' not in body:
                broken.append(f"  {key}: {url} has no anchor {raw}")

    if broken:
        print(
            f"check_thesis_links: {len(broken)} deployed link(s) do not reach "
            "a definition:"
        )
        print("\n".join(broken))
        return 1

    total = sum(len(v) for v in by_page.values())
    print(
        f"check_thesis_links: {total} deployed link(s) reach their definition "
        f"across {len(by_page)} page(s)"
    )
    return 0


def main() -> int:
    ap = argparse.ArgumentParser()
    mode = ap.add_mutually_exclusive_group(required=True)
    mode.add_argument("--write", action="store_true")
    mode.add_argument("--check", action="store_true")
    mode.add_argument("--live", action="store_true")
    mode.add_argument("--list", action="store_true")
    mode.add_argument("--coverage", action="store_true")
    ap.add_argument("--base", help="override the link base URL")
    ap.add_argument(
        "--lenient",
        action="store_true",
        help="warn instead of failing when the theories are not rendered locally",
    )
    ap.add_argument(
        "--retries",
        type=int,
        default=6,
        help="--live: attempts per URL while Pages propagates",
    )
    ap.add_argument(
        "--from-live",
        action="store_true",
        help="resolve against the published site instead of build/isabelle-html",
    )
    args = ap.parse_args()

    if args.coverage:
        return check_coverage()
    if args.live:
        return check_live(args.base, args.retries)
    if args.check and check_coverage():
        return 1

    base = args.base or pages_base()
    if args.from_live:
        index = index_live(base, args.retries)
    else:
        index = None
        if not HTML.is_dir() or not any(HTML.rglob("*.html")):
            return skip_or_fail(
                "no rendered theories under build/isabelle-html -- build them with "
                "`pixi run isabelle-html-build`",
                args.lenient,
            )

    links, unresolved = resolve(index)
    if unresolved:
        detail = (
            f"{len(unresolved)} cited entity/entities have no definition "
            "anchor:\n"
            + "\n".join(unresolved)
            + "\nEither the name is stale, or build/isabelle-html predates it "
            "(rebuild with: pixi run isabelle-html-build)"
        )
        return skip_or_fail(detail, False)

    payload = (
        json.dumps({"base": base, "links": links}, indent=2, sort_keys=True) + "\n"
    )

    if args.list:
        for key, url in sorted(links.items()):
            print(f"{key}\n    {url}")
        return 0
    if args.write:
        OUT.parent.mkdir(parents=True, exist_ok=True)
        OUT.write_text(payload)
        print(
            f"check_thesis_links: wrote {OUT.relative_to(REPO)} ({len(links)} link(s))"
        )
        return 0

    stored = OUT.read_text() if OUT.is_file() else ""
    if stored != payload:
        print(
            "check_thesis_links: the stored links no longer match the "
            "rendered theories:\n"
        )
        print(
            "".join(
                difflib.unified_diff(
                    stored.splitlines(True),
                    payload.splitlines(True),
                    fromfile="links.json (in the thesis)",
                    tofile="links.json (resolved now)",
                )
            )
        )
        return 1

    print(f"check_thesis_links: {len(links)} link(s) resolve to a definition")
    return 0


if __name__ == "__main__":
    sys.exit(main())
