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

`--write` and `--check` read the rendered theories under build/isabelle-html, which a
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
    "any": ("fact", "thm", "const", "type", "locale"),
    "session": ("page",),
    "theory": ("page",),
}
TYPST_REF = re.compile(r'\bisa(thm|const|type|locale|session|name)\(\s*"([^\"]*)"\s*\)')
GENERATED_REF = re.compile(r'\b(thy|proved|stated)\(\s*"([^\"]+)"')
THEORY_REF = re.compile(r'\bthy-badge\(\s*"([^\"]+)"\s*,\s*"([^\"]+)"\s*\)')
# `isa: "name"` on a theorem environment, and `oblig("NAME")` for a named
# assumption of `ltr_coverage`, which the HTML anchors as a fact of the locale.
ISA_ARG = re.compile(r"\bisa:\s*\"([A-Za-z][A-Za-z0-9_.']*)\"")
OBLIG = re.compile(r"\boblig\(\"([A-Z]+)\"(?:,\s*of:\s*\"([A-Za-z_]+)\")?\)")
ANCHOR = re.compile(r'id="([A-Za-z][A-Za-z0-9_.\']*)\|([a-z]+)"')


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


def _index_page(index: dict[tuple[str, str], str], rel: str, body: str) -> None:
    path = Path(rel)
    if path.name == "index.html":
        index.setdefault((path.parent.name, "page"), rel)
    else:
        index.setdefault((f"{path.parent.name}.{path.stem}", "page"), rel)
    for m in ANCHOR.finditer(body):
        qualified, kind = m.group(1), m.group(2)
        anchor = f"{qualified}|{kind}".replace("|", "%7C")
        parts = qualified.split(".")
        for i in range(1, len(parts)):
            key = (".".join(parts[i:]), kind)
            target = f"{rel}#{anchor}"

            # Prefer the original locale fact to a deeper interpreted copy.
            # Keep current project exports ahead of stale/library duplicates.
            # Per-domain and example sessions interpret the generic locales, so
            # an equally deep copy there is an instance, not the definition.
            def rank(value: str) -> tuple[bool, bool, int, bool, str]:
                page, _, entity = value.partition("#")
                return (
                    not page.startswith("Voblint/"),
                    page.startswith("Unsorted/"),
                    entity.count("."),
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
            if page == "index.html":
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
    """Map (entity name, anchor kind) -> path#anchor, relative to build/isabelle-html."""
    index: dict[tuple[str, str], str] = {}
    # Prefer this project's definitions over identically named HOL examples.
    # Old ungrouped exports may also coexist with the current Voblint group.
    for path in sorted(
        HTML.rglob("*.html"),
        key=lambda p: (
            p.relative_to(HTML).parts[0] != "Voblint",
            p.relative_to(HTML).parts[0] == "Unsorted",
            p.as_posix(),
        ),
    ):
        rel = path.relative_to(HTML).as_posix()
        _index_page(index, rel, path.read_text(errors="ignore"))
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
            refs.append((path, line, kind, m.group(2)))
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
            refs.append(
                (path, line, "thm", f"{m.group(2) or 'ltr_coverage'}.{m.group(1)}")
            )
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

    The anchor index appendix renders every `anchors.toml` item, and the oracle
    audit table every `facts.toml` key.
    """
    refs = []
    anchors = shared / "anchors.toml"
    if anchors.is_file():
        refs += [
            (anchors, 1, a["kind"], a["name"])
            for a in tomllib.loads(anchors.read_text()).get("anchor", [])
        ]
    facts = shared / "facts.toml"
    if facts.is_file():
        refs += [
            (facts, 1, "thm", name)
            for name in tomllib.loads(facts.read_text()).get("facts", {})
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
        hits = [
            index[(name, anchor_kind)]
            for anchor_kind in KIND_ANCHORS[kind]
            if (name, anchor_kind) in index
        ]
        if hits:
            # An untyped theorem-header citation may name a project datatype
            # while HOL has an unrelated constant with the same short name.
            links[key] = min(hits, key=lambda hit: not hit.startswith("Voblint/"))
        else:
            unresolved.append(
                f"  {path.relative_to(REPO)}:{line}: {name} has no "
                f"{'/'.join(KIND_ANCHORS[kind])} anchor in the rendered theories"
            )
    return links, unresolved


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
