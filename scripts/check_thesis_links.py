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

`--write` and `--check` read the rendered theories under docs/html, which a
working copy usually does not have (or has stale). `--lenient` turns that from
a failure into a warning, which is what the local hook and the day-to-day
`make check` want: a link cannot be validated before the theories are built,
and blocking a commit on that helps nobody.

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

REPO = Path(__file__).resolve().parent.parent
HTML = REPO / "docs" / "html"
OUT = REPO / "thesis" / "shared" / "generated" / "links.json"

# Isabelle's anchor kinds, per macro kind the thesis uses.
KIND_ANCHORS = {
    "thm": ("fact", "thm"),
    "const": ("const",),
    "type": ("type",),
    "locale": ("locale",),
}
TYPST_REF = re.compile(r"\bisa(thm|const|type|locale)\(\"([^\"]*)\"\)")
ANCHOR = re.compile(r'id="([A-Za-z][A-Za-z0-9_.\']*)\|([a-z]+)"')


def pages_base() -> str:
    """GitHub Pages URL for this repository."""
    try:
        url = subprocess.run(["git", "config", "--get", "remote.origin.url"],
                             cwd=REPO, capture_output=True, text=True,
                             check=True).stdout.strip()
    except (subprocess.CalledProcessError, OSError):
        return ""
    m = re.search(r"[:/]([^/:]+)/([^/]+?)(?:\.git)?$", url)
    if not m:
        return ""
    owner, repo = m.groups()
    return f"https://{owner.lower()}.github.io/{repo}/"


def _index_page(index: dict[tuple[str, str], str], rel: str, body: str) -> None:
    for m in ANCHOR.finditer(body):
        qualified, kind = m.group(1), m.group(2)
        anchor = f"{qualified}|{kind}".replace("|", "%7C")
        parts = qualified.split(".")
        for i in range(1, len(parts)):
            index.setdefault((".".join(parts[i:]), kind), f"{rel}#{anchor}")


def index_live(base: str, retries: int,
               sessions: str = "Voblint") -> dict[tuple[str, str], str]:
    """Index anchors from the published site, which is what a reader clicks.

    A working copy's docs/html and the deployed site drift apart in both
    directions, so resolving against the deployment is the only way to produce
    a map whose links are known to work today.
    """
    base = base.rstrip("/") + "/"
    root = fetch(base + "Unsorted/index.html", retries)
    if root is None:
        sys.exit(f"check_thesis_links: cannot reach {base}Unsorted/index.html")
    names = [m.group(1) for m in re.finditer(r'href="([^"/]+)/index\.html"', root)
             if sessions in m.group(1)]
    index: dict[tuple[str, str], str] = {}
    pages = 0
    for session in sorted(names):
        listing = fetch(f"{base}Unsorted/{session}/index.html", retries)
        if listing is None:
            continue
        for m in re.finditer(r'href="([^"/]+\.html)"', listing):
            page = m.group(1)
            if page == "index.html":
                continue
            rel = f"Unsorted/{session}/{page}"
            body = fetch(base + rel, retries)
            if body is None:
                continue
            _index_page(index, rel, body)
            pages += 1
    print(f"check_thesis_links: indexed {len(index)} anchor(s) from {pages} "
          f"published page(s)", file=sys.stderr)
    return index


def index_anchors() -> dict[tuple[str, str], str]:
    """Map (entity name, anchor kind) -> path#anchor, relative to docs/html."""
    index: dict[tuple[str, str], str] = {}
    for path in HTML.rglob("*.html"):
        rel = path.relative_to(HTML).as_posix()
        for m in ANCHOR.finditer(path.read_text(errors="ignore")):
            qualified, kind = m.group(1), m.group(2)
            anchor = f"{qualified}|{kind}".replace("|", "%7C")
            # Anchors are `<Theory>.<name>`, and a record field or locale
            # member carries its owner too (`CFG_Def.cfg.intra`). Prose cites
            # the short name, so register every suffix and let the shortest
            # win -- an exact citation beats a qualified one.
            parts = qualified.split(".")
            for i in range(1, len(parts)):
                index.setdefault((".".join(parts[i:]), kind), f"{rel}#{anchor}")
    return index


def cited() -> list[tuple[Path, int, str, str]]:
    refs = []
    for path in sorted((REPO / "thesis").rglob("*")):
        if path.suffix != ".typ" or not path.is_file():
            continue
        text = path.read_text(errors="ignore")
        for m in TYPST_REF.finditer(text):
            line = text.count("\n", 0, m.start()) + 1
            refs.append((path, line, m.group(1), m.group(2)))
    return refs


def resolve(index: dict[tuple[str, str], str] | None = None
            ) -> tuple[dict[str, str], list[str]]:
    if index is None:
        index = index_anchors()
    links: dict[str, str] = {}
    unresolved: list[str] = []
    for path, line, kind, name in cited():
        key = f"{kind}:{name}"
        if key in links:
            continue
        for anchor_kind in KIND_ANCHORS[kind]:
            hit = index.get((name, anchor_kind))
            if hit:
                links[key] = hit
                break
        else:
            unresolved.append(
                f"  {path.relative_to(REPO)}:{line}: {name} has no "
                f"{'/'.join(KIND_ANCHORS[kind])} anchor in the rendered theories")
    return links, unresolved


def skip_or_fail(detail: str, lenient: bool) -> int:
    """Fail, or -- locally -- say why the check could not run and move on."""
    if lenient:
        print(f"check_thesis_links: skipped -- {detail.splitlines()[0]}")
        print("  (link validity is checked against the deployed pages on main)")
        return 0
    print(f"check_thesis_links: {detail}", file=sys.stderr)
    return 1


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
            time.sleep(2 ** attempt)
    return None


def check_live(base_override: str | None, retries: int) -> int:
    """Verify every stored link against the site a reader will actually click."""
    if not OUT.is_file():
        print(f"check_thesis_links: no {OUT.relative_to(REPO)} to verify -- "
              "run --write against the rendered theories first", file=sys.stderr)
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
            # The stored anchor is percent-encoded for the URL; the page holds
            # the raw id.
            raw = anchor.replace("%7C", "|")
            if f'id="{raw}"' not in body:
                broken.append(f"  {key}: {url} has no anchor {raw}")

    if broken:
        print(f"check_thesis_links: {len(broken)} deployed link(s) do not reach "
              "a definition:")
        print("\n".join(broken))
        return 1

    total = sum(len(v) for v in by_page.values())
    print(f"check_thesis_links: {total} deployed link(s) reach their definition "
          f"across {len(by_page)} page(s)")
    return 0


def main() -> int:
    ap = argparse.ArgumentParser()
    mode = ap.add_mutually_exclusive_group(required=True)
    mode.add_argument("--write", action="store_true")
    mode.add_argument("--check", action="store_true")
    mode.add_argument("--live", action="store_true")
    mode.add_argument("--list", action="store_true")
    ap.add_argument("--base", help="override the link base URL")
    ap.add_argument("--lenient", action="store_true",
                    help="warn instead of failing when the theories are not "
                         "rendered locally")
    ap.add_argument("--retries", type=int, default=6,
                    help="--live: attempts per URL while Pages propagates")
    ap.add_argument("--from-live", action="store_true",
                    help="resolve against the published site instead of "
                         "docs/html")
    args = ap.parse_args()

    if args.live:
        return check_live(args.base, args.retries)

    base = args.base or pages_base()
    if args.from_live:
        index = index_live(base, args.retries)
    else:
        index = None
        if not HTML.is_dir() or not any(HTML.rglob("*.html")):
            return skip_or_fail(
                "no rendered theories under docs/html -- build them with "
                "`pixi run html`", args.lenient)

    links, unresolved = resolve(index)
    if unresolved:
        detail = (f"{len(unresolved)} cited entity/entities have no definition "
                  "anchor:\n" + "\n".join(unresolved) +
                  "\nEither the name is stale, or docs/html predates it "
                  "(rebuild with: pixi run html)")
        return skip_or_fail(detail, args.lenient)

    payload = json.dumps({"base": base, "links": links},
                         indent=2, sort_keys=True) + "\n"

    if args.list:
        for key, url in sorted(links.items()):
            print(f"{key}\n    {url}")
        return 0
    if args.write:
        OUT.parent.mkdir(parents=True, exist_ok=True)
        OUT.write_text(payload)
        print(f"check_thesis_links: wrote {OUT.relative_to(REPO)} "
              f"({len(links)} link(s))")
        return 0

    stored = OUT.read_text() if OUT.is_file() else ""
    if stored != payload:
        print("check_thesis_links: the stored links no longer match the "
              "rendered theories:\n")
        print("".join(difflib.unified_diff(
            stored.splitlines(True), payload.splitlines(True),
            fromfile="links.json (in the thesis)",
            tofile="links.json (resolved now)")))
        return 1

    print(f"check_thesis_links: {len(links)} link(s) resolve to a definition")
    return 0


if __name__ == "__main__":
    sys.exit(main())
