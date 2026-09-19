#!/usr/bin/env python3
"""Check that every link the site's pages carry still reaches something.

The landing page, explainer and playground link three kinds of target, and each
decays differently:

  * internal pages and assets (`playground.html`, `thesis.pdf`, `assets/...`),
    which break when the site layout changes;
  * anchors into the rendered theories (`Voblint/<Session>/<Theory>.html#...`),
    which break silently when a definition is renamed or moves -- the page
    still loads, it just no longer holds the name the sentence cites;
  * external URLs (GitHub permalinks, project sites), which break on their own.

Links are read from `pages/*.html` and from the page scripts (`explainer.js`,
`figures/*.js`), which build some definition links at runtime.

Every playground link -- in the pages, the README and docs/ -- is also checked for
what it opens, in every mode and without a build: its settings are values the
playground offers, a
`fixture=` names a regression file, and a `#code=` program decodes. A README
program link must carry one of the committed figure programs in docs/readme-figures,
so a figure, its program and its link cannot drift apart.

    scripts/check_pages_links.py --sources                   internal links, no build needed
    scripts/check_pages_links.py --site build/github-pages   internal links, local build
    scripts/check_pages_links.py --live                      everything, deployed site

`--sources` is the pre-commit check: it resolves each target to the file the site
script copies into place (SITE_LAYERS) and skips build outputs and external URLs.
Theory anchors are compared with build/isabelle-html when it exists, but only
warned about: a working copy's rendered theories are often older than its
sources, so the deployed check is the one that decides. `--site` needs `pixi run pages-site-build` first; external URLs are only
checked with `--external`. `--live` checks all three kinds against the published
site, after deployment, which is the moment the links are real. Hosts that
throttle automated clients (HTTP 403/429) are reported as unverified rather
than broken.
"""

from __future__ import annotations

import argparse
import base64
import re
import sys
import urllib.error
import urllib.parse
import urllib.request
import zlib
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))
from check_thesis_links import fetch, pages_base  # noqa: E402
from vimp_fixture import shown_source  # noqa: E402

REPO = Path(__file__).resolve().parent.parent
PAGES = REPO / "pages"

# The directories scripts/mk/pages-site.sh copies into the site, in copy order,
# each onto its site prefix: a later layer overwrites an earlier one, so --sources
# looks a path up from the last layer back.
SITE_LAYERS = [
    ("", PAGES),
    ("assets/", REPO / "docs/images"),
]
# Site paths the build generates or copies from build outputs, which a working
# copy may not have: the wasm bundle, derived data, and the PDFs.
BUILD_OUTPUTS = (
    "assets/voblint_web.bc.wasm",
    "assets/site-stats.js",
    "assets/regression-examples.json",
    "sitemap.xml",
    "thesis.pdf",
    "formalization.pdf",
)
ISABELLE_HTML = REPO / "build" / "isabelle-html"
THEORY_PREFIXES = ("Voblint/", "Unsorted/", "HOL/", "Pure/")

ATTR = re.compile(r'\b(?:href|src)="([^"]+)"')
IS_A_CONST = re.compile(r'isaConst\("([^"]+)", "([^"]+)", "([^"]+)"\)')
USER_AGENT = "voblint-link-check (+https://github.com/ManuelLerchner/Voblint-Verification-Master-Thesis)"


def collected() -> dict[str, set[str]]:
    """Map each link target to the source files that carry it."""
    links: dict[str, set[str]] = {}

    def add(url: str, source: str) -> None:
        links.setdefault(url.replace("&amp;", "&"), set()).add(source)

    for page in sorted(PAGES.glob("*.html")):
        for m in ATTR.finditer(page.read_text()):
            url = m.group(1)
            # A same-page anchor is resolved against the page it sits in.
            add(f"{page.name}{url}" if url.startswith("#") else url, page.name)
    scripts = [PAGES / "explainer.js", *sorted((PAGES / "figures").glob("*.js"))]
    for script in scripts:
        for m in IS_A_CONST.finditer(script.read_text()):
            session, theory, name = m.groups()
            add(
                f"Voblint/{session}/{theory}.html#{theory}.{name}%7Cconst",
                str(script.relative_to(PAGES)),
            )
    return links


PLAYGROUND_KEYS = {"fixture", "analysis", "globals", "context", "k"}
PLAYGROUND_SELECTS = {
    "analysis": "analysis-select",
    "globals": "globals-select",
    "context": "context-select",
}
MARKDOWN_PLAYGROUND = re.compile(
    r"(?:https?://[^\s\"'<>()]*/)?playground\.html[^\s\"'<>()]*"
)
FIGURE_PROGRAMS = REPO / "docs" / "readme-figures"
REGRESSION = REPO / "tests" / "regression"


def playground_vocabulary() -> dict[str, object]:
    """What a playground link may name, read from the playground itself."""
    html = (PAGES / "playground.html").read_text()
    script = (PAGES / "main.js").read_text()
    options = {}
    for key, select in PLAYGROUND_SELECTS.items():
        block = re.search(rf'<select id="{select}"[^>]*>(.*?)</select>', html, re.S)
        options[key] = (
            set(re.findall(r'<option value="([^"]+)"', block.group(1)))
            if block
            else set()
        )
    depth = re.search(r"^const MAX_CONTEXT_DEPTH = (\d+);", script, re.M)
    return {
        "options": options,
        "max_depth": int(depth.group(1)) if depth else 0,
    }


def unpack_code(packed: str) -> str:
    """A `#code=` program: raw deflate, base64url without padding."""
    padded = packed + "=" * (-len(packed) % 4)
    return zlib.decompress(base64.urlsafe_b64decode(padded), wbits=-15).decode()


def check_playground(url: str, source: str, vocabulary: dict[str, object]) -> list[str]:
    """What is wrong with the program and settings a playground link opens."""
    parsed = urllib.parse.urlsplit(url)
    query = urllib.parse.parse_qs(parsed.query, keep_blank_values=True)
    problems = [
        f"unknown parameter {key}" for key in query if key not in PLAYGROUND_KEYS
    ]

    for key, allowed in vocabulary["options"].items():
        for value in query.get(key, []):
            if value not in allowed:
                problems.append(f"{key}={value} is not a playground option")

    for value in query.get("k", []):
        if not value.isdigit() or int(value) > vocabulary["max_depth"]:
            problems.append(f"k={value} is outside 0..{vocabulary['max_depth']}")

    for path in query.get("fixture", []):
        if not (REGRESSION / path).is_file():
            problems.append(f"fixture={path} is not a regression file")

    code = urllib.parse.parse_qs(parsed.fragment).get("code", [])
    named = [key for key in ("fixture",) if key in query] + (["code"] if code else [])
    if len(named) > 1:
        problems.append(f"names its program twice ({', '.join(named)})")

    for packed in code:
        try:
            program = unpack_code(packed)
        except (ValueError, zlib.error, UnicodeDecodeError) as error:
            problems.append(f"#code= does not decode: {error}")
            continue
        if source == "README.md" and not any(
            program == shown_source(figure.read_text())
            for figure in FIGURE_PROGRAMS.glob("*.vimp")
        ):
            problems.append(
                f"#code= program is none of {FIGURE_PROGRAMS.relative_to(REPO)}/*.vimp"
            )

    return problems


def playground_links(page_links: dict[str, set[str]]) -> dict[str, set[str]]:
    """Every playground link, from the pages and from the Markdown documentation."""
    found = {
        url: sources
        for url, sources in page_links.items()
        if "playground.html?" in url or "playground.html#" in url
    }
    documents = [REPO / "README.md", *sorted((REPO / "docs").rglob("*.md"))]
    for document in documents:
        if "history" in document.parts or "generated" in document.parts:
            continue
        for match in MARKDOWN_PLAYGROUND.finditer(document.read_text()):
            url = match.group(0).replace("&amp;", "&")
            if "?" in url or "#" in url:
                found.setdefault(url, set()).add(str(document.relative_to(REPO)))
    return found


def split(url: str) -> tuple[str, str]:
    """Path without query, and the decoded fragment."""
    parsed = urllib.parse.urlsplit(url)
    return parsed.path, urllib.parse.unquote(parsed.fragment)


def anchor_present(body: str, fragment: str) -> bool:
    return f'id="{fragment}"' in body or f"id='{fragment}'" in body


def check_internal_local(site: Path, url: str) -> str | None:
    path, fragment = split(url)
    target = site / path
    if not target.is_file():
        return f"{path} does not exist in {site}"
    if (
        fragment
        and target.suffix == ".html"
        and not anchor_present(target.read_text(errors="ignore"), fragment)
    ):
        return f"{path} has no anchor {fragment}"
    return None


def source_of(path: str) -> Path | None:
    if path.startswith(BUILD_OUTPUTS):
        return None
    for prefix, root in reversed(SITE_LAYERS):
        if path.startswith(prefix) and (root / path[len(prefix) :]).is_file():
            return root / path[len(prefix) :]
    return PAGES / path


def check_internal_sources(
    url: str, skipped: list[str], stale: list[str]
) -> str | None:
    path, fragment = split(url)
    if path.startswith(THEORY_PREFIXES):
        if not ISABELLE_HTML.is_dir():
            skipped.append(url)
        elif detail := check_internal_local(ISABELLE_HTML, url):
            stale.append(f"  {url}: {detail}")
        return None
    target = source_of(path)
    if target is None:
        return None
    if not target.is_file():
        return f"{path} has no source file ({target.relative_to(REPO)})"
    if (
        fragment
        and target.suffix == ".html"
        and not anchor_present(target.read_text(errors="ignore"), fragment)
    ):
        return f"{path} has no anchor {fragment}"
    return None


def check_internal_live(
    base: str, url: str, retries: int, cache: dict[str, str | None]
) -> str | None:
    path, fragment = split(url)
    full = base.rstrip("/") + "/" + path
    if full not in cache:
        cache[full] = fetch(full, retries)
    body = cache[full]
    if body is None:
        return f"{full} did not respond"
    if fragment and path.endswith(".html") and not anchor_present(body, fragment):
        return f"{full} has no anchor {fragment}"
    return None


def check_external(url: str) -> tuple[str, str | None]:
    """Returns ("ok" | "unverified" | "broken", detail)."""
    target = urllib.parse.urlunsplit(urllib.parse.urlsplit(url)._replace(fragment=""))
    refused: str | None = None
    for method in ("HEAD", "GET"):
        request = urllib.request.Request(
            target, method=method, headers={"User-Agent": USER_AGENT}
        )
        try:
            with urllib.request.urlopen(request, timeout=20) as response:
                if response.status < 400:
                    return "ok", None
        except urllib.error.HTTPError as error:
            if error.code in (403, 429):
                refused = f"HTTP {error.code}"
                continue
            if method == "HEAD" and error.code in (400, 404, 405, 501):
                continue
            return "broken", f"HTTP {error.code}"
        except (urllib.error.URLError, OSError) as error:
            return "broken", str(getattr(error, "reason", error))
    return ("unverified", refused) if refused else ("broken", "no successful response")


def main() -> int:
    ap = argparse.ArgumentParser()
    mode = ap.add_mutually_exclusive_group(required=True)
    mode.add_argument(
        "--sources",
        action="store_true",
        help="check against the repository, no build needed",
    )
    mode.add_argument(
        "--site", type=Path, help="assembled site directory, e.g. build/github-pages"
    )
    mode.add_argument("--live", action="store_true", help="check the deployed site")
    ap.add_argument("--base", help="--live: override the site URL")
    ap.add_argument(
        "--external", action="store_true", help="--site: also check external URLs"
    )
    ap.add_argument(
        "--retries",
        type=int,
        default=6,
        help="--live: attempts per page while Pages propagates",
    )
    args = ap.parse_args()

    links = collected()
    broken: list[str] = []
    vocabulary = playground_vocabulary()
    playground = playground_links(links)
    for url, sources in sorted(playground.items()):
        for source in sorted(sources):
            for problem in check_playground(url, source, vocabulary):
                broken.append(f"  {url[:120]} ({source}): {problem}")
    unverified: list[str] = []
    cache: dict[str, str | None] = {}
    skipped: list[str] = []
    stale: list[str] = []
    base = args.base or pages_base()

    if args.site and not args.site.is_dir():
        print(
            f"check_pages_links: no site at {args.site} -- run `pixi run pages-site-build`",
            file=sys.stderr,
        )
        return 1
    if args.live and not base:
        print("check_pages_links: no base URL to verify against", file=sys.stderr)
        return 1

    for url, sources in sorted(links.items()):
        scheme = urllib.parse.urlsplit(url).scheme
        where = ", ".join(sorted(sources))
        if scheme in ("mailto", "javascript", "data"):
            continue
        if scheme in ("http", "https"):
            if args.sources or not (args.live or args.external):
                continue
            status, detail = check_external(url)
            if status == "broken":
                broken.append(f"  {url} ({where}): {detail}")
            elif status == "unverified":
                unverified.append(f"  {url} ({where}): {detail}")
            continue
        if args.sources:
            detail = check_internal_sources(url, skipped, stale)
        elif args.live:
            detail = check_internal_live(base, url, args.retries, cache)
        else:
            detail = check_internal_local(args.site, url)
        if detail:
            broken.append(f"  {url} ({where}): {detail}")

    if stale:
        print(
            f"check_pages_links: warning: {len(stale)} theory link(s) not found in build/isabelle-html; "
            "rebuild it with `pixi run isabelle-html-build` if the names are new:"
        )
        print("\n".join(stale))
    if skipped:
        print(
            f"check_pages_links: {len(skipped)} theory link(s) skipped -- no build/isabelle-html "
            "(checked against the deployed site on main)"
        )
    if unverified:
        print(
            f"check_pages_links: {len(unverified)} link(s) could not be verified (host refused automated access):"
        )
        print("\n".join(unverified))
    if broken:
        print(f"check_pages_links: {len(broken)} broken link(s):")
        print("\n".join(broken))
        return 1
    print(
        f"check_pages_links: {len(links)} link(s) and {len(playground)} playground link(s) "
        "checked, none broken"
    )
    return 0


if __name__ == "__main__":
    sys.exit(main())
