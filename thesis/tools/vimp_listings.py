#!/usr/bin/env python3
"""Every VIMP listing in the thesis opens its program in the playground.

`listing(lang: "c")` in ``thesis/lib/code.typ`` computes a playground link from
the text it shows and records both in a ``<vimp-listing>`` metadata element.
This tool checks the built document rather than the markup:

  * every link decodes to the program the listing shows (or, for a listing
    naming a claim, to that claim's fixture), and its settings are options the
    playground offers;
  * every such link is a clickable annotation in the compiled PDF;
  * no VIMP code reaches the document outside the linked helper;
  * a listing showing a regression fixture or a claimed program uses the
    settings that fixture or claim runs with;
  * every linked program parses (``voblint --parse-only``);
  * the helper's default settings are still the playground's.

``--write`` extracts the claims' programs and settings into
``shared/generated/vimp-claims.json``, the one input Typst cannot read itself
(fixtures live outside the thesis root). ``--source`` runs only the checks that
need no build, for the pre-commit hook.

    python3 thesis/tools/vimp_listings.py --write
    python3 thesis/tools/vimp_listings.py --check
    python3 thesis/tools/vimp_listings.py --source
"""

from __future__ import annotations

import argparse
import json
import re
import subprocess
import sys
import tempfile
import urllib.parse
from collections import Counter
from pathlib import Path

import tomllib

THESIS = Path(__file__).resolve().parents[1]
REPO = THESIS.parent
sys.path.insert(0, str(REPO / "scripts"))

import check_pages_links  # noqa: E402
import vimp_fixture  # noqa: E402

CLAIMS = THESIS / "shared" / "claims.toml"
OUT = THESIS / "shared" / "generated" / "vimp-claims.json"
CODE_TYP = THESIS / "lib" / "code.typ"
REGRESSION = REPO / "tests" / "regression"
CLI = REPO / "cli" / "voblint"
FONTS = THESIS / "assets" / "fonts"
MAIN = THESIS / "thesis.typ"

# Built only with `--input gallery=1`; a drafting reference, not thesis content.
SOURCE_EXEMPT = {"content/03-gallery.typ"}

# The voblint CLI's defaults, which a claim's argv leaves implicit.
CLI_DEFAULTS = {"globals": "warrow", "context": "none"}

VIMP_LANGS = ("c", "vimp")
VIMP_SHAPE = re.compile(
    r"\bfun\s+\w+\s*\(|__voblint_\w+\s*\(|^\s*global\s+\w+\s*;", re.M
)


# ----------------------------------------------------------------- claims ---


def run_settings(args: list[str]) -> dict[str, object]:
    """The playground settings a voblint command line selects."""
    given = vimp_fixture.analysis_settings(args)
    settings = {
        "analysis": given["analyses"][0],
        "globals": given.get("globals", CLI_DEFAULTS["globals"]),
        "context": given.get("context", CLI_DEFAULTS["context"]),
    }
    if settings["context"] == "call-string":
        settings["k"] = given["context_depth"]
    return settings


def uncommented(program: str) -> str:
    """A fixture without its comments, which document the regression run (a
    `// UNKNOWN` verdict, the domain it was written for) and would mislead in a
    playground opened at another claim's settings."""
    lines = [re.sub(r"\s*//.*$", "", line) for line in program.splitlines()]
    kept = [
        line
        for line, original in zip(lines, program.splitlines(), strict=True)
        if line or not original.strip().startswith("//")
    ]
    return "\n".join(kept).strip("\n")


def claim_runs() -> dict[str, dict]:
    """Each claim that runs one program successfully: its program and settings."""
    runs = {}
    for name, claim in tomllib.loads(CLAIMS.read_text()).get("claims", {}).items():
        programs = [a for a in claim["argv"] if a.endswith(".vimp")]
        if len(programs) != 1 or claim.get("expect_status", 0) != 0:
            continue
        # A claim that only parses (--ast) runs no analysis, so it has no
        # settings for a listing to open the playground at.
        if "--analysis" not in claim["argv"]:
            continue
        flags = [a for a in claim["argv"] if a != programs[0]]
        runs[name] = {
            "fixture": programs[0],
            "program": uncommented(
                vimp_fixture.shown_source((REPO / programs[0]).read_text())
            ),
            "settings": run_settings(flags),
        }
    return runs


def render_claims() -> str:
    return json.dumps(claim_runs(), indent=2, sort_keys=True, ensure_ascii=False) + "\n"


# --------------------------------------------------------------- programs ---


def vimp_program(shown: str) -> str:
    """What a listing's link opens: a fragment runs as the body of `main`.

    Mirrors `vimp-program` in lib/code.typ; the check compares the two.
    """
    if re.search(r"^(fun|global)\b", shown, re.M):
        return shown
    body = "\n".join("  " + line if line else line for line in shown.split("\n"))
    return "fun main() {\n" + body + "\n}"


def tokens(program: str) -> list[str]:
    """A program up to layout and comments, for recognizing a shown fixture."""
    code = re.sub(r"//[^\n]*", "", program)
    return re.findall(r"\w+|[^\s\w]", code)


def is_subsequence(part: list[str], whole: list[str]) -> bool:
    rest = iter(whole)
    return all(token in rest for token in part)


def known_runs(
    claims: dict[str, dict],
) -> dict[tuple[str, ...], list[tuple[str, dict]]]:
    """Programs the repository runs at fixed settings, by their tokens."""
    runs: dict[tuple[str, ...], list[tuple[str, dict]]] = {}
    for name, run in claims.items():
        runs.setdefault(tuple(tokens(run["program"])), []).append(
            (f"claim {name}", run["settings"])
        )
    for path in sorted(REGRESSION.rglob("*.vimp")):
        header = vimp_fixture.param_args(path)
        if not header:
            continue
        try:
            settings = run_settings(header)
        except (KeyError, ValueError):
            continue
        runs.setdefault(
            tuple(tokens(vimp_fixture.shown_source(path.read_text()))), []
        ).append((f"fixture {path.relative_to(REGRESSION)}", settings))
    return runs


def link_settings(settings: dict) -> dict[str, str]:
    """Settings as the query carries them: k only for call strings."""
    out = {key: str(settings[key]) for key in ("analysis", "globals", "context")}
    if settings["context"] == "call-string":
        out["k"] = str(settings["k"])
    return out


# ----------------------------------------------------------- source scan ---

RAW_VIMP = re.compile(r"```(?:" + "|".join(VIMP_LANGS) + r")\b")
LANG_VIMP = re.compile(r"lang:\s*\"(?:" + "|".join(VIMP_LANGS) + r")\"")


def enclosing_call(text: str, index: int) -> str | None:
    """The function whose argument list contains `index`, if any."""
    depth = 0
    for i in range(index - 1, -1, -1):
        if text[i] == ")":
            depth += 1
        elif text[i] == "(":
            if depth == 0:
                name = re.search(r"([\w-]+)\s*$", text[:i])
                return name.group(1) if name else None
            depth -= 1
    return None


def line_of(text: str, index: int) -> int:
    return text.count("\n", 0, index) + 1


def scan_source(root: Path = THESIS) -> list[str]:
    """VIMP code written so that it bypasses `listing(lang: "c")`."""
    problems = []
    for path in sorted(root.rglob("*.typ")):
        rel = path.relative_to(root).as_posix()
        if rel in SOURCE_EXEMPT or rel.startswith("shared/generated/"):
            continue
        text = path.read_text()
        for match in RAW_VIMP.finditer(text):
            problems.append(
                f"{rel}:{line_of(text, match.start())}: a ```{match.group(0)[3:]} block has no playground "
                'link; use listing(```...```, lang: "c")'
            )
        for match in LANG_VIMP.finditer(text):
            line = text[text.rfind("\n", 0, match.start()) + 1 : match.start()]
            if re.search(r"(^|[^:])//", line):
                continue
            call = enclosing_call(text, match.start())
            if call != "listing":
                problems.append(
                    f"{rel}:{line_of(text, match.start())}: VIMP code in {call or 'markup'}(...) has no "
                    'playground link; use listing(..., lang: "c")'
                )
    return problems


FIXTURE_CALL = re.compile(r'fixture\("([^"]+)"')
BARE_FIXTURE = re.compile(r"`[\w./-]+\.vimp`")


def scan_fixtures(root: Path = THESIS, repo: Path = REPO) -> list[str]:
    """Fixture paths named in the chapters: linked, and still present."""
    problems = []
    for path in sorted((root / "content").rglob("*.typ")):
        rel = path.relative_to(root).as_posix()
        text = path.read_text()
        for match in FIXTURE_CALL.finditer(text):
            target = repo / "tests/regression" / match.group(1)
            if not target.is_file():
                problems.append(
                    f"{rel}:{line_of(text, match.start())}: fixture "
                    f"{match.group(1)} does not exist under tests/regression"
                )
        for match in BARE_FIXTURE.finditer(text):
            problems.append(
                f"{rel}:{line_of(text, match.start())}: {match.group(0)} names a "
                'fixture without a link; use fixture("<path>")'
            )
    return problems


def check_defaults() -> list[str]:
    """The helper's defaults must be what the playground itself selects."""
    html = (REPO / "pages" / "playground.html").read_text()
    page = {}
    for key, select in check_pages_links.PLAYGROUND_SELECTS.items():
        block = re.search(rf'<select id="{select}"[^>]*>(.*?)</select>', html, re.S)
        chosen = (
            re.search(r'<option value="([^"]+)" selected', block.group(1))
            if block
            else None
        )
        page[key] = chosen.group(1) if chosen else None
    depth = re.search(r'id="context-depth".*?value="(\d+)"', html, re.S)
    page["k"] = depth.group(1) if depth else None

    line = re.search(
        r"^#let playground-defaults = \((.*?)\)$", CODE_TYP.read_text(), re.M | re.S
    )
    if not line:
        return ["lib/code.typ: no `playground-defaults` line"]
    ours = {
        k: v.strip('"')
        for k, v in re.findall(r'"(\w+)":\s*("[^"]*"|\d+)', line.group(1))
    }
    return [
        f"lib/code.typ: default {key}={ours.get(key)} but the playground selects {value}"
        for key, value in page.items()
        if ours.get(key) != value
    ]


# ----------------------------------------------------------- built check ---


def typst(*args: str) -> str:
    proc = subprocess.run(
        ["typst", *args, "--root", str(THESIS), "--font-path", str(FONTS)],
        capture_output=True,
        text=True,
    )
    if proc.returncode != 0:
        sys.exit(f"vimp_listings: typst {args[0]} failed\n{proc.stderr}")
    return proc.stdout


def evaluate(expression: str, main: Path = MAIN) -> list:
    """A Typst expression over the compiled document, as JSON."""
    return json.loads(typst("eval", expression, "--in", str(main)))


def pdf_uris(pdf: bytes) -> Counter:
    """Every URI action in the PDF, unescaped from PDF literal strings."""
    found = Counter()
    for match in re.finditer(rb"/S\s*/URI\s*/URI\s*\(((?:[^()\\]|\\.)*)\)", pdf, re.S):
        raw = match.group(1)
        raw = re.sub(rb"\\([0-7]{1,3})", lambda m: bytes([int(m.group(1), 8)]), raw)
        raw = re.sub(rb"\\(.)", rb"\1", raw)
        found[raw.decode("latin-1")] += 1
    return found


def parse_error(program: str) -> str | None:
    with tempfile.NamedTemporaryFile("w", suffix=".vimp", delete=False) as handle:
        handle.write(program)
    try:
        proc = subprocess.run(
            [str(CLI), "--parse-only", handle.name], capture_output=True, text=True
        )
    finally:
        Path(handle.name).unlink()
    return None if proc.returncode == 0 else (proc.stderr or proc.stdout).strip()


def describe(listing: dict) -> str:
    first = next(
        (line.strip() for line in listing["shown"].splitlines() if line.strip()), ""
    )
    return f"listing `{first[:40]}`" + (
        f" (claim {listing['claim']})" if listing["claim"] else ""
    )


def check_listing(
    listing: dict,
    claims: dict[str, dict],
    runs: dict[tuple[str, ...], list[tuple[str, dict]]],
    vocabulary: dict,
) -> list[str]:
    """What is wrong with one listing's link."""
    name = describe(listing)
    url = listing["url"]
    problems = [
        f"{name}: {p}"
        for p in check_pages_links.check_playground(url, "thesis", vocabulary)
    ]

    parsed = urllib.parse.urlsplit(url)
    query_settings = dict(urllib.parse.parse_qsl(parsed.query))
    packed = urllib.parse.parse_qs(parsed.fragment).get("code", [""])[0]
    try:
        decoded = check_pages_links.unpack_code(packed)
    except Exception as error:  # noqa: BLE001 -- reported, not raised
        return problems + [f"{name}: #code= does not decode: {error}"]

    claim = listing["claim"]
    part_of = listing.get("part-of")
    if part_of is not None:
        expected = part_of
        if not is_subsequence(tokens(listing["shown"]), tokens(part_of)):
            problems.append(f"{name}: is not part of the program it links")
    elif claim is None:
        expected = vimp_program(listing["shown"])
    elif claim not in claims:
        return problems + [f"{name}: no claim {claim} in claims.toml"]
    else:
        expected = claims[claim]["program"]
    if decoded != expected:
        problems.append(
            f"{name}: the link opens a different program than the listing shows"
        )

    settings = link_settings(listing["settings"])
    if query_settings != settings:
        problems.append(
            f"{name}: link settings {query_settings} are not the listing's {settings}"
        )

    shown = tokens(listing["shown"])
    if claim is not None:
        run = claims[claim]
        fixture = tokens(run["program"])
        if shown != fixture and not is_subsequence(shown, fixture):
            problems.append(
                f"{name}: shows neither {run['fixture']} nor an excerpt of it"
            )
        for key, value in listing["given"].items():
            if key in run["settings"] and str(value) != str(run["settings"][key]):
                problems.append(
                    f"{name}: {key}={value} overrides claim {claim}'s {key}={run['settings'][key]}"
                )
    else:
        candidates = runs.get(tuple(tokens(expected)), [])
        if candidates and not any(link_settings(s) == settings for _, s in candidates):
            options = "; ".join(
                f"{label}: {link_settings(s)}" for label, s in candidates
            )
            problems.append(
                f"{name}: shows a program the repository runs, but at other settings "
                f"than {settings} ({options}); pass claim: or matching settings"
            )

    if CLI.is_file():
        error = parse_error(decoded)
        if error:
            problems.append(f"{name}: the linked program does not parse: {error}")
    return problems


def check_built(main: Path = MAIN) -> tuple[list[str], int]:
    """Check every VIMP listing of the compiled document, and its PDF links."""
    claims = claim_runs()
    runs = known_runs(claims)
    vocabulary = check_pages_links.playground_vocabulary()
    listings = evaluate("query(<vimp-listing>).map(m => m.value)", main)
    problems = []
    for listing in listings:
        problems += check_listing(listing, claims, runs, vocabulary)

    # Block raws only: codly re-emits a listing's raw, so they are compared as a
    # set, and inline code in prose is a fragment, not a program to open.
    linked = {listing["shown"] for listing in listings}
    blocks = 'query(raw.where(block: true)).map(r => (lang: r.at("lang", default: none), text: r.text))'
    for element in evaluate(blocks, main):
        lang = element.get("lang")
        text = element.get("text", "")
        if lang in VIMP_LANGS or (lang in (None, "") and VIMP_SHAPE.search(text)):
            if text in linked:
                continue
            first = text.strip().splitlines()[0] if text.strip() else ""
            problems.append(
                f"raw `{first[:40]}` shows VIMP code without a playground link"
            )

    with tempfile.TemporaryDirectory() as tmp:
        pdf = Path(tmp) / "thesis.pdf"
        typst("compile", str(main), str(pdf))
        uris = pdf_uris(pdf.read_bytes())
    wanted = Counter(listing["url"] for listing in listings)
    for url, count in wanted.items():
        if uris[url] < count:
            problems.append(
                f"PDF has {uris[url]} link annotation(s) to a listing's playground URL, "
                f"expected {count}: {url[:100]}..."
            )
    return problems, len(listings)


# ------------------------------------------------------------------ main ---


def main() -> int:
    ap = argparse.ArgumentParser()
    mode = ap.add_mutually_exclusive_group(required=True)
    mode.add_argument(
        "--write", action="store_true", help="extract the claims' programs"
    )
    mode.add_argument("--check", action="store_true", help="check the built document")
    mode.add_argument(
        "--source", action="store_true", help="only the checks needing no build"
    )
    args = ap.parse_args()

    if args.write:
        OUT.write_text(render_claims())
        print(f"vimp_listings: wrote {OUT.relative_to(REPO)}")
        return 0

    problems = []
    if not OUT.is_file() or OUT.read_text() != render_claims():
        problems.append(
            f"{OUT.relative_to(REPO)} is stale; run `pixi run thesis-vimp-write`"
        )
    problems += scan_source()
    problems += scan_fixtures()
    problems += check_defaults()
    count = None
    if args.check:
        if not CLI.is_file():
            problems.append("cli/voblint is not built; run `pixi run cli-build`")
        built, count = check_built()
        problems += built

    for problem in problems:
        print(f"vimp_listings: {problem}", file=sys.stderr)
    if problems:
        return 1
    print(
        "vimp_listings: "
        + (
            f"{count} VIMP listing(s) link their program"
            if count is not None
            else "sources clean"
        )
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
