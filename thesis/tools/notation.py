#!/usr/bin/env python3
"""Derive the notation table from the theories and render it in three places.

The table appears in the README's Notation section and as the legend above
the explainer's flagship theorems; the thesis can render it from the same data. Three
hand-written copies would drift from each other and from the theories, so
`thesis/shared/notation.toml` types only what cannot be read off a declaration
-- how to read a symbol and what it means -- and this tool derives the rest:

  * the symbol, from the declaration's mixfix and the manifest's argument names;
  * the theory, scope (global or the declaring locale) and print mode (an
    `abbreviation (input)` is never printed back);
  * a locale abbreviation's expansion, and which global set it abbreviates;
  * the rendered-theory link.

`isar project notation` (isar-tools) finds each declaration and reads all of
that off it; an unsupported declaration shape or a missing name fails with its
file and line. This tool keeps what is particular to this repository: the
prose, the variable convention, the check that a local form abbreviates its
global set, and the three renderings.

Output: `thesis/shared/generated/notation.json` (read by the appendix), and the
generated blocks between `notation:begin`/`notation:end` markers in README.md
and pages/index.html.

    thesis/tools/notation.py --write            regenerate all three
    thesis/tools/notation.py --check            fail on drift or a missing anchor
    thesis/tools/notation.py --check --lenient  without rendered theories, accept
                                                the links the sources determine
"""

from __future__ import annotations

import argparse
import html
import json
import re
import subprocess
import sys
import tempfile
from pathlib import Path

import tomllib

REPO = Path(__file__).resolve().parents[2]

MANIFEST = REPO / "thesis" / "shared" / "notation.toml"
OUT = REPO / "thesis" / "shared" / "generated" / "notation.json"
HTML = REPO / "build" / "isabelle-html"
SYMBOLS = REPO / "thesis" / "lib" / "isabelle-symbols.typ"
SITE_SCRIPT = REPO / "scripts" / "mk" / "pages-site.sh"
README = REPO / "README.md"
PAGE = REPO / "pages" / "index.html"


class NotationError(ValueError):
    pass


# ------------------------------------------------------------ declarations


def _isar_name(form: dict) -> str:
    """How `isar project notation` names a form's declaration."""
    if "locale" in form:
        return f"{form['locale']}.{form['const']}"
    if "parameter_of" in form:
        return f"{form['parameter_of']}.{form['const']}"
    if "record" in form:
        return f"{form['record']}.{form['const']}"
    if "class" in form:
        return f"{form['class']}_class.{form['const']}"
    return form["const"]


def resolve_declarations(requests: dict[str, dict], lenient: bool) -> dict[str, dict]:
    """Each requested declaration as `isar project notation` reads it.

    `requests` maps a manifest key to {"name", "args"}. The command finds the
    declaration, fills its mixfix with the argument names and reports its kind,
    scope, print mode, an abbreviation's expansion and its rendered-theory
    link; an unsupported shape or a missing name fails with its file and line.
    With the rendered theories built, every link must reach an anchor there;
    without them, `lenient` accepts the links the sources determine.
    """
    built = HTML.is_dir() and any(HTML.rglob("*.html"))
    if not built and not lenient:
        raise NotationError(
            "no rendered theories under build/isabelle-html; build them with "
            "pixi run isabelle-html-build, or pass --lenient"
        )
    with tempfile.TemporaryDirectory() as tmp:
        manifest = Path(tmp) / "notation.toml"
        out = Path(tmp) / "notation.json"
        manifest.write_text(
            "".join(
                f"[notation.{json.dumps(key)}]\n"
                f"name = {json.dumps(req['name'])}\n"
                f"args = {json.dumps(req['args'])}\n"
                for key, req in requests.items()
            )
        )
        run = subprocess.run(
            [
                sys.executable,
                "-m",
                "isar_tools",
                "project",
                "notation",
                str(manifest),
                "--project",
                str(REPO),
                "--out",
                str(out),
                "--write",
                *(["--browser-info", str(HTML)] if built else []),
            ],
            capture_output=True,
            text=True,
            check=False,
        )
        if run.returncode != 0:
            raise NotationError(run.stderr.strip() or run.stdout.strip())
        rows = json.loads(out.read_text())["notation"]
    return {row["key"]: row for row in rows}


def _declaration(row: dict) -> str:
    """The declaration as the table names it: the command, or its owner."""
    kind, owner = row["kind"], row["owner"]
    if kind == "class_parameter":
        return f"class {owner}"
    if kind == "record_field":
        return f"record {owner}"
    if kind == "locale_parameter":
        return f"locale {owner}"
    if kind == "locale_abbreviation":
        return "abbreviation" if row["printed"] else "abbreviation (input)"
    return row["command"]


def _decl(row: dict) -> dict:
    decl = {
        "declaration": _declaration(row),
        "mixfix": row["notation"],
        "scope": row["scope"],
        "pretty_printed": row["printed"],
        "path": REPO / row["path"],
        "site": f"{row['path']}:{row['line']}",
    }
    # The table shows an expansion only for a shorthand, a locale abbreviation.
    if row["kind"] == "locale_abbreviation":
        decl["expands"] = " ".join(row["expansion"]["rhs"].split())
    return decl


def check_binds(symbol: str, row: dict) -> None:
    """A variable convention: the declaration binds `symbol` in a `for` clause."""
    lines = (REPO / row["path"]).read_text().splitlines()[row["line"] - 1 :]
    head = "\n".join(lines[:20]).split("where", 1)[0]
    if not re.search(r"\bfor\s+" + re.escape(symbol) + r"(?![A-Za-z0-9_'])", head):
        raise NotationError(
            f"{row['key']}: expected `for {symbol}` in its declaration at "
            f"{row['path']}:{row['line']}"
        )


# ------------------------------------------------------------------ links


def site_base() -> str:
    m = re.search(r'SITE_URL="\$\{SITE_URL:-([^}]+)\}"', SITE_SCRIPT.read_text())
    if not m:
        raise NotationError(f"no SITE_URL default in {SITE_SCRIPT.relative_to(REPO)}")
    return m[1].rstrip("/") + "/"


# ----------------------------------------------------------------- build


def form_record(
    decl: dict, const: str, key: str, symbol: str, row: dict, kind: str = "const"
) -> dict:
    """A form of an entry; a locale parameter links to its locale."""
    rec = {
        "const": const,
        "cite": {"kind": kind, "name": key},
        "symbol": symbol,
        "mixfix": decl["mixfix"],
        "declaration": decl["declaration"],
        "scope": decl["scope"],
        "pretty_printed": decl["pretty_printed"],
        "theory": row["theory"],
        "file": row["path"],
        "href": row["owner_url"] if kind == "locale" else row["url"],
        "session": row["session"],
    }
    if "expands" in decl:
        rec["expands"] = decl["expands"]
    if decl["scope"] != "global":
        rec["scope_href"] = row["owner_url"]
    return rec


def build(manifest: dict, lenient: bool) -> tuple[dict, list[str]]:
    groups = manifest["groups"]
    requests: dict[str, dict] = {}
    for n, raw in enumerate(manifest["entry"], 1):
        if raw.get("group") not in groups:
            raise NotationError(f"entry {n}: unknown group {raw.get('group')!r}")
        if "symbol" in raw:
            requests[f"{n}.convention"] = {"name": raw["const"], "args": []}
            # Only the declaration's site is read; the slots get placeholder names.
            for const in raw["bound_in"]:
                requests[f"{n}.binds.{const}"] = {"name": const, "args": ["_"] * 9}
        for m, f in enumerate(raw.get("forms", [])):
            requests[f"{n}.form.{m}"] = {
                "name": _isar_name(f),
                "args": f.get("args", []),
            }
        if "local" in raw:
            loc = raw["local"]
            requests[f"{n}.local"] = {
                "name": f"{loc['locale']}.{loc['const']}",
                "args": loc.get("args", []),
            }
    rows = resolve_declarations(requests, lenient)

    entries = []
    for n, raw in enumerate(manifest["entry"], 1):
        entry = {
            "id": "",
            "group": raw["group"],
            "kind": "",
            "reads": raw["reads"],
            "meaning": raw["meaning"],
            "forms": [],
            "local": None,
        }
        if "symbol" in raw:
            for const in raw["bound_in"]:
                check_binds(raw["symbol"], rows[f"{n}.binds.{const}"])
            row = rows[f"{n}.convention"]
            decl = _decl(row)
            decl["declaration"] = "variable convention"
            entry["kind"] = "convention"
            entry["forms"].append(
                form_record(decl, raw["const"], raw["const"], raw["symbol"], row)
            )
        for m, f in enumerate(raw.get("forms", [])):
            row = rows[f"{n}.form.{m}"]
            const, cite_kind, key = f["const"], "const", f["const"]
            if "locale" in f:
                key = f"{f['locale']}.{const}"
                entry["kind"] = "locale_abbreviation"
            elif "parameter_of" in f:
                # A locale parameter has no entity of its own; it links to its locale.
                key, cite_kind = f["parameter_of"], "locale"
                entry["kind"] = "notation"
            else:
                named = f.get("named", False)
                if named and row["notation"]:
                    raise NotationError(
                        f"{const}: marked `named` in the manifest, but it declares the "
                        f'mixfix "{row["notation"]}" at {row["path"]}:{row["line"]}'
                    )
                if (
                    not named
                    and "class" not in f
                    and "record" not in f
                    and not row["notation"]
                ):
                    raise NotationError(
                        f"{const}: its declaration has no mixfix at {row['path']}:{row['line']}"
                    )
                entry["kind"] = "named" if named else "notation"
            entry["forms"].append(
                form_record(_decl(row), const, key, row["symbol"], row, cite_kind)
            )
        if "local" in raw:
            loc = raw["local"]
            row = rows[f"{n}.local"]
            decl = _decl(row)
            head = decl.get("expands", "").split()[0] if decl.get("expands") else ""
            if head != entry["forms"][0]["const"]:
                raise NotationError(
                    f"{loc['locale']}.{loc['const']}: abbreviates {head}, "
                    f"not {entry['forms'][0]['const']} ({decl['site']})"
                )
            rec = form_record(
                decl,
                loc["const"],
                f"{loc['locale']}.{loc['const']}",
                row["symbol"],
                row,
            )
            rec["shorthand_for"] = entry["forms"][0]["const"]
            entry["local"] = rec
        entry["id"] = entry["forms"][0]["cite"]["name"]
        if entry["group"] == "shorthand" and entry["kind"] != "locale_abbreviation":
            raise NotationError(
                f"{entry['id']}: a shorthand must be a locale abbreviation"
            )
        entries.append(entry)

    forms = [
        f for e in entries for f in e["forms"] + ([e["local"]] if e["local"] else [])
    ]
    cites = list(
        dict.fromkeys(
            [(f["cite"]["kind"], f["cite"]["name"]) for f in forms]
            + [("locale", f["scope"]) for f in forms if f["scope"] != "global"]
        )
    )
    data = {
        "source": MANIFEST.relative_to(REPO).as_posix(),
        "base": site_base(),
        "groups": groups,
        "entries": entries,
        "citations": [{"kind": k, "name": n} for k, n in cites],
    }
    return data


# ------------------------------------------------------------- rendering


def _symbol_table() -> dict[str, str]:
    table = {}
    for m in re.finditer(r'^\s*"([^"]+)": "([^"]*)",$', SYMBOLS.read_text(), re.M):
        table[m[1]] = m[2]
    return table


SYMS = _symbol_table()
ISA_TOKEN = re.compile(r"\\<\^(bsub|esub|sub|sup)>|\\<([A-Za-z0-9]+)>|(.)", re.S)


def isa_html(s: str, md: bool = False) -> str:
    """Isabelle ASCII as HTML: glyphs from Isabelle's table, real sub/superscripts."""
    out, script = [], None
    for m in ISA_TOKEN.finditer(s):
        if m[1] == "bsub":
            out.append("<sub>")
            continue
        if m[1] == "esub":
            out.append("</sub>")
            continue
        if m[1] in ("sub", "sup"):
            script = m[1]
            out.append(f"<{script}>")
            continue
        text = SYMS.get(m[2], m[0]) if m[2] else m[3]
        text = html.escape(text, quote=False)
        if md:
            text = (
                text.replace("*", "&#42;").replace("|", "&#124;").replace("_", "&#95;")
            )
        out.append(text)
        if script:
            out.append(f"</{script}>")
            script = None
    return re.sub(r"</(sub|sup)><\1>", "", "".join(out))


PROSE = re.compile(r"\{([^}]*)\}|_([^_]+)_")


def prose_html(s: str, md: bool = False) -> str:
    out, pos = [], 0
    for m in PROSE.finditer(s):
        plain = html.escape(s[pos : m.start()], quote=False)
        out.append(plain.replace("|", "&#124;") if md else plain)
        if m[1] is not None:
            out.append(isa_html(m[1], md))
        else:
            out.append(f"_{m[2]}_" if md else f"<em>{html.escape(m[2])}</em>")
        pos = m.end()
    tail = html.escape(s[pos:], quote=False)
    out.append(tail.replace("|", "&#124;") if md else tail)
    return "".join(out)


def symbols_of(entry: dict, md: bool) -> str:
    return " / ".join(isa_html(f["symbol"], md) for f in entry["forms"])


def within(entry: dict, locale: str, sym: str) -> str:
    """The locale form of a set, worded the same in every renderer."""
    if entry["kind"] == "named":
        return (
            f"{sym} exists only where a locale fixes its environment: within {locale}"
        )
    return f"Within {locale}, the fixed parameters are omitted: {sym}"


def render_readme(data: dict) -> str:
    base = data["base"]

    def link(f, text=None):
        return f"[`{text or f['const']}`]({base}{f['href']})"

    lines = [
        "<!-- notation:begin -->",
        "<!-- Generated by thesis/tools/notation.py from thesis/shared/notation.toml. -->",
        "",
        "Theorem statements use a few symbols the theories declare. Each name links to "
        "its declaration.",
        "",
        "| Symbol | Reads as | Isabelle | Meaning |",
        "| --- | --- | --- | --- |",
    ]
    for e in data["entries"]:
        if e["group"] == "shorthand":
            # A shorthand is a row of its own: the abbreviation, what it stands
            # for and the locale it is declared in.
            for f in e["forms"]:
                mode = "" if f["pretty_printed"] else ", input only"
                lines.append(
                    f"| {isa_html(f['symbol'], True)}<br>In `{f['scope']}`{mode}, short for "
                    f"{isa_html(f['expands'], True)} | {prose_html(e['reads'], True)} | "
                    f"{link(f)} | {prose_html(e['meaning'], True)} |"
                )
            continue
        sym = symbols_of(e, True)
        if e["local"]:
            loc = e["local"]
            sym += "<br>" + within(
                e, f"`{loc['scope']}`", isa_html(loc["symbol"], True)
            )
        lines.append(
            f"| {sym} | {prose_html(e['reads'], True)} | "
            f"{' / '.join(link(f) for f in e['forms'])} | {prose_html(e['meaning'], True)} |"
        )
    lines += ["", "<!-- notation:end -->"]
    return "\n".join(lines)


def render_page(data: dict) -> str:
    def a(href, text):
        return f'<a href="{html.escape(href)}"><code>{html.escape(text)}</code></a>'

    rows = []
    for e in data["entries"]:
        if e["group"] == "shorthand":
            continue
        sym = symbols_of(e, False)
        if e["local"]:
            loc = e["local"]
            locale = a(loc["scope_href"], loc["scope"])
            short = (
                f'<a href="{html.escape(loc["href"])}">{isa_html(loc["symbol"])}</a>'
            )
            sym += f'<span class="nl-local">{within(e, locale, short)}</span>'
        consts = " ".join(a(f["href"], f["const"]) for f in e["forms"])
        rows.append(
            f'          <tr><td class="nl-sym">{sym}</td>'
            f"<td>{prose_html(e['reads'])}</td><td>{consts}</td></tr>"
        )
    return "\n".join(
        [
            "      <!-- notation:begin -->",
            "      <!-- Generated by thesis/tools/notation.py from thesis/shared/notation.toml. -->",
            '      <details class="notation-legend">',
            "        <summary>How to read the theorem statements</summary>",
            '        <table class="notation-table">',
            "          <thead><tr><th>Symbol</th><th>Reads as</th><th>In the theories</th></tr></thead>",
            "          <tbody>",
            *rows,
            "          </tbody>",
            "        </table>",
            '        <p class="notation-note">Each name links to its declaration. The '
            '<a href="https://github.com/ManuelLerchner/Voblint-Verification-Master-Thesis#notation">'
            "README's notation table</a> also gives the meaning of every symbol and the "
            "proof-local shorthands.</p>",
            "      </details>",
            "      <!-- notation:end -->",
        ]
    )


BLOCK = re.compile(r"[ \t]*<!-- notation:begin -->.*?<!-- notation:end -->", re.S)


def splice(path: Path, block: str) -> str:
    text = path.read_text()
    if len(BLOCK.findall(text)) != 1:
        raise NotationError(
            f"{path.relative_to(REPO)}: expected one <!-- notation:begin --> ... "
            "<!-- notation:end --> block"
        )
    return BLOCK.sub(lambda _: block, text)


def render_json(data: dict) -> str:
    return json.dumps(data, indent=2, ensure_ascii=False) + "\n"


def main() -> int:
    ap = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    mode = ap.add_mutually_exclusive_group(required=True)
    mode.add_argument("--write", action="store_true")
    mode.add_argument("--check", action="store_true")
    ap.add_argument(
        "--lenient",
        action="store_true",
        help="without build/isabelle-html, accept the links the sources determine",
    )
    args = ap.parse_args()
    try:
        data = build(tomllib.loads(MANIFEST.read_text()), args.lenient)
        outputs = {
            OUT: render_json(data),
            README: splice(README, render_readme(data)),
            PAGE: splice(PAGE, render_page(data)),
        }
    except NotationError as err:
        print(f"notation: {err}", file=sys.stderr)
        return 1
    if args.write:
        for path, text in outputs.items():
            if not path.is_file() or path.read_text() != text:
                path.write_text(text)
                print(f"notation: wrote {path.relative_to(REPO)}")
        return 0
    stale = [p for p, t in outputs.items() if not p.is_file() or p.read_text() != t]
    if stale:
        names = ", ".join(str(p.relative_to(REPO)) for p in stale)
        print(
            f"notation: stale against the theories and {MANIFEST.relative_to(REPO)}: "
            f"{names}; run pixi run thesis-notation-write",
            file=sys.stderr,
        )
        return 1
    n = sum(len(e["forms"]) + bool(e["local"]) for e in data["entries"])
    print(f"notation: {n} declaration(s) match the theories and their anchors")
    return 0


if __name__ == "__main__":
    sys.exit(main())
