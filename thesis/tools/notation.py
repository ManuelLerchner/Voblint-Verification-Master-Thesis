#!/usr/bin/env python3
"""Derive the notation table from the theories and render it in three places.

The table appears in appendix B of the thesis, in the README's Notation
section, and as the legend above the explainer's flagship theorems. Three
hand-written copies would drift from each other and from the theories, so
`thesis/shared/notation.toml` types only what cannot be read off a declaration
-- how to read a symbol and what it means -- and this tool derives the rest:

  * the symbol, from the declaration's mixfix and the manifest's argument names;
  * the theory, scope (global or the declaring locale) and print mode (an
    `abbreviation (input)` is never printed back);
  * a locale abbreviation's expansion, and which global set it abbreviates;
  * the rendered-theory link, from the anchor index `check_thesis_links` builds.

It recognizes only the declaration shapes the table uses: a mixfix on a
top-level `definition`/`fun`/`inductive`/`inductive_set`/`abbreviation`, a
mixfix or infix on a class parameter (also in the vendored solver), a mixfix on
a record field, a mixfix on a locale parameter, and an `abbreviation` inside a
named locale. Any other shape fails with the file and line instead of being
guessed at.

Output: `thesis/shared/generated/notation.json` (read by the appendix), and the
generated blocks between `notation:begin`/`notation:end` markers in README.md
and pages/index.html.

    thesis/tools/notation.py --write            regenerate all three
    thesis/tools/notation.py --check            fail on drift or a missing anchor
    thesis/tools/notation.py --check --lenient  without rendered theories, take
                                                links from links.json
"""

from __future__ import annotations

import argparse
import html
import json
import re
import sys
from pathlib import Path

import tomllib

REPO = Path(__file__).resolve().parents[2]
sys.path.insert(0, str(REPO / "scripts"))
sys.path.insert(0, str(Path(__file__).resolve().parent))
import check_thesis_links  # noqa: E402
from snippets import theory_files  # noqa: E402

MANIFEST = REPO / "thesis" / "shared" / "notation.toml"
OUT = REPO / "thesis" / "shared" / "generated" / "notation.json"
LINKS = REPO / "thesis" / "shared" / "generated" / "links.json"
SYMBOLS = REPO / "thesis" / "lib" / "isabelle-symbols.typ"
SITE_SCRIPT = REPO / "scripts" / "mk" / "pages-site.sh"
README = REPO / "README.md"
PAGE = REPO / "pages" / "index.html"
THESIS_APPENDIX = "appendix B"

GLOBAL_COMMANDS = "definition|fun|inductive|inductive_set|abbreviation"
TYPE = r'::\s*"[^"]*"'
# `("mixfix")` or `("mixfix" [51, 51] 50)`.
MIXFIX = r'\(\s*"([^"]*)"[^)"]*\)'
# `(infixl "sym" 65)`: the mixfix `_ sym _`.
INFIX = r'\(\s*infix[lr]?\s+"([^"]*)"\s*\d+\s*\)'


class NotationError(ValueError):
    pass


def where(path: Path, text: str, pos: int) -> str:
    return f"{path.relative_to(REPO)}:{text.count(chr(10), 0, pos) + 1}"


# ---------------------------------------------------------------- scopes


SCOPE_TOKEN = re.compile(
    r"^(?P<head>theory|locale|context|class|instantiation)\b(?P<rest>[^\n]*)"
    r"|^(?P<begin>begin)\b|(?P<endbegin>\bbegin)[ \t]*$|^(?P<end>end)\b",
    re.M,
)


def scope_at(text: str, pos: int) -> str:
    """The named locale or class a position lies in, or "global".

    Tracks `locale X ... begin`/`context X begin` blocks up to `pos`, and
    reports a header whose `begin` has not come yet (a class parameter sits
    there). An anonymous `context` reports "context", which no entry names.
    """
    stack: list[str] = []
    pending: str | None = None
    for m in SCOPE_TOKEN.finditer(text, 0, pos):
        if m["head"]:
            name = re.match(r"\s+([A-Za-z_][A-Za-z0-9_']*)", m["rest"])
            if m["head"] == "theory":
                pending = "global"
            elif m["head"] == "context" and (not name or name[1] == "begin"):
                pending = "context"
            else:
                pending = name[1] if name else m["head"]
            if re.search(r"\bbegin[ \t]*$", m["rest"]):
                stack.append(pending)
                pending = None
        elif m["begin"] or m["endbegin"]:
            stack.append(pending or "?")
            pending = None
        elif m["end"] and stack:
            stack.pop()
    if pending and pending != "global":
        return pending
    return stack[-1] if stack and stack[-1] != "global" else "global"


# ------------------------------------------------------- declarations


def _texts(vendor: bool = False) -> list[tuple[Path, str]]:
    files = theory_files()
    if not files:
        raise NotationError("no .thy files -- is vendor/td-verification checked out?")
    return [
        (p, p.read_text(errors="ignore"))
        for p in files
        if "/src/" in str(p) or (vendor and "/vendor/" in str(p))
    ]


def _mentions(name: str, texts) -> str:
    pat = re.compile(r"(?<![A-Za-z0-9_'.])" + re.escape(name) + r"\s*::")
    for path, text in texts:
        m = pat.search(text)
        if m:
            return f" (it is declared at {where(path, text, m.start())})"
    return ""


def find_global(name: str, texts, want_mixfix: bool) -> dict:
    """A top-level declaration of `name`, with its mixfix when it has one."""
    pat = re.compile(
        rf"^({GLOBAL_COMMANDS})(\s*\(input\))?\s+{re.escape(name)}\s*{TYPE}"
        rf"(?:\s*{MIXFIX})?",
        re.M,
    )
    hits = [(p, t, m) for p, t in texts for m in pat.finditer(t)]
    if not hits:
        raise NotationError(
            f"{name}: no top-level {GLOBAL_COMMANDS.replace('|', '/')} "
            f"declaration with a type{_mentions(name, texts)}"
        )
    if len(hits) > 1:
        sites = ", ".join(where(p, t, m.start()) for p, t, m in hits)
        raise NotationError(f"{name}: declared more than once: {sites}")
    path, text, m = hits[0]
    if scope_at(text, m.start()) != "global":
        raise NotationError(
            f"{name}: expected a top-level declaration, found one inside "
            f"{scope_at(text, m.start())} at {where(path, text, m.start())}"
        )
    if want_mixfix and m[3] is None:
        raise NotationError(
            f"{name}: its declaration has no mixfix at {where(path, text, m.start())}"
        )
    if not want_mixfix and m[3] is not None:
        raise NotationError(
            f"{name}: marked `named` in the manifest, but it declares the mixfix "
            f'"{m[3]}" at {where(path, text, m.start())}'
        )
    return {
        "declaration": m[1],
        "mixfix": m[3],
        "scope": "global",
        "pretty_printed": not m[2],
        "path": path,
        "text": text,
        "pos": m.start(),
    }


def find_class_param(name: str, cls: str, texts) -> dict:
    head = re.compile(rf"^class\s+{re.escape(cls)}\b", re.M)
    fix = re.compile(rf"\bfixes\s+{re.escape(name)}\s*{TYPE}\s*(?:{MIXFIX}|{INFIX})")
    for path, text in texts:
        h = head.search(text)
        if not h:
            continue
        nxt = re.compile(r"^\S", re.M).search(text, h.end())
        body_end = nxt.start() if nxt else len(text)
        m = fix.search(text, h.end(), body_end)
        if not m:
            raise NotationError(
                f"{name}: class {cls} at {where(path, text, h.start())} has no "
                f'`fixes {name} :: "..." ("...")` parameter'
            )
        return {
            "declaration": f"class {cls}",
            "mixfix": m[1] if m[1] is not None else f"_ {m[2]} _",
            "scope": "global",
            "pretty_printed": True,
            "path": path,
            "text": text,
            "pos": m.start(),
        }
    raise NotationError(f"{name}: no class {cls}")


def _block(text: str, start: int) -> int:
    """The end of the top-level command starting at `start`."""
    nxt = re.compile(r"^\S", re.M).search(text, text.index("\n", start) + 1)
    return nxt.start() if nxt else len(text)


def find_record_field(name: str, record: str, texts) -> dict:
    head = re.compile(
        rf"^record\s+(?:\([^)]*\)\s*|'\w+\s+)?{re.escape(record)}\s*=", re.M
    )
    field = re.compile(rf"^\s+{re.escape(name)}\s*{TYPE}\s*{MIXFIX}", re.M)
    for path, text in texts:
        h = head.search(text)
        if not h:
            continue
        m = field.search(text, h.end(), _block(text, h.start()))
        if not m:
            raise NotationError(
                f"{name}: record {record} at {where(path, text, h.start())} has no "
                f'field `{name} :: "..." ("...")`'
            )
        return {
            "declaration": f"record {record}",
            "mixfix": m[1],
            "scope": "global",
            "pretty_printed": True,
            "path": path,
            "text": text,
            "pos": m.start(),
        }
    raise NotationError(f"{name}: no record {record}")


def find_locale_param(name: str, locale: str, texts) -> dict:
    head = re.compile(rf"^locale\s+{re.escape(locale)}\s*=", re.M)
    param = re.compile(
        rf"\b(?:fixes|for|and)\s+{re.escape(name)}\s*(?:{TYPE}\s*)?{MIXFIX}"
    )
    for path, text in texts:
        h = head.search(text)
        if not h:
            continue
        m = param.search(text, h.end(), _block(text, h.start()))
        if not m:
            raise NotationError(
                f"{name}: locale {locale} at {where(path, text, h.start())} has no "
                f'parameter `{name} ("...")`'
            )
        return {
            "declaration": f"locale {locale}",
            "mixfix": m[1],
            "scope": locale,
            "pretty_printed": True,
            "path": path,
            "text": text,
            "pos": m.start(),
        }
    raise NotationError(f"{name}: no locale {locale}")


LOCAL_ABBREV = r"^[ \t]*abbreviation(\s*\(input\))?\s+{name}\b(?:\s*{type})?(?:\s*{mixfix})?\s*where\s*\"([^\"]*)\""


def find_local(name: str, locale: str, texts) -> dict:
    pat = re.compile(
        LOCAL_ABBREV.format(name=re.escape(name), type=TYPE, mixfix=MIXFIX), re.M
    )
    hits, elsewhere = [], []
    for path, text in texts:
        for m in pat.finditer(text):
            scope = scope_at(text, m.start())
            (hits if scope == locale else elsewhere).append((path, text, m, scope))
    if len(hits) != 1:
        found = ", ".join(f"{where(p, t, m.start())} ({s})" for p, t, m, s in elsewhere)
        raise NotationError(
            f"{locale}.{name}: expected one `abbreviation {name} ... where` in "
            f"locale {locale}, found {len(hits)}"
            + (f"; elsewhere: {found}" if found else "")
            + _mentions(name, texts)
        )
    path, text, m, _ = hits[0]
    lhs, sep, rhs = m[3].partition("\\<equiv>")
    if not sep:
        raise NotationError(
            f"{locale}.{name}: the abbreviation at {where(path, text, m.start())} "
            "is not written `lhs \\<equiv> rhs`"
        )
    return {
        "declaration": "abbreviation (input)" if m[1] else "abbreviation",
        "mixfix": m[2],
        "scope": locale,
        "pretty_printed": not m[1],
        "expands": " ".join(rhs.split()),
        "path": path,
        "text": text,
        "pos": m.start(),
    }


def check_binds(symbol: str, const: str, texts) -> None:
    decl = find_global(const, texts, want_mixfix=True)
    text, pos = decl["text"], decl["pos"]
    stop = re.compile(r"\bwhere\b").search(text, pos)
    head = text[pos : stop.start() if stop else len(text)]
    if not re.search(r"\bfor\s+" + re.escape(symbol) + r"(?![A-Za-z0-9_'])", head):
        raise NotationError(
            f"{const}: expected `for {symbol}` in its declaration at "
            f"{where(decl['path'], text, pos)}"
        )


# --------------------------------------------------------------- symbols


def fill(mixfix: str | None, name: str, args: list[str]) -> str:
    """The mixfix with its `_` slots filled, then the remaining arguments."""
    if mixfix is None:
        return " ".join([name, *args])
    out, rest, i = [], list(args), 0
    while i < len(mixfix):
        c = mixfix[i]
        if c == "'" and i + 1 < len(mixfix):
            out.append(mixfix[i + 1])
            i += 2
            continue
        if mixfix.startswith("\\<", i):
            j = mixfix.index(">", i) + 1
            out.append(mixfix[i:j])
            i = j
            continue
        if c == "(":
            i += 1
            while i < len(mixfix) and mixfix[i].isdigit():
                i += 1
            continue
        if c in ")/":
            i += 1
            continue
        if c == "_":
            if not rest:
                raise NotationError(f"{name}: fewer arguments than mixfix slots")
            out.append(rest.pop(0))
        else:
            out.append(c)
        i += 1
    return " ".join([" ".join("".join(out).split()), *rest])


# ------------------------------------------------------------------ links


def site_base() -> str:
    m = re.search(r'SITE_URL="\$\{SITE_URL:-([^}]+)\}"', SITE_SCRIPT.read_text())
    if not m:
        raise NotationError(f"no SITE_URL default in {SITE_SCRIPT.relative_to(REPO)}")
    return m[1].rstrip("/") + "/"


def links_json() -> dict:
    return json.loads(LINKS.read_text()) if LINKS.is_file() else {"links": {}}


def resolve_links(
    cites: list[tuple[str, str]], lenient: bool
) -> tuple[dict[tuple[str, str], str], list[str], list[str]]:
    """Each (kind, name)'s rendered-theory target, from the local HTML if built.

    With HTML, a citation without an anchor fails, and so does a links.json
    entry that disagrees (the thesis would link elsewhere than the README and
    site). Without HTML, `lenient` takes the stored links.json targets, which
    the deployed-site check verifies on main.
    """
    stored = links_json()["links"]
    html_dir = check_thesis_links.HTML
    problems, drift, found = [], [], {}
    if html_dir.is_dir() and any(html_dir.rglob("*.html")):
        index = check_thesis_links.index_anchors()
        for kind, name in cites:
            target = index.get((name, kind))
            if target is None:
                problems.append(
                    f"{kind} {name} has no anchor in {html_dir.relative_to(REPO)}"
                )
                continue
            found[kind, name] = target
            if stored.get(f"{kind}:{name}") != target:
                drift.append(
                    f"links.json has {stored.get(f'{kind}:{name}')!r} for {kind}:{name}, "
                    f"the rendered theories {target!r}; run pixi run thesis-links-write"
                )
        return found, problems, drift
    if not lenient:
        missing = (
            "no rendered theories under build/isabelle-html; build them with "
            "pixi run isabelle-html-build, or pass --lenient"
        )
        return found, [missing], drift
    print("notation: no rendered theories; anchors taken from links.json")
    for kind, name in cites:
        target = stored.get(f"{kind}:{name}")
        if target is None:
            problems.append(
                f"links.json has no {kind}:{name}; run pixi run thesis-links-write"
            )
        else:
            found[kind, name] = target
    return found, problems, drift


# ----------------------------------------------------------------- build


def form_record(
    decl: dict, const: str, key: str, symbol: str, kind: str = "const"
) -> dict:
    theory = decl["path"].stem
    rec = {
        "const": const,
        "cite": {"kind": kind, "name": key},
        "symbol": symbol,
        "mixfix": decl["mixfix"],
        "declaration": decl["declaration"],
        "scope": decl["scope"],
        "pretty_printed": decl["pretty_printed"],
        "theory": theory,
        "file": decl["path"].relative_to(REPO).as_posix(),
    }
    if "expands" in decl:
        rec["expands"] = decl["expands"]
    return rec


def build(manifest: dict, lenient: bool) -> tuple[dict, list[str]]:
    texts = _texts()
    solver_texts = _texts(vendor=True)
    groups = manifest["groups"]
    entries = []
    for n, raw in enumerate(manifest["entry"], 1):
        group = raw.get("group")
        if group not in groups:
            raise NotationError(f"entry {n}: unknown group {group!r}")
        entry = {
            "id": "",
            "group": group,
            "kind": "",
            "reads": raw["reads"],
            "meaning": raw["meaning"],
            "forms": [],
            "local": None,
        }
        if "symbol" in raw:
            for const in raw["bound_in"]:
                check_binds(raw["symbol"], const, texts)
            decl = find_global(raw["const"], texts, want_mixfix=False)
            decl["declaration"] = "variable convention"
            entry["kind"] = "convention"
            entry["forms"].append(
                form_record(decl, raw["const"], raw["const"], raw["symbol"])
            )
        for f in raw.get("forms", []):
            const, args = f["const"], f.get("args", [])
            cite_kind = "const"
            if "locale" in f:
                decl = find_local(const, f["locale"], texts)
                key = f"{f['locale']}.{const}"
                entry["kind"] = "locale_abbreviation"
            elif "parameter_of" in f:
                # A locale parameter has no entity of its own; it links to its locale.
                decl = find_locale_param(const, f["parameter_of"], texts)
                key, cite_kind = f["parameter_of"], "locale"
                entry["kind"] = "notation"
            elif "record" in f:
                decl = find_record_field(const, f["record"], texts)
                key = const
                entry["kind"] = "notation"
            elif "class" in f:
                decl = find_class_param(const, f["class"], solver_texts)
                key = const
                entry["kind"] = "notation"
            else:
                named = f.get("named", False)
                decl = find_global(const, texts, want_mixfix=not named)
                key = const
                entry["kind"] = "named" if named else "notation"
            entry["forms"].append(
                form_record(
                    decl, const, key, fill(decl["mixfix"], const, args), cite_kind
                )
            )
        if "local" in raw:
            loc = raw["local"]
            decl = find_local(loc["const"], loc["locale"], texts)
            head = decl["expands"].split()[0]
            if head != entry["forms"][0]["const"]:
                raise NotationError(
                    f"{loc['locale']}.{loc['const']}: abbreviates {head}, "
                    f"not {entry['forms'][0]['const']} "
                    f"({where(decl['path'], decl['text'], decl['pos'])})"
                )
            rec = form_record(
                decl,
                loc["const"],
                f"{loc['locale']}.{loc['const']}",
                fill(decl["mixfix"], loc["const"], loc.get("args", [])),
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
    links, problems, drift = resolve_links(cites, lenient)
    for f in forms:
        href = links.get((f["cite"]["kind"], f["cite"]["name"]))
        f["href"] = href
        if f["scope"] != "global":
            f["scope_href"] = links.get(("locale", f["scope"]))
        if href:
            page = href.split("#")[0]
            f["session"] = page.split("/")[-2]
            if Path(page).stem.split(".")[-1] != f["theory"]:
                problems.append(
                    f"{f['cite']['name']}: declared in {f['theory']}, "
                    f"but its anchor is on {page}"
                )
    data = {
        "source": MANIFEST.relative_to(REPO).as_posix(),
        "base": site_base(),
        "groups": groups,
        "entries": entries,
        "citations": [{"kind": k, "name": n} for k, n in cites],
    }
    return data, problems, drift


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
        "its declaration; the full table, with the print mode of each form, is "
        f"{THESIS_APPENDIX} of the [thesis]({base}thesis.pdf).",
        "",
        "| Symbol | Reads as | Isabelle | Meaning |",
        "| --- | --- | --- | --- |",
    ]
    for e in data["entries"]:
        if e["group"] == "shorthand":
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
    lines += [
        "",
        prose_html(data["groups"]["shorthand"]["note"], True),
        "",
        "| Shorthand | Stands for | Locale |",
        "| --- | --- | --- |",
    ]
    for e in data["entries"]:
        if e["group"] != "shorthand":
            continue
        for f in e["forms"]:
            mode = "" if f["pretty_printed"] else " (input only)"
            lines.append(
                f"| {link(f, f['symbol'])} | {isa_html(f['expands'], True)} | "
                f"`{f['scope']}`{mode} |"
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
            '        <p class="notation-note">Each name links to its declaration. '
            f'<a href="thesis.pdf">The thesis</a>, {THESIS_APPENDIX}, gives the meaning '
            "of every symbol and the proof-local shorthands.</p>",
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
        help="without build/isabelle-html, take anchors from links.json",
    )
    args = ap.parse_args()
    try:
        data, problems, drift = build(tomllib.loads(MANIFEST.read_text()), args.lenient)
        # The link map reads this file's citations, so on --write a new
        # citation is expected to be missing from it until thesis-links-write.
        if args.check:
            problems += drift
        elif drift:
            print(
                f"notation: {len(drift)} link(s) not yet in links.json; "
                "run pixi run thesis-links-write"
            )
        if problems:
            raise NotationError("\n  ".join(["unresolved links:", *problems]))
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
