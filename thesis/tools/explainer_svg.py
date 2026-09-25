#!/usr/bin/env python3
"""Lift explanatory SVGs out of the explainer page into thesis assets.

``pages/index.html`` carries 39 inline ``<svg>`` figures that already explain
this development; the thesis needs the same pictures, static and in print
colours.  This tool copies them.  It never writes to ``pages/``.

Three things make the copy non-trivial, and each is why this is a program
rather than a shell pipeline:

*Selection.*  No ``<svg>`` in the page carries an ``id``, and several share a
class, so neither is a stable handle on its own.  A figure is named here by a
prefix of its ``aria-label`` -- written for screen readers, semantic, and not
renamed casually -- or by a class where that class occurs once.  Either way the
selector must match exactly one element; zero and two are both errors.

*Styling.*  The extracted markup is nearly colourless: across all 39 blocks
there are seven ``fill``/``stroke`` attributes.  Everything else comes from
``pages/style.css`` and ``pages/figures/<name>.css`` through class names, and
from CSS custom properties declared on ``:root``.  A raw copy is therefore a
black-on-black figure.  This tool inlines the rules that actually apply, with
``var(...)`` already resolved, so the result is a self-contained SVG.

*Colour.*  The page's palette is named for interface roles -- ``--primary``,
``--danger``, ``--caution``.  The thesis names colours for what they mean about
a proof (``proved``, ``trusted``, ``unproved``) and for domain identity.
Copying the web palette would carry styling that means nothing here and that
collapses in greyscale.  ``VAR_MAP``, ``LITERAL_MAP`` and ``STRATA_MAP`` below are the whole
mapping; nothing else in this file names a colour.

Usage::

    python3 thesis/tools/explainer_svg.py            # write every figure
    python3 thesis/tools/explainer_svg.py --check    # fail on any drift
    python3 thesis/tools/explainer_svg.py bridge     # one figure by name
"""

from __future__ import annotations

import argparse
import re
import sys
from dataclasses import dataclass
from pathlib import Path

import tomllib

REPO = Path(__file__).resolve().parents[2]
PAGE = REPO / "pages" / "index.html"
SITE_CSS = REPO / "pages" / "style.css"
FIGURE_CSS_DIR = REPO / "pages" / "figures"
MANIFEST = REPO / "thesis" / "shared" / "explainer-figures.toml"
OUT_DIR = REPO / "thesis" / "shared" / "generated" / "svg"


# --------------------------------------------------------------------------
# The colour map.  One table, applied to every figure.
# --------------------------------------------------------------------------
#
# Left: what the page says.  Right: a thesis colour from thesis/lib/theme.typ.
# Two rules govern the choices.
#
#   * A web colour that carries proof-relevant meaning keeps that meaning:
#     `--success` marks something established, `--danger` something outside the
#     boundary, `--caution` something assumed.  These become the thesis's
#     proved / unproved / trusted, so a reader who has seen the pipeline figure
#     reads every later figure the same way.
#   * A web colour that is only interface chrome -- surfaces, borders, hover
#     tints -- maps to a neutral grey.  Preserving the site's teal-and-orange
#     identity inside a printed thesis would assert a distinction that is not
#     there.
#
# Greyscale is checked by luminance: the five semantic colours below land at
# roughly 30%, 42%, 35%, 25% and 55% relative luminance, so they stay
# distinguishable when a printer drops the hue.

THEME = {
    # thesis/lib/theme.typ, verbatim
    "proved": "#2E7D32",
    "trusted": "#B26A00",
    "unproved": "#B3261E",
    "neutral": "#37474F",
    "accent": "#1565C0",
    "muted": "#78909C",
    "stable": "#2E7D32",
    "unstable": "#EF6C00",
    "fresh": "#FFFFFF",
    "called": "#5E35B1",
    "frame": "#CFD8DC",
    "bg": "#FAFAFA",
    "sign": "#00695C",
    "ivl": "#1565C0",
    "par": "#6A1B9A",
    "cong": "#AD1457",
}


# Light tints, for the soft background variants.  The page distinguishes five
# of them by hue and uses them as fills behind a stroke of the matching strong
# colour, so collapsing them all to one near-white erases the pairing.
TINT = {
    "accent-tint": "#E3F0FB",
    "orange-tint": "#FDEEE3",
    "proved-tint": "#E6F3E7",
    "unproved-tint": "#FBEAE8",
    "called-tint": "#EFE9F7",
}

# CSS custom property -> thesis colour name.
#
# The distinction that matters here is *content* versus *chrome*.  The page's
# `--primary` is not its text colour: figures use it for node strokes, titles
# and the object under discussion, so mapping it to a grey turned five figures
# monochrome.  It is the figures' main colour and maps to the thesis's main
# colour.  `--text*` and `--border*` really are chrome and stay grey.
VAR_MAP = {
    "--primary": "accent",
    "--primary-hover": "accent",
    "--primary-soft": "accent-tint",
    "--accent": "unstable",
    "--accent-hover": "unstable",
    "--accent-soft": "orange-tint",
    "--success": "proved",
    "--success-soft": "proved-tint",
    "--danger": "unproved",
    "--danger-soft": "unproved-tint",
    "--caution": "trusted",
    "--warning": "called",
    "--warning-soft": "called-tint",
    "--text": "neutral",
    "--text-muted": "muted",
    "--text-faint": "muted",
    "--border": "frame",
    "--border-strong": "muted",
    "--bg": "bg",
    "--paper": "bg",
    "--surface": "fresh",
    "--surface-muted": "bg",
    "--surface-hover": "bg",
    "--surface-dark": "neutral",
    "--surface-dark-2": "neutral",
    "--editor-text": "neutral",
    "--editor-border": "frame",
    # The metro map gives each session of the development its own line colour.
    # That is identity, not chrome, so each keeps a distinct thesis hue rather
    # than collapsing to neutral; the six are chosen for greyscale separation.
    "--line-sem": "neutral",
    "--line-comp": "unstable",
    "--line-dom": "par",
    "--line-fw": "sign",
    "--line-sol": "trusted",
    "--line-res": "accent",
}

# The cross-section figure draws the development as rock strata, and its
# palette is already an ordered warm-to-cool ramp: browns at the bottom through
# tans and sage to pale blue at the top, with a dark bedrock beneath.  That is
# the figure's content -- the geological metaphor its caption names -- not site
# chrome, and the ramp is ordered by lightness, so it survives greyscale on its
# own.  An earlier version replaced it with a blue-grey ramp of the thesis
# palette; that threw away the metaphor and made the figure look like a generic
# layer diagram.  The original values pass through unchanged.
STRATA_MAP = {
    "--strata-bedrock": "#5B5048",
    "--strata-d1": "#8A6D52",
    "--strata-d2": "#A47D58",
    "--strata-d3": "#B98F63",
    "--strata-d4": "#C9A57A",
    "--strata-d5": "#B7AD85",
    "--strata-d6": "#9FAE8B",
    "--strata-d7": "#7FA38F",
    "--strata-d8": "#8FB3B0",
    "--strata-d9": "#A9C4C9",
    "--strata-d10": "#C4D6D8",
    "--strata-d11": "#D9C8A2",
    "--strata-examples": "#7E9B5F",
}

# Custom properties that carry no colour.  Listed so the colour pass leaves
# them alone instead of reporting them as an unmapped palette entry.
NON_COLOUR_VARS = {
    "--mono",
    "--radius",
    "--radius-sm",
    "--radius-lg",
    "--shadow",
    "--shadow-hover",
}

# Literal colours that appear as attributes or in figure CSS.  Only those that
# survive into an extracted figure need an entry; anything unmapped is passed
# through and reported by --check so the omission is visible rather than silent.
LITERAL_MAP = {
    "#cfdcdf": "frame",
    "#9db3b8": "muted",
    "#f9ece7": "bg",
    "#f3d3c7": "frame",
    "#d7e7ea": "frame",
    "#a9c6cc": "muted",
    "#6f949b": "muted",
    # Figure-local hues that never went through a custom property.
    "#3f6fb0": "accent",
    "#8a5fb0": "par",
    "#9b87d6": "called",
    "#7fa3aa": "muted",
    # Soft tints used as figure backgrounds, each behind a stroke of its own
    # strong colour.  Keeping the pairing is what makes the fill mean anything.
    "#e9f0fa": "accent-tint",
    "#eef2f3": "bg",
    "#f4eef6": "called-tint",
    "#fbeee9": "orange-tint",
    # Remaining figure-local literals: two muted teals, a near-black, a light
    # blue fill, an amber, and two cream tints.
    "#4f6f75": "muted",
    "#4f7c85": "muted",
    "#1c1a17": "neutral",
    "#8fb3d9": "frame",
    "#d99a2b": "trusted",
    "#fdf8f0": "bg",
    "#fffbea": "bg",
    # Hex forms of the page's rgb(... / alpha) tints, after flatten_rgb: the
    # site teal (its primary), and the dark stroke between strata.
    "#174b57": "accent",
    "#281e14": "neutral",
}

# Colours this tool produces.  Without them the literal pass re-examines its
# own output and reports every thesis colour as unmapped.
THEME.update(TINT)

EMITTED = (
    {v.lower() for v in THEME.values()}
    | {v.upper() for v in THEME.values()}
    | {v.lower() for v in STRATA_MAP.values()}
    | {v.upper() for v in STRATA_MAP.values()}
)

# Fonts: the page uses a display serif and the system mono.  A thesis figure
# should not introduce a third family, so both collapse onto the document's.
FONT_MAP = {
    "serif": '"New Computer Modern", "Latin Modern Roman", Georgia, serif',
    "mono": '"Isabelle DejaVu Sans Mono", "DejaVu Sans Mono", monospace',
}

# Declarations that mean nothing on a printed page.  Dropping them keeps the
# inlined stylesheet small enough to read in a diff.
DROP_PROPERTIES = {
    "transition",
    "animation",
    "animation-delay",
    "animation-duration",
    "animation-name",
    "animation-timing-function",
    "cursor",
    "pointer-events",
    "will-change",
    "user-select",
    "-webkit-user-select",
    "backdrop-filter",
    "box-shadow",
    "scroll-behavior",
}

# Rules guarded by these never fire in a static frame.
DROP_SELECTOR_TOKENS = (
    ":hover",
    ":focus",
    ":active",
    ":focus-visible",
    "@media",
    "@keyframes",
    "@supports",
)


class ExtractError(RuntimeError):
    """A failure the caller must see; never recovered from silently."""


@dataclass(frozen=True)
class Figure:
    name: str
    out: str
    aria_prefix: str | None
    svg_class: str | None
    scene: str | None
    viewbox: str | None
    colours: tuple[tuple[str, str], ...]
    drop_classes: tuple[str, ...]
    css: tuple[str, ...]
    why: str
    chapter: str


# --------------------------------------------------------------------------
# Locating one <svg>
# --------------------------------------------------------------------------


def svg_blocks(html: str) -> list[tuple[int, str]]:
    """Every top-level ``<svg>...</svg>`` block, with its offset.

    Scanned rather than parsed: the page is HTML, the figures are inline SVG,
    and an HTML parser normalises attribute case and self-closing forms that
    the output should keep byte-identical to the source.
    """
    out: list[tuple[int, str]] = []
    i = 0
    while True:
        m = re.compile(r"<svg\b").search(html, i)
        if not m:
            return out
        start = m.start()
        depth, j = 0, start
        while j < len(html):
            if html.startswith("<svg", j):
                depth += 1
                j += 4
            elif html.startswith("</svg>", j):
                depth -= 1
                j += 6
                if depth == 0:
                    break
            else:
                j += 1
        if depth != 0:
            raise ExtractError(
                f"unterminated <svg> at offset {start}: the page is malformed"
            )
        out.append((start, html[start:j]))
        i = j


def enclosing_figure_classes(html: str, offset: int) -> set[str]:
    """Classes of the innermost ``<figure>`` still open at ``offset``."""
    opened = [m for m in re.finditer(r"<figure\b[^>]*>", html[:offset])]
    closed = html[:offset].count("</figure>")
    if len(opened) <= closed:
        return set()
    m = re.search(r'class="([^"]*)"', opened[-1].group(0))
    return set(m.group(1).split()) if m else set()


def select(fig: Figure, html: str, blocks: list[tuple[int, str]]) -> str:
    """The one block ``fig`` names.  Zero or several matches are both errors.

    ``scene`` narrows the search to the ``<figure>`` whose class it names, for
    a graph the page draws twice with the same label and class.
    """
    if fig.scene:
        blocks = [
            (o, b) for o, b in blocks if fig.scene in enclosing_figure_classes(html, o)
        ]
    if fig.aria_prefix:
        what = f'aria-label prefix "{fig.aria_prefix}"'
        hits = [
            b
            for _, b in blocks
            if (m := re.search(r'aria-label="([^"]*)"', b[: b.find(">") + 1]))
            and m.group(1).startswith(fig.aria_prefix)
        ]
    elif fig.svg_class:
        what = f'class "{fig.svg_class}"'
        hits = [
            b
            for _, b in blocks
            if (m := re.search(r'class="([^"]*)"', b[: b.find(">") + 1]))
            and fig.svg_class in m.group(1).split()
        ]
    else:
        raise ExtractError(
            f"[{fig.name}] manifest entry gives neither aria_prefix nor svg_class"
        )

    if not hits:
        raise ExtractError(
            f"[{fig.name}] no <svg> in {PAGE.relative_to(REPO)} matches {what}. "
            "The figure was renamed or removed; update the manifest deliberately."
        )
    if len(hits) > 1:
        raise ExtractError(
            f"[{fig.name}] {len(hits)} figures match {what}; a selector must be unique. "
            "Lengthen aria_prefix, or select by svg_class."
        )
    return hits[0]


# --------------------------------------------------------------------------
# Collecting the CSS that applies
# --------------------------------------------------------------------------


def root_vars(css: str) -> dict[str, str]:
    m = re.search(r":root\s*\{(.*?)\}", css, re.S)
    if not m:
        raise ExtractError(
            f"no :root block in {SITE_CSS.relative_to(REPO)}; cannot resolve var()"
        )
    return {
        k.strip(): v.strip()
        for k, v in re.findall(r"(--[A-Za-z0-9-]+)\s*:\s*([^;]+);", m.group(1))
    }


def strip_comments(css: str) -> str:
    return re.sub(r"/\*.*?\*/", "", css, flags=re.S)


def rules(css: str):
    """Top-level ``selector { body }`` pairs, skipping at-rules."""
    css = strip_comments(css)
    i = 0
    while i < len(css):
        brace = css.find("{", i)
        if brace == -1:
            return
        selector = css[i:brace].strip()
        depth, j = 1, brace + 1
        while j < len(css) and depth:
            if css[j] == "{":
                depth += 1
            elif css[j] == "}":
                depth -= 1
            j += 1
        body = css[brace + 1 : j - 1]
        if selector and not selector.startswith("@"):
            yield selector, body
        i = j


# `:not()` is the one CSS feature the target renderers do not implement.  Typst
# (resvg) and rsvg both ignore a rule whose selector carries it, which is worse
# than applying it: a figure loses the rule silently and its text lands at the
# default anchor.  The page uses it in one shape --- "style this element unless
# it sets the attribute itself" --- so the pseudo-class is stripped and the
# attribute it guards is promoted to an inline style on the elements that have
# it, where it beats the class rule exactly as the guard intended.
NOT_ATTR = re.compile(r":not\(\[([A-Za-z-]+)(?:=\"[^\"]*\")?\]\)")


def promote_guarded_attributes(markup: str, attrs: set[str]) -> str:
    """Move `attr="v"` into `style="attr: v"` for every attribute in `attrs`."""
    for attr in attrs:
        markup = re.sub(
            rf'(<\w+\b[^>]*?)\s{re.escape(attr)}="([^"]*)"',
            lambda m, a=attr: f'{m.group(1)} style="{a}: {m.group(2)}"',
            markup,
        )
    return markup


def rescope(selector: str, present: set[str]) -> str | None:
    """Re-root a page selector inside the extracted fragment.

    Rules are written against the page: ``.scene-bridge .bridge-pillars rect``
    scopes on an ancestor that does not come with the figure.  Leading
    compounds whose classes are absent are therefore dropped, and the rest is
    kept *intact* -- an earlier version kept only the rightmost compound, which
    silently discarded every rule ending in a bare element (``.bridge-pillars
    rect``, ``.bridge-pillars text``) and rendered those figures as black
    boxes with no labels.

    Returns ``None`` when a surviving compound names a class the figure does
    not have: that rule belongs to a different state or a different figure.
    """
    sel = re.sub(r":where\(([^)]*)\)", r"\1", selector)
    sel = NOT_ATTR.sub("", sel)
    sel = re.sub(r"\s*[>+~]\s*", " ", sel).strip()
    compounds = sel.split()
    if not compounds:
        return None

    def classes(c: str) -> set[str]:
        return set(re.findall(r"\.([A-Za-z0-9_-]+)", c))

    i = 0
    while i < len(compounds):
        cls = classes(compounds[i])
        if cls and cls.isdisjoint(present):
            i += 1  # an outside scope; drop it
            continue
        # A compound that names a present class together with an absent one
        # (`.stratum.is-current`) is a run-time state of this figure.
        if cls and not cls <= present:
            return None
        break
    kept = compounds[i:]
    if not kept:
        return None
    anchored = False
    for c in kept:
        cls = classes(c)
        if cls and not cls <= present:
            return None
        if cls:
            anchored = True
    # A rule must name at least one class this figure has.  Without that guard
    # the site's generic element rules (`rect`, `text`, `body`) all survive and
    # restyle the figure with page chrome.
    if not anchored:
        return None
    return " ".join(kept)


def classes_in(svg: str) -> set[str]:
    out: set[str] = set()
    for m in re.finditer(r'class="([^"]*)"', svg):
        out.update(m.group(1).split())
    return out


def applicable(
    css_text: str, present: set[str], guarded: set[str]
) -> list[tuple[str, str]]:
    keep = []
    for selector, body in rules(css_text):
        if any(tok in selector for tok in DROP_SELECTOR_TOKENS):
            continue
        guarded.update(NOT_ATTR.findall(selector))
        # Every matching part is kept, not just the first.  A rule written
        # `.call-links line, .call-links path { fill: none; ... }` otherwise
        # styles the lines and leaves the paths at their default black fill.
        parts = [
            r for part in selector.split(",") if (r := rescope(part.strip(), present))
        ]
        if parts:
            keep.append((", ".join(dict.fromkeys(parts)), body))
    return keep


# --------------------------------------------------------------------------
# Recolouring
# --------------------------------------------------------------------------


def recolour(
    text: str,
    variables: dict[str, str],
    unmapped: set[str],
    override: dict[str, str] | None = None,
) -> str:
    """Rewrite the site palette into the thesis one.

    Literals are resolved before custom properties, so the pass never inspects
    a colour it produced itself; ``EMITTED`` keeps that true for values a
    figure happens to share with the thesis palette.  ``override`` is a
    figure's own entries, for a colour whose meaning differs in that figure.
    """
    override = override or {}

    def lit_sub(m: re.Match[str]) -> str:
        value = m.group(0).lower()
        if value in override:
            return THEME[override[value]]
        if value in LITERAL_MAP:
            return THEME[LITERAL_MAP[value]]
        if value.upper() in EMITTED or value in EMITTED:
            return m.group(0)
        unmapped.add(value)
        return m.group(0)

    text = re.sub(r"#[0-9a-fA-F]{6}\b", lit_sub, text)

    def var_sub(m: re.Match[str]) -> str:
        name = m.group(1)
        if name in override:
            return THEME[override[name]]
        if name in VAR_MAP:
            return THEME[VAR_MAP[name]]
        if name in STRATA_MAP:
            return STRATA_MAP[name]
        if name in NON_COLOUR_VARS:
            return variables.get(name, m.group(0))
        unmapped.add(name)
        return variables.get(name, "currentColor")

    return re.sub(r"var\(\s*(--[A-Za-z0-9-]+)\s*(?:,[^)]*)?\)", var_sub, text)


# Typst's SVG renderer (usvg) parses neither CSS Color 4 `rgb(r g b / a)` nor
# an alpha channel inside a CSS declaration it inlines; it paints the element
# black instead.  Every functional colour therefore becomes a hex colour plus
# the matching `*-opacity`, and the hex then goes through the palette like any
# other literal.
_NUM = r"\s*([\d.]+%?)\s*"
FUNC_RGB = re.compile(rf"rgba?\({_NUM}[\s,]{_NUM}[\s,]{_NUM}(?:[/,]{_NUM})?\)", re.I)
OPACITY_OF = {
    "fill": "fill-opacity",
    "stroke": "stroke-opacity",
    "stop-color": "stop-opacity",
}


def _channel(v: str) -> int:
    return round(float(v[:-1]) * 2.55) if v.endswith("%") else round(float(v))


def _alpha(v: str | None) -> str | None:
    if v is None:
        return None
    a = float(v[:-1]) / 100 if v.endswith("%") else float(v)
    return None if a >= 1 else f"{a:g}"


def _hex(m: re.Match[str]) -> str:
    return "#" + "".join(f"{_channel(m[i]):02x}" for i in (1, 2, 3))


def flatten_rgb(text: str) -> str:
    """Rewrite functional colours as hex plus an opacity property."""

    def decl(m: re.Match[str]) -> str:
        prop, colour, imp = m["prop"], FUNC_RGB.match(m["val"]), m["imp"] or ""
        a = _alpha(colour[4])
        out = f"{prop}: {_hex(colour)}{imp}"
        if a is not None:
            out += f"; {OPACITY_OF[prop]}: {a}{imp}"
        return out

    text = re.sub(
        r"(?P<prop>fill|stroke|stop-color)\s*:\s*(?P<val>rgba?\([^)]*\))(?P<imp>\s*!important)?",
        decl,
        text,
    )

    def attr(m: re.Match[str]) -> str:
        prop, colour = m["prop"], FUNC_RGB.match(m["val"])
        a = _alpha(colour[4])
        out = f'{prop}="{_hex(colour)}"'
        if a is not None:
            out += f' {OPACITY_OF[prop]}="{a}"'
        return out

    return re.sub(
        r'(?P<prop>fill|stroke|stop-color)="(?P<val>rgba?\([^)]*\))"', attr, text
    )


UNRENDERABLE = re.compile(
    r"\b(rgba?|hsla?|hwb|lab|lch|oklab|oklch|color-mix|color)\(", re.I
)


def retype(body: str) -> str:
    body = re.sub(r'"Iowan Old Style"[^;]*?serif', FONT_MAP["serif"], body)
    body = re.sub(r"var\(--mono\)", FONT_MAP["mono"], body)
    return flatten_rgb(body)


def clean_body(body: str) -> str:
    out = []
    for decl in body.split(";"):
        if ":" not in decl:
            continue
        prop = decl.split(":", 1)[0].strip().lower()
        if prop in DROP_PROPERTIES:
            continue
        out.append(decl.strip())
    return "; ".join(out)


# --------------------------------------------------------------------------
# Building one standalone SVG
# --------------------------------------------------------------------------


def open_tag_end(svg: str) -> int:
    """Offset just past the root ``<svg ...>``, respecting quoted attributes.

    Several aria-labels describe a guard and therefore contain a literal ``>``
    (``assume i >= 5``).  Splitting on the first ``>`` truncates the open tag
    mid-attribute and produces markup no XML parser accepts.
    """
    quote = None
    for i, ch in enumerate(svg):
        if quote:
            if ch == quote:
                quote = None
        elif ch in "\"'":
            quote = ch
        elif ch == ">":
            return i + 1
    raise ExtractError("unterminated <svg> open tag")


DRAWABLE = re.compile(
    r"<(rect|path|circle|ellipse|line|polyline|polygon|text|image|use)\b"
)


def xml_safe(markup: str) -> str:
    """Escape ``<``, ``>`` and bare ``&`` inside quoted attribute values.

    The source is HTML, which tolerates a raw ``<`` in an attribute; XML, which
    is what an SVG renderer parses, does not.  Several aria-labels describe a
    guard (``assume i < 5``) and would otherwise abort the parse at the first
    one, with an error pointing at the wrong place.
    """
    out, i, in_tag, quote = [], 0, False, None
    while i < len(markup):
        ch = markup[i]
        if quote:
            if ch == quote:
                quote = None
                out.append(ch)
            elif ch == "<":
                out.append("&lt;")
            elif ch == ">":
                out.append("&gt;")
            elif ch == "&" and not re.match(
                r"&(#[0-9]+|#x[0-9a-fA-F]+|[a-zA-Z][a-zA-Z0-9]*);", markup[i:]
            ):
                out.append("&amp;")
            else:
                out.append(ch)
        elif in_tag:
            if ch in "\"'":
                quote = ch
            elif ch == ">":
                in_tag = False
            out.append(ch)
        else:
            if ch == "<":
                in_tag = True
            out.append(ch)
        i += 1
    return "".join(out)


def build(fig: Figure, html: str, site_css: str, unmapped: set[str]) -> str:
    svg = select(fig, html, svg_blocks(html))

    open_tag_end_ = open_tag_end(svg)
    open_tag = svg[:open_tag_end_]
    if "viewBox" not in open_tag:
        raise ExtractError(
            f"[{fig.name}] the selected <svg> has no viewBox, so it cannot be scaled in the thesis"
        )

    for cls in fig.drop_classes:
        # Remove an element the page shows only in another state.  Choosing
        # which frame the thesis prints is editorial, so it is recorded in the
        # manifest rather than decided here.
        before = svg
        svg = re.sub(
            rf'<(\w+)([^>]*\bclass="[^"]*\b{re.escape(cls)}\b[^"]*")[^>]*/>',
            "",
            svg,
        )
        svg = re.sub(
            rf'<(\w+)([^>]*\bclass="[^"]*\b{re.escape(cls)}\b[^"]*")[^>]*>.*?</\1>',
            "",
            svg,
            flags=re.S,
        )
        if svg == before:
            raise ExtractError(
                f'[{fig.name}] drop_classes names "{cls}", which no element carries; '
                "the figure changed, or the entry is a leftover"
            )

    open_tag_end_ = open_tag_end(svg)
    open_tag = svg[:open_tag_end_]
    if fig.viewbox:
        # Labels the page lets overflow its box would be clipped in print.
        open_tag = re.sub(r'viewBox="[^"]*"', f'viewBox="{fig.viewbox}"', open_tag)

    if not DRAWABLE.search(svg[open_tag_end_:]):
        raise ExtractError(
            f"[{fig.name}] the selected <svg> is an empty shell -- the page fills it from "
            f"pages/figures/*.js at run time, so there is nothing to extract statically. "
            "Capture it as a screenshot (scripts/capture_readme_figures.mjs) or redraw it, "
            "and drop the entry from the manifest."
        )

    present = classes_in(svg)

    sheets = [site_css]
    for name in fig.css:
        path = FIGURE_CSS_DIR / f"{name}.css"
        if not path.exists():
            raise ExtractError(f"[{fig.name}] no stylesheet {path.relative_to(REPO)}")
        sheets.append(path.read_text())

    variables = root_vars(site_css)
    guarded: set[str] = set()
    collected: list[str] = []
    seen: set[tuple[str, str]] = set()
    for sheet in sheets:
        for compound, body in applicable(sheet, present, guarded):
            body = clean_body(
                recolour(retype(body), variables, unmapped, dict(fig.colours))
            )
            if not body:
                continue
            key = (compound, body)
            if key in seen:
                continue
            seen.add(key)
            collected.append(f"  {compound} {{ {body}; }}")

    if not collected:
        raise ExtractError(
            f"[{fig.name}] no stylesheet rule applies to any class in the figure. "
            "Either `css` names the wrong module, or the figure's styling moved."
        )

    body_markup = recolour(
        retype(svg[open_tag_end_:]), variables, unmapped, dict(fig.colours)
    )
    if "xmlns=" not in open_tag:
        open_tag = open_tag[:-1] + ' xmlns="http://www.w3.org/2000/svg">'

    open_tag = xml_safe(open_tag)
    body_markup = promote_guarded_attributes(body_markup, guarded)
    body_markup, dropped = strip_linked_images(xml_safe(body_markup))

    # XML forbids "--" inside a comment, and manifest prose uses it freely.
    why = fig.why.replace("--", "\u2014")
    header = (
        f"<!-- Generated by thesis/tools/explainer_svg.py from pages/index.html.\n"
        f"     Figure: {fig.name}. Do not edit; edit the manifest or the page.\n"
        + (
            f"     {dropped} linked logo image(s) dropped: Typst cannot nest an SVG.\n"
            if dropped
            else ""
        )
        + f"     {why} -->\n"
    )
    style = "<style>\n" + "\n".join(collected) + "\n</style>\n"
    leftover = UNRENDERABLE.search(style + body_markup)
    if leftover:
        raise ExtractError(
            f"[{fig.name}] a colour function Typst cannot render survives: "
            f"{(style + body_markup)[leftover.start() : leftover.start() + 40]!r}"
        )

    return header + open_tag + "\n" + style + body_markup.lstrip("\n")


# --------------------------------------------------------------------------


LINKED_IMAGE = re.compile(
    r'<image\b[^>]*?\b(?:xlink:)?href="(?!https?:|data:|#)[^"]+"[^>]*?/?>', re.S
)


def strip_linked_images(markup: str) -> tuple[str, int]:
    """Remove images the figure links to by relative path.

    The two that occur are vendor logos, and both are SVG.  Typst refuses a
    linked SVG inside an SVG, and a brand mark is web identity rather than
    thesis content, so the element goes rather than the asset being copied
    alongside.  An anchor is left untouched: a print renderer ignores it.
    """
    out, n = LINKED_IMAGE.subn("", markup)
    return out, n


def load_manifest() -> list[Figure]:
    if not MANIFEST.exists():
        raise ExtractError(f"no manifest at {MANIFEST.relative_to(REPO)}")
    data = tomllib.loads(MANIFEST.read_text())
    figures = []
    for name, spec in data.get("figures", {}).items():
        figures.append(
            Figure(
                name=name,
                out=spec.get("out", f"{name}.svg"),
                aria_prefix=spec.get("aria_prefix"),
                svg_class=spec.get("svg_class"),
                scene=spec.get("scene"),
                viewbox=spec.get("viewbox"),
                colours=tuple(
                    (k.lower() if k.startswith("#") else k, v)
                    for k, v in spec.get("colours", {}).items()
                ),
                drop_classes=tuple(spec.get("drop_classes", ())),
                css=tuple(spec.get("css", ())),
                why=spec.get("why", ""),
                chapter=spec.get("chapter", ""),
            )
        )
    for fig in figures:
        bad = [v for _, v in fig.colours if v not in THEME]
        if bad:
            raise ExtractError(
                f"[{fig.name}] colours names {', '.join(bad)}, which is not a thesis colour"
            )
    if not figures:
        raise ExtractError("the manifest declares no figures")
    return figures


def main() -> int:
    ap = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    ap.add_argument("only", nargs="*", help="figure names; default is every figure")
    ap.add_argument(
        "--check", action="store_true", help="fail on drift instead of writing"
    )
    args = ap.parse_args()

    try:
        figures = load_manifest()
        if args.only:
            wanted = set(args.only)
            unknown = wanted - {f.name for f in figures}
            if unknown:
                raise ExtractError(f"not in the manifest: {', '.join(sorted(unknown))}")
            figures = [f for f in figures if f.name in wanted]

        html = PAGE.read_text()
        site_css = SITE_CSS.read_text()
        OUT_DIR.mkdir(parents=True, exist_ok=True)

        unmapped: set[str] = set()
        stale, written = [], []
        for fig in figures:
            content = build(fig, html, site_css, unmapped)
            path = OUT_DIR / fig.out
            if args.check:
                if not path.exists() or path.read_text() != content:
                    stale.append(fig.name)
            else:
                path.write_text(content)
                written.append(fig.name)

        # An output whose manifest entry was removed would otherwise stay on
        # disk and keep rendering in the thesis, which is the failure this whole
        # tool exists to prevent.
        expected = {f.out for f in figures}
        if not args.only:
            orphans = sorted(
                p.name for p in OUT_DIR.glob("*.svg") if p.name not in expected
            )
            if orphans and args.check:
                stale.extend(f"{name} (no manifest entry)" for name in orphans)
            for name in orphans:
                if not args.check:
                    (OUT_DIR / name).unlink()
                    written.append(f"-{name}")
    except ExtractError as exc:
        print(f"explainer_svg: {exc}", file=sys.stderr)
        return 1

    if unmapped:
        print(
            "explainer_svg: no thesis colour for "
            + ", ".join(sorted(unmapped))
            + " -- add an entry to VAR_MAP or LITERAL_MAP",
            file=sys.stderr,
        )
        return 1

    if args.check:
        if stale:
            print(
                "explainer_svg: stale figures: "
                + ", ".join(stale)
                + "\n  run: python3 thesis/tools/explainer_svg.py",
                file=sys.stderr,
            )
            return 1
        print(f"explainer_svg: {len(figures)} figure(s) match pages/index.html")
        return 0

    print(
        f"explainer_svg: wrote {len(written)} figure(s) to {OUT_DIR.relative_to(REPO)}"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
