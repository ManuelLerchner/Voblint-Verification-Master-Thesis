#!/usr/bin/env python3
"""Lift the explainer's Goblint comparison into thesis data.

``pages/index.html`` carries the Goblint/Voblint comparison as the rows of
``ul.align-list``: a Goblint construct linked to its source at a pinned commit,
a status (modeled, simplified or absent), the Voblint counterpart linked to the
rendered theories, and a note. The thesis prints the same comparison as an
appendix table. Keeping one copy is the point: this tool reads the rows and
writes ``thesis/shared/generated/goblint-alignment.json``, and the appendix
renders that file. It never writes to ``pages/``.

A Voblint link becomes a formal citation. An entity anchor
(``#DG_Spec.dg_spec%7Ctype``) is cited by its kind and short name, and a bare
theory page by ``Session.Theory``; the file's ``citations`` list is what
``check_thesis_refs`` and ``check_thesis_links`` resolve, so a stale site link
fails the thesis checks as any hand-written citation would.

    python3 thesis/tools/goblint_alignment.py            # write
    python3 thesis/tools/goblint_alignment.py --check    # fail on drift
"""

from __future__ import annotations

import argparse
import json
import re
import sys
from html.parser import HTMLParser
from pathlib import Path
from urllib.parse import unquote

REPO = Path(__file__).resolve().parents[2]
PAGE = REPO / "pages" / "index.html"
OUT = REPO / "thesis" / "shared" / "generated" / "goblint-alignment.json"

STATUSES = ("modeled", "simplified", "absent")
# Isabelle's HTML anchor kind -> the thesis helper's kind.
ANCHOR_KINDS = {"const": "const", "type": "type", "locale": "locale", "fact": "thm"}
# HTML void elements never close, so they must not move the depth counter.
VOID = {
    "area",
    "base",
    "br",
    "col",
    "embed",
    "hr",
    "img",
    "input",
    "link",
    "meta",
    "source",
    "wbr",
}
PINNED = re.compile(
    r"^https://github\.com/goblint/analyzer/blob/(?P<rev>[0-9a-f]{40})/(?P<path>[^#]+)"
)


class AlignmentError(ValueError):
    pass


def citation(href: str) -> dict[str, str]:
    """The formal entity or theory a site link to the rendered theories names."""
    page, _, anchor = href.partition("#")
    path = Path(page)
    if path.suffix != ".html" or len(path.parts) < 2:
        raise AlignmentError(f"not a rendered-theory link: {href}")
    if not anchor:
        return {"kind": "theory", "name": f"{path.parent.name}.{path.stem}"}
    qualified, _, kind = unquote(anchor).partition("|")
    if kind not in ANCHOR_KINDS:
        raise AlignmentError(f"unsupported anchor kind {kind!r} in {href}")
    return {"kind": ANCHOR_KINDS[kind], "name": qualified.rsplit(".", 1)[-1]}


class _Rows(HTMLParser):
    """Collect ``li.align-row`` elements inside ``ul.align-list``."""

    def __init__(self) -> None:
        super().__init__(convert_charrefs=True)
        self.rows: list[dict] = []
        self.lists = 0
        self.row: dict | None = None
        # (cell name, depth at which the cell's element opened)
        self.cell: tuple[str, int] | None = None
        self.depth = 0

    def handle_starttag(self, tag: str, attrs: list[tuple[str, str | None]]) -> None:
        a = dict(attrs)
        classes = (a.get("class") or "").split()
        if tag in VOID:
            return
        self.depth += 1
        if tag == "ul" and "align-list" in classes:
            self.lists += 1
        elif tag == "li" and "align-row" in classes and self.lists:
            status = [c for c in classes if c in STATUSES]
            if len(status) != 1:
                raise AlignmentError(f"row with classes {classes} has no single status")
            self.row = {
                "status": status[0],
                "goblint": "",
                "goblint_url": "",
                "voblint": "",
                "refs": [],
                "note": "",
            }
        elif self.row is not None:
            for name in ("align-goblint", "align-voblint", "align-note"):
                if name in classes:
                    self.cell = (name.removeprefix("align-"), self.depth)
                    if name == "align-goblint":
                        self.row["goblint_url"] = a.get("href") or ""
            if tag == "a" and self.cell and self.cell[0] == "voblint":
                self.row["refs"].append(citation(a.get("href") or ""))

    def handle_endtag(self, tag: str) -> None:
        if tag in VOID:
            return
        if self.cell and self.depth == self.cell[1]:
            self.cell = None
        if tag == "li" and self.row is not None and self.cell is None:
            self.rows.append(self.row)
            self.row = None
        self.depth -= 1

    def handle_data(self, data: str) -> None:
        if self.row is not None and self.cell:
            self.row[self.cell[0]] += data


def _clean(text: str) -> str:
    return " ".join(text.split())


def extract(html: str) -> dict:
    parser = _Rows()
    parser.feed(html)
    if parser.lists != 1:
        raise AlignmentError(f"expected one ul.align-list, found {parser.lists}")
    if not parser.rows:
        raise AlignmentError("ul.align-list has no rows")
    rows, revisions, citations = [], set(), []
    for i, raw in enumerate(parser.rows, 1):
        m = PINNED.match(raw["goblint_url"])
        if not m:
            raise AlignmentError(
                f"row {i}: Goblint link is not pinned to a commit: {raw['goblint_url']!r}"
            )
        revisions.add(m["rev"])
        for field in ("goblint", "voblint", "note"):
            if not _clean(raw[field]):
                raise AlignmentError(f"row {i}: empty {field}")
        rows.append(
            {
                "status": raw["status"],
                "goblint": {
                    "name": _clean(raw["goblint"]),
                    "url": raw["goblint_url"],
                    "file": m["path"],
                },
                "voblint": {"label": _clean(raw["voblint"]), "refs": raw["refs"]},
                "note": _clean(raw["note"]),
            }
        )
        citations += [r for r in raw["refs"] if r not in citations]
    if len(revisions) != 1:
        raise AlignmentError(f"Goblint links pin several commits: {sorted(revisions)}")
    return {
        "source": PAGE.relative_to(REPO).as_posix(),
        "revision": revisions.pop(),
        "rows": rows,
        "citations": citations,
    }


def render(data: dict) -> str:
    return json.dumps(data, indent=2, ensure_ascii=False) + "\n"


def main() -> int:
    ap = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    ap.add_argument("--check", action="store_true", help="fail if the JSON is stale")
    args = ap.parse_args()
    try:
        text = render(extract(PAGE.read_text()))
    except AlignmentError as err:
        print(f"goblint_alignment: {err}", file=sys.stderr)
        return 1
    rel = OUT.relative_to(REPO)
    if args.check:
        if not OUT.is_file() or OUT.read_text() != text:
            print(
                f"goblint_alignment: {rel} is stale against pages/index.html; "
                "run pixi run thesis-alignment-write",
                file=sys.stderr,
            )
            return 1
        print(f"goblint_alignment: {rel} matches pages/index.html")
        return 0
    OUT.write_text(text)
    print(f"goblint_alignment: wrote {rel}")
    return 0


if __name__ == "__main__":
    sys.exit(main())
