"""The appendix's Goblint comparison is read from the explainer's alignment rows."""

import importlib.util
import json
from pathlib import Path

import pytest

REPO = Path(__file__).resolve().parent.parent
REV = "5320a6b741e50dc049f7a1b85e1709e9565cc54a"


@pytest.fixture(scope="module")
def tool():
    spec = importlib.util.spec_from_file_location(
        "goblint_alignment", REPO / "thesis/tools/goblint_alignment.py"
    )
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


def row(status="modeled", voblint=None, note="A note.", rev=REV):
    voblint = voblint or (
        '<a class="align-voblint" '
        'href="Voblint/Voblint_Framework/DG_Spec.html#DG_Spec.dg_spec%7Ctype">'
        "dg_spec</a>"
    )
    return f"""
      <li class="align-row {status}">
        <a class="align-goblint" href="https://github.com/goblint/analyzer/blob/{rev}/src/framework/analyses.ml#L1-L2">Spec</a>
        <span class="align-link" aria-label="{status}"><span>{status}</span></span>
        {voblint}
        <span class="align-note">{note}</span>
      </li>"""


def page(*rows):
    return '<img src="logo.svg"><ul class="align-list">' + "".join(rows) + "</ul><br>"


def test_row_fields_and_entity_citation(tool):
    data = tool.extract(page(row(note="Spec&#x27;s  startstate\n  is absent.")))
    assert data["revision"] == REV
    [r] = data["rows"]
    assert r["status"] == "modeled"
    assert r["goblint"]["name"] == "Spec"
    assert r["goblint"]["file"] == "src/framework/analyses.ml"
    assert r["voblint"] == {
        "label": "dg_spec",
        "refs": [{"kind": "type", "name": "dg_spec"}],
    }
    assert r["note"] == "Spec's startstate is absent."
    assert data["citations"] == [{"kind": "type", "name": "dg_spec"}]


def test_nested_links_theory_pages_and_plain_text(tool):
    both = (
        '<span class="align-voblint">'
        '<a href="V/S/DG_Spec.html#DG_Spec.dg_spec.dgs_combine_env%7Cconst">env</a>'
        ' / <a href="V/S/DG_Spec.html#DG_Spec.dg_spec.dgs_combine_assign%7Cconst">'
        "assign</a></span>"
    )
    theory = (
        '<a class="align-voblint" href="Voblint/Voblint_VIMP/VIMP_Proc.html">VIMP</a>'
    )
    plain = '<span class="align-voblint">none</span>'
    data = tool.extract(
        page(row("simplified", both), row("absent", theory), row("absent", plain))
    )
    refs = [r["voblint"]["refs"] for r in data["rows"]]
    assert refs == [
        [
            {"kind": "const", "name": "dgs_combine_env"},
            {"kind": "const", "name": "dgs_combine_assign"},
        ],
        [{"kind": "theory", "name": "Voblint_VIMP.VIMP_Proc"}],
        [],
    ]
    assert data["rows"][0]["voblint"]["label"] == "env / assign"


@pytest.mark.parametrize(
    "html, message",
    [
        (page(row(status="partial")), "no single status"),
        (page(row(rev="master")), "not pinned"),
        (page(row(), row(rev="0" * 40)), "several commits"),
        (page(row(note="")), "empty note"),
        (page(), "no rows"),
        ("<p>nothing</p>", "expected one"),
        (
            page(
                row(
                    voblint='<a class="align-voblint" href="V/S/T.html#T.f%7Cclass">f</a>'
                )
            ),
            "unsupported anchor kind",
        ),
    ],
)
def test_malformed_rows_are_rejected(tool, html, message):
    with pytest.raises(tool.AlignmentError, match=message):
        tool.extract(html)


def test_generated_data_matches_the_page(tool):
    """The committed JSON is what the page currently yields."""
    current = tool.extract(tool.PAGE.read_text())
    assert json.loads(tool.OUT.read_text()) == current
