"""How abstract values read in every output voblint writes.

Each domain prints in Goblint's notation -- `1+3ℤ`, `[0,+∞]`, `⊤` -- but an
Isabelle string literal holds ASCII only, so the generated printers emit symbol
tokens such as `<int>` and the CLI decodes them once, on the answer run_voblint
returns. The `by eval` lemmas beside each printer pin the tokens; this pins
what a reader sees: the decoded glyphs, in every rendering, with no token
surviving into any of them.

Kept out of tests/regression/ for the reason test_html_report.py gives: none
of this is about what the analyzer proved.
"""

import re
import shutil
import subprocess
import xml.etree.ElementTree as ET
from pathlib import Path

import pytest

REPO_ROOT = Path(__file__).resolve().parent.parent
VOBLINT = REPO_ROOT / "cli" / "voblint"

# One variable per shape a printer distinguishes: a constant (c), an
# unconstrained value (t), a class with residue zero (e) and without (o), and a
# half-bounded interval (n, under the guard).
PROGRAM = """\
fun main() {
  n = __voblint_nondet_int();
  c = 5;
  t = n;
  e = 2 * n;
  o = 3 * n + 1;
  if (n >= 0) {
    __voblint_check(c > 0 && t == t && e == e && o == o && n >= 0);
  }
}
"""

TOKEN = re.compile(r"<(bottom|top|int|infinity|le|ge|and)>")


@pytest.fixture(scope="module")
def program(tmp_path_factory):
    if not VOBLINT.exists():
        pytest.skip("cli/voblint not built -- run `pixi run cli-build`")
    path = tmp_path_factory.mktemp("values") / "values.vimp"
    path.write_text(PROGRAM)
    return path


def _voblint(*args):
    proc = subprocess.run(
        [str(VOBLINT), *map(str, args)],
        capture_output=True,
        text=True,
        encoding="utf-8",
    )
    assert proc.returncode == 0, proc.stderr
    return proc.stdout


def _check_state(report):
    rows = [line for line in report.splitlines() if line.startswith("8:")]
    assert len(rows) == 1, report
    return rows[0].split("UNKNOWN", 1)[1].strip()


@pytest.mark.parametrize(
    "analysis, state",
    [
        ("sign", "c=+, t=⊤, e=⊤, o=⊤, n=≥0"),
        ("interval", "c=[5,5], t=⊤, e=⊤, o=⊤, n=[0,+∞]"),
        ("parity", "c=1+2ℤ, t=⊤, e=2ℤ, o=⊤, n=⊤"),
        ("congruence", "c=5, t=⊤, e=2ℤ, o=1+3ℤ, n=⊤"),
        (
            "int",
            "c=5, t=⊤, "
            "e=signs:⊤; intervals:[-∞,+∞]; parities:2ℤ; congruences:2ℤ, "
            "o=signs:⊤; intervals:[-∞,+∞]; parities:ℤ; congruences:1+3ℤ, "
            "n=signs:≥0; intervals:[0,+∞]; parities:ℤ; congruences:ℤ",
        ),
    ],
)
def test_report_shows_goblint_notation(program, analysis, state):
    """A standalone top is ⊤ and a product component's is ℤ or [-∞,+∞], as
    Goblint's integer-domain lifter and its tuple's components print them; a
    product every component agrees is one integer prints as that integer."""
    assert _check_state(_voblint("--analysis", analysis, program)) == state


@pytest.mark.parametrize(
    "analysis", ["sign", "interval", "parity", "congruence", "int"]
)
def test_no_symbol_token_survives_any_rendering(program, analysis, tmp_path):
    """Every output reads the one decoded answer, so a renderer that bypassed
    it would show up here as a raw token."""
    outputs = {
        "report": _voblint("--analysis", analysis, program),
        "dot": _voblint("--analysis", analysis, "--dot", program),
        "snapshot": _voblint("--analysis", analysis, "--graph-snapshot", program),
    }
    html = tmp_path / "html"
    _voblint("--analysis", analysis, "--html-out", html, program)
    for doc in (html / "nodes").glob("*.xml"):
        outputs[doc.name] = doc.read_text(encoding="utf-8")
    for name, text in outputs.items():
        assert not TOKEN.search(text), (
            f"{analysis} {name}: {TOKEN.search(text).group(0)}"
        )
    assert "⊤" in outputs["report"], outputs["report"]


def test_product_value_folds_into_named_components(program, tmp_path):
    """node.xsl folds a value holding a nested <map>, so a product value is
    split at its `; ` separators into one entry per component."""
    html = tmp_path / "html"
    _voblint("--analysis", "int", "--html-out", html, program)
    doc = next(
        d
        for d in (html / "nodes").glob("main_*.xml")
        if "check c &gt; 0" in d.read_text(encoding="utf-8")
    )
    root = ET.parse(doc).getroot()
    state = root.find("./call/path/analysis[@name='int']/value/map")
    keys = [k.text for k in state.findall("key")]
    values = state.findall("value")
    by_var = dict(zip(keys, values, strict=True))

    assert by_var["c"].text == "5"
    assert by_var["t"].text == "⊤"
    components = by_var["o"].find("map")
    assert components is not None, ET.tostring(by_var["o"], encoding="unicode")
    assert [k.text for k in components.findall("key")] == [
        "signs",
        "intervals",
        "parities",
        "congruences",
    ]
    assert [v.text for v in components.findall("value")] == [
        "⊤",
        "[-∞,+∞]",
        "ℤ",
        "1+3ℤ",
    ]


def test_xml_declares_utf8(program, tmp_path):
    """A report served as text/xml with no charset would otherwise be decoded
    by whatever default the server and browser agree on."""
    html = tmp_path / "html"
    _voblint("--analysis", "congruence", "--html-out", html, program)
    for doc in [html / "index.xml", *(html / "nodes").glob("*.xml")]:
        assert doc.read_text(encoding="utf-8").startswith(
            '<?xml version="1.0" encoding="UTF-8"?>'
        ), doc.name


@pytest.mark.skipif(shutil.which("dot") is None, reason="graphviz `dot` not on PATH")
def test_graphviz_keeps_the_glyphs(program):
    """Graphviz reads DOT as UTF-8 unless told otherwise; the drawing the
    report's graph pane shows must carry the same text as the tooltip."""
    dot = _voblint("--analysis", "congruence", "--dot", program)
    svg = subprocess.run(
        ["dot", "-Tsvg"],
        input=dot,
        capture_output=True,
        text=True,
        encoding="utf-8",
        check=True,
    ).stdout
    assert "o=1+3ℤ" in svg, svg[:2000]
