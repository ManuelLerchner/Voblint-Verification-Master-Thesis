"""Structural regression for `voblint --html`.

The verdict report and the graph snapshot are already pinned elsewhere; what
this locks in is the shape of the emitted result directory, because that shape
is a contract with a frontend this repository does not own. g2html's
stylesheets match specific element names and attribute positions, so a
plausible-looking rename here renders as a blank pane rather than as a test
failure -- which is exactly the kind of break a fixture's verdict column
cannot catch.

Kept out of tests/regression/ deliberately: every case there asserts a check
verdict against concrete program semantics (see tests/run.py's module
docstring), and none of this is about what the analyzer proved.
"""

import re
import subprocess
import sys
import xml.etree.ElementTree as ET
from pathlib import Path

import pytest

REPO_ROOT = Path(__file__).resolve().parent.parent
VOBLINT = REPO_ROOT / "cli" / "voblint"

# One dead branch and one proved check, so both highlighting paths are covered
# by the same run.
FIXTURE = (
    REPO_ROOT
    / "tests/regression/06-reachability/precision/05-unreachable_dead_branch_literal.vimp"
)


@pytest.fixture(scope="module")
def report(tmp_path_factory):
    if not VOBLINT.exists():
        pytest.skip("cli/voblint not built -- run `pixi run cli-build`")
    out = tmp_path_factory.mktemp("result")
    proc = subprocess.run(
        [str(VOBLINT), "--analysis", "interval", "--html-out", str(out), str(FIXTURE)],
        capture_output=True,
        text=True,
    )
    assert proc.returncode == 0, proc.stderr
    return out


def test_directory_layout(report):
    """The paths g2html's stylesheets and script.js fetch by name."""
    seg = FIXTURE.name
    for rel in [
        "index.xml",
        "nodes/globals.xml",
        f"files/{seg}.xml",
        f"dot/{seg}/main.dot",
    ]:
        assert (report / rel).is_file(), f"missing {rel}"
    assert list((report / "nodes").glob("main_*.xml")), "no per-node documents"


def test_frontend_assets_copied(report):
    """Without these the directory is unbrowsable, however good the XML is."""
    for asset in ["report.xsl", "node.xsl", "file.xsl", "frame.html", "script.js"]:
        assert (report / asset).is_file(), f"missing frontend asset {asset}"


def test_index_names_the_function(report):
    root = ET.parse(report / "index.xml").getroot()
    assert root.tag == "report"
    files = root.findall("file")
    assert [f.get("name") for f in files] == [FIXTURE.name]
    assert [fn.get("name") for fn in files[0].findall("function")] == ["main"]


def test_node_document_shape(report):
    """node.xsl matches loc/call, and reads @id to link a node back to itself."""
    doc = next((report / "nodes").glob("main_*.xml"))
    text = doc.read_text()
    assert 'href="../node.xsl"' in text, "stylesheet instruction missing"
    root = ET.parse(doc).getroot()
    assert root.tag == "loc"
    call = root.find("call")
    assert call is not None
    assert call.get("id") == doc.stem
    # Display-only in node.xsl, but it reads them unconditionally.
    for attr in ["file", "fun", "line", "column", "endLine", "endColumn", "synthetic"]:
        assert call.get(attr) is not None, f"@{attr} missing"


def test_state_is_a_foldable_map_not_a_flat_string(report):
    """The whole point of the exercise: state lives here, structured, rather
    than inlined into a CFG node label."""
    docs = list((report / "nodes").glob("main_*.xml"))
    maps = []
    for doc in docs:
        analysis = ET.parse(doc).getroot().find("./call/path/analysis[@name='interval']")
        if analysis is not None:
            keys = analysis.findall("./value/map/key")
            if keys:
                maps.append([k.text for k in keys])
    assert maps, "no node carried an interval state"
    assert any("x" in keys for keys in maps), "expected variable x in some state"


def test_dead_and_proved_are_highlighted_in_the_dot(report):
    """The CFG pane has to show findings without being clicked through."""
    dot = (report / "dot" / FIXTURE.name / "main.dot").read_text()
    assert 'fillcolor="orange"' in dot, "unreachable node not highlighted"
    assert 'fillcolor="#cdebc5"' in dot, "proved check not highlighted"


def test_dot_carries_the_click_hooks(report):
    """Graphviz turns these into the <g id="a_N"><a xlink:href> that
    script.js selects on; without them the SVG is inert."""
    dot = (report / "dot" / FIXTURE.name / "main.dot").read_text()
    assert 'id="\\N"' in dot
    assert "URL=\"javascript:show_info('\\N');\"" in dot


def test_states_stay_out_of_node_labels(report):
    """A label carrying a state is the failure --dot-full has and this does
    not; it is what makes a product domain's graph unreadable."""
    dot = (report / "dot" / FIXTURE.name / "main.dot").read_text()
    for line in dot.splitlines():
        if "label=" in line and "->" not in line and "subgraph" not in line:
            assert "\\n" not in line, f"multi-line node label: {line.strip()}"


def test_source_view_has_exactly_the_files_lines(report):
    """A trailing newline ends the last line; it does not begin another one.
    An extra empty line renders as a numbered line that is not in the file."""
    src = next((report / "files").glob("*.xml"))
    lines = ET.parse(src).getroot().findall("ln")
    assert len(lines) == len(FIXTURE.read_text().splitlines())
    assert [int(ln.get("nr")) for ln in lines] == list(range(1, len(lines) + 1))


def test_source_view_is_syntax_highlighted(report):
    """file.xsl turns <sht type="X"> into <span class="sh X">, and its
    stylesheet only defines this palette -- an invented type renders
    unstyled."""
    src = next((report / "files").glob("*.xml"))
    text = src.read_text()
    assert "<sht " in text, "no highlighting spans emitted"
    types = set(re.findall(r'<sht type="([a-z]+)"', text))
    assert types, "no sht types"
    assert types <= {"nr", "pp", "tk", "sk", "op", "sp", "cm", "st"}, (
        f"types outside the frontend's palette: {types}"
    )
    assert "sk" in types, "expected a statement keyword (if/else/while)"
    assert "cm" in types, "expected a comment"


def test_checks_become_inline_source_annotations(report):
    """The finding a reader wants next to the code, not only in the graph."""
    warns = sorted((report / "warn").glob("warn*.xml"))
    assert warns, "no warning documents emitted"
    text = warns[0].read_text()
    assert 'href="../warn.xsl"' in text
    root = ET.parse(warns[0]).getroot()
    assert root.tag == "warning"
    piece = root.find("text")
    assert piece is not None
    assert int(piece.get("line")) > 0, "warning carries no source line"
    assert "Assertion" in piece.text

    # script.js builds ../warn/<entry>.xml from each wrn entry, so the entries
    # are quoted strings spliced into a JS array literal.
    src = next((report / "files").glob("*.xml")).read_text()
    assert 'wrn="[&quot;warn1&quot;]"' in src, "no line references warn1"


def test_warning_line_matches_the_check(report):
    """A banner on the wrong line is worse than no banner."""
    warns = sorted((report / "warn").glob("warn*.xml"))
    line = int(ET.parse(warns[0]).getroot().find("text").get("line"))
    source = FIXTURE.read_text().splitlines()
    assert "__voblint_check" in source[line - 1], (
        f"warn1 points at line {line}: {source[line - 1]!r}"
    )


def test_several_domains_land_in_one_node_document(tmp_path):
    """<analysis> is the element Goblint uses for exactly this, so several
    domains stack in one document rather than needing several reports."""
    if not VOBLINT.exists():
        pytest.skip("cli/voblint not built -- run `pixi run cli-build`")
    out = tmp_path / "multi"
    src = (
        REPO_ROOT / "tests/regression/16-composite-domain/precision"
        "/01-refinement_beats_components.vimp"
    )
    subprocess.run(
        [str(VOBLINT), "--analysis", "int,interval,sign", "--html-out", str(out), str(src)],
        capture_output=True, text=True, check=True,
    )
    # Every node carries one block per domain, in the order asked for. status
    # is separate and only present where there is a finding to report.
    for doc in (out / "nodes").glob("main_*.xml"):
        names = [
            a.get("name")
            for a in ET.parse(doc).getroot().findall("./call/path/analysis")
            if a.get("name") != "status"
        ]
        assert names == ["int", "interval", "sign"], (doc.name, names)

    # The verdicts differ between domains on this program -- int proves what
    # the others cannot, which is the whole reason to show them together.
    reported = [
        " ".join(v.text for v in status.iter("value") if v.text)
        for status in (
            ET.parse(doc).getroot().find("./call/path/analysis[@name='status']")
            for doc in (out / "nodes").glob("main_*.xml")
        )
        if status is not None
    ]
    joined = " ".join(reported)
    assert "int: PROVED" in joined, joined
    assert "interval: UNKNOWN" in joined, joined


def test_context_sensitive_report_draws_contexts_and_verdicts(tmp_path):
    """A context-sensitive run is asked for because the contexts matter, so
    the report must draw them apart rather than join them away -- and a check
    node must still carry its verdict once it does."""
    if not VOBLINT.exists():
        pytest.skip("cli/voblint not built -- run `pixi run cli-build`")
    out = tmp_path / "ctx"
    src = (
        REPO_ROOT / "tests/regression/03-procedures/precision"
        "/04-two_call_sites_entry_state.vimp"
    )
    subprocess.run(
        [str(VOBLINT), "--analysis", "interval", "--context", "entry-state",
         "--html-out", str(out), str(src)],
        capture_output=True, text=True, check=True,
    )
    dot = next((out / "dot").iterdir()).joinpath("main.dot").read_text()
    contexts = re.findall(r"subgraph (cluster_ctx_\d+)", dot)
    assert len(contexts) > 1, f"contexts joined away: {contexts}"
    assert 'fillcolor="#cdebc5"' in dot, "no proved check shaded"


def test_rerun_clears_the_previous_programs_nodes(tmp_path):
    """A stale node document is reachable from the frontend and describes a
    different CFG, so a second run must not leave one behind."""
    if not VOBLINT.exists():
        pytest.skip("cli/voblint not built -- run `pixi run cli-build`")
    out = tmp_path / "result"
    other = (
        REPO_ROOT / "tests/regression/17-call-string/known-imprecision"
        "/01-deep_recursion_bounded_context.vimp"
    )
    run = lambda src, *args: subprocess.run(
        [str(VOBLINT), *args, "--html-out", str(out), str(src)],
        capture_output=True, text=True, check=True)

    run(other, "--analysis", "interval", "--context", "call-string", "--context-depth", "60")
    many = len(list((out / "nodes").glob("*.xml")))
    run(FIXTURE, "--analysis", "interval")
    few = len(list((out / "nodes").glob("*.xml")))
    assert many > few, "second run did not shrink the node set"
    assert [d.name for d in (out / "cfgs").iterdir()] == [FIXTURE.name]


def test_refuses_a_directory_that_is_not_a_previous_report(tmp_path):
    """--html-out takes an arbitrary path, so it must not empty one that holds
    something else."""
    if not VOBLINT.exists():
        pytest.skip("cli/voblint not built -- run `pixi run cli-build`")
    target = tmp_path / "not-a-report"
    target.mkdir()
    keep = target / "important.txt"
    keep.write_text("do not delete me")

    proc = subprocess.run(
        [str(VOBLINT), "--analysis", "sign", "--html-out", str(target), str(FIXTURE)],
        capture_output=True, text=True,
    )
    assert proc.returncode == 5, proc.stdout + proc.stderr
    assert "refusing to write a report" in proc.stderr
    assert keep.read_text() == "do not delete me"


if __name__ == "__main__":
    sys.exit(pytest.main([__file__, "-q"]))
