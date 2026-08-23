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


# A declared global, so the globals pane has something to show.
GLOBALS_FIXTURE = (
    REPO_ROOT / "tests/regression/04-globals/precision/04-global_written_constant.vimp"
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


def test_source_lines_link_to_their_cfg_nodes(report):
    """ns is what makes the listing navigable rather than just pretty-printed.

    Every executable line should name the nodes compiled from it, and the
    mapping should be exact: file.xsl splices ns into select_line(), so a line
    pointing at the wrong node sends the reader to the wrong state rather than
    failing visibly.
    """
    src = next((report / "files").glob("*.xml")).read_text()
    linked = re.findall(r'<ln nr="(\d+)" ns="\[&quot;([^&]+)&quot;', src)
    assert linked, "no source line references a CFG node"

    ids = {n.stem for n in (report / "nodes").glob("*.xml")}
    for nr, node_id in linked:
        assert node_id in ids, f"line {nr} references {node_id}, which has no document"

    # The check's own line must reach the node carrying that check's verdict.
    source = FIXTURE.read_text().splitlines()
    check_lines = [
        str(i + 1) for i, l in enumerate(source) if "__voblint_check" in l
    ]
    linked_lines = {nr for nr, _ in linked}
    for nr in check_lines:
        assert nr in linked_lines, f"check on line {nr} links to no node"


def test_dead_lines_are_marked_dead(report):
    """ded greys a line out, so it has to mean 'no execution reaches this'.

    A line with no node behind it -- a brace, a comment, a blank -- is not dead
    code, and marking it so would grey out most of the file.
    """
    src = next((report / "files").glob("*.xml")).read_text()
    entries = re.findall(r'<ln nr="(\d+)" ns="(\[[^"]*\])"[^>]*ded="(true|false)"', src)
    assert entries, "no source lines emitted"

    dead = [nr for nr, _, d in entries if d == "true"]
    assert dead, "the fixture has an unreachable branch but no line is marked dead"

    for nr, ns, d in entries:
        if d == "true":
            assert ns != "[]", f"line {nr} marked dead but has no node behind it"


def test_node_documents_carry_a_source_position(report):
    """A node document with line=0 renders a location goblint does not have.

    Not every program point has a command behind it. Entry and exit nodes have
    none, and compile_proc reserves one epilogue index per function that falls
    through -- a point node whose only edge is the implicit return. Those
    report zero, which is correct; what would be wrong is a node borrowing a
    neighbour's line, so the check is that every position present is a real one
    and that the checks in particular are placed exactly.
    """
    source = FIXTURE.read_text().splitlines()
    positioned = 0
    for doc in (report / "nodes").glob("*.xml"):
        if doc.name == "globals.xml":
            continue
        line = int(ET.parse(doc).getroot().find("call").get("line"))
        if line == 0:
            continue
        assert "_pp" in doc.stem, f"{doc.name} has no command but reports line {line}"
        assert line <= len(source), f"{doc.name} points past the end of the file"
        positioned += 1
    assert positioned, "no point node carried a position"

    # A check always compiles to a program point, so every check line must be
    # one some node reports -- including a check in unreachable code, whose
    # node renders as dead but is still the node that line belongs to.
    placed = {
        int(ET.parse(doc).getroot().find("call").get("line"))
        for doc in (report / "nodes").glob("*_pp*.xml")
    }
    for i, text in enumerate(source):
        if "__voblint_check" in text:
            assert i + 1 in placed, f"no node carries the check on line {i + 1}"


def test_explicit_solver_still_annotates_the_source(tmp_path):
    """An explicit --solver used to render states with no findings beside them.

    The graph and the inline annotations are two readings of one solved table,
    and for a chosen discipline that is the table the discipline produced. The
    verdicts were never missing, only unpublished: before, the source view fell
    back to no annotations at all whenever --solver named anything but the
    domain's default.
    """
    out = tmp_path / "result"
    proc = subprocess.run(
        [
            str(VOBLINT),
            "--analysis",
            "interval",
            "--solver",
            "per-origin",
            "--html-out",
            str(out),
            str(FIXTURE),
        ],
        capture_output=True,
        text=True,
    )
    assert proc.returncode == 0, proc.stderr
    warns = sorted((out / "warn").glob("warn*.xml"))
    assert warns, "an explicit --solver emitted no warning documents"
    line = int(ET.parse(warns[0]).getroot().find("text").get("line"))
    source = FIXTURE.read_text().splitlines()
    assert "__voblint_check" in source[line - 1], (
        f"warn1 points at line {line}: {source[line - 1]!r}"
    )


def _run(tmp_path, *args):
    out = tmp_path / "result"
    proc = subprocess.run(
        [str(VOBLINT), *args, "--html-out", str(out)], capture_output=True, text=True
    )
    assert proc.returncode == 0, proc.stderr
    return out


def test_globals_pane_shows_the_constraint_systems_global_unknowns(tmp_path):
    """The globals button opened an empty pane.

    goblint's pane is GHT.iter over every GVar -- the global constraint system's
    unknowns, not C globals, whose values live in the local state. Ours holds the
    two kinds a routed D/G system side-effects: the shared slot, and one seed per
    callee entry carrying the state a call pushes into that callee.
    """
    out = _run(tmp_path, "--analysis", "interval", str(GLOBALS_FIXTURE))
    root = ET.parse(out / "nodes" / "globals.xml").getroot()
    assert root.tag == "globs"

    keys = [g.find("key").text for g in root.findall("glob")]
    assert "Global" in keys, f"shared slot missing: {keys}"
    assert any(k.startswith("enter ") for k in keys), f"no callee-entry seed: {keys}"
    # One seed per procedure, main included -- it is compiled through the same
    # wrapper, and a procedure nothing calls is listed as unreachable, not omitted.
    assert "enter main" in keys, keys


def test_a_seed_carries_the_state_pushed_into_that_callee(tmp_path):
    """The seed is the pane's whole point: what a call hands its callee.

    A procedure that is never called has no seed written to it, and must read as
    unreachable rather than borrowing another entry's state.
    """
    src = tmp_path / "seeded.vimp"
    src.write_text(
        "void bump(n) {\n  m := n + 1;\n  return m\n}\n\n"
        "void never() {\n  return 0\n}\n\n"
        "void main() {\n  x := 7;\n  y := bump(x);\n  __voblint_check(y == 8)\n}\n"
    )
    out = _run(tmp_path, "--analysis", "interval", str(src))
    rows = {
        g.find("key").text: ET.tostring(g.find("analysis"), encoding="unicode")
        for g in ET.parse(out / "nodes" / "globals.xml").getroot().findall("glob")
    }
    assert "enter bump" in rows, rows.keys()
    assert "<key>n</key><value>[7,7]</value>" in rows["enter bump"], (
        f"the seed does not carry the actual argument: {rows['enter bump']}"
    )
    assert "unreachable" in rows["enter never"], (
        f"an uncalled procedure reported a seed: {rows['enter never']}"
    )


def test_globals_document_is_in_the_shape_the_stylesheet_reads(tmp_path):
    """globals.xsl walks globs/glob/key, not globs/analysis/value/map.

    A document in the node documents' map shape renders as a blank pane rather
    than as an error, so nothing downstream fails when this drifts -- which is
    exactly how the pane came to be empty in the first place.
    """
    out = _run(tmp_path, "--analysis", "interval", str(GLOBALS_FIXTURE))
    root = ET.parse(out / "nodes" / "globals.xml").getroot()
    assert root.findall("glob"), "no <glob> rows: the stylesheet would render nothing"
    assert not root.findall("analysis"), (
        "<analysis> directly under <globs> is the node-document shape, "
        "which globals.xsl does not read"
    )
    for g in root.findall("glob"):
        assert g.find("key") is not None, "a <glob> with no <key> renders nameless"
        assert g.findall("analysis"), "a <glob> with no <analysis> renders no value"


# Every field below was once a placeholder -- a hardcoded zero, a repeated
# value, or an empty list -- that rendered as something plausible. None of them
# fail loudly when they regress, which is why each is asserted rather than
# eyeballed.
CTX_FIXTURE = (
    REPO_ROOT / "tests/regression/03-procedures/precision/04-two_call_sites_entry_state.vimp"
)


def test_context_sensitive_runs_annotate_the_source(tmp_path):
    """--context entry-state rendered states and no findings.

    A context-sensitive run has no state-carrying report, so the annotation path
    fell through to []. It has per-context verdicts instead, and those carry the
    same finding a reader opens the report for.
    """
    out = _run(tmp_path, "--analysis", "interval", "--context", "entry-state",
               str(CTX_FIXTURE))
    warns = sorted((out / "warn").glob("warn*.xml"))
    assert warns, "a context-sensitive run emitted no findings"

    source = CTX_FIXTURE.read_text().splitlines()
    check_lines = [i + 1 for i, l in enumerate(source) if "__voblint_check" in l]
    warned = sorted(
        int(ET.parse(w).getroot().find("text").get("line")) for w in warns
    )
    assert warned == check_lines, (
        f"findings land on {warned}, checks are on {check_lines}"
    )


def test_verdicts_pair_with_positions_before_dead_rows_are_dropped(tmp_path):
    """Filtering first would shift every annotation after a dead check.

    The verdict list and the parser's position list are pairwise aligned only
    while both are unfiltered, so a dead check must be dropped after the zip,
    not before it.
    """
    src = tmp_path / "dead_then_live.vimp"
    src.write_text(
        "void main() {\n"
        "  x := 5;\n"
        "  if (x < 0) {\n"
        "    __voblint_check(x == 99)\n"
        "  } else {\n"
        "    __voblint_check(x == 5)\n"
        "  }\n"
        "}\n"
    )
    out = _run(tmp_path, "--analysis", "interval", str(src))
    warns = sorted((out / "warn").glob("warn*.xml"))
    assert warns, "no findings emitted"
    lines = [int(ET.parse(w).getroot().find("text").get("line")) for w in warns]
    # The live check is on line 6; the dead one on line 4 is dropped. Reporting
    # line 4 would mean the surviving verdict took the dropped row's position.
    assert 6 in lines, f"the live check is not reported on its own line: {lines}"
    assert 4 not in lines, f"a dead check was reported: {lines}"


def test_node_locations_are_real_spans_not_repeated_values(tmp_path):
    """endColumn repeated column, so every span read as zero-width.

    The parser knew $endpos and discarded it. A command ends after its own text,
    so endColumn must exceed column on any node with a command behind it.
    """
    out = _run(tmp_path, "--analysis", "interval", str(CTX_FIXTURE))
    spans = 0
    for doc in (out / "nodes").glob("*_pp*.xml"):
        call = ET.parse(doc).getroot().find("call")
        line, col = int(call.get("line")), int(call.get("column"))
        end_line, end_col = int(call.get("endLine")), int(call.get("endColumn"))
        if line == 0:
            continue
        assert end_line >= line, f"{doc.name} ends before it starts"
        assert end_col > col, (
            f"{doc.name} spans column {col}..{end_col} -- a zero-width span"
        )
        spans += 1
    assert spans, "no node carried a span"


def test_node_order_is_a_sequence_not_the_line_number(tmp_path):
    """order is goblint's sequence number within the function.

    It was fed the line number, which is plausible, monotone, and wrong -- and a
    fabricated value is worse than the zero it replaced.
    """
    out = _run(tmp_path, "--analysis", "interval", str(CTX_FIXTURE))
    pairs = []
    for doc in (out / "nodes").glob("*_pp*.xml"):
        call = ET.parse(doc).getroot().find("call")
        line, order = int(call.get("line")), int(call.get("order"))
        if line:
            pairs.append((line, order))
    assert pairs, "no positioned node"
    assert any(line != order for line, order in pairs), (
        f"order tracks line exactly, so it is still the line number: {sorted(pairs)}"
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
