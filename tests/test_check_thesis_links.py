"""Resolve thesis citations against the HTML export's repository layout."""

import importlib.util
import json
import shutil
import subprocess
import sys
from pathlib import Path

REPO = Path(__file__).resolve().parent.parent
sys.path.insert(0, str(REPO / "scripts"))


def test_write_and_check_exported_html(tmp_path):
    scripts = tmp_path / "scripts"
    scripts.mkdir()
    checker = scripts / "check_thesis_links.py"
    shutil.copyfile(REPO / "scripts/check_thesis_links.py", checker)
    shutil.copyfile(REPO / "scripts/isabelle_html.py", scripts / "isabelle_html.py")
    thesis = tmp_path / "thesis"
    thesis.mkdir()
    (thesis / "example.typ").write_text('isatype("pp")\nisa: "pp"\n')
    page = tmp_path / "build/isabelle-html/Voblint/Voblint_CFG/CFG_Def.html"
    page.parent.mkdir(parents=True)
    page.write_text('<span class="entity_def" id="CFG_Def.pp|type"></span>')
    # Neither an old ungrouped export nor an unrelated library definition may
    # steal the short name from the project's current presentation.
    for relative in ("Unsorted/Voblint_CFG/CFG_Def.html", "HOL/Example/Other.html"):
        duplicate = tmp_path / "build/isabelle-html" / relative
        duplicate.parent.mkdir(parents=True)
        duplicate.write_text(
            '<span class="entity_def" id="Other.pp|type"></span>'
            '<span class="entity_def" id="Other.pp|const"></span>'
        )

    for mode in ("--write", "--check"):
        result = subprocess.run(
            [sys.executable, str(checker), mode, "--base", "https://example.org/"],
            capture_output=True,
            text=True,
        )
        assert result.returncode == 0, result.stdout + result.stderr

    payload = json.loads((thesis / "shared/generated/links.json").read_text())
    assert payload["links"] == {
        "type:pp": "Voblint/Voblint_CFG/CFG_Def.html#CFG_Def.pp%7Ctype",
    }
    # The untyped citation resolves to the typed key of its anchor.
    assert payload["names"] == {"pp": "type:pp"}


def test_citation_coverage_without_html(tmp_path, monkeypatch):
    spec = importlib.util.spec_from_file_location(
        "thesis_links", REPO / "scripts/check_thesis_links.py"
    )
    checker = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(checker)
    monkeypatch.setattr(checker, "REPO", tmp_path)
    thesis = tmp_path / "thesis"
    thesis.mkdir()
    (thesis / "example.typ").write_text(
        'isathm("sound")\nproved("sound")\n'
        'thy("domain")\nisasession("Session")\n'
        'thy-badge("Session", "Theory")\nisa: "domain"\n'
    )
    out = thesis / "links.json"
    monkeypatch.setattr(checker, "OUT", out)
    links = {
        "thm:sound": "Session/Theory.html#Theory.sound%7Cfact",
        "locale:domain": "Session/Theory.html#Theory.domain%7Clocale",
        "session:Session": "Session/index.html",
        "theory:Session.Theory": "Session/Theory.html",
    }
    for missing in [None, *links]:
        payload = {k: v for k, v in links.items() if k != missing}
        out.write_text(
            json.dumps(
                {
                    "base": "https://example.org/",
                    "links": payload,
                    "names": {"domain": "locale:domain"},
                }
            )
        )
        assert checker.check_coverage() == (0 if missing is None else 1)

    # A target without a definition anchor is insufficient for an entity.
    links["thm:sound"] = "Session/Theory.html"
    out.write_text(json.dumps({"base": "https://example.org/", "links": links}))
    assert checker.check_coverage() == 1


def test_lenient_check_still_rejects_missing_target(tmp_path):
    scripts = tmp_path / "scripts"
    scripts.mkdir()
    checker = scripts / "check_thesis_links.py"
    shutil.copyfile(REPO / "scripts/check_thesis_links.py", checker)
    shutil.copyfile(REPO / "scripts/isabelle_html.py", scripts / "isabelle_html.py")
    thesis = tmp_path / "thesis"
    thesis.mkdir()
    (thesis / "example.typ").write_text('proved("missing_fact")\n')
    generated = thesis / "shared/generated"
    generated.mkdir(parents=True)
    (generated / "links.json").write_text(
        json.dumps({"base": "https://example.org/", "links": {}})
    )
    result = subprocess.run(
        [sys.executable, str(checker), "--check", "--lenient"],
        capture_output=True,
        text=True,
    )
    assert result.returncode == 1
    assert "missing_fact" in result.stdout


def test_original_locale_fact_precedes_interpretation():
    spec = importlib.util.spec_from_file_location(
        "thesis_links", REPO / "scripts/check_thesis_links.py"
    )
    checker = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(checker)
    original = (
        "Voblint/Voblint_CFG/LTR_Abstract.html",
        '<span id="LTR_Abstract.ltr_coverage.cover_sound|fact"></span>',
    )
    interpreted = (
        "Voblint/Voblint_Examples/Example.html",
        '<span id="Example.instance.routed.cover_sound|fact"></span>',
    )
    stale = ("Unsorted/Old.html", '<span id="Old.cover_sound|fact"></span>')
    for pages in ((original, interpreted, stale), (stale, interpreted, original)):
        index = {}
        for page, body in pages:
            checker._index_page(index, page, body)
        assert index[("cover_sound", "fact")] == (
            "Voblint/Voblint_CFG/LTR_Abstract.html"
            "#LTR_Abstract.ltr_coverage.cover_sound%7Cfact"
        )


def test_library_declaration_precedes_project_interpretation():
    spec = importlib.util.spec_from_file_location(
        "thesis_links", REPO / "scripts/check_thesis_links.py"
    )
    checker = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(checker)
    library = (
        "Unsorted/TD/TD.html",
        '<span class="command">lemma</span>'
        '<span id="TD.solver.partial_post_solution|fact">partial_post_solution</span>',
    )
    instance = (
        "Voblint/Voblint_Solver/Globals_Rule.html",
        '<span class="command">'
        '<span id="Globals_Rule.TD_side_rule_Interp.partial_post_solution|fact">'
        "global_interpretation</span></span>",
    )
    for pages in ((library, instance), (instance, library)):
        index = {}
        for page, body in pages:
            checker._index_page(index, page, body)
        assert index[("partial_post_solution", "fact")].startswith(library[0])
        # Explicit instance citations must retain the specialized theorem.
        assert index[
            ("Globals_Rule.TD_side_rule_Interp.partial_post_solution", "fact")
        ].startswith(instance[0])


def test_unqualified_interpretation_requires_explicit_choice(tmp_path, monkeypatch):
    spec = importlib.util.spec_from_file_location(
        "thesis_links", REPO / "scripts/check_thesis_links.py"
    )
    checker = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(checker)
    index = {}
    checker._index_page(
        index,
        "Voblint/Test/Example.html",
        '<span class="command"><span id="Example.i.result|fact">'
        "global_interpretation</span></span>",
    )
    monkeypatch.setattr(checker, "REPO", tmp_path)
    monkeypatch.setattr(
        checker, "cited", lambda: [(tmp_path / "example.typ", 1, "thm", "result")]
    )
    links, _, errors = checker.resolve(index)
    assert not links
    assert "qualify the intended instance" in errors[0]


def test_live_resolution_follows_library_locale_links(monkeypatch):
    spec = importlib.util.spec_from_file_location(
        "thesis_links", REPO / "scripts/check_thesis_links.py"
    )
    checker = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(checker)
    base = "https://example.org/site/"
    pages = {
        "Voblint/index.html": '<a href="Voblint_Solver/index.html">solver</a>',
        "Voblint/Voblint_Solver/index.html": '<a href="Globals.html">Globals</a>',
        "Voblint/Voblint_Solver/Globals.html": (
            '<span class="command"><span id="Globals.i.result|fact">'
            "global_interpretation</span></span>"
            '<a href="../../Unsorted/TD/TD.html#TD.solver%7Clocale">solver</a>'
            '<a href="https://elsewhere.org/X.html#X.x|locale">external</a>'
        ),
        "Unsorted/TD/TD.html": (
            '<span class="command">locale</span>'
            '<span id="TD.solver|locale">solver</span>'
            '<span class="command">lemma</span>'
            '<span id="TD.solver.result|fact">result</span>'
        ),
    }
    fetched = []

    def fetch(url, retries):
        assert url.startswith(base)
        path = url.removeprefix(base)
        fetched.append(path)
        return pages[path]

    monkeypatch.setattr(checker, "fetch", fetch)
    index = checker.index_live(base, retries=1)
    assert index[("result", "fact")] == "Unsorted/TD/TD.html#TD.solver.result%7Cfact"
    assert len(fetched) == len(pages)


def test_manifest_facts_need_targets(tmp_path, monkeypatch):
    # The oracle audit table cites every facts.toml key; no .typ spells them out.
    spec = importlib.util.spec_from_file_location(
        "thesis_links", REPO / "scripts/check_thesis_links.py"
    )
    checker = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(checker)
    monkeypatch.setattr(checker, "REPO", tmp_path)
    shared = tmp_path / "thesis/shared"
    shared.mkdir(parents=True)
    (shared / "facts.toml").write_text('[facts.audited]\nwhy = "table row"\n')
    out = shared / "links.json"
    monkeypatch.setattr(checker, "OUT", out)
    assert ("thm", "audited") in {(k, n) for _, _, k, n in checker.cited()}

    for links, expected in (
        ({}, 1),
        ({"thm:audited": "S/T.html#T.audited%7Cfact"}, 0),
    ):
        out.write_text(json.dumps({"base": "https://example.org/", "links": links}))
        assert checker.check_coverage() == expected


def test_display_changes_text_not_target(tmp_path, monkeypatch):
    spec = importlib.util.spec_from_file_location(
        "thesis_links", REPO / "scripts/check_thesis_links.py"
    )
    checker = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(checker)
    monkeypatch.setattr(checker, "REPO", tmp_path)
    thesis = tmp_path / "thesis"
    thesis.mkdir()
    (thesis / "example.typ").write_text(
        'isaconst("loc.q", display: "q")\n'
        'isathm("loc.f", thy: "T", display: "f")\n'
        'isatype("loc.t", display: "t", thy: "T")\n'
        'isalocale(\n  "loc.l",\n  thy: "T",\n  display: "l",\n)\n'
    )
    assert [(k, n) for _, _, k, n in checker.cited()] == [
        ("const", "loc.q"),
        ("thm", "T.loc.f"),
        ("type", "T.loc.t"),
        ("locale", "T.loc.l"),
    ]
