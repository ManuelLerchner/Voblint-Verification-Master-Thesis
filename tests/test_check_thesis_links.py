"""Resolve thesis citations against the HTML export's repository layout."""

import importlib.util
import json
import shutil
import subprocess
import sys
from pathlib import Path

REPO = Path(__file__).resolve().parent.parent


def test_write_and_check_exported_html(tmp_path):
    scripts = tmp_path / "scripts"
    scripts.mkdir()
    checker = scripts / "check_thesis_links.py"
    shutil.copyfile(REPO / "scripts/check_thesis_links.py", checker)
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
        "any:pp": "Voblint/Voblint_CFG/CFG_Def.html#CFG_Def.pp%7Ctype",
    }


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
        "any:domain": "Session/Theory.html#Theory.domain%7Clocale",
        "session:Session": "Session/index.html",
        "theory:Session.Theory": "Session/Theory.html",
    }
    for missing in [None, *links]:
        payload = {k: v for k, v in links.items() if k != missing}
        out.write_text(json.dumps({"base": "https://example.org/", "links": payload}))
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
