"""The VIMP listing check: every program the thesis shows opens in the playground."""

import importlib.util
import shutil
import sys
import tempfile
from pathlib import Path

import pytest

REPO = Path(__file__).resolve().parent.parent
THESIS = REPO / "thesis"
sys.path.insert(0, str(REPO / "scripts"))

spec = importlib.util.spec_from_file_location(
    "vimp_listings", THESIS / "tools/vimp_listings.py"
)
vl = importlib.util.module_from_spec(spec)
spec.loader.exec_module(vl)

import playground_link  # noqa: E402


def listing(shown, url, claim=None, given=None, settings=None, part_of=None):
    return {
        "shown": shown,
        "url": url,
        "claim": claim,
        "part-of": part_of,
        "given": given or {},
        "settings": settings
        or {
            "analysis": "interval",
            "globals": "warrow",
            "context": "call-string",
            "k": 1,
        },
    }


@pytest.fixture(scope="module")
def context():
    claims = vl.claim_runs()
    return claims, vl.known_runs(claims), vl.check_pages_links.playground_vocabulary()


def test_source_scan_flags_vimp_outside_the_helper(tmp_path):
    (tmp_path / "ok.typ").write_text(
        '// listing(lang: "c") in a comment is prose\n'
        '#listing(lang: "c", ```\nfun main() {}\n```)\n'
        '#align(center, listing("x = 1;", lang: "c", claim: "c1"))\n'
    )
    assert vl.scan_source(tmp_path) == []

    (tmp_path / "bad.typ").write_text(
        '#raw("fun main() {}", lang: "c", block: true)\n```c\nfun main() {}\n```\n'
    )
    problems = vl.scan_source(tmp_path)
    assert any("bad.typ:1" in p and "raw(...)" in p for p in problems), problems
    assert any("bad.typ:2" in p and "```c" in p for p in problems), problems


def test_fragment_links_as_the_body_of_main():
    assert vl.vimp_program("fun main() {}") == "fun main() {}"
    assert (
        vl.vimp_program("x = 0;\n\ny = x;") == "fun main() {\n  x = 0;\n\n  y = x;\n}"
    )


def test_matching_link_passes(context):
    shown = "fun main() {\n  __voblint_check(true);\n}"
    url = playground_link.link(shown, "interval", "warrow", "call-string", 1)
    assert vl.check_listing(listing(shown, url), *context) == []


def test_link_to_another_program_or_setting_fails(context):
    shown = "fun main() {\n  __voblint_check(true);\n}"
    other = playground_link.link(
        "fun main() {}", "interval", "warrow", "call-string", 1
    )
    problems = vl.check_listing(listing(shown, other), *context)
    assert any("different program" in p for p in problems), problems

    wrong = playground_link.link(shown, "interval", "warrow", "none")
    problems = vl.check_listing(listing(shown, wrong), *context)
    assert any("link settings" in p for p in problems), problems

    invalid = playground_link.link(shown, "octagon", "warrow", "call-string", 1)
    bad = listing(
        shown,
        invalid,
        settings={
            "analysis": "octagon",
            "globals": "warrow",
            "context": "call-string",
            "k": 1,
        },
    )
    problems = vl.check_listing(bad, *context)
    assert any("not a playground option" in p for p in problems), problems


def test_claim_settings_win_and_overrides_are_flagged(context):
    claims = context[0]
    name = "dom-stride2-int"
    run = claims[name]
    url = playground_link.link(run["program"], "sign", "warrow", "none")
    shown = run["program"]
    bad = listing(
        shown,
        url,
        claim=name,
        given={"analysis": "sign"},
        settings={**run["settings"], "analysis": "sign"},
    )
    problems = vl.check_listing(bad, *context)
    assert any("overrides claim" in p for p in problems), problems

    good_url = playground_link.link(
        run["program"],
        **{
            "analysis": run["settings"]["analysis"],
            "globals_rule": run["settings"]["globals"],
            "context": run["settings"]["context"],
        },
    )
    excerpt = "v = 1;\nwhile (v < 51) { v = v + 2; }"
    assert (
        vl.check_listing(
            listing(excerpt, good_url, claim=name, settings=run["settings"]), *context
        )
        == []
    )
    unrelated = listing("y = 7;", good_url, claim=name, settings=run["settings"])
    assert any("nor an excerpt" in p for p in vl.check_listing(unrelated, *context))


def test_a_fixture_shown_at_other_settings_is_flagged(context):
    claims = context[0]
    program = claims["chain-factorial-entry"]["program"]
    url = playground_link.link(program, "interval", "warrow", "call-string", 1)
    problems = vl.check_listing(listing(program, url), *context)
    assert any("other settings" in p for p in problems), problems


def test_pdf_uris_are_unescaped():
    pdf = rb"<</S/URI/URI(https://x/p.html?a=1#code=ab\(c\)\\d)>> <</S /URI /URI (https://y)>>"
    found = vl.pdf_uris(pdf)
    assert found["https://x/p.html?a=1#code=ab(c)\\d"] == 1
    assert found["https://y"] == 1


@pytest.mark.skipif(shutil.which("typst") is None, reason="typst not installed")
def test_built_document_needs_a_clickable_link_on_every_vimp_listing():
    """Compiles small documents against the real lib/code.typ: the Typst encoder
    must round-trip, and a listing without a clickable tag or a raw VIMP block
    must fail."""
    with tempfile.TemporaryDirectory(dir=THESIS) as tmp:
        doc = Path(tmp) / "doc.typ"
        header = '#import "/lib/code.typ": listing\n'
        codly = '#import "@preview/codly:1.3.0": codly-init\n#show: codly-init\n'
        body = '#listing(lang: "c", ```\nx = 0; while (x < 3) { x = x + 1; }\n```)\n'

        doc.write_text(header + codly + body)
        problems, count = vl.check_built(doc)
        assert (problems, count) == ([], 1)

        doc.write_text(
            header + codly + body + '#raw("fun main() {}", lang: "c", block: true)\n'
        )
        problems, _ = vl.check_built(doc)
        assert any("without a playground link" in p for p in problems), problems

        # A show rule that drops links leaves the listing unclickable.
        doc.write_text(header + codly + "#show link: it => it.body\n" + body)
        problems, _ = vl.check_built(doc)
        assert any("link annotation" in p for p in problems), problems
