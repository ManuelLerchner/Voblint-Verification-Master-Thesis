"""Isabelle source anchors can name generated entities at a command keyword."""

import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parents[1] / "scripts"))
from isabelle_html import Source, generic_sources


def interpretation(name="Instance.i.answer", locale="Base.child"):
    return (
        '<span class="command"><span class="entity_def" '
        f'id="{name}|fact"><span>global_interpretation</span></span></span>'
        f' i: <a href="Base.html#{locale}%7Clocale">child</a>'
        '<span class="command">by</span> simp'
    )


def definition(name="Base.parent.answer"):
    return (
        '<span class="command"><span class="entity_def" '
        f'id="{name}|fact">definition</span></span> answer where …'
    )


def test_command_ownership_and_encoded_locale_reference():
    source = Source(interpretation() + definition())
    assert source.location("Instance.i.answer|fact") == "interpretation"
    assert source.anchors["Instance.i.answer|fact"]["locales"] == {"Base.child"}
    assert source.location("Base.parent.answer|fact") == "source"
    assert source.location("missing|fact") == "theory"


def fixture():
    return {
        "locale:Base.child": {
            "theory": "Base",
            "deps": ["locale:Base.parent"],
        },
        "locale:Base.parent": {"theory": "Base", "deps": []},
        "thm:Base.parent.answer": {"theory": "Base", "deps": []},
        "thm:Instance.i.answer": {"theory": "Instance", "deps": []},
    }


def test_generic_source_requires_locale_ancestry_and_verified_anchor():
    raw = fixture()
    sources = {"Base": Source(definition()), "Instance": Source(interpretation())}
    assert generic_sources(raw, sources) == {
        "thm:Instance.i.answer": "thm:Base.parent.answer"
    }
    raw["locale:Base.child"]["deps"] = []
    assert generic_sources(raw, sources) == {}
    raw["locale:Base.child"]["deps"] = ["locale:Base.parent"]
    sources["Base"] = Source("")
    assert generic_sources(raw, sources) == {}


def test_ambiguous_origins_are_not_guessed_and_cycles_terminate():
    raw = fixture()
    raw["locale:Base.parent"]["deps"] = ["locale:Base.child"]
    raw["thm:Extension.parent.answer"] = {"theory": "Base", "deps": []}
    sources = {
        "Base": Source(definition() + definition("Extension.parent.answer")),
        "Instance": Source(interpretation()),
    }
    assert generic_sources(raw, sources) == {}


def test_unrelated_locale_with_same_short_name_is_not_an_origin():
    raw = fixture()
    raw["locale:Other.parent"] = {"theory": "Base", "deps": []}
    sources = {"Base": Source(definition()), "Instance": Source(interpretation())}
    assert generic_sources(raw, sources) == {}
