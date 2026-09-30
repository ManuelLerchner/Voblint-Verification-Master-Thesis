"""The notation table is read off the theories' declarations, never guessed."""

import importlib.util
from pathlib import Path

import pytest

REPO = Path(__file__).resolve().parent.parent


@pytest.fixture(scope="module")
def tool():
    spec = importlib.util.spec_from_file_location(
        "notation", REPO / "thesis/tools/notation.py"
    )
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


@pytest.fixture
def rows(tool, tmp_path, monkeypatch):
    """The `names` rows of a one-theory project around `body`."""
    monkeypatch.chdir(tmp_path)
    (tmp_path / "ROOT").write_text("session Fake = HOL + theories Fake\n")

    def declared(body):
        (tmp_path / "Fake.thy").write_text(
            "theory Fake\n  imports Main\nbegin\n\n" + body + "\nend\n"
        )
        return tool.names(str(tmp_path), statements=True)

    return declared


def test_mixfix_slots_then_applied_arguments(tool):
    assert (
        tool.fill(r"\<C>\<^bsub>_,_,_\<^esub>", "ltr_collect", [r"\<G>", "g", "S", "v"])
        == r"\<C>\<^bsub>\<G>,g,S\<^esub> v"
    )
    # Blocks, breaks and priorities are layout, not symbols.
    assert (
        tool.fill(
            r"(_,_ \<turnstile>/ _ \<rightarrow>\<^sub>p/ _)",
            "pstep",
            ["G", "P", "c", "d"],
        )
        == r"G,P \<turnstile> c \<rightarrow>\<^sub>p d"
    )
    assert tool.fill(None, "carries", ["t", "c"]) == "carries t c"


def test_local_abbreviation_print_mode_and_expansion(tool, rows):
    src = rows(
        "locale L =\n  fixes g :: nat\nbegin\n"
        'abbreviation (input) cover :: "nat" where "cover \\<equiv> f g"\nend'
    )
    decl = tool.find_local("cover", "L", src)
    assert decl["pretty_printed"] is False
    assert decl["expands"] == "f g"


def test_missing_mixfix_fails_with_its_location(tool, rows):
    src = rows('definition ltr_collect :: "nat" where "ltr_collect = 0"')
    with pytest.raises(tool.NotationError, match=r"no mixfix at \S*Fake\.thy:5"):
        tool.find_global("ltr_collect", src, want_mixfix=True)


def test_abbreviation_in_the_wrong_locale_fails(tool, rows):
    src = rows(
        'locale M =\n  fixes g :: nat\nbegin\nabbreviation a where "a \\<equiv> g"\nend'
    )
    with pytest.raises(tool.NotationError, match="expected one"):
        tool.find_local("a", "L", src)


def test_html_rendering_sets_scripts(tool):
    assert tool.isa_html(r"\<C>\<^bsub>\<G>,g,S\<^esub>") == "𝒞<sub>𝒢,g,S</sub>"
    assert tool.isa_html(r"\<gamma>\<^sub>D\<^sub>G") == "γ<sub>DG</sub>"
    assert tool.prose_html("stores _s_ in {\\<gamma> a}") == "stores <em>s</em> in γ a"


def test_parameters_fields_and_infix(tool, rows):
    src = rows(
        'class w = fixes widen :: "\'a => \'a => \'a" (infixl "\\<nabla>" 65)\n'
        'record r = fld :: nat ("fld\\<^sup>#")\n'
        'locale L = fixes x :: nat\n  for route ("context\\<^sup>#")'
    )
    assert tool.find_class_param("widen", "w", src)["mixfix"] == "_ \\<nabla> _"
    assert tool.find_record_field("fld", "r", src)["mixfix"] == "fld\\<^sup>#"
    with pytest.raises(tool.NotationError, match="has no field"):
        tool.find_record_field("other", "r", src)
