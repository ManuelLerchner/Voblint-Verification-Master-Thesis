"""The notation table is read off the theories' declarations, never guessed."""

import importlib.util
from pathlib import Path

import pytest

REPO = Path(__file__).resolve().parent.parent
THY = REPO / "src" / "Fake.thy"


@pytest.fixture(scope="module")
def tool():
    spec = importlib.util.spec_from_file_location(
        "notation", REPO / "thesis/tools/notation.py"
    )
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


def texts(body):
    return [(THY, "theory Fake\n  imports Main\nbegin\n\n" + body + "\nend\n")]


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


def test_scope_tracks_locale_blocks(tool):
    text = texts(
        'locale L =\n  fixes x :: nat\nbegin\nabbreviation a where "a \\<equiv> x"\nend\n'
        'definition d :: nat where "d = 0"'
    )[0][1]
    assert tool.scope_at(text, text.index("abbreviation")) == "L"
    assert tool.scope_at(text, text.index("definition")) == "global"


def test_local_abbreviation_print_mode_and_expansion(tool):
    src = texts(
        "locale L =\n  fixes g :: nat\nbegin\n"
        'abbreviation (input) cover :: "nat" where "cover \\<equiv> f g"\nend'
    )
    decl = tool.find_local("cover", "L", src)
    assert decl["pretty_printed"] is False
    assert decl["expands"] == "f g"


def test_missing_mixfix_fails_with_its_location(tool):
    src = texts('definition ltr_collect :: "nat" where "ltr_collect = 0"')
    with pytest.raises(tool.NotationError, match=r"no mixfix at src/Fake\.thy:5"):
        tool.find_global("ltr_collect", src, want_mixfix=True)


def test_abbreviation_in_the_wrong_locale_fails(tool):
    src = texts(
        'locale M =\n  fixes g :: nat\nbegin\nabbreviation a where "a \\<equiv> g"\nend'
    )
    with pytest.raises(tool.NotationError, match="expected one"):
        tool.find_local("a", "L", src)


def test_html_rendering_sets_scripts(tool):
    assert tool.isa_html(r"\<C>\<^bsub>\<G>,g,S\<^esub>") == "𝒞<sub>𝒢,g,S</sub>"
    assert tool.isa_html(r"\<gamma>\<^sub>D\<^sub>G") == "γ<sub>DG</sub>"
    assert tool.prose_html("stores _s_ in {\\<gamma> a}") == "stores <em>s</em> in γ a"
