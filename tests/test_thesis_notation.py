"""The notation table is read off the theories' declarations, never guessed.

`isar project notation` finds each declaration, fills its mixfix and reads its
print mode, expansion and link; its own tests cover that. These test what this
repository adds: the manifest's names, the table's wording, the variable
convention and the README rendering.
"""

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


def test_forms_name_their_declarations_as_isar_does(tool):
    assert tool._isar_name({"const": "aval"}) == "aval"
    assert tool._isar_name({"const": "gamma", "class": "numeric_domain"}) == (
        "numeric_domain_class.gamma"
    )
    assert tool._isar_name({"const": "dgs_skip", "record": "dg_spec"}) == (
        "dg_spec.dgs_skip"
    )
    assert tool._isar_name({"const": "route", "parameter_of": "routed_context"}) == (
        "routed_context.route"
    )
    assert tool._isar_name({"const": "carries", "locale": "activation_coverage"}) == (
        "activation_coverage.carries"
    )


def test_the_table_names_a_member_by_its_owner(tool):
    def row(kind, **extra):
        return {"kind": kind, "owner": "o", "command": "fun", "printed": True, **extra}

    assert tool._declaration(row("constant")) == "fun"
    assert tool._declaration(row("class_parameter")) == "class o"
    assert tool._declaration(row("record_field")) == "record o"
    assert tool._declaration(row("locale_parameter")) == "locale o"
    assert tool._declaration(row("locale_abbreviation")) == "abbreviation"
    assert tool._declaration(row("locale_abbreviation", printed=False)) == (
        "abbreviation (input)"
    )


def test_a_convention_needs_its_for_clause(tool, tmp_path, monkeypatch):
    monkeypatch.setattr(tool, "REPO", tmp_path)
    (tmp_path / "T.thy").write_text(
        'inductive step :: "nat => bool" for \\<G> where "step 0"\n'
        'definition plain :: "nat" where "plain = 0"\n'
    )
    tool.check_binds("\\<G>", {"key": "k", "path": "T.thy", "line": 1})
    with pytest.raises(tool.NotationError, match=r"expected `for \\<G>`.*T\.thy:2"):
        tool.check_binds("\\<G>", {"key": "k", "path": "T.thy", "line": 2})


def test_html_rendering_sets_scripts(tool):
    assert tool.isa_html(r"\<C>\<^bsub>\<G>,g,S\<^esub>") == "𝒞<sub>𝒢,g,S</sub>"
    assert tool.isa_html(r"\<gamma>\<^sub>D\<^sub>G") == "γ<sub>DG</sub>"
    assert tool.prose_html("stores _s_ in {\\<gamma> a}") == "stores <em>s</em> in γ a"


def test_the_readme_lists_shorthands_in_its_one_table(tool):
    form = {
        "const": "cover",
        "symbol": "cover v ctx",
        "scope": "routed_context",
        "pretty_printed": False,
        "expands": "\\<gamma>\\<^sub>M (sg (Inl (v, ctx)))",
        "href": "Voblint/R.html#R.routed_context.cover%7Cconst",
    }
    data = {
        "base": "https://example.org/",
        "groups": {},
        "entries": [
            {
                "group": "shorthand",
                "reads": "the stores claimed at _v_",
                "meaning": "a claim",
                "forms": [form],
                "local": None,
            }
        ],
    }
    text = tool.render_readme(data)
    assert text.count("| Symbol |") == 1
    assert "| Shorthand |" not in text
    assert (
        "cover v ctx<br>In `routed_context`, input only, short for γ<sub>M</sub>"
        in text
    )


def _has_notation_command():
    return importlib.util.find_spec("isar_tools.project.notation") is not None


@pytest.mark.skipif(
    not _has_notation_command(), reason="isar-tools has no `project notation` yet"
)
def test_declarations_come_from_isar(tool, tmp_path, monkeypatch):
    (tmp_path / "ROOT").write_text("session Fake = HOL + theories Fake\n")
    (tmp_path / "Fake.thy").write_text(
        "theory Fake\n  imports Main\nbegin\n\n"
        'definition sq :: "nat => nat" ("_\\<^sup>2") where "sq n = n * n"\n'
        "locale L =\n  fixes g :: nat\nbegin\n"
        'abbreviation (input) cover :: "nat" where "cover \\<equiv> g"\n'
        "end\n\nend\n"
    )
    monkeypatch.setattr(tool, "REPO", tmp_path)
    # The fake session has no rendered theories, whatever build/ holds for the real one.
    monkeypatch.setattr(tool, "HTML", tmp_path / "isabelle-html")
    rows = tool.resolve_declarations(
        {
            "sq": {"name": "sq", "args": ["n"]},
            "cover": {"name": "L.cover", "args": []},
        },
        lenient=True,
    )
    assert rows["sq"]["symbol"] == "n\\<^sup>2"
    assert rows["cover"]["printed"] is False
    assert tool._decl(rows["cover"])["expands"] == "g"
