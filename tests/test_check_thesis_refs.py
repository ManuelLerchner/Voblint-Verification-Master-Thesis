"""Check declaration kinds without treating local bindings as global entities."""

import importlib.util
from pathlib import Path

import pytest

REPO = Path(__file__).resolve().parent.parent


@pytest.fixture
def inventory(tmp_path, monkeypatch):
    monkeypatch.syspath_prepend(str(REPO / "scripts"))
    spec = importlib.util.spec_from_file_location(
        "thesis_refs", REPO / "scripts/check_thesis_refs.py"
    )
    checker = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(checker)
    monkeypatch.setattr(checker, "REPO", tmp_path)
    # HOL's own theories are not what these tests are about, and slow to read.
    monkeypatch.setattr(checker, "isabelle_home", lambda: None)
    source = tmp_path / "src/Example.thy"
    source.parent.mkdir()
    (tmp_path / "ROOT").write_text(
        'session Test = HOL + directories "src" theories Example\n'
    )

    def scan(text):
        source.write_text(f"theory Example imports Main begin\n{text}\nend\n")
        return checker.build_inventory()[0]

    return scan


def test_class_parameters_and_quotient_type(inventory):
    kinds = inventory("""
class executable_domain = order +
  fixes is_empty :: "'a => bool"
    and is_full :: "'a => bool"
class sound_domain = executable_domain +
  fixes gamma :: "'a => int set"
  assumes sound: "is_empty x ==> gamma x = {}"

locale local_context =
  fixes private_lookup :: "nat => nat"
    and private_test :: "nat => bool"
begin
lemma example: "True"
  by simp
end
quotient_type 'a resolved_st_q = "'a list" / "equiv"
  by simp
""")
    for name in ("is_empty", "is_full", "gamma"):
        assert kinds[name] == {"const"}
    assert kinds["resolved_st_q"] == {"type"}
    assert kinds["sound_domain"] == {"locale"}
    assert "private_lookup" not in kinds
    assert "private_test" not in kinds


def test_constructor_layouts_and_declaration_boundaries(inventory):
    kinds = inventory("""
datatype ('a, 'b) key =
  Activation_Seed 'a
| Analysis_Global 'b

datatype mode = Sign_Analysis | Interval_Analysis

record row =
  row_value :: nat

  definition after_row :: nat where "after_row = 0"
lemma local_annotation:
  fixes not_a_selector :: nat
  shows "True"
  by simp
""")
    for name in (
        "Activation_Seed",
        "Analysis_Global",
        "Sign_Analysis",
        "Interval_Analysis",
        "row_value",
        "after_row",
    ):
        assert kinds[name] == {"const"}
    assert "not_a_selector" not in kinds
    assert kinds["key"] == {"type"}


def test_documentation_and_terms_do_not_declare_entities(inventory):
    kinds = inventory(r"""
(* outer (* nested *)
class fake_class = fixes fake_parameter :: nat
*)
text \<open>
datatype fake_type = Fake_Constructor
\<close>
definition real_constant :: nat where
  "real_constant = (let phantom = 0 in phantom)"
lemma "True"
  by simp
class actual_class =
  fixes actual_parameter :: "'a => bool"
  assumes actual_law: "actual_parameter x"
""")
    assert kinds["real_constant"] == {"const"}
    assert kinds["actual_parameter"] == {"const"}
    for name in ("fake_class", "fake_parameter", "fake_type", "Fake_Constructor", "by"):
        assert name not in kinds


def test_manifest_facts_are_citations(tmp_path, monkeypatch):
    # The oracle audit table cites every facts.toml key; no .typ spells them out.
    monkeypatch.syspath_prepend(str(REPO / "scripts"))
    spec = importlib.util.spec_from_file_location(
        "thesis_refs", REPO / "scripts/check_thesis_refs.py"
    )
    checker = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(checker)
    shared = tmp_path / "shared"
    (shared / "generated").mkdir(parents=True)
    (shared / "facts.toml").write_text('[facts.audited]\nwhy = "table row"\n')
    refs = checker.generated_citations(tmp_path)
    assert [(kind, name) for _, _, kind, name in refs] == [("thm", "audited")]


def test_inductive_rules_are_facts(inventory):
    kinds = inventory("""
inductive
  step :: "nat => nat => bool"
    ("_ ~> _" 50)
  for bound :: nat
where
  Base: "step 0 1"
| Next:
    "step n m ==> step (Suc n) (Suc m)"
""")
    assert kinds["step"] == {"const"}
    assert kinds["step.Base"] == {"thm"}
    assert kinds["step.Next"] == {"thm"}
    assert "step.bound" not in kinds


def test_display_and_thy_keep_the_cited_name(tmp_path, monkeypatch):
    monkeypatch.syspath_prepend(str(REPO / "scripts"))
    spec = importlib.util.spec_from_file_location(
        "thesis_refs", REPO / "scripts/check_thesis_refs.py"
    )
    checker = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(checker)
    (tmp_path / "shared" / "generated").mkdir(parents=True)
    (tmp_path / "example.typ").write_text(
        'isaconst("loc.q", display: "q")\n'
        'isathm("loc.f", thy: "T", display: "f")\n'
        'isatype("loc.t", display: "t", thy: "T")\n'
        'isalocale(\n  "loc.l",\n  thy: "T",\n  display: "l",\n)\n'
    )
    refs = [(k, n) for _, _, k, n in checker.collect_refs(tmp_path)]
    assert refs == [
        ("const", "loc.q"),
        ("thm", "loc.f"),
        ("type", "loc.t"),
        ("locale", "loc.l"),
    ]


def test_consts_selectors_and_definition_facts(inventory):
    kinds = inventory(r"""
consts gamma\<^sub>S :: "'s => nat set"
datatype trace = Root | Call (ltr_caller: trace) nat
class c = fixes op :: "'a => nat"
instantiation nat :: c begin
definition op_nat [simp]: "op (n::nat) = n"
instance ..
end
""")
    assert kinds["gamma\\<^sub>S"] == {"const"}
    assert kinds["Root"] == kinds["Call"] == kinds["ltr_caller"] == {"const"}
    # `definition name [simp]: "eq"` names the defining fact, not a constant.
    assert "const" not in kinds.get("op_nat", set())


def test_statement_environment_names_its_fact():
    spec = importlib.util.spec_from_file_location(
        "thesis_refs", REPO / "scripts/check_thesis_refs.py"
    )
    checker = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(checker)
    text = '#corollary(name: [Per policy], isa: "fun_route_sound")[\n  body\n]'
    m = checker.STATEMENT_ENV.search(text)
    assert m is not None
    assert m.group(1) == "corollary"
    assert checker.ISA_ARG.search(m.group(2)).group(1) == "fun_route_sound"
