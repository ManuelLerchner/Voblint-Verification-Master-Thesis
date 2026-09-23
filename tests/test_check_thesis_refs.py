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
    source = tmp_path / "src/Example.thy"
    source.parent.mkdir()

    def scan(text):
        source.write_text(text)
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
