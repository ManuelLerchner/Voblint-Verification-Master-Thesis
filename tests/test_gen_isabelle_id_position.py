"""Pins scripts/gen_vimp_isabelle.py's identifier-position/markup shape --
not the presentation choices layered on top of it.

Every IDENT-typed grammar slot must generate as Isabelle's id_position
nonterminal (not plain id), and every role dest_id_position can classify
must report SOME markup (not NONE), so a source identifier's PIDE/
browser_info coloring keeps working end to end. Which markup category
each role reports (Markup.free/Markup.bound/Markup.skolem today) is a
presentation-policy choice documented and freely changeable in
IDENT_MARKUP -- e.g. swapping a bare category for real entity
definition/reference markup once a procedure-name registry exists needs
no grammar change and should not need this test's assertions to change
either. This suite only pins the structural invariant a color swap must
still satisfy: position survives, and roles that are meant to look
different still resolve to different report expressions.
"""

import importlib.util
import sys
from pathlib import Path

import pytest
import yaml

REPO_ROOT = Path(__file__).resolve().parent.parent
GRAMMAR_PATH = REPO_ROOT / "grammar" / "vimp.yaml"
GENERATOR_PATH = REPO_ROOT / "scripts" / "gen_vimp_isabelle.py"


def _load_generator():
    spec = importlib.util.spec_from_file_location("gen_vimp_isabelle", GENERATOR_PATH)
    module = importlib.util.module_from_spec(spec)
    sys.modules[spec.name] = module
    spec.loader.exec_module(module)
    return module


gen = _load_generator()
GRAMMAR = yaml.safe_load(GRAMMAR_PATH.read_text())

# (production name, rhs index) for every generated IDENT slot this test
# cares about, paired with its expected role. Hand-picked from
# grammar/vimp.yaml's productions rather than derived generically, so a
# production that silently starts/stops carrying an IDENT slot is caught
# by a KeyError/IndexError here rather than by this test quietly checking
# nothing.
VARIABLE_ROLE_SLOTS = [
    ("exp_var", 0),         # expression use
    ("stmt_assign", 0),     # assignment target
    ("stmt_callret", 0),    # return-value target -- also covers special
                             # calls (e.g. __voblint_nondet_int()), which
                             # parse as ordinary calls, not a dedicated
                             # production
]
CALLEE_ROLE_SLOTS = [
    ("stmt_call", 0),
    ("stmt_callret", 2),
]


def _rhs_of(name):
    for prod in GRAMMAR["productions"]:
        if prod["name"] == name:
            return prod["rhs"]
    raise AssertionError(f"no production named {name!r} in grammar/vimp.yaml")


@pytest.mark.parametrize("name,index", VARIABLE_ROLE_SLOTS)
def test_variable_role_slots_are_id_position(name, index):
    rhs = _rhs_of(name)
    assert rhs[index] == "IDENT"
    assert gen.ident_role(rhs, index) == "variable"
    assert gen.isabelle_type("IDENT") == "id_position"


@pytest.mark.parametrize("name,index", CALLEE_ROLE_SLOTS)
def test_callee_role_slots_are_also_id_position(name, index):
    # Both roles parse via id_position (position provenance is uniform);
    # only the reported markup differs by role. A regression here would
    # most likely mean someone reverted a callee slot to plain `id`,
    # silently dropping its source position again.
    rhs = _rhs_of(name)
    assert rhs[index] == "IDENT"
    assert gen.ident_role(rhs, index) == "callee"
    assert gen.isabelle_type("IDENT") == "id_position"


def test_formals_and_ids_list_items_are_id_position():
    # `ids` lists bare identifiers. `formals` lists `formal`, which since
    # formals gained kinds is a production of its own -- so the identifier
    # this test is about sits one level down, in every alternative of
    # `formal`. Following that indirection is the point: a kind annotation
    # in front of the name must not cost the name its source position.
    ids = next(p for p in GRAMMAR["productions"] if p["name"] == "ids")
    assert ids["list_of"] == "IDENT"

    formals = next(p for p in GRAMMAR["productions"] if p["name"] == "formals")
    assert formals["list_of"] == "formal"

    alts = [p for p in GRAMMAR["productions"] if p.get("result") == "formal"]
    assert alts, "no production produces a 'formal'"
    for alt in alts:
        assert "IDENT" in alt["rhs"], f"{alt['name']} binds no identifier"

    assert gen.isabelle_type("IDENT") == "id_position"


def test_every_ident_role_reports_something():
    # No role may silently opt out of reporting a position at all -- that
    # would be the "position captured but never surfaced" regression this
    # whole change exists to avoid. Which markup, specifically, is not
    # pinned here (see module docstring).
    for role, markup_expr in gen.IDENT_MARKUP.items():
        assert markup_expr.strip().startswith("SOME"), (
            f"IDENT_MARKUP[{role!r}] = {markup_expr!r} reports nothing; "
            "every role must report SOME markup, even a placeholder one"
        )


def test_variable_callee_and_global_markup_are_pairwise_distinguishable():
    # The point of having three roles instead of one is that they read
    # differently. Pin distinguishability, not the specific colors: this
    # still fails if a future edit collapses two roles onto the same
    # report expression by accident, but not if it swaps, say,
    # Markup.skolem for a real entity markup for the 'callee' role alone.
    variable, callee, global_ = (
        gen.IDENT_MARKUP["variable"],
        gen.IDENT_MARKUP["callee"],
        gen.IDENT_MARKUP["global"],
    )
    assert len({variable, callee, global_}) == 3, gen.IDENT_MARKUP


def test_dest_id_position_takes_a_markup_option_first():
    # Structural check on the generated ML shape itself, not just the
    # Python-side table: every call site must thread a `report_markup`
    # argument through dest_id_position, matching DEST_ID_POSITION's own
    # `report_markup ctxt term` signature. A stale call site (`ctxt` as
    # the first argument again) would compile-fail in Isabelle, but this
    # catches the same drift at generation time, before an I/Q round trip.
    theory = gen.gen_theory_file(GRAMMAR)
    assert "fun dest_id_position report_markup ctxt " in theory
    assert "dest_id_position ctxt " not in theory
