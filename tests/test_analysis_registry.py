"""Independently written compatibility expectations for the generated registration.

Everything else about the registration is derived from manifests/analyses.yaml, so
a check derived from that manifest too would only prove the generator is
self-consistent. The expectations below are written out by hand, from the
documented support policy: each domain's default, the pairings that are
deliberately unsupported, and the agreement between the two tables that decide
support. They are meant to fail when the manifest changes what the CLI offers,
including when the change is intended -- at which point the expectation is
updated deliberately, in the same commit.

The parsing here is deliberately independent of the generator's own rendering
helpers: it reads the emitted theory text the way a reader would.
"""

import re
import subprocess
import sys
from pathlib import Path

import pytest

ROOT = Path(__file__).resolve().parent.parent
SOLVERS = ["Solver_Join", "Solver_PerOrigin", "Solver_Warrow", "Solver_WarrowPerOrigin"]

RESOLVER_EQ = re.compile(
    r'"resolve_analysis_config\s*\\<lparr>\s*cfg_domain\s*=\s*(\w+),\s*'
    r'cfg_solver\s*=\s*(None|Some\s+\w+|_),\s*'
    r'cfg_context\s*=\s*(Ctx_None|Ctx_EntryState|Ctx_CallString\s+k)\s*\\<rparr>\s*'
    r'=\s*(.*?)"', re.S)

SOLVER_EQ = re.compile(
    r'"analyse_with_solver\s+(\w+)\s+(\w+)\s+p\s*=\s*(.*?)"', re.S)


@pytest.fixture(scope="module")
def generated(tmp_path_factory):
    out = tmp_path_factory.mktemp("generated")
    subprocess.run([sys.executable, "scripts/gen_analysis_assembly.py", "--out", str(out)],
                   cwd=ROOT, check=True, capture_output=True)
    return {p.stem: p.read_text() for p in out.glob("*.thy")}


def resolve(text, domain, solver, context, k=None):
    """The plan the generated resolver answers with, by first matching equation."""
    body = text.split("fun resolve_analysis_config ")[1].split("\ndefinition")[0]
    for dom, pat, ctx, rhs in RESOLVER_EQ.findall(body):
        pat = re.sub(r"\s+", " ", pat)
        ctx = ctx.split()[0]
        if dom != domain or ctx != context:
            continue
        if pat == "None" and solver is not None:
            continue
        if pat.startswith("Some ") and pat != "Some s" and pat.split()[1] != solver:
            continue
        if pat.startswith("Some ") and solver is None:
            continue
        answer = re.sub(r"\s+", " ", rhs).strip()
        if pat == "Some s" and solver:
            answer = re.sub(r"\bs\b", solver, answer)
        if context == "Ctx_CallString":
            guard = re.match(r"\(if k = 0 then None else (.*)\)$", answer)
            if guard:
                answer = "None" if k == 0 else guard.group(1)
            answer = re.sub(r"\bk\b", str(k), answer)
        return answer
    return "<no equation>"


def with_solver(text, domain, solver):
    body = text.split("fun analyse_with_solver ")[1].split("\nlemma")[0]
    for dom, slv, rhs in SOLVER_EQ.findall(body):
        if dom == domain and slv == solver:
            return re.sub(r"\s+", " ", rhs).strip()
    return "<no equation>"


# --- Defaults ---------------------------------------------------------------

@pytest.mark.parametrize("domain,plan", [
    ("Sign_Analysis", "Some (Plan_Sign Solver_Join)"),
    ("Interval_Analysis", "Some (Plan_Interval Solver_Warrow)"),
    ("Int_Analysis", "Some (Plan_Int Solver_Warrow)"),
    ("Parity_Analysis", "Some (Plan_Parity Solver_Join)"),
    ("Congruence_Analysis", "Some (Plan_Congruence Solver_Join)"),
])
def test_implicit_default_per_domain(generated, domain, plan):
    assert resolve(generated["Config_Tables"], domain, None, "Ctx_None") == plan


# --- Deliberate gaps --------------------------------------------------------

@pytest.mark.parametrize("domain", ["Sign_Analysis", "Parity_Analysis",
                                    "Congruence_Analysis"])
@pytest.mark.parametrize("solver", ["Solver_Warrow", "Solver_WarrowPerOrigin"])
def test_finite_lattices_reject_widening(generated, domain, solver):
    """Sign, Parity and Congruence carry a `widen`, but no solved table stands
    behind it.

    Congruence is here for a different reason than the other two. Its lattice is
    not finite -- the modulus is unbounded -- but its `widen` is plain join, and a
    strictly ascending chain of residue classes is a chain of proper divisors of
    the modulus, so join alone already terminates and a warrowing route would
    solve the same system by the same steps under a different name."""
    assert resolve(generated["Config_Tables"], domain, solver, "Ctx_None") == "None"
    assert with_solver(generated["Dispatch_Tables"], domain, solver) == "None"


@pytest.mark.parametrize("context,k", [("Ctx_EntryState", None), ("Ctx_CallString", 3)])
@pytest.mark.parametrize("solver", ["Solver_PerOrigin", "Solver_Warrow",
                                    "Solver_WarrowPerOrigin"])
def test_parity_publishes_contexts_at_join_only(generated, context, solver, k):
    """Parity offers both context modes, but only under the always-join rule."""
    cfg = generated["Config_Tables"]
    assert resolve(cfg, "Parity_Analysis", solver, context, k) == "None"
    assert resolve(cfg, "Parity_Analysis", None, context, k) != "None"
    assert resolve(cfg, "Parity_Analysis", "Solver_Join", context, k) != "None"


@pytest.mark.parametrize("solver", ["Solver_PerOrigin", "Solver_WarrowPerOrigin"])
def test_int_rejects_per_origin_at_a_context_but_not_at_none(generated, solver):
    cfg = generated["Config_Tables"]
    assert resolve(cfg, "Int_Analysis", solver, "Ctx_None") != "None"
    assert resolve(cfg, "Int_Analysis", solver, "Ctx_EntryState") == "None"
    assert resolve(cfg, "Int_Analysis", solver, "Ctx_CallString", 3) == "None"


@pytest.mark.parametrize("context,k", [("Ctx_EntryState", None), ("Ctx_CallString", 3)])
@pytest.mark.parametrize("solver", ["Solver_PerOrigin", "Solver_Warrow",
                                    "Solver_WarrowPerOrigin"])
def test_congruence_publishes_contexts_at_join_only(generated, context, solver, k):
    """Congruence offers both context modes, but only under the always-join rule.

    It publishes two disciplines at `Ctx_None` and one at each context, so
    per-origin is a real gap here rather than an oversight: the routed
    configurations in Congruence_Analyses are built over
    `TD_side_always_join_Interp` alone, and no solved table stands behind any
    other pairing."""
    cfg = generated["Config_Tables"]
    assert resolve(cfg, "Congruence_Analysis", solver, context, k) == "None"
    assert resolve(cfg, "Congruence_Analysis", "Solver_Join", context, k) != "None"


@pytest.mark.parametrize("solver", SOLVERS)
def test_interval_supports_every_solver_at_every_context(generated, solver):
    cfg = generated["Config_Tables"]
    assert resolve(cfg, "Interval_Analysis", solver, "Ctx_None") != "None"
    assert resolve(cfg, "Interval_Analysis", solver, "Ctx_EntryState") != "None"
    assert resolve(cfg, "Interval_Analysis", solver, "Ctx_CallString", 3) != "None"


@pytest.mark.parametrize("domain", ["Sign_Analysis", "Interval_Analysis",
                                    "Int_Analysis", "Parity_Analysis",
                                    "Congruence_Analysis"])
@pytest.mark.parametrize("solver", [None] + SOLVERS)
def test_call_string_zero_is_not_published(generated, domain, solver):
    """Every domain publishes a shortest bound of one today, so a zero-length
    call string resolves to no plan.

    `cs_route 0` is well-defined and finite, so this is a decision about what the
    CLI offers rather than a soundness constraint. Publishing it would return a
    call-string-keyed table whose contexts are all empty -- which is not
    `Ctx_None` -- so it is a behaviour change in its own right, and this
    expectation is what would have to be revised deliberately to make it."""
    assert resolve(generated["Config_Tables"], domain, solver, "Ctx_CallString", 0) == "None"


@pytest.mark.parametrize("domain", ["Sign_Analysis", "Interval_Analysis", "Int_Analysis",
                                    "Parity_Analysis", "Congruence_Analysis"])
def test_call_string_above_the_bound_is_published(generated, domain):
    """The guard rejects only the bound below the published minimum."""
    assert resolve(generated["Config_Tables"], domain, None, "Ctx_CallString", 3) != "None"


def test_resolver_tests_only_the_published_bound(generated):
    """What makes agreement at two sample bounds an argument about every bound.

    The resolver performs exactly one syntactic test on `k`, the guard for the
    shortest published bound. Every other occurrence passes `k` through
    opaquely, so no equation can distinguish one positive bound from another and
    checking `k = 0` against some `k > 0` covers the space."""
    body = generated["Config_Tables"].split("fun resolve_analysis_config ")[1]
    body = body.split("\ndefinition")[0]
    tests = set(re.findall(r"k\s*(?:=|<|>|\\<le>|\\<ge>|\\<noteq>)\s*\w+", body))
    assert tests == {"k = 0"}, tests


def test_applied_roles_reach_isabelle_as_one_argument(generated):
    """A domain whose operations carry a configuration argument, like Int's
    `refine_mode`, supplies the role as a constant and its arguments. The
    renderer quotes it so the interpretation still receives one argument, and
    the registry cannot express anything else -- there is no proof-text override
    behind this."""
    import subprocess
    import yaml
    manifest = yaml.safe_load((ROOT / "manifests/analyses.yaml").read_text())
    sys.path.insert(0, str(ROOT / "scripts"))
    import gen_analysis_assembly as gen

    domain = dict(manifest["domains"][0])
    domain["legacy"] = dict(domain["legacy"])
    domain["legacy"]["facts"] = {"tf_st": {"const": "tf_for", "args": ["Some_Mode"]}}
    rendered = gen.render_assembly(gen.Domain(domain), manifest["solvers"])
    assert '"tf_for Some_Mode"' in rendered

    # a fact takes no arguments, so applying one is a registry error
    domain["legacy"]["facts"] = {"init_gamma": {"const": "g", "args": ["m"]}}
    with pytest.raises(SystemExit):
        gen.validate(manifest, [gen.Domain(domain)])


# --- The two tables agree ---------------------------------------------------

@pytest.mark.parametrize("domain", ["Sign_Analysis", "Interval_Analysis",
                                    "Int_Analysis", "Parity_Analysis",
                                    "Congruence_Analysis"])
@pytest.mark.parametrize("solver", SOLVERS)
def test_dispatcher_and_resolver_agree_on_support(generated, domain, solver):
    """The gap this generation exists to close: a pairing the CLI resolves must
    be one the dispatcher can actually run, and the reverse."""
    resolves = resolve(generated["Config_Tables"], domain, solver, "Ctx_None") != "None"
    dispatches = with_solver(generated["Dispatch_Tables"], domain, solver) != "None"
    assert resolves == dispatches
