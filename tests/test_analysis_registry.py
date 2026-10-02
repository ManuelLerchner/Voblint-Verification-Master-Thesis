"""Independently written expectations for the generated registration.

Everything else about the registration is derived from manifests/analyses.yaml, so
a check derived from that manifest too would only prove the generator is
self-consistent. The expectation below is written out by hand from the support
policy: the CLI runs every analysis as a field of the combined state, which
registers every context route once, with the activation list and the rule as
parameters, so every activation answers every global update rule at every route,
with no default and no gap. Each domain registers its unit route, whose facts the
combined state cites.
What can still go wrong is a route losing its parametric registration, a domain
missing from the combined state, or the run surface pinning a rule instead of
passing it through.

The parsing here is deliberately independent of the generator's own rendering
helpers: it reads the emitted theory text the way a reader would.
"""

import re
import subprocess
import sys
from pathlib import Path

import pytest

ROOT = Path(__file__).resolve().parent.parent
DOMAINS = {
    "Sign_Analysis": ("Sign", "sign"),
    "Interval_Analysis": ("Interval", "interval"),
    "Int_Analysis Refine_Fixpoint": ("Int_Fixpoint", "int_fixpoint"),
    "Int_Analysis Refine_Once": ("Int_Once", "int_once"),
    "Int_Analysis Refine_Never": ("Int_Never", "int_never"),
    "Parity_Analysis": ("Parity", "parity"),
    "Congruence_Analysis": ("Congruence", "congruence"),
}
# Analyses that run only as a field of the combined state, with no pointwise
# registration of their own.
FIELD_ONLY = {"Order_Analysis"}
MCP_ROUTES = [
    ("mcp_rule", "dg_analysis", "as r"),
    ("mcp_es_rule", "dg_analysis", "as r"),
    ("mcp_cs_rule", "dg_analysis", "as k r"),
]


@pytest.fixture(scope="module")
def generated(tmp_path_factory):
    out = tmp_path_factory.mktemp("generated")
    subprocess.run(
        [sys.executable, "scripts/gen_analysis_assembly.py", "--out", str(out)],
        cwd=ROOT,
        check=True,
        capture_output=True,
    )
    return {p.stem: p.read_text() for p in out.glob("*.thy")}


def interpretation_params(text, name):
    """The `for` parameters of `global_interpretation name`, or None if absent."""
    m = re.search(
        r"global_interpretation\s+"
        + re.escape(name)
        + r":\s*(\w+)(.*?)\n\s*(?:proof|by)\b",
        text,
        re.S,
    )
    if not m:
        return None
    params = re.search(r"\n\s*for\s+([\w ]+?)\s*$", m.group(2))
    return m.group(1), params.group(1).split() if params else []


@pytest.mark.parametrize("domain", DOMAINS)
def test_every_domain_registers_its_unit_route(generated, domain):
    """The unit registration, with the update rule left free, whose component and
    entry-state soundness the combined state cites."""
    _, prefix = DOMAINS[domain]
    name = f"{prefix}_rule"
    found = [interpretation_params(text, name) for text in generated.values()]
    found = [f for f in found if f]
    assert len(found) == 1, f"{name}: {len(found)} registrations"
    assert found[0] == ("dg_analysis_exec", ["r"])


@pytest.mark.parametrize("name,locale,params", MCP_ROUTES)
def test_the_combined_state_registers_every_route(name, locale, params):
    """One interpretation per route, with the activation list and the rule free."""
    text = (ROOT / "src/Executable_Surface/CLI/MCP_Analyses.thy").read_text()
    assert interpretation_params(text, name) == (locale, params.split())


def test_every_domain_is_a_field_of_the_combined_state(generated):
    """The analyses a caller may activate are exactly the registered domains."""
    body = generated["MCP_Carrier"].split("datatype analysis_domain =")[1]
    body = body.split("\n\n")[0]
    constructors = {d.split()[0] for d in [*DOMAINS, *FIELD_ONLY]}
    assert sorted(re.findall(r"\w+_Analysis", body)) == sorted(constructors)


def test_run_surface_passes_the_rule_through():
    """`analysis_report_of` answers every activation list at every context with one
    equation each, whatever the program-globals placement, and none of them names a
    particular rule, domain or placement."""
    text = (ROOT / "src/Executable_Surface/CLI/Analysis_Run.thy").read_text()
    body = text.split("fun analysis_report_of ")[1].split("\nsubsection")[0]
    equations = re.findall(
        r'"analysis_report_of \(Analysis_Config\s+(\w+)\s+(\w+)\s+'
        r"(\(Ctx_CallString k\)|Ctx_\w+)\s+(\w+)\)",
        body,
    )
    assert sorted(equations) == sorted(
        ("as", "r", ctx, "pg")
        for ctx in ("Ctx_None", "Ctx_EntryState", "(Ctx_CallString k)")
    )
    assert not re.search(r"\bGlobals_\w+", body)
    assert not re.search(r"\bProgram_Globals_\w+", body)
    assert not re.search(r"\b\w+_Analysis\b", body)


def test_applied_roles_reach_isabelle_as_one_argument():
    """A domain whose operations carry a configuration argument, like Int's
    `refine_mode`, supplies the role as a constant and its arguments. The
    renderer quotes it so the interpretation still receives one argument, and
    the registry cannot express anything else -- there is no proof-text override
    behind this."""
    import yaml

    manifest = yaml.safe_load((ROOT / "manifests/analyses.yaml").read_text())
    sys.path.insert(0, str(ROOT / "scripts"))
    import gen_analysis_assembly as gen

    domain = dict(manifest["domains"][0])
    domain["roles"] = {"tf_st": {"const": "tf_for", "args": ["Some_Mode"]}}
    assert '"tf_for Some_Mode"' in gen.render(gen.Domain(domain))

    # a fact takes no arguments, so applying one is a registry error
    domain["roles"] = {"init_gamma": {"const": "g", "args": ["m"]}}
    with pytest.raises(SystemExit):
        gen.validate([gen.Domain(domain)])
