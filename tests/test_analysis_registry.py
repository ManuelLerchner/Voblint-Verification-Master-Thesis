"""Independently written expectations for the generated registration.

Everything else about the registration is derived from manifests/analyses.yaml, so
a check derived from that manifest too would only prove the generator is
self-consistent. The expectation below is written out by hand from the support
policy: every domain answers every global update rule at every context route, with
no default and no gap. The rule is a parameter of one interpretation per route
rather than a list of registered disciplines, so a gap cannot be expressed; what
can still go wrong is a route losing its rule-parametric registration, or the
run surface pinning a rule instead of passing it through.

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
    "Int_Analysis": ("Int", "int"),
    "Parity_Analysis": ("Parity", "parity"),
    "Congruence_Analysis": ("Congruence", "congruence"),
}
ROUTES = [("rule", "unit_dg_analysis", "r"),
          ("es_rule", "routed_dg_analysis", "r"),
          ("cs_rule", "routed_dg_analysis", "k r")]


@pytest.fixture(scope="module")
def generated(tmp_path_factory):
    out = tmp_path_factory.mktemp("generated")
    subprocess.run([sys.executable, "scripts/gen_analysis_assembly.py", "--out", str(out)],
                   cwd=ROOT, check=True, capture_output=True)
    return {p.stem: p.read_text() for p in out.glob("*.thy")}


def interpretation_params(text, name):
    """The `for` parameters of `global_interpretation name`, or None if absent."""
    m = re.search(r"global_interpretation\s+" + re.escape(name) + r":\s*(\w+)(.*?)\nproof",
                  text, re.S)
    if not m:
        return None
    params = re.search(r"\n\s*for\s+([\w ]+?)\s*$", m.group(2))
    return m.group(1), params.group(1).split() if params else []


@pytest.mark.parametrize("domain", DOMAINS)
@pytest.mark.parametrize("suffix,locale,params", ROUTES)
def test_every_route_registers_a_rule_parametric_instance(generated, domain, suffix,
                                                          locale, params):
    """One interpretation per (domain, route) with the update rule left free."""
    _, prefix = DOMAINS[domain]
    name = f"{prefix}_{suffix}"
    found = [interpretation_params(text, name) for text in generated.values()]
    found = [f for f in found if f]
    assert len(found) == 1, f"{name}: {len(found)} registrations"
    assert found[0] == (locale, params.split())


def test_run_surface_passes_the_rule_through():
    """`analysis_result` answers every domain at every context with one equation
    each, and none of them names a particular rule."""
    text = (ROOT / "src/Executable_Surface/CLI/Analysis_Run.thy").read_text()
    body = text.split("fun analysis_result ")[1].split("\ndatatype")[0]
    equations = re.findall(r'"analysis_result\s+(\w+)\s+(\w+)\s+(\(Ctx_CallString k\)|Ctx_\w+)',
                           body)
    assert sorted(equations) == sorted(
        (domain, "r", ctx) for domain in DOMAINS
        for ctx in ("Ctx_None", "Ctx_EntryState", "(Ctx_CallString k)"))
    assert not re.search(r"\bGlobals_\w+", body)


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
