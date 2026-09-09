#!/usr/bin/env python3
"""Generates the analysis registration theories from assembly/analyses.yaml.

Three outputs, one registry:

  src/Analyses/<Domain>/generated/<Domain>_Assembly.thy   the unit-context
      instances, one `global_interpretation` of `unit_dg_analysis` per
      published solver discipline
  src/Executable_Surface/CLI/generated/Dispatch_Tables.thy   `analyse` and the
      three domain/solver tables beside it
  src/Executable_Surface/CLI/generated/Config_Tables.thy     the resolver over
      domain, solver and context

What is generated is registration, never mathematics. Every obligation is
discharged by citing a fact the manifest only names: the domain's own, or a
`TD_side_upd_rule` instance for the three solver contracts, since solver
correctness belongs to the solver. No axiom, no `sorry`, no assumption.

The manifest states policy -- which implementation, which combinations, which
default, which capabilities. Everything else here is convention: theory names,
paths, imports, binders, published prefixes, which route publishes the full
name set, and the proof text, which is the same for every domain.

Usage:
  python3 scripts/gen_analysis_assembly.py [--check] [--out DIR] [manifest]

`--out DIR` renders every output, adopted or not, so an unadopted one can be
read and diffed without touching the tree. Without it, only what the registry
marks adopted is written or compared, so the drift gate never demands a file
the tree does not yet carry.
"""

import argparse
import difflib
import re
import sys
from pathlib import Path

import yaml

MAX_LINE = 100

SYMBOL = re.compile(r"\\<\^?[A-Za-z][A-Za-z0-9_']*>")

# What may appear in an applied role. A constant or constructor name, nothing
# else: no spaces, no quotes, no cartouches, no application of its own. The
# registry cannot express a term the generator did not build.
ISABELLE_NAME = re.compile(r"^[A-Za-z][A-Za-z0-9_'.]*$")


def symbol_len(line):
    """Length in Isabelle symbols, which is what the layout rule counts."""
    return len(SYMBOL.sub("x", line))


# Published name -> locale constant. The production route publishes all of it;
# a sibling discipline publishes what makes its own run observable.
DEFINES_FULL = [
    ("spec", "analysis_spec"), ("root_query", "root_query"),
    ("equations", "equations"), ("solution", "solution"),
    ("terminates", "terminates"), ("vars", "sol_vars"), ("env", "sol_env"),
    ("result", "result"), ("globals", "globals"), ("solved", "solved"),
    ("state_at", "state_at"), ("report", "report"),
    ("report_with_state", "report_with_state"),
]
DEFINES_SIBLING = [
    ("solution", "solution"), ("terminates", "terminates"),
    ("vars", "sol_vars"), ("result", "result"),
    ("state_at", "state_at"), ("report", "report"),
]

SOLVER_ORDER = ["always_join", "per_origin", "warrowing_apinis",
                "warrowing_per_origin"]

CONTEXT_TERMS = {
    "none": ("Ctx_None", ""),
    "entry_state": ("Ctx_EntryState", "_EntryState"),
    "call_string": ("Ctx_CallString k", "_CallString"),
}
CONTEXT_ORDER = ["none", "entry_state", "call_string"]

ASSEMBLY_IMPORTS = ['"Voblint_Result.Unit_DG_Analysis"',
                    '"Voblint_Solver.TD_Solver_Bridge"',
                    '"TD.TD_side_upd_rule"']

GENERATED_NOTICE = (
    "GENERATED FILE. Source: \\<^verbatim>\\<open>assembly/analyses.yaml\\<close>; generator:\n"
    "\\<^verbatim>\\<open>scripts/gen_analysis_assembly.py\\<close>. Regenerate with the generator\n"
    "rather than hand-editing; a drift check compares regenerated output against\n"
    "this file.\n"
)


class Domain:
    """One registered domain, with every derived name resolved.

    A `legacy` entry overrides a derived name and nothing else: it exists to
    map this interface onto spellings that predate it, and each override is a
    rename waiting to happen.
    """

    def __init__(self, entry):
        self.entry = entry
        self.name = entry["name"]
        self.value_type = entry["value_type"]
        self.tag = entry["tag"]
        self.routes = entry["routes"]
        self.default = self.routes[0]
        self.has_assembly = entry.get("assembly", True)
        # Adoption is registry data, like `cli_adopted`: an output is compared
        # by the drift gate only once the tree actually carries it, so a commit
        # that adds the generator does not demand files a later commit adds.
        self.adopted = entry.get("adopted", False)
        self.contexts = entry.get("contexts", {})
        legacy = entry.get("legacy", {})
        self.legacy = legacy
        self.impl = legacy.get("impl_prefix", self.name.lower())
        self.theory = f"{self.name}_Assembly"
        self.path = f"src/Analyses/{self.name}/generated/{self.theory}.thy"
        self.constructor = f"{self.name}_Analysis"
        self.plan = f"Plan_{self.name}"

    def imports(self):
        own = [f"{self.name}_Classify", f"{self.name}_Transfer",
               f"{self.name}_Sound"]
        return own + ASSEMBLY_IMPORTS + self.legacy.get("extra_imports", [])

    def binder(self, route):
        return self.legacy.get("binders", {}).get(route, f"{self.impl}_{route}")

    def prefix(self, route):
        return self.legacy.get("prefixes", {}).get(route, f"{self.impl}_{route}")

    def report(self, route, with_state=False):
        spec = self.legacy.get("routes", {}).get(route)
        key = "report_with_state" if with_state else "report"
        if spec and key in spec:
            return spec[key]
        return f"{self.binder(route)}.{key}"

    def facts(self):
        """The interface roles, spelled the domain's way.

        `legacy.facts` overrides a role for a domain whose own theorem is not in
        registration shape: the domain keeps the stronger statement and names a
        corollary here, which is what lets the generated proof text stay the
        same for every domain.

        A role may also be an application rather than a bare name --
        `{const: int_tf_st_for, args: [Refine_Fixpoint]}` -- for a domain whose
        operations carry a configuration argument. The renderer quotes it so it
        reaches Isabelle as one argument; nothing here is free proof text.
        """
        i = self.impl
        legacy = self.legacy
        roles = {
            "tf_st": f"{i}_tf_st_for", "enter_st": f"{i}_enter_st_for",
            "init_st": f"cinit_{i}_st", "skip": f"skip_{i}",
            "assign": f"assign_{i}", "special": f"special_{i}",
            "branch": f"branch_{i}", "body": f"body_{i}",
            "return": f"return_{i}", "enter_ci": f"enter_{i}_ci_for",
            "event": f"event_{i}",
            "transfer_sound": f"{i}_is_sound_transfer_for",
            "tf_commute": f"{i}_tf_st_for_commute",
            "tf_abs_def": f"{i}_tf_abs_def",
            "enter_commute": f"{i}_enter_st_for_commute",
            "classifier": legacy.get("classifier", f"{i}_classify_check"),
            "init_gamma": legacy.get("init_gamma", f"{i}_cinit_gamma"),
        }
        roles.update(legacy.get("facts", {}))
        return roles


def fill(body, width=85):
    """Re-wrap generated prose so a longer domain or route list cannot push a
    line past the layout rule. Blank lines separate paragraphs; a line that is
    already short and ends a paragraph keeps its break."""
    out = []
    for para in body.split("\n\n"):
        words, line = para.split(), ""
        for w in words:
            if line and symbol_len(f"{line} {w}") > width:
                out.append(line)
                line = w
            else:
                line = f"{line} {w}" if line else w
        if line:
            out.append(line)
        out.append("")
    return "\n".join(out[:-1])


def role_term(role):
    """A role in term position: a bare name, or a quoted application.

    An applied role must be one argument to the interpretation, and Isabelle
    reads a quoted term as one argument. Only `const` and `args` are honoured,
    so a role can never smuggle in arbitrary syntax.
    """
    if isinstance(role, dict):
        args = " ".join(str(a) for a in role["args"])
        return f'"{role["const"]} {args}"'
    return role


def role_name(role):
    """A role in fact position. Facts take no arguments, so an application here
    is a registry error rather than something to render."""
    if isinstance(role, dict):
        raise ValueError(f"fact role cannot be applied: {role}")
    return role


def text_block(body, indent="  "):
    lines = ["text \\<open>"]
    for line in body.rstrip("\n").split("\n"):
        lines.append(f"{indent}{line}" if line else "")
    lines.append("\\<close>")
    return lines


def rule_step(rule, lead="    by (rule ", tail=")"):
    one = f"{lead}{rule}{tail}"
    if symbol_len(one) <= MAX_LINE:
        return [one]
    head, _, bracket = rule.partition("[")
    return [f"{lead}{head}", f"          [{bracket}{tail}"]


def equation(head, body, bar):
    lead = "| " if bar else "  "
    one = f'{lead}"{head} = {body}"'
    if symbol_len(one) <= MAX_LINE:
        return [one]
    return [f'{lead}"{head} =', f'     {body}"']


def statement(text, indent="  "):
    one = f'{indent}"{text}"'
    if symbol_len(one) <= MAX_LINE:
        return [one]
    lhs, _, rhs = text.partition(" = ")
    return [f'{indent}"{lhs} =', f'{indent}     {rhs}"']


def interpretation(dom, route, solvers):
    """One `global_interpretation`, with the same ten discharges every time."""
    f = dom.facts()
    interp = solvers[route]["interp"]
    binder, prefix = dom.binder(route), dom.prefix(route)
    binds = DEFINES_FULL if route == dom.default else DEFINES_SIBLING

    term = {k: role_term(v) for k, v in f.items()}
    out = [
        f"global_interpretation {binder}: unit_dg_analysis",
        f"    {term['tf_st']} {term['enter_st']} {term['init_st']}",
        f"    {interp}_solve",
        f'    "{interp}.solve_dom TYPE((unit, unit) routed_gk)',
        f"       TYPE(({dom.value_type} exec_dg_st lifted,"
        f" {dom.value_type} exec_dg_st lifted) dg_state)\"",
        f"    bot {term['classifier']}",
    ]
    # The operations. The two-line split reads best and is what a domain with
    # bare names gets; a domain that configures its operations has quoted, longer
    # roles, so fall back to packing at the layout limit.
    step = [term[k] for k in ["skip", "assign", "special", "branch", "body", "return"]]
    tail = [term["enter_ci"], term["event"], f"{interp}_solve_c"]
    pair = ["    " + " ".join(step), "    " + " ".join(tail)]
    if all(symbol_len(l) <= MAX_LINE for l in pair):
        out += pair
    else:
        line = "   "
        for op in step + tail:
            if symbol_len(f"{line} {op}") > MAX_LINE:
                out.append(line)
                line = "   "
            line = f"{line} {op}"
        out.append(line)
    out += [
        "  defines",
    ]
    for i, (published, const) in enumerate(binds):
        out.append(f"    {'' if i == 0 else 'and '}{prefix}_{published}"
                   f" = {binder}.{const}")

    out += [
        "proof (rule unit_dg_analysis.intro, goal_cases)",
        f"  case (1 gs) show ?case by (rule {role_name(f['transfer_sound'])})",
        "next",
        "  case (2 gs a s) then show ?case",
        "    unfolding fun_of_exec_dg_st_for_def",
        f"    by (rule {role_name(f['tf_commute'])}[unfolded {role_name(f['tf_abs_def'])}])",
        "next",
        "  case (3 gs ci s) show ?case",
        f"    unfolding fun_of_exec_dg_st_for_def by (rule {role_name(f['enter_commute'])})",
        "next",
        "  case (4 eqs x) then show ?case",
    ]
    out += rule_step(f"{interp}.partial_post_solution[OF _ surjective_pairing]")
    out += ["next", "  case (5 eqs x) then show ?case"]
    out += rule_step(f"{interp}.finite_stabl_solve")
    out += [
        "next",
        f"  case (6 c d s) then show ?case by (rule {role_name(f['classifier'])}_proved)",
        "next",
        f"  case (7 c d s) then show ?case by (rule {role_name(f['classifier'])}_refuted)",
        "next",
        "  case 8 show ?case by (rule refl)",
        "next",
        f"  case (9 gs) show ?case by (rule {role_name(f['init_gamma'])})",
        "next",
        "  case (10 eqs x) then show ?case",
    ]
    out += rule_step(f"{interp}.solve_dom_of_solve_c")
    out.append("qed")
    return out


def equations_eq_lemma(dom, route):
    binder, prefix = dom.binder(route), dom.prefix(route)
    pbinder, pprefix = dom.binder(dom.default), dom.prefix(dom.default)
    return [
        f'lemma {prefix}_equations_eq: "{binder}.equations = {pprefix}_equations"',
        "  by (rule ext)+",
        f"     (simp add: {binder}.equations_def {pbinder}.equations_def",
        f"        {binder}.analysis_spec_def {pbinder}.analysis_spec_def)",
    ]


def assembly_header(dom):
    routes = ", ".join(f"\\<open>{r}\\<close>" for r in dom.routes)
    plural = "instance" if len(dom.routes) == 1 else "instances"
    return f"""
{dom.name} at the context-insensitive route: {len(dom.routes)} {plural} of
\\<^locale>\\<open>unit_dg_analysis\\<close>, one per published solver discipline
({routes}), the first being the production default. The equation system, the
solve, the reader, the result table, the report and every soundness endpoint
come from that locale; this theory only names {dom.name}'s own implementation
and facts and chooses the disciplines.

Every obligation is discharged by citing a handwritten fact: {dom.name}'s own,
or, for the three solver contracts, a \\<^locale>\\<open>TD_side_upd_rule\\<close> instance.
Only those three mention the update rule, which is why a second discipline costs
a change of solver name and nothing else. Why {dom.name} publishes these
disciplines and not others is recorded in its README, not here.
"""


def render_assembly(dom, solvers):
    out = [f"theory {dom.theory}", "  imports"]
    out += [f"    {imp}" for imp in dom.imports()]
    out += ["begin", ""]
    for c in dom.legacy.get("hide_consts", []):
        out += [f"hide_const {c}", ""]
    out += [f"section \\<open>{dom.name} through the shared unit-context assembly\\<close>", ""]
    out += text_block(GENERATED_NOTICE + "\n" + fill(assembly_header(dom))) + [""]

    for route in dom.routes:
        out += [f"subsection \\<open>{solvers[route]['title']}\\<close>", ""]
        out += interpretation(dom, route, solvers) + [""]
        if route == dom.default:
            out += text_block(
                "A named \\<^type>\\<open>dg_spec\\<close> that code generation can reach declares"
                " its own\nunfolding, next to the definition, so a specification never has to"
                " be given a\nmost general ML type.") + [""]
            out += [f"declare {dom.prefix(route)}_spec_def [code_unfold]", ""]

    siblings = dom.routes[1:]
    if siblings:
        out += [f"subsection \\<open>One equation system, {len(dom.routes)} disciplines\\<close>", ""]
        out += text_block(
            "The pipeline builds its equations from the transfer parameters alone and the\n"
            "solver parameter never reaches them, so every discipline above solves the\n"
            "identical system. Stated, not asserted.") + [""]
        for route in siblings:
            out += equations_eq_lemma(dom, route) + [""]

    out.append("end")
    return "\n".join(out) + "\n"


# --- The dispatcher's tables -------------------------------------------------

def render_cli(doms, solvers, cli):
    ctor = {k: v["constructor"] for k, v in solvers.items()}

    out = [f"theory {cli['theory']}", "  imports"]
    out += [f"    {imp}" for imp in cli["imports"]]
    out += ["begin", "",
            "section \\<open>The dispatcher's domain and solver tables\\<close>", ""]
    out += text_block(GENERATED_NOTICE + """
A pairing of domain and solver discipline is supported exactly when the registry
publishes a route for it, and answers \\<^const>\\<open>None\\<close> otherwise. The four
tables below are that one list, read four ways; keeping them in step is what the
generator is for.
""") + [""]

    out += ["fun analyse :: \"analysis_domain \\<Rightarrow> imp_prog"
            " \\<Rightarrow> check_report_entry list\" where"]
    for i, d in enumerate(doms):
        out += equation(f"analyse {d.constructor} p", f"{d.report(d.default)} p", i > 0)
    out.append("")

    out += ["fun analyse_with_solver ::",
            "    \"analysis_domain \\<Rightarrow> solver_choice \\<Rightarrow> imp_prog",
            "       \\<Rightarrow> check_report_entry list option\" where"]
    first = True
    for d in doms:
        for route in SOLVER_ORDER:
            body = f"Some ({d.report(route)} p)" if route in d.routes else "None"
            out += equation(f"analyse_with_solver {d.constructor} {ctor[route]} p",
                            body, not first)
            first = False
    out.append("")

    for d in doms:
        out += [f"lemma analyse_with_solver_{d.name.lower()}_default:"]
        out += statement(f"analyse_with_solver {d.constructor} {ctor[d.default]} p"
                         f" = Some (analyse {d.constructor} p)")
        out += ["  by simp", ""]

    out += ["fun analyse_with_state ::",
            "    \"analysis_domain \\<Rightarrow> solver_choice \\<Rightarrow> imp_prog",
            "       \\<Rightarrow> (pp \\<times> exp \\<times> check_result \\<times> bool",
            "             \\<times> abstract_value abs_state) list option\" where"]
    first = True
    for d in doms:
        for route in SOLVER_ORDER:
            body = (f"Some (tag_states {d.tag} ({d.report(route, True)} p))"
                    if route in d.routes else "None")
            out += equation(f"analyse_with_state {d.constructor} {ctor[route]} p",
                            body, not first)
            first = False
    out.append("")

    out += ["lemma analyse_with_state_some_iff_with_solver:",
            "  \"(analyse_with_state d s p = None) = (analyse_with_solver d s p = None)\"",
            "  by (cases d; cases s) simp_all", ""]

    out += ["fun analyse_with_state_default ::",
            "    \"analysis_domain \\<Rightarrow> imp_prog",
            "       \\<Rightarrow> (pp \\<times> exp \\<times> check_result \\<times> bool",
            "             \\<times> abstract_value abs_state) list\" where"]
    for i, d in enumerate(doms):
        out += equation(f"analyse_with_state_default {d.constructor} p",
                        f"tag_states {d.tag} ({d.report(d.default, True)} p)", i > 0)
    out.append("")

    out += ["lemma analyse_with_state_default_eq:"]
    for d in doms:
        out += statement(f"analyse_with_state {d.constructor} {ctor[d.default]} p"
                         f" = Some (analyse_with_state_default {d.constructor} p)")
    out += ["  by simp_all", "", "end"]
    return "\n".join(out) + "\n"


# --- The resolver ------------------------------------------------------------

def resolver_equation(dom, ctx, solver_pat, plan, bar):
    ctx_term, _ = CONTEXT_TERMS[ctx]
    lead = "| " if bar else "  "
    pat = (f"\\<lparr> cfg_domain = {dom.constructor}, cfg_solver = {solver_pat},"
           f" cfg_context = {ctx_term} \\<rparr>")
    head = f"resolve_analysis_config {pat}"
    one = f'{lead}"{head} = {plan}"'
    if symbol_len(one) <= MAX_LINE:
        return [one]
    if symbol_len(f'{lead}"{head}') <= MAX_LINE:
        return [f'{lead}"{head}', f'     = {plan}"']
    if symbol_len(f"     {pat}") <= MAX_LINE:
        return [f'{lead}"resolve_analysis_config', f"     {pat}", f'     = {plan}"']
    fields, _, ctx_field = pat.rpartition(", cfg_context")
    return [f'{lead}"resolve_analysis_config', f"     {fields},",
            f"        cfg_context{ctx_field}", f'     = {plan}"']


def render_config(doms, solvers, cfg):
    ctor = {k: v["constructor"] for k, v in solvers.items()}

    out = [f"theory {cfg['theory']}", "  imports"]
    out += [f"    {imp}" for imp in cfg["imports"]]
    out += ["begin", "", "section \\<open>The resolver's support matrix\\<close>", ""]
    out += text_block(GENERATED_NOTICE + """
One table over domain, solver and context. A cell is supported when the registry
publishes a route there: at \\<^const>\\<open>Ctx_None\\<close> that means a published
report, at the two context modes a routed instance. \\<^const>\\<open>None\\<close>
everywhere else, and an unsupported cell is a missing proof, never a missing
case.

The same list decides \\<open>analyse_with_solver\\<close>, so the two cannot disagree
about what is supported.

The bound \\<open>k\\<close> carries no side condition. \\<open>cs_route\\<close> at
\\<open>k = 0\\<close> routes every activation to the context \\<^term>\\<open>[]\\<close>, which is
as well-defined and as finite as any other bound, so the resolver treats it as
one more instantiation rather than as a case to reject. It is not
\\<^const>\\<open>Ctx_None\\<close> in disguise: the equation system stays call-string
keyed, and the published result carries call-string contexts.
""") + [""]

    out += ["fun resolve_analysis_config ::",
            "    \"analysis_config \\<Rightarrow> analysis_plan option\" where"]
    first = True
    for dom in doms:
        support = {"none": (set(dom.routes), dom.default, 0)}
        for name, spec in dom.contexts.items():
            support[name] = (set(spec["solvers"]), spec["default"],
                             spec.get("min_bound", 0))
        for ctx in CONTEXT_ORDER:
            allowed, default, min_bound = support.get(ctx, (set(), None, 0))
            plan_ctor = dom.plan + CONTEXT_TERMS[ctx][1]
            arg = " k" if ctx == "call_string" else ""

            def plan(route):
                p = f"Some ({plan_ctor} {route}{arg})"
                if ctx == "call_string" and min_bound:
                    # `k = 0` at the usual bound of one: the shape the
                    # handwritten resolver already uses, and on `nat` the same
                    # test as `k < 1`.
                    guard = "k = 0" if min_bound == 1 else f"k < {min_bound}"
                    return f"(if {guard} then None else {p})"
                return p
            if not allowed:
                out += resolver_equation(dom, ctx, "_", "None", not first)
                first = False
                continue
            out += resolver_equation(dom, ctx, "None", plan(ctor[default]), not first)
            first = False
            if allowed == set(ctor):
                out += resolver_equation(dom, ctx, "Some s", plan("s"), True)
                continue
            for route in SOLVER_ORDER:
                body = plan(ctor[route]) if route in allowed else "None"
                out += resolver_equation(dom, ctx, f"Some {ctor[route]}", body, True)
    out.append("")

    out += ["definition valid_analysis_config :: \"analysis_config \\<Rightarrow> bool\" where",
            "  \"valid_analysis_config cfg = (resolve_analysis_config cfg \\<noteq> None)\"",
            "", "end"]
    return "\n".join(out) + "\n"


def validate(manifest, doms):
    """Reject a registry that is duplicated, incomplete, or names an unknown
    solver. Layout is the generator's business; this checks the policy."""
    problems = []
    solvers = manifest["solvers"]

    def unique(what, values):
        seen = set()
        for v in values:
            if v in seen:
                problems.append(f"duplicate {what}: {v}")
            seen.add(v)

    unique("domain name", [d.name for d in doms])
    unique("value type", [d.value_type for d in doms])
    unique("report tag", [d.tag for d in doms])
    unique("interpretation binder",
           [d.binder(r) for d in doms for r in d.routes if d.has_assembly])
    unique("published prefix",
           [d.prefix(r) for d in doms for r in d.routes if d.has_assembly])

    for d in doms:
        if not d.routes:
            problems.append(f"{d.name}: publishes no route")
        unique(f"{d.name} route", d.routes)
        for route in d.routes:
            if route not in solvers:
                problems.append(f"{d.name}: unknown solver {route}")
        for name, spec in d.contexts.items():
            if name not in CONTEXT_TERMS or name == "none":
                problems.append(f"{d.name}: unknown context {name}")
                continue
            if spec["default"] not in spec["solvers"]:
                problems.append(f"{d.name}/{name}: default solver is not supported")
            for route in spec["solvers"]:
                if route not in solvers:
                    problems.append(f"{d.name}/{name}: unknown solver {route}")
            bound = spec.get("min_bound", 0)
            if isinstance(bound, bool) or not isinstance(bound, int) or bound < 0:
                problems.append(f"{d.name}/{name}: min_bound must be a non-negative"
                                " integer; it is the shortest bound the domain"
                                " publishes, and the generator emits its guard")
            elif bound and name != "call_string":
                problems.append(f"{d.name}/{name}: min_bound is meaningful only for"
                                " a bounded context")
        FACT_ROLES = {"transfer_sound", "tf_commute", "tf_abs_def",
                      "enter_commute", "init_gamma", "classifier"}
        for role, value in d.legacy.get("facts", {}).items():
            if isinstance(value, dict):
                if set(value) != {"const", "args"} or not value["args"]:
                    problems.append(f"{d.name}: applied role {role} takes exactly"
                                    " `const` and a non-empty `args`")
                elif not all(isinstance(x, str) and ISABELLE_NAME.match(x)
                             for x in [value["const"], *value["args"]]):
                    problems.append(f"{d.name}: applied role {role} may name only"
                                    " constants; `const` and each argument must be"
                                    " a plain Isabelle name")
                elif role in FACT_ROLES:
                    problems.append(f"{d.name}: role {role} names a fact, and a fact"
                                    " takes no arguments")
            elif not isinstance(value, str):
                problems.append(f"{d.name}: role {role} must be a name or an"
                                " application")

        for route, spec in d.legacy.get("routes", {}).items():
            if route not in d.routes:
                problems.append(f"{d.name}: legacy name for unpublished route {route}")
            if set(spec) != {"report", "report_with_state"}:
                problems.append(f"{d.name}/{route}: a route names both a report"
                                " and a state report, or neither")
        if not d.has_assembly and not d.legacy.get("routes"):
            problems.append(f"{d.name}: no generated assembly, so every route"
                            " needs its names under legacy")

    if problems:
        sys.exit("registry is not valid:\n  " + "\n  ".join(problems))


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("manifest", nargs="?", default="assembly/analyses.yaml")
    ap.add_argument("--check", action="store_true", help="report drift, do not write")
    ap.add_argument("--out", help="write under this directory instead of in place")
    args = ap.parse_args()

    root = Path(__file__).resolve().parent.parent
    manifest = yaml.safe_load((root / args.manifest).read_text())
    solvers = manifest["solvers"]
    doms = [Domain(e) for e in manifest["domains"]]
    validate(manifest, doms)

    cli = {"theory": "Dispatch_Tables",
           "path": "src/Executable_Surface/CLI/generated/Dispatch_Tables.thy",
           "imports": ["Analysis_Config", "Dispatch_Carrier"]}
    cfg = {"theory": "Config_Tables",
           "path": "src/Executable_Surface/CLI/generated/Config_Tables.thy",
           "imports": ["Analysis_Config"]}

    rendered_assemblies = [(d, d.path, render_assembly(d, solvers))
                           for d in doms if d.has_assembly]
    targets = [(path, text) for d, path, text in rendered_assemblies if d.adopted]
    unadopted = [(path, text) for d, path, text in rendered_assemblies
                 if not d.adopted]
    cli_targets = [(cli["path"], render_cli(doms, solvers, cli)),
                   (cfg["path"], render_config(doms, solvers, cfg))]
    # An unadopted output is a preview: renderable on demand, never written into
    # the tree and never demanded by the drift check.
    if manifest.get("cli_adopted"):
        targets += cli_targets
    else:
        unadopted += cli_targets

    if args.out:
        targets += unadopted
        unadopted = []

    # An unadopted output must be absent, not merely uncompared. A file that is
    # in the tree is reachable by a ROOT and can be imported, so leaving the
    # flag false would exempt live code from the freshness check -- the one way
    # this flag could do harm.
    stale = []
    for path, _ in unadopted:
        if (Path(args.out) / Path(path).name if args.out else root / path).exists():
            stale.append(path)
            print(f"{path}: marked unadopted in the registry but present in the "
                  f"tree, so nothing checks it for staleness. Either set its "
                  f"adoption flag or remove the file.", file=sys.stderr)

    for path, rendered in targets:
        for i, line in enumerate(rendered.split("\n"), 1):
            if symbol_len(line) > MAX_LINE:
                sys.exit(f"{path}:{i}: generated line over {MAX_LINE} symbols")
            if not line.isascii():
                sys.exit(f"{path}:{i}: generated line is not ASCII")
        target = Path(args.out) / Path(path).name if args.out else root / path
        if args.check:
            current = target.read_text() if target.exists() else ""
            if current != rendered:
                stale.append(path)
                sys.stderr.writelines(difflib.unified_diff(
                    current.splitlines(keepends=True),
                    rendered.splitlines(keepends=True),
                    fromfile=f"{path} (on disk)", tofile=f"{path} (regenerated)"))
        else:
            target.parent.mkdir(parents=True, exist_ok=True)
            target.write_text(rendered)
            print(f"wrote {target}")

    if stale:
        sys.exit(f"stale generated files: {', '.join(stale)}")


if __name__ == "__main__":
    main()
