#!/usr/bin/env python3
"""Generates each analysis domain's registration theory from manifests/analyses.yaml.

One output per domain:

  src/Analyses/<Domain>/generated/<Domain>_Analyses.thy

It registers the domain three times -- at the unit context, at the entry-state
context and at the call-string context -- each registration taking the global
update rule as a parameter, so one registration serves every solver discipline.
The unit registration interprets `unit_dg_analysis`, the other two its parent
`routed_dg_analysis`.

What is generated is registration, never mathematics. Every obligation is
discharged by citing a fact the manifest only names: the domain's own, or the
rule-parametric `TD_side_rule_Interp` instance for the three solver contracts.
No axiom, no `sorry`, no assumption.

Usage:
  python3 scripts/gen_analysis_assembly.py [--check] [--out DIR] [manifest]

This is a host writer, and a running Isabelle session does not notice it: the
session goes on serving the bytes it loaded. Restart, or compare the buffer
against disk at a changed line, before believing diagnostics after a run.
"""

import argparse
import difflib
import re
import sys
from pathlib import Path

import yaml

MAX_LINE = 100
# Headroom below the layout limit, so a renamed domain cannot re-render a filled
# line one symbol too long without anything noticing.
PACK_WIDTH = 90
SYMBOL = re.compile(r"\\<\^?[A-Za-z][A-Za-z0-9_']*>")
ISABELLE_NAME = re.compile(r"^[A-Za-z][A-Za-z0-9_'.]*$")

# Named explicitly rather than relied on transitively: an implicit dependency is
# what turns a later unrelated import prune into a failure nobody can place.
COMMON_IMPORTS = [
    '"Voblint_Result.Unit_DG_Analysis"',
    '"Voblint_Result.Routed_Live_Keys"',
    '"Voblint_Framework.Call_String_Context"',
    '"Voblint_Framework.Routed_Context"',
    '"Voblint_Solver.TD_Solver_Bridge"',
    '"Voblint_Solver.Globals_Rule"',
    '"Voblint_VIMP.VIMP_Program"',
    '"TD.TD_side_upd_rule"',
]

INTERP = "TD_side_rule_Interp"

GENERATED_NOTICE = (
    "GENERATED FILE. Source: \\<^verbatim>\\<open>manifests/analyses.yaml\\<close>; generator:\n"
    "\\<^verbatim>\\<open>scripts/gen_analysis_assembly.py\\<close>. Regenerate with the generator\n"
    "rather than hand-editing; a drift check compares regenerated output against\n"
    "this file.\n"
)

ROLES = [
    "tf_st",
    "enter_st",
    "init_st",
    "skip",
    "assign",
    "special",
    "branch",
    "body",
    "return",
    "enter_ci",
    "event",
    "transfer_sound",
    "tf_commute",
    "tf_abs_def",
    "enter_commute",
    "classifier",
    "init_gamma",
]
FACT_ROLES = {
    "transfer_sound",
    "tf_commute",
    "tf_abs_def",
    "enter_commute",
    "init_gamma",
    "classifier",
}

# What distinguishes the three contexts: the global and seed keys, the route on
# the executable and on the abstract carrier, and obligation 4, which says the
# route reads only what the abstraction preserves.
CONTEXTS = [
    {
        "suffix": "",
        "title": "the unit context",
        "locale": "unit_dg_analysis",
        "header": [
            "proof (rule unit_dg_analysis.intro, rule routed_dg_analysis.intro,",
            "       goal_cases)",
        ],
        "gk": lambda vt: "(unit, unit) routed_gk",
        "keys": None,
        "route_abs": None,
        "params": "r",
        "case4": ["  case (4 \\<G> u ctx d ca) show ?case by simp"],
    },
    {
        "suffix": "_es",
        "title": "the entry-state context",
        "locale": "routed_dg_analysis",
        "header": ["proof (rule routed_dg_analysis.intro, goal_cases)"],
        "gk": lambda vt: f"(unit, {vt} list) routed_gk",
        "keys": '"Analysis_Global ()" Activation_Seed exec_formals_route "[]"',
        "route_abs": '"\\<lambda>_. formals_route_lifted_gen"',
        "params": "r",
        "case4": [
            "  case (4 \\<G> u ctx d ca) show ?case",
            "    unfolding fun_of_exec_dg_st_for_def",
            "    by (rule exec_formals_route_commute[symmetric])",
        ],
    },
    {
        "suffix": "_cs",
        "title": "the call-string context",
        "locale": "routed_dg_analysis",
        "header": ["proof (rule routed_dg_analysis.intro, goal_cases)"],
        "gk": lambda vt: "call_string_gk",
        "keys": (
            "Call_String_Context.Global Call_String_Context.Seed"
            ' "\\<lambda>_. cs_route k" "[]"'
        ),
        "route_abs": '"\\<lambda>_. cs_route k"',
        "params": "k r",
        "case4": [
            "  case (4 \\<G> u ctx d ca) show ?case by (rule cs_route_indep_of_data)"
        ],
    },
]


def symbol_len(line):
    """Length in Isabelle symbols, which is what the layout rule counts."""
    return len(SYMBOL.sub("x", line))


class Domain:
    def __init__(self, entry):
        self.name = entry["name"]
        self.value_type = entry["value_type"]
        self.impl = entry.get("impl", self.name.lower())
        self.imports = entry["imports"]
        self.overrides = entry.get("roles", {})
        self.path = f"src/Analyses/{self.name}/generated/{self.name}_Analyses.thy"

    def roles(self):
        """The interface roles, spelled the domain's way unless overridden."""
        i = self.impl
        roles = {
            "tf_st": f"{i}_tf_st_for",
            "enter_st": f"{i}_enter_st_for",
            "init_st": f"cinit_{i}_st",
            "skip": f"skip_{i}",
            "assign": f"assign_{i}",
            "special": f"special_{i}",
            "branch": f"branch_{i}",
            "body": f"body_{i}",
            "return": f"return_{i}",
            "enter_ci": f"enter_{i}_ci_for",
            "event": f"event_{i}",
            "transfer_sound": f"{i}_tf.is_sound_transfer_for",
            "tf_commute": f"{i}_tf_st_for_commute",
            "tf_abs_def": f"{i}_tf.tf_abs_def",
            "enter_commute": f"{i}_enter_st_for_commute",
            "classifier": f"{self.name.lower()}_classify_check",
            "init_gamma": f"{self.name.lower()}_cinit_gamma",
        }
        roles.update(self.overrides)
        return roles


def role_term(role):
    """A role in term position: a bare name, or a quoted application, which
    Isabelle reads as one argument."""
    if isinstance(role, dict):
        return f'"{role["const"]} {" ".join(role["args"])}"'
    return role


def text_block(body):
    lines = ["text \\<open>"]
    lines += [f"  {line}" if line else "" for line in body.rstrip("\n").split("\n")]
    return lines + ["\\<close>"]


def rule_step(rule):
    one = f"    by (rule {rule})"
    if symbol_len(one) <= MAX_LINE:
        return [one]
    head, _, bracket = rule.partition("[")
    return [f"    by (rule {head}", f"          [{bracket})"]


def pack_operands(groups):
    """One line per group where that fits, else filled by width."""
    lines = ["    " + " ".join(gs) for gs in groups]
    if all(symbol_len(packed) <= MAX_LINE for packed in lines):
        return lines
    out, line = [], "   "
    for op in [op for gs in groups for op in gs]:
        if symbol_len(f"{line} {op}") > PACK_WIDTH:
            out.append(line)
            line = "   "
        line = f"{line} {op}"
    return out + [line]


def registration(dom, ctx):
    """One registration with the same twelve discharges every time; only the
    context terms and obligation 4 vary."""
    r = dom.roles()
    t = {k: role_term(v) for k, v in r.items()}
    vt = dom.value_type
    out = [
        f"global_interpretation {dom.name.lower()}{ctx['suffix']}_rule: {ctx['locale']}",
        f"    {t['tf_st']} {t['enter_st']} {t['init_st']}",
    ]
    if ctx["keys"]:
        out.append(f"    {ctx['keys']}")
    out += [
        f'    "{INTERP}_solve r"',
        f'    "{INTERP}.solve_dom TYPE({ctx["gk"](vt)})',
        f'       TYPE(({vt} exec_dg_st lifted, {vt} exec_dg_st lifted) dg_state) r"',
        f"    bot {t['classifier']}",
    ]
    tail = [t["enter_ci"], t["event"]] + (
        [ctx["route_abs"]] if ctx["route_abs"] else []
    )
    groups = [
        [t[k] for k in ["skip", "assign", "special", "branch", "body", "return"]],
        tail,
        [f'"{INTERP}_solve_c r"'],
    ]
    if not ctx["route_abs"]:
        groups = [groups[0], tail + groups[2]]
    out += pack_operands(groups)
    out.append(f"  for {ctx['params']}")
    out += ctx["header"]
    out += [
        f"  case (1 \\<G>) show ?case by (rule {r['transfer_sound']})",
        "next",
        "  case (2 \\<G> a s) then show ?case",
        "    unfolding fun_of_exec_dg_st_for_def",
        f"    by (rule {r['tf_commute']}[unfolded {r['tf_abs_def']}])",
        "next",
        "  case (3 \\<G> ci s) show ?case",
        f"    unfolding fun_of_exec_dg_st_for_def by (rule {r['enter_commute']})",
        "next",
        *ctx["case4"],
        "next",
        "  case (5 v ctx) show ?case by simp",
        "next",
        "  case (6 eqs x) then show ?case",
        *rule_step(f"{INTERP}.partial_post_solution[OF _ surjective_pairing]"),
        "next",
        "  case (7 eqs x) then show ?case",
        *rule_step(f"{INTERP}.finite_stabl_solve"),
        "next",
        f"  case (8 c d s) then show ?case by (rule {r['classifier']}_proved)",
        "next",
        f"  case (9 c d s) then show ?case by (rule {r['classifier']}_refuted)",
        "next",
        "  case 10 show ?case by (rule refl)",
        "next",
        f"  case (11 \\<G>) show ?case by (rule {r['init_gamma']})",
        "next",
        "  case (12 eqs x) then show ?case",
        *rule_step(f"{INTERP}.solve_dom_of_solve_c"),
        "qed",
    ]
    return out


def render(dom):
    out = [f"theory {dom.name}_Analyses", "  imports"]
    out += [f"    {i}" for i in dom.imports + COMMON_IMPORTS] + ["begin", ""]
    out += [
        f"section \\<open>Registering {dom.name} at every context and update rule\\<close>",
        "",
    ]
    out += text_block(
        GENERATED_NOTICE + "\n"
        f"{dom.name} runs through the shared D/G pipeline three times: at the unit context,\n"
        "keyed by the abstract values a callee's formals hold on entry, and keyed by a\n"
        "bounded call string. Each registration leaves the rule that merges a value\n"
        "side-effected into a global as a parameter \\<open>r\\<close>, and the call-string\n"
        "one also its bound \\<open>k\\<close>, so one registration serves every discipline and\n"
        "every bound. The equation system, the solve, the result table and every soundness\n"
        "endpoint come from the interpreted locale; this theory only names the domain's\n"
        "own implementation and facts."
    ) + [""]
    for ctx in CONTEXTS:
        out += [f"subsection \\<open>At {ctx['title']}\\<close>", ""]
        out += registration(dom, ctx) + [""]
    out.append("end")
    return "\n".join(out) + "\n"


def validate(doms):
    """Reject a registry that is duplicated or names an ill-formed role."""
    problems = []
    for what, values in [
        ("domain name", [d.name for d in doms]),
        ("value type", [d.value_type for d in doms]),
    ]:
        if len(values) != len(set(values)):
            problems.append(f"duplicate {what}")
    for d in doms:
        for role, value in d.overrides.items():
            if role not in ROLES:
                problems.append(f"{d.name}: unknown role {role}")
            elif isinstance(value, dict):
                if set(value) != {"const", "args"} or not value["args"]:
                    problems.append(
                        f"{d.name}: applied role {role} takes exactly"
                        " `const` and a non-empty `args`"
                    )
                elif not all(
                    isinstance(x, str) and ISABELLE_NAME.match(x)
                    for x in [value["const"], *value["args"]]
                ):
                    problems.append(
                        f"{d.name}: applied role {role} may name only constants"
                    )
                elif role in FACT_ROLES:
                    problems.append(
                        f"{d.name}: role {role} names a fact, and a fact"
                        " takes no arguments"
                    )
            elif not isinstance(value, str):
                problems.append(
                    f"{d.name}: role {role} must be a name or an application"
                )
    if problems:
        sys.exit("registry is not valid:\n  " + "\n  ".join(problems))


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("manifest", nargs="?", default="manifests/analyses.yaml")
    ap.add_argument("--check", action="store_true", help="report drift, do not write")
    ap.add_argument("--out", help="write under this directory instead of in place")
    args = ap.parse_args()

    root = Path(__file__).resolve().parent.parent
    manifest = yaml.safe_load((root / args.manifest).read_text())
    doms = [Domain(e) for e in manifest["domains"]]
    validate(doms)

    stale = []
    for dom in doms:
        text = render(dom)
        for i, line in enumerate(text.split("\n"), 1):
            if symbol_len(line) > MAX_LINE:
                sys.exit(f"{dom.path}:{i}: generated line over {MAX_LINE} symbols")
            if not line.isascii():
                sys.exit(f"{dom.path}:{i}: generated line is not ASCII")
        target = Path(args.out) / Path(dom.path).name if args.out else root / dom.path
        if args.check:
            current = target.read_text() if target.exists() else ""
            if current != text:
                stale.append(dom.path)
                sys.stderr.writelines(
                    difflib.unified_diff(
                        current.splitlines(keepends=True),
                        text.splitlines(keepends=True),
                        fromfile=f"{dom.path} (on disk)",
                        tofile=f"{dom.path} (regenerated)",
                    )
                )
        else:
            target.parent.mkdir(parents=True, exist_ok=True)
            target.write_text(text)
            print(f"wrote {target}")
    if stale:
        sys.exit(f"stale generated files: {', '.join(stale)}")


if __name__ == "__main__":
    main()
