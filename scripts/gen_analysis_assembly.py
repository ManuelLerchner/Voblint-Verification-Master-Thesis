#!/usr/bin/env python3
"""Generates the analysis registrations and the combined state from manifests/analyses.yaml.

One output per domain, plus one for the combined state:

  src/Analyses/<Domain>/generated/<Domain>_Analyses.thy
  src/Executable_Surface/CLI/generated/MCP_Carrier.thy

A domain is registered once per context it lists (`contexts`, default `[unit]`),
each registration taking the global update rule as a parameter, so one
registration serves every solver discipline. The unit registration interprets
`unit_dg_analysis`, the entry-state and call-string ones its parent
`routed_dg_analysis_exec`. The combined state has one lifted field per domain,
in manifest order, and the per-domain cases the handwritten `MCP_Analyses`
registers over.

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
from string import Template

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

# How an analysis runs as one field of the combined state. Each role is a term
# template; its placeholders are $G (the globals predicate), $p (the program),
# $gs (the declared globals as a list), $f (the field of a state), $v (the field
# of a published value), $q (a query), $x (a variable) and $c (the field of a
# context). The three *_type roles are types, and the last four name facts.
FIELD_ROLES = [
    "state_type",
    "published_type",
    "context_type",
    "component",
    "gamma",
    "empty",
    "read",
    "published_gamma",
    "published_empty",
    "answer",
    "display",
    "init",
    "route",
    "context_values",
    "component_sound",
    "single_entry",
    "init_sound",
    "answer_sound",
]

# What distinguishes the three contexts: the global and seed keys, the route on
# the executable and on the abstract carrier, and obligation 4, which says the
# route reads only what the abstraction preserves.
CONTEXTS = [
    {
        "key": "unit",
        "suffix": "",
        "title": "the unit context",
        "locale": "unit_dg_analysis",
        "header": [
            "proof (rule unit_dg_analysis.intro, rule routed_dg_analysis_exec.intro,",
            "       goal_cases)",
        ],
        "gk": lambda vt: "(unit, unit) routed_gk",
        "keys": None,
        "route_abs": None,
        "params": "r",
        "case4": ["  case (4 \\<G> u ctx d ca) show ?case by simp"],
    },
    {
        "key": "entry-state",
        "suffix": "_es",
        "title": "the entry-state context",
        "locale": "routed_dg_analysis_exec",
        "header": ["proof (rule routed_dg_analysis_exec.intro, goal_cases)"],
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
        "key": "call-string",
        "suffix": "_cs",
        "title": "the call-string context",
        "locale": "routed_dg_analysis_exec",
        "header": ["proof (rule routed_dg_analysis_exec.intro, goal_cases)"],
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
        self.contexts = entry.get("contexts", ["unit"])
        self.prefix = self.name.lower()
        self.constructor = f"{self.name}_Analysis"
        self.value_constructor = entry.get("value_constructor", f"{self.name}Value")
        self.field_overrides = entry.get("field", {})
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

    def field(self):
        """How the analysis runs as a field of the combined state, as term
        templates over the placeholders of FIELD_ROLES. The defaults are those of
        a pointwise domain registered at the unit context."""
        r, vt, vc, p = (
            self.roles(),
            self.value_type,
            self.value_constructor,
            self.prefix,
        )
        roles = {
            "state_type": f"{vt} exec_dg_st lifted",
            "published_type": f"{vt} abs_state lifted",
            "context_type": f"{vt} list",
            "component": "ask_assign (exec_component $G"
            " (resolved_st_q_is_bot_for (declared_global_vars $p))"
            f" {applied(r['tf_st'], '$G')} {applied(r['enter_st'], '$G')})",
            "gamma": "gamma_point (map_lift (fun_of_resolved_st_q_for $G) $f)",
            "empty": "(case $f of Bot \\<Rightarrow> True"
            " | Lifted st \\<Rightarrow> resolved_st_q_is_bot_for $gs st)",
            "read": "map_lift (fun_of_resolved_st_q_for $G) $f",
            "published_gamma": "gamma_point $v",
            "published_empty": "(case $v of Bot \\<Rightarrow> True"
            " | Lifted st \\<Rightarrow> is_empty_state st)",
            "answer": "(case $v of Bot \\<Rightarrow> \\<top>"
            f" | Lifted st \\<Rightarrow> {p}_eval_answer st $q)",
            "display": f"{vc} (case $v of Bot \\<Rightarrow> \\<bottom>"
            " | Lifted st \\<Rightarrow> st $x)",
            "init": f"Lifted {bare(r['init_st'])}",
            "route": "exec_formals_route $G u [] $f ca",
            "context_values": f"map {vc} $c",
            "component_sound": f"ask_assign_sound[OF {p}_rule.comp_sound]",
            "single_entry": "single_entry_ask_assign[OF single_entry_exec_component]",
            "init_sound": f"{p}_rule.init_sound",
            "answer_sound": f"{p}_eval_answer_sound",
        }
        roles.update(self.field_overrides)
        return roles

    def term(self, role, **values):
        """A field role with its placeholders filled in."""
        return Template(self.field()[role]).substitute(values)


def role_term(role):
    """A role in term position: a bare name, or a quoted application, which
    Isabelle reads as one argument."""
    if isinstance(role, dict):
        return f'"{role["const"]} {" ".join(role["args"])}"'
    return role


def wrap_prose(text, width=84):
    """Fill a paragraph to the width text blocks use."""
    lines, line = [], ""
    for word in text.split():
        if line and len(f"{line} {word}") > width:
            lines.append(line)
            line = word
        else:
            line = f"{line} {word}" if line else word
    return "\n".join(lines + [line])


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
    ctxs = [c for c in CONTEXTS if c["key"] in dom.contexts]
    where = {
        "unit": "at the unit context",
        "entry-state": "keyed by the abstract values a callee's formals hold on entry",
        "call-string": "keyed by a bounded call string",
    }
    places = [where[c["key"]] for c in ctxs]
    listed = (
        places[0]
        if len(places) == 1
        else ", ".join(places[:-1]) + ", and " + places[-1]
    )
    out += text_block(
        GENERATED_NOTICE
        + "\n"
        + wrap_prose(
            f"{dom.name} runs through the shared D/G pipeline {listed}. The CLI runs it as"
            " a field of the combined state of \\<open>MCP_Analyses\\<close>,"
            " whose component and soundness this unit registration supplies. Each"
            " registration leaves the rule that merges a value side-effected into a"
            " global as a parameter \\<open>r\\<close>"
            + (
                ", and the call-string one also its bound \\<open>k\\<close>"
                if any(c["key"] == "call-string" for c in ctxs)
                else ""
            )
            + ". The equation system, the solve, the result table and every soundness"
            " endpoint come from the interpreted locale; this theory only names the"
            " domain's own implementation and facts."
        )
    ) + [""]
    for ctx in ctxs:
        out += [f"subsection \\<open>At {ctx['title']}\\<close>", ""]
        out += registration(dom, ctx) + [""]
    out.append("end")
    return "\n".join(out) + "\n"


MCP_PATH = "src/Executable_Surface/CLI/generated/MCP_Carrier.thy"


def wrap_term(text, indent, width=PACK_WIDTH):
    """Break a long term at spaces; Isabelle reads the pieces as one term."""
    out, line = [], " " * indent
    for word in text.split(" "):
        piece = f"{line}{word}" if line.strip() == "" else f"{line} {word}"
        if symbol_len(piece) > width and line.strip():
            out.append(line)
            line = " " * (indent + 2) + word
        else:
            line = piece
    return out + [line]


def atomic(term):
    """Whether a term needs no parentheses as an argument."""
    if " " not in term:
        return True
    if not term.startswith("("):
        return False
    depth = 0
    for i, ch in enumerate(term):
        depth += ch == "("
        depth -= ch == ")"
        if depth == 0:
            return i == len(term) - 1
    return False


def arg(term):
    return term if atomic(term) else f"({term})"


def nest(items):
    """The nested analysis products holding one item per registered analysis."""
    term = items[-1]
    for item in reversed(items[:-1]):
        term = f"Product {arg(item)} {arg(term)}"
    return term


def nest_type(types):
    ty = types[-1]
    for t in reversed(types[:-1]):
        ty = f"({t}, {ty}) analysis_product"
    return ty


def pright_n(n, r="r"):
    term = r
    for _ in range(n):
        term = f"pright {arg(term)}"
    return term


def slot_expr(k, n, r="r"):
    """Field k (1-based) of n."""
    if k == n:
        return pright_n(n - 1, r)
    return f"pleft {arg(pright_n(k - 1, r))}"


def applied(role, arg):
    """A role applied to one more argument, parenthesized."""
    if isinstance(role, dict):
        return f"({role['const']} {' '.join(role['args'])} {arg})"
    return f"({role} {arg})"


def bare(role):
    if isinstance(role, dict):
        return f"({role['const']} {' '.join(role['args'])})"
    return role


def fun_block(header, cases):
    out = header
    for i, (lhs, rhs) in enumerate(cases):
        lead = '  "' if i == 0 else '| "'
        first = f"{lead}{lhs} ="
        body = wrap_term(rhs + '"', 5)
        out += [first] + body
    return out


def render_mcp(doms):
    n = len(doms)
    G = "\\<G>"
    out = [
        "theory MCP_Carrier",
        "  imports",
        '    "Voblint_CLI.Analysis_Config"',
        '    "Voblint_CLI.Dispatch_Carrier"',
        '    "Voblint_CLI.MCP_Field"',
        "begin",
        "",
    ]
    out += [
        "section \\<open>The combined state of the registered analyses\\<close>",
        "",
    ]
    out += text_block(
        GENERATED_NOTICE
        + "\n"
        + wrap_prose(
            "Every registered analysis owns one field of the combined state, in"
            " manifest order. This theory names the analyses, lays out the fields,"
            " and states for each analysis how its field runs, what it describes,"
            " how it reads back and answers queries, and where it starts. Nothing"
            " here is proved beyond citing each analysis's own registration; the"
            " combination and its soundness are in"
            " \\<open>MCP_Analyses\\<close>."
        )
    ) + [""]
    out += ["datatype analysis_domain ="]
    out += [("    " if i == 0 else "  | ") + d.constructor for i, d in enumerate(doms)]
    out += [""]
    out += ["subsection \\<open>Fields\\<close>", ""]
    for k in range(1, n + 1):
        out += [f"definition slot{k} where", f'  "slot{k} r = {slot_expr(k, n)}"', ""]
    for k in range(1, n + 1):
        items = [slot_expr(j, n) for j in range(1, k)] + ["v"]
        if k < n:
            items.append(pright_n(k))
        out += [f"definition set_slot{k} where"]
        out += wrap_term(f'"set_slot{k} r v = {nest(items)}"', 2)
        out += [""]
    names = [f"slot{k}_def" for k in range(1, n + 1)] + [
        f"set_slot{k}_def" for k in range(1, n + 1)
    ]
    out += wrap_term("lemmas slot_defs [simp] = " + " ".join(names), 0) + [""]
    for name, role in [
        ("mcp_st", "state_type"),
        ("mcp_val", "published_type"),
        ("mcp_ctx", "context_type"),
    ]:
        ty = nest_type([d.field()[role] for d in doms])
        out += [f"type_synonym {name} ="] + wrap_term(f'"{ty}"', 2) + [""]

    out += ["subsection \\<open>Each analysis on its own field\\<close>", ""]

    def per(fn):
        return [fn(k, d) for k, d in enumerate(doms, 1)]

    out += fun_block(
        [
            "fun mcp_component_of ::",
            '  "(vname \\<Rightarrow> bool) \\<Rightarrow> imp_prog \\<Rightarrow> analysis_domain'
            ' \\<Rightarrow> mcp_st lifted mcp_component" where',
        ],
        per(
            lambda k, d: (
                f"mcp_component_of {G} p {d.constructor}",
                f"lens_of (lift_get slot{k}) (lift_put set_slot{k})"
                f" {arg(d.term('component', G=G, p='p'))}",
            )
        ),
    )
    out += [""]
    out += fun_block(
        [
            'fun part_gamma :: "(vname \\<Rightarrow> bool) \\<Rightarrow> analysis_domain \\<Rightarrow> mcp_st lifted \\<Rightarrow> store set" where'
        ],
        per(
            lambda k, d: (
                f"part_gamma {G} {d.constructor}",
                f"(\\<lambda>x. {d.term('gamma', G=G, f=f'(lift_get slot{k} x)')})",
            )
        ),
    )
    out += [""]
    out += fun_block(
        [
            'fun part_live :: "analysis_domain \\<Rightarrow> mcp_st \\<Rightarrow> bool" where'
        ],
        per(
            lambda k, d: (
                f"part_live {d.constructor} r",
                f"(slot{k} r \\<noteq> \\<bottom>)",
            )
        ),
    )
    out += [""]
    out += fun_block(
        [
            'fun part_empty :: "vname list \\<Rightarrow> analysis_domain \\<Rightarrow> mcp_st \\<Rightarrow> bool" where'
        ],
        per(
            lambda k, d: (
                f"part_empty gs {d.constructor} r",
                d.term("empty", gs="gs", f=f"(slot{k} r)"),
            )
        ),
    )
    out += [""]

    out += ["subsection \\<open>What each field publishes\\<close>", ""]
    out += [
        'definition mcp_rd :: "(vname \\<Rightarrow> bool) \\<Rightarrow> mcp_st \\<Rightarrow> mcp_val" where'
    ]
    rd = nest(per(lambda k, d: d.term("read", G=G, f=f"(slot{k} r)")))
    out += wrap_term(f'"mcp_rd {G} r = {rd}"', 2) + [""]
    out += fun_block(
        [
            'fun val_gamma :: "analysis_domain \\<Rightarrow> mcp_val \\<Rightarrow> store set" where'
        ],
        per(
            lambda k, d: (
                f"val_gamma {d.constructor} v",
                d.term("published_gamma", v=f"(slot{k} v)"),
            )
        ),
    )
    out += [""]
    out += [
        'definition mcp_gamma_v :: "analysis_domain list \\<Rightarrow> mcp_val \\<Rightarrow> store set" where',
        '  "mcp_gamma_v as v = (\\<Inter>a \\<in> set as. val_gamma a v)"',
        "",
    ]
    out += fun_block(
        [
            'fun val_empty :: "analysis_domain \\<Rightarrow> mcp_val \\<Rightarrow> bool" where'
        ],
        per(
            lambda k, d: (
                f"val_empty {d.constructor} v",
                d.term("published_empty", v=f"(slot{k} v)"),
            )
        ),
    )
    out += [""]
    out += fun_block(
        [
            'fun val_answer :: "analysis_domain \\<Rightarrow> mcp_val \\<Rightarrow> query \\<Rightarrow> answer" where'
        ],
        per(
            lambda k, d: (
                f"val_answer {d.constructor} v q",
                d.term("answer", v=f"(slot{k} v)", q="q"),
            )
        ),
    )
    out += [""]
    out += fun_block(
        [
            'fun value_of :: "analysis_domain \\<Rightarrow> mcp_val \\<Rightarrow> vname \\<Rightarrow> abstract_value" where'
        ],
        per(
            lambda k, d: (
                f"value_of {d.constructor} v x",
                d.term("display", v=f"(slot{k} v)", x="x"),
            )
        ),
    )
    out += [""]

    out += [
        "subsection \\<open>Where each field starts, and what it keys a callee by\\<close>",
        "",
    ]
    out += text_block(
        wrap_prose(
            "The entry state starts every active field at its analysis's own entry state and"
            " every other field at its bottom. A field no active analysis runs is never read,"
            " and keeping it at bottom makes the solver's joins, widenings and"
            " comparisons on it constant-time. Under the entry-state policy a callee is keyed"
            " by what the active fields key it by; a field no active analysis runs keys"
            " nothing."
        )
    ) + [""]
    out += ['definition mcp_init :: "analysis_domain list \\<Rightarrow> mcp_st" where']
    init = nest(
        per(
            lambda k, d: (
                f"(if {d.constructor} \\<in> set as then {arg(d.term('init'))}"
                " else \\<bottom>)"
            )
        )
    )
    out += wrap_term(f'"mcp_init as = {init}"', 2) + [""]
    out += [
        "definition mcp_formals_route ::",
        '  "analysis_domain list \\<Rightarrow> (vname \\<Rightarrow> bool) \\<Rightarrow> pp \\<Rightarrow> mcp_ctx \\<Rightarrow> mcp_st lifted',
        '     \\<Rightarrow> call_action \\<Rightarrow> mcp_ctx" where',
    ]
    route = nest(
        per(
            lambda k, d: (
                f"(if {d.constructor} \\<in> set as then"
                f" {d.term('route', G=G, f=f'(lift_get slot{k} d)')} else [])"
            )
        )
    )
    out += wrap_term(f'"mcp_formals_route as {G} u ctx d ca = {route}"', 2) + [""]
    out += ["definition mcp_root_ctx :: mcp_ctx where"]
    out += wrap_term(f'"mcp_root_ctx = {nest(["[]"] * n)}"', 2) + [""]
    out += fun_block(
        [
            'fun ctx_values :: "analysis_domain \\<Rightarrow> mcp_ctx \\<Rightarrow> abstract_value list" where'
        ],
        per(
            lambda k, d: (
                f"ctx_values {d.constructor} ctx",
                d.term("context_values", c=f"(slot{k} ctx)"),
            )
        ),
    )
    out += [""]

    out += [
        "subsection \\<open>What each analysis's registration supplies\\<close>",
        "",
    ]
    comps = " ".join(
        f"field_component_sound[OF {d.field()['component_sound']}]" for d in doms
    )
    out += [
        "lemma mcp_component_of_sound:",
        '  "mcp_component_sound (declared_global p) (part_gamma (declared_global p) a)',
        '     (mcp_component_of (declared_global p) p a)"',
        "  by (cases a; simp only: part_gamma.simps mcp_component_of.simps;",
    ]
    out += wrap_term("rule " + comps + ";", 6)
    out += ["      auto simp: less_eq_analysis_product_def)", ""]
    singles = " ".join(dict.fromkeys(d.field()["single_entry"] for d in doms))
    out += [
        'lemma single_entry_mcp_component_of: "single_entry (mcp_component_of \\<G> p a)"'
    ]
    out += wrap_term(
        f"by (cases a) (auto intro!: single_entry_lens_of lift_put_get {singles})", 2
    )
    out += [""]
    silent = [d.constructor for d in doms if "component" not in d.field_overrides]
    out += [
        "lemma mcp_component_of_silent:",
        f'  "a \\<in> {{{", ".join(silent)}}}',
        f'     \\<Longrightarrow> mc_qry (mcp_component_of {G} p a) x q = \\<top>"',
        "  by (cases a) (simp_all add: lens_of_def ask_assign_def exec_component_def"
        " lens_component_def)",
        "",
    ]
    inits = " ".join(d.field()["init_sound"] for d in doms if d.field()["init_sound"])
    out += [
        "lemma mcp_init_sound:",
        '  "cinit_stores (declared_global p)',
        '     \\<subseteq> mcp_gamma_v as (mcp_rd (declared_global p) (mcp_init as))"',
        "proof -",
        '  have "cinit_stores (declared_global p)',
        '          \\<subseteq> val_gamma a (mcp_rd (declared_global p) (mcp_init as))"',
        '    if "a \\<in> set as" for a',
        "    by (cases a)",
    ]
    out += wrap_term(
        "(use that "
        + inits
        + " in \\<open>simp_all add: mcp_init_def mcp_rd_def\\<close>)",
        7,
    )
    out += ["  then show ?thesis by (auto simp: mcp_gamma_v_def)", "qed", ""]
    answers = " ".join(d.field()["answer_sound"] for d in doms)
    out += [
        'lemma val_answer_sound: "s \\<in> val_gamma a v \\<Longrightarrow> eval_holds q (val_answer a v q) s"',
        "  by (cases a)",
    ]
    out += wrap_term("(auto split: lifted.splits intro: " + answers + ")", 5)
    out += ["", "end"]
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
        known = [c["key"] for c in CONTEXTS]
        if d.contexts and "unit" not in d.contexts:
            problems.append(f"{d.name}: a registration starts at the unit context")
        # The pointwise defaults cite the domain's own unit registration.
        if not d.contexts and set(d.field_overrides) != set(FIELD_ROLES):
            problems.append(
                f"{d.name}: without a registration every field role is given"
            )
        for role in d.field_overrides:
            if role not in FIELD_ROLES:
                problems.append(f"{d.name}: unknown field role {role}")
        for c in d.contexts:
            if c not in known:
                problems.append(f"{d.name}: unknown context {c}")
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
    outputs = [(dom.path, render(dom)) for dom in doms if dom.contexts]
    outputs += [(MCP_PATH, render_mcp(doms))]
    for path, text in outputs:
        for i, line in enumerate(text.split("\n"), 1):
            if symbol_len(line) > MAX_LINE:
                sys.exit(f"{path}:{i}: generated line over {MAX_LINE} symbols")
            if not line.isascii():
                sys.exit(f"{path}:{i}: generated line is not ASCII")
        target = Path(args.out) / Path(path).name if args.out else root / path
        if args.check:
            current = target.read_text() if target.exists() else ""
            if current != text:
                stale.append(path)
                sys.stderr.writelines(
                    difflib.unified_diff(
                        current.splitlines(keepends=True),
                        text.splitlines(keepends=True),
                        fromfile=f"{path} (on disk)",
                        tofile=f"{path} (regenerated)",
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
