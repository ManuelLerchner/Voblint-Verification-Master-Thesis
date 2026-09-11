#!/usr/bin/env python3
"""Generates the analysis registration theories from assembly/analyses.yaml.

Six kinds of output, one registry:

  src/Analyses/<Domain>/generated/<Domain>_Assembly.thy   the unit-context
      instances, one `global_interpretation` of `unit_dg_analysis` per
      published solver discipline
  src/Analyses/<Domain>/generated/<Domain>_Analyses.thy   the contextual
      registrations, one per context and solver the domain registers; a domain
      with hand-written contextual content names another theory
      (`registrations.theory`)
  src/Analyses/<Domain>/generated/<Domain>_Checks.thy   the published runtime
      names, bound to the assembly's instances
  src/Analyses/<Domain>/generated/<Domain>_Entry.thy   the runtime API and its
      production soundness: each discipline's endpoints, read through the
      equation that renames the assembly's state reader to the published result
      table
  src/Executable_Surface/CLI/generated/Dispatch_Tables.thy   `analyse` and the
      three domain/solver tables beside it
  src/Executable_Surface/CLI/generated/Config_Tables.thy     the resolver over
      domain, solver and context

Every output lives under `generated/`, so the path itself says the file is not
hand-editable. Nothing downstream sees that: an import names a theory, never a
directory, and `directories "generated"` is already on each session's search
path, so a generated theory keeps its bare name and its consumers and ROOT entry
are untouched.

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

This is a host writer, and a running Isabelle session does not notice it. That
holds for a regeneration in place as much as for a file deleted and recreated
elsewhere: same path, same theory name, no ROOT change, no `Duplicate theory
name` exception -- nothing announces itself, and the session goes on serving
the bytes it loaded. Diagnostics taken after a run of this generator describe
the previous render until the session is restarted, and because a regeneration
moves lines, they will cite offsets whose content has changed underneath.
Restart before believing them, or compare the buffer against disk at a line
the run changed.
"""

import argparse
import difflib
import re
import sys
from pathlib import Path

import yaml

MAX_LINE = 100
# What the operand packer fills to. Deliberately below MAX_LINE so a rename has
# room to grow without pushing a generated line past the layout rule.
PACK_WIDTH = 90

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
    ("root_query", "root_query"),
    ("solution", "solution"), ("terminates", "terminates"),
    ("vars", "sol_vars"), ("result", "result"),
    ("state_at", "state_at"), ("report", "report"),
]

# How a second registration of the same context names itself.
SOLVER_BINDER_SUFFIX = {"always_join": "join", "per_origin": "po",
                        "warrowing_apinis": "warrow", "warrowing_per_origin": "wpo"}

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
        # What the theory layer registers, as opposed to what the CLI resolves.
        # A domain may register a context it does not expose, so the two can
        # come apart and the emitter must read only this.
        regs = dict(entry.get("registrations", {}))
        # Domain-level, not per context: which pinned role arguments a
        # contextual registration leaves free. The unit registration cannot --
        # a `global_interpretation` fixes every parameter -- so this applies to
        # the contextual ones only, and applies to all of them alike.
        self.generalize = regs.pop("generalize", {})
        # Generated in place under the domain's existing theory name, so no
        # importer and no ROOT entry changes: `directories "generated"` is
        # already on the search path. A domain with hand-written content left
        # names a separate theory for the generated half instead.
        self.ctx_theory = regs.pop("theory", f"{self.name}_Analyses")
        # Adopted per domain, like the assembly: an unadopted contextual theory
        # renders under `--out` and is neither written nor compared, so the
        # migration moves one domain at a time.
        self.ctx_adopted = regs.pop("adopted", False)
        self.registrations = regs
        # The runtime API layer: one block of endpoints per solver discipline
        # the domain publishes soundness for. Absent means the domain keeps a
        # hand-written entry theory, which is what a domain with content that is
        # not transport has to do.
        ent = dict(entry.get("entry", {}))
        self.entry_adopted = ent.pop("adopted", False)
        self.entry_theory = ent.pop("theory", f"{self.name}_Entry")
        self.entry_path = ent.pop(
            "path", f"src/Analyses/{self.name}/generated/{self.entry_theory}.thy")
        self.entry_imports = ent.pop(
            "imports", [f"{self.name}_Checks"])
        self.entry_hide = ent.pop("hide_consts", [])
        self.entry_routes = ent.pop("routes", {})
        # The published runtime names: what the CLI and the entry layer call the
        # assembly's instances. Absent means the domain keeps a hand-written
        # checks theory, which is what a domain with content that is not a
        # binding has to do.
        chk = dict(entry.get("checks", {}))
        self.checks_adopted = chk.pop("adopted", False)
        self.checks_theory = chk.pop("theory", f"{self.name}_Checks")
        self.checks_path = chk.pop(
            "path", f"src/Analyses/{self.name}/generated/{self.checks_theory}.thy")
        self.checks_prefix = chk.pop("ctx_prefix", "")
        self.checks_imports = chk.pop("imports", [])
        self.checks_hide = chk.pop("hide_consts", [])
        self.checks_routes = chk.pop("routes", {})
        legacy = entry.get("legacy", {})
        self.legacy = legacy
        self.impl = legacy.get("impl_prefix", self.name.lower())
        self.theory = f"{self.name}_Assembly"
        self.path = f"src/Analyses/{self.name}/generated/{self.theory}.thy"
        self.ctx_path = (f"src/Analyses/{self.name}/generated/"
                         f"{self.ctx_theory}.thy")
        self.constructor = f"{self.name}_Analysis"
        self.plan = f"Plan_{self.name}"

    def imports(self):
        own = [f"{self.name}_Classify", f"{self.name}_Transfer",
               f"{self.name}_Sound"]
        return own + ASSEMBLY_IMPORTS + self.legacy.get("extra_imports", [])

    def binder(self, route):
        return self.legacy.get("binders", {}).get(route, f"{self.impl}_{route}")

    def ctx_binder(self, ctx, solver=None):
        """The binder for one contextual registration.

        A context's first published solver takes the plain name; a second is
        distinguished by its solver, since both registrations coexist in one
        theory and one `context` block.
        """
        override = self.legacy.get("ctx_binders", {}).get(ctx)
        if override:
            return override
        base = f"{self.name.lower()}_{CONTEXT_PARAMS[ctx]['binder_suffix']}"
        solvers = self.registrations.get(ctx, {}).get("solvers", [])
        if solver is None or not solvers or solver == solvers[0]:
            return base
        return f"{base}_{SOLVER_BINDER_SUFFIX[solver]}"

    def check_solver_order(self, ctx):
        """The first listed solver owns the route's public names.

        `ctx_binder` and `solver_suffix` both give the first entry the plain
        name, so it is what `interval_es` and every alias defined from it mean.
        Reordering the list therefore rebinds those names to another discipline
        while every citation keeps typechecking -- a change no build catches.
        Pinning the first entry to the declared default makes that mechanical.
        """
        reg = self.registrations.get(ctx, {})
        solvers = reg.get("solvers", [])
        default = reg.get("default")
        if not solvers or default is None or solvers[0] == default:
            return
        # Only a route that publishes through `defines` can be harmed: there the
        # first solver owns route-wide constant names. A route inside a
        # `context fixes` block publishes none, so its first solver owns only
        # alias spellings -- confusing to read, but nothing silently rebinds.
        # Int is that case deliberately and predates this check.
        if context_binders(self, ctx):
            return
        raise SystemExit(
            f"{self.name}.{ctx}: solvers[0] is {solvers[0]!r} but default is "
            f"{default!r}. The first solver owns the unsuffixed binder and the "
            f"route's public names, so it must be the default; reordering it "
            f"silently rebinds them."
        )

    def solver_suffix(self, ctx, solver):
        """A context's first published solver takes the plain name; a second is
        suffixed by its solver, at the end of the whole name."""
        solvers = self.registrations.get(ctx, {}).get("solvers", [])
        if not solvers or solver == solvers[0]:
            return ""
        return f"_{SOLVER_BINDER_SUFFIX[solver]}"

    def publishes(self, ctx):
        """Which solvers publish their constants from this theory.

        Registrations must all live here -- solvers of one context share a
        `context fixes` block and an interpretation's re-exports cannot leave
        it. Published constants are free-standing definitions, so a domain may
        put an alternative discipline's in a theory of its own; Int does. Not
        inferable from shape, so the registry says it.
        """
        reg = self.registrations.get(ctx, {})
        return reg.get("publishes", reg.get("solvers", [])[:1])

    def published(self, ctx):
        """Which constants this domain publishes for a context.

        Defaults to the shape Sign uses. Not derivable: the tree is not uniform
        and neither difference has an external consumer, so a domain that
        differs says so rather than having its surface changed by generation.
        """
        return self.registrations.get(ctx, {}).get(
            "published",
            ["result", "report", "terminates", "terminates_of_solve_c"])

    def ctx_defines(self, ctx):
        """The published names of a contextual registration.

        Derived from the domain's lowercase name -- not `impl_prefix`, which is
        the implementation's spelling and diverges from the published one
        (Interval publishes `interval_entry_state_spec` while implementing as
        `ivl`). A domain whose published names predate this convention gives the
        whole ordered list in `legacy.ctx_defines`.
        """
        override = self.legacy.get("ctx_defines", {}).get(ctx)
        if override:
            return [(published, const) for entry in override
                    for published, const in entry.items()]
        return [(name.format(dom=self.name.lower()), const)
                for name, const in ENTRY_STATE_DEFINES]

    def prefix(self, route):
        return self.legacy.get("prefixes", {}).get(route, f"{self.impl}_{route}")

    def checks_names(self, route):
        """One discipline's checks entry with its defaults filled in."""
        names = self.checks_routes.get(route)
        if names is None:
            return None
        first = route == self.routes[0]
        return dict(names, ctx_prefix=self.checks_prefix,
                    published=names.get(
                        "published", CHECKS_FULL if first else CHECKS_SIBLING))

    def report(self, route, with_state=False):
        """What the dispatcher calls for this discipline.

        A domain that publishes its runtime names from a generated checks
        theory names the report there, so the dispatcher reads that spelling
        rather than a second copy of it. Only the state-carrying report needs a
        case: a discipline that does not publish one of its own is read through
        its \\<^locale>\\<open>analysis_surface\\<close> interpretation instead.
        """
        spec = self.legacy.get("routes", {}).get(route)
        key = "report_with_state" if with_state else "report"
        if spec and key in spec:
            return spec[key]
        names = self.checks_names(route)
        if names:
            if key in names["published"]:
                return checks_spellings(self, route, names)[key]
            return f"{names['surface']}.{key}"
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
            # The transfer functions are the domain's own constants, but the
            # theorems about them come from the `nonrelational_transfer`
            # interpretation and are cited under its prefix rather than
            # re-exported under a domain-prefixed alias.
            "transfer_sound": f"{i}_tf.is_sound_transfer_for",
            "tf_commute": f"{i}_tf_st_for_commute",
            "tf_abs_def": f"{i}_tf.tf_abs_def",
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


def role_term(role, generalize=None):
    """A role in term position: a bare name, or a quoted application.

    An applied role must be one argument to the interpretation, and Isabelle
    reads a quoted term as one argument. Only `const` and `args` are honoured,
    so a role can never smuggle in arbitrary syntax.

    `generalize` maps a pinned argument to the binder that replaces it, so a
    registration that leaves a configuration parameter free renders the same
    roles against that binder. The substitution is by value rather than by
    position, so it does not depend on how many arguments a role takes.
    """
    if isinstance(role, dict):
        subst = generalize or {}
        args = " ".join(subst.get(str(a), {}).get("binder", str(a))
                        for a in role["args"])
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
    """One `global_interpretation`, with the same twelve discharges every time."""
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

    out += obligations(f, interp, UNIT_HEADER, UNIT_CASE4)
    return out


# The unit locale adds no axioms of its own, so its `intro` leaves the parent's
# predicate as one goal; the parent's own `intro` splits that into the twelve
# assumptions. `unfold_locales` would go further and decompose the transfer
# bundle per operation, which the domain's whole-bundle soundness rule cannot
# discharge one goal at a time. A contextual registration interprets the parent
# directly and so needs only the parent's `intro`.
UNIT_HEADER = ["proof (rule unit_dg_analysis.intro, rule routed_dg_analysis.intro,",
               "       goal_cases)"]
ROUTED_HEADER = ["proof (rule routed_dg_analysis.intro, goal_cases)"]

# Obligation 4 says the route reads only what the abstraction preserves. At the
# unit context the route is constant, so it is trivial; elsewhere it is the one
# obligation that carries the context's own content.
UNIT_CASE4 = ["  case (4 gs u ctx d ca) show ?case by simp"]


def obligations(f, interp, header, case4):
    """The twelve routed obligations. Every registration discharges the same
    twelve in the same order; only the header and obligation 4 vary."""
    out = list(header)
    out += [
        f"  case (1 gs) show ?case by (rule {role_name(f['transfer_sound'])})",
        "next",
        "  case (2 gs a s) then show ?case",
        "    unfolding fun_of_exec_dg_st_for_def",
        f"    by (rule {role_name(f['tf_commute'])}[unfolded {role_name(f['tf_abs_def'])}])",
        "next",
        "  case (3 gs ci s) show ?case",
        f"    unfolding fun_of_exec_dg_st_for_def by (rule {role_name(f['enter_commute'])})",
        "next",
    ]
    # Obligation 4 is the caller's: at the unit context the route ignores the
    # state and it is trivial, elsewhere it carries the context's own content.
    out += case4
    out += [
        "next",
        # The seed key is a different constructor from the global one. Inherited
        # from the routed parent and independent of the domain.
        "  case (5 v ctx) show ?case by simp",
        "next",
        "  case (6 eqs x) then show ?case",
    ]
    out += rule_step(f"{interp}.partial_post_solution[OF _ surjective_pairing]")
    out += ["next", "  case (7 eqs x) then show ?case"]
    out += rule_step(f"{interp}.finite_stabl_solve")
    out += [
        "next",
        f"  case (8 c d s) then show ?case by (rule {role_name(f['classifier'])}_proved)",
        "next",
        f"  case (9 c d s) then show ?case by (rule {role_name(f['classifier'])}_refuted)",
        "next",
        "  case 10 show ?case by (rule refl)",
        "next",
        f"  case (11 gs) show ?case by (rule {role_name(f['init_gamma'])})",
        "next",
        "  case (12 eqs x) then show ?case",
    ]
    out += rule_step(f"{interp}.solve_dom_of_solve_c")
    out.append("qed")
    return out


# A contextual registration differs from the unit one in seven positional
# arguments and in obligation 4. `route` is the executable route and `route_abs`
# the abstract one; they coincide everywhere except entry state, where the
# difference between them is the whole content of obligation 4.
CONTEXT_PARAMS = {
    "entry_state": {
        "binder_suffix": "es",
        "gk": lambda vt: f"(unit, {vt} list) routed_gk",
        "global": '"Analysis_Global ()"',
        "seed": "Activation_Seed",
        "route": "exec_formals_route",
        "root_ctx": '"[]"',
        "route_abs": '"\\<lambda>_. formals_route_lifted_gen"',
        "case4": ["  case (4 gs u ctx d ca) show ?case",
                  "    unfolding fun_of_exec_dg_st_for_def",
                  "    by (rule exec_formals_route_commute[symmetric])"],
        "ctx_type": lambda vt: f"{vt} list",
        "arg": "",
        "sound": "entry_state_activation_collect_sound",
        # The two facts a source-level contextual statement needs beside the
        # per-context bound: that every valid trace carries an admitted context,
        # and the union equation that follows from it. Both rest on the same
        # entry-coverage premise `sound` already carries.
        "has_context": "entry_state_has_context",
        "union": "entry_state_ltr_collect_eq_Union",
        # The caller-facing pair: same two endpoints, but carrying one
        # `ctx_vars_cover` closure premise instead of four positional ones.
        "sound_of_cover": "entry_state_activation_collect_sound_of_cover",
        "union_of_cover": "entry_state_ltr_collect_eq_Union_of_cover",
        # The same pair with no coverage premise at all: the live keys of a
        # terminating solve are closed by construction.
        "sound_of_terminates": "entry_state_activation_collect_sound_of_terminates",
        "union_of_terminates": "entry_state_ltr_collect_eq_Union_of_terminates",
        "gamma_reader": "gamma_reader_eq_lookup",
        "vars_finite": "vars_finite_of_terminates",
    },
    "call_string": {
        "binder_suffix": "cs",
        "gk": lambda vt: "call_string_gk",
        "global": "Call_String_Context.Global",
        "seed": "Call_String_Context.Seed",
        "route": '"\\<lambda>_. cs_route k"',
        "root_ctx": '"[]"',
        "route_abs": '"\\<lambda>_. cs_route k"',
        "case4": ["  case (4 gs u ctx d ca) show ?case"
                  " by (rule cs_route_indep_of_data)"],
        "ctx_type": lambda vt: "call_string",
        "arg": "k ",
        "sound": "fun_route_activation_collect_sound[OF cs_route_context_agree]",
        # The call-string binder is a plain `interpretation` under `fixes k`, so
        # a caller outside cannot name it; this alias is the only way out.
        "gamma_reader": "gamma_reader_eq_lookup",
        "vars_finite": "vars_finite_of_terminates",
        # The functional route's source-level pair. The union side is
        # unconditional here -- a total key needs no coverage to carry a context.
        "sound_of_cover":
            "fun_route_activation_collect_sound_of_cover[OF cs_route_context_agree]",
        "sound_of_terminates":
            "fun_route_activation_collect_sound_of_terminates[OF cs_route_context_agree]",
        "union_of_cover": "fun_route_ltr_collect_eq_Union",
    },
}

# Published name -> locale constant, for an entry-state registration. A domain
# whose spellings predate this list overrides it wholesale in `legacy`, because
# the overriding domain also reorders and adds a name; a rename map alone could
# not express that.
ENTRY_STATE_DEFINES = [
    ("{dom}_entry_state_spec", "analysis_spec"),
    ("{dom}_entry_state_root_query", "root_query"),
    ("{dom}_entry_state_equations", "equations"),
    ("{dom}_entry_state_solution", "solution"),
    ("{dom}_entry_state_terminates_for", "terminates"),
    ("{dom}_entry_state_vars", "sol_vars"),
    ("{dom}_entry_state_env", "sol_env"),
    ("analyse_{dom}_entry_state_result_for", "result"),
    ("analyse_{dom}_entry_state_report_for", "verdict_report"),
    ("analyse_{dom}_entry_state_projection_for", "check_projection"),
    ("{dom}_entry_state_context_rel", "admitted_contexts"),
]


def pack_operands(groups):
    """Lay out the operand lines, one line per group where that fits.

    The groups are the reader's grouping -- the six local operations, then the
    call and event operations with the route, then the solver's decision
    procedure. A domain whose operations carry a configuration argument has
    quoted, longer roles and will not fit that way, so fall back to filling by
    width, which is what the layout rule actually requires.
    """
    lines = ["    " + " ".join(gs) for gs in groups if gs]
    if all(symbol_len(l) <= MAX_LINE for l in lines):
        return lines
    # Fill to a narrower budget than the layout limit. A line filled exactly to
    # the limit has no headroom: renaming a domain re-renders it one symbol too
    # long, and nothing would catch that, because the drift gate compares
    # generated against checked-in and both sides move together.
    out, line = [], "   "
    for op in [op for gs in groups for op in gs]:
        if symbol_len(f"{line} {op}") > PACK_WIDTH:
            out.append(line)
            line = "   "
        line = f"{line} {op}"
    out.append(line)
    return out


def context_binders(dom, ctx):
    """What the enclosing `context fixes` block binds, if anything.

    One block per context, not per registration: a domain with two solvers at
    one context puts both interpretations inside the same block, and opening a
    second would fix the same binder twice.
    """
    binders = [f"{v['binder']} :: {v['type']}" for v in (dom.generalize or {}).values()]
    if ctx == "call_string":
        binders.append("k :: nat")
    return binders


def contextual_interpretation(dom, ctx, route, solvers, generalize=None):
    """One contextual interpretation of `routed_dg_analysis`.

    The unit registration interprets `unit_dg_analysis`, which fixes the
    context to `unit`; here the context terms come from `CONTEXT_PARAMS`, the
    solvers from the registry's `registrations:` entry, and the locale is the
    parent directly. It is a `global_interpretation` unless an enclosing
    `context fixes` block leaves a parameter free.
    """
    f = dom.facts()
    p = CONTEXT_PARAMS[ctx]
    interp = solvers[route]["interp"]
    binder = dom.ctx_binder(ctx, route)
    term = {k: role_term(v, generalize) for k, v in f.items()}
    vt = dom.value_type
    # A `global_interpretation` cannot leave a parameter free, so any
    # registration with a free parameter is a plain `interpretation` inside a
    # `context fixes` block and publishes by direct application rather than by
    # `defines` renaming. A call-string bound is always such a parameter; a
    # domain that generalises a pinned configuration argument adds its own.
    fixed = bool(context_binders(dom, ctx))
    out = [
        f"{'' if fixed else 'global_'}interpretation {binder}: routed_dg_analysis",
        f"    {term['tf_st']} {term['enter_st']} {term['init_st']}",
        f"    {p['global']} {p['seed']} {p['route']} {p['root_ctx']}",
        f"    {interp}_solve",
        f'    "{interp}.solve_dom TYPE({p["gk"](vt)})',
        f"       TYPE(({vt} exec_dg_st lifted, {vt} exec_dg_st lifted) dg_state)\"",
        f"    bot {term['classifier']}",
    ]
    out += pack_operands([
        [term[k] for k in ["skip", "assign", "special", "branch", "body", "return"]],
        [term["enter_ci"], term["event"], p["route_abs"]],
        [f"{interp}_solve_c"],
    ])
    # The published names are route-wide, not per-discipline, so only the
    # registration that owns the unsuffixed binder may claim them; a second
    # discipline repeating the block would be a duplicate definition. The others
    # are reached through their own binder, which a `global_interpretation`
    # exports anyway.
    if not fixed and not dom.solver_suffix(ctx, route):
        out += ["  defines"]
        for i, (published, const) in enumerate(dom.ctx_defines(ctx)):
            out.append(f"    {'' if i == 0 else 'and '}{published} = {binder}.{const}")
    out += obligations(f, interp, ROUTED_HEADER, p["case4"])
    return out


def term_of(quoted):
    """A registration argument in term position.

    The interpretation takes each argument quoted, which is how Isabelle reads a
    term as one argument; inside a definition body the same term is written
    plainly, parenthesised when it is an application.
    """
    if not quoted.startswith('"'):
        return quoted
    inner = quoted[1:-1]
    return f"({inner})" if " " in inner else inner


def published_constants(dom, ctx, route, solvers):
    """The constants a domain publishes for one registration.

    Which ones is registry data, because it is not derivable and the tree is
    not uniform: Sign publishes a `terminates` and no `_for` hop at call
    strings, Int publishes the hop and no `terminates`. Neither difference has
    an external consumer, so unifying them is a change worth making
    deliberately rather than as a side effect of generating them.

    How each is built *is* derivable. A `_for` hop applies the pipeline at an
    explicit global predicate; a plain constant instantiates the hop at the
    program's own, or applies the pipeline directly when there is no hop to
    instantiate -- which is the case exactly when the registration has no
    `defines` and the domain publishes no hop of its own.
    """
    f = dom.facts()
    p = CONTEXT_PARAMS[ctx]
    interp = solvers[route]["interp"]
    d, vt = dom.name.lower(), dom.value_type
    # In term position inside a definition body, not as an interpretation
    # argument: an applied role is quoted for the latter and must not be for
    # the former, or the body's own quoting is broken by the nested pair.
    term = {k: term_of(role_term(v)) for k, v in f.items()}
    arg, ctx_ty = p["arg"], p["ctx_type"](vt)
    sfx = dom.solver_suffix(ctx, route)
    lead = "nat \\<Rightarrow> " if ctx == "call_string" else ""
    pipe = ["    " + " ".join([term["tf_st"], term["enter_st"], term["init_st"]]),
            "      " + " ".join([term_of(p["global"]), term_of(p["seed"]),
                                 term_of(p["route"]), term_of(p["root_ctx"])])]
    RESULT_TY = f"({ctx_ty}, {vt} abs_state) analysis_result"
    REPORT_TY = "(pp \\<times> exp \\<times> contextual_verdict) list"
    kinds = dom.published(ctx)
    # A hop exists when the domain publishes one, or when a `defines` list
    # already produced it -- an entry-state registration that is not
    # generalised binds `analyse_<d>_entry_state_<k>_for` there.
    def has_hop(k):
        return (f"{k}_for" in kinds
                or (ctx == "entry_state" and not dom.generalize))

    out = []
    for kind in kinds:
        if kind == "terminates_of_solve_c":
            continue          # a `lemmas` re-export, rendered with the registration
        base = f"analyse_{d}_{ctx}_{kind}"
        if kind.endswith("_for"):
            k = kind[:-4]
            op = "result" if k == "result" else "verdict_report"
            extra = "" if k == "result" else f" {term['classifier']}"
            ty = RESULT_TY if k == "result" else REPORT_TY
            out += [f"definition {base}{sfx} ::",
                    f'    "{lead}(vname \\<Rightarrow> bool) \\<Rightarrow> imp_prog'
                    f' \\<Rightarrow> {ty}" where',
                    f'  "{base}{sfx} {arg}gs p =',
                    f"     routed_dg_pipeline.{op}"] + pipe + [
                    f'       {interp}_solve{extra} gs p"', ""]
        elif kind == "terminates":
            if ctx == "entry_state" and not dom.generalize:
                out += [f'definition {base}{sfx} :: "imp_prog \\<Rightarrow> bool" where',
                        f'  "{base}{sfx} p =',
                        f'     {d}_entry_state_terminates_for (declared_global p) p"', ""]
            else:
                out += [f"definition {base}{sfx} ::",
                        f'    "{lead}imp_prog \\<Rightarrow> bool" where',
                        f'  "{base}{sfx} {arg}p =',
                        "     routed_dg_pipeline.terminates"] + pipe + [
                        f"       ({interp}.solve_dom TYPE({p['gk'](vt)})",
                        f"          TYPE(({vt} exec_dg_st lifted,"
                        f" {vt} exec_dg_st lifted) dg_state))",
                        '       (declared_global p) p"', ""]
        else:
            op = "result" if kind == "result" else "verdict_report"
            extra = "" if kind == "result" else f" {term['classifier']}"
            ty = RESULT_TY if kind == "result" else REPORT_TY
            head = [f"definition {base}{sfx} ::",
                    f'    "{lead}imp_prog \\<Rightarrow> {ty}" where',
                    f'  "{base}{sfx} {arg}p =']
            if has_hop(kind):
                out += head + [
                    f'     {base}_for{sfx} {arg}(declared_global p) p"', ""]
            else:
                out += head + [f"     routed_dg_pipeline.{op}"] + pipe + [
                    f'       {interp}_solve{extra} (declared_global p) p"', ""]
    return out


def soundness_lemmas(dom, ctx, route, solvers):
    """The re-exports, one set per registration.

    These must sit inside the registration's own block: an `interpretation`
    does not export outside its context, so a `lemmas` citing the binder is
    part of the registration rather than something beside it. A second solver
    gets its own set, suffixed the way the tree already spells the alternative
    disciplines -- at the end of the whole name, after any `_for`.
    """
    p, d = CONTEXT_PARAMS[ctx], dom.name.lower()
    binder = dom.ctx_binder(ctx, route)
    sfx = dom.solver_suffix(ctx, route)
    # A domain whose re-exports predate this convention names them. These have
    # to travel with the registration -- an `interpretation` does not export
    # outside its context -- so unlike the published constants they cannot be
    # left hand-written, and naming them is not the registry carrying code.
    reg = dom.registrations.get(ctx, {})
    # Absent means the convention; present means exactly these, and an empty
    # mapping means none -- which is what a domain says when its re-exports
    # resolve from an importing theory and can stay hand-written.
    names = reg.get("re_exports")
    if names is None:
        names = {"sound": f"analyse_{d}_{ctx}_sound"}
        names["gamma_reader"] = f"analyse_{d}_{ctx}_gamma_reader_eq_lookup"
        names["vars_finite"] = f"analyse_{d}_{ctx}_vars_finite"
        if ctx == "call_string":
            names["sound_of_cover"] = f"analyse_{d}_call_string_sound_of_cover"
            names["sound_of_terminates"] = f"analyse_{d}_call_string_sound_of_terminates"
            names["union_of_cover"] = (
                f"analyse_{d}_call_string_ltr_collect_eq_Union")
        if ctx == "entry_state":
            names["has_context"] = f"analyse_{d}_entry_state_has_context"
            names["union"] = f"analyse_{d}_entry_state_ltr_collect_eq_Union"
            names["sound_of_cover"] = f"analyse_{d}_entry_state_sound_of_cover"
            names["union_of_cover"] = (
                f"analyse_{d}_entry_state_ltr_collect_eq_Union_of_cover")
            names["sound_of_terminates"] = f"analyse_{d}_entry_state_sound_of_terminates"
            names["union_of_terminates"] = (
                f"analyse_{d}_entry_state_ltr_collect_eq_Union_of_terminates")
        if ctx == "call_string" and "terminates_of_solve_c" in dom.published(ctx):
            names["terminates_of_solve_c"] = (
                f"analyse_{d}_call_string_terminates_of_solve_c")
    out = []
    if "sound" in names:
        out += [f"lemmas {names['sound']}{sfx} =", f"  {binder}.{p['sound']}", ""]
    # Guarded on the route, not just on the name: only entry state has these,
    # since a functional route earns its union equation without a witness.
    for key in ("has_context", "union", "sound_of_cover", "union_of_cover",
                "sound_of_terminates", "union_of_terminates",
                "gamma_reader", "vars_finite"):
        if key in names and key in p:
            out += [f"lemmas {names[key]}{sfx} =", f"  {binder}.{p[key]}", ""]
    # Listed, not derived. A domain could publish `terminates` without
    # exporting its discharge rule, or export the rule for a `terminates` a
    # downstream theory owns; nothing in the locale forbids either. Deriving
    # the link would be the generator asserting a shape rather than reading one.
    if "terminates_of_solve_c" in names:
        out += [f"lemmas {names['terminates_of_solve_c']}{sfx} =",
                f"  {binder}.terminates_of_solve_c", ""]
    return out


# Named explicitly rather than relied on transitively. `declared_global` comes
# from VIMP_Program and `formals_route_lifted_gen` from Routed_Context; both
# would resolve through the domain's own imports, but an implicit dependency is
# what turns a later unrelated import prune into a failure nobody can place.
CONTEXTUAL_IMPORTS = ['"Voblint_Result.Routed_Live_Keys"',
                      '"Voblint_Framework.Call_String_Context"',
                      '"Voblint_Framework.Routed_Context"',
                      '"Voblint_Solver.TD_Solver_Bridge"',
                      '"Voblint_VIMP.VIMP_Program"',
                      '"TD.TD_side_upd_rule"']

CONTEXT_TITLE = {
    "call_string": "call-string",
    "entry_state": "entry-state",
}


def render_contextual(dom, solvers):
    """A domain's contextual registrations, as one generated theory.

    Ordered as the reader needs it and as the hand-written originals were: each
    registration with the re-exports that must share its block, then the
    constants that registration publishes.
    """
    out = [f"theory {dom.ctx_theory}", "  imports"]
    # Exactly what the hand-written theory imported, never less. A generated
    # theory replacing a hand-written one inherits its consumers, and an import
    # dropped here fails in those consumers rather than here -- `Sign_Assembly`
    # went missing this way and took `Sign_Checks` and `Sign_Entry` with it,
    # while the generated theory itself stayed clean. The lists differ per
    # domain (Interval imports `_Exec_Sound`, Int imports neither its assembly
    # nor its transfer), so this is registry data, captured per domain.
    imports = dom.legacy.get("ctx_imports")
    if imports is None:
        imports = [f"{dom.name}_{t}"
                   for t in ["Sound", "Assembly", "Classify", "Transfer", "Exec"]
                   ] + CONTEXTUAL_IMPORTS
    out += [f"    {i}" for i in imports] + ["begin", ""]
    out += text_block(GENERATED_NOTICE) + [""]
    for ctx in CONTEXT_ORDER:
        reg = dom.registrations.get(ctx)
        if not reg:
            continue
        dom.check_solver_order(ctx)
        title = CONTEXT_TITLE[ctx]
        out += [f"section \\<open>{dom.name} at the {title} context\\<close>", ""]
        # `generalize:` is one registry decision with seven consequences known
        # so far, and expect an eighth: `defines` does four separate jobs --
        # it names constants, exports a binder, supplies the `_for` hops, and
        # makes a registration a `global_interpretation` -- so a registration
        # without one loses four things at once, and each loss surfaces
        # somewhere different. Seven symptoms, four causes, one overloaded
        # mechanism. The consequences here are: the registration is a plain
        # `interpretation` rather
        # than a `global_interpretation`; it has no `defines`, so there is no
        # `_spec` constant to declare `[code_unfold]`; its published constants
        # apply the pipeline directly instead of wrapping renamed names; and
        # its `_for` hop is a definition rather than a `defines` entry. They
        # are listed together because finding them one at a time is what cost
        # us Int.
        binders = context_binders(dom, ctx)
        if binders:
            out += ["context", "  fixes " + " and ".join(binders), "begin", ""]
        for solver in reg["solvers"]:
            out += contextual_interpretation(
                dom, ctx, solver, solvers, dom.generalize) + [""]
            # Inside the block whenever there is one. An `interpretation` does
            # not export beyond its context, so a `lemmas` citing its binder
            # must share it; only a `global_interpretation`, which has no
            # enclosing block, can be re-exported from outside. Deciding this
            # per context kind rather than per registration is right for a
            # domain that pins and wrong for one that generalises.
            if binders:
                out += soundness_lemmas(dom, ctx, solver, solvers)
        if binders:
            out += ["end", ""]
        if not dom.generalize and ctx == "entry_state":
            out += [f"declare {dom.name.lower()}_entry_state_spec_def"
                    " [code_unfold]", ""]
        # Registrations are all here -- solvers of one context share a `context
        # fixes` block. Published constants need not be: a domain may keep an
        # alternative discipline's in a theory of its own, and Int does, so
        # emitting them here would duplicate a definition its consumer owns.
        for solver in (dom.publishes(ctx) if dom.published(ctx) else []):
            out += [f"subsection \\<open>The published {title} constants"
                    f"{dom.solver_suffix(ctx, solver) and ': ' + solvers[solver]['title'].lower()}"
                    "\\<close>", ""]
            out += published_constants(dom, ctx, solver, solvers)
        if not binders:
            for solver in reg["solvers"]:
                out += soundness_lemmas(dom, ctx, solver, solvers)
    out.append("end")
    return "\n".join(out) + "\n"


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


# --- The runtime API and its production soundness ----------------------------

# What a rendered entry line fills to. Below MAX_LINE for the same reason the
# operand packer is: a longer domain name must have room to grow before the
# layout rule is what fails.
ENTRY_WIDTH = 95


def either(one, wrapped):
    """The one-line form where it fits the entry budget, the wrapped form
    otherwise. Both spellings are written out, so a rename changes which one is
    picked and never how the wrapped form reads."""
    return [one] if symbol_len(one) <= ENTRY_WIDTH else list(wrapped)


def closure_assumptions(names, and_ind):
    """The five facts the routed solve turns on, as `assumes`.

    Termination, entry coverage and the three forward-closure conditions. Stated
    once per discipline rather than repeated on every theorem; `and_ind` is 4
    inside a `context` and 6 inside a corollary, which is the only difference
    between the two places they appear.
    """
    a, c = " " * and_ind, " " * (and_ind + 4)
    fst = f"fst ({names['sol']} (declared_global p) p)"
    out = [f'  assumes solve: "{names["terminates"]} (declared_global p) p"',
           f'{a}and entry_cov: "(cfg_entry (prog_cfg p), ())',
           f'{c}\\<in> {fst}"']
    out += either(f'{a}and fwd_ok: "\\<And>u a w ctx. (u, ctx) \\<in> {fst}',
                  [f'{a}and fwd_ok: "\\<And>u a w ctx.',
                   f'{c}(u, ctx) \\<in> {fst}'])
    out += [f"{c}\\<Longrightarrow> (u, a, w) \\<in> intra (prog_cfg p)",
            f'{c}\\<Longrightarrow> (w, ctx) \\<in> {fst}"',
            f'{a}and call_fwd_ok: "\\<And>u ctx dst fs as q k.',
            f"{c}(u, ctx) \\<in> {fst}",
            f"{c}\\<Longrightarrow> (u, CallEdge dst fs as, FunctionEntry q, k)"
            " \\<in> calls (prog_cfg p)"]
    out += either(f'{c}\\<Longrightarrow> (FunctionEntry q, ()) \\<in> {fst}"',
                  [f"{c}\\<Longrightarrow> (FunctionEntry q, ())",
                   f'{c}      \\<in> {fst}"'])
    out += [f'{a}and comb_fwd_ok: "\\<And>cl c1 dst fs as q k.',
            f"{c}(cl, c1) \\<in> {fst}",
            f"{c}\\<Longrightarrow> (cl, CallEdge dst fs as, FunctionEntry q, k)"
            " \\<in> calls (prog_cfg p)",
            f'{c}\\<Longrightarrow> (k, c1) \\<in> {fst}"']
    return out


def result_cap(tbl, at, lead, cont, bot):
    """The concretization of one node's table entry, as the right-hand side of a
    subset or a membership.

    `tbl` is the applied result table, `at` the node it is read at, `lead` the
    text the first line opens with, and `cont`/`bot` the columns the wrapped
    table and the dead-code case align to.
    """
    return either(f"{lead}\\<lbrakk>case lookup_context ({tbl}) {at} of",
                  [f"{lead}\\<lbrakk>case lookup_context",
                   f"{' ' * cont}({tbl}) {at} of"]) + [
        f"{' ' * bot}Bot \\<Rightarrow> bot | Lifted st"
        " \\<Rightarrow> st\\<rbrakk>\""]


def entry_state_at(dom, route, names):
    p, b = dom.prefix(route), dom.binder(route)
    rf = names["result_for"]
    return [f"lemma {p}_state_at_eq:",
            f'  "{p}_state_at gs p v',
            f"     = (case lookup_context ({rf} gs p) v () of",
            "          Bot \\<Rightarrow> bot | Lifted st \\<Rightarrow> st)\"",
            f"  by (simp add: {b}.state_at_unfold {rf}_def)"]


def entry_reports(dom, route, names):
    """The two check-report endpoints, inside the discipline's own block."""
    b, cl = dom.binder(route), names["closure"]
    rp = names["report_for"]
    base = rp[:-len("_for")]
    out = []
    for verdict, sense in [("Proved", "truthy (aval c s)"),
                           ("Refuted", "\\<not> truthy (aval c s)")]:
        out += [f"theorem {base}_sound_{verdict.lower()}_for:",
                "  fixes v :: pp and c :: exp"]
        out += either(
            f'  assumes mem: "(v, c, Check_{verdict})'
            f' \\<in> set ({rp} (declared_global p) p)"',
            [f'  assumes mem: "(v, c, Check_{verdict})',
             f'      \\<in> set ({rp} (declared_global p) p)"'])
        out += ['  shows "\\<forall>s \\<in> ltr_collect (declared_global p)'
                " (prog_cfg p)",
                f'                (cinit_stores (declared_global p)) v. {sense}"',
                f"  by (rule {b}.report_{verdict.lower()}_sound_closure",
                f"        [OF {cl} mem[unfolded {rp}_def]])", ""]
    return out


def entry_discipline(dom, route, names):
    """One discipline's block: the closure bundle and the endpoints that read
    the table it produces."""
    b, cl, rf = dom.binder(route), names["closure"], names["result_for"]
    out = ["context", "  fixes p :: imp_prog"]
    out += closure_assumptions(names, 4) + ["begin", ""]
    out += [f"lemmas {cl} =", "  solve"]
    out += [f"  {f}[unfolded {b}.sol_vars_def[symmetric]]"
            for f in ["fwd_ok", "call_fwd_ok", "comb_fwd_ok", "entry_cov"]]
    out += ["", f"lemma {rf[:-len('_for')]}_node_sound_for:",
            '  "ltr_collect (declared_global p) (prog_cfg p)'
            " (cinit_stores (declared_global p)) v"]
    out += result_cap(f"{rf} (declared_global p) p", "v ()",
                      "     \\<subseteq> ", 14, 23)
    out += [f"  using {b}.result_node_sound_closure[OF {cl}]",
            f"  unfolding {dom.prefix(route)}_state_at_eq .", ""]
    out += entry_reports(dom, route, names)
    out += ["end", ""]
    return out


def entry_coverage(dom, route, names):
    """The decidable side condition, and the two source-level readings that take
    it. Only a discipline whose endpoints are published in full carries these."""
    b, sol, rf = dom.binder(route), names["sol"], names["result_for"]
    unfold = f"cover[unfolded {b}.sol_vars_def[symmetric]]"
    fst = f"fst ({sol} (declared_global p) p)"
    out = ["subsection \\<open>Coverage as one checkable side condition\\<close>", ""]
    out += text_block(fill(COVERAGE_TEXT)) + ["", "context",
                                              "  fixes p :: imp_prog", "begin", ""]
    out += [f"lemma {names['cover']}:"]
    out += either(f'  assumes cover: "vars_cover_exec (prog_cfg p) ({fst})"',
                  ['  assumes cover: "vars_cover_exec (prog_cfg p)',
                   f'      ({fst})"'])
    out += either(f'  shows "vars_cover (prog_cfg p) ({fst})"',
                  ['  shows "vars_cover (prog_cfg p)',
                   f'      ({fst})"'])
    out += either(
        f"  by (rule {b}.vars_cover_of_exec_prog[unfolded {b}.sol_vars_def, OF cover])",
        [f"  by (rule {b}.vars_cover_of_exec_prog",
         f"        [unfolded {b}.sol_vars_def, OF cover])"]) + [""]

    out += [f"lemma {rf[:-len('_for')]}_node_sound_of_cover:",
            f'  assumes solve: "{names["terminates"]} (declared_global p) p"']
    out += either(f'    and cover: "vars_cover (prog_cfg p) ({fst})"',
                  ['    and cover: "vars_cover (prog_cfg p)',
                   f'                  ({fst})"'])
    out += ['  shows "ltr_collect (declared_global p) (prog_cfg p)'
            " (cinit_stores (declared_global p)) v"]
    out += result_cap(f"{rf} (declared_global p) p", "v ()",
                      "           \\<subseteq> ", 20, 29)
    out += [f"  using {b}.result_node_sound", f"          [OF solve {unfold}]",
            f"  unfolding {dom.prefix(route)}_state_at_eq .", ""]

    out += ["subsection \\<open>Source runs, in the vocabulary the runtime API"
            " returns\\<close>", ""]
    out += text_block(fill(source_text(rf))) + [""]
    base = rf[:-len("_result_for")]
    tbl = f"{rf} (declared_global p) p"
    for kind, final in [("source", "(residual, s, frs)"),
                        ("completed_run", "(SKIP, s, [])")]:
        if kind == "completed_run":
            out += text_block(fill(COMPLETED_TEXT)) + [""]
        out += [f"theorem {base}_{kind}_sound_for:", "  fixes s0 s :: store",
                f'  assumes solve: "{names["terminates"]} (declared_global p) p"']
        out += either(f'    and cover: "vars_cover (prog_cfg p) ({fst})"',
                      ['    and cover: "vars_cover (prog_cfg p)',
                       f'                  ({fst})"'])
        out += ['    and wf: "wf_compile_input (declared_global p) (prog_table p)'
                ' (prog_procs p)"',
                '    and s0: "s0 \\<in> cinit_stores (declared_global p)"',
                '    and run: "star (pstep (declared_global p) (prog_table p))',
                f'                (main_body (prog_table p), s0, []) {final}"']
        if kind == "source":
            out += ['  shows "\\<exists>v stk. csim (prog_table p) (prog_cfg p)'
                    " (residual, s, frs) (v, s, stk)"]
            out += result_cap(tbl, "v ()",
                              "                 \\<and> s \\<in> ", 32, 37)
        else:
            out += [f'  shows "s \\<in> \\<lbrakk>case lookup_context ({tbl})',
                    "                            (cfg_exit (prog_cfg p)) () of",
                    "                          Bot \\<Rightarrow> bot | Lifted st"
                    " \\<Rightarrow> st\\<rbrakk>\""]
        out += [f"  using {b}.{kind}_sound",
                f"          [OF solve {unfold} wf s0 run]",
                f"  unfolding {dom.prefix(route)}_state_at_eq .", ""]
    out += ["end", ""]
    return out


def entry_corollaries(dom, route, names, full):
    """The same endpoints at \\<^const>\\<open>declared_global\\<close>, which is what the
    dispatcher and the CLI actually call."""
    rp, rep = names["report_for"], names["report"]
    base = rp[:-len("_for")]
    out = text_block(fill(corollary_text(rep, base))) + [""]
    for verdict, sense in [("Proved", "truthy (aval c s)"),
                           ("Refuted", "\\<not> truthy (aval c s)")]:
        out += [f"corollary {rep}_sound_{verdict.lower()}:",
                "  fixes p :: imp_prog and v :: pp and c :: exp"]
        out += closure_assumptions(names, 6)
        out += [f'      and mem: "(v, c, Check_{verdict})'
                f' \\<in> set ({rep} p)"',
                '  shows "\\<forall>s \\<in> ltr_collect (declared_global p)'
                " (prog_cfg p)",
                f'                (cinit_stores (declared_global p)) v. {sense}"',
                f"  by (rule {base}_sound_{verdict.lower()}_for",
                "        [OF solve entry_cov fwd_ok call_fwd_ok comb_fwd_ok",
                f"            mem[unfolded {rep}_def]])", ""]
    if not full:
        return out

    res, rf = names["result"], names["result_for"]
    fst = f"fst ({names['sol']} (declared_global p) p)"
    sbase = rf[:-len("_result_for")]
    out += text_block(fill(headline_text(res, names))) + [""]
    for kind, final in [("source", "(residual, s, frs)"),
                        ("completed_run", "(SKIP, s, [])")]:
        out += [f"corollary {sbase}_{kind}_sound:",
                "  fixes p :: imp_prog and s0 s :: store",
                '  assumes wf: "wf_compile_input (declared_global p)'
                ' (prog_table p) (prog_procs p)"',
                f'    and solve: "{names["terminates"]} (declared_global p) p"']
        out += either(f'    and cover: "vars_cover (prog_cfg p) ({fst})"',
                      ['    and cover: "vars_cover (prog_cfg p)',
                       f'                  ({fst})"'])
        out += ['    and s0: "s0 \\<in> cinit_stores (declared_global p)"',
                '    and run: "star (pstep (declared_global p) (prog_table p))',
                f'                (main_body (prog_table p), s0, []) {final}"']
        if kind == "source":
            out += ['  shows "\\<exists>v stk. csim (prog_table p) (prog_cfg p)'
                    " (residual, s, frs) (v, s, stk)"]
            out += result_cap(f"{res} p", "v ()",
                              "                 \\<and> s \\<in> ", 32, 37)
        else:
            out += result_cap(f"{res} p", "(cfg_exit (prog_cfg p)) ()",
                              '  shows "s \\<in> ', 9, 26)
        out += [f"  unfolding {res}_def",
                f"  by (rule {sbase}_{kind}_sound_for[OF solve cover wf s0 run])",
                ""]
    return out


COVERAGE_TEXT = """
\\<^const>\\<open>vars_cover\\<close> implies the four closure facts above, at the one
context this routed solve uses. Bundling them is what makes the side condition
decidable in a single step: \\<^const>\\<open>vars_cover_exec\\<close> walks the two edge
enumerations, so a caller discharges coverage
\\<^theory_text>\\<open>by eval\\<close> instead of by four hand-written case analyses over
the solved key set.
"""

COMPLETED_TEXT = """
The completed-run reading of the same fact, and the one a reader meets first: a
source run that finishes leaves its final store inside the analysis result at the
program exit. It is weaker --- one point instead of all of them --- but it needs no
\\<^const>\\<open>csim\\<close> witness to state.
"""


def source_text(rf):
    return f"""
What a caller of \\<^const>\\<open>{rf}\\<close> actually wants to know: run the source
program, stop anywhere, and the store you are holding is described by the entry
the analysis returned for the program point you are standing at. The simulation
\\<^const>\\<open>csim\\<close> is what names that point --- a partly executed command and
its frame stack sit at a graph node, and it is that node's table entry the store
belongs to.
"""


def corollary_text(rep, base):
    return f"""
\\<^const>\\<open>{rep}\\<close>'s own soundness corollaries: the check-report layer's
\\<^const>\\<open>declared_global\\<close> \\<open>p\\<close> convenience instances, matching
\\<open>{base}_sound_proved_for\\<close>/\\<open>_refuted_for\\<close> above.
"""


def headline_text(res, names):
    return f"""
The headline pair, at \\<^const>\\<open>declared_global\\<close> \\<open>p\\<close> and over
\\<^const>\\<open>{res}\\<close> --- the table the runtime API hands back. Two side
conditions survive, and both are decided per program rather than proved once: the
solver returned a partial post-solution for this program
(\\<^const>\\<open>{names['terminates']}\\<close>; no result here proves the solver
terminates on every input), and it solved enough keys
(\\<^const>\\<open>vars_cover\\<close>, decidable through \\<open>{names['cover']}\\<close>).
"""


def entry_header(dom, disciplines):
    """The orientation block: what the theory settles and what a reader needs."""
    one = len(disciplines) == 1
    return f"""
{dom.name}'s public soundness, in the vocabulary its runtime API returns: the
branch the unified dispatcher takes when the configured domain is {dom.name}.
Nothing is derived here. Each published solver discipline has its own instance of
the shared unit-context assembly, that instance already proves every statement
below over the assembly's own names, and one equation per discipline is all it
takes to say the same thing about the name a caller sees.

{"The" if one else "In each block the"} four coverage facts are stated once, as
context assumptions, rather than repeated on every theorem. They are requirements
on the solved key set, assumed here and not derived from termination: an edge or
call out of an unknown the solve visited must land on one it also visited. They
are weaker than the unconditional \\<^const>\\<open>vars_cover\\<close>, so each statement
below is exactly as applicable as an unconditional one would be. The
\\<open>vars_cover\\<close> readings, which a caller can discharge
\\<^theory_text>\\<open>by eval\\<close>, follow each discipline that publishes them.

No per-domain \\<^theory_text>\\<open>export_code\\<close> here: a caller reaches the
generic, already-sound report through the unified dispatcher \\<open>analyse\\<close>,
which is the one thing exported to OCaml. A second, domain-specific export
module would be a parallel, redundant API surface for the same computation.
"""


SIBLING_TEXT = """
The siblings \\<open>analyse_with_solver\\<close> compares against the production
default. Each reads its own instance's solved table, and each proves the same
statements by the same route --- the update rule is a parameter of
\\<^locale>\\<open>unit_dg_analysis\\<close>, so nothing below re-derives node soundness.
"""


def render_entry(dom, solvers):
    """A domain's runtime API and its production soundness, as one theory.

    Pure transport: every statement is the shared assembly's own theorem, read
    through the equation that renames the assembly's state reader to the name the
    published result table carries.
    """
    disciplines = [r for r in dom.routes if r in dom.entry_routes]
    out = [f"theory {dom.entry_theory}", "  imports"]
    out += [f"    {i}" for i in dom.entry_imports] + ["begin", ""]
    for c in dom.entry_hide:
        out += [f"hide_const {c}", ""]
    out += [f"section \\<open>{dom.name} codegen API: an arbitrary VIMP program,"
            " and its production soundness\\<close>", ""]
    out += text_block(GENERATED_NOTICE + "\n"
                      + fill(entry_header(dom, disciplines))) + [""]

    for i, route in enumerate(disciplines):
        names = dom.entry_routes[route]
        full = names.get("endpoints", "full") == "full"
        title = solvers[route]["title"]
        if i == 1:
            out += ["section \\<open>Solver-choice soundness: the sibling update"
                    " rules\\<close>", ""]
            out += text_block(fill(SIBLING_TEXT)) + [""]
        out += [f"subsection \\<open>{title}"
                f"{': the production default' if i == 0 else ''}\\<close>", ""]
        out += entry_state_at(dom, route, names) + [""]
        out += entry_discipline(dom, route, names)
        if full:
            out += entry_coverage(dom, route, names)
        out += entry_corollaries(dom, route, names, full)
    out.append("end")
    return "\n".join(out) + "\n"


# --- The published runtime names ---------------------------------------------

# What the production route publishes, and what a sibling discipline does. Both
# are defaults: a domain that publishes a different set says so, because the tree
# is not uniform and no rule predicts which way it differs.
CHECKS_FULL = ["eqs", "sol", "terminates", "terminates_via_solve_c", "vars_finite",
               "result_for", "result", "report_for", "report",
               "report_for_with_state", "report_with_state", "solved"]
CHECKS_SIBLING = ["sol", "result_for", "result", "report_for", "report"]


def defn_head(name, typ):
    """A definition header, on one line where the budget allows."""
    return either(f'definition {name} :: "{typ}" where',
                  [f"definition {name} ::", f'    "{typ}" where'])


def at_declared_global(name, hop):
    """The convenience instance: the same constant at the program's own globals."""
    return either(f'  "{name} p = {hop} (declared_global p) p"',
                  [f'  "{name} p =', f'     {hop} (declared_global p) p"'])


def checks_spellings(dom, route, names):
    """Every name one discipline publishes, resolved once.

    The equation system takes no discipline suffix: there is one system and
    every discipline solves it, which is what the assembly's `_equations_eq`
    lemmas make a theorem. Everything else carries the route's suffix, and the
    solved system may carry a different one from the published API: Interval
    leaves the solve's bare name to always-join while the published names it
    dispatches on read bare as production, so `solved_suffix` says which
    discipline each layer leaves unmarked. A route whose published names predate
    the convention overrides them by key under `names`, and each such override
    is a rename waiting to happen.
    """
    d, x = dom.name.lower(), names["ctx_prefix"]
    sfx = names.get("suffix", "")
    ssfx = names.get("solved_suffix", sfx)
    tag = sfx.lstrip("_") or SOLVER_BINDER_SUFFIX[route]
    spelled = {
        "eqs": f"{x}_eqs_prog",
        "sol": f"{x}_sol_prog{ssfx}",
        "terminates": f"{x}_terminates_prog{ssfx}",
        "terminates_via_solve_c": f"{x}_terminates_prog{ssfx}_via_solve_c",
        "vars_finite": f"{x}_vars_finite{ssfx}",
        "result_for": f"analyse_{d}_result{sfx}_for",
        "result": f"analyse_{d}_result{sfx}",
        "report_for": f"analyse_{d}_report{sfx}_for",
        "report": f"analyse_{d}_report{sfx}",
        "report_for_with_state": f"analyse_{d}_report{sfx}_for_with_state",
        "report_with_state": f"analyse_{d}_report{sfx}_with_state",
        "solved": f"analyse_{d}_ctx_solved{sfx}_for",
        "report_eq": f"{d}_report_{tag}_eq",
    }
    spelled.update(names.get("names", {}))
    return spelled


def checks_solved_system(dom, route, names, vt, first):
    """The abbreviations that give the assembly's solve the names the CLI uses,
    and the two side conditions a caller discharges against that solve."""
    p, b = dom.prefix(route), dom.binder(route)
    pub, nm, out = names["published"], checks_spellings(dom, route, names), []
    dg = (f"({vt} exec_dg_st lifted, {vt} exec_dg_st lifted) dg_state")
    if "eqs" in pub:
        out += [f"abbreviation {nm['eqs']} ::",
                '    "(vname \\<Rightarrow> bool) \\<Rightarrow> imp_prog',
                "       \\<Rightarrow> (pp \\<times> unit, (unit, unit) routed_gk,",
                f'            {dg}) eqsT" where',
                f'  "{nm["eqs"]} \\<equiv> {p}_equations"', ""]
    if "sol" in pub:
        out += [f"abbreviation {nm['sol']} ::",
                '    "(vname \\<Rightarrow> bool) \\<Rightarrow> imp_prog',
                "       \\<Rightarrow> (pp \\<times> unit) set",
                "            \\<times> (pp \\<times> unit + (unit, unit) routed_gk",
                f'                 \\<Rightarrow> {dg})" where',
                f'  "{nm["sol"]} \\<equiv> {p}_solution"', ""]
    if "terminates" in pub:
        out += either(
            f'abbreviation {nm["terminates"]} ::'
            ' "(vname \\<Rightarrow> bool) \\<Rightarrow> imp_prog \\<Rightarrow> bool" where',
            [f"abbreviation {nm['terminates']} ::",
             '    "(vname \\<Rightarrow> bool) \\<Rightarrow> imp_prog'
             ' \\<Rightarrow> bool" where'])
        out += [f'  "{nm["terminates"]} \\<equiv> {p}_terminates"', ""]
    lemmas = []
    if "terminates_via_solve_c" in pub:
        lemmas += either(f"lemmas {nm['terminates_via_solve_c']} ="
                         f" {b}.terminates_of_solve_c",
                         [f"lemmas {nm['terminates_via_solve_c']} =",
                          f"  {b}.terminates_of_solve_c"])
    if "vars_finite" in pub:
        lemmas += either(f"lemmas {nm['vars_finite']} ="
                         f" {b}.vars_finite_of_terminates",
                         [f"lemmas {nm['vars_finite']} =",
                          f"  {b}.vars_finite_of_terminates"])
    if lemmas:
        if first:
            out += text_block(fill(side_condition_text(nm["terminates"]))) + [""]
        out += lemmas + [""]
    return out


def checks_tables(dom, route, names, vt):
    """The result table, the check report and the state-carrying sibling."""
    b, p = dom.binder(route), dom.prefix(route)
    pub, nm = names["published"], checks_spellings(dom, route, names)
    res = f"(unit, {vt} abs_state) analysis_result"
    rep = "check_report_entry list"
    st = (f"(pp \\<times> exp \\<times> check_result \\<times> bool"
          f" \\<times> {vt} abs_state) list")
    out = []
    # The state-carrying names put the discipline suffix before `_with_state`,
    # which is where the tree already puts it, so a kind names both spellings
    # rather than the renderer deriving one from the other.
    for kind, for_key, const, typ, text in [
            ("result", "result_for", "result", res, None),
            ("report", "report_for", "report", rep, REPORT_TEXT),
            ("report_with_state", "report_for_with_state",
             "report_with_state", st, WITH_STATE_TEXT)]:
        if for_key not in pub and kind not in pub:
            continue
        base, for_name = nm[kind], nm[for_key]
        if text and for_key in pub:
            out += text_block(fill(text(dom, nm["result_for"]))) + [""]
        if for_key in pub:
            out += defn_head(for_name, "(vname \\<Rightarrow> bool)"
                             f" \\<Rightarrow> imp_prog \\<Rightarrow> {typ}")
            out += [f'  "{for_name} = {p}_{const}"', ""]
            if kind == "result":
                out += text_block(fill(CONVENIENCE_TEXT)) + [""]
        if kind in pub:
            out += defn_head(base, f"imp_prog \\<Rightarrow> {typ}")
            out += at_declared_global(
                base, for_name if for_key in pub
                else f"{p}_{const}") + [""]
    if "solved" in pub:
        out += text_block(fill(SOLVED_TEXT)) + [""]
        name = nm["solved"]
        out += [f"definition {name} ::",
                "    \"(vname \\<Rightarrow> bool) \\<Rightarrow> imp_prog",
                f"     \\<Rightarrow> (unit, {vt} abs_state) analysis_result",
                f"          \\<times> (String.literal \\<times> {vt} abs_state lifted)"
                ' list" where',
                f'  "{name} = {p}_solved"', "",
                f"lemma fst_{name} [simp]:",
                f'  "fst ({name} gs p) = {nm["result_for"]} gs p"',
                f"  by (simp add: {name}_def {nm['result_for']}_def",
                f"      {b}.solved_eq)", ""]
    return out


def checks_surface(dom, routes, solvers):
    """One \\<^locale>\\<open>analysis_surface\\<close> interpretation per discipline, and
    the equation that reads each published report back through it."""
    d, cls = dom.name.lower(), dom.facts()["classifier"]
    out = ["subsection \\<open>The published surface, one interpretation per"
           " discipline\\<close>", ""]
    out += text_block(fill(surface_text(dom, len(routes)))) + [""]
    for route, names in routes:
        out += [f"interpretation {names['surface']}: analysis_surface",
                f"  {checks_spellings(dom, route, names)['result']} bot {cls}",
                "  by unfold_locales", ""]
    for route, names in routes:
        b, nm = dom.binder(route), checks_spellings(dom, route, names)
        rep, res, eq = nm["report"], nm["result"], nm["report_eq"]
        simps = [f"{rep}_def"]
        if "report_for" in names["published"]:
            simps.append(f"{nm['report_for']}_def")
        simps += [f"{res}_def", f"{nm['result_for']}_def", f"{b}.report_def",
                  "surface_unfold"]
        out += either(f'lemma {eq}: "{rep} p'
                      f' = {names["surface"]}.report p"',
                      [f"lemma {eq}:",
                       f'  "{rep} p = {names["surface"]}.report p"'])
        line = "  by (simp add:"
        for s in simps:
            if symbol_len(f"{line} {s}") > ENTRY_WIDTH:
                out.append(line)
                line = "     "
            line = f"{line} {s}"
        out += [line + ")", ""]
    return out


CONVENIENCE_TEXT = """
Convenience instance at \\<^const>\\<open>declared_global\\<close> \\<open>p\\<close>, the
classifier every caller with only an \\<^typ>\\<open>imp_prog\\<close> in hand recomputes
anyway.
"""

NOTATION_TEXT = """
These are notation, not a layer: an \\<^theory_text>\\<open>abbreviation\\<close>
introduces no constant, so nothing has to be unfolded to get back to the assembly
and nothing extra reaches the code generator.
"""

SOLVED_TEXT = """
Both halves of one solve: the locals table every check report already reads, and
the globals beside it. Binding the solve once is what keeps a report that shows
both from solving twice.
"""


def REPORT_TEXT(dom, result_for):
    return f"""
The report the exported \\<open>analyse\\<close> API dispatches to. It reads its per-node
state through \\<^const>\\<open>{result_for}\\<close>'s
\\<^type>\\<open>analysis_result\\<close> table --- \\<^const>\\<open>lookup_context\\<close>, not
a raw solver-environment lookup --- so a \\<^const>\\<open>Lifted\\<close> point classifies
at its projected state and a \\<^const>\\<open>Bot\\<close> one (dead, or never covered;
the two are not distinguishable here) classifies at \\<^const>\\<open>bot\\<close>. That
preserves \\<^type>\\<open>check_result\\<close>'s three-way verdict rather than
introducing a fourth, \\<open>Dead\\<close> outcome the type does not carry.
"""


def WITH_STATE_TEXT(dom, result_for):
    return f"""
The state-carrying sibling: same table, with the per-check {dom.name} environment
attached to each entry instead of discarded, and an \\<open>unreachable\\<close> flag
read straight off \\<^const>\\<open>lookup_context\\<close>'s
\\<^const>\\<open>Bot\\<close>/\\<^const>\\<open>Lifted\\<close> case split. The flag is
\\<^term>\\<open>True\\<close> exactly when that unknown is \\<^const>\\<open>Bot\\<close>; what
\\<^const>\\<open>Bot\\<close> certifies about concrete reachability is the surrounding
soundness statement's business, not this definition's.
"""


def side_condition_text(terminates):
    return f"""
The one side condition a caller discharges per program. It is not a decision
procedure: \\<^const>\\<open>{terminates}\\<close> follows when the solver's own
executable entry point returns a result on this program's equations, and nothing
here says that entry point returns on every input.
"""


def sibling_text(dom, eq_lemma, rule, production):
    return f"""
The same equation system solved under the {rule} update rule instead of the
{production} rule production uses, so \\<open>analyse_with_solver\\<close> can compare
solver choices on one system (\\<open>{eq_lemma}\\<close> is what makes "one system" a
theorem rather than a claim). These are bindings onto the assembly's own
instance for this rule, so the sibling carries the same soundness endpoints the
default does --- the update rule is a parameter of the assembly, not a reason to
leave it.
"""


def surface_text(dom, n):
    return f"""
{dom.name}'s {n} disciplines through the shared
\\<^locale>\\<open>analysis_surface\\<close>. There is one interpretation for each
discipline {dom.name} publishes and none for any it does not, so the absent
interpretation and the absent solver route agree by construction rather than by a
separately maintained legality table. Why {dom.name} publishes these disciplines
and not others is recorded in its README, not here.
"""


def checks_header(dom, n):
    return f"""
{dom.name}'s public runtime API: the names a caller outside this session uses,
each bound to one of the shared unit-context assembly's {n} instances. Those
instances define the equation system, the solve, the result table and the
classified report; nothing is computed at this point, and nothing is rebuilt
here.

A context-sensitive run pairs the same classifier with a different solved system
and reaches none of the names below, so no routing policy is needed here.
"""


def render_checks(dom, solvers):
    """A domain's published runtime names, as one generated theory.

    Every name is a binding onto one of the assembly's instances: the equation
    system, the solve and the classified report are already built there, and
    nothing is recomputed at this point.
    """
    routes = [(r, dom.checks_routes[r]) for r in dom.routes
              if r in dom.checks_routes]
    vt, d, x = dom.value_type, dom.name.lower(), dom.checks_prefix
    out = [f"theory {dom.checks_theory}", "  imports"]
    out += [f"    {i}" for i in dom.checks_imports] + ["begin", ""]
    for c in dom.checks_hide:
        out += [f"hide_const {c}", ""]
    out += [f"section \\<open>What a whole-program {dom.name} run reports\\<close>", ""]
    out += text_block(GENERATED_NOTICE + "\n"
                      + fill(checks_header(dom, len(routes)))) + [""]

    routes = [(r, dom.checks_names(r)) for r, _ in routes]
    for i, (route, names) in enumerate(routes):
        if i == 0:
            out += ["subsection \\<open>The solved system, under the name the CLI"
                    " already uses\\<close>", ""]
            out += text_block(fill(NOTATION_TEXT)) + [""]
            out += checks_solved_system(dom, route, names, vt, True)
            out += ["subsection \\<open>Solved-result table and check"
                    " report\\<close>", ""]
        else:
            rule = solvers[route]["rule"]
            out += [f"subsection \\<open>Solver-choice variant: the {rule} update"
                    " rule\\<close>", ""]
            out += text_block(fill(sibling_text(
                dom, f"{dom.prefix(route)}_equations_eq", rule,
                solvers[dom.routes[0]]["rule"]))) + [""]
            out += checks_solved_system(dom, route, names, vt, False)
        out += checks_tables(dom, route, names, vt)

    out += checks_surface(dom, routes, solvers)
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

A call-string cell carries the shortest bound its domain publishes, and the
resolver rejects anything below it: every domain sets that to 1 today, so
\\<open>k = 0\\<close> answers \\<^const>\\<open>None\\<close>. That is a usability decision
rather than a soundness one. \\<open>cs_route\\<close> at \\<open>k = 0\\<close> routes every
activation to the context \\<^term>\\<open>[]\\<close>, as well-defined and as finite as
any other bound, and it is not \\<^const>\\<open>Ctx_None\\<close> in disguise: the
equation system stays call-string keyed, and the published result carries
call-string contexts, all of them empty. Lowering the bound is a real
behaviour change, not a relaxation of a check.
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

        for route, spec in d.entry_routes.items():
            if route not in d.routes:
                problems.append(f"{d.name}: entry endpoints for the unpublished"
                                f" route {route}")
            kind = spec.get("endpoints", "full")
            required = {"terminates", "sol", "result_for", "report_for",
                        "report", "closure"}
            if kind == "full":
                required |= {"result", "cover"}
            elif kind != "reports":
                problems.append(f"{d.name}/{route}: endpoints is `full` or"
                                " `reports`")
            missing = required - set(spec)
            if missing:
                problems.append(f"{d.name}/{route}: the entry block does not name "
                                + ", ".join(sorted(missing)))

        if d.checks_routes and not d.checks_prefix:
            problems.append(f"{d.name}: a checks block names the abbreviation"
                            " prefix its solved system is published under")
        for route, spec in d.checks_routes.items():
            if route not in d.routes:
                problems.append(f"{d.name}: published names for the unpublished"
                                f" route {route}")
            if "surface" not in spec:
                problems.append(f"{d.name}/{route}: the checks block does not name"
                                " the surface interpretation binder")
            if route != d.default and "suffix" not in spec:
                problems.append(f"{d.name}/{route}: a discipline other than the"
                                " production one names the suffix its published"
                                " constants carry")

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

    rendered = []
    for d in doms:
        if d.has_assembly:
            rendered.append((d.path, render_assembly(d, solvers), d.adopted))
        if d.registrations:
            rendered.append((d.ctx_path, render_contextual(d, solvers),
                             d.ctx_adopted))
        if d.checks_routes:
            rendered.append((d.checks_path, render_checks(d, solvers),
                             d.checks_adopted))
        if d.entry_routes:
            rendered.append((d.entry_path, render_entry(d, solvers),
                             d.entry_adopted))
    targets = [(path, text) for path, text, adopted in rendered if adopted]
    unadopted = [(path, text) for path, text, adopted in rendered if not adopted]
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
