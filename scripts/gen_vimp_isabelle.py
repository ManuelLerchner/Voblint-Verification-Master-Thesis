#!/usr/bin/env python3
"""M6: generates src/VIMP/VIMP_Grammar_Generated.thy -- nonterminals,
`syntax` (Isabelle mixfix declarations), and the `Vimp_Grammar_Tr` ML
structure (parse_translation's AST-lowering, exposed for VIMP_Notation.thy
to call into) -- from the canonical grammar/vimp.yaml.

Generated theory has no notion of `imp_prog`: whole-program assembly
(`program { ... }`, main-selection, `imp_prog` construction) is
VIMP_Notation.thy's own hand-written territory, matching
`special: program_structure`'s scope in grammar/vimp.yaml and
gen_vimp_menhir.py's own hand-written gen_program_rule. VIMP_Notation.thy
imports this theory and calls `Vimp_Grammar_Tr.stmts_opt_tr`/`exp_tr`/
`formals_of`/etc. directly.

Two lowering rules stay hand-written inside `Vimp_Grammar_Tr` (as fixed
text this module emits, not derived from grammar/vimp.yaml's structured
metadata): Isabelle's binary Num literal decoding (`dest_num`/
`read_num_const`, no Menhir analogue, since Isabelle's own numeral literals
compile to a binary One/Bit0/Bit1 encoding, not a plain digit string) and
the compositional unary-minus rule. `_exp_zero`/`_exp_one` and
`_stmt_call0`/`_stmt_callret0` (gen_isabelle_extra_syntax/_actions) are
Isabelle-target realizations of a canonical rule Isabelle's own mixfix
grammar can't express directly -- see those functions' comments.

Nonterminal naming mirrors VIMP_Notation.thy's own pre-cutover `imp2_*`
convention. IDENT/INT aren't generated terminals here: Isabelle's outer
lexer already provides `id`/`num_const` as built-in nonterminals, so
grammar/vimp.yaml's `terminals:` section (which describes lexical
*patterns* for target lexers that need them, i.e. Menhir/ocamllex) has no
Isabelle-side equivalent to generate -- another instance of the schema's
"target-specific lexical mechanics stay out of the neutral grammar"
principle.

Requires PyYAML to regenerate; not to build (the .thy file is committed,
same convention codegen/generated/ already uses).
Usage: python3 scripts/gen_vimp_isabelle.py [grammar/vimp.yaml] [out_dir]
"""

import sys
from pathlib import Path

import yaml

REPO_ROOT = Path(__file__).resolve().parent.parent
DEFAULT_GRAMMAR = REPO_ROOT / "grammar" / "vimp.yaml"
DEFAULT_OUT = REPO_ROOT / "src" / "VIMP"

# Isabelle mixfix escaping: '(' ')' '_' need a leading "'" so the mixfix
# parser doesn't read them as argument-slot/grouping syntax.
MIXFIX_ESCAPE = {"(": "'(", ")": "')", "_": "'_"}

# result nonterminal -> imp2_* name. `program`/`globals`/`function` aren't
# here: they're handled by the hand-written top-level wrapper (see
# gen_program_syntax), the same way gen_vimp_menhir.py hand-writes
# gen_program_rule rather than forcing "main" selection through the
# generic per-production template.
NONTERMINAL = {
    "exp": "imp2_exp",
    "stmt": "imp2_stmt",
    "stmts": "imp2_stmts",
    "stmts_opt": "imp2_stmts_opt",
    "actuals": "imp2_actuals",
    "ty": "imp2_ty",
    "formal": "imp2_formal",
    "formals": "imp2_formals",
    "ids": "imp2_ids",
}

# IDENT/INT map to Isabelle's own built-in nonterminals, not a generated
# terminal (see module docstring).
BUILTIN_TERMINAL = {"INT": "num_const"}


def ident_role(rhs: list, i: int) -> str:
    """'callee' for an IDENT immediately followed by LPAREN (a call's
    callee name -- VIMP has no other IDENT-typed procedure-name occurrence
    in a generated production; function_decl's own name lives in
    VIMP_Notation.thy's hand-written territory), 'variable' for every other
    IDENT occurrence (an expression use, an assignment/random/callret
    target, or a formals/ids declaration list item). Same signal
    stmt_id_arg_priority already uses for a different purpose (argument
    priority); kept as one shared classifier so the two can't drift apart.
    Every IDENT position gets `id_position` regardless of role (see
    isabelle_type) -- this classifier now decides only which markup
    category, if any, dest_id_position reports at that position (see
    IDENT_MARKUP), not which Isabelle nonterminal it parses as. Keeping
    position-carrying provenance uniform across both roles means a later
    phase can start reporting procedure/entity markup for callee
    occurrences without another grammar migration -- provenance and
    markup classification are separate concerns; only the latter is
    role-dependent."""
    followed_by = rhs[i + 1] if i + 1 < len(rhs) else None
    return "callee" if followed_by == "LPAREN" else "variable"


# PRESENTATION POLICY, not a semantic classification: ident_role -> the
# Markup.T option expression dest_id_position reports at that position.
# Markup.free/Markup.bound/Markup.skolem are real Isabelle markup
# categories with their own established meaning in Isabelle's own term
# presentation (a genuine free variable, a quantifier-bound variable, a
# Skolem constant); VIMP repurposes them here purely for their distinct,
# already-styled colors in jEdit/browser_info, not because a VIMP
# procedure name IS a Skolem constant or a declared global IS a bound
# variable. Treat this table as freely swappable -- e.g. for real
# procedure entity definition/reference markup once a name registry
# exists -- not as a claim about what these categories mean.
#
# 'variable' occurrences report Markup.free.
# 'callee' occurrences report Markup.skolem -- a stopgap, not a considered
# semantic classification: a bare Markup.entity report (tried first) turned
# out to render as plain text, since jEdit/browser_info only style the
# entity_def/entity_ref markup that Name_Space.markup's serial-linked
# registration produces, not a bare kind+name tag. Markup.skolem is the
# same kind of simple, registry-free constant as Markup.free, just with its
# own distinct color, chosen only to make callee occurrences visibly
# different from variable occurrences until a real procedure-name registry
# funds proper entity definition/reference markup (navigation, not just
# color) -- both roles already parse via id_position, so that upgrade needs
# no further grammar change, only a different report here.
#
# 'global' is a fourth, narrower category: the `ids` list production
# (globals_decl's `global x, y;`) is a variable-declaration list just like
# `formals`, but reported separately (Markup.bound, also a stopgap color
# choice) so a declared-global name reads differently from an ordinary
# local/formal occurrence at its declaration site. This does NOT extend to
# every later USE of that name (`x := x + 1` still reports Markup.free
# regardless of whether `x` was declared global) -- that would need each
# variable occurrence resolved against the program's declared-global list,
# i.e. actual name resolution across productions, not a per-production
# markup choice; out of scope here, matching the same boundary that keeps
# procedure def/ref out of scope above.
IDENT_MARKUP = {"variable": "SOME Markup.free", "callee": "SOME Markup.skolem", "global": "SOME Markup.bound"}


def isabelle_type(sym: str) -> str:
    if sym == "IDENT":
        return "id_position"
    if sym in BUILTIN_TERMINAL:
        return BUILTIN_TERMINAL[sym]
    if sym in NONTERMINAL:
        return NONTERMINAL[sym]
    raise ValueError(f"no Isabelle nonterminal/terminal mapping for {sym!r}")


def is_arg_symbol(sym: str) -> bool:
    return sym == "IDENT" or sym in BUILTIN_TERMINAL or sym in NONTERMINAL


def literal_text(g: dict, token: str) -> str:
    for table in (g["keywords"], g["punctuation"]):
        for word, tok in table.items():
            if tok == token:
                return word
    raise ValueError(f"no literal text for token {token!r}")


def mixfix_template(g: dict, rhs: list) -> str:
    parts = []
    for sym in rhs:
        if is_arg_symbol(sym):
            parts.append("_")
        else:
            text = literal_text(g, sym)
            parts.append("".join(MIXFIX_ESCAPE.get(c, c) for c in text))
    return " ".join(parts)


# Production name -> exact mixfix template, overriding mixfix_template's
# generic uniform-space rendering. Confirmed empirically necessary, not a
# stylistic preference: the generic renderer's leading space before an
# escaped LPAREN (e.g. stmt_random's "random '( ')") made `x := random()`
# genuinely ambiguous against stmt_callret0's `_ := _()` shape -- Isabelle
# reported "Inner syntax error" (failed to disambiguate); the same input
# parsed cleanly, failing only downstream at the expected harness-only
# translation step, once that leading space was removed. call/callret
# share the same "id immediately followed by a call's parens" shape and so
# the same risk (their sibling call0/callret0 forms are exactly the
# competing alternative), hence covered here too.
#
# The fix is NOT "no space before any LPAREN" generically: that was tried
# and broke stmt_if/stmt_while/stmt_check, which don't have a competing
# production at all -- confirming this is specifically about resolving a
# real ambiguity between sibling productions, not a general spacing rule.
# Isabelle's own exact disambiguation mechanism here isn't something this
# generator needs to model in general; matching the hand-written original's
# proven-working spacing for exactly the productions that need it is
# sufficient and lower-risk than a broader heuristic.
TEMPLATE_OVERRIDE = {
    "stmt_random": "_ := random'(')",
    "stmt_call": "_'( _ ')",
    "stmt_callret": "_ := _'( _ ')",
}


def arg_types(g: dict, rhs: list) -> list:
    return [
        isabelle_type(sym)
        for i, sym in enumerate(rhs)
        if is_arg_symbol(sym)
    ]


# -- Priority assignment -----------------------------------------------
# grammar/vimp.yaml's precedence table is qualitative (ordered low->high,
# with an associativity per level); Isabelle mixfix needs real numbers.
# Levels are spaced 10 apart starting at 30 (leaving headroom below for
# any future lower-precedence addition, and matching the rough magnitude
# VIMP_Notation.thy's original numbers already used). Left-assoc: left arg
# = level, right arg = level+1, result = level. Right-assoc: mirrored.
# None (non-associative, e.g. LT/EQEQ): both args one level tighter than
# the level below (matches how comparisons sit strictly above +/- in the
# original grammar, non-chainable).

def build_precedence_table(g: dict) -> dict:
    table = {}
    for i, level in enumerate(g["precedence"]):
        base = 30 + i * 10
        table[level["assoc"], tuple(level["tokens"])] = base
    return table


def precedence_of(g: dict, token: str):
    for level in g["precedence"]:
        if token in level["tokens"]:
            base = 30 + g["precedence"].index(level) * 10
            return level["assoc"], base
    return None


# -- Syntax line rendering ------------------------------------------------

ATOM_PRIORITY = 1000  # exp productions with no listed operator: unconditionally embeddable

# `stmt` has no precedence-climbing structure at all -- every stmt
# production sits at one flat level (matching VIMP_Notation.thy's own
# convention: every `_imp2_*` stmt production ends in "... 61"), since
# statements combine only via ';' (stmts' own _one/_seq priority, a
# separate nonterminal), never as each other's operands. An exp/actuals
# argument gets 0 (accepts any expression of that type unconditionally --
# correct here since parens/self-priority already make every exp
# producible at any argument priority).
#
# An `id` argument is NOT uniformly ATOM_PRIORITY: a bare 1000 for every
# id slot was tried and is genuinely wrong, not just non-matching style --
# confirmed empirically (Isabelle reported "Inner syntax error" on
# `x := random()`, ambiguous against stmt_callret0's `_ := _()` shape,
# where both the assignment target and a bare-identifier callee sit at the
# same priority). The original hand-written grammar instead uses two
# distinct priorities for two distinct id ROLES: an id immediately
# followed by ASSIGN is the statement's assignment TARGET (900); an id
# immediately followed by LPAREN is a CALL's callee name (1000, i.e.
# ATOM_PRIORITY). Both are mechanically derivable from what token follows
# the id in `rhs` -- not an arbitrary two-number special case.
STMT_LEVEL = 61
STMT_TARGET_ID_PRIORITY = 900
STMT_CALLEE_ID_PRIORITY = ATOM_PRIORITY


def stmt_id_arg_priority(rhs: list, i: int) -> int:
    return STMT_CALLEE_ID_PRIORITY if ident_role(rhs, i) == "callee" else STMT_TARGET_ID_PRIORITY


def render_syntax_line(g: dict, prod: dict) -> str:
    name = "_" + prod["name"]
    result_nt = prod["result"]
    result = NONTERMINAL[result_nt]
    rhs = prod["rhs"]
    args = arg_types(g, rhs)
    template = TEMPLATE_OVERRIDE.get(prod["name"]) or mixfix_template(g, rhs)
    arg_positions = [i for i, s in enumerate(rhs) if is_arg_symbol(s)]

    # A production's own `precedence:` field (e.g. exp_uminus's UMINUS)
    # overrides scanning its rhs tokens against the table -- required
    # whenever an rhs token is itself ambiguous between levels (MINUS
    # appears in both the binary PLUS/MINUS level and, via exp_uminus's
    # override, the unary NOT/UMINUS level; scanning rhs tokens alone
    # would silently pick the binary level for the unary production too).
    # Confirmed by an actual failed load test, not just by inspection: a
    # first version without this override produced valid-looking syntax
    # declarations (no load-time error) but the resulting priority made
    # every `value` command using unary minus fail to parse.
    override = prod.get("precedence")
    prec_tokens = [override] if override else [s for s in rhs if precedence_of(g, s) is not None]
    if len(prec_tokens) == 1:
        assoc, level = precedence_of(g, prec_tokens[0])
        if len(arg_positions) == 2 and rhs[arg_positions[0]] == result_nt == rhs[arg_positions[1]]:
            left, right = (level, level + 1) if assoc == "left" else (level + 1, level)
            prio = f" [{left}, {right}] {level}"
        elif len(arg_positions) == 1:
            prio = f" [{level}] {level}"
        else:
            prio = f" {level}"
    elif result_nt == "exp":
        # A recursive self-typed argument (the inner exp in a paren
        # production) needs an explicit, unconstrained [0] so it can hold
        # anything; a foreign-typed argument (exp_var's `id`) needs no
        # bracket at all -- it's outside this priority chain entirely.
        recursive_args = [i for i in arg_positions if rhs[i] == result_nt]
        if recursive_args:
            prio = f" [{', '.join('0' for _ in recursive_args)}] {ATOM_PRIORITY}"
        else:
            prio = f" {ATOM_PRIORITY}"
    elif result_nt == "stmt":
        arg_priorities = [stmt_id_arg_priority(rhs, i) if rhs[i] == "IDENT" else 0 for i in arg_positions]
        prio = f" [{', '.join(map(str, arg_priorities))}] {STMT_LEVEL}" if arg_priorities else f" {STMT_LEVEL}"
    else:
        prio = ""

    type_sig = " => ".join(args + [result]) if args else result
    quoted_type = f'"{type_sig}"' if " => " in type_sig else type_sig
    return f'  "{name}" :: {quoted_type} ("{template}"{prio})'


def gen_nonterminals(g: dict) -> str:
    return "\n".join(f"nonterminal {nt}" for nt in NONTERMINAL.values())


def gen_list_syntax(prod: dict) -> list:
    """Isabelle mixfix has no native "zero-or-more, separated" construct, so
    every `list_of`/`optional_list_of` production needs a hand-derived pair
    of productions -- but NOT the same shape for all of them. Two genuinely
    different fold directions exist in the hand-written original, matching
    the same `constructor:` presence/absence gen_vimp_menhir.py's
    gen_list_rule already branches on:

    - `constructor:` present (stmts): left-fold accumulator, `_one`/`_seq`,
      accumulator-first (`imp2_stmts => imp2_stmt => imp2_stmts`) -- matches
      how Seq naturally left-associates a sequence.
    - `constructor:` absent (actuals/formals/ids): right-recursive cons,
      `_one`/`_cons`, item-first (`imp2_exp => imp2_actuals => imp2_actuals`)
      -- matches how the hand-written actuals_tr/formals_of/names_of already
      pattern-match (item, then the rest of the list).

    An earlier version of this function used the `_seq` (left-fold) shape
    unconditionally for both cases; that's syntactically valid Isabelle (a
    bare `syntax` declaration doesn't care about fold direction) but wrong
    once parse_translation has to pattern-match a specific argument order --
    caught by cross-checking against VIMP_Notation.thy's actual
    `_imp2_actuals_cons` shape, not by the earlier load test (which only
    proved the syntax block parses, not that it matches the existing
    argument order)."""
    result = NONTERMINAL[prod["result"]]
    # Every current IDENT-item list (formals, ids) is a variable-declaration
    # list, so the IDENT fallback is id_position, not plain id -- same
    # variable-role treatment as any other declaration/use occurrence.
    item = NONTERMINAL.get(prod.get("list_of") or prod.get("optional_list_of"), "id_position")
    sep = {"SEMI": ";", "COMMA": ","}[prod.get("separator", "COMMA")]
    if "optional_list_of" in prod:
        base = NONTERMINAL[prod["result"].removesuffix("_opt")]
        return [
            f'  "_{prod["name"]}_none" :: {result} ("")',
            f'  "_{prod["name"]}_some" :: "{base} => {result}" ("_")',
        ]
    if "constructor" in prod:
        return [
            f'  "_{prod["name"]}_one" :: "{item} => {result}" ("_" 61)',
            f'  "_{prod["name"]}_seq" :: "{result} => {item} => {result}" ("_{sep} _" [61, 61] 61)',
        ]
    return [
        f'  "_{prod["name"]}_one" :: "{item} => {result}" ("_")',
        f'  "_{prod["name"]}_cons" :: "{item} => {result} => {result}" ("_{sep} _")',
    ]


# Whole-program assembly (`program { ... }`, main-selection, `imp_prog`
# construction) is NOT generated here: it's VIMP_Notation.thy's own
# hand-written territory (matching `special: program_structure`'s scope and
# gen_vimp_menhir.py's own hand-written gen_program_rule), and that theory
# owns the imp2_funcs nonterminal and its productions directly. This
# generated theory has no notion of imp_prog at all.

# -- Isabelle-target realizations of a canonical rule Isabelle's own mixfix
# grammar can't express directly. Neither belongs in grammar/vimp.yaml:
# the canonical INT terminal already covers 0/1 uniformly (Menhir's actual
# int parsing doesn't care), and `actuals`'s `min: 0` already covers a
# zero-arg call for Menhir (its growing-list rule derives the empty case
# directly). Isabelle needs an explicit escape hatch for each instead --
# `num_const` has no derivation for the literal 0 or 1 (Num.num's
# One/Bit0/Bit1 encoding has no zero, and 1 is the unwrapped base case),
# and mixfix lists have no empty derivation at all (confirmed empirically:
# an isolation load test with only the generic actuals/formals productions
# failed to parse `f()` -- ambiguity gen_vimp_menhir.py's own comment on
# stmt_call/stmt_callret already anticipated from the Menhir side, just
# manifesting as a parse failure here instead of a shift/reduce conflict).
# Generated here, in the SAME `K "..." $ ...` action shape as every other
# clause, rather than hand-maintained prose in a .thy file -- but they are
# still genuinely Isabelle-target realizations of a canonical rule, not a
# duplicate/extension of the language itself.

def gen_isabelle_extra_syntax() -> list:
    return [
        '  "_exp_zero" :: imp2_exp ("0" 1000)',
        '  "_exp_one" :: imp2_exp ("1" 1000)',
        # Both ids are id_position now (see isabelle_type/ident_role):
        # first is the zero-arg callret's return TARGET (variable role),
        # second the callee (callee role) -- both carry position, only
        # dest_id_position's markup argument differs per role.
        "  \"_stmt_call0\" :: \"id_position => imp2_stmt\" (\"_'(')\" [1000] 61)",
        "  \"_stmt_callret0\" :: \"id_position => id_position => imp2_stmt\" (\"_ := _'(')\" [900, 1000] 61)",
    ]


def gen_isabelle_extra_actions() -> dict:
    return {
        "exp": [
            '(Const ("_exp_zero", _), []) => K c_N $ HOLogic.mk_number HOLogic.intT 0',
            '(Const ("_exp_one", _), []) => K c_N $ HOLogic.mk_number HOLogic.intT 1',
        ],
        "stmt": [
            f'(Const ("_stmt_call0", _), [x0]) => K c_Call $ (K c_None) $ (HOLogic.mk_literal (dest_id_position ({IDENT_MARKUP["callee"]}) ctxt x0)) $ K c_Nil',
            f'(Const ("_stmt_callret0", _), [x0, x2]) => K c_Call $ ((K c_Some $ (HOLogic.mk_literal (dest_id_position ({IDENT_MARKUP["variable"]}) ctxt x0)))) $ (HOLogic.mk_literal (dest_id_position ({IDENT_MARKUP["callee"]}) ctxt x2)) $ K c_Nil',
        ],
    }


def gen_syntax_block(g: dict) -> str:
    # `special:` productions (exp_num, exp_uminus) still need a mixfix
    # syntax line -- the mixfix TEMPLATE is fully mechanical from rhs/
    # precedence metadata; only the ACTION (parse_translation) is hand-
    # written for these. An earlier version filtered them out here too,
    # matching the parse_translation-side skip -- wrong: without
    # `_exp_num`/`_exp_uminus` declared, no numeral or unary-minus
    # expression parses at all, which a real load test caught (every
    # `value` command touching a numeral failed with "Inner syntax
    # error"). `program_structure`'s production (`program`) doesn't need
    # this fix: its result ("program") was never in NONTERMINAL to begin
    # with, so it's excluded by the membership check below regardless.
    lines = ['syntax']
    for prod in g["productions"]:
        if prod.get("list_of") or prod.get("optional_list_of"):
            continue
        if prod["result"] not in NONTERMINAL:
            continue
        lines.append(render_syntax_line(g, prod))
    for prod in g["productions"]:
        if prod.get("list_of") or prod.get("optional_list_of"):
            lines.extend(gen_list_syntax(prod))
    lines.extend(gen_isabelle_extra_syntax())
    return "\n".join(lines)


# -- parse_translation generation (feasibility prototype) -----------------
#
# Scope: the generic `lower:`/`passthrough:` shape, plus list productions'
# fold (Seq-accumulator or Cons-list, matching gen_list_syntax above). Kept
# OUT, matching grammar/vimp.yaml's own `special:` boundary: integer_literal
# (Isabelle's binary Num decoding, dest_num/read_num_const -- no Menhir
# analogue), unary_minus (same cancellation-vs-compositional judgment call
# gen_vimp_menhir.py's SPECIAL_ACTIONS already makes), program_structure
# (main-partitioning, imp_prog construction). Those three stay hand-written
# helpers that a generated action calls into, not generated themselves.

# lower.ctor name -> qualified Isabelle constant, mirroring the `val c_X =
# "..."` table already hand-written in VIMP_Notation.thy's parse_translation.
# Genuinely project-specific (which theory/type each constructor lives in),
# not derivable from grammar/vimp.yaml -- same status as
# gen_vimp_menhir.py's `Voblint_CLI.Core.` qualification prefix.
TR_CONST = {
    "N": "VIMP_Syntax.N",
    "V": "VIMP_Syntax.V",
    "Plus": "VIMP_Syntax.exp.Plus",
    "Minus": "VIMP_Syntax.exp.Minus",
    "Times": "VIMP_Syntax.exp.Times",
    "Less": "VIMP_Syntax.exp.Less",
    "Eq": "VIMP_Syntax.exp.Eq",
    "Not": "VIMP_Syntax.exp.Not",
    "And": "VIMP_Syntax.exp.And",
    "Or": "VIMP_Syntax.exp.Or",
    "SKIP": "VIMP_Proc.com.SKIP",
    "Seq": "VIMP_Proc.com.Seq",
    "Assign": "VIMP_Proc.com.Assign",
    "Return": "VIMP_Proc.com.Return",
    "Check": "VIMP_Proc.com.Check",
    "If": "VIMP_Proc.com.If",
    "While": "VIMP_Proc.com.While",
    "Call": "VIMP_Proc.com.Call",
    "I8": "VIMP_Ikind.ikind.I8",
    "U8": "VIMP_Ikind.ikind.U8",
    "I16": "VIMP_Ikind.ikind.I16",
    "U16": "VIMP_Ikind.ikind.U16",
    "I32": "VIMP_Ikind.ikind.I32",
    "U32": "VIMP_Ikind.ikind.U32",
    "I64": "VIMP_Ikind.ikind.I64",
    "U64": "VIMP_Ikind.ikind.U64",
}

# lower.ctor name -> the `c_X` val bound to that same qualified constant in
# VAL_DECLS (see gen_grammar_tr_structure) -- referencing the val instead of
# re-quoting the literal string keeps every occurrence of a given
# constructor spelled identically, one string constant per constructor.
CTOR_VAL = {
    "N": "c_N", "V": "c_V", "Plus": "c_Plus", "Minus": "c_Minus", "Times": "c_Times",
    "Less": "c_Less", "Eq": "c_Eq", "Not": "c_Not",
    "And": "c_And", "Or": "c_Or",
    "SKIP": "c_SKIP", "Seq": "c_Seq", "Assign": "c_Assign",
    "Return": "c_Return", "Check": "c_Check", "If": "c_If", "While": "c_While",
    "Call": "c_Call",
    "I8": "c_I8", "U8": "c_U8", "I16": "c_I16", "U16": "c_U16",
    "I32": "c_I32", "U32": "c_U32", "I64": "c_I64", "U64": "c_U64",
}

# result nonterminal -> the SML function that lowers it to a HOL term.
# `formals`/`ids` aren't here: function_decl (the only production that would
# reference a "formals"-typed rhs argument) isn't generated in this theory
# at all -- it's part of VIMP_Notation.thy's hand-written program_structure
# territory, which calls Vimp_Grammar_Tr.formals_of directly.
TR_FN = {
    "exp": "exp_tr",
    "stmt": "stmt_tr",
    "stmts": "stmts_tr",
    "stmts_opt": "stmts_opt_tr",
    "actuals": "actuals_tr",
    "ty": "ty_tr",
}


def render_pattern_and_binds(prod: dict):
    """SML pattern for one production's Const-application, plus a position
    -> SML variable-name map for render_action_isabelle to consume. Every
    IDENT position -- variable or callee role alike -- now parses via
    id_position (see isabelle_type) and so binds the WHOLE raw subterm
    unmatched (Pure wraps it in `_constrain $ Free $ <markup>`); the role
    only decides, at the use site in render_lower_arg_isabelle, which
    markup category dest_id_position reports there, not how this pattern
    binds it. A nonterminal-typed position binds as a fresh variable meant
    to be passed through that nonterminal's own _tr function."""
    binds, pats = {}, []
    for i, sym in enumerate(prod["rhs"]):
        if sym == "IDENT":
            v = f"x{i}"
            pats.append(v)
            binds[i] = v
        elif sym in NONTERMINAL:
            v = f"a{i}"
            pats.append(v)
            binds[i] = v
    name = "_" + prod["name"]
    return f'(Const ("{name}", _), [{", ".join(pats)}])', binds


def render_lower_arg_isabelle(prod: dict, arg: dict, binds: dict, raw_idents: bool = False) -> str:
    """`raw_idents` covers the one real ambiguity in this rendering: whether
    an IDENT-typed slot becomes a HOL string literal immediately (every
    `{ctor: ..., args: [...]}` site -- the result feeds straight into an
    exp/stmt HOL constructor) or stays a plain SML string
    (`{tuple: [...]}`'s sole use, function_decl -- its one caller is
    `special: program_structure`, hand-written code that partitions by name
    equality and needs a raw string, matching how gen_vimp_menhir.py's own
    tuple renderer leaves OCaml identifiers unconverted too). Every IDENT
    slot's bound name is the raw id_position subterm, not yet a string --
    dest_id_position extracts the name and reports the role-appropriate
    markup category (IDENT_MARKUP) at its position, or none at all for a
    callee occurrence today, before either path uses the extracted name."""
    if "rhs" in arg:
        i = arg["rhs"]
        sym = prod["rhs"][i]
        if sym == "IDENT":
            markup = IDENT_MARKUP[ident_role(prod["rhs"], i)]
            name_expr = f"dest_id_position ({markup}) ctxt {binds[i]}"
            return name_expr if raw_idents else f"HOLogic.mk_literal ({name_expr})"
        return f"{TR_FN[sym]} ctxt {binds[i]}"
    if "some" in arg:
        return f"(K c_Some $ ({render_lower_arg_isabelle(prod, arg['some'], binds, raw_idents)}))"
    if "none" in arg:
        return "K c_None"
    if "literal" in arg:
        return "@{term True}" if arg["literal"] else "@{term False}"
    if "int" in arg:
        return f"HOLogic.mk_number HOLogic.intT {arg['int']}"
    raise ValueError(f"unrecognized lower arg shape: {arg}")


def render_action_isabelle(prod: dict) -> str:
    """One match-arm of the result nonterminal's _tr function. Productions
    with `special:` return None -- the caller splices in a hand-written
    clause instead (see gen_tr_function)."""
    if prod.get("special"):
        return None
    pattern, binds = render_pattern_and_binds(prod)
    if "passthrough" in prod:
        # A passthrough arg is always a recursive same-type subterm (grouping
        # parens): recurse through this nonterminal's own _tr, don't just
        # rebind -- the parsed value is still a raw parse-tree Const, not a
        # HOL term, until translated.
        rhs = f"{TR_FN[prod['result']]} ctxt {binds[prod['passthrough']]}"
        return f"{pattern} => {rhs}"
    lower = prod["lower"]
    if "tuple" in lower:
        # Route each tuple slot through the same rhs-argument rendering as
        # `args:` (render_lower_arg_isabelle) -- a tuple slot is exactly as
        # likely to need HOLogic.mk_literal (IDENT) or a nested _tr call
        # (nonterminal) as any `ctor` argument; binding it raw silently
        # leaves a parse-tree Const term where an SML string/HOL term was
        # expected (caught by cross-checking function_decl's generated
        # output against funcs_cons's hand-written `formals_of formals`).
        items = [render_lower_arg_isabelle(prod, {"rhs": i}, binds, raw_idents=True) for i in lower["tuple"]]
        rhs = "(" + ", ".join(items) + ")"
        return f"{pattern} => {rhs}"
    ctor = CTOR_VAL[lower["ctor"]]
    args = [render_lower_arg_isabelle(prod, a, binds) for a in lower["args"]]
    rhs = f'K {ctor}' if not args else f'K {ctor} $ ' + " $ ".join(f"({a})" for a in args)
    return f"{pattern} => {rhs}"


def gen_tr_function(g: dict, result_nt: str, extra_clauses: list = None) -> str:
    """Assembles the _tr function for one nonterminal from every non-special,
    non-list production targeting it, in grammar/vimp.yaml's own order, plus
    caller-supplied hand-written clauses (for that nonterminal's `special:`
    productions) spliced in first so they take priority the same way the
    hand-written original orders _imp2_uminus's nested-cancellation case
    before the generic recursive case. Every _tr function takes a
    Proof.context first: dest_id_position (called by variable-role IDENT
    slots, transitively reachable from any of these) needs one to report
    Markup.free at the identifier's source position."""
    fn = TR_FN[result_nt]
    clauses = list(extra_clauses or [])
    for prod in g["productions"]:
        if prod["result"] != result_nt or prod.get("list_of") or prod.get("optional_list_of"):
            continue
        arm = render_action_isabelle(prod)
        if arm is not None:
            clauses.append(arm)
    body = "\n       | ".join(clauses)
    return (
        f"{fn} ctxt t =\n"
        f"      (case Term.strip_comb t of\n"
        f"         {body}\n"
        f'       | _ => raise TERM ("Vimp_Grammar_Tr: {fn}", [t]))'
    )


def gen_list_tr(prod: dict, fn_name: str = None) -> str:
    """_tr for one list production, matching gen_list_syntax's fold choice:
    constructor-present -> left-fold through that constructor (stmts_tr);
    constructor-absent, nonterminal item (actuals) -> right-recursive
    List.Cons of the item's own _tr; constructor-absent, IDENT item
    (formals/ids) -> plain SML string list (no HOL wrapping at this stage --
    deferred to whichever caller assembles the surrounding term), matching
    formals_of/names_of in the hand-written original -- `fn_name` lets the
    caller ask for exactly those names rather than the mechanical `<name>_tr`
    default, since VIMP_Notation.thy's funcs_tr/prog_tr already call them
    that. Which of the two constructor-absent shapes applies is fully
    determined by whether the item symbol is a generated nonterminal or the
    IDENT terminal -- not an arbitrary special case, just a branch on symbol
    kind already present in the schema."""
    name = prod["name"]
    fn = fn_name or f"{name}_tr"
    item = prod.get("list_of") or prod.get("optional_list_of")
    if "optional_list_of" in prod:
        base = prod["result"].removesuffix("_opt")
        empty_ctor = CTOR_VAL[prod["empty"]]
        return (
            f'{fn} ctxt (Const ("_{name}_none", _)) = K {empty_ctor}\n'
            f'  | {fn} ctxt (Const ("_{name}_some", _) $ s) = {TR_FN[base]} ctxt s\n'
            f'  | {fn} _ t = raise TERM ("Vimp_Grammar_Tr: {fn}", [t])'
        )
    sep_one = f'(Const ("_{name}_one", _) $ x)'
    if "constructor" in prod:
        ctor = CTOR_VAL[prod["constructor"]]
        seq = f'(Const ("_{name}_seq", _) $ xs $ x)'
        return (
            f"{fn} ctxt {sep_one} = {TR_FN[item]} ctxt x\n"
            f'  | {fn} ctxt {seq} = K {ctor} $ ({fn} ctxt xs) $ ({TR_FN[item]} ctxt x)\n'
            f'  | {fn} _ t = raise TERM ("Vimp_Grammar_Tr: {fn}", [t])'
        )
    cons = f'(Const ("_{name}_cons", _) $ x $ rest)'
    if item == "formal":
        # A formals list is an SML (name, kind-term option) pair list, not a
        # HOL list: its consumer (VIMP_Notation's hand-written program
        # assembly) needs the raw names for proc_decl construction and the
        # annotated kinds for the program's declared-kind list. formal_tr is
        # the hand-written per-item lowering (FORMAL_TR below).
        return (
            f'{fn} ctxt (Const ("_{name}_one", _) $ x) = [formal_tr ctxt x]\n'
            f'  | {fn} ctxt {cons} = formal_tr ctxt x :: {fn} ctxt rest\n'
            f'  | {fn} _ t = raise TERM ("Vimp_Grammar_Tr: {fn}", [t])'
        )
    if item == "IDENT":
        # Item bound raw (not `Free (x, _)`): id_position wraps it in
        # `_constrain $ Free $ <markup>`, and dest_id_position -- not this
        # pattern -- is what extracts the name and reports its position.
        # Both current IDENT-item lists (formals, ids/globals) are variable
        # declarations, but `ids` reports the narrower 'global' category
        # (see IDENT_MARKUP) so a `global x, y;` declaration reads
        # differently from an ordinary formal parameter.
        markup = IDENT_MARKUP["global"] if name == "ids" else IDENT_MARKUP["variable"]
        return (
            f'{fn} ctxt (Const ("_{name}_one", _) $ x) = [dest_id_position ({markup}) ctxt x]\n'
            f'  | {fn} ctxt (Const ("_{name}_cons", _) $ x $ rest) = dest_id_position ({markup}) ctxt x :: {fn} ctxt rest\n'
            f'  | {fn} _ t = raise TERM ("Vimp_Grammar_Tr: {fn}", [t])'
        )
    return (
        f"{fn} ctxt {sep_one} = K c_Cons $ ({TR_FN[item]} ctxt x) $ K c_Nil\n"
        f'  | {fn} ctxt {cons} = K c_Cons $ ({TR_FN[item]} ctxt x) $ ({fn} ctxt rest)\n'
        f'  | {fn} _ t = raise TERM ("Vimp_Grammar_Tr: {fn}", [t])'
    )


def indent(text: str, prefix: str = "  ") -> str:
    return "\n".join(prefix + line if line else line for line in text.split("\n"))


VAL_DECLS = """\
val c_N      = "VIMP_Syntax.N"
val c_V      = "VIMP_Syntax.V"
val c_Plus   = "VIMP_Syntax.exp.Plus"
val c_Minus  = "VIMP_Syntax.exp.Minus"
val c_Times  = "VIMP_Syntax.exp.Times"

val c_Less   = "VIMP_Syntax.exp.Less"
val c_Eq     = "VIMP_Syntax.exp.Eq"
val c_Not    = "VIMP_Syntax.exp.Not"
val c_And    = "VIMP_Syntax.exp.And"
val c_Or     = "VIMP_Syntax.exp.Or"

val c_SKIP   = "VIMP_Proc.com.SKIP"
val c_Assign = "VIMP_Proc.com.Assign"
val c_Seq    = "VIMP_Proc.com.Seq"
val c_If     = "VIMP_Proc.com.If"
val c_While  = "VIMP_Proc.com.While"
val c_Call   = "VIMP_Proc.com.Call"
val c_Return = "VIMP_Proc.com.Return"
val c_Check  = "VIMP_Proc.com.Check"

val c_I8     = "VIMP_Ikind.ikind.I8"
val c_U8     = "VIMP_Ikind.ikind.U8"
val c_I16    = "VIMP_Ikind.ikind.I16"
val c_U16    = "VIMP_Ikind.ikind.U16"
val c_I32    = "VIMP_Ikind.ikind.I32"
val c_U32    = "VIMP_Ikind.ikind.U32"
val c_I64    = "VIMP_Ikind.ikind.I64"
val c_U64    = "VIMP_Ikind.ikind.U64"

val c_None   = "Option.option.None"
val c_Some   = "Option.option.Some"
val c_Cons   = "List.list.Cons"
val c_Nil    = "List.list.Nil"

fun K name = Const (name, dummyT)"""

# A formal parameter as its assembly consumers need it: the raw SML name
# for proc_decl construction, plus the annotated kind as a HOL term when
# one was written. Hand-written for the same reason formals_of's pair-list
# shape is: the pair never becomes a HOL term here; VIMP_Notation's
# program assembly splits it.
FORMAL_TR = """\
fun formal_tr ctxt t =
  (case Term.strip_comb t of
     (Const ("_formal_untyped", _), [x]) =>
       (dest_id_position (SOME Markup.free) ctxt x, NONE)
   | (Const ("_formal_typed", _), [k, x]) =>
       (dest_id_position (SOME Markup.free) ctxt x, SOME (ty_tr ctxt k))
   | _ => raise TERM ("Vimp_Grammar_Tr: formal_tr", [t]))"""

# Numeral decoding (special: integer_literal) and the compositional
# unary-minus rule (special: unary_minus) stay hand-written -- see the
# theory header text this module also generates. Everything below them is
# mechanical from grammar/vimp.yaml.
DEST_NUM = """\
(* Decode Isabelle's Num binary structure: One=1, Bit0 n=2n, Bit1 n=2n+1.
   Leaf may also be a decimal-string Const (e.g. Const("20",_)) from the
   raw lexer. *)
fun dest_num (Const (c, _)) =
      let val name = Long_Name.base_name c
      in if name = "One" then 1
         else case Int.fromString name of
                SOME n => n
              | NONE => raise TERM ("Vimp_Grammar_Tr: not a num leaf", [Const (c, dummyT)])
      end
  | dest_num (Const (c, _) $ t) =
      let val name = Long_Name.base_name c
          val n    = dest_num t
      in if name = "Bit0" then 2 * n
         else if name = "Bit1" then 2 * n + 1
         else raise TERM ("Vimp_Grammar_Tr: not a num constructor", [Const (c, dummyT) $ t])
      end
  | dest_num t = raise TERM ("Vimp_Grammar_Tr: dest_num catchall", [t])

fun read_num_const (Const ("_constify", _) $ t) = read_num_const t
  | read_num_const (Const ("_position", _) $ t) = read_num_const t
  | read_num_const ((Const ("_constrain", _) $ t) $ _) = read_num_const t
  | read_num_const (Free (s, _)) =
      (case Int.fromString s of
         SOME n => n
       | NONE => raise TERM ("Vimp_Grammar_Tr: not a numeral", [Free (s, dummyT)]))
  | read_num_const (Const (s, _)) =
      (case Int.fromString (Long_Name.base_name s) of
         SOME n => n
       | NONE => raise TERM ("Vimp_Grammar_Tr: not a numeral", [Const (s, dummyT)]))
  | read_num_const t = dest_num t

fun neg_num n = K c_N $ HOLogic.mk_number HOLogic.intT (~ n)"""

# Every IDENT (see isabelle_type) parses via id_position, not plain id --
# Pure wraps it as `_constrain $ Free (name, _) $ <markup>`, where
# <markup>'s type encodes the token's source position (the same convention
# HOL's own numeral parsing already produces, consumed above by
# read_num_const's `_constrain` case -- but read_num_const only strips that
# wrapper, since a numeral's own PIDE markup comes from lexer token
# classification, not from this parse_translation). Keeping id_position
# uniform across every IDENT -- not just variable occurrences -- means
# every VIMP identifier's source position is available for markup, even
# though `report_markup` (IDENT_MARKUP, chosen per ident_role at each call
# site) currently leaves callee occurrences unreported (NONE): provenance
# and markup classification are separate concerns, and a later phase can
# start reporting entity/procedure-reference markup for callee occurrences
# without another grammar migration.
DEST_ID_POSITION = """\
fun dest_id_position report_markup ctxt (Const ("_constrain", _) $ Free (s, _) $ m) =
      (case (report_markup, Term_Position.decode_position m) of
         (SOME markup, SOME (ps, _)) =>
           (List.app (fn p => Context_Position.report ctxt (#pos p) markup) ps; s)
       | _ => s)
  | dest_id_position _ _ (Free (s, _)) = s
  | dest_id_position _ _ t = raise TERM ("Vimp_Grammar_Tr: dest_id_position", [t])"""

EXP_SPECIALS = [
    '(Const ("_exp_num", _), [n]) =>\n'
    '           K c_N $ HOLogic.mk_number HOLogic.intT (read_num_const n)',
    '(Const ("_exp_uminus", _), [a]) =>\n'
    '           (case Term.strip_comb a of\n'
    '              (Const ("_exp_num", _), [n]) => neg_num (read_num_const n)\n'
    '            | (Const ("_exp_zero", _), []) =>\n'
    '                K c_N $ HOLogic.mk_number HOLogic.intT 0\n'
    '            | (Const ("_exp_one", _), []) => neg_num 1\n'
    '            | _ =>\n'
    '                K c_Minus $ (K c_N $ HOLogic.mk_number HOLogic.intT 0) $ exp_tr ctxt a)',
]


def gen_grammar_tr_structure(g: dict) -> str:
    """The `Vimp_Grammar_Tr` ML structure body: exp_tr/actuals_tr each
    stand alone (exp_tr calls only itself; actuals_tr calls the
    already-defined exp_tr), while stmts_tr/stmts_opt_tr/stmt_tr form one
    genuine mutual-recursion cycle (stmt_tr -> stmts_opt_tr -> stmts_tr ->
    stmt_tr) and must share one `fun ... and ...` chain. formals_of/names_of
    stand alone too (IDENT items only, no recursion into the rest). This
    shape mirrors VIMP_Notation.thy's own pre-cutover structure (aexp_tr/
    bexp_tr/actuals_tr separate, pbody_tr+stmts_tr+stmt_tr+com_tr one chain,
    names_of/formals_of separate) -- not arbitrary, just what SML's
    mutual-recursion rules require here."""
    extra_actions = gen_isabelle_extra_actions()
    exp_body = gen_tr_function(g, "exp", EXP_SPECIALS + extra_actions["exp"])
    stmt_body = gen_tr_function(g, "stmt", extra_actions["stmt"])
    ty_body = gen_tr_function(g, "ty")

    list_by_name = {p["name"]: p for p in g["productions"] if p.get("list_of") or p.get("optional_list_of")}
    actuals_body = gen_list_tr(list_by_name["actuals"])
    stmts_body = gen_list_tr(list_by_name["stmts"])
    stmts_opt_body = gen_list_tr(list_by_name["stmts_opt"])
    formals_body = gen_list_tr(list_by_name["formals"], fn_name="formals_of")
    names_body = gen_list_tr(list_by_name["ids"], fn_name="names_of")

    stmt_chain = "fun " + "\nand ".join([stmts_body, stmts_opt_body, stmt_body])

    return "\n\n".join([
        VAL_DECLS,
        DEST_NUM,
        DEST_ID_POSITION,
        f"fun {exp_body}",
        f"fun {actuals_body}",
        stmt_chain,
        f"fun {ty_body}",
        FORMAL_TR,
        f"fun {formals_body}",
        f"fun {names_body}",
    ])


HEADER = """\
theory VIMP_Grammar_Generated
  imports VIMP_Proc
begin

text \\<open>
  GENERATED FILE. Source: \\<^verbatim>\\<open>grammar/vimp.yaml\\<close>; generator:
  \\<^verbatim>\\<open>scripts/gen_vimp_isabelle.py\\<close>. Regenerate with the generator rather
  than hand-editing; a CI drift check compares regenerated output against
  this file.

  Owns the grammar-level nonterminals, syntax, and lowering (\\<open>Vimp_Grammar_Tr\\<close>)
  shared by every VIMP quotation: expressions, statements, statement lists,
  actuals, and the two identifier-list shapes (\\<open>formals\\<close>/\\<open>ids\\<close>). Does not
  register \\<open>imp \\<lbrakk> ... \\<rbrakk>\\<close> or the whole-program \\<open>program { ... }\\<close> quotation
  itself, and has no notion of \\<open>imp_prog\\<close> -- those are \\<^verbatim>\\<open>VIMP_Notation\\<close>'s
  concern (main-selection, \\<open>proc_rep\\<close> construction, and everything else specific
  to that record shape), which imports this theory and calls into
  \\<open>Vimp_Grammar_Tr\\<close> for the pieces that are the same regardless of what the
  surrounding quotation ultimately builds.

  Two lowering rules stay hand-written inside \\<open>Vimp_Grammar_Tr\\<close> rather than
  being generated from \\<open>grammar/vimp.yaml\\<close> directly: Isabelle's binary
  \\<open>Num\\<close> literal decoding (\\<open>dest_num\\<close>/\\<open>read_num_const\\<close>, no Menhir analogue)
  and the compositional unary-minus rule (folds a numeral operand into a
  negative \\<open>N\\<close>, otherwise \\<open>Minus (N 0) x\\<close> -- deliberately does NOT cancel a
  nested unary minus; \\<open>--x\\<close> lowers to \\<open>Minus (N 0) (Minus (N 0) (V x))\\<close>,
  matching the shipped CLI frontend, not to \\<open>x\\<close>). \\<open>_exp_zero\\<close>/\\<open>_exp_one\\<close>
  and \\<open>_stmt_call0\\<close>/\\<open>_stmt_callret0\\<close> are Isabelle-target realizations of a
  canonical rule that Isabelle's own mixfix grammar cannot express directly:
  \\<open>num_const\\<close> has no derivation for the literal \\<open>0\\<close> or \\<open>1\\<close> (\\<open>Num.num\\<close>'s
  \\<open>One\\<close>/\\<open>Bit0\\<close>/\\<open>Bit1\\<close> encoding has no zero, and \\<open>1\\<close> is the unwrapped base
  case), and mixfix lists have no empty derivation at all -- both confirmed
  empirically, not just by inspection: an isolation load test with only the
  generic \\<open>actuals\\<close> production failed to parse \\<open>f()\\<close>.
\\<close>
"""


def gen_theory_file(g: dict) -> str:
    parts = [
        HEADER,
        gen_nonterminals(g),
        "",
        gen_syntax_block(g),
        "",
        "ML \\<open>",
        "structure Vimp_Grammar_Tr =",
        "struct",
        indent(gen_grammar_tr_structure(g)),
        "end",
        "\\<close>",
        "",
        "end",
    ]
    return "\n".join(parts) + "\n"


def main():
    grammar_path = Path(sys.argv[1]) if len(sys.argv) > 1 else DEFAULT_GRAMMAR
    out_dir = Path(sys.argv[2]) if len(sys.argv) > 2 else DEFAULT_OUT
    out_dir.mkdir(parents=True, exist_ok=True)
    g = yaml.safe_load(grammar_path.read_text())
    out_path = out_dir / "VIMP_Grammar_Generated.thy"
    out_path.write_text(gen_theory_file(g))
    print(f"wrote {out_path}")


if __name__ == "__main__":
    main()
