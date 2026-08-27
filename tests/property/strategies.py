"""Hypothesis strategies for VIMP ASTs, and their S-expression serialization
for ast_driver.ml's build_skeleton/build_com/build_exp (see ast_driver.ml).

VIMP has one unified `exp` type -- arithmetic, comparison, and logical
operators are ordinary exp constructors, not a separate aexp/bexp split
(see VIMP_Expr.thy's `aval`/`truthy`). grammar/vimp.yaml's `exp_paren`
production (`LPAREN exp RPAREN`, passthrough) means any exp tree is
source-expressible: VIMP_Source_Print.thy's string_of_exp is a uniform
precedence-climbing printer (exp_prio) that parenthesizes a subexpression
exactly when its own constructor binds looser than the calling position
requires, for every constructor alike. `exps` below therefore generates
arbitrary trees over all ten constructors, not just left-associated
arithmetic -- the printer's parens make any shape round-trip.

com's Seq is under a different restriction, for a different reason:
vimp_parser.ml's `stmts` left-folds a ';'-chained statement list into nested
Seq (matching VIMP_Notation.thy's stmts_tr), so only left-nested Seq trees
-- never Seq(s1, Seq(s2, s3)) -- round-trip. `atomic_com`/`coms` below use
a left-fold-over-a-list shape to stay within that restriction.

Variable/procedure names are drawn from small fixed, keyword-disjoint pools
rather than random identifiers: this sidesteps keyword collisions entirely
(by construction, not by filtering/assume rejection) while still exercising
name reuse, shadowing-shaped programs, and multi-procedure call graphs.

Declarations are absent from these strategies on purpose. VIMP_Source_Print
.thy's pretty_string_of_program prints no kind on a global or a formal, no
procedure return kind, and no local declaration at all, so what it emits is a
declaration skeleton rather than source the frontend accepts. ast_driver fills
that skeleton in -- one fixed kind throughout, the locals a body's own variable
uses imply, a return kind for a value-returning procedure -- and builds the
AST from the same derivation, so a generated program still round-trips
exactly. `programs` therefore describes the shape being tested (expressions,
statement nesting, call graphs) and nothing about which kind a name carries.

`programs_with_locals`/`source_with_locals` add an extra, freely-shaped
prologue on top of that completed source, for the properties that only need
parse acceptance: several names per line, varied kinds. Those names avoid
every name ast_driver already declares, so the two prologues never collide.
"""

import re

from hypothesis import strategies as st

VAR_POOL = ["x", "y", "z", "n", "acc"]
GLOBAL_POOL = ["g1", "g2"]
PROC_POOL = ["f", "g", "helper"]
MAIN_NAME = "main"
LOCAL_KIND_POOL = [
    "int8", "uint8", "int16", "uint16", "int32", "uint32", "int64", "uint64",
]


def sexp(x) -> str:
    if x is None:
        return "None"
    if isinstance(x, str):
        return x
    if isinstance(x, (list, tuple)):
        return "(" + " ".join(sexp(e) for e in x) + ")"
    raise TypeError(f"not sexp-serializable: {x!r}")


# -- exp: arbitrary nesting over all ten constructors (see module docstring) -

def exps(max_leaves=5):
    leaves = st.one_of(
        st.integers(min_value=-1000, max_value=1000).map(lambda n: ("N", str(n))),
        st.sampled_from(VAR_POOL).map(lambda x: ("V", x)),
    )
    return st.recursive(
        leaves,
        lambda children: st.one_of(
            st.tuples(st.just("Plus"), children, children),
            st.tuples(st.just("Minus"), children, children),
            st.tuples(st.just("Times"), children, children),
            st.tuples(st.just("Less"), children, children),
            st.tuples(st.just("Eq"), children, children),
            children.map(lambda e: ("Not", e)),
            st.tuples(st.just("And"), children, children),
            st.tuples(st.just("Or"), children, children),
        ),
        max_leaves=max_leaves,
    )


# -- com -----------------------------------------------------------------

@st.composite
def atomic_com(draw, depth):
    assignable = VAR_POOL + GLOBAL_POOL
    leaf_kinds = ["skip", "assign", "random", "check", "call", "return"]
    kinds = leaf_kinds + (["if", "while"] if depth > 0 else [])
    kind = draw(st.sampled_from(kinds))

    if kind == "skip":
        return "Skip"
    if kind == "assign":
        return ("Assign", draw(st.sampled_from(assignable)), draw(exps()))
    if kind == "random":
        return ("Random", draw(st.sampled_from(assignable)))
    if kind == "check":
        return ("Check", draw(exps()))
    if kind == "call":
        dst = draw(st.one_of(st.none(), st.sampled_from(VAR_POOL).map(lambda x: ("Some", x))))
        proc = draw(st.sampled_from(PROC_POOL))
        actuals = draw(st.lists(exps(), max_size=2))
        return ("Call", dst, proc, actuals)
    if kind == "return":
        return ("Return", draw(st.one_of(st.none(), exps().map(lambda a: ("Some", a)))))
    if kind == "if":
        return ("If", draw(exps()), draw(coms(depth - 1)), draw(coms(depth - 1)))
    if kind == "while":
        return ("While", draw(exps()), draw(coms(depth - 1)))
    raise AssertionError(kind)


@st.composite
def coms(draw, depth=3, max_stmts=3):
    node = draw(atomic_com(depth))
    for _ in range(draw(st.integers(min_value=0, max_value=max_stmts - 1))):
        node = ("Seq", node, draw(atomic_com(depth)))
    return node


# -- proc / program --------------------------------------------------------
#
# Formal parameters are drawn only from VAR_POOL, disjoint from GLOBAL_POOL,
# so they never collide with a global (vimp_parser.ml's program rejects a
# proc that declares a global as a formal). Procedure names and global names
# are each drawn without replacement, so they're pairwise distinct too
# (vimp_parser.ml also rejects duplicate procedure/global names).

@st.composite
def programs(draw, max_procs=len(PROC_POOL), body_depth=3):
    proc_names = draw(st.lists(st.sampled_from(PROC_POOL), max_size=max_procs, unique=True))
    procs = []
    for name in proc_names:
        formals = draw(st.lists(st.sampled_from(VAR_POOL), max_size=2, unique=True))
        body = draw(coms(depth=body_depth - 1))
        procs.append((name, formals, body))
    main_body = draw(coms(depth=body_depth))
    globals_ = draw(st.lists(st.sampled_from(GLOBAL_POOL), max_size=len(GLOBAL_POOL), unique=True))
    return (procs, main_body, globals_)


# -- variables a body touches ----------------------------------------------
#
# Mirrors ast_driver's com_vars: every variable a body reads or writes that is
# neither a global nor one of the procedure's formals becomes a declared local
# in the printed source, so an extra prologue spliced on top must avoid those
# names or the frontend rejects the result as a duplicate declaration. A call's
# callee is a Call field, never a ("V", _) leaf, so a procedure name never
# counts as a variable here.


def _exp_vars(e, acc):
    tag = e[0]
    if tag == "V":
        acc.add(e[1])
    elif tag == "N":
        pass
    elif tag == "Not":
        _exp_vars(e[1], acc)
    else:
        _exp_vars(e[1], acc)
        _exp_vars(e[2], acc)


def used_vars(com, acc=None):
    acc = set() if acc is None else acc
    if com == "Skip":
        return acc
    tag = com[0]
    if tag == "Assign":
        acc.add(com[1])
        _exp_vars(com[2], acc)
    elif tag == "Random":
        acc.add(com[1])
    elif tag == "Check":
        _exp_vars(com[1], acc)
    elif tag == "Seq":
        used_vars(com[1], acc)
        used_vars(com[2], acc)
    elif tag == "If":
        _exp_vars(com[1], acc)
        used_vars(com[2], acc)
        used_vars(com[3], acc)
    elif tag == "While":
        _exp_vars(com[1], acc)
        used_vars(com[2], acc)
    elif tag == "Call":
        if com[1] is not None:
            acc.add(com[1][1])
        for actual in com[3]:
            _exp_vars(actual, acc)
    elif tag == "Return":
        if com[1] is not None:
            _exp_vars(com[1][1], acc)
    else:
        raise AssertionError(f"unrecognized com tag: {tag}")
    return acc


# -- procedure-local declarations ------------------------------------------
#
# A declaration is `<kind> name1, name2, ...;` with an explicit kind: unlike
# a global, a local has no untyped form. All of a procedure's declarations
# form a prologue between the body's `{` and its first statement --
# grammar/vimp.yaml's function_decl puts `locals_star` before `stmts_opt`,
# and a declaration after a statement is a parse error. Both the placement
# and the name-collision rules below are respected by construction, so no
# generated program is ever one the frontend must reject.

@st.composite
def locals_prologue(draw, available=(), kind_of=None):
    """Extra declaration groups for one procedure, as [(kind, [name, ...]), ...].

    `available` is the set of names the caller has cleared for prologue use
    program-wide, and `kind_of` fixes each name's kind. Both are decided once
    per program rather than per procedure, because compilation resolves a name
    through one flat kind environment: the same name declared at two kinds
    anywhere in the program is rejected by the frontend, so a generator that
    drew kinds per procedure would produce programs the language does not
    have. VAR_POOL is disjoint from GLOBAL_POOL, so a local can never shadow a
    declared global either. The empty prologue stays the common case -- almost
    every program in the regression corpus has none.
    """
    available = list(available)
    if not available:
        return []
    names = draw(st.lists(st.sampled_from(available), max_size=len(available), unique=True))
    groups = []
    while names:
        take = draw(st.integers(min_value=1, max_value=len(names)))
        head, names = names[:take], names[take:]
        # One group per kind, since a group carries a single kind keyword.
        by_kind = {}
        for n in head:
            by_kind.setdefault(kind_of[n], []).append(n)
        groups.extend(by_kind.items())
    return groups


@st.composite
def programs_with_locals(draw, max_procs=len(PROC_POOL), body_depth=3):
    """A program paired with one locals prologue per procedure, main included.

    The AST half is an ordinary `programs()` value: locals are carried
    separately because they do not survive printing (see the module
    docstring), so this pair is for parse-level properties, not round-trip.
    """
    procs, main_body, globals_ = draw(programs(max_procs=max_procs, body_depth=body_depth))

    # Every name ast_driver itself declares -- any procedure's formals, any
    # body's variables -- is off limits to the extra prologue, and off limits
    # program-wide rather than per procedure. ast_driver declares those at its
    # own fixed kind, so a prologue re-declaring one elsewhere at a different
    # kind would be the same flat-environment conflict.
    taken = set(used_vars(main_body))
    for _name, formals, body in procs:
        taken |= set(formals) | set(used_vars(body))

    available = [x for x in VAR_POOL if x not in taken]
    kind_of = {x: draw(st.sampled_from(LOCAL_KIND_POOL)) for x in available}

    prologues = {}
    for name, _formals, _body in procs:
        prologues[name] = draw(locals_prologue(available=available, kind_of=kind_of))
    prologues[MAIN_NAME] = draw(locals_prologue(available=available, kind_of=kind_of))
    return (procs, main_body, globals_), prologues


# A definition header sits at column zero and opens with its return kind --
# `void` for a procedure that yields no value, a kind keyword otherwise.
PROC_HEADER = re.compile(r"^(?:void|" + "|".join(LOCAL_KIND_POOL) + r") (\w+)\(")


def source_with_locals(source: str, prologues: dict) -> str:
    """Splice each procedure's locals prologue into printed VIMP source.

    ast_driver's completed source puts a procedure's own forced local
    declarations directly after its header, so inserting these lines right
    after that header keeps them inside the prologue the grammar requires;
    the four-space indent matches the printer's own body indent. Body lines
    are indented, headers are not, so the header regex cannot match inside a
    body.
    """
    out = []
    for line in source.split("\n"):
        out.append(line)
        header = PROC_HEADER.match(line)
        if header:
            out.extend(
                f"    {kind} {', '.join(names)};"
                for kind, names in prologues.get(header.group(1), [])
            )
    return "\n".join(out)
