"""Hypothesis strategies for VIMP ASTs, and their S-expression serialization
for ast_driver.ml's build_program/build_com/build_exp (see ast_driver.ml).

VIMP has one unified `exp` type -- arithmetic, comparison, and logical
operators are ordinary exp constructors, not a separate aexp/bexp split
(see VIMP_Expr.thy's `aval`/`truthy`). manifests/vimp-grammar.yaml's `exp_paren`
production (`LPAREN exp RPAREN`, passthrough) means any exp tree is
source-expressible: the grammar-generated printer (cli/frontend/vimp_printer.ml) is a uniform
precedence-climbing printer (the precedence table in manifests/vimp-grammar.yaml) that parenthesizes a subexpression
exactly when its own constructor binds looser than the calling position
requires, for every constructor alike. `exps` below therefore generates
arbitrary trees over all expression constructors, not just left-associated
arithmetic -- the printer's parens make any shape round-trip.

com's Seq is under a different restriction, for a different reason:
vimp_parser.ml's `stmts` left-folds a list of terminated simple statements and braced statements into nested
Seq (matching VIMP_Notation.thy's stmts_tr), so only left-nested Seq trees
-- never Seq(s1, Seq(s2, s3)) -- round-trip. `atomic_com`/`coms` below use
a left-fold-over-a-list shape to stay within that restriction.

Variable/procedure names are drawn from small fixed, keyword-disjoint pools
rather than random identifiers: this sidesteps keyword collisions entirely
(by construction, not by filtering/assume rejection) while still exercising
name reuse, shadowing-shaped programs, and multi-procedure call graphs.
"""

from hypothesis import strategies as st

VAR_POOL = ["x", "y", "z", "n", "acc"]
GLOBAL_POOL = ["g1", "g2"]
PROC_POOL = ["f", "g", "helper"]
MAX_PROCS = len(PROC_POOL)


def sexp(x) -> str:
    if x is None:
        return "None"
    if isinstance(x, str):
        return x
    if isinstance(x, (list, tuple)):
        return "(" + " ".join(sexp(e) for e in x) + ")"
    raise TypeError(f"not sexp-serializable: {x!r}")


# -- exp: arbitrary nesting over all ten constructors (see module docstring) -


KIND_NAMES = ["i8", "u8", "i16", "u16", "i32", "u32", "i64", "u64"]


def exps(max_leaves=5, pool=VAR_POOL):
    numbers = st.integers(min_value=-1000, max_value=1000).map(lambda n: ("N", str(n)))
    leaves = (
        st.one_of(numbers, st.sampled_from(pool).map(lambda x: ("V", x)))
        if pool
        else numbers
    )
    return st.recursive(
        leaves,
        lambda children: st.one_of(
            st.tuples(st.just("Plus"), children, children),
            st.tuples(st.just("Minus"), children, children),
            st.tuples(st.just("Times"), children, children),
            st.tuples(st.just("Div"), children, children),
            st.tuples(st.just("Mod"), children, children),
            st.tuples(st.just("Less"), children, children),
            st.tuples(st.just("LessEq"), children, children),
            st.tuples(st.just("Greater"), children, children),
            st.tuples(st.just("GreaterEq"), children, children),
            st.tuples(st.just("NotEq"), children, children),
            st.tuples(st.just("Eq"), children, children),
            children.map(lambda e: ("Not", e)),
            st.tuples(st.just("And"), children, children),
            st.tuples(st.just("Or"), children, children),
            st.tuples(st.just("Cast"), st.sampled_from(KIND_NAMES), children),
        ),
        max_leaves=max_leaves,
    )


# -- com -----------------------------------------------------------------


@st.composite
def atomic_com(draw, depth, value_return=True):
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
        dst = draw(
            st.one_of(st.none(), st.sampled_from(VAR_POOL).map(lambda x: ("Some", x)))
        )
        proc = draw(st.sampled_from(PROC_POOL))
        actuals = draw(st.lists(exps(), max_size=2))
        return ("Call", dst, proc, actuals)
    if kind == "return":
        values = exps().map(lambda a: ("Some", a))
        return (
            "Return",
            draw(st.one_of(st.none(), values) if value_return else st.none()),
        )
    if kind == "if":
        return (
            "If",
            draw(exps()),
            draw(coms(depth - 1, value_return=value_return)),
            draw(coms(depth - 1, value_return=value_return)),
        )
    if kind == "while":
        return ("While", draw(exps()), draw(coms(depth - 1, value_return=value_return)))
    raise AssertionError(kind)


@st.composite
def coms(draw, depth=3, max_stmts=3, value_return=True):
    node = draw(atomic_com(depth, value_return))
    for _ in range(draw(st.integers(min_value=0, max_value=max_stmts - 1))):
        node = ("Seq", node, draw(atomic_com(depth, value_return)))
    return node


def main_program(names, last, globals_=()):
    """A program whose main declares each of names by an arbitrary value, then
    runs last."""
    node = ("Random", names[0])
    for x in names[1:]:
        node = ("Seq", node, ("Random", x))
    return ([], ([(x, "i32") for x in names], ("Seq", node, last)), list(globals_))


def seq_items(node):
    """The statements of a left-nested Seq chain, in order."""
    if isinstance(node, tuple) and node[0] == "Seq":
        return seq_items(node[1]) + [node[2]]
    return [node]


def returns_value(node):
    if not isinstance(node, tuple):
        return False
    if node[0] == "Return":
        return node[1] is not None
    return any(returns_value(child) for child in node[1:] if isinstance(child, tuple))


# -- proc / program --------------------------------------------------------
#
# Every variable declares its kind. Formals are drawn from VAR_POOL, disjoint
# from GLOBAL_POOL, so they never collide with a global; every other name a
# body may use is a local, written first by one statement at the top of the
# body, which the printer turns into its declaration (`k x = e;` or `k x;`).
# Each such initializer reads only names declared before it. Procedure names
# and global names are drawn without replacement, so they are pairwise
# distinct. main returns no value and so declares no return kind.


@st.composite
def body_with_locals(draw, formals, globals_, depth, value_return):
    declared = [x for x, _ in formals] + [g for g, _ in globals_]
    locals_ = [x for x in VAR_POOL + GLOBAL_POOL if x not in declared]
    items = []
    typed = []
    for x in locals_:
        typed.append((x, draw(st.sampled_from(KIND_NAMES))))
        if draw(st.booleans()):
            items.append(("Assign", x, draw(exps(pool=declared))))
        else:
            items.append(("Random", x))
        declared.append(x)
    items += seq_items(draw(coms(depth=depth, value_return=value_return)))
    node = items[0]
    for item in items[1:]:
        node = ("Seq", node, item)
    return typed, node


@st.composite
def programs(draw, max_procs=MAX_PROCS, body_depth=3):
    proc_names = draw(
        st.lists(st.sampled_from(PROC_POOL), max_size=max_procs, unique=True)
    )
    globals_ = [
        (g, draw(st.sampled_from(KIND_NAMES)))
        for g in draw(
            st.lists(
                st.sampled_from(GLOBAL_POOL), max_size=len(GLOBAL_POOL), unique=True
            )
        )
    ]
    procs = []
    for name in proc_names:
        formals = [
            (x, draw(st.sampled_from(KIND_NAMES)))
            for x in draw(st.lists(st.sampled_from(VAR_POOL), max_size=2, unique=True))
        ]
        locals_, body = draw(
            body_with_locals(formals, globals_, body_depth - 1, value_return=True)
        )
        ret = (
            draw(st.sampled_from(KIND_NAMES))
            if returns_value(body)
            else draw(st.one_of(st.none(), st.sampled_from(KIND_NAMES)))
        )
        procs.append((name, ret, formals, locals_, body))
    main_locals, main_body = draw(
        body_with_locals([], globals_, body_depth, value_return=False)
    )
    return (procs, (main_locals, main_body), globals_)
