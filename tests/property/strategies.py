"""Hypothesis strategies for VIMP ASTs, and their S-expression serialization
for ast_driver.ml's build_program/build_com/... (see ast_driver.ml).

Only source-expressible aexp shapes are generated: VIMP_Source_Print.thy's
string_of_aexp prints Plus/Minus/Times with no parens at all (the source
grammar has no parenthesized aexp production -- see VIMP_Notation.thy /
vimp_parser.ml's aexp_prod/aexp), so only left-associated trees survive a
print/parse round trip: Times nests only on its left branch over atoms
(N/V), and Plus/Minus nest only on their left branch over Times-chains.
Encoding that shape directly in `terms`/`aexps` below (rather than
generating arbitrary trees and filtering) keeps every generated example
relevant and gives Hypothesis useful shrinking.

com's Seq is under the same restriction, for the same reason:
vimp_parser.ml's `stmts` left-folds a ';'-chained statement list into nested
Seq (matching VIMP_Notation.thy's stmts_tr), so only left-nested Seq trees
-- never Seq(s1, Seq(s2, s3)) -- round-trip. `atomic_com`/`coms` below use
the same left-fold-over-a-list shape as `terms`/`aexps`.

bexp has no such restriction: VIMP_Notation.thy's bexp grammar parenthesizes
And/Or/Not explicitly, so arbitrary nesting round-trips.

Variable/procedure names are drawn from small fixed, keyword-disjoint pools
rather than random identifiers: this sidesteps keyword collisions entirely
(by construction, not by filtering/assume rejection) while still exercising
name reuse, shadowing-shaped programs, and multi-procedure call graphs.
"""

from hypothesis import strategies as st

VAR_POOL = ["x", "y", "z", "n", "acc"]
GLOBAL_POOL = ["g1", "g2"]
PROC_POOL = ["f", "g", "helper"]


def sexp(x) -> str:
    if x is None:
        return "None"
    if isinstance(x, str):
        return x
    if isinstance(x, (list, tuple)):
        return "(" + " ".join(sexp(e) for e in x) + ")"
    raise TypeError(f"not sexp-serializable: {x!r}")


# -- aexp: left-associated only (see module docstring) -----------------------

@st.composite
def atoms(draw):
    return draw(
        st.one_of(
            st.integers(min_value=-1000, max_value=1000).map(lambda n: ("N", str(n))),
            st.sampled_from(VAR_POOL).map(lambda x: ("V", x)),
        )
    )


@st.composite
def terms(draw, max_atoms=3):
    node = draw(atoms())
    for _ in range(draw(st.integers(min_value=0, max_value=max_atoms - 1))):
        node = ("Times", node, draw(atoms()))
    return node


@st.composite
def aexps(draw, max_terms=3, max_atoms=3):
    node = draw(terms(max_atoms))
    for _ in range(draw(st.integers(min_value=0, max_value=max_terms - 1))):
        op = draw(st.sampled_from(["Plus", "Minus"]))
        node = (op, node, draw(terms(max_atoms)))
    return node


# -- bexp: arbitrarily nested, always parenthesized in source ----------------

def bexps(max_leaves=5):
    leaves = st.one_of(
        st.sampled_from([("Bc", "true"), ("Bc", "false")]),
        st.tuples(st.sampled_from(["Less", "Eq"]), aexps(), aexps()),
    )
    return st.recursive(
        leaves,
        lambda children: st.one_of(
            children.map(lambda b: ("Not", b)),
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
        return ("Assign", draw(st.sampled_from(assignable)), draw(aexps()))
    if kind == "random":
        return ("Random", draw(st.sampled_from(assignable)))
    if kind == "check":
        return ("Check", draw(bexps()))
    if kind == "call":
        dst = draw(st.one_of(st.none(), st.sampled_from(VAR_POOL).map(lambda x: ("Some", x))))
        proc = draw(st.sampled_from(PROC_POOL))
        actuals = draw(st.lists(aexps(), max_size=2))
        return ("Call", dst, proc, actuals)
    if kind == "return":
        return ("Return", draw(st.one_of(st.none(), aexps().map(lambda a: ("Some", a)))))
    if kind == "if":
        return ("If", draw(bexps()), draw(coms(depth - 1)), draw(coms(depth - 1)))
    if kind == "while":
        return ("While", draw(bexps()), draw(coms(depth - 1)))
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
