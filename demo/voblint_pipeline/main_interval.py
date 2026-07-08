"""Interval demo: monovariant widening vs per-origin widening on a climbing global.

Run from the demo/ directory:  python -m voblint_pipeline.main_interval

Mirrors the Isabelle example Example_Interval_Recursion_Origin.thy.  The recursion
there and the loop here create the same thing --- a global `G` that climbs
monotonically --- which is the hard case for an infinite-height (interval) analysis.
We run three disciplines and compare:

  1. plain join      -- diverges (G climbs forever); we cap the rounds to show it
  2. monovariant widening
  3. per-origin widening (Origin_Lift): keeps each write origin's cell separate

and observe that (2) and (3) give the *same* interval for G --- the same phenomenon as
the machine-checked `rec_per_origin_matches_monovariant`.

Correspondence with Isabelle (checked):
  * EXACT: the interval domain ops (join/plus/minus/leq/`widen_ivl_core`) and the tree
    transform (`lift_tree`/`collapse`/`inject`, Origin_Lift.thy).
  * STAND-IN: the fixpoint *strategy* is a naive Kleene-with-widening, not the vendored
    TD Apinis warrowing (no narrowing; establish-then-widen models that the real solver
    never widens from bottom).  And this program is a `while`-loop, not the recursive
    procedure of Example_Interval_Recursion_Origin.thy (the demo has no Call yet) --- so
    the *numbers* need not equal the `by eval` result, but the *phenomenon* is the same.
  * `times` is an unverified approximation (not exercised here).
"""
from __future__ import annotations
from . import imp_ast as A
from . import cfg as C
from .trees import UnitEtf, side_cfg_T_eff, UNIT_G
from .strategy_tree import R
from .interval import IntervalDomain, IntervalTransfer
from .state import AbsState
from .solver import solve, solve_widening, side_env
from .origin_lift import solve_per_origin, read_per_origin
from .main import collect_vars


# G := 0;  while (G < 3) { G := G + 1 }
PROG = A.Seq(
    A.Assign("G", A.N(0)),
    A.While(A.Less(A.V("G"), A.N(3)),
            A.Assign("G", A.Plus(A.V("G"), A.N(1)))))


def _global_G(state_or_origin, dom, vars):
    """Read the interval for G out of a solved global slot (AbsState or OriginState)."""
    st = state_or_origin.collapse() if hasattr(state_or_origin, "collapse") else state_or_origin
    return dom.show(st["G"])


def run():
    dom = IntervalDomain()
    vars = tuple(sorted(collect_vars(PROG)))
    print("program:  G := 0;  while (G < 3) { G := G + 1 }")
    print("variables:", vars, " (G is a global)\n")

    g = C.compile_prog(PROG)
    print("CFG edges:")
    for u, a, w in sorted(g.edges, key=str):
        print(f"  {u:>2} --{type(a).__name__:<12}--> {w}")
    print(f"entry = {g.entry}, exit = {g.exit}\n")

    # globals start at bottom (established by the program's `G := 0`); locals at top
    s0 = AbsState(dom, vars,
                  {x: (dom.bot() if A.is_global(x) else dom.top()) for x in vars})
    bot0 = AbsState.const(dom, vars, dom.bot())
    etf = UnitEtf(IntervalTransfer(), mixed=True)
    T = side_cfg_T_eff(g, etf, bot0, s0)
    points, globals_ = g.points(), [UNIT_G]

    # 1. plain join -- infinite-height domain, does not converge
    print("[1] plain join (capped at 8 rounds; interval height is infinite):")
    sig1, it1 = solve(T, points, globals_, dom, vars, max_rounds=8)
    conv1 = "converged" if it1 < 8 else "NOT converged (still climbing)"
    print(f"    after {it1} rounds: G = {_global_G(sig1[R(UNIT_G)], dom, vars)}   -- {conv1}\n")

    # 2. monovariant widening
    print("[2] monovariant widening:")
    sig2, it2 = solve_widening(T, points, globals_, dom, vars)
    G2 = _global_G(sig2[R(UNIT_G)], dom, vars)
    print(f"    converged in {it2} rounds: G = {G2}\n")

    # 3. per-origin widening (origin = program point)
    print("[3] per-origin widening (origin = program point):")
    sig3, it3 = solve_per_origin(T, points, globals_, dom, vars, org_of=lambda x: x)
    n_origins = len(sig3[R(UNIT_G)].m)
    G3 = _global_G(sig3[R(UNIT_G)], dom, vars)
    print(f"    converged in {it3} rounds; G's slot has {n_origins} origin cell(s)")
    print(f"    collapsed G = {G3}\n")

    # comparison -- the evidence
    same = (G2 == G3)
    print("result:")
    print(f"    monovariant widening   G = {G2}")
    print(f"    per-origin  widening   G = {G3}")
    print(f"    -> {'IDENTICAL' if same else 'DIFFERENT'} "
          f"({'same phenomenon as rec_per_origin_matches_monovariant' if same else 'differs'})\n")
    print("why: per-origin widening separates the *writes* to G by origin, but every")
    print("transfer *reads* collapse_origins -- the join over all origins, including the")
    print("loop edge's own climbing cell -- so the monotone self-loop survives the split")
    print("and G still widens to the top. Precision needs origin-separated *reads*, not")
    print("just widening (docs/OPEN_PROBLEMS.md P11/P12, docs/PER_ORIGIN_WIDENING.md).")


if __name__ == "__main__":
    run()
