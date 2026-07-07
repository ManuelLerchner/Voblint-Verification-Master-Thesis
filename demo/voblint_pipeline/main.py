"""End-to-end demo: com -> CFG -> equation system -> post-fixpoint -> abstract state.

Run from the demo/ directory:  python -m voblint_pipeline.main
"""
from __future__ import annotations
from . import imp_ast as A
from . import cfg as C
from .trees import UnitEtf, side_cfg_T_eff, UNIT_G
from .strategy_tree import L
from .sign import SignDomain, SignTransfer, STOP, SBOT
from .state import AbsState
from .solver import solve, side_env


def collect_vars(c: A.Com) -> set[str]:
    vs: set[str] = set()
    def av(a):
        if isinstance(a, A.V): vs.add(a.x)
        for f in ("a", "b"):
            if hasattr(a, f): av(getattr(a, f))
    def bv(b):
        for f in ("a", "b"):
            if hasattr(b, f):
                sub = getattr(b, f)
                (av if isinstance(sub, A.Aexp) else bv)(sub)
    def cv(c):
        if isinstance(c, A.Assign): vs.add(c.x); av(c.a)
        if isinstance(c, A.Seq):    cv(c.c1); cv(c.c2)
        if isinstance(c, A.If):     bv(c.b); cv(c.c1); cv(c.c2)
        if isinstance(c, A.While):  bv(c.b); cv(c.c)
    cv(c)
    return vs


def run(prog: A.Com, s0_vals: dict):
    dom = SignDomain()
    vars = tuple(sorted(collect_vars(prog) | set(s0_vals)))
    print("variables:", vars, "  (globals start with 'G')\n")

    # 1. AST -> CFG
    g = C.compile_prog(prog)
    print("CFG edges:")
    for u, a, w in sorted(g.edges, key=str):
        print(f"  {u:>2} --{type(a).__name__:<12}--> {w}")
    print(f"entry = {g.entry}, exit = {g.exit}\n")

    # 2. initial abstract state s0 (unmentioned vars default to Top)
    s0 = AbsState(dom, vars, {x: s0_vals.get(x, STOP) for x in vars})
    bot0 = AbsState.const(dom, vars, SBOT)

    # 3. equation system (mixed etf: local edges skip the global slot)
    etf = UnitEtf(SignTransfer(), mixed=True)
    T = side_cfg_T_eff(g, etf, bot0, s0)

    # 4. solve to a post-fixpoint
    print("solving (Kleene iteration):")
    sigma, iters = solve(T, g.points(), [UNIT_G], dom, vars, verbose=True)
    print(f"converged in {iters} rounds\n")

    # 5. read back the abstract state + gamma at each point
    print("abstract state per program point  (side_env = local slot |_| globals):")
    for v in sorted(g.points()):
        env = side_env(sigma, v, [UNIT_G], dom, vars)
        gam = ", ".join(f"{x} in {dom.gamma(env[x])}" for x in vars)
        print(f"  pp {v:>2}: {env.show()}   -- gamma: {gam}")


if __name__ == "__main__":
    # x := 5;  y := x + 3;  if (x < 0) then z := 0 - x else z := x
    prog = A.Seq(
        A.Assign("x", A.N(5)),
        A.Seq(
            A.Assign("y", A.Plus(A.V("x"), A.N(3))),
            A.If(A.Less(A.V("x"), A.N(0)),
                 A.Assign("z", A.Minus(A.N(0), A.V("x"))),
                 A.Assign("z", A.V("x")))))
    run(prog, s0_vals={})
