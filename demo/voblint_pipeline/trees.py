"""Edge/combine trees, the sequential-composition monad, and the equation-system
generator.

seqcomp_tree            : monadic bind (Strategy_Tree_Monad.thy)
unit_edge_tree          : src/.../TD_Side_CFG.thy:128
local_edge_tree         : src/.../TD_Side_CFG.thy:369
unit_combine_tree       : src/.../TD_Side_CFG.thy:140
apply_etf / apply_tf    : src/.../Constraint_System.thy:443, :44
side_rhs_fold_eff       : src/.../TD_Side_Tree.thy:36
make_side_rhs_tree_eff  : src/.../TD_Side_Tree.thy:50
side_cfg_T_eff          : src/.../TD_Side_Tree.thy:61

The single global slot of the base system is the unit key g = () , modelled here
as the constant UNIT_G.
"""
from __future__ import annotations
from typing import Callable
from .strategy_tree import Tree, Answer, QueryL, QueryG, Side
from .state import AbsState
from . import cfg as C
from . import imp_ast as A

UNIT_G = None   # the () global key of the base (unit) system


def seqcomp_tree(t: Tree, k: Callable[[AbsState], Tree]) -> Tree:
    """Run t, feed its local Answer to k, preserving Side writes and queries."""
    if isinstance(t, Answer):  return k(t.d)
    if isinstance(t, QueryL):  return QueryL(t.x, lambda v: seqcomp_tree(t.k(v), k))
    if isinstance(t, QueryG):  return QueryG(t.g, lambda v: seqcomp_tree(t.k(v), k))
    if isinstance(t, Side):    return Side(t.g, t.d, seqcomp_tree(t.t, k))
    raise TypeError(t)


def unit_edge_tree(f: Callable[[AbsState], AbsState], u) -> Tree:
    """TD_Side_CFG.thy:128 — read local+global, apply f, publish global, answer local."""
    def after_su(su: AbsState) -> Tree:
        def after_g(g: AbsState) -> Tree:
            res = f(su.join(g))
            return Side(UNIT_G, res.restrict_global(), Answer(res.restrict_local()))
        return QueryG(UNIT_G, after_g)
    return QueryL(u, after_su)


def local_edge_tree(f: Callable[[AbsState], AbsState], u) -> Tree:
    """TD_Side_CFG.thy:369 — purely local: no QueryG, no Side."""
    def after_su(su: AbsState) -> Tree:
        return Answer(f(su.restrict_local()).restrict_local().join(su.restrict_global()))
    return QueryL(u, after_su)


def unit_combine_tree(cc, ex) -> Tree:
    """TD_Side_CFG.thy:140 — procedure return: caller locals + callee globals."""
    def after_sc(sc: AbsState) -> Tree:
        def after_se(se: AbsState) -> Tree:
            def after_g(g: AbsState) -> Tree:
                res = sc.join(g).restrict_local().join(se.join(g).restrict_global())
                return Side(UNIT_G, res.restrict_global(), Answer(res.restrict_local()))
            return QueryG(UNIT_G, after_g)
        return QueryL(ex, after_se)
    return QueryL(cc, after_sc)


class UnitEtf:
    """unit_etf_of_transfer tf (TD_Side_CFG.thy:553): every edge is a unit tree.

    `tf` is a forward DomainTransfer providing apply_tf(action) -> (state->state).
    `mixed` routes purely-local actions through local_edge_tree instead.
    """
    def __init__(self, tf, mixed: bool = False):
        self.tf, self.mixed = tf, mixed

    def edge_tree(self, a: C.EA, u) -> Tree:
        f = self.tf.apply_tf(a)                       # Constraint_System.thy:44
        if self.mixed and _local_edge_action(a):
            return local_edge_tree(f, u)
        return unit_edge_tree(f, u)

    def combine_tree(self, cc, ex) -> Tree:
        return unit_combine_tree(cc, ex)


def _local_edge_action(a: C.EA) -> bool:
    """Constraint_System — an edge that neither reads nor writes globals."""
    if isinstance(a, C.EA_Nop):        return True
    if isinstance(a, C.EA_Assign):     return (not A.is_global(a.x)) and (not A.aexp_mentions_global(a.a))
    if isinstance(a, (C.EA_Assume, C.EA_AssumeNot)): return not A.bexp_mentions_global(a.b)
    if isinstance(a, C.EA_Enter):      return False
    raise TypeError(a)


# ---- the generator ------------------------------------------------------------
def side_rhs_fold_eff(etf, acc: AbsState, ps: list, cs: list) -> Tree:
    """TD_Side_Tree.thy:36 — fold incoming edges then combines, joining into acc."""
    if not ps and not cs:
        return Answer(acc)
    if ps:
        (u, a), rest = ps[0], ps[1:]
        return seqcomp_tree(etf.edge_tree(a, u),
                            lambda res: side_rhs_fold_eff(etf, acc.join(res), rest, cs))
    (ccx, ex), rest = cs[0], cs[1:]
    return seqcomp_tree(etf.combine_tree(ccx, ex),
                        lambda res: side_rhs_fold_eff(etf, acc.join(res), [], rest))


def side_cfg_T_eff(g: C.Cfg, etf, bot0: AbsState, s0: AbsState):
    """TD_Side_Tree.thy:61/50 — the equation system T: pp -> strategy_tree."""
    def T(v: int) -> Tree:
        at_entry = (v == g.entry)
        acc0 = bot0.join(s0.restrict_local()) if at_entry else bot0
        t = side_rhs_fold_eff(etf, acc0, g.predecessor_list(v), g.combine_predecessor_list(v))
        # entry seeds the global slot with the initial globals (gseed = UNIT_G)
        return Side(UNIT_G, s0.restrict_global(), t) if at_entry else t
    return T
