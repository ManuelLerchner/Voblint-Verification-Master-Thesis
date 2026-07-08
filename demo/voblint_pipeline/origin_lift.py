"""Per-origin widening as an equation-system transform.

Mirrors src/Analysis/Generic/Solver/Exec/Origin_Lift.thy (and the domain
src/Analysis/Generic/Domain/Origin_State.thy).

Per-origin widening keeps each write origin's contribution to a shared slot in its
own cell and widens those cells independently; a read `collapse`s the cells.  Here it
is a *thin adapter*: `lift_tree` lifts an existing equation system's value domain from
AbsState to OriginState (origin -> AbsState).  Reads collapse, writes inject at the
evaluated unknown's origin, transfers unchanged; the lifted system is then solved by
the ordinary widening iteration, whose per-origin pointwise widening *is* per-origin
widening.  No new solver.

The headline (matching the Isabelle `by eval` theorems `rec_per_origin_*`): on a
climbing global the observable result is the *same* as monovariant widening, because
the read collapses across origins and re-merges the self-loop before the transfer.
"""
from __future__ import annotations
from .strategy_tree import Tree, Answer, QueryL, QueryG, Side, L, R, traverse_rhs, sides_of_rhs
from .state import AbsState, bot_state


class OriginState:
    """Origin_State.thy — a value per origin, implicit bottom default.

    `m` maps an origin (here a program point) to an AbsState; an origin absent from
    `m` holds bottom.  The observable value is `collapse` = the join over all cells."""
    __slots__ = ("dom", "vars", "m")

    def __init__(self, dom, vars, m: dict):
        bs = bot_state(dom, vars)
        self.dom, self.vars = dom, tuple(vars)
        self.m = {k: v for k, v in m.items() if v != bs}   # drop bottom cells (canonical)

    @classmethod
    def bot(cls, dom, vars) -> "OriginState":
        return cls(dom, vars, {})

    @classmethod
    def inject(cls, org, st: AbsState) -> "OriginState":
        """inject_origin: the contribution `st`, at origin `org` only."""
        return cls(st.dom, st.vars, {org: st})

    def collapse(self) -> AbsState:
        """collapse_origins: join over all origins (bottom if empty)."""
        acc = bot_state(self.dom, self.vars)
        for v in self.m.values():
            acc = acc.join(v)
        return acc

    def _cell(self, k) -> AbsState:
        return self.m.get(k, bot_state(self.dom, self.vars))

    def join(self, other: "OriginState") -> "OriginState":
        keys = set(self.m) | set(other.m)
        return OriginState(self.dom, self.vars,
                           {k: self._cell(k).join(other._cell(k)) for k in keys})

    def widen(self, other: "OriginState") -> "OriginState":
        keys = set(self.m) | set(other.m)
        return OriginState(self.dom, self.vars,
                           {k: self._cell(k).widen(other._cell(k)) for k in keys})

    def leq(self, other: "OriginState") -> bool:
        return all(self._cell(k).leq(other._cell(k)) for k in set(self.m) | set(other.m))

    def __eq__(self, other):
        return isinstance(other, OriginState) and self.m == other.m

    def show(self) -> str:
        return f"<{len(self.m)} origin(s); collapse={self.collapse().show()}>"


# ---- the tree transform (Origin_Lift.thy: lift_tree) --------------------------
def lift_tree(org, t: Tree) -> Tree:
    """Read -> collapse; write (Answer/Side) -> inject at `org`; transfer unchanged."""
    if isinstance(t, Answer):
        return Answer(OriginState.inject(org, t.d))
    if isinstance(t, QueryL):
        return QueryL(t.x, lambda ov: lift_tree(org, t.k(ov.collapse())))
    if isinstance(t, QueryG):
        return QueryG(t.g, lambda ov: lift_tree(org, t.k(ov.collapse())))
    if isinstance(t, Side):
        return Side(t.g, OriginState.inject(org, t.d), lift_tree(org, t.t))
    raise TypeError(t)


def origin_lift_eqs(org_of, T):
    """origin_lift_eqs: tag each equation's writes/answers with its unknown's origin."""
    return lambda x: lift_tree(org_of(x), T(x))


def solve_per_origin(T, points, global_keys, dom, vars, org_of=lambda x: x,
                     verbose: bool = False, max_rounds: int = 1000):
    """TD_side_per_origin_widen_solve: widening iteration over the origin-lifted system.

    Values are OriginState; widening is per-origin (pointwise per cell).  Returns
    (sigma, iterations) with sigma mapping keys to OriginState."""
    Tl = origin_lift_eqs(org_of, T)
    obot = OriginState.bot(dom, vars)
    sigma = {L(v): obot for v in points}
    sigma |= {R(g): obot for g in global_keys}

    it = 0
    while it < max_rounds:
        it += 1
        new = dict(sigma)
        for v in sorted(points):
            t = Tl(v)
            cur = new[L(v)]
            new[L(v)] = cur.widen(cur.join(traverse_rhs(t, sigma, dom, vars)))
            for key, d in sides_of_rhs(t, sigma, dom, vars).items():
                base = new.get(key, obot)
                new[key] = base.widen(base.join(d))
        if verbose:
            print(f"  round {it}: " +
                  " ".join(f"{k[1]}={new[k].show()}" for k in new if k[0] == 'L'))
        if all(new[k] == sigma[k] for k in new):
            return new, it
        sigma = new
    return sigma, it


def read_per_origin(sigma: dict, key) -> AbsState:
    """collapse_origins of one solved slot: the observable value."""
    return sigma[key].collapse()
