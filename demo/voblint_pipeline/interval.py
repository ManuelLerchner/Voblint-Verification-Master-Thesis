"""The Interval domain — mirrors src/Analysis/Instances/Interval (Interval_Domain,
Ivl_Exec).

An interval is [lo, hi] with lo, hi drawn from {-inf} u Z u {+inf}; the empty
interval (lo > hi) is bottom.  Unlike Sign this lattice has *infinite height*, so a
climbing value never stabilises under plain join --- widening is what makes an
analysis over it terminate.  That is exactly what the recursion/loop examples probe.

Instances mirror the Isabelle ones: order, join (sup), bot/top, and
widening/narrowing (Ivl_Exec `widen`/`narrow`).
"""
from __future__ import annotations
from dataclasses import dataclass
from . import imp_ast as A
from .state import AbsState

NEG_INF = float("-inf")
POS_INF = float("inf")


@dataclass(frozen=True)
class Ivl:
    lo: float          # -inf, an int (stored as float), or +inf
    hi: float
    def is_bot(self) -> bool:
        return self.lo > self.hi


BOT = Ivl(POS_INF, NEG_INF)     # Ivl PlusInf MinInf
TOP = Ivl(NEG_INF, POS_INF)     # Ivl MinInf PlusInf


def _num(x) -> str:
    if x == NEG_INF: return "-inf"
    if x == POS_INF: return "+inf"
    return str(int(x))


def ivl_show(a: Ivl) -> str:
    return "_|_" if a.is_bot() else f"[{_num(a.lo)}, {_num(a.hi)}]"


def ivl_gamma(a: Ivl) -> str:
    if a.is_bot():                     return "{}"
    if a.lo == NEG_INF and a.hi == POS_INF: return "Z"
    return f"{{{_num(a.lo)} <= n <= {_num(a.hi)}}}"


def ivl_join(a: Ivl, b: Ivl) -> Ivl:      # sup (Interval_Domain)
    if a.is_bot(): return b
    if b.is_bot(): return a
    return Ivl(min(a.lo, b.lo), max(a.hi, b.hi))


def ivl_leq(a: Ivl, b: Ivl) -> bool:      # <=
    if a.is_bot(): return True
    if b.is_bot(): return False
    return b.lo <= a.lo and a.hi <= b.hi


def ivl_widen(a: Ivl, b: Ivl) -> Ivl:
    """widen_ivl_core (Interval_Domain.thy:259), verbatim -- no bottom special case:
         Ivl (if l1<=l2 then l1 else MinInf) (if u2<=u1 then u1 else PlusInf).
    Note this makes `widen(bot, b) = top`: the operator is only ever meant to be
    applied to an *established* (non-bottom) left value -- the solver establishes a
    slot by join first and only then widens on re-visits (see solve_widening)."""
    return Ivl(a.lo if a.lo <= b.lo else NEG_INF,
               a.hi if b.hi <= a.hi else POS_INF)


# ---- abstract arithmetic (interval, with careful infinity handling) -----------
def _m(x, y):                              # products, treating 0 * inf as 0
    return 0.0 if (x == 0 or y == 0) else x * y

def ivl_plus(a: Ivl, b: Ivl) -> Ivl:
    if a.is_bot() or b.is_bot(): return BOT
    return Ivl(a.lo + b.lo, a.hi + b.hi)

def ivl_minus(a: Ivl, b: Ivl) -> Ivl:
    if a.is_bot() or b.is_bot(): return BOT
    return Ivl(a.lo - b.hi, a.hi - b.lo)

def ivl_times(a: Ivl, b: Ivl) -> Ivl:
    """Endpoint-product interval multiply.  APPROXIMATE: not verified against
    Isabelle `ivl_times_core` / `times_eint` and not exercised by the current
    examples (which use only `+`).  Kept for completeness; check before relying on it."""
    if a.is_bot() or b.is_bot(): return BOT
    ps = [_m(a.lo, b.lo), _m(a.lo, b.hi), _m(a.hi, b.lo), _m(a.hi, b.hi)]
    return Ivl(min(ps), max(ps))


def aval_ivl(a: A.Aexp, sigma: AbsState) -> Ivl:
    if isinstance(a, A.N):     return Ivl(float(a.n), float(a.n))
    if isinstance(a, A.V):     return sigma[a.x]
    if isinstance(a, A.Plus):  return ivl_plus(aval_ivl(a.a, sigma), aval_ivl(a.b, sigma))
    if isinstance(a, A.Minus): return ivl_minus(aval_ivl(a.a, sigma), aval_ivl(a.b, sigma))
    if isinstance(a, A.Times): return ivl_times(aval_ivl(a.a, sigma), aval_ivl(a.b, sigma))
    raise TypeError(a)


class IntervalDomain:
    """Implements the Domain protocol (with widen) for AbsState."""
    def bot(self):         return BOT
    def top(self):         return TOP
    def join(self, x, y):  return ivl_join(x, y)
    def leq(self, x, y):   return ivl_leq(x, y)
    def widen(self, x, y): return ivl_widen(x, y)
    def gamma(self, x):    return ivl_gamma(x)
    def show(self, x):     return ivl_show(x)


class IntervalTransfer:
    """Forward domain_transfer for intervals.  As in the Sign demo, assume/assume_not
    are the identity (sound, imprecise) -- the guard is not refined, so widening runs
    to [.., +inf] with no narrowing back."""
    def assign(self, x, a):
        return lambda sigma: sigma.update(x, aval_ivl(a, sigma))
    def assume(self, b):      return lambda sigma: sigma
    def assume_not(self, b):  return lambda sigma: sigma
    def enter(self):
        def f(sigma: AbsState):
            return AbsState(sigma.dom, sigma.vars,
                            {x: (sigma[x] if A.is_global(x) else TOP) for x in sigma.vars})
        return f

    def apply_tf(self, a):
        from . import cfg as C
        if isinstance(a, C.EA_Nop):        return lambda s: s
        if isinstance(a, C.EA_Assign):     return self.assign(a.x, a.a)
        if isinstance(a, C.EA_Assume):     return self.assume(a.b)
        if isinstance(a, C.EA_AssumeNot):  return self.assume_not(a.b)
        if isinstance(a, C.EA_Enter):      return self.enter()
        raise TypeError(a)
