"""Abstract states and the local/global splitters.

abs_state is a total map vname -> 'd (domain element).  For a concrete program we
carry the finite set of variables that occur in it, so an AbsState is an honest
total function on the relevant names.

restrict_local / restrict_global : src/.../TD_Side_CFG.thy:25,29
side_env / glob_env              : src/.../TD_Side_CFG.thy:93, Constraint_System.thy:525
combine_abs  <sc|se>             : src/.../Constraint_System.thy:273
"""
from __future__ import annotations
from typing import Protocol
from .imp_ast import is_global


class Domain(Protocol):
    """A sound_domain: a bounded semilattice with a concretisation gamma.
    Domains over an infinite-height lattice (Interval) also provide `widen`."""
    def bot(self): ...
    def join(self, x, y): ...
    def leq(self, x, y) -> bool: ...
    def gamma(self, x) -> str: ...
    def show(self, x) -> str: ...
    def widen(self, x, y): ...   # optional; required for widening solves


class AbsState:
    """Total map vname -> 'd over a fixed variable universe `vars`."""
    __slots__ = ("dom", "vars", "m")

    def __init__(self, dom: Domain, vars: tuple[str, ...], m: dict):
        self.dom, self.vars, self.m = dom, tuple(vars), dict(m)

    @classmethod
    def const(cls, dom, vars, val):
        return cls(dom, vars, {x: val for x in vars})

    def __getitem__(self, x):        return self.m[x]
    def update(self, x, v):          # sigma(x := v)
        m = dict(self.m); m[x] = v; return AbsState(self.dom, self.vars, m)

    def join(self, other: "AbsState") -> "AbsState":   # pointwise ⊔
        return AbsState(self.dom, self.vars,
                        {x: self.dom.join(self.m[x], other.m[x]) for x in self.vars})

    def leq(self, other: "AbsState") -> bool:          # pointwise ≤
        return all(self.dom.leq(self.m[x], other.m[x]) for x in self.vars)

    def widen(self, other: "AbsState") -> "AbsState":  # pointwise domain widening
        return AbsState(self.dom, self.vars,
                        {x: self.dom.widen(self.m[x], other.m[x]) for x in self.vars})

    def __eq__(self, other):         return isinstance(other, AbsState) and self.m == other.m

    def restrict_local(self) -> "AbsState":
        """TD_Side_CFG.thy:25 — globals -> bot, locals kept."""
        b = self.dom.bot()
        return AbsState(self.dom, self.vars,
                        {x: (b if is_global(x) else self.m[x]) for x in self.vars})

    def restrict_global(self) -> "AbsState":
        """TD_Side_CFG.thy:29 — locals -> bot, globals kept."""
        b = self.dom.bot()
        return AbsState(self.dom, self.vars,
                        {x: (self.m[x] if is_global(x) else b) for x in self.vars})

    def show(self) -> str:
        return "{" + ", ".join(f"{x}:{self.dom.show(self.m[x])}" for x in self.vars) + "}"


def combine_abs(sc: AbsState, se: AbsState) -> AbsState:
    """Constraint_System.thy:273 — <sc|se>: globals from callee, locals from caller."""
    return AbsState(sc.dom, sc.vars,
                    {x: (se.m[x] if is_global(x) else sc.m[x]) for x in sc.vars})


def bot_state(dom, vars) -> AbsState:
    return AbsState.const(dom, vars, dom.bot())
