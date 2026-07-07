"""Strategy trees and their three interpreters.

datatype strategy_tree : vendor/td-verification/Basics_side.thy:94
traverse_rhs           : Basics_side.thy:297   (the local answer)
sides_of_rhs           : Basics_side.thy:289   (the global writes)
dep_aux                : Basics_side.thy:101    (the read set / scheduling deps)

Unknowns are keyed Inl x (local, ('L', pp)) and Inr g (global, ('R', g)).
A solution `sigma` is a dict key -> AbsState.  Continuations (the `'d => tree`
argument of QueryL/QueryG) are plain Python callables, exactly as in HOL.
"""
from __future__ import annotations
from dataclasses import dataclass
from typing import Callable
from .state import AbsState


def L(x):  return ("L", x)   # Inl x
def R(g):  return ("R", g)   # Inr g


class Tree: ...
@dataclass
class Answer(Tree):  d: AbsState
@dataclass
class QueryL(Tree):  x: object; k: Callable[[AbsState], "Tree"]
@dataclass
class QueryG(Tree):  g: object; k: Callable[[AbsState], "Tree"]
@dataclass
class Side(Tree):    g: object; d: AbsState; t: "Tree"


def _read(sigma: dict, key, dom, vars) -> AbsState:
    v = sigma.get(key)
    return v if v is not None else AbsState.const(dom, vars, dom.bot())


def traverse_rhs(t: Tree, sigma: dict, dom, vars) -> AbsState:
    """Basics_side.thy:297 — walk queries, skip Side, return the Answer."""
    while True:
        if isinstance(t, Answer):  return t.d
        if isinstance(t, QueryL):  t = t.k(_read(sigma, L(t.x), dom, vars)); continue
        if isinstance(t, QueryG):  t = t.k(_read(sigma, R(t.g), dom, vars)); continue
        if isinstance(t, Side):    t = t.t; continue
        raise TypeError(t)


def sides_of_rhs(t: Tree, sigma: dict, dom, vars) -> dict:
    """Basics_side.thy:289 — bot everywhere except each Side g d accumulates d at R(g)."""
    if isinstance(t, Answer):  return {}
    if isinstance(t, QueryL):  return sides_of_rhs(t.k(_read(sigma, L(t.x), dom, vars)), sigma, dom, vars)
    if isinstance(t, QueryG):  return sides_of_rhs(t.k(_read(sigma, R(t.g), dom, vars)), sigma, dom, vars)
    if isinstance(t, Side):
        m = dict(sides_of_rhs(t.t, sigma, dom, vars))
        cur = m.get(R(t.g))
        m[R(t.g)] = t.d if cur is None else cur.join(t.d)
        return m
    raise TypeError(t)


def dep_aux(t: Tree, sigma: dict, dom, vars) -> set:
    """Basics_side.thy:101 — the set of unknowns the tree reads under sigma."""
    if isinstance(t, Answer):  return set()
    if isinstance(t, QueryL):  return {L(t.x)} | dep_aux(t.k(_read(sigma, L(t.x), dom, vars)), sigma, dom, vars)
    if isinstance(t, QueryG):  return {R(t.g)} | dep_aux(t.k(_read(sigma, R(t.g), dom, vars)), sigma, dom, vars)
    if isinstance(t, Side):    return dep_aux(t.t, sigma, dom, vars)
    raise TypeError(t)
