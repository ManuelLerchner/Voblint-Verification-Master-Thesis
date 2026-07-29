"""VIMP AST — mirrors src/VIMP/VIMP_Syntax.thy and src/VIMP/VIMP_Proc.thy.

Expressions (aexp/bexp) and commands (com). A variable is *global* iff its name
is empty or starts with 'G' (is_global, src/VIMP/VIMP_Globals.thy:24).
"""
from __future__ import annotations
from dataclasses import dataclass


def is_global(x: str) -> bool:
    """src/VIMP/VIMP_Globals.thy:24 — is_global x = (x = [] or hd x = 'G')."""
    return x == "" or x[0] == "G"


# ---- aexp (src/VIMP/VIMP_Syntax.thy:30) ---------------------------------------
class Aexp: ...
@dataclass(frozen=True)
class N(Aexp):      n: int              # literal
@dataclass(frozen=True)
class V(Aexp):      x: str              # variable
@dataclass(frozen=True)
class Plus(Aexp):   a: Aexp; b: Aexp
@dataclass(frozen=True)
class Minus(Aexp):  a: Aexp; b: Aexp
@dataclass(frozen=True)
class Times(Aexp):  a: Aexp; b: Aexp


# ---- bexp (src/VIMP/VIMP_Syntax.thy:44) — enough for the demo ------------------
class Bexp: ...
@dataclass(frozen=True)
class Less(Bexp):   a: Aexp; b: Aexp
@dataclass(frozen=True)
class Not(Bexp):    b: Bexp


# ---- com (src/VIMP/VIMP_Proc.thy:20) — intra core -----------------------------
class Com: ...
@dataclass(frozen=True)
class SKIP(Com): pass
@dataclass(frozen=True)
class Assign(Com):  x: str; a: Aexp
@dataclass(frozen=True)
class Seq(Com):     c1: Com; c2: Com
@dataclass(frozen=True)
class If(Com):      b: Bexp; c1: Com; c2: Com
@dataclass(frozen=True)
class While(Com):   b: Bexp; c: Com


def aexp_mentions_global(a: Aexp) -> bool:
    if isinstance(a, N):    return False
    if isinstance(a, V):    return is_global(a.x)
    if isinstance(a, (Plus, Minus, Times)):
        return aexp_mentions_global(a.a) or aexp_mentions_global(a.b)
    raise TypeError(a)


def bexp_mentions_global(b: Bexp) -> bool:
    if isinstance(b, Less): return aexp_mentions_global(b.a) or aexp_mentions_global(b.b)
    if isinstance(b, Not):  return bexp_mentions_global(b.b)
    raise TypeError(b)
