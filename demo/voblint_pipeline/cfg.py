"""CFG + AST->CFG compilation.

edge_action:            src/CFG/CFG_Def.thy:38
cfg (edges/combines):   src/CFG/CFG_Def.thy:61
compile:                src/CFG/IMP2_Proc_to_CFG.thy:19
predecessor_list:       src/CFG/CFG_Def.thy:147
combine_predecessor_list: src/CFG/CFG_Def.thy:260

Program points are nat (pp). compile Pi lay c n returns
(next_fresh, entry, exit, edges, combines).  Only the intra core (SKIP, Assign,
Seq, If, While) is modelled; Scope/Call add EA_Enter edges + combine triples.
"""
from __future__ import annotations
from dataclasses import dataclass, field
from .imp_ast import Com, SKIP, Assign, Seq, If, While, Bexp, Aexp


# ---- edge_action (src/CFG/CFG_Def.thy:38) -------------------------------------
class EA: ...
@dataclass(frozen=True)
class EA_Nop(EA): pass
@dataclass(frozen=True)
class EA_Assign(EA):    x: str; a: Aexp
@dataclass(frozen=True)
class EA_Assume(EA):    b: Bexp
@dataclass(frozen=True)
class EA_AssumeNot(EA): b: Bexp
@dataclass(frozen=True)
class EA_Enter(EA): pass


@dataclass
class Cfg:
    """src/CFG/CFG_Def.thy:61 — edges + combines + entry/exit."""
    entry: int
    exit: int
    edges: set          # (u:int, a:EA, w:int)
    combines: set       # (caller:int, callee_exit:int, return:int)

    def points(self) -> set[int]:
        pts = {self.entry, self.exit}
        for u, _, w in self.edges: pts |= {u, w}
        for c, e, r in self.combines: pts |= {c, e, r}
        return pts

    def predecessor_list(self, v: int):
        """src/CFG/CFG_Def.thy:147 — incoming (u, a) edges of v."""
        return [(u, a) for (u, a, w) in sorted(self.edges, key=str) if w == v]

    def combine_predecessor_list(self, v: int):
        """src/CFG/CFG_Def.thy:260 — (caller, callee_exit) of returns into v."""
        return [(c, e) for (c, e, r) in sorted(self.combines, key=str) if r == v]


def compile(c: Com, n: int):
    """src/CFG/IMP2_Proc_to_CFG.thy:19 — returns (next, entry, exit, edges, combines)."""
    if isinstance(c, SKIP):
        return (n + 2, n, n + 1, {(n, EA_Nop(), n + 1)}, set())

    if isinstance(c, Assign):
        return (n + 2, n, n + 1, {(n, EA_Assign(c.x, c.a), n + 1)}, set())

    if isinstance(c, Seq):
        n1, en1, ex1, E1, C1 = compile(c.c1, n)
        n2, en2, ex2, E2, C2 = compile(c.c2, n1)
        splice = set() if ex1 == en2 else {(ex1, EA_Nop(), en2)}
        return (n2, en1, ex2, E1 | splice | E2, C1 | C2)

    if isinstance(c, If):
        en = n
        n1, en1, ex1, E1, C1 = compile(c.c1, n + 1)
        n2, en2, ex2, E2, C2 = compile(c.c2, n1)
        xn = n2
        edges = ({(en, EA_Assume(c.b), en1), (en, EA_AssumeNot(c.b), en2)}
                 | E1 | E2 | {(ex1, EA_Nop(), xn), (ex2, EA_Nop(), xn)})
        return (n2 + 1, en, xn, edges, C1 | C2)

    if isinstance(c, While):
        head = n
        n1, en1, ex1, E1, C1 = compile(c.c, n + 1)
        xn = n1
        edges = ({(head, EA_Assume(c.b), en1), (head, EA_AssumeNot(c.b), xn)}
                 | E1 | {(ex1, EA_Nop(), head)})
        return (n1 + 1, head, xn, edges, C1)

    raise TypeError(f"compile: unsupported command {c}")


def compile_prog(c: Com) -> Cfg:
    _, en, ex, E, C = compile(c, 0)
    return Cfg(entry=en, exit=ex, edges=E, combines=C)
