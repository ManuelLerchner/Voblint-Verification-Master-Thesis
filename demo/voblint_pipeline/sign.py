"""The Sign domain — mirrors src/Analysis/Instances/Sign/Sign_Domain.thy.

7-element lattice, gamma (concretisation), join = lattice LUB, and the abstract
arithmetic tables (plus/minus/times).  The forward transfer (SignTransfer) builds
assign/assume/assume_not/enter.

NOTE on assume: the real analyzer refines guards with the backward domain
(afilter/bfilter, Abstract_Domain.thy + Sign_Domain.thy).  Here assume/assume_not
are the identity — SOUND (an over-approximation) but imprecise.  Everything else
is faithful.  Swap in a bfilter to recover guard precision.
"""
from __future__ import annotations
from .state import AbsState, Domain
from . import imp_ast as A
from . import cfg as C

# sign elements (Sign_Domain.thy:26)
SBOT, SNEG, SNONPOS, SZERO, SNONNEG, SPOS, STOP = \
    "Bot", "Neg", "NonPos", "Zero", "NonNeg", "Pos", "Top"
ELEMENTS = [SBOT, SNEG, SNONPOS, SZERO, SNONNEG, SPOS, STOP]

GAMMA = {SBOT: "{}", SNEG: "{n<0}", SNONPOS: "{n<=0}", SZERO: "{0}",
         SNONNEG: "{n>=0}", SPOS: "{n>0}", STOP: "Z"}

# sign_le (Sign_Domain.thy:14) as the reflexive-transitive covering relation
_LE = {
    SBOT:    ELEMENTS,                        # bot below all
    SNEG:    [SNEG, SNONPOS, STOP],
    SNONPOS: [SNONPOS, STOP],
    SZERO:   [SZERO, SNONPOS, SNONNEG, STOP],
    SNONNEG: [SNONNEG, STOP],
    SPOS:    [SPOS, SNONNEG, STOP],
    STOP:    [STOP],
}
def sign_le(a, b) -> bool:  return b in _LE[a]


def join(a, b):
    """Least upper bound in the lattice (= sup_sign / join_sign, Sign_Domain.thy:97)."""
    ubs = [e for e in ELEMENTS if sign_le(a, e) and sign_le(b, e)]
    # the LUB is the unique upper bound that is below every other upper bound
    return next(e for e in ubs if all(sign_le(e, e2) for e2 in ubs))


def sign_of_int(n: int):
    return SNEG if n < 0 else (SZERO if n == 0 else SPOS)


# abstract arithmetic (Sign_Domain.thy:140/158/183) via sign envelopes of gamma
_REPS = {SNEG: [-1], SNONPOS: [-1, 0], SZERO: [0], SNONNEG: [0, 1],
         SPOS: [1], STOP: [-1, 0, 1]}

def _envelope(op, a, b):
    if a == SBOT or b == SBOT: return SBOT
    outs = {sign_of_int(op(i, j)) for i in _REPS[a] for j in _REPS[b]}
    acc = SBOT
    for s in outs: acc = join(acc, s)
    return acc

def plus(a, b):   return _envelope(lambda i, j: i + j, a, b)
def minus(a, b):  return _envelope(lambda i, j: i - j, a, b)
def times(a, b):  return _envelope(lambda i, j: i * j, a, b)


def aval_sign(a: A.Aexp, sigma: AbsState):
    """Sign_Domain.thy:219 — abstract evaluation of an expression."""
    if isinstance(a, A.N):     return sign_of_int(a.n)
    if isinstance(a, A.V):     return sigma[a.x]
    if isinstance(a, A.Plus):  return plus(aval_sign(a.a, sigma), aval_sign(a.b, sigma))
    if isinstance(a, A.Minus): return minus(aval_sign(a.a, sigma), aval_sign(a.b, sigma))
    if isinstance(a, A.Times): return times(aval_sign(a.a, sigma), aval_sign(a.b, sigma))
    raise TypeError(a)


class SignDomain:
    """Implements the Domain protocol for AbsState."""
    def bot(self):            return SBOT
    def top(self):            return STOP
    def join(self, x, y):     return join(x, y)
    def leq(self, x, y):      return sign_le(x, y)
    def gamma(self, x):       return GAMMA[x]
    def show(self, x):        return x


class SignTransfer:
    """The forward domain_transfer for sign (Sign_Domain.thy:609)."""
    def assign(self, x, a):   # assign_sign (Sign_Domain.thy:534)
        return lambda sigma: sigma.update(x, aval_sign(a, sigma))
    def assume(self, b):      # bfilter_sign b True  -- identity here (see module note)
        return lambda sigma: sigma
    def assume_not(self, b):  return lambda sigma: sigma
    def enter(self):          # enter_sign (Sign_Domain.thy:560): locals -> Top
        def f(sigma: AbsState):
            return AbsState(sigma.dom, sigma.vars,
                            {x: (sigma[x] if A.is_global(x) else STOP) for x in sigma.vars})
        return f

    def apply_tf(self, a: C.EA):
        """Constraint_System.thy:44 — dispatch edge_action to a state transformer."""
        if isinstance(a, C.EA_Nop):        return lambda s: s
        if isinstance(a, C.EA_Assign):     return self.assign(a.x, a.a)
        if isinstance(a, C.EA_Assume):     return self.assume(a.b)
        if isinstance(a, C.EA_AssumeNot):  return self.assume_not(a.b)
        if isinstance(a, C.EA_Enter):      return self.enter()
        raise TypeError(a)
