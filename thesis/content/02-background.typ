#import "../lib/math.typ": *
#import "../lib/theorems.typ": theorem, definition
#import "@preview/glossarium:0.5.10": gls, glspl

= Background <ch:background>

== Lattices and fixpoints

Following @nipkow14, a complete lattice $(lat(D), lle)$ has all joins; we write $lbot$ and $ltop$
for the least and greatest elements, $ljoin$ and $lmeet$ for binary join and
meet, and $lJoin$ for the join of a set. A monotone $f : lat(D) -> lat(D)$ has
a least fixpoint $lfp f$.

#theorem(name: [Knaster--Tarski])[
  Let $(lat(D), lle)$ be a complete lattice and $f$ monotone. Then
  $ lfp f = lMeet setcomp(d in lat(D), f d lle d) . $
]

== Abstract interpretation

An abstraction --- #gls("ai") in the sense of Cousot --- relates a concrete
lattice to an abstract one. The
formalization fixes only the concretization $conc$, since soundness never
needs a best abstraction:

#definition(name: [Sound domain], isa: "sound_domain")[
  $sh(d)$ describes $s$ when $s in conc sh(d)$, and $conc$ is monotone:
  $sh(d_1) lle sh(d_2) ==> conc sh(d_1) subset.eq conc sh(d_2)$.
]

Widening $widen$ and narrowing $narrow$ enforce termination over lattices of
infinite height; @fig:widening shows both on a single loop head.

== Side-effecting constraint systems

TODO. Following @apinis12: the #gls("cfg") becomes a system of unknowns $Unk$, right-hand sides $rhs(x)$, the side-effect operation
$sidefx$, and $partpost$ as the certificate a solver must produce.
