#import "../lib/math.typ": *
#import "../lib/code.typ": isaconst, isai, isalocale, isathm, isatype, listing
#import "../lib/theorems.typ": definition
#import "../lib/figures.typ": check-row

#let _join-a = check-row("pg-contexts-none-join", cond: "a == 6")

= Background <ch:background>

This chapter introduces the order-theoretic, semantic and Isabelle/HOL notions
that later chapters assume, each only as far as they use it. We use the counting loop of @fig:source-morph as the example throughout:

#listing(lang: "c", ```
i = 0; while (i < 5) { i = i + 1; }
```)

At the loop head, $i$ takes exactly the values $0, 1, dots, 5$.

== Lattices and fixpoints

An analysis needs to compare descriptions by precision and to name the
description a loop's equations determine. An ordered set $(lat(D), lle)$ orders descriptions by precision: $a lle b$
means that $a$ is at least as precise as $b$. For sets of concrete states the
order is inclusion. The least element $lbot$ describes no states, the top
$ltop$, when present, all states, and the join $a ljoin b$ is the least upper
bound of its operands. A complete lattice has a join $lJoin X$ and a meet
$lMeet X$ for every subset, and $f$ is monotone when $a lle b$ implies
$f(a) lle f(b)$ @nipkow14.

By the Knaster–Tarski theorem, a monotone $f$ on a complete lattice has a
least fixpoint $lfp f$, the meet of all $d$ with $f(d) lle d$ @tarski55.
Such a value is closed: another application of $f$ adds nothing
outside it, so it is an inductive invariant. The invariant need not be the
least. At the loop head, "$0 <= i <= 5$" and "$i >= 0$" are both closed under
entering the loop and running its body, but only the first is least. Kleene
iteration $lJoin_(n in NN) f^n(lbot)$ reaches $lfp f$ for functions that
preserve joins of increasing chains @cousot79tarski, and a monotone iteration
from bottom stabilizes on a finite-height order. Infinite domains need an
extrapolation operation (@sec:widening). Voblint requires less than a complete
lattice: the numeric interface of @ch:domains asks for a bounded join
semilattice, which has finite joins, a bottom and a top, together with a
monotone concretization, and the solver's certificate does not claim a least
fixpoint.

== Abstract interpretation

Correctness of an abstract result needs a meaning for abstract values. Let $C$ be a set of concrete states and $A$ an ordered abstract carrier. A
concretization $conc : A -> cal(P)(C)$ gives each abstract value its meaning.
Soundness of an abstract result $a$ for a collecting set $S$ means
$ S subset.eq conc(a), $
the consistency requirement between an abstract and a concrete interpretation
in @cousot77.
At the loop head the interval $[0, 5]$ for $i$ is sound, and so is $[0, 10]$.
It permits $i = 7$, which no execution produces. Soundness bounds the reachable
stores from above and says nothing about which permitted stores occur.

A Galois connection also gives a best abstraction
$abstr : cal(P)(C) -> A$ with $abstr(S) lle a equiv S subset.eq conc(a)$
@cousot79. Voblint uses only the inclusion and lets each domain supply its own
sound operations, as in the concretization-based mechanization of @nipkow14.
A best abstraction matters only for claims of optimal precision, and Voblint
makes none. The concretization of an integer domain is in general an infinite
set, so it serves only to state and prove soundness, and the executable part of
a domain does not mention it (@ch:domains).

For a concrete operation $f : C -> C$ and an abstract operation, or transfer
function, $sh(f) : A -> A$, the required local property is
$ s in conc(a) quad ==> quad f(s) in conc(sh(f)(a)). $
The loop body's increment has the interval transfer $[l, u] |-> [l + 1, u + 1]$,
which satisfies this property. A nondeterministic operation must include every
permitted successor. The property composes along paths, and at control-flow
joins the upper-bound laws of join and monotonicity of concretization keep the
states from both predecessors.

A collecting semantics associates a set of reachable stores with every program
point @cousot77, here the stores with $i in {0, dots, 5}$ at the loop head. Its abstract
counterpart associates an abstract state with that point.

Interprocedural analysis adds a second index. The running example of
@fig:program-to-equations calls `bump(n)`, which returns $n + 1$, once with
argument $5$ and once with $4$. A context-insensitive analysis keeps one
abstract state for the entry of `bump`, which must describe both calls. An
analysis that joins the two entry values has $n in [4, 5]$ there, and both
callers receive $[5, 6]$. The analyzer prints #box(raw(_join-a.state)) when it
merges the calls by join, and its default update rule loses more
(@sec:eq-coarse). A context-sensitive
analysis keeps one abstract state per program point and _calling context_, for
instance one context per argument value, and reports $n in [5, 5]$ and
$n in [4, 4]$ separately. Its soundness statement is then
indexed by the context too, and needs a concrete counterpart: the set of stores
at a point that belong to a given context. @ch:traces defines those
context-indexed sets.

The classical designs differ in what a context records @sharir81
@rival20[§8.4.1] @seidl12compiler[§§2.6, 2.9]. The call-string approach takes the call stack as context and
bounds it to the $k$ most recent call sites, since a recursive procedure
otherwise has infinitely many contexts. The functional approach computes a
procedure summary independent of callers, which each call site instantiates. In
Goblint, an analysis derives the context from the callee's abstract start
state, in full or through a projection @erhard25[Examples 2, 3], and a local
solver analyzes a procedure body only in the contexts that some call produces
@seidl12compiler[§2.8] @seidl21. Voblint offers the context-insensitive policy, bounded call strings
and entry-state contexts (@ch:equations). @sec:contexts explains why it admits
callee contexts through a relation rather than computing them by a function.

== Widening and narrowing <sec:widening>

Intervals have infinite ascending chains, such as
$ [0, 0] llt [0, 1] llt [0, 2] llt dots. $
A widening $a widen b$ extrapolates an update and bounds both operands; a
classical widening also stabilizes the corresponding iteration sequences
@cousot77. The two requirements are separate, since the upper-bound law gives
soundness but not termination. At the example's loop head, plain joins take five
increases, and a million with the bound $10^6$. The standard interval widening
replaces a growing bound by infinity @cousot77, so the first change, from
$[0, 0]$ to $[0, 1]$, gives $[0, infinity]$ at once. Entering the loop
restricts $i$ to $[0, 4]$, the body yields $[1, 5]$, and the head's right-hand
side evaluates to $[0, 0] ljoin [1, 5] = [0, 5]$, a bound narrowing can recover.

When $b lle a$, a narrowing satisfies the bracket laws @cousot77
$ b lle a narrow b lle a. $
For a closed value $a$ and the candidate $b = f(a)$, the lower bracket keeps
$f(a) lle a narrow f(a)$, and for monotone $f$ the narrowed value is closed
again: $f(a narrow f(a)) lle f(a) lle a narrow f(a)$. Warrowing narrows when the candidate lies below the
current value and widens otherwise @apinis13 @grass24, so each update bounds
the candidate. Its use in a solver still needs a proof about reads, side
effects and stabilization; Voblint reuses the verified solver of @tilscher26,
whose partial-correctness theorem needs no monotonicity (@sec:side-effects).

== Side-effecting constraint systems <sec:side-effects>

A solver receives the analysis as a system of constraints over unknowns. Let
$Unk$ be a set of unknowns and let $sol : Unk -> A$ assign abstract values.
For an ordinary constraint system, each unknown $x$ has a right-hand side
$rhs(x)$, and a post-solution satisfies
$ rhs(x)(sol) lle sol(x). $
The intraprocedural recipe takes one unknown per program point, whose
right-hand side joins the transfers of its incoming edges; interprocedural
analyses add contexts to the index. For the example's loop head $h$, with the interval of $i$ as
value,
$ rhs(h)(sol) = [0, 0] ljoin ((sol(h) lmeet [-infinity, 4]) + 1). $
Both $sol(h) = [0, 5]$ and $sol(h) = [0, infinity]$ satisfy the
post-solution inequality, and either bounds the collecting semantics, which is
why a certificate need not be least.

An analysis with one unknown per program point is _flow-sensitive_: its value
holds whenever execution is at that point. A _flow-insensitive_ fact, such as
one range for a global variable, holds throughout the run; mixed analyses
choose per aspect of the state @seidl26 (@sec:mixed-flow). Such a fact is an unknown without a
program point, and every point that changes it must contribute to it.
Side-effecting systems let a right-hand side make such contributions to other
unknowns during its evaluation @apinis12. A call site, for instance, publishes
the callee's entry value to a seed unknown that the callee's entry reads
(@sec:eq-seed). If evaluating the right-hand side for $x$ returns $d$ and emits
contributions $(y_i, d_i)$, the certificate must bound all of them:
$ d lle sol(x), quad d_i lle sol(y_i) " for every emitted contribution". $
The formal certificate, #isaconst("part_post_solution"), requires them only on
the part of the system the query depends on (@sec:certificate).

A _local_ solver produces such a partial certificate. With contexts as
indices a system can have infinitely many unknowns, of which only those
influencing the query matter @seidl21. Goblint's top-down solver is local: it
evaluates right-hand sides on demand from the query and applies warrowing at
the unknowns where a read closes a cycle (@fig:td-trace). Seidl and Vogler
prove that their variants with widening and narrowing, including the
side-effecting one, terminate on arbitrary, possibly non-monotone, systems as
long as only finitely many unknowns are encountered @seidl21[Thms. 5.1, 9.4].
The Isabelle formalization of the side-effecting solver @tilscher26 proves
partial correctness only: when a solve terminates, it returns a partial
post-solution. It contains no termination theorem for that solver, so
termination is a premise of the main theorem (@sec:termination). The proof architecture follows the split: the equation
generator shows that any suitable post-solution over-approximates the
semantics, and the solver shows that a terminating run provides one.

== Isabelle/HOL mechanisms

The following mechanisms of Isabelle/HOL @nipkow14 recur in later chapters. A _type class_ collects
operations and laws that an instance proves once for a carrier
@haftmann07, such as the numeric class #isalocale("sound_domain") of
@ch:domains; a type has at most one instance of each class. A _locale_ fixes
parameters and assumptions; interpreting it proves the assumptions for an
instance and yields its theorems @ballarin14. The coverage contract
#isalocale("ltr_coverage") is one, which separates the semantics from any
domain or solver. An _inductive definition_ is the least relation closed under
its rules and comes with rule induction; source execution and valid
activation-local traces are defined this way. A _quotient type_ identifies
representations up to an equivalence that lifted operations must respect
@huffman13. @ch:solving uses one to relate finite executable abstract states
to the function-valued abstract states of the soundness statements. _Code
equations_ determine what code generation emits @haftmann10, and
@ch:executable discusses the trust that remains. Theories are grouped into
_sessions_, which Isabelle builds and checks as units (@fig:appendix-sessions).

A _proof by evaluation_ does not follow the kernel discipline of @ch:intro.
The method `eval` compiles a closed proposition, such as "this solve returns
this table", to code, runs it, and accepts the outcome as a theorem through the
code generator's oracle, so the theorem trusts the code generator and the
runtime that executes the code. Such paths have failed before: in 2025,
normalization by evaluation, which also bypasses the kernel, admitted a proof
of `False`, fixed in the following release @paulson26broken. Several witnesses about fixed programs are
proved this way; the text marks them, and @tab:oracles-audit lists which
audited theorems depend on the oracle.

== Notation <sec:notation>

The thesis and the theories share one notation. We use $s$ for a concrete store.
The concretization #isaconst("gamma") of an abstract value is written $conc$,
and #isaconst("gamma_state") of a pointwise state $a$ is written $sem(a)$, both
as the theories write them. The order $lle$, join $ljoin$, bottom $lbot$ and top $ltop$ are
those of Isabelle/HOL's order and lattice classes, and $widen$ and $narrow$ are
the widening and narrowing of the solver's update rules. Program points are
written $v$, contexts $c$, and $sol$ denotes an equation-system valuation.
A superscript sharp marks the abstract counterpart of a concrete operation. The remaining
formal objects appear either under the notation their Isabelle declaration
gives them, such as #isai("\<lbrakk>e\<rbrakk>\<^sub>e s") for evaluating an expression and
#isai("\<G>, \<Pi> \<turnstile> cfg \<rightarrow>\<^sub>p cfg'") for a source step, or under their
Isabelle name applied to its arguments; @tab:notation lists the symbols.
