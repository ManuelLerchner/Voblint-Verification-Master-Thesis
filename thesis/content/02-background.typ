#import "../lib/math.typ": *
#import "../lib/code.typ": isacmd, isaconst, isai, isalocale, isasession, isathm, isatype, listing
#import "../lib/theorems.typ": definition
#import "../lib/sources.typ": thy
#import "../lib/figures.typ": subfigures
#import "../lib/theme.typ": vb
#import "@preview/cetz:0.5.2"
#import "@preview/fletcher:0.5.8" as fletcher: diagram, edge, node


// The counting loop's control-flow graph. With `values`, a dictionary from
// node name to (least, widened) intervals, each node also shows its value in
// the least solution and, where it differs, after widening.
#let _loop-cfg(values) = {
  set text(size: 8.5pt)
  let body(name) = {
    let label = $#name$
    if values == none { label } else {
      let (least, wide) = values.at(name)
      stack(
        spacing: 2pt,
        [#label #h(3pt) #least],
        if wide != none { text(fill: vb.trusted, wide) },
      )
    }
  }
  let pt(pos, lbl, name) = node(
    pos,
    body(name),
    name: lbl,
    shape: if values == none { circle } else { rect },
    corner-radius: 2pt,
    stroke: 0.6pt + vb.neutral,
    inset: 3.5pt,
  )
  diagram(
    spacing: if values == none { (13mm, 6mm) } else { (20mm, 5mm) },
    node((0, 0), text(fill: vb.muted)[start], name: <s>, stroke: none),
    pt((0, 1), <h>, "h"),
    pt((0, 2), <b>, "b"),
    pt((0, 3), <t>, "t"),
    pt((1, 1), <e>, "e"),
    edge(<s>, <h>, "-|>", raw("i = 0"), label-side: right),
    edge(<h>, <b>, "-|>", raw("i < 5"), label-side: left),
    edge(<b>, <t>, "-|>", raw("i = i + 1"), label-side: left),
    edge(<t>, <h>, "-|>", bend: 60deg),
    edge(<h>, <e>, "-|>", raw("!(i < 5)"), label-side: left),
  )
}


// The loop-head lattice of the counting loop; the widening figure adds the
// extrapolation arrows once widening and narrowing are defined.
#let _loop-lattice(mode, scale: 0.68cm, size: 8.5pt) = cetz.canvas(length: scale, {
  let extrapolate = mode != "fix"
  // warrowing is one operator, so it gets one colour of its own
  let wcol = if mode == "warrow" { vb.cong } else { vb.trusted }
  let ncol = if mode == "warrow" { vb.cong } else { vb.par }
  import cetz.draw: *
  let lbl(pos, body, anchor: "west", fill: black) = content(
    pos,
    box(fill: white, inset: 1.2pt, text(size, fill: fill, body)),
    anchor: anchor,
  )
  let lfp-pt = (0, 3.2)
  let wide = (1.2, 6.2)
  // the lattice as a diamond, the post-fixpoints as the cone above lfp
  line((0, 0), (-4.5, 4), (0, 8), (4.5, 4), close: true, stroke: 0.6pt + vb.neutral)
  line(
    lfp-pt,
    (-2.7, 5.6),
    (0, 8),
    (2.7, 5.6),
    close: true,
    fill: vb.proved.lighten(85%),
    stroke: 0.5pt + vb.proved,
  )
  // widening jumps into the cone, narrowing comes back down
  if extrapolate {
    bezier(
      (0.12, 0.55),
      (1.15, 6.0),
      (3.6, 2.2),
      stroke: (
        paint: wcol,
        thickness: 0.8pt,
        dash: if mode == "warrow" { none } else { "dashed" },
      ),
      mark: (end: ">", fill: wcol),
    )
  }
  if extrapolate {
    bezier(
      (1.1, 6.0),
      (0.14, 3.32),
      (1.4, 4.0),
      stroke: (paint: ncol, thickness: 0.8pt),
      mark: (end: ">", fill: ncol),
    )
  }
  // Kleene iterates of the joining iteration
  for i in range(0, if mode == "fix" { 5 } else { 1 }) {
    circle((0, 0.5 + i * 0.6), radius: 0.07, fill: vb.accent, stroke: none)
  }
  circle(lfp-pt, radius: 0.12, fill: vb.proved, stroke: none)
  if extrapolate { circle(wide, radius: 0.1, fill: wcol, stroke: none) }
  lbl((-0.25, 0.5), [$[0, 0]$], anchor: "east")
  if mode == "fix" {
    lbl((-0.25, 1.7), [joins: $[0, 1], dots, [0, 4]$], anchor: "east", fill: vb.accent)
  }
  lbl((-0.3, 3.2), [least fixpoint $[0, 5]$], anchor: "east", fill: vb.proved)
  if extrapolate {
    lbl((1.45, 6.3), [$[0, infinity]$])
    if mode == "warrow" {
      lbl((2.3, 2.75), [warrowing $widen narrow$], fill: wcol)
    } else {
      lbl((2.3, 2.75), [widening $widen$], fill: vb.trusted)
      lbl((0.8, 4.7), [narrowing $narrow$], anchor: "east", fill: vb.par)
    }
  }
  lbl((-2.9, 6.4), [post-fixpoints \ $f(d) lle d$], anchor: "east", fill: vb.proved)
  content((0, -0.4), text(9.5pt)[$lbot$])
  content((0, 8.4), text(9.5pt)[$ltop$])
})


= Background <ch:background>

This chapter introduces the order-theoretic, semantic and Isabelle/HOL notions
that later chapters assume, each only as far as they use it. An analysis
computes, for every program point, a description of the states that can occur
there. Descriptions are ordered by precision, and the analysis is expressed as a
system of equations over them whose solutions are fixpoints or post-fixpoints
(@sec:lattices). Abstract interpretation gives each description a meaning, a
set of concrete states, and states soundness as inclusion in that set
(@sec:abs-int). A program's equations are read off its control-flow
graph (@sec:constraints), and widening is used to force convergence on domains
with infinite ascending chains (@sec:widening). Procedures add a second index,
the calling context, which @sec:contexts introduces. Goblint states an analysis as a
side-effecting constraint system (@sec:side-effects), which the verified
top-down solver solves (@sec:td). The last section introduces the Isabelle/HOL
mechanisms the formalization uses, and @tab:notation lists the notation the
thesis shares with the theories. We use the counting loop of
@fig:counting-loop as the intraprocedural example.

#figure(
  grid(
    columns: (48%, auto),
    column-gutter: 16mm,
    align: horizon,
    listing(lang: "c", ```
    i = 0;
    while (i < 5) {
      i = i + 1;
    }
    ```),
    _loop-cfg(none),
  ),
  kind: image,
  caption: [The counting loop and its control-flow graph (schematic). Nodes
    are program points: $h$ is the loop head, $b$ the start of the body, $t$
    the point after the increment and $e$ the point after the loop. Edges
    carry the assignment or the condition that leads from one point to the
    next.],
) <fig:counting-loop>

A _control-flow graph_ represents a program by its program points, the nodes,
and edges between them, each labelled with the assignment or condition executed
when control passes along it. @ch:program-model compiles VIMP programs to such
graphs. The _loop head_ $h$ in @fig:counting-loop is the program point at which
the condition `i < 5` is tested. An execution is a path through the graph from its entry. The
counting loop runs from `start` to $h$, around the cycle through $b$ and $t$
back to $h$ five times, and then to $e$. A loop thus becomes a cycle, and the
loop head is the node at which the cycle is entered and left. Execution reaches
$h$ once before the first iteration and again after each run of the body, and
$i$ takes exactly the values $0, 1, dots, 5$ there. An analysis attaches a
description to $h$ that must cover the states of every path reaching it
(@sec:side-effects discusses facts that do not depend on the node). The following sections compute that description.

== Lattices and fixpoints <sec:lattices>

An analysis needs to compare descriptions by precision and to name the
description a loop's equations determine. An ordered set $(lat(D), lle)$, Isabelle's
class #isalocale("order"), orders descriptions by precision: $a lle b$
means that $a$ is at least as precise as $b$. For sets of concrete states the
order is inclusion. The least element $lbot$ describes no states, the top
$ltop$, when present, all states, and the join $a ljoin b$ is the least upper
bound of its operands (#isalocale("semilattice_sup")). A complete lattice (#isalocale("complete_lattice")) has a join $lJoin X$ and a meet
$lMeet X$ for every subset, and $f$ is monotone (#isaconst("mono")) when $a lle b$ implies
$f(a) lle f(b)$ @nipkow14[Def. 13.1] @mine17[§2.1].

By the Knaster–Tarski theorem, a monotone $f$ on a complete lattice has a
least fixpoint $lfp f$, the meet of all $d$ with $f(d) lle d$ @tarski55[Thm. 1].
Isabelle defines #isaconst("lfp") as this meet and proves the fixpoint equation
$lfp f = f(lfp f)$ for monotone $f$ as #isathm("lfp_unfold").
Every $d$ with $f(d) lle d$ is closed: another application of $f$ adds nothing
outside it, so it is an inductive invariant @mine17[§4.7.7]. Such an invariant
need not be the least (@fig:loop-solutions). For functions
that preserve joins of increasing chains, the supremum of the Kleene iterates
$f^n(lbot)$ is $lfp f$ @mine17[Thm. 2.2]. On a finite-height order, monotone
iteration from bottom eventually stabilizes at that fixpoint
(#isathm("lfp_Kleene_iter"), @seidl12compiler[§1.5]). Infinite domains need an extrapolation operation
(@sec:widening). Voblint requires less than a complete
lattice: the numeric interface of @ch:domains asks for a bounded join
semilattice with a top (#isalocale("executable_domain"), over
#isalocale("bounded_semilattice_sup_bot")), together with a
monotone concretization (#isalocale("sound_domain"), @sec:abs-int). A solver need not compute the least fixpoint
either, and a widening-based solver need not return it (@sec:widening). @sec:abs-int shows why a post-fixpoint
suffices.


== Abstract interpretation <sec:abs-int>

Correctness of an abstract result needs a meaning for abstract values. Let $C$ be a set of concrete states and $A$ an
_abstract domain_, an ordered set of abstract values. Later chapters call the
underlying set of such a domain its _carrier_. A
concretization $conc : A -> cal(P)(C)$ gives each abstract value its meaning.
Soundness of an abstract result $a$ for a collecting set $R$ means
$ R subset.eq conc(a), $
the consistency requirement between an abstract and a concrete interpretation
in @cousot77[§6] @mine17[Def. 2.11].

The running example uses the _interval domain_ @cousot77[§9.2] @mine17[§4.5]. Its elements are
$lbot$ and the intervals $[l, u]$ with $l in ZZ union {-infinity}$,
$u in ZZ union {infinity}$ and $l <= u$, and an interval denotes the integers
between its bounds:
$ conc([l, u]) = {n in ZZ | l <= n <= u}, quad conc(lbot) = emptyset. $
The order is inclusion of these sets, so $[l, u] lle [l', u']$ holds exactly
when $l' <= l$ and $u <= u'$ (#isaconst("less_eq_ivl")). The join $[l, u] ljoin [l', u'] =
[min(l, l'), max(u, u')]$ (#isaconst("sup_ivl")) is the smallest interval containing both, and may
contain values neither operand does: $[0, 0] ljoin [5, 5] = [0, 5]$. The meet
intersects the bounds (#isaconst("meet_ivl")). Voblint's type #isatype("ivl")
keeps raw bound pairs: $lbot$ is #isaconst("bot_ivl") $= [infinity, -infinity]$,
other inverted pairs also denote $emptyset$, and order and join compare
bounds, which agrees with the description above on non-empty intervals. Its
concretization is #isaconst("gamma_ivl") (@ch:domains).

At the loop head both $[0, 5]$ and $[0, 10]$ are sound (@fig:concretization),
as is every interval that contains $[0, 5]$. An analysis aims for the most
precise of them, the one with the smallest concretization, because it admits
fewer values and so decides more checks: $[0, 5]$ proves `i <= 5` at the loop
head, and $[0, 10]$ does not. For the counting-loop equations of @sec:constraints
this is their least solution, which widening may miss (@sec:widening).

#figure(
  cetz.canvas(length: 0.62cm, {
    import cetz.draw: *
    let row(y, label) = content((-0.6, y), text(9pt, label), anchor: "east")
    let bar(y, a, b, color) = rect(
      (a - 0.3, y - 0.22),
      (b + 0.3, y + 0.22),
      fill: color.lighten(80%),
      stroke: 0.5pt + color,
      radius: 0.1,
    )
    let dot(x, y, color) = circle((x, y), radius: 0.13, fill: color, stroke: none)
    // number line
    line((-0.4, 0), (10.6, 0), stroke: 0.5pt + vb.neutral, mark: (end: ">"))
    for n in range(0, 11) {
      line((n, -0.1), (n, 0.1), stroke: 0.5pt + vb.neutral)
      content((n, -0.45), text(8pt, str(n)))
    }
    content((10.9, -0.45), text(9pt)[$i$])
    // join of two points adds the values between them
    row(1.2, [$conc([0, 0] ljoin [5, 5])$])
    bar(1.2, 0, 5, vb.muted)
    dot(0, 1.2, vb.neutral)
    dot(5, 1.2, vb.neutral)
    // a coarser sound value permits values no run has
    row(2.3, [$conc([0, 10])$])
    bar(2.3, 0, 10, vb.trusted)
    circle((7, 2.3), radius: 0.16, fill: white, stroke: 0.7pt + vb.unproved)
    content((7, 2.85), text(8pt, fill: vb.unproved)[permitted, never reached])
    row(3.4, [$conc([0, 5])$])
    bar(3.4, 0, 5, vb.proved)
    // the collecting semantics at the loop head
    row(4.5, [reachable values $R$])
    for n in range(0, 6) { dot(n, 4.5, vb.accent) }
  }),
  placement: auto,
  caption: [Concretization of intervals at the loop head. Both $[0, 5]$ and
    $[0, 10]$ contain the reachable values $R$, and $[0, 10]$ also permits
    $i = 7$. The join of $[0, 0]$ and $[5, 5]$ adds the values in between.],
) <fig:concretization>

A _Galois connection_ strengthens this correspondence with an abstraction
function $abstr : cal(P)(C) -> A$ such that
$abstr(S) lle a <==> S subset.eq conc(a)$ @cousot79[§5.3]. It maps every
concrete set to its best abstraction, and for a concrete set transformer
$F : cal(P)(C) -> cal(P)(C)$ the best abstract transformer is
$abstr compose F compose conc$ @cousot79[§7.2]. Cousot and Cousot call this the ideal situation and note that
efficient representations do not always meet it @cousot92plilp[§5]. Some
domains have no best abstraction at all. A disc has no smallest enclosing
convex polyhedron @mine17[Ex. 2.11]. For Coq, Jourdan et al. add a further reason: $abstr$ is not computable once the
concrete type is infinite, and a specification through $conc$ alone states
soundness conditions and removes the obligation to prove optimality
@jourdan15[§2]. Nipkow likewise drops $abstr$ and proves given abstract
interpreters correct @nipkow12[§5.2]. Voblint follows this style, as do the
concretization-based frameworks of @cousot92jlc[§7]: each domain supplies its
own operations and proves them sound against $conc$. Its soundness theorem
claims coverage and says nothing about optimal precision, so no proof needs a
best abstraction. The concretization of an integer domain is in general infinite, so
only the proofs use it (@ch:domains).

For a concrete operation $f : C -> C$ and an abstract operation, or transfer
function, $sh(f) : A -> A$, the required local property @cousot77[§6] @mine17[Def. 2.15] is
$ s in conc(a) quad ==> quad f(s) in conc(sh(f)(a)). $
Voblint states it once per kind of edge in #isalocale("sound_transfer_for"), for
instance for an assignment as #isathm("tf_sound_assign_for"). The loop body's
increment has the interval transfer $[l, u] |-> [l + 1, u + 1]$, the addition
#isaconst("plus_ivl") with $[1, 1]$, which satisfies this property. A nondeterministic operation must include every
permitted successor. The property composes along paths @mine17[Thm. 2.6], and at control-flow
joins the upper-bound laws of join and monotonicity of concretization
(#isathm("gamma_mono"), giving #isathm("gamma_sup_ub1") and #isathm("gamma_sup_ub2")) keep the states from both predecessors.

A post-fixpoint $a$ of a sound abstract transfer $sh(f)$ therefore suffices
@mine17[Thm. 2.8]. Let $F(X) = I union f(X)$ be the concrete transfer on sets of states, with
initial states $I$, so that $lfp F$ is the set of reachable states. If
$I subset.eq conc(a)$, $sh(f)$ is sound and $sh(f)(a) lle a$, then
$F(conc(a)) subset.eq I union conc(sh(f)(a)) subset.eq conc(a)$, so
$conc(a)$ is a post-fixpoint of $F$ and, by Knaster–Tarski, contains
$lfp F$. In the counting loop, $I$ is the $[0, 0]$ that `i = 0` contributes.

== Constraint systems <sec:constraints>

A collecting semantics associates a set of reachable stores, the concrete
states of VIMP, with every program point @cousot77[§4] @mine17[§3.4] (#isaconst("ltr_collect") in @ch:traces), here the stores with $i in {0, dots, 5}$ at the loop head, and its abstract
counterpart associates an abstract state. A non-relational abstract state maps each variable to an abstract value and concretizes to the
stores whose variables lie in the respective values.
An analysis states its result as a system of constraints over unknowns. An
intraprocedural analysis takes one unknown per program point, and
interprocedural systems commonly refine a program-point unknown by a calling
context, whose concrete meaning @sec:contexts gives. For the
counting loop, take one unknown per program point of @fig:counting-loop, valued
in intervals of $i$. Each unknown must cover what the edges entering its point
produce:
$
  h & gt.eq [0, 0] ljoin t, & quad b & gt.eq h lmeet [-infinity, 4], \
  t & gt.eq b sh(+) [1, 1], & quad e & gt.eq h lmeet [5, infinity].
$
The assignment `i = 0` contributes $[0, 0]$ to $h$, the condition `i < 5`
restricts the branch into the body, and its negation restricts the exit.
Substituting $b$ and $t$ into the first inequality gives one for the loop head,
$h gt.eq f(h)$ with
$ f(d) = [0, 0] ljoin ((d lmeet [-infinity, 4]) sh(+) [1, 1]), $
whose post-fixpoints @fig:lattice-fixpoints shows. A solution assigns an interval to
every unknown such that all four inequalities hold. @fig:loop-solutions shows
two. Both bound the collecting semantics, the widened one of @sec:widening less
precisely at $h$ and $e$, so a solution need not be least.

In general, let $Unk$ be a set of unknowns and $sol : Unk -> A$ a valuation.
Each unknown $x$ has a right-hand side $rhs(x)$, a function of the valuation,
and $sol$ is a _post-solution_ if
$ rhs(x)(sol) lle sol(x) quad "for every unknown" x. $
For the loop head, $rhs(h)(sol) = [0, 0] ljoin sol(t)$. The argument of
@sec:abs-int applies unknown by unknown, so a post-solution bounds the
reachable states at every program point at once. Such systems are often called
equation systems, although soundness only requires these inequalities. A
solver receives the analysis in this form, and the verified solver certifies a
partial post-solution, #isaconst("part_post_solution"), which holds on the
unknowns it has solved (@sec:td).

#subfigures(
  figure(
    _loop-cfg((
      h: ($[0, 5]$, $[0, infinity]$),
      b: ($[0, 4]$, none),
      t: ($[1, 5]$, none),
      e: ($[5, 5]$, $[5, infinity]$),
    )),
    caption: [two solutions on the graph],
  ),
  <fig:loop-solutions>,
  figure(
    _loop-lattice("fix", scale: 0.44cm, size: 7pt),
    caption: [post-fixpoints of $h gt.eq f(h)$],
  ),
  <fig:lattice-fixpoints>,
  columns: (1fr, 1fr),
  align: bottom,
  caption: [The counting loop's inequalities, solved by hand. (a) The least
    solution at each node of @fig:counting-loop and, in orange, the values
    widening reaches (@sec:widening). (b) Post-fixpoints of the loop-head
    constraint (schematic, shaded) and its least fixpoint $[0, 5]$.],
  label: <fig:loop-constraints>,
)


== Widening and narrowing <sec:widening>

An analysis should terminate quickly, whether or not the analyzed program
does. With joins
alone, successive abstract iterates can mirror successive loop iterations. At the example's loop head, joins take five increases after $[0, 0]$, a loop bound
of $10^6$ takes a million, and for `while (true) { i = i + 1; }` the iteration
never stabilizes, because intervals have infinite ascending chains such as
$ [0, 0] llt [0, 1] llt [0, 2] llt dots. $
A procedure that calls itself with $n + 1$ lets the value at its entry grow in
the same way. A widening $a widen b$ extrapolates an update and bounds both operands
(#isalocale("widening"), with laws #isathm("widen_ge1") and #isathm("widen_ge2")). A
classical widening also stabilizes the corresponding iteration sequences
@cousot77[§9.1.3] @cousot92plilp[§4]. The upper-bound law alone gives
soundness and does not ensure termination. A common strategy widens at selected loop heads, and
TD extrapolates where a read closes a cycle (@sec:td). The standard interval
widening replaces a growing bound by infinity @cousot77[§9.2] @mine17[§4.5.2] (#isaconst("widen_ivl_core")),
so widening at $h$ turns the first change there, from $[0, 0]$ to $[0, 1]$, into
$[0, infinity]$ at once. This value is a post-fixpoint without the bound $5$,
which the program states in the loop condition `i < 5`. The branch into the body refines the head's value against the
condition, a backward step from the guard to the stores that pass it
(#isalocale("backward_domain")), and restricts $[0, infinity]$ to $[0, 4]$ (#isaconst("inv_less_ivl")).
The body yields $[1, 5]$, and evaluating the head again gives
$[0, 0] ljoin [1, 5] = [0, 5]$ (@fig:widening).

#subfigures(
  figure(
    _loop-lattice("wn", scale: 0.5cm, size: 7.5pt),
    caption: [widening, then narrowing],
  ),
  <fig:widening-phases>,
  figure(
    _loop-lattice("warrow", scale: 0.5cm, size: 7.5pt),
    caption: [warrowing $widen narrow$ in one update],
  ),
  <fig:widening-warrow>,
  columns: (1fr, 1fr),
  placement: auto,
  caption: [Extrapolation on the lattice of @fig:lattice-fixpoints. (a) Widening
    jumps from $[0, 0]$ to the post-fixpoint $[0, infinity]$, and narrowing then
    recovers the least fixpoint $[0, 5]$. (b) Warrowing applies one operator
    that widens or narrows depending on whether the candidate lies below the
    current value. Here both reach $[0, 5]$.],
  label: <fig:widening>,
)

Narrowing lets the iteration take this smaller value. When $b lle a$, a
narrowing satisfies the bracket laws @cousot77[§9.3.4] @cousot92plilp[§4]
$ b lle a narrow b lle a, $
which the solver's class #isalocale("narrowing") states as #isathm("narrow_ge")
and #isathm("narrow_le").
For a closed value $a$ and the candidate $b = f(a)$, the lower bracket keeps
$f(a) lle a narrow f(a)$, and for monotone $f$ the narrowed value is closed
again: $f(a narrow f(a)) lle f(a) lle a narrow f(a)$. Being closed, the
narrowed value stays above the least fixpoint. In the counting loop the interval narrowing
(#isaconst("narrow_ivl_td")) reaches $[0, 5]$, but
in general narrowing need not recover the least fixpoint. Narrowing needs this monotonicity @seidl12compiler[§1.10]. Right-hand sides
that contain a widening are not monotone, because the interval widening itself
is not @cousot92plilp[Ex. 11]. The verified TD solver
applies both operators through one update, warrowing. Warrowing (#isaconst("warrow")) narrows when the candidate lies
below the current value and widens otherwise @apinis13 @grass24, so each update
bounds the candidate (#isathm("warrowing_properties")). The solver does not rely
on the narrowing argument above: its result is a post-solution because every
returned unknown is stable (@sec:td).

The strategies need not agree for arbitrary iteration schemes. Tilscher et al.
prove them equivalent for TD without side effects under precise widening and
monotonic right-hand sides and dependencies @tilscher26jar. The system below
satisfies these assumptions, but the solver of @fig:solver-sketch runs one
global widening phase and lies outside that theorem. On the system
$
  x gt.eq [0, 0] ljoin (y lmeet [-infinity, 5]), quad
  y gt.eq (x lmeet [-infinity, 9]) ljoin ((y lmeet [-infinity, 5]) sh(+) [2, 2]),
$
solved round robin with extrapolation at both unknowns, they differ. Widening until nothing changes and then narrowing yields
the least solution $x = [0, 5]$, $y = [0, 7]$. Warrowing narrows $y$ to
$[0, 9]$ while $x$ is still $[0, infinity]$. Once $x$ settles at $[0, 5]$,
the candidate for $y$ is $[0, 7]$, but interval narrowing only refines infinite
bounds, so $y$ stays at $[0, 9]$. On other systems warrowing is the more precise one, because narrowing one
unknown early can give another a smaller candidate before its infinite bound
is replaced. For $x gt.eq (y lmeet [-infinity, 10]) sh(+) [2, 2]$ and
$y gt.eq [0, 0] ljoin ((y lmeet [0, 7]) sh(+) [2, 2])$, the phased run gives
$x = [2, 12]$ and warrowing the least $x = [2, 11]$.

// The listing is long, so it may continue on the next page.
#show figure.where(kind: raw): set block(breakable: true)
#figure(
  {
    // The file keeps PEP 8's double blank lines; the listing drops them.
    show raw: set text(size: 5.8pt)
    raw(read("/shared/code/solver_sketch.py").replace("\n\n\n", "\n"), lang: "python", block: true)
  },
  kind: raw,
  caption: [An unverified round-robin solver over intervals, run with widening and
    then narrowing, and with warrowing, on the two-unknown system of
    @sec:widening.],
) <fig:solver-sketch>

== Side-effecting constraint systems <sec:side-effects>

An analysis with one unknown per program point is _flow-sensitive_: its value
holds whenever execution is at that point. A _flow-insensitive_ analysis associates one abstract
value with an aspect of the state independently of the current program point,
for example one range for a global variable across the program. Mixed analyses
choose per aspect of the state @seidl26 (@sec:mixed-flow). Such a fact is an unknown without a
program point, and every point that changes it must contribute to it.
Side-effecting systems let a right-hand side make such contributions to other
unknowns during its evaluation @apinis12. A call site, for instance, publishes
the callee's entry value to a seed unknown (#isaconst("Activation_Seed")) that
the callee's entry reads (@sec:eq-seed). If evaluating the right-hand side for $x$ returns $d$ and emits
contributions $(y_i, d_i)$, a post-solution must bound all of them:
$ d lle sol(x), quad d_i lle sol(y_i) " for every emitted contribution". $
In the running example of @fig:program-to-equations, without contexts, the
call nodes of `bump(5)` and `bump(4)` emit $n in [5, 5]$ and $n in [4, 4]$ to
`bump`'s seed, which must then bound their join $n in [4, 5]$.
The _certificate_ property established for the solver's result,
#isaconst("part_post_solution"), requires them only on
the part of the system the query depends on (@sec:certificate).

A _local_ solver produces such a partial certificate. With contexts as
indices a system can have infinitely many unknowns, of which only those
influencing the query matter @seidl21. Seidl and Vogler prove on paper that their
top-down variants with widening and narrowing, including the side-effecting
one, terminate on arbitrary, possibly non-monotone, systems as long as only
finitely many unknowns are encountered @seidl21[Thms. 1 and 5].

== The verified top-down solver <sec:td>

Kleene iteration is one way to compute a solution. Solvers iterate unknown by
unknown instead: in rounds or with a worklist of unknowns whose inequalities
may be violated @seidl12compiler[§§1.5, 1.12], in chaotic orders chosen for
widening @bourdoncle93, or locally, on demand from a query, as the solver RLD
@hofmann10 does. Voblint reuses the verified local top-down solver (TD) of
@stade24 @tilscher26.

TD starts from a query unknown and evaluates right-hand sides on demand. When
the right-hand side of $x$ reads an unknown $y$, TD first solves $y$ and
records that $x$ depends on $y$. When the value of $y$ changes later, every
unknown that read it is marked unstable (destabilized) and evaluated again. At unknowns where
a read closes a cycle, TD combines the old and the new value with warrowing
instead of replacing it (@fig:td-trace). Side contributions to a global are
merged into its value by an update rule (#isalocale("update_rule"),
@sec:update-rules). The run ends once the
discovered dependency closure of the query is stable, and it returns the set $S$ of stable unknowns together
with the valuation $sol$.

The formalization splits the unknowns into _local_ unknowns $Unk$, which have a
right-hand side, and _globals_ $G$, which receive only side contributions. Later chapters call
them _shared keys_. The term does not mean the program's globals, although
@sec:mixed-flow stores those at one shared key. A
right-hand side is a _strategy tree_ (#isatype("strategy_tree")), which
exposes every read and every side effect to the solver:
$
  tau ::= ctor("Answer")(d) | ctor("QueryL")(y, k) | ctor("QueryG")(g, k)
  | ctor("Side")(g, d, tau)
$
with a local unknown $y in Unk$, a global $g in G$, an abstract value $d in A$
and a continuation $k : A -> tau$ that receives the value read. $ctor("Answer")(d)$
returns $d$ as the value of the right-hand side, $ctor("QueryL")$ and
$ctor("QueryG")$ read a local or a global unknown, and $ctor("Side")(g, d, tau)$
contributes $d$ to $g$ before continuing with $tau$. Evaluating $tau$ against $sol$ follows the queries and
yields a value $italic("eval")(tau, sol)$ (#isaconst("traverse_rhs")), the set $italic("dep")(tau, sol)$ of local unknowns it
reads, and the join $italic("side")(tau, sol)$ of its side contributions per global
(#isaconst("sides_of_rhs")). @fig:strategy-trees shows two
right-hand sides in both forms.

#let _tree(steps) = {
  set text(size: 8pt)
  diagram(
    spacing: (6mm, 7mm),
    node-stroke: 0.6pt + vb.neutral,
    node-corner-radius: 2pt,
    node-inset: 4pt,
    ..steps.enumerate().map(((i, s)) => node((0, i), s.at(0))),
    ..range(steps.len() - 1).map(i => edge(
      (0, i),
      (0, i + 1),
      "-|>",
      steps.at(i).at(1),
      label-side: left,
    )),
  )
}
#subfigures(
  figure(
    grid(
      rows: (auto, auto),
      row-gutter: 5mm,
      align: center,
      $rhs(h)(sol) = [0, 0] ljoin sol(t)$,
      _tree((
        ($ctor("QueryL")(t)$, $v$),
        ($ctor("Answer")([0, 0] ljoin v)$, none),
      )),
    ),
    caption: [the loop head $h$],
  ),
  <fig:tree-loop>,
  figure(
    grid(
      rows: (auto, auto),
      row-gutter: 5mm,
      align: center,
      [publish $n in [5, 5]$ to the seed of `bump`, \ then answer the caller's state $q$],
      _tree((
        ($ctor("Side")(italic("Seed")(italic("bump")), n in [5, 5])$, none),
        ($ctor("Answer")(q)$, none),
      )),
    ),
    caption: [the call `bump(5)`, simplified],
  ),
  <fig:tree-call>,
  columns: (1fr, 1fr),
  align: bottom,
  caption: [Right-hand sides and their strategy trees. Each query names the
    unknown it reads and passes the value on, and $ctor("Side")$ records a
    contribution to a global. @sec:eq-call gives the full tree of a call, which
    also reads the caller's state and the callee's result, answers their
    combination and selects the callee's context.],
  label: <fig:strategy-trees>,
)

The solver is defined as mutually recursive functions without a termination
proof. Isabelle's function package then supplies a domain predicate $D$,
which holds exactly for the query unknowns on which the
recursion terminates. The main theorem, #isathm("partial_post_solution"),
states partial correctness for a system with right-hand sides $rhs(u)$,
$u in Unk$:
$
  D(x) and italic("solve")(x) = (S, sol) ==> x in S and forall u in S. \
  italic("dep")(rhs(u), sol) subset.eq S and
  italic("eval")(rhs(u), sol) lle sol(u) and italic("side")(rhs(u), sol) lle sol
$
Together with $x in S$, the three conditions for all $u in S$ are
#isaconst("part_post_solution"), the last compared pointwise over the
globals. $S$, the _key set_, contains
the query and is closed under the local reads of its right-hand sides, and on $S$
the valuation is a post-solution in the sense above, side contributions
included. The theorem needs no monotonicity of the right-hand sides and says
nothing about unknowns outside $S$. The executable solver #isaconst("solve_c")
returns an optional result and is proved equivalent to the solver on the
domain predicate (#isathm("term_equivalence")), and Voblint's corollary
#isathm("solve_dom_of_solve_c") concludes that a run that returns a result
satisfies the domain predicate. The Isabelle
formalization contains no general machine-checked termination theorem for the
side-effecting solver, so termination remains a premise of Voblint's main
theorem (#isaconst("config_terminates"), @sec:termination).

Voblint instantiates the solver's locale #isalocale("TD_side_upd_rule") with
its own equation system. The soundness proof meets the solver at
#isaconst("part_post_solution"): the equation generator shows that any
valuation satisfying it over-approximates the semantics, and the solver
theorem shows that a terminating run provides one (@sec:certificate).

== Isabelle/HOL mechanisms

// The declarations below are examples, set smaller than the running text.
#show raw.where(block: true): set text(size: 6.5pt)

The formalization uses a few mechanisms of Isabelle/HOL @nipkow14 that recur in
later chapters.

A _type class_ collects operations and laws that an instance proves once for a
carrier @haftmann07. The solver's class #isalocale("widening") fixes the
operator $widen$ and assumes that it bounds both operands:
#thy("widening")
A type has at most one instance of each class.

A _locale_ fixes parameters and assumptions, and interpreting it proves the
assumptions for an instance and yields its theorems @ballarin14. Unlike a
class, a locale can be interpreted several times for one type.
#isalocale("semantic_intersection") fixes an intersection operator and assumes
that it keeps every value both operands admit:
#thy("semantic_intersection")

An _inductive definition_ is the least relation closed under its rules and
comes with rule induction. Execution on the control-flow graph,
#isaconst("cstep"), has one rule per kind of step:
#thy("cstep")
Source execution #isaconst("pstep") is defined the same way, and
#isacmd("inductive_set") defines a set by rules, such as the valid
activation-local traces #isaconst("valid_ltr").

A _quotient type_ identifies representations up to an equivalence
@huffman13. @ch:solving identifies finite executable abstract states that read
back to the same function-valued state:
#thy("resolved_st_q")
Its operations are lifted with #isacmd("lift_definition").

_Code equations_ determine what code generation emits @haftmann10, and one
#isacmd("export_code") declaration emits the analyzer's OCaml from them.
@ch:executable discusses the trust that remains. Theories are grouped into
_sessions_, which Isabelle builds and checks as units, and a session imports
others as a whole. The control-flow graph lives in #isasession("Voblint_CFG"),
which builds on #isasession("Voblint_VIMP") (@fig:appendix-sessions).

A _proof by evaluation_ extends the trusted computing base beyond Isabelle's
inference kernel. The method `eval` compiles a closed proposition to code, runs it, and accepts the computed
result through the code generator's
evaluation oracle, which the theorem then trusts along with the runtime. In 2025, a defect in
normalization by evaluation, which also extends trust beyond the kernel,
admitted a proof of `False` @paulson26broken. Several witnesses about fixed programs are
proved this way, such as #isathm("nv_solve_c"),
and @tab:oracles-audit lists those among the audited theorems.
