#import "../lib/math.typ": *
#import "../lib/code.typ": (
  isacmd, isaconst, isai, isalocale, isasession, isathm, isatype, listing, playground-link,
)
#import "../lib/theorems.typ": definition
#import "../lib/sources.typ": proved, thy
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
    lbl((1.45, 6.3), [$[0, +infinity]$])
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

@ch:intro described soundness informally: an analysis result must contain
every state that a real run reaches, and it may contain more. Such a result is
an _over-approximation_. To prove that Voblint computes one, we need precise
definitions of the runs, of the abstract states, and of how an analyzer
computes them from a system of constraints. We introduce them using one small
program, which we follow from its executions to the result of the solver.

== Executions and the collecting semantics <sec:collecting>


An analysis describes the states a program can be in at each of its points, so
we first make the points explicit. A _control-flow graph_ has the program
points as nodes and an edge for every way control can pass from one point to
the next, labeled with the assignment or condition executed on the way.
@fig:counting-loop shows the graph of a loop that counts `i` from $0$ to $5$,
our running example. The loop becomes a cycle through $h$, $b$, and $t$, and
its _loop head_ $h$ is the node through which control enters and exits the cycle.

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
    the point after the increment, and $e$ the point after the loop. Edges
    carry the assignment or the condition that leads from one point to the
    next. The edge from $t$ back to $h$ has no effect.],
) <fig:counting-loop>

The state of an execution is a _store_, which maps each variable to its
value, here the value of $i$. An execution starts at the entry of the graph in
an initial store and follows a path, updating the store at every edge. The
counting loop reaches $h$ once before the first iteration and again after each
run of the body, so $i$ takes exactly the values $0, 1, dots, 5$ there.
Collecting, for every program point, the stores of all executions that reach
it gives the _collecting semantics_ $cal(C)$ @cousot77[§4] @mine17[§3.4],
which maps every program point $v$ to the set $cal(C)(v)$ of stores reached
there. Here $cal(C)(h)$ holds the stores with $i in {0, dots, 5}$. For
programs with procedures, @ch:traces defines Voblint's version over execution
traces (#isaconst("node_collect")).

The collecting semantics is the exact answer an analysis approximates. An
analysis is _sound_ if, at every program point, its result describes every store
that the collecting semantics gives there. It may describe more stores,
which costs precision, but never fewer. Soundness thus relates three levels: the
individual executions, the collecting semantics that gathers the stores
they reach, and the abstract states that an analysis computes. @fig:intro-nest
refines these levels for Voblint.

== Lattices and fixpoints <sec:lattices>

At $h$, the intervals $[0, 5]$ and $[0, 10]$ both contain every value $i$ takes
there (the collecting semantics ${0, dots, 5}$), but $[0, 10]$ also admits
$i = 7$, which no execution reaches. A description is _more precise_ than
another if it admits fewer states. Ordered sets make this comparison formal.
In an ordered set $(lat(D), lle)$ (#isalocale("order")),
$a lle b$ means that $a$ is at least as precise as $b$ @nipkow14[Def. 10.23].
For sets of concrete states, the order is inclusion.

Two descriptions reaching a point along different paths must be combined into
one that covers both. Their _join_ $a ljoin b$ is the least upper bound, the
most precise element above both (#isalocale("semilattice_sup")). At the loop
head, the value before the loop and the value after the body are combined this
way. Dually, the _meet_ $a lmeet b$ is the greatest lower bound. An analysis
uses it at a branch to restrict the incoming value to the values the condition
admits. If the analysis knew only $[0, 10]$ at $h$, entering the body would
restrict it to $[0, 10] lmeet [-infinity, 4] = [0, 4]$. Soundness does not need this
refinement, since $[0, 10]$ itself is sound at $b$, but it makes the result
more precise, and Goblint and Voblint both refine at branches. The least
element $lbot$ lies below every element, and a top element $ltop$, if one
exists, lies above every element. In abstract interpretation, $lbot$ describes
no states and $ltop$ describes all of them. A _complete lattice_
(#isalocale("complete_lattice")) has a join $lJoin X$ and a meet $lMeet X$ for
every subset $X$ @nipkow14[Def. 13.1] @mine17[Def. 2.5].

Voblint's solver, however, requires only a join semilattice with a least
element (#isalocale("bounded_semilattice_sup_bot")) that carries the widening
and narrowing operators of @sec:widening, so joins need to exist only for
pairs. A numeric domain adds a top element. Refinement at a branch adds a
pairwise intersection that keeps every value both operands admit
(#isalocale("sound_intersection"), @sec:branches).

An analysis computes the description at a point from the descriptions at its
predecessors, by a function $f$ on $lat(D)$. The classical theory requires $f$
to be _monotone_ (#isaconst("mono")), so that $a lle b$ implies
$f(a) lle f(b)$ @nipkow14[Def. 10.26] @mine17[Def. 2.9] and more precise input
never yields less precise output. For a monotone $f$, the iterates $lbot,
f(lbot), f(f(lbot)), dots$ form an ascending chain. Each of them lies below
every fixpoint. The verified solver that Voblint reuses, however, does not assume
monotonicity.

A _fixpoint_ of $f$ is an element with $f(d) = d$, and a _post-fixpoint_ is an
element with $f(d) lle d$, so applying $f$ once more yields nothing above $d$. By the
Knaster–Tarski theorem, a monotone $f$ on a complete lattice has a least
fixpoint $lfp f$, the meet of all post-fixpoints @tarski55[Thm. 1]
(#isaconst("lfp"), #isathm("lfp_unfold")), so every post-fixpoint lies above
$lfp f$. For a monotone $f$ on a
finite-height order, the iteration from $lbot$ stabilizes after finitely many
steps
@seidl12compiler[§1.5], and an iterate that no longer changes is the least
fixpoint (#isathm("lfp_Kleene_iter")).

An analysis does not have to reach $lfp f$. Every post-fixpoint of an $f$ that
includes the initial states and approximates each step soundly already contains
the collecting semantics (@sec:abs-int).


== Abstract interpretation <sec:abs-int>

The correctness of an abstract result needs a meaning for its elements. Let $U$ be
a set of concrete objects, such as integers or stores (#isatype("store")),
and $A$ an _abstract
domain_, an ordered set of _domain elements_ whose underlying set is its
_carrier_. A domain element is an _abstract value_ when it describes the
values of one variable, such as an interval for one integer, and an _abstract
state_ when it describes stores. A concretization $conc : A -> cal(P)(U)$ gives
each domain element its meaning. It is monotone, so a less precise element
admits at least the same objects: $a lle b$ implies
$conc(a) subset.eq conc(b)$ (#isathm("gamma_mono")). Soundness at a program
point $v$ (@sec:collecting) then becomes an inclusion. If $a$ is the analysis
result at $v$, then
$ cal(C)(v) subset.eq conc(a), $
the consistency requirement between an abstract and a concrete interpretation
in @cousot77[§6] @mine17[Def. 2.11].

The running example uses the _interval domain_ @cousot77[§9.2] @mine17[§4.5].
Its elements are $lbot$ and the intervals $[l, u]$ with
$l in ZZ union {-infinity}$, $u in ZZ union {+infinity}$ and $l <= u$, and an
interval denotes the integers between its bounds:
$ conc([l, u]) = {n in ZZ | l <= n <= u}, quad conc(lbot) = emptyset. $
The order is inclusion of these sets, so $[l, u] lle [l', u']$ holds exactly
when $l' <= l$ and $u <= u'$. The join
$[l, u] ljoin [l', u'] = [min(l, l'), max(u, u')]$ is the smallest interval
containing both. An interval cannot have holes, so the join may contain values
that neither operand contains: $[0, 0] ljoin [5, 5] = [0, 5]$. The meet
intersects the bounds. This is the textbook domain. Voblint's representation
#isatype("ivl") admits every pair of bounds, so $lbot$ is one of several empty
pairs (@sec:domain-carrier-laws).

At the loop head, both $[0, 5]$ and $[0, 10]$ are sound (@fig:concretization),
as is every interval that contains $[0, 5]$. An analysis aims for a precise one,
because a more precise element admits fewer values and so decides more checks:
$[0, 5]$ proves `i <= 5` at the loop head, and $[0, 10]$ does not.

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
    row(4.5, [collecting semantics $cal(C)(h)$])
    for n in range(0, 6) { dot(n, 4.5, vb.accent) }
  }),
  placement: none,
  caption: [Concretization of intervals at the loop head. Both $[0, 5]$ and
    $[0, 10]$ contain the collecting semantics $cal(C)(h)$, and $[0, 10]$ also permits
    $i = 7$. The join of $[0, 0]$ and $[5, 5]$ adds the values in between.],
) <fig:concretization>

Much of abstract interpretation also assumes an abstraction function
$abstr : cal(P)(U) -> A$ that forms a _Galois connection_ with $conc$ and gives
every set of states a best abstraction @cousot79[§5.3], the most precise
domain element whose concretization contains the set. Not every useful domain
has such best abstractions, and Cousot and Cousot treat a Galois connection as
the ideal case that efficient representations do not always meet
@cousot92plilp[§5]. Voblint uses $conc$ alone, like the verified analyzers of
Jourdan et al. and of Nipkow @jourdan15[§2] @nipkow12[§5.2], since its
soundness theorem claims coverage and nothing about optimal precision. The
concretization exists only in the logic. Since its result is in general an
infinite set, it is never executed, and the analyzer itself is defined from
executable operations only,
so that it can be exported and run as a standalone program.

The analysis replaces each concrete operation by an abstract one, a _transfer
function_ $sh(f) : A -> A$, which must not lose any state that the concrete
operation can produce. In general, a program's steps form a relation $->$ on
$U$, and one state may have several successors, even infinitely many, for example, when the next value is read from user input. The _post-image_
$"post"(X) = setcomp(s', exists s in X. s -> s')$ collects the successors of
all states in $X$. The transfer function is sound if, for every $a$,
$ "post"(conc(a)) subset.eq conc(sh(f)(a)), $
so stepping from any state that $a$ describes leads to a state that
$sh(f)(a)$ describes @cousot77[§6] @mine17[Def. 2.15] @rival20[§4.2.2]. The
square of @fig:transfer-square thus commutes only up to inclusion. In the
counting loop, the edge from $b$ to $t$ executes `i = i + 1`. Over $ZZ$, the
interval transfer $[l, u] |-> [l + 1, u + 1]$ is sound for it, and applied to
$[0, 4]$ it yields $[1, 5]$, which contains every successor $i = 1, dots, 5$.
Soundness
composes along paths
@mine17[Thm. 2.6], and at control-flow joins the upper-bound laws of the join
keep the states from both predecessors (#isathm("gamma_sup_ub1"),
#isathm("gamma_sup_ub2")).

#figure(
  {
    set text(size: 9pt)
    diagram(
      spacing: (12mm, 10mm),
      node((0, 0), $a$, name: <a>),
      node((2, 0), $sh(f)(a)$, name: <fa>),
      node((0, 1), $conc(a)$, name: <ga>),
      node((1, 1), $"post"(conc(a))$, name: <pa>),
      node((2, 1), $conc(sh(f)(a))$, name: <gfa>),
      edge(<a>, <fa>, "-|>", $sh(f)$),
      edge(<a>, <ga>, "-|>", $conc$, label-side: right),
      edge(<fa>, <gfa>, "-|>", $conc$, label-side: left),
      edge(<ga>, <pa>, "-|>", $"post"$, label-side: right),
      node((1.5, 1), $subset.eq$),
    )
  },
  kind: image,
  caption: [Soundness of a transfer function $sh(f)$: the square commutes up to
    inclusion.],
) <fig:transfer-square>

Sound transfer functions make every post-fixpoint that contains the initial
states a sound result
@mine17[Thm. 2.8]. The standard argument uses one domain element that
describes the whole program. It works with _configurations_, each a program
point together with a store, so that one relation $->$ describes every step
of the program, each moving an execution along one edge. The constraint systems of
@sec:constraints then split this element into one abstract state per program
point. In the counting loop, a configuration is a pair
$(p, n)$ of a program point and the value of $i$, so
$U = {"start", h, b, t, e} times ZZ$. With the set $I$ of initial
configurations, the reachable configurations form the least fixpoint of
$ F(X) = I union "post"(X) $
@rival20[§4.1.1, Thm. 4.1]. A set with $F(X) subset.eq X$ contains the initial
configurations and the successors of all its elements, so no execution can
leave it, and $lfp F$ is the smallest such set. In the counting loop,
executions begin at the node `start`, with any value of $i$, so
$I = {("start", n) | n in ZZ}$. Iterating $F$ from $emptyset$ adds one step at
a time: $(h, 0)$, then $(b, 0)$, $(t, 1)$, $(h, 1)$, and so on, up to $(h, 5)$
and finally $(e, 5)$. The least fixpoint contains $(h, n)$ exactly for
$n in {0, dots, 5}$, which is $cal(C)(h)$, since $cal(C)$ groups the reachable
configurations by their program point.

Now take a domain element $a$ with $I subset.eq conc(a)$ and
$sh(f)(a) lle a$, for a sound $sh(f)$. Soundness of $sh(f)$ and monotonicity
of $conc$ give
$F(conc(a)) subset.eq I union conc(sh(f)(a)) subset.eq conc(a)$. So $conc(a)$
is a post-fixpoint of $F$ and, by Knaster–Tarski, contains $lfp F$, every
reachable configuration. Here $F$ works on sets of configurations and $sh(f)$ on
domain elements, and the soundness of $sh(f)$ relates the two through $conc$.

Voblint's proof uses the same principle on a set of execution traces defined
inductively as a least fixpoint, and proceeds by induction over its rules.
Analyzers such as Goblint keep one abstract state per program point
@rival20[§4.2.1] and state one inequality per point, whose solution plays the
role of $a$.

== Constraint systems <sec:constraints>

An analysis needs an abstract state at every program point, and the state at
one point depends on the states at its predecessors. The analysis therefore
states its result as a system of constraints. Each _unknown_ of the system
stands for the abstract state at one program point, and each constraint says
what the unknown must cover.

The counting loop has one variable, so an abstract state is an interval for
$i$. (With several variables, a _non-relational_ state maps each variable to
its own abstract value.) With one unknown per program point of
@fig:counting-loop, each unknown must cover what the edges entering its point
produce:
$
  h & gt.eq [0, 0] ljoin t, & quad b & gt.eq h lmeet [-infinity, 4], \
  t & gt.eq b sh(+) [1, 1], & quad e & gt.eq h lmeet [5, +infinity].
$
The assignment `i = 0` yields $[0, 0]$ at $h$, the condition `i < 5`
restricts the branch into the body, and its negation restricts the exit.
Substituting $b$ and $t$ into the first inequality gives one for the loop head,
$h gt.eq f(h)$, with
$ f(d) = [0, 0] ljoin ((d lmeet [-infinity, 4]) sh(+) [1, 1]), $
whose post-fixpoints appear in @fig:lattice-fixpoints. A solution assigns an
interval to every unknown such that all four inequalities hold, and
@fig:loop-solutions shows two. Both contain the collecting semantics
(${0, dots, 5}$ at $h$), and the second is less precise at $h$ and $e$, so a
solution need not be the least one.

In general, let $Unk$ be a set of unknowns and $sol : Unk -> A$ a
_valuation_, which assigns a domain element to every unknown. Valuations are
ordered pointwise: $sol lle sol'$ if $sol(x) lle sol'(x)$ for every unknown
$x$. Each unknown $x$ has a _right-hand side_ $rhs(x)$, a function of the
valuation, and $sol$ is a _post-solution_ if
$ rhs(x)(sol) lle sol(x) quad "for every unknown" x $
(#isaconst("post_solution")), what the constraint-system literature calls a
solution @saan26phd[§2.4.4]. For the loop head,
$rhs(h)(sol) = [0, 0] ljoin sol(t)$. A post-solution is a post-fixpoint of all
right-hand sides at once, so the argument of @sec:abs-int applies at every
program point, and a post-solution bounds the reachable states everywhere. We
use the term _constraint system_ for the general concept and the term _equation
system_ for the system that Voblint generates and the solver receives, although
soundness only
requires inequalities.

#subfigures(
  figure(
    _loop-cfg((
      h: ($[0, 5]$, $[0, +infinity]$),
      b: ($[0, 4]$, none),
      t: ($[1, 5]$, none),
      e: ($[5, 5]$, $[5, +infinity]$),
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
  align: auto,
  caption: [The counting loop's inequalities, solved by hand. (a) The least
    solution at each node of @fig:counting-loop and, in orange where it
    differs, a less precise solution. (b) Post-fixpoints of the loop-head
    constraint (schematic, shaded) and its least fixpoint $[0, 5]$.],
  label: <fig:loop-constraints>,
)

The formulation goes back to data-flow analysis, where Kildall computes one
value per node of a program graph by iteration @kildall73[§3].

Programs with procedures can be analyzed with one unknown per program point or
separately per calling context, which abstracts how an activation
(one execution from call to return) was reached @aho06[§7.2.1]. Sharir and Pnueli
distinguish call strings, which record recent call sites, from the functional approach,
which relates abstract entry and return states @sharir81. Context-sensitive constraint
systems use unknowns $[v, c]$ for program point $v$ and context $c$ @apinis12[§3].
For the calls `bump(5)` and `bump(4)` in @ch:intro, entry-argument contexts
distinguish return values $6$ and $5$, while a single unknown must cover both.

== Widening and narrowing <sec:widening>

An analysis should terminate in reasonable time, even on a program whose
executions do not terminate. With
joins alone, successive abstract iterates can mirror successive loop
iterations. At the example's loop head, joins take five increases after $[0,
  0]$. For `while (true) { i = i + 1; }`, the iteration over intervals with bounds
in $ZZ$ never stabilizes, because these intervals have infinite ascending chains
such as
$ [0, 0] llt [0, 1] llt [0, 2] llt dots. $


#subfigures(
  figure(
    _loop-lattice("wn", scale: 0.5cm, size: 7.5pt),
    caption: [widening, then narrowing],
  ),
  <fig:widening-phases>,
  figure(
    _loop-lattice("warrow", scale: 0.5cm, size: 7.5pt),
    caption: [warrowing $widen narrow$, one operator for both steps],
  ),
  <fig:widening-warrow>,
  columns: (1fr, 1fr),
  placement: auto,
  caption: [Extrapolation on the lattice of @fig:lattice-fixpoints. (a) Widening
    jumps from $[0, 0]$ to the post-fixpoint $[0, +infinity]$, and narrowing then
    recovers the least fixpoint $[0, 5]$. (b) Warrowing takes the same two
    steps with one operator, which widens while the candidate grows and
    narrows once it lies below the current value. Here both reach $[0, 5]$.],
  label: <fig:widening>,
)

A _widening_ $a widen b$ replaces the update from the old value $a$ to the new
value $b$ by a guess that lies above both, which keeps the result sound
(#isalocale("widening")). A classical widening is also chosen so that repeated
widening stabilizes after finitely many steps @cousot77[§9.1.3]
@cousot92plilp[§4], which the upper-bound law alone does not ensure. A common
strategy widens at loop heads. The standard interval widening replaces a
growing bound by $+infinity$ @cousot77[§9.2] @mine17[§4.5.2], so widening at
$h$ turns the first change there, from $[0, 0]$ to $[0, 1]$, into
$[0, +infinity]$ at once. Propagated through the loop, this value yields the
less precise solution of @fig:loop-solutions, which loses the bound $5$ of the
loop condition `i < 5`.

The branch into the body restricts $[0, +infinity]$ to $[0, 4]$, the body
yields $[1, 5]$, and evaluating the head again gives
$[0, 0] ljoin [1, 5] = [0, 5]$. A widened iteration only grows and would not
take this smaller value. A _narrowing_ lets it descend. Both steps
appear in @fig:widening-phases, and @fig:widening-warrow shows one update
operator that combines them, widening or narrowing depending on the candidate.


A narrowing $a narrow b$ combines the current value $a$ with a candidate
$b lle a$ and returns a value between the two @cousot77[§9.3.4]
@cousot92plilp[§4]:
$ b lle a narrow b lle a. $ These are the _bracket laws_ of the solver's class #isalocale("narrowing"). A classical
narrowing must also make repeated narrowing stabilize. The class omits this
law, since termination of the solver is not proved. In the counting loop, the
interval narrowing reaches $[0, 5]$, but in general, narrowing need not recover
the least fixpoint.

Soundness of the result does not depend on how the solver widens and narrows.
The verified TD solver applies both operators in a single update,
_warrowing_ (#isaconst("warrow")). It narrows when the candidate lies below
the current value and widens otherwise @apinis13 @apinis16[§3] @grass24, so
each update lies above the candidate
(#isathm("warrowing_properties", thy: "Warrowing")). An unknown whose value no
longer changes under this update therefore satisfies its inequality. The
solver's correctness theorem uses only this and holds whether or not the
right-hand sides are monotone (@sec:td). Monotonicity is thus needed for the
classical theory of least fixpoints, but not to certify that a returned
valuation is a post-solution. As long as the operators satisfy their laws, the
choice of widening and narrowing affects only precision and termination.

== Side-effecting constraint systems <sec:side-effects>

The analyses so far are _flow-sensitive_: they respect the order in which
statements execute and therefore compute a separate abstract state for every
program point. For some facts, one value for the whole program is enough. A
_flow-insensitive_ analysis ignores execution order and keeps one abstract
value for an aspect of the state across the program, for example, one range for
a global variable, and mixed analyses choose between the two per aspect
@seidl26.

A flow-insensitive fact needs an unknown of its own that belongs to no program
point, and every point that changes the fact has to feed its new value into
that unknown. An ordinary right-hand side for the unknown would have to list
all these points in advance, which is not always possible. In a
context-sensitive analysis, for example, an unknown that writes a global is a
pair of a program point and a calling context, and the contexts are discovered
only while the system is solved.

Side-effecting constraint systems avoid that list. Seidl, Vene, and Müller-Olm
introduced them for multithreaded programs @seidl03[§3], and Apinis et al. use
them for context-sensitive analysis @apinis12. While the right-hand side of
one unknown is evaluated, it may _publish_ a _contribution_ to another unknown
as a _side effect_. We follow the verified solver and let side effects target
only _global unknowns_ $Unk_G$, which have no right-hand side and receive only
contributions. From here on, $Unk$ denotes the _local_ unknowns, which keep
their right-hand sides, and a valuation $sol$ assigns values to both kinds. A
global unknown need not correspond to a global variable of the program. A
right-hand side then returns a pair @saan26phd[§2.4.5],
$rhs(x) : (Unk union Unk_G -> A) -> (Unk_G harpoon.rt A) times A$, of a
partial map $rho$ of the contributions it publishes, joined per global
unknown, and its own value $d$. If $rhs(x)(sol) = (rho, d)$, a post-solution
must bound both, $d lle sol(x)$ and $rho(g) lle sol(g)$ for every
$g in op("dom")(rho)$. If the assignments
`g = 5` and `g = 4` publish $[5, 5]$ and $[4, 4]$ to the unknown of a
flow-insensitive global `g`, that unknown must bound their join $[4, 5]$. This
describes what a right-hand side computes. The verified solver represents its
evaluation by a strategy tree (@sec:td), so that it discovers reads and side
effects while it solves.

With contexts as indices, a system can have infinitely many unknowns, of which
only those that influence the _query_, the unknown whose value is asked for,
matter. A _local_ solver therefore explores the system from the query and
solves only the unknowns that it meets @seidl21. Its result comes with a
_certificate_, the property #isaconst("part_post_solution", thy: "Basics_side"),
which requires the bounds above only on a set of unknowns that contains the
query and is closed under the local reads of its right-hand sides.

== The verified top-down solver <sec:td>

// The counting loop of fig:counting-loop, for the playground link below.
#let _counting-loop = "i = 0;\nwhile (i < 5) {\n  i = i + 1;\n}\n"

A straightforward implementation of Kleene iteration recomputes every unknown in
every round, although most values
no longer change. Practical solvers therefore update one unknown at a time. They
work in rounds or with a worklist of unknowns whose inequalities may be violated
@seidl12compiler[§§1.5, 1.12], in orders chosen for widening @bourdoncle93, or
locally, on demand from a query, as the solver RLD does @hofmann10. Voblint
reuses the verified local top-down solver (TD) of @stade24 @tilscher26.

TD starts from the query and evaluates right-hand sides on demand. When the
right-hand side of $x$ reads an unknown $y$, TD first solves $y$ and records
that $x$ depends on $y$. An unknown is _stable_ if it has been evaluated and no
unknown that it read has changed since then. When the value of $y$ changes
later, every unknown that read it is _destabilized_ and evaluated again. The
unknowns at which a read closes a cycle are the solver's _widening points_
@seidl21. TD detects them while it solves @apinis16[§4], so they need not
coincide with the loop heads of the control-flow graph. At a widening point, it
combines the old and the new value with warrowing. The
#link(playground-link(_counting-loop, trace: "verbose"))[playground] replays this run on the counting loop step by step. Contributions published to a
global unknown are merged into its value by an _update rule_
(#isalocale("update_rule")), which keeps one record per _origin_, the unknown whose right-hand side
published the contribution (@sec:update-rules). The run ends
once every unknown the query transitively reads is stable, and it returns this
_stable set_ $V$ together with the valuation $sol$.

To solve on demand, TD has to discover which unknowns a right-hand side reads,
so that it can solve each of them first. In the counting loop, the reads are
fixed, since the right-hand side of $h$ always reads $t$. In general, a
right-hand side may choose the next unknown from a value it has already read.
At a procedure call, for instance, the callee context to read is known only
once the caller's value has been read. The verified solver therefore receives
every right-hand side as a _strategy tree_
(#isatype("strategy_tree", thy: "Basics_side")), a small program that reads
one unknown at a time and makes every read and every side effect explicit:
$
  tau ::= ctor("Answer", thy: "Basics_side")(d) | ctor("QueryL")(y, k) | ctor("QueryG")(g, k)
  | ctor("Side")(g, d, tau)
$
with a local unknown $y in Unk$, a global unknown $g in Unk_G$, a domain
element $d in A$ and a continuation $k : A -> tau$ that receives the value
read. $ctor("Answer", thy: "Basics_side")(d)$ returns $d$ as the value of the
right-hand side, $ctor("QueryL")$ and $ctor("QueryG")$ read a local or a
global unknown, and $ctor("Side")(g, d, tau)$ publishes $d$ to $g$ before
continuing with $tau$. @fig:strategy-trees shows the trees of the counting
loop and of a flow-insensitive assignment.

#let _tree(steps) = {
  set text(size: 7.5pt)
  diagram(
    spacing: (4mm, 6mm),
    node-stroke: 0.6pt + vb.neutral,
    node-corner-radius: 2pt,
    node-inset: 3.5pt,
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
#let _ans(x) = $ctor("Answer", thy: "Basics_side")(#x)$
#figure(
  grid(
    columns: 5,
    column-gutter: 3mm,
    row-gutter: 3mm,
    align: center + top,
    $h$, $b$, $t$, $e$, [`g = 5` after $u$],
    _tree((($ctor("QueryL")(t)$, $v$), (_ans($[0, 0] ljoin v$), none))),
    _tree((($ctor("QueryL")(h)$, $v$), (_ans($v lmeet [-infinity, 4]$), none))),
    _tree((($ctor("QueryL")(b)$, $v$), (_ans($v sh(+) [1, 1]$), none))),
    _tree((($ctor("QueryL")(h)$, $v$), (_ans($v lmeet [5, +infinity]$), none))),
    _tree((
      ($ctor("QueryL")(u)$, $v$),
      ($ctor("Side")(g, [5, 5])$, none),
      (_ans($v$), none),
    )),
  ),
  kind: image,
  placement: none,
  caption: [Right-hand sides as strategy trees. The first four are the
    inequalities of the counting loop (@sec:constraints): each reads one
    unknown, passes its value $v$ on, and answers. The last publishes the
    value of a flow-insensitive global `g` (@sec:side-effects) before
    answering.],
) <fig:strategy-trees>

The solver's main theorem, #isathm("partial_post_solution"), establishes the
certificate #isaconst("part_post_solution", thy: "Basics_side") of
@sec:side-effects and states partial correctness. If the run terminates on the
query $x$ and returns its stable set
$V$ and the valuation $sol$, then $V$ contains $x$, is closed under the local
reads of its right-hand sides, and on $V$ the valuation is a post-solution,
published contributions included. The theorem needs no monotonicity of the
right-hand sides and says nothing about unknowns outside $V$. We call the set
on which this certificate holds the _solved set_. Termination of this solver is not proved, and @sec:isabelle explains how
Isabelle defines such a function.

== Isabelle/HOL mechanisms used in this development <sec:isabelle>

// The declarations below are examples, set smaller than the running text.
#show raw.where(block: true): set text(size: 6.5pt)

This section explains the mechanisms of Isabelle/HOL @nipkow14 needed to read
the definitions and theorems that later chapters show, each with the place
where the formalization uses it.

HOL is a typed logic of total functions. We write $x :: tau$ for "$x$ has type
$tau$", $tau_1 => tau_2$ for the type of functions from $tau_1$ to $tau_2$,
#isai("'a") for a type variable, and $lambda x. t$ for the function that maps
$x$ to $t$. A _datatype_ declares a type by its constructors and comes with
case distinction and structural induction. VIMP's commands
#isatype("gcom") are one (@sec:vimp). A _record_ is a tuple with named fields.
The analysis interface #isatype("dg_spec") is one (@sec:sound-core).

Every HOL function is total, so an ordinary recursive definition needs a
termination proof. Otherwise a definition such as $f(n) = f(n) + 1$ would yield $0 = 1$ @nipkow14[§2.3.4]. Isabelle's function package can also define a
recursive function without one. The result is still a total HOL constant, but
its defining equations are proved only on its _domain_, the arguments on which
the recursion terminates, and theorems about it assume membership in that
domain. The vendored solver is defined this way, with the domain
#isaconst("solve_dom", thy: "TD_side_upd_rule"). @sec:termination explains why Voblint's main
theorem nevertheless needs no termination premise.

A _type class_ collects operations and laws that an instance proves once for a
carrier @haftmann07. The solver's class #isalocale("widening") fixes the
operator $widen$ and assumes that it bounds both operands:
#thy("widening")
A type has at most one instance of each class. The numeric domains state
their algebra as classes (@ch:domains).

A _locale_ fixes parameters and assumptions, and interpreting it proves the
assumptions for an instance and yields its theorems @ballarin14. Unlike a
class, a locale can be interpreted several times for one type. Voblint states
its soundness obligations as locale assumptions, so an analysis becomes sound
by interpreting the locale. #isalocale("sound_intersection"), for instance,
fixes an intersection that keeps every value both operands admit and lies
below both:
#thy("sound_intersection")

An _inductive definition_ is the least relation closed under its rules, and
#isacmd("inductive_set") defines a set the same way. Its _rule induction_
proves a property of every element with one case per rule. The solver's
verification defines #isaconst("reach"), the unknowns on which a
query $x$ transitively depends, by two rules:
#thy("reach")
Source execution #isaconst("pstep") (@fig:pstep), graph execution
#isaconst("cstep") (@fig:cstep), the valid activation traces
#isaconst("valid_activation_trace") and the reflexive–transitive closure
$scripts(->)^*$ of a step relation are defined by rules as well, and a source
run is written $scripts(->)_p^*$ (#isaconst("psteps")).

A theorem declares its variables and their types after #isai("fixes"),
introduces abbreviations local to the statement after #isai("defines"), lists
its premises after #isai("assumes") and states its conclusion after
#isai("shows"). The source-level theorem of @sec:headline uses all four:
// deps: preview -- shown for its syntax; @sec:headline introduces what it uses.
#proved("run_voblint_source_sound")
It fixes a program $p :: #isatype("imp_prog")$ and two stores, abbreviates the
program's globals classifier, procedure table and graph, and assumes an initial
store, a source run $scripts(->)_p^*$ from it and an answer of the analyzer. It
shows that the reached configuration is observed at some graph node $v$
(written $gt.closed$, #isaconst("at_node"), @sec:csim), and that at every such
node the reached store lies in the collecting semantics, in the state the
report gives there, and in the stores its verdicts admit. Inside a proposition, $A ==> B$ is implication and $exists$,
$and$, $or$ are the usual connectives. Subscripts, superscripts, and symbols
such as $tack.r$ are notation for a constant applied to its arguments, and the
text names the constant at first use.

A _quotient type_ identifies representations up to an equivalence
@huffman13. The executable abstract states of @ch:solving are one: two finite
representations are identified when they read back to the same
function-valued state:
#thy("default_st")
Its operations are lifted with #isacmd("lift_definition").

_Code equations_ determine what code generation emits @haftmann10, and one
#isacmd("export_code") declaration emits the analyzer's OCaml from them, so
the delivered analyzer runs the definitions the theorems are about. The
generated code is _trusted_, not proved: no theorem states that the OCaml
program computes what the Isabelle definitions compute, so its correctness
rests on the code generator and the OCaml toolchain. The trust has a basis.
The generator translates code equations that are proved from the definitions,
apart from target-language adaptations such as the mapping of integers to
OCaml's arbitrary-precision numbers (#isacmd("code_printing")), which are
trusted. Haftmann and Nipkow give its source and intermediate language
a semantics and prove the translation of type classes correct on paper
@haftmann10, and the regression corpus runs the generated analyzer against
expected verdicts (@ch:executable). Theories are grouped
into _sessions_, which Isabelle builds and checks as units, and which later
chapters cite as the home of a construction. The control-flow graph, for
instance, lives in #isasession("Voblint_CFG"), which builds on
#isasession("Voblint_VIMP").

The _trusted computing base_ is the code that must be correct for a proof to
be believed, normally only Isabelle's inference kernel. A _proof by
evaluation_ extends it. The method `eval` compiles a closed proposition to code, runs it, and accepts
the result through the code generator's evaluation oracle. In 2025, a defect in
normalization by evaluation, which also extends trust beyond the kernel,
admitted a proof of `False` @paulson26broken. Theorems about fixed programs such as #isathm("nv_report") are proved this
way.
