#import "@preview/fletcher:0.5.8": diagram, edge, node
#import "../lib/theme.typ": vb
#import "../lib/code.typ": isaconst, isai, isalocale, isathm, isatype, listing, oblig
#import "../lib/math.typ": *
#import "../lib/theorems.typ": definition, theorem
#import "../lib/sources.typ": proved, thy
#import "../lib/figures.typ": (
  call-edge, dep-edge, entry-node, global-unk, intra-edge, ppoint, side-edge, unk,
)

= What an Analysis Supplies <ch:analysis-interface>

@ch:traces reduced soundness to five obligations over sets of stores, and
@ch:domains supplied finite descriptions of such sets. An analysis connects
the two, but only part of an abstract interpreter is specific to it. Some parts
are the same for every analysis: the control-flow graph, the equations built
from it, the calling contexts and the solver. Others are what makes Sign differ
from Interval: what an assignment does to a description, what a guard reveals
about the current state, and what a call passes to its callee. Goblint keeps
the two apart @seidl26[§5], and so does Voblint. An analysis is a plug-in that answers the
questions the program constructs pose, and the framework does the rest. The
soundness proof follows the same split: the framework's part is proved once,
in the chapters that follow, and a new analysis only shows that each of its
operations covers the corresponding concrete behaviour.

This chapter describes the plug-in: which questions it answers and what it has
to prove. The simplest plug-in would be one function per ordinary edge, from
the description before the edge to the one after it. Three things in the
program semantics need more. Some facts, such as one flow-insensitive range for
a global variable, belong to no single program point, and an analysis must be
able to read and extend them from exactly the edges that use them (@sec:dg). A call
cannot be handled as an ordinary edge transfer: after it returns, the caller's
own variables are the ones from before the call, and only the globals and the
result come from the callee, so the return must see both sides (@sec:calls).
Finally, a call may be split into cases that enter the callee separately, and
each case must remember the caller state it came from (@sec:calls).

The plug-in follows Goblint's analysis specification, with one method for each
operation of the record in @fig:dg-spec. The correspondence is one of structure only.
What each operation means comes from the VIMP and CFG semantics of
@ch:program-model, and Goblint's OCaml code plays no part in it. @ch:equations
turns the plug-in's guarantees into the five obligations of @ch:traces.

== Edge transfers and analysis globals <sec:dg>

An ordinary edge of the control-flow graph carries an action: an assignment, a
guard or its negation, a library call, the entry into a procedure body, a
return statement, a check, or no effect. @ch:program-model gives each action
$a$ its concrete meaning #isaconst("edge_step"): for a store $s$,
#isai("edge_step a s") is the set of stores the edge can produce. An
assignment yields one updated store, `nondet` one store per possible value, and
a guard yields $s$ itself, or no store when $s$ falsifies it.

An analysis describes the stores that reach a program point by an abstract
value $d$, whose concretization $conc_(D)(d)$ is the set of stores it describes
(@ch:domains). For each action $a$ it supplies an _abstract transfer_
$sh(f)_a$, which maps the value before the edge to the value after it. The
transfer is sound if it loses no successor: every $s in conc_(D)(d)$ and every
$s' in$ #isai("edge_step a s") satisfy $s' in conc_(D)(sh(f)_a (d))$. For a
transfer that uses only the local value, this is the obligation
#oblig("INTRA") of @ch:traces, stated for one edge. A transfer that also reads
and publishes analysis globals, introduced below, owes the same with the value
of the analysis global added on both sides (@sec:sound-core). The kinds of
action give an analysis seven edge transfers, named after the methods of
Goblint's `Spec` with the same role: skip, assign, special, branch, body,
return and event. They become the first fields of the record #isatype("dg_spec")
(@sec:sound-core).

=== Analysis globals <sec:analysis-globals>

Not every fact belongs to one program point. Seidl et al. describe the
specification of a mixed flow-sensitive analysis in Goblint @seidl26[§6]. It
consists of a local domain $D_L$ of facts tracked per program point and
context, a set of _analysis globals_ with a domain $D_G$ of their values,
transfer functions for the basic statements, and `enter` and `combine` for
calls. An analysis global is an unknown of its own, without a program point.
If the range of a global variable `g` is analyzed flow-insensitively, an
assignment to `g` contributes its value to the unknown of `g` as a side effect
(@sec:side-effects), and an edge that reads `g` depends on that unknown.
Goblint's
#link(
  "https://github.com/goblint/analyzer/blob/5320a6b741e50dc049f7a1b85e1709e9565cc54a/src/framework/analyses.ml#L168",
)[`Spec`]
accordingly declares a local
lattice `D` and a global lattice `G`. The word _global_ thus has two meanings. A _program global_ is a variable of
the VIMP program, like a global variable in C. An analysis global is an unknown
of the solver without a program point. The two are independent: an analysis
may track a program global flow-sensitively in its local value, and an analysis
global need not stand for any program variable. The numeric analyses of this
thesis track program globals in the local value, as Goblint's base analysis
does for single-threaded programs, and need no analysis global.

=== Side-effecting transfers and the manager <sec:manager>

A transfer of a mixed flow-sensitive analysis still returns the next local
value, but it may also read analysis globals and contribute new values to them:
it is _side-effecting_. In Goblint, a transfer does this through a
#link("https://github.com/goblint/analyzer/blob/5320a6b741e50dc049f7a1b85e1709e9565cc54a/src/framework/analyses.ml#L142")[_manager_]: an argument that gives it the current local value
and operations to read an analysis global and to contribute to one, among
others. For example, `man.sideg g d` contributes `d` to the analysis global
`g`, and the framework collects such contributions and passes them to the
solver @seidl26[§6]. Voblint adopts this design with the manager's local value,
reads, contributions and queries. Its transfer receives a manager instead of a
local value, and returns a program that computes the next local value and may
read and contribute to analysis globals on the way:
#{
  show raw.where(block: true): set text(size: 6.5pt)
  thy("man_transfer")
}
The manager is a record of type #isatype("man"):
#{
  show raw.where(block: true): set text(size: 6.5pt)
  thy("man")
}
Here `'dl` and `'dg` are the local and the global lattice, $D_L$ and $D_G$, `'v` names the
analysis globals, and `'x` and `'k` name the solver's local and global unknowns. #isaconst("man_local") is the current local value. The program is a
#isatype("strategy_program"), which compiles to a strategy tree
(@sec:side-effects). The record fixes only the types of the fields. The
framework hands every transfer the manager #isaconst("mk_dg_man") builds, in
which #isaconst("man_global") $v$ reads the global $v$ and compiles to a
#ctor("QueryG"), #isaconst("man_sideg") $v$ $g$ publishes $g$ to it and
compiles to a #ctor("Side"), and #isaconst("man_ask") poses a query to
the other analyses, which answer it through their query handlers (@ch:cooperation). The manager thus separates what an analysis asks for from how the solver tracks it. Soundness constrains what the program returns and publishes, not the order or
number of the reads and publications that produce them. The constraint is
#oblig("INTRA") for the compiled program, which @sec:sound-core states
precisely: every successor of a store covered by the source value and the
current value of the analysis global must be covered by the value the program
answers together with the value it publishes. A program that loses a successor,
answers too little or publishes too little cannot discharge it, so no soundness
theorem exists for its analysis. The solver's certificate then bounds each
analysis global by every contribution to it (@sec:certificate), and the solved
values inherit the coverage.

Dependencies therefore follow what a transfer actually does. The right-hand
side of an edge depends on an analysis global only if its transfer reads it, so
when a write enlarges the global, the solver re-evaluates exactly those
right-hand sides (@fig:shared-deps, @sec:eq-seed). A transfer that neither
reads nor contributes to an analysis global compiles to an equation that reads
only the value at the edge's source and publishes nothing
(#isathm("sp_compile_transfer_program_local_transfer")). The numeric analyses
are of this kind, so for them the manager changes nothing about the equations.

// A straight-line procedure with a flow-insensitive global: which right-hand
// sides read (grey) and publish to (double tip) its analysis global, and which
// nodes the solver re-evaluates when it grows (orange).
#figure(
  {
    set text(size: 8pt)
    let pt(i) = if i in (2, 3) {
      unk((0, i), $u_#i$, state: "unstable", name: label("u" + str(i)))
    } else { ppoint((0, i), $u_#i$, name: label("u" + str(i))) }
    diagram(
      spacing: (12mm, 10mm),
      ..range(4).map(pt),
      global-unk((1.6, 2), $kappa$, name: <k>),
      ..range(4).map(i => node((-0.75, i), text(fill: vb.muted, $(d_#i, bot)$))),
      node((2.2, 2), text(fill: vb.muted, $(bot, v)$)),
      intra-edge(<u0>, <u1>, label: "x = x + 1", label-side: right),
      intra-edge(<u1>, <u2>, label: "g = g + 1", label-side: right),
      intra-edge(<u2>, <u3>, label: "y = g", label-side: right),
      dep-edge(<k>, <u2>, bend: 18deg),
      dep-edge(<k>, <u3>, bend: 18deg),
      side-edge(<u2>, <k>, bend: 18deg),
    )
  },
  kind: image,
  placement: none,
  caption: [The right-hand sides that depend on the analysis global $kappa$ that tracks `g` flow-insensitively (schematic). Grey arrows are reads
    (#ctor("QueryG")), the purple double-tipped arrow is a side effect
    (#ctor("Side")). When `g = g + 1` enlarges $kappa$, the solver re-evaluates
    the nodes whose right-hand side reads it (orange). The edge `g = g + 1` both reads $kappa$, for the old
    value of `g`, and publishes the new one. The edge `x = x + 1`
    does not use `g`, so $u_1$ does not depend on $kappa$. Each unknown holds a
    #isatype("dg_state") (grey): a node its local value $d_i$ in the local half,
    $kappa$ the range $v$ of `g` in the global half.],
) <fig:shared-deps>

=== Global unknowns in the solver <sec:global-unknowns>

In the solver, an analysis global is a _global unknown_: an unknown without a right-hand side, which only receives side contributions (@sec:side-effects).
Analysis globals are not the only global unknowns. The framework adds its own, as
Goblint's does with #link("https://github.com/goblint/analyzer/blob/5320a6b741e50dc049f7a1b85e1709e9565cc54a/src/framework/analyses.ml#L55")[one global unknown per function] for the contexts it
is called in. The global unknowns of Voblint are named by the datatype
#isatype("global_unknown"): #isaconst("Analysis_Global") wraps the name of an
analysis global, and #isaconst("Activation_Seed") is a callee-entry seed. A
seed carries a local value and stands in for Goblint's side effect into the
callee's entry unknown, since the vendored solver allows side effects only to global unknowns (@sec:eq-seed).

The vendored solver requires all unknowns to share one value type, whereas
local unknowns and analysis globals range over different domains. Every unknown
therefore holds a pair #isatype("dg_state") of a local and a global component,
#isaconst("dg_local") and #isaconst("dg_global") (@fig:shared-deps). A local unknown
or a seed uses the local half, an analysis global the global half, and the
unused half is $lbot$. Transfers never see the pair: #isaconst("man_local") and
#isaconst("man_global") hand them the half they need. Goblint's solvers also
need one value type and use a #link("https://github.com/goblint/analyzer/blob/5320a6b741e50dc049f7a1b85e1709e9565cc54a/src/constraint/translators.ml#L30")[lifted sum] of the two lattices
instead. Voblint deviates here on purpose. A sum needs an extra top element where a
local and a global value meet, and every proof that reads an unknown would have
to handle it. With the pair, all lattice operations work componentwise, so the
solver's requirements on the value type follow from those on the two halves.

A transfer also refers to its analysis globals only by name. The solver keeps each of them in a global unknown, next to the framework's own global unknowns such as the callee-entry seeds. The manager maps each name to its global unknown, so a transfer that goes through the manager never touches a global unknown of the framework.

== The call boundary <sec:calls>

Voblint handles a call as Goblint does, with an entry and a return. Entry
computes the value with which the callee starts, the solver analyzes the callee
from it, and the return combines the callee's exit value with the caller's
value. The concrete semantics fixes what the return has to describe: after the
call, the caller continues with its own locals, the callee's globals and the
result (#isaconst("combine_collect") in #oblig("RETURN")). In this program the
continuation takes `x` from the caller and `g` and `y` from the callee
(@fig:return-stores):

#listing(lang: "c", ```
global g;
fun inc(a) { g = g + a; return a - 1; }
fun main() { g = 1; x = 5; y = inc(x); }
```)

// The call `y = inc(x)` on the control-flow graph, as the playground draws it,
// with the store at each of the four nodes around the call. The continuation
// takes `x` from the caller (blue) and `g` and the result from the callee (green).
#let _st(pos, body, name: none) = node(
  pos,
  align(left, text(size: 7pt, body)),
  stroke: none,
  name: name,
)
#let _from-s(body) = text(fill: vb.accent, body)
#let _from-t(body) = text(fill: vb.proved, body)
#figure(
  {
    set text(size: 8pt)
    diagram(
      spacing: (6mm, 9mm),
      ppoint((1, 0), `pp5`, name: <c-pp5>),
      ppoint((1, 2), `pp6`, name: <c-pp6>),
      entry-node((4, 0), [entry `inc`], name: <c-ent>),
      entry-node((4, 2), [exit `inc`], name: <c-ex>),
      _st((0, 0), [caller $s$: \ #_from-s[`x = 5`], `g = 1`]),
      _st((0, 2), [continuation: \ #_from-s[`x = 5`], #_from-t[`g = 6`], #_from-t[`y = 4`]]),
      _st((5, 0), [entry: \ `g = 1`, `a = 5`]),
      _st((5, 2), [exit $t$: \ #_from-t[`g = 6`], `a = 5`, \ #_from-t[result $4$]]),
      intra-edge(<c-pp5>, <c-pp6>, label: "continuation", label-side: right),
      intra-edge(<c-ent>, <c-ex>, label: "g := g + a; return a - 1", label-side: left),
      call-edge(<c-pp5>, <c-ent>, label: "call inc(x)", label-side: left),
      call-edge(<c-ex>, <c-pp6>, label: "resume", label-side: right),
    )
  },
  kind: image,
  placement: auto,
  caption: [The call `y = inc(x)` on the control-flow graph of the program
    above, with the store at the four nodes around it (schematic: the body of
    `inc` is drawn as one edge). Entry keeps the globals and binds the formal
    `a` (#isaconst("enter_state")). The continuation takes the caller's locals
    from $s$ (blue) and the globals and the result from the callee's exit $t$
    (green, #isaconst("combine_collect")).],
) <fig:return-stores>

The abstract return therefore receives two values, the caller's value and the
callee's exit value, like the abstract `combine` of the functional approach
@seidl12compiler[§2.6]. As in Goblint, it has two stages:
#isaconst("dgs_combine_env") merges the two environments, and
#isaconst("dgs_combine_assign") writes the result into the destination,
starting from the local value the first stage produced. Only their composition
carries an obligation, so a specification may do the whole return in either
stage (@sec:whole-state).

At a call, entry decides two abstract values, elements of the local domain
$D_L$ that describe sets of stores: the value $e$ with which the callee starts,
and the _resume value_ $q$ from which the caller continues after the call (the
theories call $q$ the continuation). Usually $q$ is the caller's own abstract
value at the call, but an analysis may weaken it there, for example by
forgetting facts the callee may invalidate. Entry answers a list of such pairs
$(q, e)$, as Goblint's `enter` does. For each pair, the framework selects a
callee context for $e$, reads the callee's result in that context, and combines
it with the $q$ of the same pair. The whole-state analyses of @sec:whole-state
answer a single pair. Several pairs split a call into cases, say by the sign of
an argument, each analyzed in its own callee context
(#isathm("ov_two_contexts") runs Sign with two overlapping alternatives). The
list makes the context semantics of @sec:contexts a relation.

=== Paired entry coverage

The entry obligation asks for one pair that covers the caller and the callee
together.

#definition(name: [Paired entry coverage], isa: "entry_pairs_cover", cmd: "definition")[
  Under a concretization `gammaD`, a list of pairs covers the caller store and
  the entered store if one pair covers both:
  #{
    show raw.where(block: true): set text(size: 6.5pt)
    thy("entry_pairs_cover")
  }
]

The covering pair's entry selects a callee context covering the real
activation, and its resume value covers the real caller, which is the
correlation #oblig("RETURN") needs (@sec:contract). The quantifier is
existential because the alternatives form a disjunction: each pair covers the
runs it was computed for.

The pairing matters. Results are combined only with the resume value of their
own pair, so covering the caller in one pair and the entered store in another
is not enough (@fig:unpaired-cover).

#figure(
  {
    set text(size: 8.5pt)
    set par(first-line-indent: 0pt, justify: false)
    let hit(body) = box(
      inset: (x: 4pt, y: 2.5pt),
      radius: 2pt,
      stroke: 0.8pt + vb.proved,
      fill: vb.proved.lighten(88%),
      [#body #h(2pt) #text(fill: vb.proved, size: 7.5pt)[covers the run]],
    )
    let miss(body) = box(inset: (x: 4pt, y: 2.5pt), radius: 2pt, stroke: 0.6pt + vb.frame, body)
    let to = text(fill: vb.muted)[#sym.arrow.r]
    let bad(body) = box(
      inset: (x: 4pt, y: 2.5pt),
      radius: 2pt,
      stroke: 0.8pt + vb.unproved,
      fill: vb.unproved.lighten(90%),
      body,
    )
    let head(body) = text(size: 7.5pt, fill: vb.muted, body)
    grid(
      columns: (auto, auto, auto, auto, auto, auto, auto, auto, auto),
      column-gutter: 7pt,
      row-gutter: 8pt,
      align: (right + horizon,) + (center + horizon,) * 8,
      [],
      head[resume value $q$],
      head[entry $e$],
      [],
      head[context],
      [],
      head[callee result],
      [],
      head[contribution],

      head[pair 1], hit($x > 0$), miss($a < 0$), to, [$a < 0$], to, [$a < 0$], to, bad($y < 0$),
      head[pair 2], miss($bot$), hit($a > 0$), to, [$a > 0$], to, [$a > 0$], to, $bot$,
    )
    v(4pt)
    align(center)[
      the run: $x = 1$ at the call, $a = 1$ at the entry, $y = 1$ after the
      return #h(1em) the claim: $y < 0$ #h(0.3em) #text(fill: vb.unproved)[misses
        the run]
    ]
  },
  kind: image,
  caption: [The unpaired condition is too weak. For `y = p(x)` with
    `fun p(a) { return a; }`, $x = 1$ and contexts separating the sign of the
    entry, pair 1's resume value covers the caller store and pair 2's entry
    covers the entered store. Each callee result is combined with its own
    pair's resume value, and the joined claim $y < 0$ excludes the run's
    $y = 1$. The figure is a hand calculation. The theorem below proves the
    failure in a set-level model that combines each pair's entry set with its
    own resume set directly.],
) <fig:unpaired-cover>

#theorem(name: [Entry coverage must be paired], isa: "unpaired_entry_cover_unsound")[
  Take `y = p(x)` with `p(a)` returning `a`, the caller store $x = 1$ and its
  entered store $a = 1$. Represent abstract values by sets of stores. The
  answer $[(x > 0, a < 0), (emptyset, a > 0)]$ covers the caller store with its
  first pair and the entered store with its second, but no pair covers both.
  Every store obtained by combining a pair's callee result with that pair's
  resume value has $y < 0$, whereas the run ends with $y = 1$.
]

#{
  show raw.where(block: true): set text(size: 6.5pt)
  proved("unpaired_entry_cover_unsound")
}

== The analysis soundness contract <sec:sound-core>

An analysis bundles its operations into one record, #isatype("dg_spec"),
with one field per operation (@fig:dg-spec). The seven edge transfers of
@sec:dg have type #isatype("man_transfer"). The entry of @sec:calls answers a
list of pairs, and the two return stages also receive the callee's exit value.
The query handler is the subject of @ch:cooperation. Every field has the role of
the Goblint method it is named after, except the event transfer: Goblint
handles its check function in `special`.

#figure(
  {
    show raw.where(block: true): set text(size: 6.5pt)
    thy("dg_spec")
  },
  kind: image,
  placement: bottom,
  caption: [The declaration of #isatype("dg_spec"), lifted from the theory.
    Each field carries, marked $sharp$, the name of the method of Goblint's
    `Spec` with the same role.],
) <fig:dg-spec>

@ch:equations proves the coverage obligations once, so it needs from each
analysis a fixed set of facts that mention neither contexts nor the solver. The
locale #isalocale("analysis_contract"), the _analysis soundness contract_,
states what a specification owes a concretization $conc_(D G)(d, g)$ of a local value and the value of the analysis global. Two of its assumptions are structural. The concretization
is monotone in both arguments, which turns the solver's order inequalities into
set inclusions as $conc$ does for a domain (@ch:domains). Every transfer is well
formed in the sense of #isaconst("dg_spec_wf"): it runs its continuation
exactly once, so what a compiled transfer publishes is well defined.

The other two concern what each edge's right-hand side returns and publishes,
since the solver's certificate bounds exactly these (@ch:solving):
#oblig("INTRA") for each edge transfer and #oblig("RETURN") for the composed
combine, the latter at arbitrary values, since a pair's resume value is held by
no unknown. Both read and check the global component at one slot, because the
locale fixes the type of analysis global names to `unit`. It therefore covers
analyses with a single global, which includes every analysis in the
development; a second global would need a concretization over a global
environment. Entry is absent: its soundness depends on which alternative the
routed equations select, and @sec:eq-routing states it as paired coverage.

The contract asks the carriers only for a
bounded join semilattice and $conc_(D G)$ only for monotonicity; it never
requires a map from variables to abstract values. For this reason the
relational carrier of @sec:relational (#isaconst("rel_order_spec")) satisfies
the same contract without a change to the framework.

Most analyses neither read nor publish an analysis global. For them the framework
has a narrower interface, the _local specification_ #isatype("local_spec"). It
has one field per field of #isatype("dg_spec"), and each field is a pure function
of local values. Each field also receives a query channel, which
@ch:cooperation introduces. Its soundness #isaconst("sound_local_spec") asks for a
monotone concretization and one law per operation: an edge field covers the
concrete successors of its edge, entry satisfies paired entry coverage, the
composed return covers #isaconst("combine_collect"), and the query handler
answers only what holds. #isaconst("dg_spec_of") runs a local specification as
a #isatype("dg_spec") whose transfers neither read nor publish an analysis global, and
#isathm("dg_spec_of_contract") derives the analysis soundness contract from
#isaconst("sound_local_spec"). The proof layer thus has two entry points.
Equations, routing and the solver are proved over #isatype("dg_spec") and
#isalocale("analysis_contract"), and an analysis with an analysis global such as
#isaconst("rel_order_spec") interprets the contract directly. The analyzer runs
local specifications only (@ch:executable).

@fig:contract-routes shows how the analyses of this thesis reach the contract.
A numeric domain supplies its primitive operations as one record
#isatype("nonrelational_ops") and certifies them once by interpreting
#isalocale("sound_nonrelational_ops") (@sec:instances-supply). The certificate
yields one soundness rule per operation (@sec:whole-state), and these rules
prove the executed local specification #isaconst("exec_spec") sound. The order
analysis of @sec:relational is a local specification over the relational
carrier (#isaconst("order_spec")) and proves its field laws directly.

#let _cbox(pos, name, body) = node(
  pos,
  text(size: 8pt, body),
  name: name,
  inset: 4pt,
  stroke: 0.6pt + vb.neutral,
  shape: rect,
  corner-radius: 2pt,
)
#let _clab(body) = text(size: 7pt, body)
#figure(
  diagram(
    spacing: (26mm, 10mm),
    _cbox((0, 0), <c-prim>, [primitive operations \ #isatype("nonrelational_ops")]),
    _cbox((0, 1), <c-cert>, [certificate, once per domain \ #isalocale("sound_nonrelational_ops")]),
    _cbox((0, 2), <c-rules>, [one rule per operation \ #isalocale("sound_nonrelational_transfer")]),
    _cbox((0, 3), <c-local>, [sound local specification \ #isaconst("sound_local_spec")]),
    _cbox((0, 4), <c-contract>, [analysis soundness contract \ #isalocale("analysis_contract")]),
    _cbox((1, 3), <c-order>, [order analysis \ #isaconst("order_spec")]),
    _cbox(
      (1, 4),
      <c-relspec>,
      [order analysis with an analysis global \ #isaconst("rel_order_spec")],
    ),
    edge(
      <c-prim>,
      <c-cert>,
      "->",
      stroke: 0.6pt + vb.neutral,
      label: _clab[one interpretation per domain],
      label-side: left,
    ),
    edge(
      <c-cert>,
      <c-rules>,
      "->",
      stroke: 0.6pt + vb.neutral,
      label: _clab(isathm("sound_nonrelational_ops.is_sound_nonrelational_transfer")),
      label-side: left,
    ),
    edge(
      <c-rules>,
      <c-local>,
      "->",
      stroke: 0.6pt + vb.neutral,
      label: _clab[#isathm("dg_domain_exec.exec_spec_sound"), at #isaconst("exec_spec")],
      label-side: left,
    ),
    edge(
      <c-local>,
      <c-contract>,
      "->",
      stroke: 0.6pt + vb.neutral,
      label: _clab[#isathm("dg_spec_of_contract"), through #isaconst("dg_spec_of")],
      label-side: left,
    ),
    edge(
      <c-order>,
      <c-local>,
      "->",
      stroke: 0.6pt + vb.neutral,
      label: _clab(isathm("order_spec_sound")),
      label-side: right,
    ),
    edge(
      <c-relspec>,
      <c-contract>,
      "->",
      stroke: 0.6pt + vb.neutral,
      label: _clab[interpretation],
      label-side: left,
    ),
  ),
  kind: image,
  placement: auto,
  caption: [How the analyses of this thesis reach the analysis soundness
    contract. An arrow leads from what an analysis supplies to what it thereby
    establishes, and its label names the Isabelle fact. A numeric domain
    certifies its record of primitive operations once, which yields one rule
    per operation; these rules make its executed local specification sound.
    The order analysis is a sound local specification by its own proof. Every
    sound local specification meets the contract through
    #isaconst("dg_spec_of"). The order analysis with an analysis global is not a local specification and interprets the contract itself.],
) <fig:contract-routes>

== Whole-state analyses <sec:whole-state>

Most analyses use neither analysis globals nor case splits at calls, and
for them the contract should reduce to one rule per operation. The builder
#isaconst("local_state_dg_spec_for") takes seven pure edge operations and a
callee-entry operation, forms a local specification with a fixed call boundary
and runs it through #isaconst("dg_spec_of"). Entry answers the single pair
whose resume value is the unchanged caller value, and the return is
#isaconst("combine_collect_abs"), the abstract counterpart of
#isaconst("combine_collect"). The
unchanged resume value is sound although it may describe stale globals, as in
the `inc` program, because the return takes every global from the callee's
exit. This builder leaves #isaconst("dgs_combine_env") the identity and does
the whole return in #isaconst("dgs_combine_assign"). The rules are the eight
assumptions of #isalocale("sound_nonrelational_transfer"), one per operation,
and #isathm("sound_nonrelational_transfer.local_state_dg_spec_for_contract")
derives the analysis soundness contract from them through
#isathm("dg_spec_of_contract").

The executed analyses use the local specification #isaconst("exec_spec") over
the executable carrier of @ch:solving. It splits the return as Goblint does:
the environment stage takes caller locals and callee globals, and the assign
stage writes the result. #isathm("dg_domain_exec.exec_spec_sound") proves it
sound from the same per-operation rules, pulled back along the readback of
@ch:solving. #isathm("dg_domain_exec.analysis_contract_st") derives the
analysis soundness contract for its image under #isaconst("dg_spec_of"),
#isaconst("local_state_dg_spec_st_for_lifted"). The analyzer runs
#isaconst("exec_spec") as one field of the combined state of @ch:cooperation.

== What the interface leaves out <sec:omissions>

There is no synchronization hook, which would need its own concrete semantics
and obligation. The initial state is not a field either. The pipeline
#isalocale("dg_pipeline") takes it beside the specification, and its one
obligation, #isathm("dg_analysis.init_sound"), is to cover the fixed initial
stores #isaconst("cinit_stores"). Goblint's `startstate` may also install
facts of its own, such as global initializers. The context of a call is not a
field: the routing policy of @ch:equations chooses it. The contract places no soundness obligation on the query field
#isaconst("dgs_query"); @ch:cooperation gives answers their meaning.

An analysis meets #isalocale("analysis_contract") directly or, as a sound local
specification, through #isathm("dg_spec_of_contract").
The interface takes its shape from Goblint: a local and a global lattice, a manager, entry pairs
and a two-stage return. New in this chapter are a soundness contract for that shape
and the paired entry obligation with its counterexample.
@ch:equations derives the five obligations of @ch:traces from the contract,
paired entry coverage, the initial state and the adequacy of the routing
policy.
