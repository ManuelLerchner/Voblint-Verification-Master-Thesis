#import "@preview/fletcher:0.5.8": diagram, edge, node
#import "../lib/theme.typ": vb
#import "../lib/code.typ": isaconst, isai, isalocale, isathm, isatype, listing, oblig
#import "../lib/math.typ": *
#import "../lib/theorems.typ": definition, theorem

= What an Analysis Supplies <ch:analysis-interface>

An analysis should prove its obligations without knowing the
context policy or the solver. Equations, solver, call wiring and context policy
are the same for every analysis, so the framework should own them and prove
them once, and the analysis should supply only its operations and their
soundness. The task is to find the smallest interface for which this works,
and four simpler interfaces fail. A single local lattice cannot hold a fact that is
true throughout a run. Transfers that thread a shared value make every equation
depend on it (@sec:dg). A return edge from the callee's exit loses the caller's
locals, and an entry obligation under which some alternative covers the caller
and some other covers the callee is unsound (@sec:calls). The interface below
avoids all four. It follows the
#link("https://github.com/goblint/analyzer/blob/5320a6b741e50dc049f7a1b85e1709e9565cc54a/src/framework/analyses.ml")[pinned Goblint specification],
one method per program construct (@tab:dg-spec-fields), and its obligations
mention neither contexts nor the solver: #oblig("INTRA") and #oblig("RETURN")
become obligations on each edge transfer and on the return, which for a
whole-state analysis are one soundness rule per operation, and @ch:equations derives
#oblig("CALL") and #oblig("TOTAL") from paired entry coverage and the routing
policy. The correspondence with Goblint is architectural. The meaning of each
operation comes from the VIMP and CFG semantics of @ch:program-model, and
Goblint's OCaml code plays no part in it.

== Edges, and a shared component <sec:dg>

For a concretization $conc_(D)$ of the analysis's values, an edge transfer
must map every store $s in conc_(D)(d)$ and every successor
#isai("s' \<in> edge_step a s") to $s' in conc_(D)(f_a (d))$, which is
#oblig("INTRA") for one edge. Seven fields of the record #isatype("dg_spec")
are such transfers (@tab:dg-spec-fields). A check runs the event operation, not a branch:
observing a check must keep the stores that violate it, since those are what
the verdict detects. It does not run the skip operation either, so a domain
whose skip is not the identity cannot change what a check edge does. Goblint
instead handles `__goblint_check` in `special`, which returns the local state
unchanged when refinement is disabled.

#figure(
  table(
    columns: (auto, 1fr),
    stroke: none,
    table.hline(),
    [*field*], [*concrete step it approximates*],
    table.hline(stroke: 0.5pt),
    [#isaconst("dgs_skip")], [no-op edge],
    [#isaconst("dgs_assign")], [assignment],
    [#isaconst("dgs_special")], [recognised library call],
    [#isaconst("dgs_branch")], [guard or its negation],
    [#isaconst("dgs_body")], [entry into a procedure body],
    [#isaconst("dgs_return")], [`return e`, writing #isaconst("ret_var")],
    [#isaconst("dgs_event")], [check edge, observed],
    [#isaconst("dgs_enter")], [call entry #isaconst("call_enter"), as pairs],
    [#isaconst("dgs_combine_env")], [first stage of the return: environments],
    [#isaconst("dgs_combine_assign")], [second stage: result into the destination],
    [#isaconst("dgs_query")], [none: answers a question about the current state],
    table.hline(),
  ),
  placement: auto,
  caption: [The fields of #isatype("dg_spec"). Each field
    #raw("dgs_")$m$ has the role of the method $m$ of Goblint's `Spec`, except
    #isaconst("dgs_event"): Goblint handles its check function in `special`.
    Only the composition of the two return stages carries an obligation
    (@sec:sound-core). The query handler is the subject of
    @ch:cooperation.],
) <tab:dg-spec-fields>

A transfer from one local value to the next suffices for an analysis that
keeps every fact per program point. It cannot express a fact that holds
throughout the run, such as one range for a global variable to which every
write contributes: such a fact is an unknown without a program point
(@sec:side-effects). Goblint's `Spec` therefore declares a local lattice `D`
and a global lattice `G`, and the carrier #isatype("dg_state") pairs a local
component #isai("locals") with a shared component #isai("globs"). The vendored
solver has one value type for all unknowns, so every unknown holds a whole
#isatype("dg_state"). A local unknown, owned by one node in one context, uses
its #isai("locals") half, as does the callee-entry seed of @ch:equations; the
key of an analysis global uses its #isai("globs") half. The unused half is
$lbot$.

The next simplest transfer receives the local and the shared value and returns
both. That shape makes every edge equation read the shared unknown and publish
to it, even for an analysis that ignores it. Since the solver re-evaluates
every reader of a changed key (@sec:eq-seed), every change of the shared value
would then re-evaluate every edge. A transfer is instead a program over the
solver's reads and publications. It receives a manager: #isaconst("man_local")
is the current local value, #isaconst("man_global") reads a named analysis
global, and #isaconst("man_sideg") publishes to one. A transfer that uses
neither capability compiles to an equation whose only dependency is its source
unknown and which publishes nothing
(#isathm("sp_compile_transfer_program_local_transfer")). The program form
loses no generality. The relational witness of @sec:relational writes its transfers
in the threading shape and wraps each as a program that reads the shared value,
publishes the new one and answers the local result (#isaconst("rel_transfer")).
Goblint's transfer functions have the program shape: they read `man.global`,
call `man.sideg`, and return a local value.

The manager also hides solver keys (#isaconst("mk_dg_man")), so a transfer
written against it never names a key. The types do not enforce this, and
soundness does not depend on it: the equation-soundness theorem of
@ch:equations restricts no publication, and a hand-built publication at a
framework key only raises the solved value there, which can lose precision.

A VIMP global and a shared unknown are different objects. The five numeric
analyses keep the whole abstract store, globals included, in #isai("locals"),
as Goblint's base analysis does for single-threaded programs
(@sec:mixed-flow). Their transfer and concretization proofs then stay pointwise
over one store, globals remain flow-sensitive because every node and context
has its own local value, and a context computed from the entered local value
(@ch:equations) sees the globals too. Their transfers use neither capability,
so the shared component adds no dependency and no publication to them. The
shared namespace carries callee entry values (@ch:equations), the relational
witness of @ch:instances, and the globals of @sec:mixed-flow.

== The call boundary <sec:calls>

The obvious model treats a call as two edges: an entry edge into the callee and
a return edge carrying the callee's exit value to the caller's continuation.
The return edge fails on this program:

#listing(lang: "c", ```
global g;
fun inc(a) { g = g + a; return a - 1; }
fun main() { g = 1; x = 5; y = inc(x); }
```)

#figure(
  table(
    columns: (auto, auto, auto, auto, auto),
    align: (left, center, center, center, left),
    stroke: none,
    table.hline(),
    [*name*], [*caller* $s$], [*callee entry*], [*callee exit* $t$], [*continuation*],
    table.hline(stroke: 0.5pt),
    [`g` (global)], [1], [1], [6], [6, from $t$],
    [`x` (local)], [5], [0], [0], [5, from $s$],
    [`y` (destination)], [any], [0], [0], [4, the result in $t$],
    table.hline(),
  ),
  caption: [Stores of the `inc` run. Entry keeps globals and resets locals
    (#isaconst("enter_state")).],
) <tab:return-stores>

Forwarding the exit value would claim `x = 0` after the call, and forwarding
the caller's value would claim `g = 1`. The continuation takes caller locals, callee
globals and the result (#isaconst("combine_collect") in #oblig("RETURN")), so
the abstract return must be binary: a caller value and the callee's exit value,
as the abstract `combine` of the functional approach is @seidl12compiler[§2.6].

On the entry side, one callee entry value with the caller resuming from its
call-site value is sound, and the whole-state analyses of @sec:whole-state use
this form. Goblint's `enter` is more general. It returns a list of pairs, so
an analysis may weaken caller facts at the call or split a call into cases, say
by the sign of an argument, each reaching its own callee context. The field
#isaconst("dgs_enter") has the same shape: a list of pairs $(q, e)$ of a
_resume value_ $q$, from which the caller continues (the theories call it the
continuation), and a callee entry value $e$. The framework routes each $e$ to a
callee context and combines the result read there with the $q$ of the same
pair (#isathm("ov_two_contexts") runs Sign with two overlapping alternatives).
The list makes the context semantics of @sec:contexts a relation, and it
makes the paired obligation below necessary.

=== Why coverage must be paired

A simpler obligation asks the list to cover the caller store $s$ in some
resume value and the entered store #isai("s' = call_enter \<G> a s") in some
entry. It is too weak, because results are combined only with the resume value
of their own pair (@fig:unpaired-cover). The example needs contexts that
separate the two entries: with a single context both entries reach one seed,
the callee result covers both signs, and this program no longer shows the
failure.

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

#definition(name: [Paired entry coverage], isa: "entry_pairs_cover", cmd: "definition")[
  Under a concretization $conc_(D)$, a list $P$ covers the caller store $s$ and the entered store $s'$ if
  $ exists (q, e) in P. quad s in conc_(D)(q) and s' in conc_(D)(e). $
]

The covering pair's entry selects a callee context covering the real
activation, and its resume value covers the real caller. This is the
correlation of #oblig("RETURN") (@sec:contract), stated for one call's
alternatives. The
quantifier is existential because the alternatives form a disjunction: each
pair covers the runs it was computed for, and requiring every pair to cover
every caller would forbid the case split the list exists to express.

As in Goblint, the return has two stages, #isaconst("dgs_combine_env") and
#isaconst("dgs_combine_assign"), and the second runs from the local value the
first produced. Only their composition carries an obligation, so a
specification may do the whole return in either stage (@sec:whole-state).

== The analysis soundness contract <sec:sound-core>

@ch:equations proves the coverage obligations once, so it needs from each
analysis a fixed set of facts that mention neither contexts nor the solver. The
locale #isalocale("analysis_contract"), the _analysis soundness contract_,
states what a specification owes a concretization $conc_(D G)(d, g)$ of a local
and a shared value. Two of its assumptions are structural. The concretization
is monotone in both arguments, which turns the solver's order inequalities into
set inclusions as $conc$ does for a domain (@ch:domains). Every transfer is well
formed in the sense of #isaconst("dg_spec_wf"): it runs its continuation
exactly once, so what a compiled transfer publishes is well defined.

The other two concern what each edge's right-hand side returns and publishes,
since the solver's certificate bounds exactly these (@ch:solving):
#oblig("INTRA") for each edge transfer and #oblig("RETURN") for the composed
combine, the latter at arbitrary values, since a pair's resume value is held by
no unknown. Both read and check the shared component at one slot, because the
locale fixes the type of analysis global names to `unit`. It therefore covers
analyses with a single global, which includes every analysis in the
development; a second global would need a concretization over a global
environment. Entry is absent: its soundness depends on which alternative the
routed equations select, and @sec:eq-routing states it as paired coverage.

The obligations are stated over what the compiled programs return and publish.
No local and shared pair is reconstructed, and a transfer that publishes
nothing is checked against $lbot$. The contract asks the carriers only for a
bounded join semilattice and $conc_(D G)$ only for monotonicity; it never
requires a map from variables to abstract values. For this reason the
relational carrier of @sec:relational (#isaconst("rel_order_spec")) satisfies
the same contract without a change to the framework.

Most analyses use neither capability of the manager. For them the framework
has a narrower interface, the _local specification_ #isatype("local_spec"). It
has one field per row of @tab:dg-spec-fields, and each field is a pure function
of local values. Each field also receives a query channel, which
@ch:cooperation introduces. A local specification cannot read or publish an
analysis global. Its soundness #isaconst("sound_local_spec") asks for a
monotone concretization and one law per field: an edge field covers the
concrete successors of its edge, entry satisfies paired entry coverage, the
composed return covers #isaconst("combine_collect"), and the query handler
answers only what holds. #isaconst("dg_spec_of") runs a local specification as
a #isatype("dg_spec") whose transfers use neither capability, and
#isathm("dg_spec_of_contract") derives the analysis soundness contract from
#isaconst("sound_local_spec"). The proof layer thus has two entry points.
Equations, routing and the solver are proved over #isatype("dg_spec") and
#isalocale("analysis_contract"), and an analysis with a shared value such as
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
    _cbox((1, 4), <c-relspec>, [order analysis with shared state \ #isaconst("rel_order_spec")]),
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
    #isaconst("dg_spec_of"). The order analysis with a shared state is not a local
    specification and interprets the contract itself.],
) <fig:contract-routes>

== Whole-state analyses <sec:whole-state>

Most analyses use neither the shared component nor case splits at calls, and
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
#isathm("dg_spec_of_contract"). A non-relational domain does not prove these
rules one by one. It supplies its primitive operations as one record and
certifies them once, and
#isathm("sound_nonrelational_ops.is_sound_nonrelational_transfer") derives the
rules (@sec:instances-supply).

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

There is no synchronization and no analysis-supplied initial state. Each would
need its own concrete semantics and obligation. The context of a call is not a
field either: the routing policy of @ch:equations chooses it. The contract
places no soundness obligation on the query field #isaconst("dgs_query"). A transfer may ask
through the manager, but what an answer means, and how several analyses answer
one another, is the subject of @ch:cooperation.

An analysis meets the analysis soundness contract
#isalocale("analysis_contract") either directly or as a sound local
specification through #isathm("dg_spec_of_contract"). A whole-state analysis
proves one soundness rule per operation, and
#isathm("sound_nonrelational_transfer.local_state_dg_spec_for_contract")
derives the contract from these rules, as
#isathm("dg_domain_exec.analysis_contract_st") does for the executed variant.
The contract states #oblig("INTRA") per edge and #oblig("RETURN") for the
composed combine, over a monotone concretization and well-formed transfers,
for analyses with a single analysis global. It mentions no context policy, no
solver and no variable map. Entry soundness is paired entry coverage, and the
unpaired variant fails (#isathm("unpaired_entry_cover_unsound")).
The interface takes its shape from Goblint: a local and a global lattice, a manager, entry pairs
and a two-stage return. New in this chapter are a soundness contract for that shape
and the paired entry obligation with its counterexample.
@ch:equations consumes exactly these two facts: it proves the five obligations
of @ch:traces for the generated equations from the contract, paired entry
coverage and the adequacy of the routing policy.
