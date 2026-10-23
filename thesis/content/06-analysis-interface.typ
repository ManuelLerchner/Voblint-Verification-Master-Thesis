#import "@preview/fletcher:0.5.8": diagram, node
#import "../lib/theme.typ": vb
#import "../lib/code.typ": isaconst, isai, isalocale, isathm, isatype, listing, oblig, thy-badge
#import "../lib/math.typ": *
#import "../lib/sources.typ": thy
#import "../lib/figures.typ": call-edge, entry-node, intra-edge, ppoint, snapshot-var
#import "../lib/claims.typ": claim-ref

= The Analysis Interface <ch:analysis-interface>

@ch:domains ended with laws about one abstract state. Its order agrees with
its meaning, and its operations over-approximate the concrete ones. The
obligations of @ch:traces, however, speak about edges, calls, and contexts, so
something must say what an analysis does at each step of a program. The
non-relational domains of @ch:domains settle this through their primitives,
which determine every edge (@sec:domain-contract). Other analyses need more. A
relational analysis does not store one value per variable (@sec:rel-state), an
analysis may keep facts that belong to no program point, and analyses may need
each other's facts to be precise (@ch:cooperation). Calls, moreover, need more
than one transfer, because the caller's locals survive the call, while the
callee's globals and result flow back.

Everything else between an analysis and the obligations is the same for every
analysis, namely, the equations built from the control-flow graph, the calling
contexts, and the solver. Goblint therefore separates an analysis from the framework that runs it
@seidl26[§6], and Voblint makes the same split in its program and in its proof.
This chapter describes what an analysis must supply, and what it must prove
about it, so that the framework can discharge the obligations of @ch:traces
once for every analysis. An analysis supplies a record of abstract operations,
and the analysis contract states what they preserve.

== Edge transfers and the enter/combine protocol <sec:calls>

An ordinary edge of the control-flow graph carries an action $a$, such as an
assignment or a guard, whose concrete meaning #isaconst("edge_step") is fixed
by @ch:program-model. For a store $s$, #isai("edge_step a s") is the set of
stores the edge can produce. An analysis describes the stores at a program
point by an abstract state $d$ of its _local domain_ $D_L$ and
supplies, for each action $a$, a transfer function $asem(a)$. The transfer is
sound if it loses no successor:
$ s in conc(d) and s' in #isai("edge_step a s") ==> s' in conc(asem(a) thin d). $
This condition is the abstract counterpart of the obligation #oblig("INTRA") of
@ch:traces for one edge.

A call cannot be handled by one such transfer. After it returns, the caller's
own locals are the ones from before the call, while the globals and the result
come from the callee (#isaconst("combine_collect"), #oblig("RETURN")). An analysis
therefore needs two states at a call, one for the callee to start from and one
that saves what the caller needs when execution returns. As in Goblint, it
supplies two operations. _Enter_ (#isaconst("dgs_enter")) produces both
states, and _combine_ (#isaconst("dgs_combine_env"),
#isaconst("dgs_combine_assign")) builds the caller's state after the call from
the resume state and the callee's exit state. Take one call:

#listing(lang: "c", ```
global g;
fun inc(a) { g = g + a; return a - 1; }
fun main() { g = 1; x = 5; y = inc(x); }
```)

At the call `y = inc(x)`, the _entry state_ $e$ describes the store the
callee starts with (`g = 1`, `a = 5`). The _resume state_ $q$ describes the caller's store (`x = 5`,
`g = 1`). For soundness, enter must return such a pair, $q$ covering the
caller's store and $e$ covering the entered store, a property called
_entry coverage_ (#isaconst("entry_pairs_cover")). When the callee exits with state $r$,
combine merges $q$ and $r$ (@fig:return-stores).

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
      _st((0, 0), [resume state $q$ \ describes #_from-s[`x = 5`], `g = 1`]),
      _st(
        (0, 2),
        [$sh("combine")(q, r)$ \ describes #_from-s[`x = 5`], #_from-t[`g = 6`], #_from-t[`y = 4`]],
      ),
      _st((5, 0), [entry state $e$ \ describes `g = 1`, `a = 5`]),
      _st(
        (5, 2),
        [exit state $r$ \ describes #_from-t[`g = 6`], `a = 5`, \ #_from-t[result $4$]],
      ),
      intra-edge(<c-pp5>, <c-pp6>, label: "continuation", label-side: right),
      intra-edge(<c-ent>, <c-ex>, label: "g := g + a; return a - 1", label-side: left),
      call-edge(<c-pp5>, <c-ent>, label: $sh("enter")$, label-side: left),
      call-edge(<c-ex>, <c-pp6>, label: $sh("combine")$, label-side: right),
    )
  },
  kind: image,
  placement: none,
  caption: [Enter and combine at the call `y = inc(x)`, with the concrete store
    each abstract state must describe (schematic, with the body of `inc` drawn
    as one edge). The combined state must describe the caller's locals (blue)
    together with the callee's globals and result (green), as
    #isaconst("combine_collect") does.],
) <fig:return-stores>

Like Goblint's `enter`, enter may return several pairs, one per path in
Goblint's #link("https://github.com/goblint/analyzer/blob/5320a6b741e50dc049f7a1b85e1709e9565cc54a/src/lifters/specLifters.ml#L722")[path-sensitivity lifter] @apinis14[§5.7]. The analyses
shipped with Voblint return one, so path-sensitive analyses remain future work.

== Local soundness laws of an analysis <sec:sound-core>

The operations of @sec:calls say how an analysis propagates abstract states.
They do not by themselves guarantee that these states cover the concrete
executions, and the framework cannot check this without knowing what the
analysis tracks. It therefore asks every analysis for local guarantees, which
@ch:equations composes into the five obligations of @ch:traces for every
program and context policy. Edge transfers account for #oblig("INTRA") and
combine for #oblig("RETURN"). The obligations #oblig("CALL") and #oblig("TOTAL") depend
on the context policy, so the framework derives them from the entry coverage of
@sec:calls together with the policy (@sec:eq-routing), and #oblig("INIT") requires the
initial state $d_0$ to cover the initial stores, which the analysis discharges
when it is registered (#isathm("dg_analysis.init_sound")).

The framework takes the operations of an analysis as one parameter, the record
#isatype("dg_spec") with one field per operation: the edge transfers, enter,
the two combine stages, and a query handler that @ch:cooperation uses to let
analyses exchange facts.

#{
  show raw.where(block: true): set text(size: 6.5pt)
  thy("dg_spec")
}

Every field except the query handler carries, marked $sharp$, the name of the
corresponding method of Goblint's `Spec`. A #isatype("call_info") names the
callee, its formals, the arguments, and the destination of a call.

The record holds the operations, and the _analysis contract_
#isalocale("analysis_contract") states what their results must satisfy. For
an analysis whose transfers depend only on the local state, it consists of
three laws on the concretization $conc$:
#block(inset: (left: 1.5em, y: 0.3em))[
  #grid(
    columns: (auto, 1fr),
    column-gutter: 1.2em,
    row-gutter: 0.75em,
    [monotonicity], $d lle d' ==> conc(d) subset.eq conc(d')$,
    [edges], $s in conc(d), thin s' in #isai("edge_step a s") ==> s' in conc(asem(a) thin d)$,
    [combine],
    $s in conc(q), thin t in conc(r) ==> #isaconst("combine_collect") (s, t) in conc("combine"(q, r))$,
  )
]
Monotonicity turns the solver's inequalities into inclusions between sets of
stores, as for a domain (@ch:domains). The edge law is the condition of
@sec:calls and covers #oblig("INTRA"). The combine law covers #oblig("RETURN").
If $q$ describes the caller's store $s$ and the exit state $r$ describes the
callee's final store $t$, the combined state describes the store in which the
caller continues. Transfers that also use facts without a program point need a
more general form of these laws, which @sec:analysis-globals states.

== Facts shared across program points <sec:shared-facts>

Not every fact belongs to one program point. An analysis may, for example,
keep one range for a global variable `g` that holds throughout the execution.

=== Reading and publishing analysis globals #thy-badge("Voblint_Framework", "DG_Spec_Sound") <sec:analysis-globals>

Seidl et al. describe a Goblint analysis with two domains @seidl26[§6]. The
local domain $D_L$ holds facts per program point and context, and the _global domain_ $D_G$ holds
the values of _analysis globals_, which are unknowns without a program point. An assignment to `g`
publishes its value to the analysis global of `g` as a side effect, and an
edge that reads `g` depends on that unknown. Goblint's
#link("https://github.com/goblint/analyzer/blob/5320a6b741e50dc049f7a1b85e1709e9565cc54a/src/framework/analyses.ml#L168")[`Spec`] likewise declares a local lattice `D` and a global lattice `G`.

The word _global_ thus has two meanings. A _program global_ is a variable of the VIMP program. An analysis global is a fact the
analysis keeps flow-insensitively. The two are independent, and by default, the numeric analyses keep program
globals in the local state and use no analysis global (@sec:mixed-flow).

A transfer that uses analysis globals still returns the next local state, but
it may read and publish them on the way, in Goblint through a
#link("https://github.com/goblint/analyzer/blob/5320a6b741e50dc049f7a1b85e1709e9565cc54a/src/framework/analyses.ml#L142")[_manager_] argument whose contributions the framework passes to the
solver @seidl26[§6]. Voblint adopts this design. Its transfer (#isatype("man_transfer")) receives a manager of type
#isatype("man") instead of a local state. It reads an analysis global $v$ with
#isaconst("man_global") $v$ and publishes $d$ to it with #isaconst("man_sideg") $v$ $d$. As a result, the equations of @ch:equations depend on an analysis
global only where a transfer actually reads it. A transfer that is a pure function of the local state reads only the state at
the edge's source and publishes nothing
(#isathm("sp_compile_transfer_program_local_transfer")).

With analysis globals, a local state alone no longer fixes which stores it
describes, because its meaning may depend on their values. The analysis
contract therefore uses a concretization $conc_(D G)(d, eta)$ of a local state
$d$ under an _environment_ $eta$, which maps every analysis global to its value.
Each law of @sec:sound-core takes $eta$ as an extra parameter
(#isathm("analysis_contract.gammaDG_mono"),
#isathm("analysis_contract.step_sound"),
#isathm("analysis_contract.combine_sound")). Monotonicity holds in both
arguments, and the edge and combine laws describe their results under $eta$
joined with what the operation publishes. A technical premise
(#isaconst("dg_spec_wf")) requires that the program of every operation run its
continuation exactly once, so that what it publishes is well defined. The locale
states these laws over the solver's representation of a valuation:
#{
  show raw.where(block: true): set text(size: 6.5pt)
  thy("analysis_contract")
}
Here, $sigma$ (#isai("\<tau>") in the locale) is an arbitrary valuation of the solver's unknowns
(@sec:global-unknowns), $d$ is its local half #isaconst("dg_local") at the
edge's source, and $eta$ is #isai("genv key \<tau>"), its values at the analysis
globals. #isaconst("edge_out") and #isaconst("edge_pub") are the local state a
transfer returns and what it publishes, and #isaconst("combine_out") and
#isaconst("combine_pub") are the same for combine. An analysis without
analysis globals ignores $eta$ and meets the three laws of @sec:sound-core.

=== Where program globals are stored #thy-badge("Voblint_Framework", "DG_Keyed_Split_Spec") <sec:mixed-flow>

The contract leaves open where program globals are kept. By default, program globals are part of the local state,
as in Goblint's default base analysis for single-threaded programs
(#link("https://github.com/goblint/analyzer/blob/5320a6b741e50dc049f7a1b85e1709e9565cc54a/src/analyses/base.ml#L539")[`base.ml`],
@saan26phd[§5.6.1]).
The other placement keeps each program global at an analysis global of its
own, published by side effects and read where it is used. The analysis is then
_mixed flow-sensitive_, flow-sensitive in the locals and flow-insensitive in
the globals.

// A value at `pp7`, after both calls, from the flow-sensitive Sign run.
#let _mf(var) = snapshot-var("mixed-flow-sign", "main_pp7_ctx0", var)
// The same value from the run with program globals on the shared channel.
#let _mfs(var) = snapshot-var("mixed-flow-sign-shared", "main_pp7_ctx0", var)

#listing(lang: "c", claim: "mixed-flow-sign", ```
global Gx;
fun set() { Gx = 1; }
fun get() { return Gx; }
fun main() { x = 1; set(); y = get(); }
```)

The flow-insensitive placement keeps one value of `Gx` for every program
point, including those before `set` runs, so it must cover the initial
`Gx = 0` as well as the 1 written by `set`. Sign therefore claims only #signval(_mfs("y")) for `y`
after `y = get()` (claim #claim-ref("mixed-flow-sign-shared")), although every
execution ends with `y = 1`. Flow-sensitively, Sign carries #signval("+") from
`set`'s exit into `get`'s entry and derives #signval(_mf("y")) (claim
#claim-ref("mixed-flow-sign")). In sequential VIMP, the flow-insensitive
placement can thus cost precision.

The flow-insensitive placement matters beyond this example. Another thread may
write a shared global at any point, so the simplest thread-modular analysis
keeps shared globals flow-insensitively @seidl26[§1, Ex. 4] @saan26phd[§5.3.1]. More generally, mixed flow-sensitivity
lets an analysis choose per fact whether precision at each program point is
worth a value per point and context.
The placement is proved to meet the analysis contract for the analyzer's
product state (#isathm("keyed_split_contract")), so the end-to-end soundness theorem
covers both placements, and a future extension with threads can build on a
verified flow-insensitive core.
