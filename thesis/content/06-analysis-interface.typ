#import "@preview/fletcher:0.5.8": diagram, node
#import "../lib/theme.typ": vb
#import "../lib/code.typ": isaconst, isai, isalocale, isathm, isatype, listing, oblig, thy-badge
#import "../lib/math.typ": *
#import "../lib/sources.typ": thy
#import "../lib/figures.typ": call-edge, entry-node, intra-edge, ppoint, snapshot-var
#import "../lib/claims.typ": claim-ref

= The Analysis Interface <ch:analysis-interface>

The equations, calling contexts, and solver discharge the obligations of
@ch:traces in the same way for every analysis. Voblint therefore separates
each analysis from this framework, as Goblint does @seidl26[§6]
(@sec:state-of-art). This chapter states the operations and proofs an analysis
must supply for the framework's argument to apply.

For the non-relational domains of @ch:domains, the domain primitives determine every edge
transfer (@sec:domain-contract). Other analyses need more. A relational
analysis can track relationships between variables, an analysis
may keep facts that belong to no program point, and analyses may need each
other's facts to be precise (@ch:cooperation). Calls, moreover, need more than
one transfer, because the caller's locals survive the call, while the callee's
globals and result flow back.

== Edge transfers and the enter/combine protocol <sec:calls>

An ordinary CFG edge carries an action $a$, such as an assignment or guard.
For a store $s$, $sem(a)(s)$ is its set of successor stores
(#isaconst("edge_step"), @sec:valid). An analysis describes the stores at a program
point by an abstract state $d$ of its _local domain_ $D_L$. Its
concretization $conc(d)$ is the set of stores described by $d$. For each
action $a$, the analysis supplies a transfer function $asem(a)$. The transfer
is sound if, for every store $s$ described by $d$ and every successor store
$s'$ produced by $a$, the resulting abstract state describes $s'$:
$ s in conc(d) and s' in sem(a)(s) ==> s' in conc(asem(a) thin d). $
This condition is the abstract counterpart of the obligation #oblig("INTRA") of
@ch:traces for one edge.

The interprocedural protocol separates call entry from return. After a call returns, the caller's
own locals are the ones from before the call, while the globals and the result
come from the callee (#isaconst("combine_collect"), #oblig("RETURN")). An analysis
therefore needs two states at a call, one for the callee to start from and one
that saves what the caller needs when execution returns. As in Goblint,
_enter_ (#isaconst("dgs_enter")) produces both
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
    as one edge). The combined state preserves `x = 5` from the caller and takes `g = 6`
    and the result `4` from the callee, assigning the result to `y`.],
) <fig:return-stores>

Enter may return several pairs, and each pair can get its own context
(@sec:contexts). A path-sensitive analysis keeps separate abstract alternatives
for executions reaching the same point, rather than immediately joining them.
Goblint returns one pair per such alternative in its
#link("https://github.com/goblint/analyzer/blob/5320a6b741e50dc049f7a1b85e1709e9565cc54a/src/lifters/specLifters.ml#L722")[path-sensitivity lifter] @apinis14[§5.7]. The analyses
shipped with Voblint return one, so path-sensitive analyses remain future work.

== Local soundness laws of an analysis <sec:sound-core>

The equation-system proof in
@ch:equations composes the local soundness laws into the five obligations of @ch:traces for every
program and context policy. Edge transfers account for #oblig("INTRA") and
combine for #oblig("RETURN"). The obligations #oblig("CALL") and #oblig("TOTAL") depend
on the context policy, so the framework derives them from the entry coverage of
@sec:calls together with the policy. Finally, #oblig("INIT")
requires the initial state $d_0$ to cover the initial stores, which the
analysis discharges when it is registered (#isathm("dg_analysis.init_sound")).

The record #isatype("dg_spec") packages an analysis's edge transfers, enter,
two combine stages, and a query handler for exchanging facts (@ch:cooperation).
The _analysis contract_ #isalocale("analysis_contract") states their soundness
laws. For
an analysis whose transfers depend only on the local state, it consists of
three laws on the concretization $conc$:
#block(inset: (left: 1.5em, y: 0.3em))[
  #grid(
    columns: (auto, 1fr),
    column-gutter: 1.2em,
    row-gutter: 0.75em,
    [monotonicity], $d lle d' ==> conc(d) subset.eq conc(d')$,
    [edges], $s in conc(d), thin s' in sem(a)(s) ==> s' in conc(asem(a) thin d)$,
    [combine],
    $s in conc(q), thin t in conc(r) ==> #isaconst("combine_collect") _(italic("dst")) (s, t) in conc("combine"(q, r))$,
  )
]
Monotonicity turns the solver's inequalities into inclusions between sets of
stores, as for a domain (@ch:domains). The edge law is the condition of
@sec:calls and covers #oblig("INTRA"). The combine law covers #oblig("RETURN").
Transfers that also use facts without a program point need a
more general form of these laws, which @sec:analysis-globals states.

== Analysis globals and program globals <sec:shared-facts>

Not every fact belongs to one program point. A flow-insensitive fact, such as
one range for a global variable `g` across the whole execution, lives in an
unknown attached to no program point, and the points that change it contribute
to that unknown by side effects (@sec:side-effects). The transfers of
@sec:calls only map local states to local states, so the interface has to give
them access to such unknowns.

=== Analysis globals #thy-badge("Voblint_Framework", "DG_Spec_Sound") <sec:analysis-globals>

Seidl et al. describe a Goblint analysis with two domains @seidl26[§6]. The
local domain $D_L$ holds facts per program point and context, and the _global domain_ $D_G$ holds
the values of _analysis globals_, which are unknowns without a program point. An assignment to `g`
publishes its value to the analysis global of `g` as a side effect, and an
edge that reads `g` depends on that unknown. Goblint's `Spec` likewise
declares a local lattice `D` and a global lattice `G`.

The word _global_ thus has two meanings. A _program global_ is a variable of the VIMP program. An analysis global is a fact the
analysis keeps flow-insensitively. The two are independent, and by default, the numeric analyses keep program
globals in the local state and use no analysis global (@sec:mixed-flow).

A transfer still returns the next local state, but may read and publish
analysis globals through a
#link("https://github.com/goblint/analyzer/blob/5320a6b741e50dc049f7a1b85e1709e9565cc54a/src/framework/analyses.ml#L142")[_manager_] argument whose contributions the framework passes to the
solver @seidl26[§6]. Voblint likewise passes a manager instead of a local state
(#isatype("man_transfer")). The equations of @ch:equations depend on an analysis
global only where a transfer actually reads it. A transfer that is a pure function of the local state reads only the state at
the edge's source and publishes nothing
(#isathm("sp_compile_transfer_program_local_transfer")).

The record packages these manager-based operations:
#{
  show raw.where(block: true): set text(size: 6.5pt)
  thy("dg_spec")
}
Every field except the query handler carries, marked $sharp$, the name of the
corresponding method of
#link("https://github.com/goblint/analyzer/blob/5320a6b741e50dc049f7a1b85e1709e9565cc54a/src/framework/analyses.ml#L168")[`Spec`],
the module signature of a Goblint analysis. A #isatype("call_info") names the
callee, its formals, the arguments, and the destination of a call.

The analysis contract uses a concretization $conc_(D G)(d, eta)$ of a local state
$d$ under an _environment_ $eta$, which maps every analysis global to its value.
Each law of @sec:sound-core takes $eta$ as an extra parameter. Monotonicity
holds in both arguments, and the edge and combine laws describe their results
under $eta$ joined with what the operation publishes.

An operation is represented by a _strategy program_, a function that takes a
continuation describing what to do with its result and builds a strategy tree
(#isatype("strategy_program"), @sec:td). Grafting a continuation $h$ onto a
tree replaces each answer leaf $d$ by the tree $h(d)$. Well-formedness requires
that grafting after the program has built its tree gives the same tree as
first appending $h$ to the supplied continuation and then running the program
(#isaconst("sp_wf")). The analysis contract requires this property of its
operations (#isaconst("dg_spec_wf")).

The solver stores each value as a pair with a local and a global half
(@sec:global-unknowns). In the locale below, $sigma$ (#isai("\<tau>") in
Isabelle) is a valuation of these pairs, $d$ is its local half
#isaconst("dg_local") at the edge's source, and $eta$ is
#isai("genv key \<tau>"), its values at the analysis globals. The locale
#isalocale("analysis_contract") states the laws in this representation:
#{
  show raw.where(block: true): set text(size: 6.5pt)
  thy("analysis_contract")
}

#isaconst("edge_out") and #isaconst("edge_pub") are the local state a
transfer returns and what it publishes, and #isaconst("combine_out") and
#isaconst("combine_pub") are the same for combine. An analysis without
analysis globals ignores $eta$ and meets the three laws of @sec:sound-core.

=== Placement of program globals #thy-badge("Voblint_Framework", "DG_Keyed_Split_Spec") <sec:mixed-flow>

The contract leaves open where program globals are kept. The default placement
of @sec:analysis-globals keeps them in the local state, as in Goblint's default
base analysis for single-threaded programs
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

The flow-insensitive placement matters for concurrent programs. Another thread
may write a shared global at any point, so the simplest thread-modular
analysis, which analyzes each thread on its own, keeps shared globals
flow-insensitively @seidl26[§1, Ex. 4] @saan26phd[§5.3.1].
For a sound analysis without analysis globals, the proof of this placement
requires a _frame law_. Here $eta$ gives the stored abstract value of each
program global, since each has its own analysis global. Suppose the input
store is described under $eta$, and a result state $r$ describes an output
store that agrees with it on all program globals outside a set $W$. Recombine
the local-variable part of $r$ with the abstract global values from $r$ on
$W$ and from $eta$ outside $W$. The resulting
state must still describe that output store. The analyzer's product carrier
meets this law and the required order conditions
(#isathm("keyed_split_contract")), so the end-to-end soundness theorem covers
both placements. A future extension with threads can build on this verified
flow-insensitive core.
