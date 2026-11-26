#import "@preview/fletcher:0.5.8": diagram, node
#import "../lib/theme.typ": vb
#import "../lib/code.typ": isaconst, isai, isalocale, isathm, isatype, listing, oblig, thy-badge
#import "../lib/math.typ": *
#import "../lib/sources.typ": thy
#import "../lib/figures.typ": call-edge, entry-node, intra-edge, ppoint, snapshot-var
#import "../lib/claims.typ": claim-ref
#import "../lib/cfg-graphs.typ": mixed-flow-final, mixed-flow-graph, mixed-flow-published

= Analyses and Their Soundness Laws <ch:analysis-interface>

A domain of @ch:domains describes the stores at one program point. To meet the
obligations of @ch:traces, an analysis adds transfer functions that carry these
descriptions through the program and across calls, and it proves each of them
sound. Much of what discharges these obligations is
the same for every analysis: the equations built from the control-flow graph,
the calling contexts, and the solver. Voblint therefore separates an analysis
from the framework that runs it, as Goblint does @seidl26[§6]
(@sec:state-of-art), and makes the split in its proof as well as in its
program.

== Edge transfers and the enter/combine protocol <sec:calls>

An ordinary CFG edge carries an action $a$, such as an assignment or guard.
For a store $s$, $sem(a)(s)$ is its set of successor stores
(#isaconst("edge_step"), @sec:valid). An analysis describes the stores at a program
point by an abstract state $d$ of its _local domain_ $D_L$. Its
concretization $conc(d)$ is the set of stores described by $d$. For each
action $a$, the analysis supplies a transfer function $asem(a)$, where $sharp$ marks an abstract operation. The transfer
is sound if, for every store $s$ described by $d$ and every successor store
$s'$ produced by $a$, the resulting abstract state $asem(a) thin d$ describes
$s'$. This condition is the abstract counterpart of the obligation #oblig("INTRA") of
@ch:traces, which requires each local edge to preserve the cover.

After a call returns, the caller's own locals are the ones from before the
call, while the globals and the result come from the callee
(#isaconst("combine_collect"), the store that #oblig("RETURN") covers). An analysis therefore needs
two states at a call, one for the callee to start from and one that saves what
the caller needs when execution returns. As in Goblint, _enter_ $enterh$
(#isaconst("dgs_enter")) produces both states, and _combine_ $combineh$ builds the
caller's state after the call from the resume state and the callee's exit
state. Take one call:

#listing(lang: "c", ```
global g;
fun inc(a) { g = g + a; return a - 1; }
fun main() { g = 1; x = 5; y = inc(x); }
```)

At the call `y = inc(x)`, the _entry state_ $e$ describes the store the
callee starts with (`g = 1`, `a = 5`). The _resume state_ $q$ describes the caller's store (`x = 5`,
`g = 1`). For soundness, enter must return such a pair, $q$ describing the
caller's store and $e$ describing the entered store, a property called
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
        [$combineh(q, r)$ \ describes #_from-s[`x = 5`], #_from-t[`g = 6`], #_from-t[`y = 4`]],
      ),
      _st((5, 0), [entry state $e$ \ describes `g = 1`, `a = 5`]),
      _st(
        (5, 2),
        [exit state $r$ \ describes #_from-t[`g = 6`], `a = 5`, \ #_from-t[result $4$]],
      ),
      intra-edge(<c-pp5>, <c-pp6>, label: "continuation", label-side: right),
      intra-edge(<c-ent>, <c-ex>, label: "g := g + a; return a - 1", label-side: left),
      call-edge(<c-pp5>, <c-ent>, label: $enterh$, label-side: left),
      call-edge(<c-ex>, <c-pp6>, label: $combineh$, label-side: right),
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

The local soundness laws of an analysis together yield the five obligations of
@ch:traces for every program and context policy. #oblig("CALL") (cover the entered store) and
#oblig("TOTAL") (every covered call has a context) depend on the policy as well and follow from the entry coverage of
@sec:calls. #oblig("INIT") requires the initial state $d_0$ to describe the
initial stores, which the analysis discharges when it is registered
(#isathm("dg_analysis.init_sound")).

The _analysis contract_ #isalocale("analysis_contract") states the soundness
laws of the operations of @sec:calls. For an analysis whose transfers depend only on the local state, it consists of
three laws on the concretization $conc$:
#block(inset: (left: 1.5em, y: 0.3em))[
  #grid(
    columns: (auto, 1fr),
    column-gutter: 1.2em,
    row-gutter: 0.75em,
    [monotonicity], $d lle d' ==> conc(d) subset.eq conc(d')$,
    [edges], $s in conc(d), thin s' in sem(a)(s) ==> s' in conc(asem(a) thin d)$,
    [combine],
    $s in conc(q), thin t in conc(r) ==> #isaconst("combine_collect") _(italic("dst")) (s, t) in conc(combineh(q, r))$,
  )
]
Monotonicity turns the solver's inequalities into inclusions between sets of
stores, as for a domain (@ch:domains). The edge law is the condition of
@sec:calls and yields #oblig("INTRA"). The combine law, where $italic("dst")$
is the call's destination, yields #oblig("RETURN").
Transfers that read facts without a program point need the more general laws
of @sec:analysis-globals.

== Analysis globals and program globals <sec:shared-facts>

Not every fact belongs to one program point. A flow-insensitive fact, such as
one range for a global variable `g` across the whole execution, lives in an
unknown attached to no program point, and the points that change it contribute
to that unknown by side effects (@sec:side-effects). The transfers of
@sec:calls only map local states to local states, so the interface has to give
them access to such unknowns.

=== Analysis globals #thy-badge("Voblint_Framework", "DG_Spec_Sound") <sec:analysis-globals>

A Goblint analysis has two domains @seidl26[§6]. The
local domain $D_L$ holds facts per program point and context, and the _global domain_ $D_G$ holds
the values of _analysis globals_, which are unknowns without a program point. An assignment to `g`
publishes its value to the analysis global of `g` as a side effect, and an
edge that reads `g` depends on that unknown.
#link("https://github.com/goblint/analyzer/blob/5320a6b741e50dc049f7a1b85e1709e9565cc54a/src/framework/analyses.ml#L168")[`Spec`],
the module signature of a Goblint analysis, likewise declares a local lattice
`D` and a global lattice `G`.

The word _global_ thus has two meanings. A _program global_ is a variable of the VIMP program. An analysis global is a fact the
analysis keeps flow-insensitively. The two are independent, and by default, the numeric analyses keep program
globals in the local state and use no analysis global (@sec:mixed-flow).

A transfer still returns the next local state. In Goblint it receives a
#link("https://github.com/goblint/analyzer/blob/5320a6b741e50dc049f7a1b85e1709e9565cc54a/src/framework/analyses.ml#L142")[_manager_],
an argument that gives it the local state and lets it read and publish
analysis globals, and the framework passes the published contributions to the
solver @seidl26[§6]. Voblint likewise passes a manager instead of a local state
(#isatype("man_transfer")).

The record #isatype("dg_spec") packages these manager-based operations with a
query handler through which analyses exchange facts:
#{
  show raw.where(block: true): set text(size: 6.5pt)
  thy("dg_spec")
}
Every field except the query handler carries, marked $sharp$, the name of the
corresponding method of `Spec`. A #isatype("call_info") is the call information of @sec:valid: the
callee, its formal parameters, the actual arguments, and the variable that receives the result.

With analysis globals, a local state alone no longer fixes which stores it
describes. The laws therefore take an _environment_ $eta : V_G -> D_G$, from the analysis's
global names $V_G$ to their values (in Goblint, the manager's `global`), and use a concretization $conc_(D G)(d, eta)$. A
transfer at $d$ and $eta$ returns a local state $d'$ together with the
contributions $p$ it publishes to analysis globals, and combine at $q$, $r$,
and $eta$ returns a pair $(q', p)$ in the same way. The three laws of
@sec:sound-core become
#block(inset: (left: 1.5em, y: 0.3em))[
  #grid(
    columns: (auto, 1fr),
    column-gutter: 1.2em,
    row-gutter: 0.75em,
    [monotonicity],
    $d lle d', thin eta lle eta' ==> conc_(D G)(d, eta) subset.eq conc_(D G)(d', eta')$,

    [edges], $s in conc_(D G)(d, eta), thin s' in sem(a)(s) ==> s' in conc_(D G)(d', eta ljoin p)$,
    [combine],
    [$s in conc_(D G)(q, eta), thin t in conc_(D G)(r, eta)$ \
      #h(
        1.5em,
      ) $==> #isaconst("combine_collect") _(italic("dst")) (s, t) in conc_(D G)(q', eta ljoin p)$],
  )
]
An analysis without analysis
globals ignores $eta$ and publishes nothing, so the laws reduce to those of
@sec:sound-core. The locale #isalocale("analysis_contract") states these laws.

=== Placement of program globals #thy-badge("Voblint_Framework", "DG_Keyed_Split_Spec") <sec:mixed-flow>

The contract leaves open where program globals are kept. The default placement
of @sec:analysis-globals keeps them in the local state, as in Goblint's default
base analysis for single-threaded programs
(#link("https://github.com/goblint/analyzer/blob/5320a6b741e50dc049f7a1b85e1709e9565cc54a/src/analyses/base.ml#L539")[`base.ml`],
@saan26phd[§5.6.1]).
The flow-insensitive placement keeps each program global at an analysis global of its
own, published by side effects and read where it is used. The analysis is then
_mixed flow-sensitive_, meaning flow-sensitive in the locals and flow-insensitive in
the globals. In the following program, this placement costs precision.

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

The flow-insensitive placement keeps a single value of `Gx` shared by all
program points (@fig:mixed-flow). The entry of `main` publishes
the initial value, #signval(mixed-flow-published("entry_main")), and the point
after `Gx = 1` in `set` publishes #signval(mixed-flow-published("pp1")). The
global unknown holds their join, #signval(mixed-flow-final), and every read of
`Gx`, including `return Gx` in `get`, returns this join. Yet
`get` only runs after `set` has written $1$, so `Gx` is positive there in every
execution. Sign therefore claims only #signval(_mfs("y")) for `y`
after `y = get()` (claim #claim-ref("mixed-flow-sign-shared")). Flow-sensitively, Sign carries #signval("+") from
`set`'s exit into `get`'s entry and derives #signval(_mf("y")) (claim
#claim-ref("mixed-flow-sign")).

#figure(
  mixed-flow-graph,
  placement: none,
  caption: [The solved graph of the program above with `Gx` placed
    flow-insensitively, in Sign. Solid green edges are side effects into the
    global unknown of `Gx` (diamond) and the read at `return Gx`. Dashed edges
    are calls, dotted edges continuations. Return edges are omitted. Labels and values come from claims
    #claim-ref("mixed-flow-shared-dot") and #claim-ref("mixed-flow-shared-trace").],
) <fig:mixed-flow>


VIMP has no threads, so the flow-sensitive default loses nothing. The
flow-insensitive placement prepares the analysis of concurrent programs. There
another thread may write a shared global at any point, so a thread-modular
analysis, which analyzes each thread on its own, can keep shared globals
flow-insensitively @seidl26[§1, Ex. 4] @saan26phd[§5.3.1]. The end-to-end
soundness theorem covers both placements (#isathm("keyed_split_contract")).
Every analysis so far sees only its own state. The next chapter lets analyses
exchange facts while they run.
