#import "@preview/fletcher:0.5.8": diagram, node
#import "../lib/theme.typ": vb
#import "../lib/code.typ": isaconst, isai, isalocale, isathm, isatype, listing, oblig, thy-badge
#import "../lib/math.typ": *
#import "../lib/sources.typ": thy
#import "../lib/figures.typ": call-edge, entry-node, intra-edge, ppoint, snapshot-var
#import "../lib/claims.typ": claim-ref

= What an Analysis Supplies <ch:analysis-interface>

@ch:domains ended with laws about one abstract state. The obligations of @ch:traces, however, speak about edges, calls, and contexts.
Most of what connects the two is the same for every analysis, namely the
equations built from the control-flow graph, the calling contexts, and the
solver. Sign and Interval differ only in the abstract effect of each program
construct. Goblint therefore separates an analysis from the framework that
runs it @seidl26[§6], and Voblint makes the same split in its program and in
its proof. An analysis supplies a record of abstract operations and proves the
analysis contract about them, and the framework then discharges the
obligations of @ch:traces once for every analysis.

== Transfers at edges and calls <sec:calls>

An ordinary edge of the control-flow graph carries an action $a$, such as an
assignment or a guard, whose concrete meaning @ch:program-model fixes. For a
store $s$, #isai("edge_step a s") is the set of stores the edge can produce.
An analysis describes the stores at a program point by an abstract state $d$
and supplies, for each action $a$, an abstract transfer $asem(a)$. The
transfer is sound if it loses no successor:
$ s in conc_(D)(d) and s' in #isai("edge_step a s") ==> s' in conc_(D)(asem(a) med d). $
This is the abstract counterpart of the obligation #oblig("INTRA") of
@ch:traces for one edge. Unlike Saan's abstract operators @saan26phd[§2.4.2],
it does not require strictness, $asem(a) med lbot = lbot$. The interface has
one transfer per kind of action, named after the corresponding method of
Goblint's `Spec`.

A call cannot be handled by one such transfer. After it returns, the caller's
own locals are the ones from before the call, while the globals and the result
come from the callee (#oblig("RETURN")). The abstract return must therefore see
both sides. As in Goblint, an analysis supplies two operations at a call.
_Enter_ (#isaconst("dgs_enter")) gives the abstract state the callee starts
from, and _combine_, in two stages, gives the caller's state after the call.
Take one call:

#listing(lang: "c", ```
global i32 g;
fun i32 inc(i32 a) { g = g + a; return a - 1; }
fun main() { g = 1; i32 x = 5; i32 y = inc(x); }
```)

At the call `y = inc(x)`, enter describes two stores. The _entry state_ $e$
describes the store the callee starts with (`g = 1`, `a = 5`). The _resume
state_ $q$ describes the caller's store (`x = 5`, `g = 1`), which combine later
merges with the callee's exit state $r$ (@fig:return-stores).

// The call `y = inc(x)` on the control-flow graph, as the playground draws it,
// with the store at each of the four nodes around the call. The combined state
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
      intra-edge(<c-pp5>, <c-pp6>, label: $q$, label-side: right),
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

Combine runs in the two stages of Goblint's `Spec`, mirroring the concrete
return of @sec:pstep. The first stage, $sh("combine_env")$, merges the caller's
locals from $q$ with the callee's globals from $r$, as #isaconst("combine_env")
does for stores. The second stage writes the callee's
result to the call's destination, here `y`, as #isaconst("combine_assign") does
for stores. Soundness is stated for the two
stages together (@sec:sound-core), so an analysis may divide the work between
them as it likes.

For soundness, enter must return a resume state that covers the caller's
store and an entry state that covers the entered store
(#isaconst("entry_pairs_cover")). Like Goblint's `enter`, it may return several
such pairs, which Goblint's
#link(
  "https://github.com/goblint/analyzer/blob/5320a6b741e50dc049f7a1b85e1709e9565cc54a/src/lifters/specLifters.ml#L722",
)[path-sensitivity lifter]
uses to return one pair per path @apinis14[§5.7]. Every analysis shipped with
Voblint returns a single pair, so path-sensitive analyses remain future work.

== Facts without a program point #thy-badge("Voblint_Framework", "DG_Manager") <sec:shared-facts>

Not every fact belongs to one program point. An analysis may keep, for
example, one range for a global variable `g` that holds throughout the run.
Seidl et al. describe a Goblint analysis with two domains @seidl26[§6]. The
local domain $D_L$ holds facts per program point and context, and $D_G$ holds
the values of _analysis globals_, which are unknowns without a program point.
An assignment to `g` publishes its value to the analysis global of `g` as a
side effect, and an edge that reads `g` depends on that unknown. Goblint's
#link(
  "https://github.com/goblint/analyzer/blob/5320a6b741e50dc049f7a1b85e1709e9565cc54a/src/framework/analyses.ml#L168",
)[`Spec`]
accordingly declares a local lattice `D` and a global lattice `G`.

The word _global_ thus has two meanings. A _program global_ is a variable of
the VIMP program, and an analysis global is a fact the analysis keeps
flow-insensitively. The two are independent. By default, the numeric analyses
keep program globals in the local state and use no analysis global.

In Goblint, a transfer reads and publishes analysis globals through a
#link(
  "https://github.com/goblint/analyzer/blob/5320a6b741e50dc049f7a1b85e1709e9565cc54a/src/framework/analyses.ml#L142",
)[_manager_]
argument, which also gives it the current local state. For example,
`man.sideg g d` publishes `d` to `g`, and the framework passes such
publications to the solver @seidl26[§6]. Voblint adopts this design, and its
transfers (#isatype("man_transfer")) receive a manager instead of a local
state. A Voblint manager holds the local state $d$ at the edge's source, a
function that reads the value of an analysis global, a function that publishes
a value to one, and a function that asks other analyses
(@ch:cooperation). The transfer returns the new local state $d'$. The
framework records which analysis globals it read and what it published, and
turns the reads into dependencies of the edge's equation and the publications
into side effects. The equation of an edge therefore depends on an analysis
global only where its transfer reads it, and a transfer that is a pure
function of the local state reads only the state at the edge's source and
publishes nothing.

== The analysis contract #thy-badge("Voblint_Framework", "DG_Spec_Sound") <sec:sound-core>

The framework takes an analysis as one parameter, the record
#isatype("dg_spec") with one field per operation (@fig:dg-spec), namely the
edge transfers of @sec:calls, enter, the two combine stages, and a query
handler through which other analyses can ask it for facts. Of the edge
transfers, $sh("skip")$ handles an edge without effect,
$sh("assign")$ an assignment, $sh("branch")$ a guard, and $sh("special")$ a
call of a library function such as `__voblint_nondet_int`. $sh("body")$ handles
the edge from a procedure's entry node into its body, $sh("return")$ the edge
to its result node, which a `return e` or the end of the body takes, and
$sh("event")$ a check, which leaves the store unchanged.

#figure(
  {
    show raw.where(block: true): set text(size: 6.5pt)
    thy("dg_spec")
  },
  kind: image,
  placement: none,
  caption: [The declaration of #isatype("dg_spec"), lifted from the theory.
    Every field except the query handler carries, marked $sharp$, the name of
    the corresponding method of Goblint's `Spec`. The edge each transfer
    handles is given in the text. A #isatype("call_info") names the callee, its
    formals, the arguments, and the destination of a call.],
) <fig:dg-spec>

The goal is a fixed set of laws from which the obligations of @ch:traces
follow for every record that satisfies them. Most of them form the _analysis
contract_ #isalocale("analysis_contract"). Since a transfer may read analysis
globals, a local state alone no longer fixes which stores it describes. The
contract therefore uses a concretization $conc_(D G)(d, rho)$ of a local state
$d$ under an _environment_ $rho$, which maps every analysis global to its
value.
It states three laws. First, $conc_(D G)$ is monotone in both arguments
(#isathm("analysis_contract.gammaDG_mono")), which turns the solver's
inequalities into inclusions as $conc$ does for a domain. Second, the step law
(#isathm("analysis_contract.step_sound")), the counterpart of
#oblig("INTRA"), reads
$ s in conc_(D G)(d, rho) and s' in #isai("edge_step a s") ==> s' in conc_(D G)(d', rho ljoin p), $
where the manager hands the transfer the local state $d$ at the edge's source
and reads analysis globals from $rho$, and the transfer returns $d'$ and
publishes $p$ ($lbot$ wherever it publishes nothing). A transfer that publishes nothing thus
meets the condition of @sec:calls with $rho$ as a fixed parameter. Third, the
combine law (#isathm("analysis_contract.combine_sound")) is the counterpart
of #oblig("RETURN") in the same shape. It concerns the two combine stages run
one after the other. Given stores of the resume state $q$ and of the exit
state $r$, the combined state must describe the store that takes the caller's
locals from the first and the program globals and result from the second.
A transfer is a program that passes its result on to the rest of the
equation, so it could in principle do so twice or not at all, and what it
publishes would then be ill defined. A well-formedness premise
(#isaconst("dg_spec_wf")) requires every operation to pass its result on
exactly once. Beyond these laws, the contract asks the domains only
for a join semilattice with a least element, and never for a map from
variables to abstract values (@sec:rel-state).

The contract supplies the context-independent core of #oblig("INTRA") and
#oblig("RETURN"). #oblig("CALL") requires that the callee's entry covers the
entered store _in every context the policy admits for the call_. Entry
coverage provides the covering pair, but the context policy of @ch:traces
decides in which contexts it is analyzed, so the contract alone does not discharge
#oblig("CALL"). #oblig("TOTAL"), that every covered call reaches some context,
follows from the policy, and for entry-state contexts also from entry
coverage. #oblig("INIT") requires the analysis's initial state to cover the
initial stores, which the analysis discharges when it is registered
(#isathm("dg_analysis.place_init")).

== Program globals: flow-sensitive or flow-insensitive #thy-badge("Voblint_Framework", "DG_Keyed_Split_Spec") <sec:mixed-flow>

The contract leaves open where program globals are kept. By default they are
part of the local state, as in Goblint's default base analysis for
single-threaded programs
(#link("https://github.com/goblint/analyzer/blob/5320a6b741e50dc049f7a1b85e1709e9565cc54a/src/analyses/base.ml#L539")[`base.ml`],
@saan26phd[§5.6.1]). The other placement keeps each program global at an
analysis global of its own, written by side effects and read where it is used.
The analysis is then _mixed flow-sensitive_, flow-sensitive in the locals and
flow-insensitive in the globals.

// A value at `pp7`, after both calls, from the flow-sensitive Sign run.
#let _mf(var) = snapshot-var("mixed-flow-sign", "main_pp7_ctx0", var)
// The same value from the run with program globals on the shared channel.
#let _mfs(var) = snapshot-var("mixed-flow-sign-shared", "main_pp7_ctx0", var)

#listing(lang: "c", claim: "mixed-flow-sign", ```
global i32 Gx;
fun set() { Gx = 1; }
fun i32 get() { return Gx; }
fun main() { i32 x = 1; set(); i32 y = get(); }
```)

The flow-insensitive value of `Gx` must cover the initial `Gx = 0` (VIMP starts
every global at $0$, @sec:pstep) as well as
the 1 written by `set`. Sign therefore claims only #signval(_mfs("y")) for `y`
after `y = get()` (claim #claim-ref("mixed-flow-sign-shared")), although every
run ends with `y = 1`. Flow-sensitively, Sign carries #signval("+") from
`set`'s exit into `get`'s entry and derives #signval(_mf("y")) (claim
#claim-ref("mixed-flow-sign")). In sequential VIMP the flow-insensitive
placement can thus cost precision, and a guard on such a global refines
nothing, as in Goblint's non-relational
thread-modular analyses @saan26phd[§5.6.2]. The placement suits multithreaded
programs, where the simplest thread-modular analysis keeps shared globals
flow-insensitively @seidl26[§1, Ex. 4] @saan26phd[§5.3.1], which a threaded
extension of VIMP could build on.

Like Goblint and Apinis et al. @apinis12[§5] @seidl26[§3], the analyzer keeps
one unknown per program global, so a write that changes `g` destabilizes only
the right-hand sides that read `g` and their dependents. The placement is a
wrapper that the framework puts around an analysis that keeps no analysis
globals of its own, in the shipped analyzer the combination of all selected
analyses (@ch:cooperation). The wrapper adds the analysis globals itself. At
each edge it reads the program globals the edge mentions from their analysis
globals and publishes those the edge can write. The result meets the
analysis contract whenever the inner analysis is sound and the domain satisfies
monotonicity laws and a frame law for the globals a transfer does not assign
(#isathm("keyed_split_contract")). The combined analysis satisfies them
(#isathm("mcp_cs_keyed")), so #isathm("run_voblint_source_sound") covers this
placement.

The interface is modular. An analysis proves facts about its own operations
only, while context handling, equation construction, and solving are
implemented and proved once by the framework.
