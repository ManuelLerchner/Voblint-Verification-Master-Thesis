#import "@preview/fletcher:0.5.8": diagram, node
#import "../lib/theme.typ": vb
#import "../lib/code.typ": isaconst, isai, isalocale, isathm, isatype, listing, oblig
#import "../lib/math.typ": *
#import "../lib/sources.typ": thy
#import "../lib/figures.typ": call-edge, entry-node, intra-edge, ppoint, snapshot-var
#import "../lib/claims.typ": claim-ref

= What an Analysis Supplies <ch:analysis-interface>

@ch:domains ended with laws about one abstract state. Its order agrees with
its meaning, and its operations over-approximate the concrete ones. The
obligations of @ch:traces, however, speak about edges, calls and contexts.
Most of what connects the two is the same for every analysis, namely the
equations built from the control-flow graph, the calling contexts and the
solver. What
makes Sign differ from Interval is only the abstract effect of each program
construct. Goblint therefore separates an analysis from the framework that
runs it @seidl26[§6], and Voblint makes the same split in its program and in
its proof.

This chapter describes what an analysis must supply, and what it must prove
about it, so that the framework can discharge the obligations of @ch:traces
once for every analysis. An analysis supplies a record of abstract operations,
and the analysis contract states what they must preserve.

== Transfers at edges and calls <sec:calls>

An ordinary edge of the control-flow graph carries an action $a$, such as an
assignment or a guard, whose concrete meaning #isaconst("edge_step") is fixed
by @ch:program-model. For a store $s$, #isai("edge_step a s") is the set of
stores the edge can produce. An analysis describes the stores at a program
point by an abstract state $d$ of its _local domain_ $D_L$ (@sec:shared-facts) and
supplies, for each action $a$, an abstract transfer $sh(f)_a$. The transfer is
sound if it loses no successor:
$ s in conc_(D)(d) and s' in #isai("edge_step a s") ==> s' in conc_(D)(sh(f)_a (d)). $
This is the abstract counterpart of the obligation #oblig("INTRA") of
@ch:traces for one edge. The interface has one transfer per kind of action,
named after the corresponding method of Goblint's `Spec` (@fig:dg-spec).

A call cannot be handled by one such transfer. After it returns, the caller's
own locals are the ones from before the call, while the globals and the result
come from the callee (#isaconst("combine_collect"), #oblig("RETURN")). The
abstract return must therefore see both sides. As in Goblint, an analysis
supplies two operations at a call. _Enter_ (#isaconst("dgs_enter")) gives the
abstract state the callee starts from, and _combine_
(#isaconst("dgs_combine_env"), #isaconst("dgs_combine_assign")) gives the
caller's state after the call. Take one
call:

#listing(lang: "c", ```
global g;
fun inc(a) { g = g + a; return a - 1; }
fun main() { g = 1; x = 5; y = inc(x); }
```)

Enter describes two stores associated with the call `y = inc(x)`. The _entry state_ $e$
describes the store the callee starts with (`g = 1`, `a = 5`). The _resume
state_ $q$ describes the caller's store (`x = 5`, `g = 1`), which combine later
merges with the callee's exit state $r$ (the theories call $q$ the
continuation). @fig:return-stores shows $q$, $e$ and $r$ and the state combine
computes from $q$ and $r$.

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

For soundness, enter must answer a pair of a resume state that covers the
caller's store and an entry state that covers the entered store
(#isaconst("entry_pairs_cover")). Like Goblint's `enter`, it may answer several
such pairs. Goblint's
#link(
  "https://github.com/goblint/analyzer/blob/5320a6b741e50dc049f7a1b85e1709e9565cc54a/src/lifters/specLifters.ml#L722",
)[path-sensitivity lifter]
uses this to return one pair per path. Every analysis shipped with Voblint
answers a single pair, and only a test example of @ch:traces answers two, so
path-sensitive analyses remain future work.

== Facts without a program point <sec:shared-facts>

Not every fact belongs to one program point. An analysis may keep, for
example, one range for a global variable `g` that holds throughout the run.
Seidl et al. describe a Goblint analysis with two domains @seidl26[§6]. The
local domain $D_L$ holds facts per program point and context, and $D_G$ holds
the values of _analysis globals_, which are unknowns without a program point. An assignment to `g`
publishes its value to the analysis global of `g` as a side effect, and an
edge that reads `g` depends on that unknown. Goblint's
#link(
  "https://github.com/goblint/analyzer/blob/5320a6b741e50dc049f7a1b85e1709e9565cc54a/src/framework/analyses.ml#L168",
)[`Spec`]
accordingly declares a local lattice `D` and a global lattice `G`.

The word _global_ thus has two meanings. A _program global_ is a variable of the VIMP program. An analysis global is a fact the
analysis keeps flow-insensitively. The two are independent. An analysis may
track a program global in its local state, and an analysis global need not
stand for any program variable. By default the numeric analyses keep program
globals in the local state and use no analysis global (@sec:mixed-flow).

A transfer that uses analysis globals still returns the next local state, but
it may also read and publish them on the way. In Goblint, it does this through
a
#link(
  "https://github.com/goblint/analyzer/blob/5320a6b741e50dc049f7a1b85e1709e9565cc54a/src/framework/analyses.ml#L142",
)[_manager_]
argument. The manager gives the transfer the current local state and
operations to read and publish analysis globals. For example, `man.sideg g d`
publishes `d` to the analysis global `g`, and the framework passes such publications to the solver @seidl26[§6]. Voblint adopts this
design. Its transfer (#isatype("man_transfer")) receives a manager of type
#isatype("man") instead of a local state. It reads an analysis global $v$ with
#isaconst("man_global") $v$ and publishes $d$ to it with #isaconst("man_sideg") $v$ $d$. As a result, the equations of @ch:equations depend on an analysis
global only where a transfer actually reads it. A transfer that is a pure function of the local state reads only the state at
the edge's source and publishes nothing
(#isathm("sp_compile_transfer_program_local_transfer")). By default, the
numeric analyses are of this kind.

== The analysis contract <sec:sound-core>

The framework takes an analysis as one parameter, the record
#isatype("dg_spec") with one field per operation (@fig:dg-spec): the edge
transfers of @sec:calls, enter, the two combine stages, and a query handler
that @ch:cooperation uses to let analyses exchange facts.

#figure(
  {
    show raw.where(block: true): set text(size: 6.5pt)
    thy("dg_spec")
  },
  kind: image,
  placement: none,
  caption: [The declaration of #isatype("dg_spec"), lifted from the theory.
    Every field except the query handler carries, marked $sharp$, the name of the corresponding method of Goblint's `Spec`. A #isatype("call_info")
    names the callee, its formals, the arguments and the destination of a
    call.],
) <fig:dg-spec>

The goal is that @ch:equations can derive the obligations of @ch:traces for
every record that satisfies a fixed set of laws. Most of them form the
_analysis contract_ #isalocale("analysis_contract"). Since a transfer may read
analysis globals, a local state alone no longer fixes which stores it
describes. The contract therefore uses a concretization $conc_(D G)(d, e)$ of
a local state $d$ under an _environment_ $e$, which maps every analysis global
to its value. The locale states three semantic laws and one technical premise:
#{
  show raw.where(block: true): set text(size: 6.5pt)
  thy("analysis_contract")
}
First, $tau$ is an arbitrary
valuation of the solver's unknowns and `key` maps each analysis global to its
unknown. Together they give the local state #isai("dg_local (\<tau> src)") at
the edge's source and the environment #isai("genv key \<tau>"), the $d$ and
$e$ above. Second, #isaconst("edge_out") and #isaconst("edge_pub") are the
local state a transfer returns and the environment of what it publishes, which
is $lbot$ at every unknown it does not publish to.
#isaconst("combine_out") and #isaconst("combine_pub") are the same for combine,
whose resume state is $q$ and whose exit state is $r$. Third, $cal(G)$ marks
the program globals, which #isaconst("combine_collect") takes from the callee.

#isathm("analysis_contract.gammaDG_mono") requires that a larger state or
environment describes more stores. This turns the solver's inequalities
between values into inclusions between sets of stores, as $conc$ does for a
domain (@ch:domains). #isathm("analysis_contract.step_sound") is the abstract counterpart of
#oblig("INTRA"). Every store the edge produces from a store described under
$e$ is described by the returned state under $e$ joined with the publications.
A transfer that publishes nothing thus meets the condition of @sec:calls with
$e$ as a fixed parameter. #isathm("analysis_contract.combine_sound") is the counterpart of
#oblig("RETURN") in the same shape. Finally,
#isaconst("dg_spec_wf") requires that the program of every operation runs
its continuation exactly once, so what it publishes is well defined. Beyond
these laws, the contract asks the domains only for a join semilattice with a
least element, and never for a map from variables to abstract values
(@sec:relational).

The contract supplies the context-independent core of #oblig("INTRA") and
#oblig("RETURN"). #oblig("CALL") requires that the callee's entry covers the entered
store _in the context the call enters_. Entry coverage
(#isaconst("entry_pairs_cover")) provides the covering pair, but the routing
policy chooses the context in which it is analyzed, so @ch:equations combines
the two. #oblig("TOTAL"), that every covered call reaches some context, follows from
the policy, and for entry-state contexts also from entry coverage
(@sec:eq-routing). #oblig("INIT") requires the analysis's initial state
$d_0$ to cover the initial stores, which the analysis discharges when it is
registered (#isathm("dg_analysis.init_sound")).

== Program globals: flow-sensitive or flow-insensitive <sec:mixed-flow>

The contract leaves open where program globals are kept. By default, program globals are part of the local state,
as in Goblint's default base analysis for single-threaded programs
(#link("https://github.com/goblint/analyzer/blob/5320a6b741e50dc049f7a1b85e1709e9565cc54a/src/analyses/base.ml#L539")[`base.ml`]).
The other placement keeps each program global at an analysis global of its
own, written by side effects and read where it is used. The analysis is then
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

The flow-insensitive value of `Gx` must cover the initial `Gx = 0` as well as
the 1 written by `set`. Sign therefore claims only #signval(_mfs("y")) for `y`
after `y = get()` (claim #claim-ref("mixed-flow-sign-shared")), although every
run ends with `y = 1`. Flow-sensitively, Sign carries #signval("+") from
`set`'s exit into `get`'s entry and derives #signval(_mf("y")) (claim
#claim-ref("mixed-flow-sign")). In sequential VIMP the flow-insensitive
placement can thus cost precision. It is particularly useful for multi-threaded programs, where a thread-modular
analysis keeps the values that threads exchange through shared
globals flow-insensitively @seidl26[§1, Ex. 4]. VIMP has no threads, but a future extension of VIMP with threads could build on this placement
(@sec:outlook-extending).

Like Goblint and Apinis et al. @apinis12[§5] @seidl26[§3], the analyzer keeps
one unknown per program global, so a write that changes `g` destabilizes only the right-hand sides that read
`g` and those that depend on them. #isathm("keyed_split_contract") shows that this
placement meets the analysis contract whenever the wrapped analysis is sound and the domain satisfies monotonicity
laws and a frame law for the globals a transfer does not assign, which the analyzer's combined
state does (#isathm("mcp_keyed_dg_analysis")). #isathm("run_voblint_source_sound")
therefore covers it.

An analysis thus supplies a record of abstract operations, and the analysis
contract states what these operations must preserve. The interface is modular, since an analysis proves facts about its own
operations only, while context handling, equation construction and solving are
implemented and proved once by the framework. @ch:cooperation combines
several such analyses into one.
