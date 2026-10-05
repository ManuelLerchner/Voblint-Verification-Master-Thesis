#import "@preview/fletcher:0.5.8": diagram, edge, node
#import "../lib/theme.typ": vb
#import "../lib/code.typ": isaconst, isai, isalocale, isathm, isatype, listing, oblig
#import "../lib/math.typ": *
#import "../lib/theorems.typ": definition, theorem
#import "../lib/sources.typ": proved, thy
#import "../lib/figures.typ": (
  call-edge, dep-edge, entry-node, global-unk, intra-edge, ppoint, side-edge, snapshot-var,
  subfigures, unk,
)
#import "../lib/claims.typ": claim-ref

= What an Analysis Supplies <ch:analysis-interface>

@ch:traces reduced soundness to five obligations over sets of stores, and
@ch:domains supplied finite abstract states that represent such sets. An analysis connects
the two, but only part of an abstract interpreter is specific to it. Some parts
are the same for every analysis: the control-flow graph, the equations built
from it, the calling contexts and the solver. Others are what makes Sign differ
from Interval: what an assignment does to an abstract state, what a guard reveals
about the current state, and what a call passes to its callee. Goblint keeps
the two apart @seidl26[§5], and so does Voblint. An analysis is a plug-in that answers the
questions the program constructs pose, and the framework does the rest. The
soundness proof follows the same split: the framework's part is proved once,
in the chapters that follow, and a new analysis only shows that each of its
operations covers the corresponding concrete behaviour.

This chapter describes the plug-in: which questions it answers and what it has
to prove. The simplest plug-in would be one function per ordinary edge, from
the abstract state before the edge to the one after it. Two things in the program semantics need more. A call
cannot be handled as an ordinary edge transfer: after it returns, the caller's
own variables are the ones from before the call, and only the globals and the
result come from the callee, so the return must see both sides (@sec:calls).
Some facts, such as one flow-insensitive range for a global variable, belong to
no single program point, and an analysis must be able to read and extend them
from exactly the edges that use them (@sec:shared-facts). The program's own
globals can be kept this way, too (@sec:mixed-flow).

The plug-in follows Goblint's analysis specification, with one method for each
operation (@sec:spec-record). The correspondence is one of structure only.
What each operation means comes from the VIMP and CFG semantics of
@ch:program-model, and Goblint's OCaml code plays no part in it. @ch:equations
turns the plug-in's guarantees into the five obligations of @ch:traces.

== Edge transfers <sec:dg>

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
and publishes facts without a program point owes the same with their values
added on both sides (@sec:shared-facts). The kinds of action give an
analysis seven edge transfers, named after the methods of Goblint's `Spec`
with the same role: skip, assign, special, branch, body, return (for the
return statement) and event.

== The call boundary <sec:calls>

At a call, an analysis supplies two operations, as Goblint's `Spec` does:
_enter_, which gives the abstract value the callee starts from, and _combine_,
which gives the caller's value after the call. The solver analyzes the callee
in between. The concrete semantics of @ch:program-model fixes what the two
must approximate: #isaconst("call_enter") keeps the globals, resets the
callee's locals to $0$ and binds the formals, and #isaconst("combine_collect")
gives the caller its own locals, the callee's globals and the result
(#oblig("RETURN")). Take one call:

#listing(lang: "c", ```
global g;
fun inc(a) { g = g + a; return a - 1; }
fun main() { g = 1; x = 5; y = inc(x); }
```)

Enter describes the two stores that exist at the call `y = inc(x)`, each by an
abstract state, an element of the domain $D_L$ the analysis keeps
per program point. The _entry state_ $e$
describes the store the callee starts with (`g = 1`, `a = 5`). The _resume
state_ $q$ describes the caller's store (`x = 5`, `g = 1`), which combine
later merges with the callee's exit (the theories call $q$ the
continuation). Usually $q$ is the caller's own abstract state at the call, but
an analysis may weaken it there, for example by forgetting facts the callee
may invalidate. @fig:return-stores shows both values and what combine makes
of them.

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
  caption: [The analysis's operations at the call `y = inc(x)` of the program
    above, and the concrete store each abstract state must describe
    (schematic: the body of `inc` is drawn as one edge). Enter answers the
    resume state $q$ and the entry state $e$; after the callee is analyzed,
    combine merges $q$ with the callee's exit state $r$. The combined
    value must describe the caller's locals (blue) together with the callee's
    globals and result (green), as #isaconst("combine_collect") does.],
) <fig:return-stores>

Combine therefore receives two values, the caller's value and the
callee's exit state, like the abstract `combine` of the functional approach
@seidl12compiler[§2.6]. As in Goblint, it has two stages:
#isaconst("dgs_combine_env") merges the two environments, and
#isaconst("dgs_combine_assign") writes the result into the destination,
starting from the local value the first stage produced. Only their composition
carries an obligation, so a specification may do the whole combine in either
stage.

The callee is analyzed from $e$, and its result is combined with $q$. Enter
must describe both stores: its resume state must cover the caller's store and
its entry state the entered store (#isaconst("entry_pairs_cover")). The
formalization, like Goblint's `enter`, lets enter answer a list of such pairs,
each analyzed in a context of its own; every analysis in this thesis answers
one, and we describe that case.

== Facts without a program point <sec:shared-facts>

=== Analysis globals <sec:analysis-globals>

Not every fact belongs to one program point. Seidl et al. describe the
specification of a mixed flow-sensitive analysis in Goblint @seidl26[§6]. It
consists of the local domain $D_L$ of facts tracked per program point and
context, a set of _analysis globals_ with a domain $D_G$ of their values,
transfer functions for the basic statements, and `enter` and `combine` for
calls. An analysis global is an unknown of its own, without a program point.
If the range of a global variable `g` is analyzed flow-insensitively, an
assignment to `g` publishes its value to the unknown of `g` as a side effect
(@sec:side-effects), and an edge that reads `g` depends on that unknown.
Goblint's
#link(
  "https://github.com/goblint/analyzer/blob/5320a6b741e50dc049f7a1b85e1709e9565cc54a/src/framework/analyses.ml#L168",
)[`Spec`]
accordingly declares a local
lattice `D` and a global lattice `G`. The word _global_ thus has two meanings.
A _program global_ is a variable of the VIMP program, like a global variable in
C. An analysis global is a fact the analysis keeps flow-insensitively. The two
are independent: an analysis may track a program global flow-sensitively in its
local value, and an analysis global need not stand for any program variable.
By default the numeric analyses keep program globals in the local value and need
no analysis global. Under the other placement, each program global becomes an
analysis global named by the variable itself (@sec:mixed-flow).

=== Side-effecting transfers and the manager <sec:manager>

A transfer of a mixed flow-sensitive analysis still returns the next local
value, but it may also read analysis globals and publish new values to them:
it is _side-effecting_. In Goblint, a transfer does this through a
#link("https://github.com/goblint/analyzer/blob/5320a6b741e50dc049f7a1b85e1709e9565cc54a/src/framework/analyses.ml#L142")[_manager_]: an argument that gives it the current local value
and operations to read an analysis global and to publish to one, among
others. For example, `man.sideg g d` publishes `d` to the analysis global
`g`, and the framework passes such publications to the solver @seidl26[§6].
Voblint adopts this design with the manager's local value, reads, publications
and queries. Its transfer receives a manager instead of a local value, and
returns a program that computes the next local value and may read and publish
analysis globals on the way:
#{
  show raw.where(block: true): set text(size: 6.5pt)
  thy("man_transfer")
}
The manager is a record of type #isatype("man"):
#{
  show raw.where(block: true): set text(size: 6.5pt)
  thy("man")
}
Here `'dl` and `'dg` are the local and the global lattice, $D_L$ and $D_G$,
and `'v` names the analysis globals. #isaconst("man_local") is the current
local value. A #isatype("strategy_program") is a program that may read and
publish values before it yields its result, a strategy tree of @sec:td
(@fig:strategy-trees) that hands this result to a continuation, and `'x` and
`'k` name the unknowns it reads. The framework builds the manager
(#isaconst("mk_dg_man")): #isaconst("man_global") $v$ reads the current value
of the analysis global $v$, and #isaconst("man_sideg") $v$ $g$ publishes $g$
to it. Its #isaconst("man_ask") answers every query with $ltop$, and the
framework installs the analysis's own query handler over it (@ch:cooperation).

Dependencies therefore follow what a transfer actually does: the right-hand
side of an edge depends on an analysis global only if its transfer reads it. A
transfer built with #isaconst("local_transfer") from a function on local values
reads only the value at the edge's source and publishes nothing
(#isathm("sp_compile_transfer_program_local_transfer")). The numeric analyses
are built this way, so for them the manager changes nothing about the
equations. In the solver, analysis globals become global unknowns, next to
the seeds through which @ch:equations passes entry states to callees
(@sec:global-unknowns).

== The specification record <sec:spec-record>

The framework takes an analysis as one parameter, so its operations form
one record, #isatype("dg_spec"), with one field per operation (@fig:dg-spec). The seven edge transfers of
@sec:dg have type #isatype("man_transfer"). Enter (@sec:calls) answers the
pair $(q, e)$, and the two combine stages also receive the callee's exit state.
The query handler is the subject of @ch:cooperation. Every field has the role
of the Goblint method it is named after. A check `__voblint_check(c)` becomes
an edge whose action is an event (#isatype("analysis_event")), so the event
transfer sees it; Goblint handles `__goblint_check` in `special` instead.

#figure(
  {
    show raw.where(block: true): set text(size: 6.5pt)
    thy("dg_spec")
  },
  kind: image,
  placement: none,
  caption: [The declaration of #isatype("dg_spec"), lifted from the theory.
    Every field except the query handler carries, marked $sharp$, the name of
    the method of Goblint's `Spec` with the same role. A #isatype("call_info")
    names the callee, its formals, the arguments and the destination of a call.
    Enter, the combine stages and the query handler have their own transfer types over
    the same manager.],
) <fig:dg-spec>

== The analysis contract <sec:sound-core>

Which facts must one analysis prove so that @ch:equations can discharge the
obligations of @ch:traces for it, once for every analysis? Most of them form
one locale, the _analysis contract_
#isalocale("analysis_contract"). The analysis contract speaks only
about the analysis's own objects: its record of operations, and a
concretization $conc_(D G)(d, e)$ that says which stores a local value $d$
describes, given an _environment_ $e$ that maps each analysis-global name to
its value. It mentions no context and no solver. It asks for four things:

+ _Monotone meaning._ A larger value describes more stores: $conc_(D G)$ is
  monotone in both arguments, the environment ordered pointwise
  (#isathm("analysis_contract.gammaDG_mono")). This turns the solver's inequalities between
  values into inclusions between sets of stores, as $conc$ does for a domain
  (@ch:domains).
+ _Well-formed programs._ Every transfer hands its result to its continuation
  exactly once (#isaconst("dg_spec_wf")), so what a compiled transfer
  publishes is well defined.
+ _Sound edges_ (#oblig("INTRA")). Take a store before an edge that the
  source's value covers, together with the environment $e$ the transfer reads.
  Every store the edge can produce must be covered by the value the compiled
  program answers, together with $e$ joined with what the program publishes
  (#isathm("analysis_contract.step_sound")).
+ _Sound returns_ (#oblig("RETURN")). Take a caller store covered by the
  resume state and a callee exit store covered by the exit state, both against
  $e$. The store after the return must be covered by what the two combine
  stages answer, against $e$ joined with what they publish
  (#isathm("analysis_contract.combine_sound")). This must hold at arbitrary values, because no unknown holds the
  resume state for the solver to bound.

A transfer is thus judged by what its compiled program answers and publishes,
however its reads and publications are arranged. A transfer that changes no
analysis global owes no publication: the environment it read still describes
the result. The solver's certificate bounds each analysis global by every
publication to it (@sec:certificate), and the solved values inherit the
coverage.

The type `'v` of analysis-global names is a parameter of the locale. A key map
sends each name to its global unknown, and #isaconst("genv") reads the
environment off a valuation through that map. The edge and return obligations
quantify over every key map and every valuation, so the analysis never learns
how its names are laid out in the solver. An analysis with a single
global takes `'v` to be `unit`, and #isathm("analysis_contract_unitI") derives
the analysis contract from obligations stated against that one value. The analyzer
names analysis globals by program variables. Under flow-sensitive program
globals it never reads or publishes them, and under flow-insensitive ones each
variable's global holds that variable's value (@sec:mixed-flow). Otherwise the
analysis contract asks the carriers only for a join semilattice with a least element
and $conc_(D G)$ only for monotonicity. It never requires a map from variables
to abstract values (@sec:relational).

The analysis contract covers #oblig("INTRA") and #oblig("RETURN"), the two obligations
of @ch:traces that involve no context. @ch:equations derives the other three
from further premises. #oblig("CALL"), that the callee's entry covers the
entered store in the context the call enters, combines the analysis's
entry coverage (@sec:calls), a premise outside the locale, with the routing
policy. #oblig("TOTAL"), that every covered call reaches some context, comes
from the policy alone. #oblig("INIT") needs the initial abstract state to
cover the initial stores, an assumption the analysis's registration discharges
(#isathm("dg_analysis.init_sound")).

== Program globals as flow-insensitive unknowns <sec:mixed-flow>

// A value at `pp7`, after both calls, from the flow-sensitive Sign run.
#let _mf(var) = snapshot-var("mixed-flow-sign", "main_pp7_ctx0", var)
// The same value from the run with program globals on the shared channel.
#let _mfs(var) = snapshot-var("mixed-flow-sign-shared", "main_pp7_ctx0", var)

By default the shipped analyses keep program globals in the flow-sensitive
local value of every unknown, next to the locals. Goblint's base analysis makes the same
choice for single-threaded programs: it reads globals from its local state and
publishes nothing (#link("https://github.com/goblint/analyzer/blob/5320a6b741e50dc049f7a1b85e1709e9565cc54a/src/analyses/base.ml")[`base.ml`]).
The other placement keeps each program global at a global unknown of its own,
written by side effects and read where it is used: a _mixed flow-sensitive_
analysis, flow-sensitive in the locals and flow-insensitive in the globals.
The following program compares the two placements:

#listing(lang: "c", claim: "mixed-flow-sign", ```
global Gx;
fun set() { Gx = 1; }
fun get() { return Gx; }
fun main() { x = 1; set(); y = get(); }
```)

Flow-sensitively, the value of `Gx` travels with the state. It enters `set`
with the caller's state, comes back through the return combination and enters
`get` from `main`'s continuation, so every procedure's unknowns carry every
global. An analysis may instead keep one fact per global that holds throughout
the run: a flow-insensitive unknown written by side effects (@ch:background),
which the certificate (@sec:certificate) makes bound everything published to
it. The write in `set` then reaches the read in `get` through that fact. This
loses precision, because the fact must cover the initial `Gx = 0` as well as
the written 1. Sign can only claim #signval("≥0") for `Gx` and for `y` after
`y = get()`, although every run ends with `y = 1`. A flow-sensitive analysis
carries #signval("+") from `set`'s exit into `get`'s entry and derives
#signval(_mf("y")) for `y` (claim #claim-ref("mixed-flow-sign")).

For a sequential VIMP program the flow-insensitive placement only loses
precision, as here. Its purpose is the language VIMP could grow into. Seidl et
al. name multi-threaded code as a main source of mixed flow sensitivity: a
thread-modular analysis collects the values that threads exchange through
shared globals flow-insensitively, so that each thread's local state can be
tracked flow-sensitively without considering every thread that may run
concurrently @seidl26[§1, Ex. 4]. They also report that global store widening
improves scalability and helps incremental analysis @seidl26[§1]. Neither use
arises in VIMP, which has no threads. The placement shows that the framework
and its end-to-end theorem already carry a mixed flow-sensitive analysis:
program globals at global unknowns, written by side effects, read by name, and
covered by the source-level theorem. An extension of VIMP with threads would
reuse this machinery and add a thread semantics and synchronization
(@sec:outlook-extending).

The simplest lifter, #isaconst("ownership_split_lift"), adds one global unknown
$kappa$ whose value is an abstract store for all VIMP globals together. Every
lifted transfer reads the globals from $kappa$ and publishes the global half of
its result there. A solved store is read back by merging the local half with
$sol(kappa)$ (#isaconst("gamma_ownership_split")), and
#isathm("ownership_split_lift_contract") shows that the lifted specification
meets the analysis contract for every transfer bundle that satisfies
#isalocale("sound_nonrelational_transfer"). The values of different globals
stay apart inside $kappa$, since joins and widening act on each entry of the
store, but the solver sees one unknown (@fig:shared-deps-one). A write to `g`
therefore re-evaluates a node that reads only `h`, and the update rule decides
between widening and narrowing for the whole store (@sec:update-rules): while
`g` still grows, $kappa$ is widened, and `h` cannot be narrowed until `g` has
stabilized. Apinis et al., Seidl et al. and Goblint keep one unknown per global
@apinis12[§5] @seidl26[§3].

The analyzer does the same. Its lifter #isaconst("keyed_split_spec") keeps each
program global $x$ at its own unknown $ctor("Analysis_Global") thin x$
(@fig:shared-deps-per), so the analysis-global names are the program's
variable names. A transfer reads only
the globals its edge mentions (#isaconst("edge_global_reads")) and publishes
only the globals its edge may assign (#isaconst("edge_global_writes")), each
cut to the part of the result that describes that global. In place of every
global it does not read, the wrapped transfer receives a value that claims
nothing about it. A call reads the globals its arguments mention. The initial
value of each global is published by the program entry like any other write,
so the solved value of a global already includes its initialization. For two globals `g` and `h`,
#isathm("read_g_depends_on_g_only") and #isathm("write_h_publishes_h_only")
check this shape on one reading and one writing edge.

Skipping the unwritten globals is sound because a concrete step leaves them
unchanged (#isathm("edge_step_frame")). #isathm("keyed_split_contract")
turns this into the analysis contract over environments
(@sec:sound-core) for every sound local specification, given monotone
operations to recombine a local half with a global environment and to cut out
one global, and one frame law on the carrier: a store that the result
describes, and that agrees on every unwritten global with a store the read
environment describes, is described by the result's local half recombined
with the published globals and the read environment elsewhere. The combined
state of @ch:cooperation provides these operations field by field
(#isathm("mcp_keyed_dg_analysis")): a pointwise field splits each name by
where it is stored, and the order analysis's relation stays wholly local. The
routed obligations of @sec:eq-routing are discharged for this placement as for
the default one, for every program and under all three context policies. The
placement is therefore an analysis setting of #isaconst("run_voblint")
(#ctor("Program_Globals_Flow_Insensitive"), @sec:headline), and
#isathm("run_voblint_source_sound") covers it. The command-line interface and
the playground default to bounded narrowing under this placement.

On the program above the flow-insensitive placement leaves `y` at
#signval(_mfs("y")) after both calls (claim #claim-ref("mixed-flow-sign-shared")).
This bound is what the flow-insensitive `Gx` leaves.

// A straight-line procedure over two flow-insensitive globals g and h: which
// right-hand sides read (grey) and publish to (double tip) the global unknowns,
// and which nodes the solver re-evaluates when g = g + 1 publishes (orange).
// (a) one global unknown for all globals (ownership_split_lift); (b) one global
// unknown per global, as in Voblint's flow-insensitive placement and Goblint.
#let _deps(split) = {
  set text(size: 8pt)
  let hot = if split { (2,) } else { (2, 3) }
  let pt(i) = if i in hot {
    unk((0, i), $u_#i$, state: "unstable", name: label("u" + str(i)))
  } else { ppoint((0, i), $u_#i$, name: label("u" + str(i))) }
  let edges = (
    intra-edge(<u0>, <u1>, label: "x = x + 1", label-side: right),
    intra-edge(<u1>, <u2>, label: "g = g + 1", label-side: right),
    intra-edge(<u2>, <u3>, label: "y = h", label-side: right),
  )
  if split {
    diagram(
      spacing: (10mm, 9mm),
      ..range(4).map(pt),
      global-unk((1.5, 1.6), $kappa_g$, name: <kg>),
      global-unk((1.5, 3), $kappa_h$, name: <kh>),
      ..edges,
      dep-edge(<kg>, <u2>, bend: 18deg),
      side-edge(<u2>, <kg>, bend: 18deg),
      dep-edge(<kh>, <u3>, bend: 18deg),
    )
  } else {
    diagram(
      spacing: (10mm, 9mm),
      ..range(4).map(pt),
      global-unk((1.5, 2), $kappa$, name: <k>),
      ..range(4).map(i => node((-0.75, i), text(fill: vb.muted, $(d_#i, bot)$))),
      node((2.1, 2), text(fill: vb.muted, $(bot, v)$)),
      ..edges,
      dep-edge(<k>, <u2>, bend: 18deg),
      side-edge(<u2>, <k>, bend: 18deg),
      dep-edge(<k>, <u3>, bend: 18deg),
    )
  }
}

#subfigures(
  figure(_deps(false), caption: [one global unknown $kappa$ for `g` and `h`]),
  <fig:shared-deps-one>,
  figure(_deps(true), caption: [one global unknown per global]),
  <fig:shared-deps-per>,
  columns: (1.2fr, 1fr),
  placement: auto,
  caption: [The right-hand sides that depend on the global unknowns of two
    flow-insensitive globals `g` and `h` (schematic). Grey arrows are reads
    (#ctor("QueryG")), purple double-tipped arrows publications (#ctor("Side")),
    and orange nodes are re-evaluated when `g = g + 1` enlarges the value of
    `g`; $u_1$, after `x = x + 1`, depends on no global. With one global
    unknown for all globals (a), the write to `g` also re-evaluates $u_3$,
    which reads only `h`. With one global unknown per global (b), as in
    Voblint's flow-insensitive placement and in Goblint, it does not. In (a)
    each unknown holds a #isatype("dg_state") (grey).],
  label: <fig:shared-deps>,
)

The update rule is chosen once per run, for the seeds and every global
together (@sec:update-rules). @ch:related compares the instance with earlier
mechanizations of mixed flow sensitivity. The lifter wraps the state that the
active analyses share, and @ch:cooperation describes how several analyses
combine into that state.
