#import "@preview/fletcher:0.5.8": diagram, edge, node
#import "../lib/theme.typ": vb
#import "../lib/code.typ": isaconst, isai, isalocale, isathm, isatype, listing, oblig
#import "../lib/math.typ": *
#import "../lib/theorems.typ": definition, theorem
#import "../lib/sources.typ": proved, thy
#import "../lib/figures.typ": call-edge, entry-node, intra-edge, ppoint

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
the description before the edge to the one after it. Two things in the program semantics need more. A call
cannot be handled as an ordinary edge transfer: after it returns, the caller's
own variables are the ones from before the call, and only the globals and the
result come from the callee, so the return must see both sides (@sec:calls).
Some facts, such as one flow-insensitive range for a global variable, belong to
no single program point, and an analysis must be able to read and extend them
from exactly the edges that use them (@sec:shared-facts).

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
with the same role: skip, assign, special, branch, body, return and event.

== The call boundary <sec:calls>

At a call, an analysis supplies two operations, as Goblint's `Spec` does:
_entry_, which gives the abstract value the callee starts from, and _return_,
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

Entry describes the two stores that exist at the call `y = inc(x)`, each by an
abstract value, an element of the domain $D_L$ of values the analysis keeps
per program point. The _entry value_ $e$
describes the store the callee starts with (`g = 1`, `a = 5`). The _resume
value_ $q$ describes the caller's store (`x = 5`, `g = 1`), which combine
later merges with the callee's exit (the theories call $q$ the
continuation). Usually $q$ is the caller's own abstract value at the call, but
an analysis may weaken it there, for example by forgetting facts the callee
may invalidate. @fig:return-stores shows both values and what the return makes
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
      _st((0, 0), [resume value $q$ \ describes #_from-s[`x = 5`], `g = 1`]),
      _st(
        (0, 2),
        [$sh("combine")(q, t^sharp)$ \ describes #_from-s[`x = 5`], #_from-t[`g = 6`], #_from-t[`y = 4`]],
      ),
      _st((5, 0), [entry value $e$ \ describes `g = 1`, `a = 5`]),
      _st(
        (5, 2),
        [exit value $t^sharp$ \ describes #_from-t[`g = 6`], `a = 5`, \ #_from-t[result $4$]],
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
    above, and the concrete store each abstract value must describe
    (schematic: the body of `inc` is drawn as one edge). Entry answers the
    resume value $q$ and the entry value $e$; after the callee is analyzed,
    combine merges $q$ with the callee's exit value $t^sharp$. The combined
    value must describe the caller's locals (blue) together with the callee's
    globals and result (green), as #isaconst("combine_collect") does.],
) <fig:return-stores>

The abstract return therefore receives two values, the caller's value and the
callee's exit value, like the abstract `combine` of the functional approach
@seidl12compiler[§2.6]. As in Goblint, it has two stages:
#isaconst("dgs_combine_env") merges the two environments, and
#isaconst("dgs_combine_assign") writes the result into the destination,
starting from the local value the first stage produced. Only their composition
carries an obligation, so a specification may do the whole return in either
stage.

The callee is analyzed from $e$, and its result is combined with $q$. Entry
must describe both stores: its resume value must cover the caller's store and
its entry value the entered store (#isaconst("entry_pairs_cover")). The
formalization, like Goblint's `enter`, lets entry answer a list of such pairs,
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
The numeric analyses of this thesis keep program globals in the local value and
need no analysis global (@sec:mixed-flow).

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
the seeds through which @ch:equations passes entry values to callees
(@sec:global-unknowns).

== The specification record <sec:spec-record>

The framework takes an analysis as one parameter, so its operations form
one record, #isatype("dg_spec"), with one field per operation (@fig:dg-spec). The seven edge transfers of
@sec:dg have type #isatype("man_transfer"). The entry of @sec:calls answers the
pair $(q, e)$, and the two return stages also receive the callee's exit value.
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
    Entry, return stages and query handler have their own transfer types over
    the same manager.],
) <fig:dg-spec>

== The analysis soundness contract <sec:sound-core>

Which facts must one analysis prove so that @ch:equations can discharge the
obligations of @ch:traces for it, once for every analysis? Most of them form
one locale, the _analysis soundness contract_
#isalocale("analysis_contract"). The contract speaks only
about the analysis's own objects: its record of operations, and a
concretization $conc_(D G)(d, g)$ that says which stores a local value $d$
describes, given the value $g$ of the analysis global. It mentions no context
and no solver. It asks for four things:

+ _Monotone meaning._ A larger value describes more stores: $conc_(D G)$ is
  monotone in both arguments (#isathm("analysis_contract.gammaDG_mono")). This turns the solver's inequalities between
  values into inclusions between sets of stores, as $conc$ does for a domain
  (@ch:domains).
+ _Well-formed programs._ Every transfer hands its result to its continuation
  exactly once (#isaconst("dg_spec_wf")), so what a compiled transfer
  publishes is well defined.
+ _Sound edges_ (#oblig("INTRA")). Take a store before an edge that the
  source's value covers, together with the current value of the analysis
  global. Every store the edge can produce must be covered by the value the
  compiled program answers, together with the value it publishes
  (#isathm("analysis_contract.step_sound")).
+ _Sound returns_ (#oblig("RETURN")). Take a caller store covered by the
  resume value and a callee exit store covered by the exit value. The store
  after the return must be covered by what the two return stages answer and
  publish (#isathm("analysis_contract.combine_sound")). This must hold at arbitrary values, because no unknown holds the
  resume value for the solver to bound.

A transfer is thus judged by what its compiled program answers and publishes,
however its reads and publications are arranged. The solver's certificate
bounds each analysis global by every publication to it (@sec:certificate), and
the solved values inherit the coverage.

The locale fixes the type of analysis-global names to `unit`, so an analysis
has exactly one global unknown, and $conc_(D G)(d, g)$ takes one value $g$.
@sec:mixed-flow shows what this single slot costs when several program globals
share it. Otherwise the contract asks the carriers only for a join semilattice
with a least element and $conc_(D G)$ only for monotonicity. It never requires
a map from variables to abstract values (@sec:relational).

The contract covers #oblig("INTRA") and #oblig("RETURN"), the two obligations
of @ch:traces that involve no context. @ch:equations derives the other three
from further premises. #oblig("CALL"), that the callee's entry covers the
entered store in the context the call enters, combines the analysis's
entry coverage (@sec:calls), a premise outside the locale, with the routing
policy. #oblig("TOTAL"), that every covered call reaches some context, comes
from the policy alone. #oblig("INIT") needs the initial abstract state to
cover the initial stores, an assumption the analysis's registration discharges
(#isathm("dg_analysis.init_sound")).
