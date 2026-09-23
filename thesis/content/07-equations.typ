#import "@preview/fletcher:0.5.8": diagram, edge, node
#import "../lib/theme.typ": vb
#import "../lib/code.typ": isaconst, isai, isalocale, isathm, isatype, listing, oblig
#import "../lib/math.typ": *
#import "../lib/theorems.typ": theorem
#import "../lib/figures.typ": snapshot-var
#import "../lib/claims.typ": claim-snapshot, snapshot-cluster-of, snapshot-verdict
#import "../lib/sources.typ": proved

// A verdict or state of a registered CLI claim (shared/claims.toml), read from
// the checked output rather than typed.
#let _cli(name, cond, col) = {
  let cells = read("/shared/generated/" + name + ".txt")
    .split("\n")
    .map(l => l.trim().split(regex("\s{2,}")))
    .find(c => c.len() == 5 and c.at(2) == cond)
  assert(cells != none, message: "claim " + name + " has no check " + cond)
  raw(cells.at(col))
}

= Equations, Contexts, and Routing <ch:equations>

@ch:traces reduced soundness to five local obligations on a claim
#isai("cover v c"), and @ch:analysis-interface supplied the abstract
operations. The claim still has to be computed, and there are three problems
with doing so. One unknown per node, the intraprocedural recipe, merges the
calls of a procedure and loses facts that every execution satisfies
(@sec:eq-coarse). A callee's entry cannot list the calls that reach it,
because which calls route to a context is known only once their callers are
solved (@sec:eq-seed). The equations compute contexts from abstract entry
values, while the obligations speak about contexts that the relation $R$
admits for concrete calls (@sec:eq-routing). This chapter builds an equation
system that meets all three, for every domain and context policy, whose
post-solutions $sol$ satisfy, for every node $v$ and context $c$,
$
  #isai("activation_collect \<G> R startcontext g S v c") subset.eq conc(sol(v, c)).
$
It serves RQ2, by linking computed contexts to admitted ones, and RQ3, by
proving the obligations once for all policies. The running example is
`bump(5); bump(4)` of @fig:program-to-equations, with call nodes $u_1$, $u_2$
(`pp2`, `pp3`) and continuations $k_1 = u_2$, $k_2$ (`pp4`).

== One unknown per node is too coarse <sec:eq-coarse>

The intraprocedural recipe of @ch:background keeps one unknown per CFG node.
Extended naively to calls, the entry of `bump` joins both call sites and holds
$n in {4, 5}$ at best, the return at $k_1$ assigns $a in {5, 6}$, and the check
`a == 6` fails although every execution satisfies it: the analyzer without
contexts reports #_cli("pg-contexts-none", "a == 6", 3) with
#_cli("pg-contexts-none", "a == 6", 4). The lower bound $-infinity$ comes from
widening the shared entry value (@sec:eq-seed). The collecting semantics
already assigns the two activations to different contexts
(@tab:bump-buckets), and the fix gives the unknowns the same index.

== Unknowns indexed by node and context <sec:eq-unknowns>

A local unknown is a pair $(v, c)$, and $sol(v, c)$ is the state claimed for
activations of context $c$ at node $v$. Contexts are activation-stable
(@sec:contexts), so the right-hand side of $(v, c)$ reads its local predecessors
at the same $c$, and #oblig("INTRA") follows from edge-transfer soundness
before any context policy is chosen. The generator #isaconst("routed_node_rhs")
joins one contribution per incoming local edge, one per call whose continuation
is $v$, the initial state at the program entry, and, at a callee entry, the
read of its seed (@sec:eq-seed). The call contributions decide where the
second index comes from.

The index also fixes how a return finds its caller. The contribution of a call
at $u$ to its continuation $(k, c)$ reads the caller's value at $(u, c)$, a key
that already exists because the caller was analyzed there. The return
therefore resumes the caller's context and never reconstructs it from the
callee's. For call strings of length $k$ this matters: truncation drops the
oldest call site, and recovering it on return would require joining every
caller compatible with the truncated string. Keeping the caller's context in
the continuation's key removes that step. Goblint's local unknowns have the
same shape, a node paired with a context (@app:goblint-alignment).

== A call reads and writes several unknowns <sec:eq-call>

A call contributes to its continuation $(k_1, c)$ by the protocol of
@sec:calls. The unknown it reads last depends on the caller
value it read first, so a dependency graph derived from CFG edges cannot list
it. The solver's equations are therefore #isatype("strategy_tree")s: an answer,
a local or shared query followed by a function of the value read, or a side
effect followed by a further tree. Each contribution of the generator is
written as a small program over reads of unknowns (#isatype("strategy_program")),
and the generator joins their results and compiles them into one tree. For a
single callee the call contribution is
$
  italic("call") & = #ctor("QueryL") thin (u_1, c) thin (lambda d. thick
                     scripts(lJoin)_((q, e) in enterh(d)) thin t_(q, e)), \
        t_(q, e) & = #ctor("Side") thin (italic("Seed")(italic("bump"), c'), e) thin
                   (#ctor("QueryL") thin (ctor("FunctionResult") thin italic("bump"), c') \
                 & #h(4em) (lambda r. thick
                     #ctor("Answer") thin combineassignh(combineenvh(q, r))))
$
with $c' = ctxh(u_1, c, e)$. Generating this equation never enters the callee:
it names the callee's keys and nothing else, so recursion needs no special
case. An alternative whose entry value $e$ is bottom publishes no seed and
reads no exit; its program combines $q$ with a bottom callee result. Apinis et
al. add the same test so that procedures which are not called are not analyzed
@apinis12, and Goblint's call handling applies it as well. The shortcut needs
one assumption of the routed locale: a value the test classifies as bottom
concretizes to the empty set, so the test never skips a concrete call.
@fig:eq-unknowns shows the resulting unknowns. Under entry-state contexts
the analyzer separates the two copies and reports
#_cli("pg-contexts-entry", "a == 6", 3) for `a == 6` with
#_cli("pg-contexts-entry", "a == 6", 4), and likewise for `b == 5`.

#let _loc(pos, body) = node(
  pos,
  text(0.8em, body),
  stroke: 0.7pt + vb.accent,
  fill: vb.accent.lighten(93%),
  corner-radius: 2pt,
  inset: 4pt,
)
#let _seed(pos, body) = node(
  pos,
  text(0.8em, body),
  stroke: 0.7pt + vb.called,
  fill: vb.called.lighten(93%),
  corner-radius: 7pt,
  inset: 4pt,
)
#let _read(a, b, lab, side: left) = edge(
  a,
  b,
  "-|>",
  stroke: 0.7pt + vb.neutral,
  label: text(7.5pt, fill: vb.neutral, lab),
  label-side: side,
)
#let _pub(a, b, lab, side: left) = edge(
  a,
  b,
  "-|>",
  stroke: (paint: vb.called, thickness: 0.7pt, dash: "dashed"),
  label: text(7.5pt, fill: vb.called, lab),
  label-side: side,
)

#let _b = $italic("bump")$

#figure(
  placement: auto,
  diagram(
    spacing: (18mm, 8mm),
    _seed((0, 0), $italic("Seed")(#_b, c_1)$),
    _loc((0, 1), $(ctor("FunctionEntry") thin #_b, c_1)$),
    _loc((0, 2), $(ctor("FunctionResult") thin #_b, c_1)$),
    _loc((1.3, 0), $(u_1, c_0)$),
    _loc((1.3, 2), $(k_1, c_0) = (u_2, c_0)$),
    _loc((1.3, 5), $(k_2, c_0)$),
    _seed((2.6, 3), $italic("Seed")(#_b, c_2)$),
    _loc((2.6, 4), $(ctor("FunctionEntry") thin #_b, c_2)$),
    _loc((2.6, 5), $(ctor("FunctionResult") thin #_b, c_2)$),
    _read((1.3, 0), (1.3, 2), [caller]),
    _read((1.3, 2), (1.3, 5), [caller], side: right),
    _read((0, 0), (0, 1), [seed read], side: right),
    _read((0, 1), (0, 2), [local], side: right),
    _read((0, 2), (1.3, 2), [result], side: right),
    _read((2.6, 3), (2.6, 4), [seed read]),
    _read((2.6, 4), (2.6, 5), [local]),
    _read((2.6, 5), (1.3, 5), [result]),
    _pub((1.3, 2), (0, 0), $n = 5$, side: right),
    _pub((1.3, 5), (2.6, 3), $n = 4$),
  ),
  caption: [Unknowns of the running example when the two calls reach
    different contexts $c_1 != c_2$ (`main` runs in $c_0$). A solid arrow: the
    right-hand side at its head reads the unknown at its tail. A dashed arrow:
    the right-hand side at its tail publishes to the shared key at its head.
    Under the unit context the two copies coincide and one seed receives both
    publications. Drawn from the equation definitions.],
) <fig:eq-unknowns>

== The callee entry reads a published seed <sec:eq-seed>

The entry unknown $(ctor("FunctionEntry") thin p, c')$ has no local
predecessors, and which call sites route to $c'$ is known only once their
caller values are, so its right-hand side cannot enumerate its contributors.
Side-effecting systems reverse the direction: each caller contributes to the
callee's entry while evaluating its own equation (@ch:background).

Apinis et al. side-effect the entered state directly into the start unknown of
the callee in the selected context @apinis12, and Goblint does the same with a
side effect on a local unknown. The reused solver's #ctor("Side") targets
shared keys only, and adding local side effects would mean forking the solver
and redoing its partial-correctness proof. Voblint instead publishes
$e$ at a shared key #isaconst("Activation_Seed") indexed by callee entry and
context, written $italic("Seed")(p, c')$, and the entry equation reads it back.
The seed is a shared substitute for the start unknown.

Publishing does not make the solver analyze the callee. #ctor("Side") joins its
value into the key and destabilizes the key's readers. It reads nothing, and
the solver adds an unknown to the demanded set only when some right-hand side
reads it. The callee is demanded by the exit read that follows the
publication, #ctor("QueryL") $(ctor("FunctionResult") thin p, c')$. Solving
that unknown reaches the entry through local dependencies, and the entry
equation reads the seed, which the publication has already filled.

Context selection and publication use the same entered value $e$. A route
computed from any other value, such as the caller's own state or a frame
entered against bottom globals, stores the seed at a context its value does
not belong to whenever the entry transfer reads globals. The regressions
#isathm("w0_seed_at_entered_frame") and #isathm("w0_no_seed_at_caller_frame")
evaluate one call with such an entry transfer: the seed is published at the context of
the entered frame, and nothing is published at the context the caller's state would
select.

The proxy has two costs. It adds one shared unknown per callee entry and
context and one update per call. It also changes where widening happens. A
seed has no equation of its own, and #isaconst("run_voblint") merges
contributions into it with the update rule selected for shared keys, so under
a warrowing rule a seed can be widened. In @sec:eq-coarse the first call
contributes $n in [5, 5]$ to the one seed of `bump` and the second
$n in [4, 4]$. Their join $[4, 5]$ is not below $[5, 5]$, so the rule widens
the lower bound to $-infinity$. Neither contribution changes afterwards, and the
rule leaves the key untouched when an origin repeats its contribution, so no
narrowing step recovers the bound. No operational equivalence with Goblint's
fixpoint is claimed; @app:goblint-alignment records the deviation.

== Routing a concrete activation to a context <sec:eq-routing>

#oblig("CALL") and #oblig("TOTAL") refer to the relation $R$ of @sec:contexts,
which admits contexts for concrete calls, while the equations publish only at
contexts that $ctxh$ computes from abstract entry values. The locale
#isalocale("routed_context_base_hetero") links the two by two per-instance
obligations. _Adequacy_: whenever $R$ admits $c'$ for a real call from a covered
caller store $s$, the entry answer contains a pair $(q, e)$ that covers $s$ and
the entered store in the paired sense of @sec:calls, and whose entry routes to
exactly $c'$, a context whose callee entry lies in the key set. _Totality_:
every covered call admits some context. Taking the context from the covering
pair keeps a proof from reading one pair's callee result into another pair's
resume value.

For a functional policy totality is immediate, and so is the part of adequacy
that fixes the context. The unit policy sends every call to $()$. A call
string of length $k$ is updated by #isaconst("cs_route") from the call site and
the caller's context alone, and the concrete side applies the same term
(#isathm("cs_route_context_agree")), so every alternative routes to the
admitted context. The rest of adequacy still needs a proof: some alternative
must cover
the caller store and the entered store, which is the paired entry coverage of
@ch:analysis-interface, and the routed entry key must lie in the key set.

An entry-state context is the list of abstract values of the callee's formal
parameters in the entered state (#isaconst("exec_formals_route")). Globals and
other locals do not take part. This is an instance of the partial contexts of
Apinis et al., where calls are distinguished by one component of the reaching
abstract state and merged on the others @apinis12. Such a context cannot be a
function of the concrete call. Abstracting the concrete entered store would
select a context at which no seed was published. If the caller's solved value
only knows $n in [4, 5]$, a concrete call with $n = 4$ is routed to the context
$[4, 5]$, while its own entered store abstracts to $[4, 4]$. Moreover, an
entry operation may answer one call with several overlapping alternatives
(@sec:cover).

The relation #isaconst("routed_entry_context_rel") therefore reads the contexts
off the solution. It takes the solved table as a parameter and admits $c'$ for
a concrete call exactly when some alternative of the entry answer at the
caller's solved value covers the call and routes to $c'$. No decoder of
concrete stores is needed, and a seed exists at every admitted context because
the analyzer published one there. The covering and routing parts of adequacy
hold by definition, the key-set part follows from closure of the key set, and
totality is paired entry coverage. The shipped relation
#isaconst("admitted_contexts") instantiates it with the one-alternative entry
of every selectable analysis. For entry-state policies the context-indexed
collecting semantics that the theorem below bounds is thus indexed by the
analyzer's own solution. The source-level theorem of @ch:results is stated over
the context-free collecting semantics, so this dependence does not reach it.

The policy decides which calls share an unknown, and with it what the analysis
can prove (@fig:eq-policies). A call string of length one keeps the two calls
of `wrap` apart but merges them in `scale`, because both arrive from the same
site. Length two and entry-state routing keep them apart down to `scale`.
@sec:eval-rq4 reports a machine-checked strict separation of this kind between
lengths one and two for one program.

#let _policy(name, title) = {
  let s = claim-snapshot(name)
  let procs = ("main", "wrap", "scale")
  let shown = s.clusters.filter(c => c.proc in procs)
  let ctxlabel(c) = {
    let t = c.ctx
    if t == "root context" { "root" } else if t.starts-with("call-string=") {
      t.slice("call-string=".len())
    } else { t }
  }
  let pos = (:)
  for (row, p) in procs.enumerate() {
    let copies = shown.filter(c => c.proc == p)
    for (i, c) in copies.enumerate() {
      pos.insert(c.id, (i - (copies.len() - 1) / 2, row))
    }
  }
  let pairs = ()
  for e in s.edges.filter(e => e.label.starts-with("enter ")) {
    let a = snapshot-cluster-of(s, e.src)
    let b = snapshot-cluster-of(s, e.dst)
    if a != none and b != none and a.id in pos and b.id in pos {
      // Calls from several sites into one copy share an arrow and list the sites.
      let site = s.nodes.at(e.src).label
      let i = pairs.position(p => p.at(0) == a.id and p.at(1) == b.id)
      if i == none { pairs.push((a.id, b.id, site)) } else if not pairs.at(i).at(2).contains(site) {
        pairs.at(i).at(2) += ", " + site
      }
    }
  }
  let check = s.nodes.values().find(n => "check a == 2" in n.lines)
  let state = check.lines.find(l => l.starts-with("a="))
  let verdict = snapshot-verdict(s, "a == 2")
  let tone = if verdict == "PROVED" { vb.proved } else { vb.unstable }
  block(width: 100%, {
    align(center, text(size: 8pt, weight: "bold", title))
    v(2pt)
    align(center, diagram(
      spacing: (19mm, 7mm),
      ..shown.map(c => node(
        pos.at(c.id),
        text(size: 7pt)[#c.proc \ #raw(ctxlabel(c))],
        shape: rect,
        stroke: 0.6pt + vb.accent,
        fill: vb.accent.lighten(93%),
        corner-radius: 2pt,
        inset: 3pt,
      )),
      ..pairs.map(((a, b, site)) => edge(
        pos.at(a),
        pos.at(b),
        "-|>",
        stroke: 0.6pt + vb.called,
        label: text(size: 7pt, fill: vb.called, raw(site)),
        label-sep: 1pt,
      )),
    ))
    v(2pt)
    align(center, text(size: 7.5pt)[`a == 2`: #text(fill: tone, verdict), #raw(state)])
  })
}

// The call site of a call as the analyzer numbers it, so the caption cannot
// drift from the graph it describes.
#let _site(call) = {
  let s = claim-snapshot("ctx-demo-k2")
  raw(s.nodes.at(s.edges.find(e => e.label == "enter " + call).src).label)
}

#figure(
  {
    set par(first-line-indent: 0pt, justify: false)
    grid(
      columns: (1fr, 1fr),
      column-gutter: 8pt,
      row-gutter: 10pt,
      _policy("ctx-demo-none", [no contexts]), _policy("ctx-demo-entry", [entry states]),
      _policy("ctx-demo-k1", [call strings, length 1]),
      _policy("ctx-demo-k2", [call strings, length 2]),
    )
  },
  kind: image,
  placement: auto,
  caption: [Procedure copies under four context policies for the playground's
    default program (@fig:pg-overview): `scale(v)` returns `2 * v`, `wrap(w)`
    returns `scale(w)` from #_site("scale(w)"), and `main` calls `a = wrap(1)`
    at #_site("wrap(1)") and `b = wrap(4)` at #_site("wrap(4)"), then checks
    `a == 2`. Boxes are procedure copies labelled with their contexts as the
    analyzer prints them (`root` is the initial context of `main`), arrows
    calls labelled with their sites. Read from
    the analyzer's solved graph (Interval, claims `ctx-demo-*`).],
) <fig:eq-policies>

== Discharging the contract <sec:eq-discharge>

It remains to show that post-solutions of the generated system meet the
coverage contract. The routed locale proves the five obligations once, for all
policies and domains.

#theorem(name: [Routed collecting soundness], isa: "activation_collect_dg_sound")[
  Let $sol$ be a post-solution of the generated system on a key set that
  contains the program entry in the initial context and is closed under local
  edges and call continuations. Let the initial stores be covered by the initial
  abstract state, the specification satisfy the analysis soundness contract
  #isalocale("sound_dg_spec_core"), the callee list the generator uses at each
  call site include every callee a covered call can enter, and routing be
  adequate and total. Then #isai("activation_collect \<G> R startcontext g S v c") $subset.eq
  conc(sol(v, c))$ for every node $v$ and context $c$, and the left-hand side is
  empty outside the key set.
]

The statement paraphrases the lemma together with the assumptions of its
locale #isalocale("routed_context_base_hetero"). It omits the soundness of the
bottom test of @sec:eq-call and three assumptions that every compiled program
and routed key type satisfy: finitely many call edges, one call edge per call
node (#isaconst("calls_source_unique")), and seed keys distinct from the key
of the analysis's own globals. Closure under local edges is required only from
keys whose claim is nonempty.

#oblig("INIT") comes from the initial state at the entry, #oblig("INTRA") from
edge-transfer soundness at a fixed context (@sec:eq-unknowns), and
#oblig("TOTAL") from routing totality. #oblig("CALL") passes through the seed:
the continuation's equation publishes $e$, the post-solution bounds the seed,
and the entry equation reads it back. #oblig("RETURN") uses the alternative
that adequacy returns, whose program reads the result at that $c'$ and
combines it with the matching $q$.

== One publication per key <sec:eq-buffer>

One right-hand side can publish to the same key twice: in the analysis of
@sec:mixed-flow every incoming edge of a node publishes to one shared key, and
two entry alternatives routed to one context publish to one seed.
Declaratively, the contributions are joined, but a solver applies its update rule per publication,
and every rule records the latest contribution of each origin, the unknown
whose equation published (@sec:update-rules). Two publications from one
right-hand side have the same origin, so the second replaces the first in that
record. Under #isaconst("update_global_warrowing_apinis") the key is then
warrowed toward the join of the recorded contributions, which no longer
contains the first one. If the value drops, the key's readers are re-evaluated,
the first publication differs from the record again, and the two publications
can alternate without converging. The regression theory defines such an
unbuffered equation but does not evaluate it, because it is expected not to
terminate. This non-termination is not proved.

#isaconst("buffer_sides") accumulates the publications of one right-hand side
per key and flushes each key once, so an update rule only sees completed
contributions.
#isathm("keyed_multiwrite_buffered_terminates") shows by evaluation that the
buffered version terminates under the warrowing rule, and for a node with two
real predecessor edges #isathm("merge_global_value") shows that the flushed value is the join of
both contributions. The executable analyses run the buffered generator, which
also defers the node's own publication until its contributions are folded. The
soundness proof speaks about the direct generator, and
#isathm("part_post_solution_routed_node_rhs_buffered") transfers the
certificate between them. Their correspondence is declarative: equal answers,
publications and dependencies at each valuation. Whether the two schedules
reach the same solution is left to the regression corpus.

== Program globals as flow-insensitive unknowns <sec:mixed-flow>

// A value at `pp7`, after both calls, from the flow-sensitive Sign run.
#let _mf(var) = snapshot-var("mixed-flow-sign", "main_pp7_ctx0", var)

The shipped analyses keep program globals in the flow-sensitive local value of
every unknown, next to the locals. Goblint's base analysis makes the same
choice for single-threaded programs: it reads globals from its local state and publishes nothing
(@app:goblint-alignment). Seidl et al. present the flow-insensitive treatment
of a global as a choice made for efficiency @seidl26. The following program
shows what the flow-sensitive placement costs and what the alternative loses:

#listing(lang: "c", claim: "mixed-flow-sign", ```
global Gx;
fun set() { Gx = 1; }
fun get() { return Gx; }
fun main() { x = 1; set(); y = get(); }
```)

Flow-sensitively, the value of `Gx` belongs to the state at every node of every
procedure. It enters `set` with the caller's state, comes back through the
return combination, and enters `get` from `main`'s continuation. Every
procedure's unknowns carry every global, whether or not the procedure mentions
it. With the full entry state as context @apinis12, two calls that differ only
in a global would even analyze the callee twice. Voblint's entry-state
contexts project to the formal parameters (@sec:eq-routing) and avoid that. An
analysis may instead keep one fact per global that holds throughout the run.
The write in `set` then reaches the read in `get` through that fact instead of
along the call chain. This loses precision, because the fact must cover the initial `Gx = 0`
as well as the written 1, so Sign can only claim #signval("≥0") for `Gx` and
for `y` after `y = get()`, although every run ends with `y = 1`. A
flow-sensitive analysis carries #signval("+") from `set`'s exit into `get`'s
entry and derives #signval(_mf("y")) for `y` (claim `mixed-flow-sign`). The
local `x` is #signval(_mf("x")) under both placements.

Such a fact is a flow-insensitive unknown written by side effects
(@ch:background); the certificate (@sec:certificate) makes it bound everything
contributed to it, from anywhere and in any context. The entry seeds of
@sec:eq-seed are one use of such unknowns, and program globals are the second.

The lifter #isaconst("ownership_split_lift") adds one key
$kappa = #isaconst("Analysis_Global") thin ()$ whose value is an abstract
store for all VIMP globals together. This realizes the flow-insensitive
system of Apinis et al. with one key for all globals, where the paper and
Goblint keep one unknown per global @apinis12 (@app:goblint-alignment). For an
edge $(u, a, v)$ with whole-state transfer $f_a$, the edge's lifted
contribution to $(v, c)$ computes
$ s = f_a (#isaconst("combine_env") cal(G) thin sol(u, c) thin sol(kappa)), $
answers #isaconst("restrict_local_for") $cal(G) thin s$ and publishes
#isaconst("restrict_global_for") $cal(G) thin s$ at $kappa$. Here $cal(G)$
classifies the declared globals, #isaconst("combine_env") takes
each global name from its second argument and every other name from its first,
and the two restrictions set the other half to #lbot. The program entry
publishes the global half of the initial state, a call publishes the global
halves of both components of every entry pair, and a return reassembles
caller and callee exit with the same $sol(kappa)$. @fig:mixed-flow shows the
unknowns of the program.

// A publication routed around the lanes it would otherwise cross.
#let _pubvia(pts, lab, side: left) = edge(
  ..pts,
  "-|>",
  stroke: (paint: vb.called, thickness: 0.7pt, dash: "dashed"),
  label: text(7.5pt, fill: vb.called, lab),
  label-side: side,
  label-pos: 0.5,
)

#figure(
  placement: auto,
  {
    set text(size: 10pt)
    show raw: set text(size: 8pt)
    let two(top, bottom) = stack(spacing: 2.5pt, top, text(size: 8pt, bottom))
    diagram(
      spacing: (6.5mm, 9mm),
      _seed((0, 0), $italic("Seed")(italic("set"))$),
      _loc((1, 0), raw("entry_set")),
      _loc((2, 0), `pp0`),
      _loc((3, 0), `pp1`),
      _loc((4, 0), raw("exit_set")),
      _loc((1, 1), raw("entry_main")),
      _loc((2, 1), `pp4`),
      _loc((3, 1), `pp5`),
      _loc((4, 1), `pp6`),
      _loc((5, 1), two(`pp7`, [`x` #signval("+"), `y` #signval("≥0")])),
      _seed((6, 1), two($kappa$, [`Gx` #signval("≥0")])),
      _seed((2, 2), $italic("Seed")(italic("get"))$),
      _loc((3, 2), raw("entry_get")),
      _loc((4, 2), `pp2`),
      _loc((5, 2), raw("exit_get")),
      _read((0, 0), (1, 0), []),
      _read((1, 0), (2, 0), []),
      _read((2, 0), (3, 0), []),
      _read((3, 0), (4, 0), []),
      _read((1, 1), (2, 1), []),
      _read((2, 1), (3, 1), []),
      _read((3, 1), (4, 1), []),
      _read((4, 1), (5, 1), []),
      _read((2, 2), (3, 2), []),
      _read((3, 2), (4, 2), []),
      _read((4, 2), (5, 2), []),
      _read((4, 0), (4, 1), []),
      _read((5, 2), (5, 1), []),
      _read((6, 1), (5, 2), [`Gx`], side: left),
      _pubvia(((4, 1), (3.6, 0.5), (0, 0.5), (0, 0)), []),
      _pubvia(((5, 1), (4.6, 1.5), (2, 1.5), (2, 2)), []),
      _pubvia(((3, 0), (3, -0.6), (6, -0.6), (6, 1)), [`Gx` #signval("+")]),
      _pubvia(((1, 1), (1, 2.6), (6.3, 2.6), (6.3, 1)), [`Gx` #signval("0")], side: right),
    )
  },
  caption: [Unknowns of the `set`/`get` program for the ownership-split Sign
    analysis under the unit context (omitted). Solid arrows are reads, dashed
    arrows publications, as in @fig:eq-unknowns. Every lifted right-hand side
    also reads $kappa$ and publishes its global half. The figure draws only the
    initial contribution from `main`'s entry, the write in `set`, and the read
    of `Gx` in `return Gx`. The values at `pp7` and $kappa$ are evaluated in Isabelle
    (#isathm("mf_snapshot")); the edge labels are derived by hand.],
) <fig:mixed-flow>

A mixed state $(d, g)$ denotes
$
  #isaconst("gamma_ownership_split") cal(G) thin d thin g
  = sem(#isaconst("combine_env") cal(G) thin d thin g),
$
the stores whose locals $d$ describes and whose globals $g$ describes, and the
claim at $(v, c)$ pairs $sol(v, c)$ with the one value $sol(kappa)$. The
invariant behind soundness is that $sol(kappa)$ describes the globals of every
store reached anywhere, because every transfer publishes the global half of its
result. The return then needs nothing new from the callee except its result: a
concrete return keeps the caller's locals and takes the callee's globals
(@sec:calls), and both sides are described under the same $g$
(#isathm("gamma_ownership_split_combine_env")). The call cannot publish only
the entry: splitting the resume value discards its global half, and a proof
that this half adds nothing would be a further obligation.

What is proved has three levels. For every classifier and every whole-state
specification built from sound transfers,
#isathm("ownership_split_lift_core_sound") establishes
#isalocale("sound_dg_spec_core") for the lifted specification and
#isaconst("gamma_ownership_split"). The proof reduces each obligation to the
wrapped transfer's soundness, since restricting and reassembling rebuilds the
state the transfer ran on. At the executable carrier,
#isathm("sound_dg_spec_core_mf") proves the same for Sign. The routed
obligations of @sec:eq-routing are discharged for the program above only,
under the unit context and the join update rule, from facts evaluated on its
solved table: the solve terminates, the key set is closed, and no formal
parameter is global. The evaluations use Isabelle's code-generator oracle,
the trust boundary of @ch:executable. From these,
#isathm("mf_activation_collect_sound") and #isathm("mf_ltr_collect_sound")
(@app:statements) bound the collecting semantics at every node,
#isathm("mf_source_sound") extends the bound to source runs, and at `pp7`,
the node #isai("Statement 7") after both calls:

#proved("mf_after_calls")

The statement mentions only `x` and `y`: the bound on `y` is what the
flow-insensitive `Gx` leaves, and no theorem produces a verdict for this
analysis. It is not selectable in #isaconst("run_voblint"), and no theorem
discharges its routed obligations for every program.

The shipped analyzer therefore makes little use of the shared unknowns. In
#isaconst("run_voblint") side effects write only to the entry seeds: every
selectable analysis instantiates #isaconst("analysis_spec"), which never writes
$kappa$ and whose concretization ignores it. One unknown per program global, as
in Seidl et al. @seidl26, needs a concretization that reads an environment of
shared values, since #isalocale("sound_dg_spec_core") admits a single global
name. The manager is already generic in the name type. @ch:related compares
the instance with earlier mechanizations of mixed flow sensitivity.

== Finite context spaces <sec:eq-finite>

A terminating solve visits finitely many unknowns, but a finite context space
does not force termination: values can ascend forever inside a finite key
space. For call strings of length at most $k$ over the nodes of a compiled
program, the candidate space is finite (#isathm("compiled_call_strings_finite")).
This bounds the solved keys only if they lie in that space, which truncation
alone does not ensure: a start context built from foreign nodes stays short
without entering it. #isathm("compiled_call_string_vars_finite") therefore takes
the containment as a hypothesis. An entry-state context is a list of abstract
values at the callee's arity. For Sign and Parity that space is finite. For
Interval, Congruence and the Int product it is not, and widening bounds the
values of existing unknowns without bounding how many are created: the
regression `21-context-sensitivity/01`
recurses with a fresh argument per level and does not finish within its time
limit. The end-to-end theorem therefore keeps a per-program termination premise
(@sec:termination).

The chapter proves the composition step of RQ3 for the equations, and the
routing half of RQ2. #isathm("activation_collect_dg_sound") discharges the five
obligations of @ch:traces once for every domain, context policy and
specification: any post-solution on a key set that contains the program entry
and is closed under local edges and call continuations bounds every context
bucket, given the analysis soundness contract, paired entry coverage, a complete
callee list and adequate, total routing. For functional policies totality and
the context half of adequacy hold by construction. For entry-state policies the
relation is read off the solved table (#isaconst("routed_entry_context_rel")),
which makes the covering and routing parts of adequacy definitional and
totality paired entry coverage. These results belong to K2 and K3.
@ch:solving must supply the post-solution and its key set, and @ch:results must derive the
closure of the key set, which the solver does not provide directly.
