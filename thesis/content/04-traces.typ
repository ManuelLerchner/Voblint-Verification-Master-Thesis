#import "@preview/fletcher:0.5.8" as fletcher: diagram, edge, node
#import "../lib/math.typ": *
#import "../lib/theme.typ": vb
#import "../lib/figures.typ": *
#import "../lib/code.typ": *
#import "../lib/sources.typ": proved, thy
#import "../lib/theorems.typ": corollary, definition, example, lemma, theorem
#import "../lib/cfg-graphs.typ": sum-graph

= Traces and the Coverage Contract <ch:traces>

@ch:program-model matched every source run with a run of the compiled graph.
For an analysis that computes one abstract state per node, this suffices. A
context-sensitive analysis, however, computes a separate state for each node and
calling context, so to justify its result we need to know which executions each
context represents. The collecting semantics of @ch:background, which gathers
the stores reached at each node, does not record this. In the running example,
both calls of `bump` reach the same result node, but a context-sensitive
analysis may distinguish the activation entered with $5$ from the one entered
with $4$.

Each call of a procedure starts a new _activation_ of it, which lasts until the
call returns @aho06[§7.2.1]. We represent executions by _activation traces_.
An activation trace records the path of one activation through the graph,
together with the trace of the caller that created it and, after a call
returns, the finished callee. The calling contexts of an activation are then
derived from its trace. An analysis result is judged through its _claim_,
which assigns each node and context a set of stores. For the analyzer, the
claim at a node and context is the concretization of the abstract value it
computed there. On the trace semantics we build a local _coverage contract_, a
set of conditions on the claim that mention only concrete stores. Once they
hold, the claim for a node and a context covers the stores that executions in
that context reach there, and the claims of all contexts together cover every
store that a run reaches at the node.

== Why contexts need traces <sec:why-traces>

The collecting semantics of @ch:background assigns each node $v$ of a
control-flow graph the set of stores that some run holds on reaching $v$
@cousot77[§4]. @ch:background over-approximated it with one unknown per node,
which we now write $[v]$ @apinis12[§2]. A context-sensitive analysis instead
splits $[v]$ into unknowns $[v, c]$, one per calling context $c$, following the
value tables of Sharir and Pnueli @sharir81 in the constraint-system
formulation of Apinis et al. @apinis12[§3]. Seidl et al. state that the
invariant for $[u, c]$ "only need[s] to take into account executions reaching
$u$ that satisfy the restriction imposed by context $c$" @seidl26[§4]. The
claim for $[v, c]$ therefore has to describe only a subset of the stores that
the claim for $[v]$ describes, and it can be correspondingly more precise.

In the running example (@fig:program-to-equations), `bump` returns its
argument plus one. A context-insensitive analysis has one claim for the result
node of `bump`, which must describe both results, $6$ and $5$. An analysis
that distinguishes the two calls by their argument can instead claim $6$ for
the call with argument $5$ and $5$ for the call with argument $4$. To justify
these claims, we must know which store at the result node belongs to which
call, and the collecting semantics does not record it.

The frame stack of the graph execution (@sec:cstep) records the callers that
wait for the running activation. It holds, however, only what execution needs
to resume them, and it forgets a call once the call has returned. The contexts
of a callee, in contrast, depend on the caller's context and store at the
call, and after the return the caller continues in the contexts it had
before. Nor does the run itself make this explicit. A flat record of the run,
the list of node-store pairs $(v, s)$ that it passes through
(@fig:flat-nested, top), interleaves the steps of all activations. In the
program of @fig:cfgmap, `sum(2)` calls `dec` and then itself, so one run
visits the nodes of `sum` in three activations, and finding the contexts of a
step would mean recovering from the list which call created its activation and
which return resumes which caller.

Grouping the same run by activation makes these relationships explicit
(@fig:flat-nested, bottom). A call creates a new activation attached to its
caller, and a return composes the finished callee back into that caller. The
construction is inspired by the _local traces_ of Schwarz et al. @schwarz21,
which record one thread's view of a concurrent execution. An activation trace
records one activation's view of a sequential run.

#let _acts = (vb.neutral, vb.accent, vb.sign, vb.par, vb.cong, vb.trusted)
// Colour alone does not survive greyscale printing: every box names its
// activation, and a hand-over names the callee.
#let _act-names = ("main", "sum(2)", "dec(2)", "sum(1)", "dec(1)", "sum(0)")
#let _chip(a, body) = box(
  inset: (x: 2pt, y: 1pt),
  radius: 2pt,
  fill: _acts.at(a).lighten(88%),
  stroke: 0.5pt + _acts.at(a),
  text(size: 6.3pt, font: "DejaVu Sans Mono", fill: vb.neutral, bottom-edge: "descender", body),
)
#let _mark(a) = box(
  inset: (x: 1.8pt, y: 1pt),
  radius: 2pt,
  stroke: (paint: _acts.at(a), thickness: 0.8pt, dash: "dashed"),
  text(
    size: 6pt,
    fill: _acts.at(a),
    weight: "bold",
    bottom-edge: "descender",
  )[#sym.arrow.r.hook #_act-names.at(a)],
)
#let _chips(..items) = (
  items
    .pos()
    .map(it => if type(it) == int { _mark(it) } else {
      _chip(it.at(0), it.at(1))
    })
    .join(h(2.5pt))
)
#let _act(a, name, path, ..inner) = block(
  width: 100%,
  inset: 2.3pt,
  radius: 3pt,
  stroke: 0.6pt + _acts.at(a),
  below: 1.5pt,
)[
  #text(size: 6.8pt, weight: "bold", fill: _acts.at(a), name) #h(3pt) #path
  #inner.pos().join()
]

// The run is written once, as its tree of activations: a step is a node name,
// a callee is a nested activation. Both the flat list and the grouping are
// drawn from it.
#let _call(a, ..steps) = (act: a, steps: steps.pos())
#let _run = _call(
  0,
  "entry_main",
  "pp9",
  _call(
    1,
    "entry_sum",
    "pp2",
    "pp5",
    _call(2, "entry_dec", "pp0", "exit_dec"),
    "pp6",
    _call(
      3,
      "entry_sum",
      "pp2",
      "pp5",
      _call(4, "entry_dec", "pp0", "exit_dec"),
      "pp6",
      _call(5, "entry_sum", "pp2", "pp3", "exit_sum"),
      "pp7",
      "exit_sum",
    ),
    "pp7",
    "exit_sum",
  ),
  "pp10",
  "pp11",
  "exit_main",
)
#let _flat(t) = (
  t.steps.map(x => if type(x) == str { ((t.act, x),) } else { _flat(x) }).join()
)
#let _nested(t) = _act(
  t.act,
  _act-names.at(t.act),
  _chips(..t.steps.map(x => if type(x) == str { (t.act, x) } else { x.act })),
  ..t.steps.filter(x => type(x) != str).map(x => pad(left: 8pt, _nested(x))),
)
#figure(
  {
    align(center, block(width: 52%, layout(size => {
      let g = sum-graph
      scale(size.width / measure(g).width * 100%, reflow: true, g)
    })))
    v(0.6em)
    set par(first-line-indent: 0pt, justify: false, leading: 0.9em)
    set align(left)
    block(spacing: 0pt, {
      set par(leading: 0.45em)
      text(size: 7.5pt, weight: "bold", fill: vb.muted)[flat list]
      h(3pt)
      _flat(_run).map(((a, x)) => _chip(a, x)).join(h(2.5pt))
    })
    v(0.5em)
    text(size: 7.5pt, weight: "bold", fill: vb.muted)[grouped by activation]
    v(0.2em)
    _nested(_run)
  },
  kind: image,
  caption: [The compiled graph of the program in @fig:cfgmap (top) and one run
    on it, as the flat list of its steps and grouped by activation. Colors mark
    each step's activation, which the flat list itself does not record. A
    dashed tag #sym.arrow.r.hook marks a call of the named callee. The run is
    written out by hand, and stores are omitted.],
) <fig:flat-nested>

== Traces <sec:traces>

=== Activation traces #thy-badge("Voblint_CFG", "Activation_Trace_Def") <sec:activation-trace>

We turn the grouping of @fig:flat-nested into a datatype.

#block(breakable: false)[
  #definition(
    name: [Activation trace],
    isa: "activation_trace",
    cmd: "datatype",
    snippet: {
      thy("activation_path")
      thy("activation_trace")
    },
    snippet-caption: [The declarations of #isatype("activation_path") and #isatype("activation_trace"), lifted from the theory. An #isatype("activation_path") is the path of one activation, a list of pairs of a CFG node and a store.],
    snippet-label: <fig:activation-trace>,
  )[
    A trace has one constructor per way an activation begins or continues
    (@fig:activation-trace).
  ]
]

$#Root($pi$)$ is the initial activation of the program with activation path
$pi$, and a run starts with $#Root($[(italic("entry"), s_0)]$)$ at the entry
of `main` with an initial store $s_0$. $#CallT($t'$, $pi$)$ is a callee
created by the caller $t'$, whose activation path begins at the callee's
entered store. $#ResumeT($t'$, $t''$, $pi$)$ is the activation $t'$ continued
past the call that produced the finished callee $t''$. Its path $pi$ begins
with the whole path of $t'$, followed by the continuation, so a call starts a
fresh path and a return extends the caller's. We write #isaconst("path_of") $t$ for
the path of $t$, and #isaconst("extend", thy: "Activation_Trace_Def") $t$ $(v, s)$ for $t$ with the step
$(v, s)$ appended to its path. $#isaconst("sink_node") med t$ and
$#isaconst("sink_store") med t$ are the node and store of the last entry of the
path, and $#isaconst("caller_of") med t$ is the caller that created the
activation. A $ctor("Root")$ has no caller, a $ctor(
  "Call", thy: "Activation_Trace_Def"
)$ stores its caller, and a $ctor("Resume")$ keeps the
caller of the activation it continues,
$#isaconst("caller_of") (#ResumeT($t'$, $t''$, $pi$)) = #isaconst("caller_of") med t'$.

Each trace represents the history of one activation up to a program point, so
on well-formed compiled programs its activation path stays inside the nodes of
one procedure (#isathm("valid_activation_trace_frag_callers")). A whole run is
a family of traces linked by their caller and callee fields. Because a
$ctor("Call", thy: "Activation_Trace_Def")$ stores its caller exactly, frozen
at the call node, a finished callee composes back into the activation that
created it, without a search for a compatible stack frame. A return therefore
continues exactly the caller that created the callee.

The datatype stores no calling context. Which information a context records
depends on the analysis, and for contexts built from abstract entry states it
even depends on the analysis's own result, so a trace that stored its context
would change the traces with every analysis. Instead, the traces and the
stores they collect are fixed once, independently of any analysis. Each
analysis supplies for every concrete call the set of callee contexts it
admits, and the contexts of traces are derived from these sets
(@sec:contexts). The soundness theorems are therefore proved once for all such
choices.

=== Valid traces #thy-badge("Voblint_CFG", "Activation_Trace_Def") <sec:valid>

The datatype also admits terms that no execution produces. A path may jump
from the entry of `sum` directly to its result node, along no edge of the
graph, and a $ctor("Resume")$ may continue `main` after its call `sum(2)` with
the finished inner activation `sum(1)`, whose caller is `sum(2)`. Validity
rules out such terms.

#definition(
  name: [Valid traces],
  isa: "valid_activation_trace",
  cmd: "inductive_set",
  snippet: thy("valid_activation_trace"),
  snippet-caption: [The four rules of #isaconst("valid_activation_trace"): root, intra, call, and ret. Each reads the graph relation for its own kind of step: #isaconst("intra") for local flow, and #isaconst("calls") both for entering a callee and for recovering the continuation $italic("cont")$ at a return.],
  snippet-label: <fig:valid-rules>,
)[
  For a graph $g$ and a set $S$ of initial stores,
  #isai("valid_activation_trace g S") is the least set of traces closed under
  the four rules of @fig:valid-rules.
]

The root rule corresponds to the initial graph configuration, and the other
three correspond to the rules of #isaconst("cstep"). Intra appends a step
along a local edge. Call starts a new trace that holds the caller, where
#isaconst("cstep") pushes a frame, and ret builds a trace that holds caller
and callee, where #isaconst("cstep") pops the frame.

The ret rule applies when a callee trace has reached a result node
#isai("FunctionResult p"). No edge leaves that node, since it serves every
caller of $p$, so the rule finds the caller through
#isai("caller_of callee = Some caller") and takes the #isaconst("calls") edge
from its call node into $p$, the only such edge on compiled programs. That
edge names the continuation $italic("cont")$, where the caller continues with
the store that #isaconst("combine_collect") builds from both final stores.

=== Graph runs are valid traces #thy-badge("Voblint_Compile", "Source_To_Trace") <sec:source-bridge>

The traces describe the runs of the compiled graph, and through @sec:csim
those of VIMP programs, keeping the history that the frame stack discards.

#definition(name: [Trace representation], isa: "activation_trace_repr", cmd: "definition")[
  A valid trace represents a graph configuration if it ends at the
  configuration's node and store, and its chain of creating callers matches
  the runtime frame stack.
]

For a well-formed compiled program (#isaconst("wf_compile_input")), the
correspondence is lock-step. The initial configuration is represented by a
$ctor("Root")$ trace, a local graph step extends the current trace, a call
creates a $ctor("Call", thy: "Activation_Trace_Def")$ trace, and a return a
$ctor("Resume")$ trace (#isathm("cstep_preserves_activation_trace_repr")).
Hence every configuration that a graph run of such a program reaches has a
representing valid trace
(#isathm("csteps_preserve_located_activation_trace")). The converse is not
proved, and soundness does not need it. With the simulation of
@ch:program-model, this result extends to VIMP programs.

#theorem(name: [Source runs are traces], isa: "source_run_has_activation_trace", statement: true)[
  For a well-formed compiled program, every finite source execution from an
  initial store in $S$ has a matching graph configuration and a valid trace
  ending at the same node with the same store, whose caller chain represents
  the graph's frame stack.
]

=== The node collecting semantics #thy-badge("Voblint_CFG", "Activation_Trace_Collect") <sec:collect>

Collecting the final stores of the valid traces per node gives the _node
collecting semantics_. It plays the role of the collecting semantics of @ch:background for programs
with procedures, with valid traces in place of runs.

#block(breakable: false)[
  #definition(name: [Node collecting semantics], isa: "node_collect", cmd: "definition")[
    #thy("node_collect")
  ]
]

Its core VIMP instance is #isai("\<C>\<^bsub>\<kappa>,g,S\<^esub>")
(#isaconst("node_collect")), and a store is in
#isai("\<C>\<^bsub>\<kappa>,g,S\<^esub> v") exactly when some valid trace ends
at $v$ with this store. From here on #isai("\<kappa>"), #isai("g"), and
#isai("S") are the kind environment, graph, and initial stores of the program
at hand. A procedure's result is an ordinary collected node, and the stores in
which a run of the whole program completes are those collected at
$ctor("FunctionResult") italic("main")$. Every store that a finite source
execution of a well-formed program reaches therefore lies in the node
collecting semantics at a corresponding node
(#isathm("source_reaches_node_collect")).

The node collecting semantics forgets the traces, so a claim stated over it
alone is context-insensitive. The traces themselves keep their structure, so
the same set of traces can also be split by context.

== Calling contexts #thy-badge("Voblint_CFG", "Activation_Trace_Context") <sec:contexts>

A _context_ is an index under which an activation is analyzed, and one
activation may carry several. At a fixed node $v$, activations with the same
context $c$ contribute to the same abstract unknown $[v, c]$. Contexts change
only at calls. A local step keeps the contexts of the trace
(#isathm("activation_context_rel_extend")), and after a return the caller
continues in the contexts it had before the call.

Which information a context records is the analysis's _context policy_
@sharir81 @rival20[§8.4.1] @seidl12compiler[§2.6] @seidl12compiler[§2.9]. The
call-string approach records the call history, in practice bounded to the $k$
most recent call sites, since a recursive procedure otherwise has infinitely
many contexts. The functional approach instead computes caller-independent
procedure summaries that each call site instantiates. Goblint uses partial
tabulation, a variant of the functional approach that tabulates summaries only
for the calling contexts the analysis meets @saan26phd[§3.3]
@schwarz25phd[§5, p. 110], and obtains a callee's context by applying each
analysis's `context` function to its abstract entry state. Erhard et al. treat
full entry states, their projections, and call strings in one framework
@erhard25[§4]. Voblint offers bounded call strings, whose length zero gives
the context-insensitive analysis, and entry-state contexts, whose context is
the list of abstract values of the callee's formals in the entry state and whose number
nothing bounds.

These selectors choose one callee context per call. The _entry operation_ of
an analysis, Goblint's `enter`, turns an abstract caller state at a call into
abstract entry states of the callee. In Goblint it may return several
alternatives for one call, each a pair of a caller state and a callee entry
state with its own context. Several alternatives let an analysis split a call
into cases. Suppose, hypothetically, that a caller passes an argument that is
either negative or positive, and that its state keeps the two cases apart, for
instance as two path-sensitive states, which no shipped Voblint analysis has.
With a single entry state, a sign
analysis analyzes the callee once for the join of both cases, which it can
only describe by $ltop$, any sign. With one alternative per case, it analyzes
the callee once in a context for negative and once for positive arguments and
keeps the sign apart. If the cases overlap, one concrete call belongs to
several contexts at once, which a context function of the call cannot
express. A Voblint policy therefore returns, for each concrete call, a set of
callee contexts. The shipped analyses return one alternative per call, so for
them the set has at most one element for a fixed caller context. An entry
operation that returns two overlapping alternatives admits one concrete call
in two contexts (#isathm("ov_two_contexts_admitted"), evaluated for a
hand-built Interval specification).

The set may also be empty. Under entry-state contexts it is empty for every
caller store that the analysis's state at the call site does not describe, for
instance at a call that the analysis considers unreachable. There an empty set
loses nothing, because the claim contains no such store. At a call that the
program actually makes, however, an entry operation that returned no
alternative would leave the callee unanalyzed and the continuation at $lbot$.
In the counterexample program, which has no branches, every run reaches the
continuation (#isathm("ov_empty_no_callee_context"),
#isathm("ov_empty_continuation_bot")).
The coverage contract therefore has to require a context at every call whose
caller store the claim contains.

#block(breakable: false)[
  #definition(
    name: [Context policy],
    isa: "call_context_policy",
    cmd: "type_synonym",
    snippet: thy("context_policy"),
    snippet-caption: [The declaration of #isatype("call_context_policy"), lifted from the theory.],
    snippet-label: <fig:call-context-rel>,
  )[
    A context policy maps a concrete call to the set of callee contexts it admits
    (@fig:call-context-rel).
  ]
]

A context policy is a function on concrete calls and is never executed. It
names, for each concrete call, the contexts in which a claim has to cover the
callee. Each argument of a policy $italic("adm")$ serves some policy. The
call site lets call strings record where a call happened, so with call
strings of length one, `bump(5)` enters the context that consists of its call
site in `main`. The caller's context lets call strings extend the caller's
history and lets entry-state contexts read the abstract state computed for the
caller in that context, and the call information is what the entry operation
needs to compute an abstract entry state. The two stores serve entry-state
contexts, whose abstract entry state must describe the entered store, the
callee's store after the formals have been bound (`bump(5)` enters with
$n = 5$), and whose alternative must describe the caller store that the return
later combines with the callee's result. On the graph, the policy is applied
to the call edges, with the entered store that the edge's entry transfer
#isaconst("call_enter") computes.

#definition(name: [Context of a trace], isa: "activation_context_rel", cmd: "inductive")[
  The relation #isaconst("activation_context_rel") relates each trace to the
  contexts its activation may carry, which can be none, one, or several. The
  root activation carries the initial context #isai("c\<^sub>0"). A called
  activation carries a context $c'$ if its caller carries some context $c$ and
  $c'$ lies in the set that $italic("adm")$ admits for the call from $c$. A
  resumed activation carries the contexts that the caller had before the call.
]

The contexts of an activation are thus fixed when it is created.#footnote[The
  #link(site("index.html#settings"))[explainer page] draws, for each policy, the contexts that the analyzer
  creates for one program.] Since a return continues exactly the caller that
created the callee, the result of a callee that carries $c'$ flows back only
to the callers whose calls admitted $c'$. A claim for a context therefore needs
to cover only the executions in that context. The node collecting semantics
can now be split by context. A store belongs to context $c$ at node $v$ if some
valid trace ending at $v$ with that store carries $c$.

#block(breakable: false)[
  #definition(
    name: [Activation collecting semantics],
    isa: "activation_collect",
    cmd: "definition",
  )[
    #thy("activation_collect")
  ]
]

Its core VIMP instance
#isai("\<A>\<^bsub>\<kappa>,adm,c₀,g,S\<^esub> v c")
(#isaconst("activation_collect")) is the _activation collecting semantics_ at
$v$ and $c$, and the claim for the unknown $[v, c]$ must contain it. In the
running example under interval entry-state contexts, a context is the
list of abstract values of the formals, here only $n$. Thus `bump(5)` gets the
context $[[5, 5]]$ and `bump(4)` the context $[[4, 4]]$. At `bump`'s
result node, the activation collecting semantics of $[[5, 5]]$ holds the
final store with result $6$, that of $[[4, 4]]$ the final store with
result $5$, and the node collecting semantics both. Stores reached in two
contexts lie in both sets.

The split makes the claims more precise. A single claim for the result node
must contain both stores, so an interval analysis can at best bound the result
by $[5, 6]$, while a claim per context only has to contain $6$ in
$[[5, 5]]$ and $5$ in $[[4, 4]]$. No store is lost as long as every
valid trace carries at least one context, which the coverage contract of the
next section guarantees.

Under entry-state contexts, the policy reads the abstract state that the
analysis computed for the caller, so the activation collecting semantics
depends on the analysis it is meant to justify. This dependence is harmless.
The valid traces and the node collecting semantics do not mention any policy.
The policy only decides how their stores are distributed over contexts, and
under the totality condition of the coverage contract it cannot drop a store.
The union of the activation collecting semantics over all contexts then equals
the node collecting semantics for every such policy (@sec:contract,
#isathm("node_collect_eq_Union_activation_collect")). The analyzer itself
never evaluates a policy. It chooses callee contexts from the abstract entry
states it computes, a step called routing, and @sec:eq-routing proves that
this choice agrees with the policy.

== The coverage contract #thy-badge("Voblint_CFG", "Activation_Trace_Abstract") <sec:contract>

The goal is a claim #isai("cover"), with a set of stores #isai("cover v c")
for each node $v$ and context $c$, that contains
#isai("\<A>\<^bsub>\<kappa>,adm,c₀,g,S\<^esub> v c") everywhere. For the
analyzer, #isai("cover v c") is the concretization of the abstract value
computed for $[v, c]$. The coverage contract reduces the goal to local
conditions on #isai("cover") that mention only stores, and it is therefore the
interface between the analyzer and the concrete semantics.

Valid traces grow by four rules, so it is enough to check the claim locally
against the same four cases. There is one obligation per rule: #oblig("INIT") for the root activation, #oblig("INTRA") for a local edge, #oblig("CALL") for the entry into a callee, and #oblig("RETURN") for the continuation after a callee finishes. Each obligation other than #oblig("INIT") looks at one step of a run and requires the
claim to contain the store after the step whenever it contains the stores
before it. @fig:contract shows
these obligations at one call, together with a fifth, #oblig("TOTAL").

#let _key(pos, name, body, col: vb.neutral) = node(
  pos,
  text(size: 7pt, body),
  stroke: 0.8pt + col,
  fill: col.lighten(90%),
  corner-radius: 3pt,
  inset: 4pt,
  name: name,
)
#let _ob(o) = text(size: 7pt, fill: vb.accent, weight: "bold", smallcaps(o))
#figure(
  diagram(
    spacing: (14mm, 9mm),
    node((-1, 0), text(size: 7pt, fill: vb.muted)[initial stores], stroke: none, name: <c-init>),
    _key((0, 0), <c-entry>, [entry, $c_0$]),
    _key((1, 0), <c-u>, [call site $u$, $c$]),
    _key((1, -1), <c-pe>, [callee entry, $c'$], col: vb.sign),
    _key((2, -1), <c-pr>, [callee result, $c'$], col: vb.sign),
    _key((2, 0), <c-k>, [continuation $k$, $c$]),
    edge(<c-init>, <c-entry>, "-|>", label: _ob("Init")),
    edge(<c-entry>, <c-u>, "-|>", label: _ob("Intra"), label-side: right),
    edge(<c-u>, <c-pe>, "-|>", label: _ob("Call"), stroke: vb.called),
    edge(<c-pe>, <c-pr>, "-|>", label: _ob("Intra")),
    edge(<c-pr>, <c-k>, "-|>", label: _ob("Return"), stroke: vb.called),
    edge(
      <c-u>,
      <c-k>,
      "..|>",
      label: text(size: 6.5pt, fill: vb.muted)[caller store $s$],
      label-side: right,
    ),
  ),
  kind: image,
  placement: none,
  caption: [The obligations at one call (schematic). Boxes are (node, context)
    pairs, and solid arrows show where each obligation applies, #oblig("INTRA")
    repeatedly along an activation path. The dotted arrow is no obligation. It
    shows the caller store $s$ that #oblig("RETURN") combines with the callee's
    result in the admitted context $c'$. #oblig("TOTAL") demands that at least
    one $c'$ exists.],
) <fig:contract>

#oblig("RETURN") pairs every caller store $s$ that the claim contains at $u$
with every callee result $t$ that the claim contains in a context $c'$
admitted for the call from $s$, and not only with the result that the call
from $s$ produced. The context is the only link between caller and callee
stores, so finer contexts make these pairs closer to the real ones.

The fifth obligation, #oblig("TOTAL"), concerns a call at a call site $u$ in
a caller context $c$ from a caller store $s$. If $s in #isai("cover u c")$,
#oblig("TOTAL") requires the policy to admit at least one callee context for
the call from $s$ (#isaconst("call_context_total_on")). The other four
obligations do not suffice without it (#isathm("total_dropped_unsound")). At a
call that gets no context, #oblig("CALL") and #oblig("RETURN") hold vacuously,
so nothing constrains the claim at the continuation, while the resumed caller
keeps its contexts. A store that the caller reaches after the return can
therefore lie outside the claim.

Asking for contexts at every call would be too strong for entry-state
policies, whose sets are empty for the caller stores that the analysis
excludes (@sec:contexts). Asking for them only at reachable calls would be
weaker, since the claim contains every reachable caller store, but an
analysis cannot decide which calls are reachable. It can only inspect its own
claim, so
#oblig("TOTAL") is stated over the stores the claim contains. Call strings, including the context-insensitive length zero,
admit a context for every call and meet #oblig("TOTAL") for every claim
(#isathm("call_context_total_on_of_fun")). For entry-state contexts it follows
from the coverage of the analysis's entry operation. Isabelle states the five obligations as the assumptions of the locale
#isalocale("activation_coverage") (@fig:activation-coverage). A _locale_ fixes
parameters and assumptions. Interpreting it for an instance proves the
assumptions and yields the locale's theorems for that instance @ballarin14.
An analysis therefore becomes sound by interpreting a locale.

#figure(
  {
    show raw.where(block: true): set text(size: 6pt)
    thy("activation_coverage")
  },
  kind: image,
  placement: none,
  caption: [The declaration of #isalocale("activation_coverage"), lifted from the
    theory. In #oblig("RETURN"), #isai("admits_call_context g adm u c p' s es c'")
    states that some call edge from #isai("u") into $p'$ enters the store
    #isai("es") from #isai("s") and that the policy admits $c'$ for this call.
    $p'$ and #isai("es") range over every call edge out of #isai("u"). On
    compiled programs a call site has one call edge
    (#isathm("compile_prog_calls_source_unique")), so $p' = p$.],
) <fig:activation-coverage>

#block(breakable: false)[
  #theorem(name: [Context-indexed soundness], isa: "activation_collect_sound")[
    If the claim meets the five obligations of
    #isalocale("activation_coverage"), then for every node $v$ and context $c$, the activation collecting semantics
    at $v$ and $c$ is contained in the claim #isai("cover v c").
  ]

  #proved("activation_collect_sound")
]

The proof is an induction over the four rules of valid traces, with a
strengthened claim about each trace $t$. The trace carries at least one
context, and #isaconst("sink_store") $t$ lies in the claim at
#isaconst("sink_node") $t$ for every context $t$ carries. The induction
proves this for the whole chain of callers of a trace, because the ret rule
needs it for the caller as well as for the callee. Root, intra and call follow
from #oblig("INIT"), #oblig("INTRA") and #oblig("CALL"), and in the call case
#oblig("TOTAL") supplies the context of the new activation, since the caller's
store lies in the claim. The ret case is the hard step. For each context $c$
of the resumed caller, the caller's store lies in the claim at the call site
in $c$, so #oblig("TOTAL") admits some $c'$ for the call. The callee carries
$c'$, because its contexts are exactly those admitted from its caller's
contexts along its own entry edge, and its final store therefore lies in the
claim at the result node in $c'$. #oblig("RETURN") combines the two stores in
$c$.

#block(breakable: false)[
  The strengthened claim also gives every valid trace at least one context, so
  the activation collecting semantics of all contexts together is exactly the
  node collecting semantics.

  #theorem(
    name: [Exhaustive contexts],
    isa: "node_collect_eq_Union_activation_collect",
    statement: true,
  )[
    Under the five coverage obligations, including #oblig("TOTAL"), the node
    collecting semantics at every node $v$ is the union of the activation
    collecting semantics at $v$ over all contexts.
  ]
]

#corollary(name: [Claims cover the collection], isa: "node_collect_covered", statement: true)[
  Under the five coverage obligations, every store of the node collecting
  semantics at $v$ lies in the claim #isai("cover v c") of some context $c$.
]

Apinis et al. make the corresponding observation for the abstract side
@apinis12[§3]. After local solving, the abstract values that reach a program
point are bounded by the join of the solution's values there over the
contexts the solver encountered.

Every finite source execution of a well-formed program is matched by a graph
run (@ch:program-model), which a valid activation trace represents
(@sec:source-bridge). Its contexts place its final store in their activation
collecting semantics (@sec:contexts), which every claim meeting the coverage
contract contains. The following chapters construct such claims by abstract
interpretation.
