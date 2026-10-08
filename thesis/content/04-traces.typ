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
context represents.

The collecting semantics of @ch:background, which gathers the stores reached
at each node, does not record this.
In the running example, both calls of `bump` reach the same result node, but a
context-sensitive analysis may distinguish the activation entered with $5$ from
the one entered with $4$. This chapter gives that distinction a concrete
meaning.

Each call of a procedure starts a new _activation_ of it, which lasts until the
call returns @aho06[§7.2.1]. We represent executions by _activation traces_.
An activation trace records the path of one activation through the graph. It
also records the trace of the caller that created the activation, because the
context of a call is chosen from the caller's context and store. After a call
returns, it records the finished callee as well, whose result the activation
continues with. The calling contexts of an activation are then derived from
its trace.

On this semantics we build a local _coverage contract_. Its obligations are
the concrete interface that the abstract analyses and the equation system of
@ch:domains to @ch:solving must satisfy. Once they hold, the claim for a node
and a context covers the stores that executions in that context reach there,
and the claims of all contexts together cover every store that a run reaches
at the node.

== Why contexts need traces <sec:why-traces>

The collecting semantics of @ch:background assigns each node $v$ of a
control-flow graph the set of stores that some run holds on reaching $v$
@cousot77[§4]. @ch:background over-approximated it with one unknown per node,
which we now write $[v]$ @apinis12[§2]. A context-sensitive analysis instead
splits $[v]$ into unknowns $[v, c]$, one per calling context $c$, following the
value tables of Sharir and Pnueli @sharir81, as Apinis et al. formulate them as
a constraint system @apinis12[§3]. Seidl et al. state that the invariant for
$[u, c]$ "only need[s] to take into account executions reaching $u$ that
satisfy the restriction imposed by context $c$" @seidl26[§4]. The claim for
$[v, c]$ therefore has to describe only a subset of the stores that the claim for $[v]$
describes, and it can be correspondingly more precise.

In the running example (@fig:program-to-equations), `main` calls `bump(5)` and
then `bump(4)`, and `bump` returns its argument plus one. A context-insensitive
analysis has one claim for the result node of `bump`, which must describe both
results, $6$ and $5$. An analysis that distinguishes the two calls by their
argument can instead claim the result $6$ for the call with argument $5$ and
the result $5$ for the call with argument $4$. To justify these claims, we must know which store at the result node belongs
to which call. The collecting semantics, however, is too weak to tell. It holds
both stores at the result node but does not record which activation reached
each of them, so we need a richer semantics that keeps this information.

The graph execution (@sec:cstep) has a frame stack, which records the callers
that wait for the running activation. The stack, however, holds only what
execution needs to resume these callers, and it forgets a call once the call
has returned. A context policy needs more. It chooses the context of a call
from the caller's context and store at the call, and after the return the
caller must continue in the context it had before. Activation traces keep this
information. A callee trace records the caller that created it, and a resumed
trace records both the caller and the finished callee.

Contexts could in principle be derived from the graph run itself. A flat
record of the run, namely the list of node-store pairs $(v, s)$ that the run
passes through (@fig:flat-nested, top), interleaves the steps of all
activations and leaves their nesting implicit. In the program of @fig:cfgmap,
`sum(2)` calls `dec` and then itself, so one run visits the nodes of `sum` in
three activations. To find the context of a step, one would therefore have to
recover from the list which call created its activation and which return
resumes which caller.

Grouping the same run by activation, in contrast, makes these relationships
explicit (@fig:flat-nested, bottom). Each activation has its own activation
path. A call creates a new activation attached to its caller, and a return
composes the finished callee back into that caller. The construction is
inspired by the _local traces_ of Schwarz et al. @schwarz21, which record one
thread's view of a concurrent execution. An activation trace applies the same
idea to a sequential program and records one activation's view of the run
(@sec:rel-goblint).

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
    on it, as the flat list of its steps and grouped by activation. Colours mark
    each step's activation, which the flat list itself does not record. A
    dashed tag #sym.arrow.r.hook marks a call of the named callee. The run is
    written out by hand, and stores are omitted.],
) <fig:flat-nested>

== Traces <sec:traces>

=== Activation traces #thy-badge("Voblint_CFG", "Activation_Trace_Def") <sec:activation-trace>

We turn the grouping of @fig:flat-nested into a datatype.

#block(breakable: false)[
  #definition(name: [Activation trace], isa: "activation_trace", cmd: "datatype")[
    A trace has one constructor per way an activation begins or continues.
  ]

  #figure(
    {
      show raw.where(block: true): set text(size: 6.2pt)
      thy("activation_path")
      thy("activation_trace")
    },
    kind: image,
    placement: none,
    caption: [The declarations of #isatype("activation_path") and #isatype("activation_trace"), lifted from the theory. An #isatype("activation_path") is the path of one activation, a list of pairs of a CFG node and a store.],
  ) <fig:activation-trace>
]

$#Root($pi$)$ is the initial activation of the program with activation path
$pi$. A run starts with $#Root($[(italic("entry"), s_0)]$)$, the entry node of
the graph, which is the entry of `main`, paired with an initial store $s_0$.
$#CallT($t'$, $pi$)$ is a callee created by the caller $t'$
(#isaconst("activation_trace_caller")); its activation path begins at the callee's entered store.
$#ResumeT($t'$, $t''$, $pi$)$ is the activation $t'$
(#isaconst("activation_trace_current")) continued past the call that produced the finished
callee $t''$ (#isaconst("activation_trace_callee")). The observer
$#isaconst("path_of") thin t$ returns the activation path,
$#isaconst("sink_node") thin t$ the node of its last entry,
$#isaconst("sink_store") thin t$ that entry's store, and
$#isaconst("caller_of") thin t$ the caller that created the activation, which
a $ctor("Root")$ does not have. The
#link("https://manuellerchner.github.io/Voblint-Verification-Master-Thesis/index.html#observers")[explainer page] shows these observers interactively on a
run of the program of @fig:flat-nested.

Each trace represents the history of one activation up to a program point, so
on well-formed compiled programs its activation path stays inside the nodes of
one procedure (#isathm("valid_activation_trace_frag_callers")). A callee is a
new activation and gets a trace of its own, which holds its caller as a field.
When the callee finishes, a $ctor("Resume")$ creates a new trace for the
continued caller, which holds both the frozen caller and the finished callee.
A whole run is therefore a family of traces linked by these fields.

Because a $ctor("Call", thy: "Activation_Trace_Def")$ stores its caller
exactly, frozen at the call node, a finished callee composes back into the
activation that created it, and no search for a compatible stack frame is
needed. This is what makes context-specific return flow sound. A return
continues exactly the caller that created the callee, in that caller's
context, so the result of a callee entered in context $c'$ flows back only to
the callers whose calls admitted $c'$. A claim for a context therefore needs to cover only the executions in that
context.

The datatype stores no calling context. Which information a context records
depends on the analysis. A call-string analysis distinguishes activations by
their recent call sites, and an entry-state analysis by abstract entry states
that it computes itself. If a trace stored its context, the concrete semantics
would change with every analysis, and for entry-state contexts it would even
depend on the analysis's own result (@sec:eq-routing). Instead, the
concrete semantics is fixed once. Each context policy supplies, for every concrete call, the set of callee
contexts it admits, and contexts of traces are derived from these sets
(@sec:contexts). The soundness theorems are proved once for all policies, and an analysis only
has to show that its claim meets the coverage contract of @sec:contract for
its policy.

=== Valid traces #thy-badge("Voblint_CFG", "Activation_Trace_Def") <sec:valid>

The datatype also admits terms that no execution produces. A path may contain
a step that follows no edge of the graph, for instance a jump from the entry of
`sum` directly to its result node. A $ctor("Resume")$ may pair a caller with a
callee that another activation created, for instance continue `main` after its
call `sum(2)` with the finished inner activation `sum(1)`, whose caller is
`sum(2)`. Validity rules out such terms.

#definition(name: [Valid traces], isa: "valid_activation_trace", cmd: "inductive_set")[
  For a global-variable classifier $cal(G)$, a graph $g$ and a set $S$ of
  initial stores, #isai("\<T>\<^bsub>\<G>,g,S\<^esub>") (#isaconst("valid_activation_trace")) is
  the least set of traces closed under the four rules of @fig:valid-rules.
]

#figure(
  thy("valid_activation_trace"),
  kind: image,
  caption: [The four rules of #isaconst("valid_activation_trace"): root, intra, call and
    ret. Each reads the relation for its own phenomenon: #isaconst("intra")
    for local flow, #isaconst("calls") for entering a callee and for
    recovering the continuation $italic("cont")$ at a return.],
) <fig:valid-rules>

The root rule corresponds to the initial graph configuration, and the other
three rules correspond to the three rules of #isaconst("cstep"). Intra appends
a step along a local edge. Call starts a new trace that holds the caller, where
#isaconst("cstep") pushes a frame. Ret builds a third trace that holds caller
and callee, where #isaconst("cstep") pops the frame.
The #link("https://manuellerchner.github.io/Voblint-Verification-Master-Thesis/index.html#semantics")[explainer page] animates the source execution,
the graph execution and the activation trace side by side on one program.

The ret rule applies when a callee trace has reached a result node
#isai("FunctionResult p"). In a compiled graph no edge leaves it, since one
result node serves every caller of $p$, so the rule finds the caller through
#isai("caller_of callee = Some caller") and takes a #isaconst("calls") edge
from its call node into $p$, on compiled programs the only one. That edge
names the continuation $italic("cont")$, where the caller continues with the
store that #isaconst("combine_collect") builds from both final stores.

=== Graph runs are valid traces #thy-badge("Voblint_Compile", "Source_To_Trace") <sec:source-bridge>

The traces describe the runs of the compiled graph, and through @sec:csim
those of VIMP programs, keeping the history that the frame stack discards.

#block(breakable: false)[
  #definition(name: [Trace representation], isa: "activation_trace_repr", cmd: "definition")[
    A valid trace represents a graph configuration if it ends at the
    configuration's node and store and its chain of creating callers matches
    the runtime frame stack.
  ]

  #figure(
    {
      show raw.where(block: true): set text(size: 6pt)
      thy("stack_repr")
      thy("activation_trace_repr")
    },
    kind: image,
    placement: none,
    caption: [The declarations of #isaconst("stack_repr") and
      #isaconst("activation_trace_repr"), lifted from the theory.],
  ) <fig:activation-trace-repr>
]

For a well-formed compiled program (#isaconst("wf_compile_input")), the
correspondence is lock-step. A local graph step extends the current trace, a
call creates a $ctor("Call", thy: "Activation_Trace_Def")$ trace, and a return creates a $ctor("Resume")$
trace (#isathm("cstep_preserves_activation_trace_repr")). The initial configuration has a representing trace, a $ctor("Root")$ trace
(#isathm("located_activation_trace_entry")). Hence
every configuration that a graph run of such a program reaches has a
representing valid trace (#isathm("csteps_preserve_located_activation_trace")). Only this
direction is proved, and soundness needs no more. With the simulation of
@ch:program-model, it extends to VIMP programs.

#block(breakable: false)[
  #theorem(name: [Source runs are traces], isa: "source_run_has_activation_trace")[
    For a well-formed compiled program, every finite source execution from an
    initial store in $S$ has a matching graph configuration and a valid trace ending at
    the same node with the same store, whose caller chain represents the graph's
    frame stack.
  ]

  #proved("source_run_has_activation_trace")
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

A store is in #isai("\<C>\<^bsub>\<G>,g,S\<^esub> v") exactly when some valid
trace ends at $v$ with this store. The classifier, graph and initial stores
are those of the program at hand, written #isai("\<G>"), #isai("g") and
#isai("S") from here on. A procedure's result is an ordinary collected node,
and whole-program completion is collection at
$ctor("FunctionResult") italic("main")$. Every store that a finite source
execution of a well-formed program reaches therefore lies in the node
collecting semantics at a corresponding node
(#isathm("source_reaches_node_collect")).

The node collecting semantics forgets the traces, so a claim stated over it
alone is context-insensitive. The valid traces themselves, however, keep their
structure. The same set of traces thus supports two views: collected per node,
as here, and split by context, as in @sec:contexts.

== Calling contexts #thy-badge("Voblint_CFG", "Activation_Trace_Context") <sec:contexts>

A _context_ is the index under which an activation is analyzed. At a fixed node,
activations with the same context contribute to the same abstract unknown
$[v, c]$. Contexts change only at calls. Within one activation, a step along a
local edge keeps the contexts of the trace
(#isathm("activation_context_rel_extend")), and after a return the caller continues in the contexts it had before the call
(#isathm("activation_context_rel_Resume_iff")).

Which information a context records is a design decision of the analysis, and
the literature describes many such _context policies_ @sharir81 @rival20[§8.4.1]
@seidl12compiler[§2.6] @seidl12compiler[§2.9]. The call-string approach records
the call history, and practical variants bound it to the $k$ most recent call
sites, since a recursive procedure otherwise has infinitely many contexts. The
functional approach, in contrast, computes a procedure summary independent of
callers, which each call site instantiates. Goblint obtains the context of a
callee by applying each analysis's `context` function to the callee's abstract
entry state (@sec:rel-goblint), and Erhard et al. treat full entry states,
their projections and call strings in one framework @erhard25[§4]. Voblint
offers the context-insensitive policy, bounded call strings and entry-state
contexts (#isatype("context_mode"), @ch:equations).

These context selectors are functions, each choosing one callee context per
call from the call site, the caller's context or the entry state. Goblint's entry operation, however, may return several
alternatives for one call, each a pair of a caller state and a callee entry
state, and each alternative gets its own context. Several alternatives let an
analysis split a call into cases. Suppose a caller passes an argument that is either negative or positive, and
the caller's state keeps the two cases apart, for instance as two
path-sensitive states. With a single entry state, the callee is analyzed
once for the join of both cases, which a sign analysis can only describe by the
greatest element $ltop$, any sign. With one alternative per case, the callee is analyzed once in a
context for negative arguments and once in a context for positive ones, so the analysis
preserves the argument's sign separately in the two contexts. If the cases overlap, one
concrete call lies in several alternatives and belongs to several contexts at
once. A context function of the call cannot express this, so a Voblint policy
returns, for each concrete call, a set of callee contexts. The analyses
shipped with Voblint return one alternative per call, so for them the set has
at most one element for a fixed caller context. A separate example returns two
overlapping alternatives and admits one concrete call in two contexts
(#isathm("ov_two_contexts_admitted")). The set may also be empty. Under entry-state contexts it is empty for every
caller store that the analysis's state at the call site does not describe, for
instance at a call that the analysis considers unreachable. No alternative
describes such a store, so no context is admitted for it. Emptiness is
harmless there, because the claim contains no such store. It is harmful at a call that the program actually makes. In one example, an
entry operation that returns no alternative leaves the callee unanalyzed and
the continuation at $lbot$ (#isathm("ov_empty_no_callee_context"),
#isathm("ov_empty_continuation_bot")), although the program, which has no
branches, reaches the continuation. The coverage contract rules this out
through #oblig("TOTAL") (@sec:contract).

#block(breakable: false)[
  #definition(name: [Context policy], isa: "context_policy", cmd: "type_synonym")[
    A context policy maps a concrete call to the set of callee contexts it admits.
  ]

  #figure(
    {
      show raw.where(block: true): set text(size: 6.2pt)
      thy("context_policy")
    },
    kind: image,
    placement: none,
    caption: [The declaration of #isatype("context_policy"), lifted from the theory.],
  ) <fig:call-context-rel>
]

A context policy is a mathematical object over concrete stores and is not
executed. The analyzer instead chooses callee contexts from the abstract entry
states it computes, and @sec:eq-routing gives the two conditions, totality and
adequacy, under which these choices agree with the policy.

A context policy $italic("adm")$ maps a concrete call to the set of callee
contexts $c'$ it admits. Each of its arguments serves some policy. The call site
lets call strings record where a call happened: with call strings of length
one, `bump(5)` enters the context that consists of its call site in `main`. The
caller's context lets call strings extend the caller's history and lets
entry-state routing read the abstract state that the analysis computed for the
caller in that context. The call information, the call's callee, formals,
arguments and result variable, is what the analysis's entry operation needs to
compute an abstract entry state. The two stores, finally, serve entry-state
contexts. The context is read off an abstract entry state, the values it gives the
formals, and that entry state must describe the entered store, the store at the
callee's entry after the formals have been bound: `bump(5)` enters with
$n = 5$. Each alternative also describes the
caller, and the return later combines this description with the callee's
result. A context is therefore admitted only for a caller store that its
alternative describes (@sec:eq-routing).

#isaconst("admits_call_context") applies $italic("adm")$ to an actual call edge
of the graph, with the entered store that the edge's entry transfer
#isaconst("call_enter") computes from the caller's store.

The relation #isaconst("activation_context_rel") assigns contexts to whole
traces. It does not pick one context per activation. It states which contexts
an activation may carry, and there can be none, one or several. The root
activation carries the initial context #isai("c\<^sub>0"). A called activation
carries a context $c'$ if its caller carries some context $c$ and $c'$ lies in
the set that $italic("adm")$ admits for the call from $c$. A resumed activation carries
the contexts that the caller had before the call. The
#link(
  "https://manuellerchner.github.io/Voblint-Verification-Master-Thesis/index.html#settings",
)[explainer page]
draws, for each policy, the contexts that the analyzer creates on one
program, with every copy of a procedure labelled by its context.

#block(breakable: false)[
  #definition(name: [Context of a trace], isa: "activation_context_rel", cmd: "inductive")[
    The contexts that a trace may carry.
  ]

  #figure(
    {
      show raw.where(block: true): set text(size: 6pt)
      thy("activation_context_rel")
    },
    kind: image,
    placement: none,
    caption: [The declaration of #isaconst("activation_context_rel"), lifted from the theory.],
  ) <fig:trace-context>
]

The contexts of an activation are thus fixed when the activation is
created, and calls it makes later do not change them.

With the contexts of a trace in hand, the node collecting semantics can be
split by context. A store belongs to context $c$ at node $v$ if some valid
trace ending at $v$ with that store carries $c$.

#block(breakable: false)[
  #definition(
    name: [Activation collecting semantics],
    isa: "activation_collect",
    cmd: "definition",
  )[
    #thy("activation_collect")
  ]
]

We call #isai("\<A>\<^bsub>\<G>,adm,c₀,g,S\<^esub> v c") the _activation collecting semantics_ at $v$ and $c$.
It contains the final stores of the valid traces that end at $v$ and carry
$c$, and the claim for the unknown $[v, c]$ must contain it. In the running example under interval entry-state contexts, `bump(5)` gets the
context $[[5, 5]]$ and `bump(4)` the context $[[4, 4]]$
(@sec:eq-routing). The final store of `bump(5)`, with result $6$, lies in
the activation collecting semantics of context $[[5, 5]]$ at the result node of
`bump`, and the final store of `bump(4)`, with result $5$, in that of context
$[[4, 4]]$. The node collecting semantics at the result node contains both
stores. A store that activations in two contexts reach lies in the sets of
both contexts.

The two sets show what the split by context buys. A single claim for the
result node must contain both stores, so an interval analysis can at best bound the result by $[5, 6]$. A claim per context only has to contain the stores of
its own context, the result $6$ in context $[[5, 5]]$ and the result $5$ in
context $[[4, 4]]$. No store is lost by the split as long as every valid trace carries at
least one context, because then every store of the node collecting semantics
lies in the activation collecting semantics of some context. The coverage
contract of the next section guarantees this.

== The coverage contract #thy-badge("Voblint_CFG", "Activation_Trace_Abstract") <sec:contract>

The goal is a claim #isai("cover") $v$ $c$, a set of stores for each node and
context, that contains #isai("\<A>\<^bsub>\<G>,adm,c₀,g,S\<^esub> v c"). A claim is a mathematical
object, and its sets of stores may be infinite. The analyzer instead computes
abstract values, and @ch:equations takes #isai("cover v c") to be the
concretization of the value computed for $[v, c]$. The coverage contract
reduces the goal to local conditions on #isai("cover") that mention only
stores. It is therefore the interface between the analyzer and the concrete
semantics.

Valid traces grow by four rules, so it is enough to check the claim locally
against the same four cases. #oblig("INIT") covers the root activation,
#oblig("INTRA") a local edge, #oblig("CALL") the entry into a callee and
#oblig("RETURN") the continuation after a callee finishes. Apart from #oblig("INIT"), each of these four obligations looks at one step of a run and requires the
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
    pairs. Solid arrows show where each obligation applies; #oblig("INTRA") may be
    applied repeatedly along an activation path. The dotted arrow is no
    obligation. It shows the caller store $s$ that #oblig("RETURN") reads.
    #oblig("RETURN") combines the caller's store $s$ with the
    callee's result read in the admitted context $c'$. #oblig("TOTAL") demands
    that at least one $c'$ exists.],
) <fig:contract>

The fifth obligation, #oblig("TOTAL"), concerns a call at a call site $u$ in
a caller context $c$ from a caller store $s$. If $s in #isai("cover u c")$,
#oblig("TOTAL") requires the policy to admit at least one callee context for
the call from $s$ (#isaconst("call_context_total_on")).

The other four obligations do not suffice without it
(#isathm("total_dropped_unsound")). At a call that gets no context, #oblig("CALL") and #oblig("RETURN") hold
vacuously, so nothing forces the claim at the continuation, while the resumed
caller keeps its context (#isathm("resume_keeps_context")). A store that the
caller reaches after the return can therefore lie outside the claim.

Asking for contexts at every call would be too strong for entry-state
policies, whose sets are empty for the caller stores that the analysis
excludes (@sec:contexts). The context-insensitive policy and
call strings admit a context for every call and meet #oblig("TOTAL") for every
claim (#isathm("call_context_total_on_of_fun")). For entry-state contexts it
follows from the coverage of the analysis's entry (@sec:eq-routing).
Isabelle states the five obligations as the assumptions of the locale
#isalocale("activation_coverage") (@fig:activation-coverage).

#figure(
  {
    show raw.where(block: true): set text(size: 6pt)
    thy("activation_coverage")
  },
  kind: image,
  placement: top,
  caption: [The declaration of #isalocale("activation_coverage"), lifted from the
    theory. In #oblig("RETURN"), $p'$ and #isai("es") range over every call edge
    out of #isai("u"). On compiled programs a call site has one call edge
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

#block(breakable: false)[
  The same obligations give every valid trace at least one context, so the
  activation collecting semantics of all contexts together are exactly the
  node collecting semantics.

  #theorem(
    name: [Exhaustive contexts],
    isa: "node_collect_eq_Union_activation_collect",
  )[
    Under the five coverage obligations, including #oblig("TOTAL"), the node
    collecting semantics at every node $v$ is the union of the activation
    collecting semantics at $v$ over all contexts.
  ]

  #proved("node_collect_eq_Union_activation_collect")
]

#block(breakable: false)[
  #corollary(name: [Claims cover the collection], isa: "node_collect_covered")[
    Under the five coverage obligations, every store of the node collecting
    semantics at $v$ lies in the claim #isai("cover v c") of some context $c$.
  ]

  #proved("node_collect_covered")
]

Apinis et al. recall the corresponding observation for the abstract side
@apinis12[§3]: after local solving, the abstract values that reach a program
point are bounded by the join of the solution's values at that point over the contexts
the solver encountered.

This chapter has built the concrete half of the soundness argument. Every
finite source execution of a well-formed program is matched by a graph run
(@ch:program-model), which a valid activation trace represents
(@sec:source-bridge). Its contexts place its final store in their activation
collecting semantics (@sec:contexts), which every claim meeting the coverage
contract contains. The following chapters construct
such claims by abstract interpretation, with abstract domains describing sets
of stores (@ch:domains) and equation systems computing the abstract values
(@ch:equations, @ch:solving).
