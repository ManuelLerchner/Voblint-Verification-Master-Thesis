#import "@preview/fletcher:0.5.8" as fletcher: diagram, edge, node
#import "@preview/curryst:0.6.0": prooftree, rule
#import "@preview/cetz:0.5.2"
#import "../lib/math.typ": *
#import "../lib/theme.typ": vb
#import "../lib/figures.typ": *
#import "../lib/code.typ": *
#import "../lib/sources.typ": proved, thy
#import "../lib/theorems.typ": corollary, definition, example, lemma, theorem
#import "../lib/cfg-graphs.typ": sum-graph

= Traces and the Coverage Contract <ch:traces>

In the context-sensitive formulation used here, an analysis computes separate
invariants for the same program point under different calling contexts. To
justify such a result, we need a concrete account of which executions each
context represents.

The node-indexed collecting semantics of @ch:background forgets this. In the
running example, both calls of `bump` reach the same result node, but a
context-sensitive analysis may distinguish the activation entered with $5$ from
the one entered with $4$. This chapter gives that distinction a concrete
meaning.

We represent executions by _activation-local traces_. A trace follows one
procedure activation. A callee trace keeps the caller that created it, and a
resumed trace keeps the callee it has completed. We read calling contexts from
this structure and do not store them in the execution semantics. Context
membership is a relation, so one concrete call may be admitted under several
contexts.

From this semantics we derive a local _coverage contract_. Its obligations are
the concrete interface that the abstract analyses and the equation system of
@ch:domains to @ch:solving must satisfy. Once they hold, every
context-indexed claim covers the executions assigned to its context, and the
union of the context-indexed collections is the trace collecting semantics (@sec:collect).

== Why contexts need traces <sec:why-traces>

The collecting semantics of @ch:background assigns each node $v$ of a
control-flow graph the set of stores that some run holds on reaching $v$
@cousot77[§4], which an unknown $[v]$ per node over-approximates @apinis12[§2]. A
context-sensitive analysis splits $[v]$ into unknowns $[v, c]$, one per calling
context $c$, following the value tables of Sharir and Pnueli @sharir81, as
Apinis et al. formulate them as a constraint system @apinis12[§3].
Seidl et al. state that the invariant for $[u, c]$ "only need[s] to take into
account executions reaching $u$ that satisfy the restriction imposed by context
$c$" @seidl26[§4]. Such a claim states that every store of an execution in
context $c$ at node $v$ is described by the abstract value that the analysis
computes for $[v, c]$.

Take the running example (@fig:program-to-equations): `main` calls `bump(5)`
and then `bump(4)`, and `bump` returns its argument plus one. At the end of
`bump`, the collecting semantics holds two stores, one with argument $5$ and
result $6$, one with argument $4$ and result $5$. An analysis with one context
per argument claims "result $6$ in context $5$". The collecting semantics cannot
justify this claim, because it does not say which of the two stores belongs to
context $5$. It has forgotten which activation holds each store. The two
activations of `bump` use the same nodes, but they were entered
by different calls, and a context policy may use exactly that entry information
to tell them apart.

The graph execution (@sec:cstep) already has a call stack. This stack stores
only what is needed to resume suspended callers. Activation-local traces keep
more of the history. Because a callee trace keeps its creating caller and a
resumed trace keeps both caller and callee, the context relation can choose a
callee context at the call and keep the caller's context across calls and
returns. On well-formed compiled programs, the caller structure of a trace is
proved to match the runtime stack (@sec:source-bridge).

A flat record of the graph run, namely the list of node-store pairs $(v, s)$
that the run passes through (@fig:flat-nested, top), interleaves the steps of
all activations and leaves their nesting implicit. In the program of @fig:cfgmap,
`sum(2)` calls `dec` and then itself, so one run visits the nodes of `sum` in
three activations. To find the context of a step, one has to recover from the
list which call created its activation and which return resumes which caller.

Grouping the same run by activation makes these relationships explicit
(@fig:flat-nested, bottom). Each activation has its own local path. A call
creates a new activation attached to its caller, and a return composes the
finished callee back into that caller. This construction adapts the _local traces_ of Schwarz et al. @schwarz21, each
one thread's view of a concurrent execution, to procedure activations. Here a
local trace is one activation's view of a sequential execution
(@sec:rel-goblint).

@sec:traces turns this grouping into a datatype, gives the rules that make a
trace valid, shows that every graph run is represented by a valid trace, and
reads the trace collecting semantics off the valid traces. @sec:contexts then reads
calling contexts off the same traces.

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

=== Activation-local traces <sec:ltr>

We turn the grouping of @fig:flat-nested into a datatype.

#block(breakable: false)[
  #definition(name: [Activation-local trace], isa: "ltr", cmd: "datatype")[
    A trace has one constructor per way an activation begins or continues.
  ]

  #figure(
    {
      show raw.where(block: true): set text(size: 6.2pt)
      thy("trace")
      thy("ltr")
    },
    kind: image,
    placement: none,
    caption: [The declarations of #isatype("trace") and #isatype("ltr"), lifted from the theory. A #isatype("trace") is a local path, a list of pairs of a CFG node and a store.],
  ) <fig:ltr>
]

$#Root($pi$)$ is the initial activation of the program with local path $pi$.
$#CallT($tau'$, $pi$)$ is a callee created by the caller $tau'$
(#isaconst("ltr_caller")); its local path begins at the callee's entry store.
$#ResumeT($tau'$, $tau''$, $pi$)$ is the activation $tau'$
(#isaconst("ltr_current")) continued past the call that produced the finished
callee $tau''$ (#isaconst("ltr_callee")). The observer
$#isaconst("path") thin tau$ returns the local path,
$#isaconst("sink_node") thin tau$ the node of its last entry and
$#isaconst("sink_store") thin tau$ that entry's store.

Each trace represents the history of one activation up to a program point. On
well-formed compiled programs, its local path stays inside the nodes of one
procedure (#isathm("valid_ltr_frag_callers")). A call creates a separate trace
for the callee, which holds its caller as a field. When the callee finishes, a
$ctor("Resume")$ creates a new trace for the continued caller, which keeps both
the frozen caller and the finished callee. A whole run is therefore a family of
traces linked by these fields. A $ctor("Call")$ stores its caller exactly,
frozen at the call node. So a finished callee composes back into the activation
that created it, and no search for a compatible stack frame is needed. Validity
forces the frozen caller of a $ctor("Resume")$ to be exactly the creating
caller of its callee (#isathm("valid_ltr_Resume_fields")). The context defined
below does not read the finished callee. Both the validity rules and the
context need the activation that created a trace.

#definition(name: [Creating caller], isa: "caller_of", cmd: "fun")[
  The creating caller is a partial function: a $ctor("Root")$ has none.
  #thy("caller_of")
]

A resumed activation is the same activation, so its creating caller is that of
the activation it resumed; the recursion descends through every call the
activation has already made and returned from. The definition mentions no
calling context. @sec:contexts reads the context off the trace instead of
storing it there. A stored context would make the concrete semantics depend on
the analysis. For entry-state routing, the admissible contexts even depend on
the solved table (@sec:eq-routing). Reading the context off the trace lets
every policy share one semantics.

=== Valid traces <sec:valid>

The datatype admits terms that no execution produces: a path whose step follows
no edge, or a $ctor("Resume")$ pairing a caller with a callee that another
activation created. Validity rules such terms out.

#definition(name: [Valid traces], isa: "valid_ltr", cmd: "inductive_set")[
  For a global-variable classifier $cal(G)$, a graph $g$ and a set $S$ of
  initial stores (for VIMP programs #isaconst("cinit_stores"): globals $0$,
  locals arbitrary), #isai("\<T>\<^bsub>\<G>,g,S\<^esub>") (#isaconst("valid_ltr")) is
  the least set of traces closed under the four rules of @fig:valid-rules.
]

#figure(
  thy("valid_ltr"),
  kind: image,
  caption: [The four rules of #isaconst("valid_ltr"): init, intra, call and
    ret. Each reads the relation for its own phenomenon: #isaconst("intra")
    for local flow, #isaconst("calls") for entering a callee and for
    recovering the continuation $italic("cont")$ at a return.],
) <fig:valid-rules>

Init corresponds to the initial graph configuration, and the other three rules
correspond to the three rules of #isaconst("cstep"). Intra appends a step along
a local edge. Call starts a new trace that holds the caller, where
#isaconst("cstep") pushes a frame. Ret builds a third trace that holds caller
and callee, where #isaconst("cstep") pops the frame. After the pop the graph
configuration no longer records the finished call, but the
$ctor("Resume")$ trace still holds the caller, so the caller's context can be
read from it.

The ret rule follows no edge out of #isai("FunctionResult p"). It reads the
continuation from a #isaconst("calls") tuple that leaves the caller's call node
and enters $p$, so one result node serves every caller of $p$. On compiled
graphs each call node has a single outgoing #isaconst("calls") tuple
(#isaconst("calls_source_unique"), #isathm("compile_prog_calls_source_unique")),
so this is the tuple through which the callee was entered. The premise
#isai("caller_of callee = Some caller") reads the caller from the callee's own
structure. No separate matching invariant is needed.

=== Graph runs are valid traces <sec:source-bridge>

The traces are meant to describe the runs of the compiled graph, and through
@sec:csim the runs of VIMP programs.

#block(breakable: false)[
  #definition(name: [Trace representation], isa: "ltr_repr", cmd: "definition")[
    A valid trace represents a graph configuration if it ends at the
    configuration's node and store and its chain of creating callers matches
    the runtime frame stack.
  ]

  #figure(
    {
      show raw.where(block: true): set text(size: 6pt)
      thy("stack_repr")
      thy("ltr_repr")
    },
    kind: image,
    placement: none,
    caption: [The declarations of #isaconst("stack_repr") and
      #isaconst("ltr_repr"), lifted from the theory.],
  ) <fig:ltr-repr>
]

For a well-formed compiled program (#isaconst("wf_compile_input")), the
correspondence is lock-step. A local graph step extends the current trace, a
call creates a $ctor("Call")$ trace, and a return creates a $ctor("Resume")$
trace (#isathm("cstep_preserves_ltr_repr")). The initial configuration is
represented by a $ctor("Root")$ trace (#isathm("located_ltr_entry")). Hence
every configuration that a graph run of such a program reaches has a
representing valid trace (#isathm("csteps_preserve_located_ltr")). Only this
direction is proved, and soundness needs only this direction. Composed with the
simulation of @ch:program-model, it extends to VIMP programs.

#theorem(name: [Source runs are traces], isa: "source_run_has_ltr")[
  For a well-formed compiled program, every finite source execution from an
  initial store in $S$ has a matching graph configuration and a valid trace ending at
  the same node with the same store, whose caller chain represents the graph's
  frame stack.
]

#proved("source_run_has_ltr")

=== The trace collecting semantics <sec:collect>

From the valid traces we can read off which stores some activation can hold
at a node. This gives the _trace collecting semantics_, a counterpart of the
node-indexed collecting semantics of @ch:background.

#block(breakable: false)[
  #definition(name: [Trace collecting semantics], isa: "ltr_collect", cmd: "definition")[
    #thy("ltr_collect")
  ]
]

A store is in #isai("\<C>\<^bsub>\<G>,g,S\<^esub> v") exactly when some valid
trace ends at $v$ with this store. The classifier, graph and initial stores
are those of the program at hand, written #isai("\<G>"), #isai("g") and
#isai("S") from here on. In @fig:flat-nested, the three activations of `sum`
reach #raw("exit_sum") with different stores; the collected set keeps the
stores and forgets which activation held each. A procedure's result is an
ordinary collected node, and whole-program completion is collection at
$ctor("FunctionResult") italic("main")$.

#isaconst("ltr_collect") is a function from nodes to store sets, like the
intraprocedural collecting semantics of @ch:background, so a claim stated over
it alone is context-insensitive. The trace structure remains available in
#isaconst("valid_ltr"), and @sec:contexts reads the context off it.

By @sec:source-bridge, every store that a finite source execution of a
well-formed program reaches lies in the trace collecting semantics at a related node
(#isathm("source_reaches_ltr_collect")).
The node is existential because #isaconst("csim") is not functional
(@sec:csim).

== Calling contexts, as a relation <sec:contexts>

A _context_ is the key under which an activation is analyzed. At a fixed node,
activations with the same context contribute to the same abstract unknown
$[v, c]$. The classical designs differ in what a context records @sharir81 @rival20[§8.4.1] @seidl12compiler[§2.6] @seidl12compiler[§2.9]. The call-string approach records the call history, and practical variants bound it to the $k$ most recent call sites, since a recursive procedure otherwise has infinitely many contexts. The functional approach computes a procedure summary independent of callers, which each call site instantiates. Goblint computes the callee context after its entry operation, by passing each
resulting callee entry state to the analysis's `context` operation
(@app:goblint-alignment), and Erhard et al. treat full entry states, their projections and call strings in one framework @erhard25[§4]. Voblint offers the context-insensitive policy, bounded call strings and entry-state contexts (#isatype("context_mode"), @ch:equations).

Voblint models context membership as a relation, because Goblint's entry
operation may answer one call with several pairs of a caller continuation and a
callee entry state, each routed to its own context.
Its path-sensitive lifter uses this to enter the callee once for each path of
the caller
(#link("https://github.com/goblint/analyzer/blob/5320a6b741e50dc049f7a1b85e1709e9565cc54a/src/lifters/specLifters.ml")[`PathSensitive2`]).
When such alternatives overlap, one concrete call belongs to several contexts
at once. Suppose the caller knows $x in [0, 9]$ before a call
`h(x)` and the entry operation splits the parameter's range into the
alternatives $[0, 5]$ and $[3, 9]$. For a sound split, the alternatives must together cover the caller's value,
but they need not be disjoint. Entry-state routing
(#isaconst("routed_entry_context_rel")) sends each to the context named by its
entry value, $c_1$ and $c_2$. A concrete call with $x = 4$ lies in both
alternatives, and both analyses of `h` describe it. A function would force the
concrete semantics to choose one of them, although no execution determines the
choice. A relation can admit both $c_1$ and $c_2$, as the analysis does. For a
Sign specification whose entry operation returns two overlapping alternatives,
#isathm("ov_two_contexts_admitted") proves that one concrete call is admitted
under two distinct contexts. The shipped numeric analyses are built from the shared local-state
specification (#isaconst("analysis_spec")), whose entry operation returns a
single alternative (#isathm("dgs_enter_local_state_st_for_lifted")). By the definition of
#isaconst("routed_entry_context_rel"), a concrete call then admits at most one
callee context from a fixed caller context.

The analyzer does not choose between $c_1$ and $c_2$. It analyzes every
admitted context, and @sec:eq-call shows how the call equation joins them.

#block(breakable: false)[
  #definition(name: [Call-context relation], isa: "call_context_rel", cmd: "type_synonym")[
    A call-context relation says which callee contexts are admissible for a call.
  ]

  #figure(
    {
      show raw.where(block: true): set text(size: 6.2pt)
      thy("call_context_rel")
    },
    kind: image,
    placement: none,
    caption: [The declaration of #isatype("call_context_rel"), lifted from the theory.],
  ) <fig:call-context-rel>
]

A call-context relation $R$ decides whether a candidate callee context $c'$ is
admissible for a concrete call. It may depend on the call, the caller's context,
the caller's store and the entered store. Ordinary context functions are the
special case that admits exactly one context
(#isaconst("call_context_rel_of_fun")). Both stores are present because an
analysis may split a call into several pairs of a caller value and a callee
entry value, and soundness requires one such pair to cover the concrete call as
a whole (@sec:calls). #isaconst("admits_call_context") holds for a call site
$u$, a caller context, a callee $p$, a caller store $s$, an entered store and a
callee context $c'$ when some #isaconst("calls") edge from $u$ enters $p$ with
exactly this entered store and $R$ admits $c'$ for that edge. The context of a
whole trace is built from these calls.

#block(breakable: false)[
  #definition(name: [Context of a trace], isa: "trace_context", cmd: "inductive")[
    #isai("trace_context \<G> R startcontext g t ctx") reads "$t$ may carry
    #isai("ctx")".
  ]

  #figure(
    {
      show raw.where(block: true): set text(size: 6pt)
      thy("trace_context")
    },
    kind: image,
    placement: none,
    caption: [The declaration of #isaconst("trace_context"), lifted from the theory.],
  ) <fig:trace-context>
]

A $ctor("Root")$ carries only the initial context #isai("startcontext"). A
$ctor("Call")$ trace whose path starts at #isai("FunctionEntry p") with entered
store #isai("es") carries every context that is admitted, from some context of its
caller, for a call to $p$ with this entered store. Admission is checked at the
caller's last node and store. A $ctor("Resume")$ carries the contexts of the
resumed caller. So the contexts an activation may carry are determined when it is created,
and $ctor("Resume")$ keeps them while the activation calls and returns from
other procedures.
The classifier, the graph, the relation $R$ and the initial context are fixed
per program.

With the context of a trace in hand, the trace collecting semantics of @sec:collect
can be split by context. A store belongs to context $c$ at node $v$ if some
valid trace ending at $v$ with that store carries $c$.

#block(breakable: false)[
  #definition(
    name: [Context-indexed collecting semantics],
    isa: "activation_collect",
    cmd: "definition",
  )[
    #thy("activation_collect")
  ]
]

#isaconst("activation_collect") collects the final stores of the valid traces
that end at $v$ and carry $c$. This is the concrete set that the claim for
$[v, c]$ must over-approximate, relative to the policy #isai("R"). For a
fixed node $v$, we call these context-indexed sets the _buckets_ of $v$, an
informal shorthand for #isai("\<A>\<^bsub>\<G>,R,startcontext,g,S\<^esub> v c").
In the example of @sec:why-traces, with one context per argument, the final
store of the `bump(5)` activation belongs to the bucket of context $5$, and
the final store of `bump(4)` to the bucket of context $4$.

Unlike the classes of a partition, buckets may overlap: one trace may carry
several contexts, as the call of `h` with $x = 4$ does (@fig:buckets, right).
Under a functional policy the bucket of $c$ contains the final stores of the
traces whose key, computed by the context function, is $c$
(#isathm("activation_collect_of_fun")). Each valid trace then carries exactly
one context, so the traces fall into disjoint classes. The buckets may still
overlap, because two traces in different contexts may end in the same store.

Soundness needs neither functional contexts nor disjoint buckets. The claim for
each context only has to cover that context's bucket. A store in two buckets is
covered twice, once by each claim. The end-to-end argument does need the
buckets together to cover the trace collecting semantics, since a store in no bucket
would escape every claim. The contract establishes the stronger sufficient property that every valid
trace carries at least one context.

// The grey region is the collecting semantics at the node; the context
// regions tile it completely (a cover), overlapping only on the right.
#let _bucket-panel(title, regions, dots) = cetz.canvas(length: 1cm, {
  import cetz.draw: *
  let (w, h) = (4.2, 2.2)
  for (i, (x0, x1, col, lab)) in regions.enumerate() {
    rect((x0, 0), (x1, h), stroke: 0.9pt + col, fill: col.lighten(80%).transparentize(35%))
    // Stagger the spans only where regions overlap.
    let overlap = regions.len() > 1 and regions.at(0).at(1) > regions.at(1).at(0)
    let y = h + 0.15 + (if overlap { 0.3 * i } else { 0 })
    line((x0, y), (x1, y), stroke: 0.9pt + col, mark: (start: "|", end: "|"))
    content(((x0 + x1) / 2, y + 0.17), text(size: 7pt, fill: col, weight: "bold", lab))
  }
  rect((0, 0), (w, h), stroke: 0.8pt + vb.neutral, fill: none)
  content((w / 2, -0.28), text(size: 7pt, fill: vb.muted, title))
  for (pos, lab) in dots {
    circle(pos, radius: 0.06, fill: vb.neutral, stroke: none)
    content((pos.at(0), pos.at(1) - 0.24), text(size: 6.5pt, font: "DejaVu Sans Mono", lab))
  }
})
#figure(
  grid(
    columns: 2,
    column-gutter: 18pt,
    align: bottom,
    _bucket-panel(
      [#isai("\<C>\<^bsub>\<G>,g,S\<^esub> v") at the result of `bump`],
      ((0, 2.1, vb.accent, [context $5$]), (2.1, 4.2, vb.sign, [context $4$])),
      (((1.05, 1.15), "bump(5)"), ((3.15, 1.15), "bump(4)")),
    ),
    _bucket-panel(
      [#isai("\<C>\<^bsub>\<G>,g,S\<^esub> v") at the entry of `h`],
      ((0, 2.7, vb.accent, [$c_1$]), (1.5, 4.2, vb.cong, [$c_2$])),
      (((0.7, 1.15), "x=1"), ((2.1, 1.15), "x=4"), ((3.5, 1.15), "x=8")),
    ),
  ),
  kind: image,
  placement: none,
  caption: [Buckets inside the trace collecting semantics #isai("\<C>\<^bsub>\<G>,g,S\<^esub> v")
    (black frame). In these examples the buckets together fill it. Left: the runs of
    `bump` split into the buckets of contexts $5$ and $4$, a partition. Right:
    with overlapping entry alternatives $[0, 5]$ and $[3, 9]$, the call with
    $x = 4$ lies in both buckets, which cover the collection without
    partitioning it. Illustrative.],
) <fig:buckets>

Forcing the buckets into a partition would also be arbitrary. Both analyses of
`h` describe the call with $x = 4$, and no execution decides whether it belongs
to $c_1$ or to $c_2$. Overlapping buckets avoid this choice: the call lies in
every context whose analysis describes it.

This covering can fail. If $R$ admits no context for a call, the resulting
callee trace carries no context and contributes to no bucket. Unless another
trace with a context reaches the same store, the union misses it. The contract
therefore requires every covered call state to admit at least one callee
context.

Demanding this of $R$ for every call and every store would be too strong. An
entry-state policy admits the contexts that the analysis computed for the
call. For a call that the analysis considers unreachable it computed nothing,
and it admits no context there. The requirement is therefore stated relative
to the claim. $R$ must admit a context only for the stores that the claim
itself covers at a call site. This is why the totality is _conditional_.

#figure(
  cetz.canvas(length: 1cm, {
    import cetz.draw: *
    let dot(p, name, hollow: false) = {
      circle(
        p,
        radius: 0.07,
        fill: if hollow { white } else { vb.neutral },
        stroke: 0.7pt + vb.neutral,
        name: name,
      )
    }
    // Call site u in context c; the claim's stores sit in the dashed region.
    rect((0, 0), (3.2, 2.6), stroke: 0.8pt + vb.neutral, fill: vb.bg, radius: 0.15)
    content((1.6, 2.85), text(size: 7.5pt)[call site $u$, context $c$])
    rect(
      (0.3, 0.85),
      (2.9, 2.3),
      stroke: (paint: vb.accent, thickness: 0.9pt, dash: "dashed"),
      radius: 0.1,
    )
    content((1.6, 1.0), text(size: 6.5pt, fill: vb.accent)[covered by the claim])
    dot((0.9, 2.0), "s1")
    dot((1.6, 1.6), "s2")
    dot((2.3, 2.0), "s3")
    dot((1.6, 0.42), "s4", hollow: true)
    content((2.35, 0.42), anchor: "west", text(size: 6.5pt, fill: vb.muted)[exempt])
    let cx = 5.6
    for (i, (lab, col)) in (
      ([$c'_1$], vb.accent),
      ([$c'_2$], vb.sign),
      ([$c'_3$], vb.cong),
    ).enumerate() {
      let y = 2.2 - 0.8 * i
      rect(
        (cx, y - 0.28),
        (cx + 1.3, y + 0.28),
        stroke: 0.8pt + col,
        fill: col.lighten(85%),
        radius: 0.1,
        name: "k" + str(i),
      )
      content((cx + 0.65, y), text(size: 7.5pt, fill: col, weight: "bold", lab))
    }
    content((cx + 0.65, 2.85), text(size: 7.5pt)[callee entry])
    let arr(a, b) = line(a, b, stroke: 0.7pt + vb.called, mark: (end: ">", fill: vb.called))
    arr("s1", "k0.west")
    arr("s2", "k1.west")
    arr("s3", "k1.west")
    arr("s3", "k2.west")
  }),
  kind: image,
  placement: none,
  caption: [Conditional totality at one call edge. Every store that the claim
    covers at the call site (dashed) needs at least one callee context that
    $R$ admits (arrows); a store may get several. A store outside the claim
    (hollow) needs none. Illustrative.],
) <fig:total>

#block(breakable: false)[
  #definition(name: [Conditional totality], isa: "call_context_total_on", cmd: "definition")[
    At every call edge, every store the claim admits at the call site in a
    context $c$ has _some_ callee context that $R$ admits from $c$.
  ]

  #figure(
    {
      show raw.where(block: true): set text(size: 6pt)
      thy("call_context_total_on")
    },
    kind: image,
    placement: none,
    caption: [The declaration of #isaconst("call_context_total_on"), lifted from the theory.],
  ) <fig:call-context-total-on>
]

Read from left to right (@fig:total), the definition says the following. For
every call edge from $u$, every context $c$ and every store $s$ that the claim
covers at $u$ in $c$, $R$ admits some callee context $c'$ for this call from
$c$ with the entered store. Stores outside the claim impose nothing. Together with the four closure
obligations, this suffices for soundness. The proof follows a run step by step. When the run
reaches a call site, the other obligations have already placed its store in the
claim there, so the condition applies and the callee gets a context.

A functional policy satisfies the condition for every claim, since it always
names exactly one context (#isathm("call_context_total_on_of_fun")). Call
strings are functional in this sense: the callee's context is the caller's
context extended by the call site and cut to the last $k$ calls
(#isaconst("cs_context")). In the
running example, the policy that gives each call of `bump` the context of its
argument is such a function: `bump(5)` enters context $5$ and `bump(4)` enters
context $4$, whatever the claim is. A relational policy such as entry-state
routing reads the admitted contexts off the computed claim and has to discharge
the condition against it. For entry-state routing this follows from paired
entry coverage (@sec:eq-routing).

== The coverage contract <sec:contract>

A claim #isai("cover") maps a node $v$ and a context $c$ to a set of stores. It
is meant to contain every store that can reach $v$ in context $c$. Like the
collecting semantics, a claim is a mathematical object. Its sets of stores may
be infinite, so the analyzer does not compute it directly. The following chapters turn the solver's result into an abstract reader indexed
by $(v, c)$; only the unknowns the solver encounters need to be computed. In
the routed instance, #isai("cover v c") is the concretization of the value this
reader returns for $(v, c)$ (@ch:equations). The contract below is therefore the interface between the
analyzer and the concrete semantics. It mentions only stores and no abstract
domain.

Valid traces grow by four rules, so it is enough to check the claim locally
against the same four cases. #oblig("INIT") covers the root activation,
#oblig("INTRA") a local edge, #oblig("CALL") the entry into a callee and
#oblig("RETURN") the continuation after a callee finishes. A fifth condition,
#oblig("TOTAL"), ensures that a call from a covered store is not lost because
the relation admits no callee context. @fig:contract shows the five obligations
at one call.

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
    applied repeatedly along a local path. The dotted arrow is no
    obligation. It shows the caller store $s$ that #oblig("RETURN") reads.
    #oblig("RETURN") combines the caller's store $s$ with the
    callee's result read in the admitted context $c'$. #oblig("TOTAL") demands
    that at least one $c'$ exists (@fig:total).],
) <fig:contract>


Isabelle states the obligations as the assumptions of the locale
#isalocale("ltr_coverage") (@fig:ltr-coverage). In #oblig("RETURN"), the
admitted call is named by $p'$ and #isai("es"). They are bound separately from
the call edge of the first premise, so the obligation covers every context
admitted for any call edge out of #isai("cl"). On compiled programs a call site
has only one call edge (#isathm("compile_prog_calls_source_unique")), so
$p' = p$.

#figure(
  {
    show raw.where(block: true): set text(size: 6pt)
    thy("ltr_coverage")
  },
  kind: image,
  placement: auto,
  caption: [The declaration of #isalocale("ltr_coverage"), lifted from the theory.],
) <fig:ltr-coverage>

=== What the contract gives <sec:consequences>

The contract has two consequences. First, each context's bucket lies inside
that context's claim, which is the per-context soundness statement. Second, under the full contract, #oblig("TOTAL") supplies the existence step
that shows every valid trace carries at least one context, so the
union of the buckets is exactly the trace collecting semantics
(@fig:buckets).

The proof of the first consequence is a rule induction over the valid traces.
Each rule of #isaconst("valid_ltr") matches one obligation: a root trace is
covered by #oblig("INIT"), an extended trace by #oblig("INTRA"), a callee trace
by #oblig("CALL"), and a resumed trace by #oblig("RETURN"). #oblig("TOTAL")
supplies an admitted callee context in the call and return cases. The return case
needs a bound on the caller as well as on the finished callee, so the induction
hypothesis is strengthened to every trace on the chain of creating callers
(#isathm("caller_chain_closure")).

#block(breakable: false)[
  #theorem(name: [Context-indexed soundness], isa: "activation_collect_sound")[
    Assume the five obligations. Then for every node $v$ and context $c$,
    #align(center, isai("\<A>\<^bsub>\<G>,R,startcontext,g,S\<^esub> v c \<subseteq> cover v c"))
  ]

  #proved("activation_collect_sound")
]

#theorem(
  name: [Exhaustive buckets],
  isa: "ltr_collect_eq_Union_activation_collect",
)[
  Under the five coverage obligations, including #oblig("TOTAL"),
  #align(
    center,
    isai(
      "\<C>\<^bsub>\<G>,g,S\<^esub> v = (\<Union>c. \<A>\<^bsub>\<G>,R,startcontext,g,S\<^esub> v c)",
    ),
  )
]

#proved("ltr_collect_eq_Union_activation_collect")

With this equality, a context-specific claim can be more precise than a single
sound claim that must cover the whole node, as "result $6$ in context $5$" for
`bump`, while the union of the buckets still contains every store of the
trace collecting semantics. For the abstract side, Apinis et al. @apinis12[§3] observe that after local
solving, a program point can only be reached by
abstract values bounded by the join of the partial solution's values at that
point over the contexts that the solver encountered. Here we make the corresponding concrete sets explicit for our relational
trace semantics and prove that each is covered by its claim.

@fig:ch4-chain summarizes the chapter. A context is a property of an
activation trace, and the five coverage obligations guarantee that the claim
covers every context's bucket. With #oblig("TOTAL"), the buckets together
recover the trace collecting semantics. For well-formed programs, the trace
representation and the forward simulation of @ch:program-model transfer these
guarantees to finite VIMP source executions. The following chapters construct
such claims from abstract domains and equations.

#let _step(pos, name, body) = node(
  pos,
  text(size: 7.5pt, body),
  stroke: 0.8pt + vb.neutral,
  fill: vb.bg,
  corner-radius: 3pt,
  inset: 5pt,
  name: name,
)
#let _via(body) = text(size: 6.5pt, fill: vb.muted, body)
#figure(
  diagram(
    spacing: (11mm, 10mm),
    label-size: 6.5pt,
    _step((0, 0), <h-src>, [VIMP source run]),
    _step((1, 0), <h-cfg>, [graph run]),
    _step((2, 0), <h-tr>, [valid trace]),
    _step((3, 0), <h-bk>, [buckets #isai("\<A>") $v$ $c$, all $c$]),
    _step((4, 0), <h-cl>, [claims #isai("cover") $v$ $c$, all $c$]),
    _step((3, 1), <h-col>, [collection #isai("\<C>") $v$]),
    edge(<h-src>, <h-cfg>, "-|>", label: _via[simulation], label-side: left),
    edge(<h-cfg>, <h-tr>, "-|>", label: _via[represents], label-side: left),
    edge(<h-tr>, <h-bk>, "-|>", label: _via[context], label-side: left),
    edge(<h-bk>, <h-cl>, "-|>", label: _via[each $subset.eq$], label-side: left),
    edge(
      <h-bk>,
      <h-col>,
      "-|>",
      label: _via[union $=$, with #smallcaps("Total")],
      label-side: left,
    ),
  ),
  kind: image,
  placement: none,
  caption: [The links of this chapter. A source run is represented by a valid
    trace. The trace's contexts place its store in the buckets of those
    contexts. The
    coverage contract bounds each bucket by the claim for its context, and with
    #oblig("TOTAL") the union of all buckets is the trace collecting semantics.],
) <fig:ch4-chain>
