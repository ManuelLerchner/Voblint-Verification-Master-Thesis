#import "@preview/fletcher:0.5.8" as fletcher: diagram, edge, node
#import "../lib/math.typ": *
#import "../lib/theme.typ": vb
#import "../lib/figures.typ": *
#import "../lib/code.typ": *
#import "../lib/sources.typ": proved, thy
#import "../lib/theorems.typ": corollary, definition, example, lemma, theorem
#import "../lib/cfg-graphs.typ": sum-graph

= Traces and the Coverage Contract <ch:traces>

@ch:program-model matched every source execution with a graph execution.
For an analysis that computes one abstract state per node, this suffices. A
context-sensitive analysis, however, computes a separate state for each node and
calling context, so justifying its result requires knowing which executions each
context stands for. This chapter gives that distinction a concrete meaning. It
groups executions into _activation traces_, reads calling contexts off them,
and states the _coverage contract_, the local conditions under which an
analysis result contains every store that an execution brings to a node in a
context.

== Why calling contexts need activation traces <sec:why-traces>

A context-sensitive analysis splits the unknown $[v]$ of a node into unknowns
$[v, c]$, one per calling context $c$ (@sec:interproc). Seidl et al. state that the invariant for
$[u, c]$ "only need[s] to take into account executions reaching $u$ that
satisfy the restriction imposed by context $c$" @seidl26[§4]. The abstract state
for $[v, c]$ therefore has to describe only a subset of the stores that the
state for $[v]$ describes, and it can be correspondingly more precise.

For the calls `bump(5)` and `bump(4)` of the running example
(@fig:program-to-equations), an analysis with entry-state contexts claims the
result $6$ in the context of the first call and $5$ in that of the second
(@sec:interproc). To justify these claims, it must be known which store at the
result node of `bump` belongs to which call. The collecting semantics, however, is too weak to tell. It holds
both stores at the result node but does not record which activation reached
each of them, so a richer semantics that keeps this information is needed.

Contexts depend on how an activation was created, for example, on its call site
or arguments and on the context of its caller (@sec:contexts). After a return,
the caller must continue in the contexts it had before the call.
Neither the graph execution nor a flat record of its runs exposes this. Each
frame of the stack in @sec:cstep holds only what execution needs to resume its
caller, and the frame disappears once the call has returned. The list of
node-store pairs $(v, s)$ that a run passes through (@fig:flat-nested, top)
interleaves the steps of all activations. In the program of @fig:cfgmap,
`sum(2)` calls `dec` and then itself, so one run visits the nodes of `sum` in
three activations, and the list does not say which call created each of them
or which return resumes which caller.

Grouping the same run by activation, in contrast, makes these relationships
explicit (@fig:flat-nested, bottom). Each call of a procedure starts a new
_activation_, which lasts until the call returns @aho06[§7.2.1], and each
activation has its own activation path. A call creates a new activation attached to its caller, and a return
composes the finished callee back into that caller.

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

== From graph executions to activation traces <sec:traces>

Activation traces adapt the _local traces_ of threads @schwarz21 to procedure activations.

=== Grouping a run by activation #thy-badge("Voblint_CFG", "Activation_Trace_Def") <sec:activation-trace>

The grouping of @fig:flat-nested becomes a datatype with one constructor per
way a box arises. The outermost box, the activation of `main`, is a root. A box
opened by a call is a callee trace and remembers its caller. When a callee
finishes, its caller continues in a new trace that remembers both the caller at
the call and the finished callee.

#block(breakable: false)[
  #definition(name: [Activation trace], isa: "activation_trace", cmd: "datatype")[
    A trace has one constructor per way an activation begins or continues.
    Its #isatype("activation_path") is the path of one activation, a list of
    pairs of a CFG node and a store.
  ]

  #{
    show raw.where(block: true): set text(size: 6.2pt)
    thy("activation_path")
    thy("activation_trace")
  }
]

$#Root($pi$)$ is the initial activation of the program with activation path
$pi$. A run starts with $#Root($[(italic("entry"), s_0)]$)$, the entry node of
the graph, which is the entry of `main`, paired with an initial store $s_0$.
$#CallT($t'$, $pi$)$ is a callee created by the caller $t'$. Its activation path begins at the callee's entered store.
$#ResumeT($t'$, $t''$, $pi$)$ is the activation $t'$ continued past the call that produced the finished
callee $t''$. The observer
$#isaconst("path_of") thin t$ returns the activation path,
$#isaconst("sink_node") thin t$ the node of its last entry,
$#isaconst("sink_store") thin t$ that entry's store, and
$#isaconst("caller_of") thin t$ the caller that created the activation, which
a $ctor("Root")$ does not have. The
#link(site("index.html#observers"))[explainer page] shows these observers interactively on a
run of the program of @fig:flat-nested.

Each trace represents the history of one activation up to a program point, so
on well-formed compiled programs, its activation path stays inside the nodes of
one procedure (#isathm("valid_activation_trace_frag_callers")). A callee is a
new activation and gets a trace of its own, which holds its caller as a field.
When the callee finishes, a $ctor("Resume")$ creates a new trace for the
resumed caller, which holds both the frozen caller and the finished callee.
A whole run is therefore a family of traces linked by these fields.

Because a $ctor("Call", thy: "Activation_Trace_Def")$ stores its caller
exactly, frozen at the call site, a finished callee composes back into the
activation that created it, and no search for a compatible stack frame is
needed. This is what makes context-specific return flow sound. A return
continues exactly the caller that created the callee, in each context that
caller carries, so the exit state of a callee entered in context $c'$ flows back only to
the callers whose calls admitted $c'$. The abstract state for a context therefore needs to
describe only the executions in that context.

This design follows the local traces of Schwarz et al. @schwarz21[§3]. A
local trace is the view of one thread on a concurrent execution and ends at a
program point with that thread's local state. The set of local traces is
defined inductively, from initial traces, a rule that starts a created thread
with the local state of its creator, and one rule per edge that extends a
trace by a step. For a lock, this rule also incorporates a second trace, one
that ends in an unlock of the same mutex. Activation traces take over this
scheme with an activation in place of a thread. $ctor("Root")$ corresponds to
an initial trace, $ctor("Call", thy: "Activation_Trace_Def")$ to thread
creation, a local step to a unary edge rule, and $ctor("Resume")$ to the
binary lock rule, which here incorporates the finished callee. The traces
themselves differ. A local trace is an acyclic graph of events from several
threads, ordered by program order and by the creation and locking orders, and
a lock may incorporate a trace of whichever thread last released the mutex. An
activation trace holds the path of a single activation and refers to at most
two other traces, and a $ctor("Resume")$ accepts only the callee that this
activation itself created. Activations do not run concurrently, so nothing
corresponds to reading globals written by another thread.

=== Valid traces follow graph steps #thy-badge("Voblint_CFG", "Activation_Trace_Def") <sec:valid>

The datatype also admits terms that no execution produces. A path may contain
a step that follows no edge of the graph, for instance, a jump from the entry of
`sum` directly to its result node. A $ctor("Resume")$ may pair a caller with a
callee that another activation created, for instance, continue `main` after its
call `sum(2)` with the finished inner activation `sum(1)`, whose caller is
`sum(2)`. Validity rules out such terms by
defining how traces arise. A trace is valid if it can be built from
an initial store by rules that mirror the steps of graph execution, one for
starting the program, one for a local edge, one for a call, and one for a
return. Every step that a valid trace records then follows an edge of the
graph, and every $ctor("Resume")$ combines a caller with the callee that it
created itself.

#block(breakable: false)[
  #definition(name: [Valid traces], isa: "valid_activation_trace", cmd: "inductive_set")[
    For a global-variable classifier $cal(G)$, a graph $g$, and a set $S$ of
    initial stores, #isai("\<T>\<^bsub>\<G>,g,S\<^esub>") (#isaconst("valid_activation_trace")) is
    the least set of traces closed under the following four rules.
  ]

  #thy("valid_activation_trace")
]

The root rule corresponds to the initial graph configuration, and the other
three rules correspond to the three rules of #isaconst("cstep"). Intra appends
a step along a local edge. Call starts a new trace that holds the caller, where
#isaconst("cstep") pushes a frame. Ret builds a third trace that holds the caller
and the callee, where #isaconst("cstep") pops the frame.

The ret rule applies when a callee trace has reached a result node
#isai("FunctionResult p"), which no edge leaves in a compiled graph. The rule
finds the caller through #isai("caller_of callee = Some caller") and takes the
#isaconst("calls") edge from its call site into $p$. That edge names the
continuation $italic("cont")$, where the caller continues with the store that
#isaconst("combine_collect") builds from both final stores.

=== Every source execution yields a valid trace #thy-badge("Voblint_Compile", "Source_To_Trace") <sec:source-bridge>

The rules of valid traces mirror the rules of #isaconst("cstep"), but nothing
so far states that a graph execution actually yields a valid trace. Graph configurations are therefore related to traces.
Besides the node and the store, the relation matches the trace's callers with
the frame stack, so that it still holds after a return.

#block(breakable: false)[
  #definition(name: [Trace representation], isa: "activation_trace_repr", cmd: "definition")[
    A valid trace represents a graph configuration if it ends at the configuration's node and store, and its chain of creating callers matches
    the runtime frame stack.
  ]

  #{
    show raw.where(block: true): set text(size: 6pt)
    thy("stack_repr")
    thy("activation_trace_repr")
  }
]

For a well-formed compiled program (#isaconst("wf_compile_input")), the
correspondence is lock-step. A local graph step extends the current trace, a
call creates a $ctor("Call", thy: "Activation_Trace_Def")$ trace, and a return creates a $ctor("Resume")$
trace (#isathm("cstep_preserves_activation_trace_repr")). The initial configuration has a representing trace, a $ctor("Root")$ trace
(#isathm("located_activation_trace_entry")). Hence,
every configuration that a graph execution of such a program reaches has a
representing valid trace (#isathm("csteps_preserve_located_activation_trace")). The converse is neither proved nor needed.

#block(breakable: false)[
  #theorem(name: [Source executions are traces], isa: "source_run_has_activation_trace")[
    For a well-formed compiled program, every finite source execution from an
    initial store in $S$ has a matching graph configuration and a valid trace ending at
    the same node with the same store, whose caller chain represents the graph's
    frame stack.
  ]

  #{
    show raw.where(block: true): set text(size: 6.2pt)
    proved("source_run_has_activation_trace")
  }
]

The proof composes the simulation of @sec:csim (#isathm("csim_star")) with
the lock-step correspondence above. The source configuration, the graph
configuration, and the trace hold the same store, so every store a source
execution reaches is the final store of a valid trace.

=== Collecting trace stores per node #thy-badge("Voblint_CFG", "Activation_Trace_Collect") <sec:collect>

Collecting the final stores of the valid traces per node gives the _node
collecting semantics_. It plays the role of the collecting semantics of @ch:background for programs
with procedures, with valid traces in place of runs.

#block(breakable: false)[
  #definition(name: [Node collecting semantics], isa: "node_collect", cmd: "definition")[
    #thy("node_collect")
  ]
]

A store is in #isai("\<C>\<^bsub>\<G>,g,S\<^esub> v") exactly when some valid
trace ends at $v$ with this store. The classifier, graph, and initial stores
are those of the program at hand, written #isai("\<G>"), #isai("g"), and
#isai("S") from here on. A procedure's result is an ordinary collected node,
and the stores in which a run of the whole program completes are those collected at $ctor("FunctionResult") italic("main")$. Every store that a finite source
execution of a well-formed program reaches therefore lies in the node
collecting semantics at a corresponding node
(#isathm("source_reaches_node_collect")).

The node collecting semantics forgets the traces, so a soundness statement
over it alone is context-insensitive. The valid traces themselves, however, keep their
structure. The same set of traces thus supports two views: collected per node,
and split by context (@sec:contexts).

== Assigning calling contexts to traces #thy-badge("Voblint_CFG", "Activation_Trace_Context") <sec:contexts>

A context-sensitive analysis of the running example claims the result $6$ for
`bump` in the context of the call `bump(5)` and $5$ in that of `bump(4)`. Checking
such claims requires knowing which executions each context stands for. This
section assigns contexts to activation traces and uses them to split the
stores collected at each node.

Contexts are chosen at calls. When `main` calls `bump(5)`, the analysis decides
in which context it analyzes the callee. With call strings of length one, the
context is the call site in `main`. With entry-state contexts, it is the
abstract value of the formal parameter at the callee's entry, $[[5, 5]]$ under
Interval (@sec:eq-routing). In general, the choice may depend on the call site,
on the caller's context, which call strings extend, on the call itself, which
names the callee, its formals, arguments, and destination, and on the
caller's store and the _entered store_, the store at the callee's entry after
the formals have been bound. A _context policy_ fixes this choice for every
concrete call.

#block(breakable: false)[
  #definition(name: [Context policy], isa: "context_policy", cmd: "type_synonym")[
    A context policy maps a concrete call to the set of callee contexts it admits.
  ]

  #{
    show raw.where(block: true): set text(size: 6.2pt)
    thy("context_policy")
  }
]

A policy returns a set of contexts rather than one, because an analysis may
split a call into cases. Goblint's entry operation may return several
alternatives for one call, each a pair of a resume state and an entry
state, and each alternative gets its own context. Suppose a caller passes an
argument that is either negative or positive, and its state keeps the two
cases apart, for instance, as two path-sensitive states. With one alternative
per case, the callee is analyzed in one context for negative arguments and in
another for positive ones, and a sign analysis keeps the sign in both, whereas a
single entry state would join the cases to $ltop$. When the cases overlap, one
concrete call belongs to several contexts at once
(#isathm("ov_two_contexts_admitted")).

The set may also be empty, for instance, at a call that the analysis
considers unreachable. An entry-state policy admits no context there, because
the analysis's state at the call site describes no caller store
(@sec:eq-routing). Stores that the analysis result excludes need no context. At a call that the program actually makes, however, an empty set
would lose the callee, which the coverage contract rules out (@sec:contract).

A policy speaks about a single call. The contexts of a whole trace follow by
applying it along the calls that created the trace. The root activation
carries the initial context #isai("c\<^sub>0"). A callee carries every
context $c'$ that the policy admits for its call from some context $c$ of its
caller (#isaconst("admits_call_context"), which passes the policy the caller's
store and the entered store that #isaconst("call_enter") computes from it). A
local step keeps the contexts of the trace
(#isathm("activation_context_rel_extend")), and a resumed caller carries
the contexts it had before the call
(#isathm("activation_context_rel_Resume_iff")). An activation may therefore
carry several contexts or none. The
#link(site("index.html#settings"))[explainer page]
draws, for each policy, the contexts that the analyzer creates for one program.

#block(breakable: false)[
  #definition(name: [Context of a trace], isa: "activation_context_rel", cmd: "inductive")[
    The contexts that a trace may carry.
  ]

  #{
    show raw.where(block: true): set text(size: 6pt)
    thy("activation_context_rel")
  }
]

Voblint offers three policies (#isatype("context_mode")): the unit context policy
with one context for every activation, call strings bounded to the $k$
most recent call sites, and entry-state contexts
@sharir81 @seidl12compiler[§§2.6, 2.9]. Entry-state contexts follow Goblint's
partial tabulation, which tabulates procedure summaries only for the calling
contexts the analysis meets @saan26phd[§3.3] @schwarz25phd[§5, p. 110]. Unlike
bounded call strings, they can form an infinite set, so the analysis may not
terminate (@sec:certificate). The traces themselves store no context, since
the concrete semantics should not change with the analysis. The policy is
instead a parameter of the theorems, which therefore hold for every policy. It
may even be defined from the analysis result, as the entry-state policy is
(@sec:eq-routing). This is not circular, because the final guarantee concerns
the stores collected per node, which no policy changes. The policy only
decides how these stores are split among contexts.

The node collecting semantics can now be split by context. A store belongs to
context $c$ at node $v$ if some valid trace ending at $v$ with that store
carries $c$.

#block(breakable: false)[
  #definition(
    name: [Activation collecting semantics],
    isa: "activation_collect",
    cmd: "definition",
  )[
    #thy("activation_collect")
  ]
]

The set #isai("\<A>\<^bsub>\<G>,adm,c₀,g,S\<^esub> v c") is called the _activation collecting semantics_ at $v$ and $c$.
It contains the final stores of the valid traces that end at $v$ and carry
$c$, and the abstract state computed for $[v, c]$ must describe it. In the running example under interval entry-state contexts, `bump(5)` gets the
context $[[5, 5]]$ and `bump(4)` the context $[[4, 4]]$
(@sec:eq-routing). The final store of `bump(5)`, with result $6$, lies in
the activation collecting semantics of context $[[5, 5]]$ at `bump`'s result node, and the final store of `bump(4)`, with result $5$, in that of context
$[[4, 4]]$. The node collecting semantics there contains both stores.

Splitting by context makes the result more precise. A single abstract state
for the result node must describe both stores, so an interval analysis can at best bound the result by $absval(ivl(5, 6))$. A state per context only has to describe the stores of
its own context, $6$ in $[[5, 5]]$ and $5$ in $[[4, 4]]$. No store is lost as long as every valid trace carries a context. An analysis
therefore needs one set of stores per node and context that contains the
activation collecting semantics, and the next section reduces this requirement
to local checks.

== The coverage contract and its soundness #thy-badge("Voblint_CFG", "Activation_Trace_Abstract") <sec:contract>

An analysis result is sound if, at every node $v$ and in every context $c$,
it accounts for the stores of the activation collecting semantics
#isai("\<A>\<^bsub>\<G>,adm,c₀,g,S\<^esub> v c"). This is stated over a _cover_, a function #isai("cover") that assigns a set of
stores to each node and context. Since valid
traces grow by only four rules, it suffices to check the cover against each
rule once. The _coverage contract_ does this with one local obligation per rule,
each mentioning only stores. For a call edge from $u$ into procedure $p$ with
continuation $k$, it requires
#block(inset: (left: 1.5em, y: 0.3em))[
  #grid(
    columns: (auto, 1fr),
    column-gutter: 1em,
    row-gutter: 0.75em,
    oblig("INIT"), $s in S ==> s in "cover"(#isaconst("cfg_entry") g, c_0)$,
    oblig("INTRA"),
    $(u, a, v) in #isaconst("intra") g, thin s in "cover"(u, c), thin s' in #isaconst("edge_step") a thin s ==> s' in "cover"(v, c)$,

    oblig("CALL"),
    [$s in "cover"(u, c), thin c' "admitted from" s$ \
      #h(1.5em)$==> #isaconst("call_enter") (s) in "cover"(ctor("FunctionEntry") p, c')$],

    oblig("RETURN"),
    [$s in "cover"(u, c), thin c' "admitted at" u "from" s "for" (p', e), thin t in "cover"(ctor("FunctionResult") p, c')$ \
      #h(1.5em)$==> #isaconst("combine_collect") (s, t) in "cover"(k, c)$],
  )
]
In #oblig("CALL"), "$c'$ admitted from $s$" means that the policy admits $c'$
for this call edge from $s$ in context $c$. #oblig("RETURN") must hold for
every admitted $c'$, since one call may admit several contexts and the
returning activation may carry any of them. Because $c'$ ranges only over
admitted contexts, the return of `bump(5)` combines only callee results of
contexts entered from this call. In "$c'$ admitted at $u$ from $s$ for
$(p', e)$", the admitting call edge may be any edge leaving $u$, into $p'$ with
entered store $e$ (#isaconst("admits_call_context")). A compiled graph has one call edge per
call site (#isaconst("calls_source_unique"),
#isathm("compile_prog_calls_source_unique")), so on such a graph the admitting
edge is always the call edge of the return. In the running
example under entry-state contexts, #oblig("CALL") requires the cover at the
entry of `bump` in context $[[5, 5]]$ to contain the entered store with
$n = 5$, and #oblig("RETURN") requires the cover at the continuation in `main`
to contain the store in which `a` holds $6$. @fig:contract shows the
obligations at one call, together with a fifth, #oblig("TOTAL").

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
    pairs, and each solid arrow is labeled with the obligation it represents.
    The dotted arrow is no obligation. It marks the caller store $s$ that
    #oblig("RETURN") reads.],
) <fig:contract>

#oblig("CALL") and #oblig("RETURN") constrain only the contexts that the policy
admits. If a call from a store in the cover gets no context at all, both
hold vacuously, and no obligation requires the cover at the call's
continuation to contain the store the call returns with. The resumed caller, however, still carries its contexts there
(#isathm("resume_keeps_context")), so the cover can miss a store that the
program reaches (#isathm("total_dropped_unsound")). #oblig("TOTAL") therefore requires the
policy to admit at least one callee context for every call from a store
$s in #isai("cover u c")$ (#isaconst("call_context_total_on")). It asks only
about stores in the cover, because entry-state policies admit no context for
the stores that the analysis excludes (@sec:contexts). Call strings and the
unit context policy meet #oblig("TOTAL") for every cover (#isathm("call_context_total_on_of_fun")). For
entry-state contexts, it follows from the coverage of the analysis's entry
(@sec:eq-routing).

Isabelle states the five obligations as the assumptions of the locale
#isalocale("activation_coverage").

#{
  show raw.where(block: true): set text(size: 6pt)
  thy("activation_coverage")
}

The contract implies the goal by induction over the four rules of valid
traces, one obligation per rule.

#block(breakable: false)[
  #theorem(name: [Context-indexed soundness], isa: "activation_collect_sound")[
    If the cover meets the five obligations of
    #isalocale("activation_coverage"), then for every node $v$ and context $c$, the activation collecting semantics
    at $v$ and $c$ is contained in #isai("cover v c").
  ]

  #proved("activation_collect_sound")
]

The theorem bounds each context separately. Since #oblig("TOTAL") gives every
valid trace a context, the sets of all contexts together contain the whole
node collecting semantics:

#block(breakable: false)[
  #corollary(name: [The cover contains the collection], isa: "node_collect_covered")[
    Under the five coverage obligations, every store of the node collecting
    semantics at $v$ lies in #isai("cover v c") for some context $c$.
  ]

  #proved("node_collect_covered")
]

This completes the concrete half of the soundness argument. Every store that a
finite source execution reaches appears in a graph execution (@ch:program-model),
as the final store of a valid trace (@sec:source-bridge), in the activation
collecting semantics of the trace's contexts (@sec:contexts), and hence in
every cover that meets the coverage contract. An analysis therefore never
reasons about whole runs, only about sets of stores that each kind of step
preserves. The following chapters build such analyses from abstract domains
(@ch:domains), transfer functions (@ch:analysis-interface), and a solved
equation system (@ch:equations, @ch:solving).
