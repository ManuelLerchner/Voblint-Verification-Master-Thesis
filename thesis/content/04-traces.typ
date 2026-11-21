#import "@preview/fletcher:0.5.8" as fletcher: diagram, edge, node
#import "../lib/math.typ": *
#import "../lib/theme.typ": vb
#import "../lib/figures.typ": *
#import "../lib/code.typ": *
#import "../lib/theorems.typ": corollary, definition, example, lemma, theorem
#import "../lib/cfg-graphs.typ": sum-graph

= Traces and the Coverage Contract <ch:traces>

@ch:program-model matched every source execution with a graph execution.
For an analysis that computes one abstract state per node, this suffices. A
context-sensitive analysis, however, keeps a separate abstract state for each
pair of a node and a calling context. Its soundness argument must say which
executions each pair describes. The graph execution of @sec:cstep cannot
answer this, because it records only a node, a store, and a frame stack, and
no calling context.

Activation traces close this gap. They remember the caller of every
activation, and each trace carries a calling context. One local
condition per kind of execution step then suffices for a context-sensitive
analysis to over-approximate the stores at each node and context.

== Calling contexts and the collecting semantics <sec:why-traces>

A context-sensitive analysis replaces the unknown $[v]$ of a node by unknowns
$[v, c]$, one per calling context $c$ (@sec:interproc). Seidl et al. state that
the invariant for $[u, c]$ "only need[s] to take into account executions
reaching $u$ that satisfy the restriction imposed by context $c$"
@seidl26[§4]. The abstract state for $[v, c]$ therefore has to describe only a
subset of the stores that the state for $[v]$ describes, and it can be
correspondingly more precise.

Consider the recursive program of @fig:cfgmap. Its call `sum(2)` calls
`dec(2)`, then `sum(1)`, which calls `dec(1)` and `sum(0)`. The three
activations of `sum` return $3$, $1$, and $0$, respectively. All visit the
same result node. A set of stores collected at that node retains these results
but forgets which invocation produced which result. An analysis that separates
invocations by their entry values needs that association to justify a different
result in each context.

Contexts depend on how an activation was created, such as its call site or its
arguments. After a return, the caller must continue in the contexts it had
before the call. Neither the graph execution nor a flat record of its
runs exposes this. Each frame of the stack of @sec:cstep holds only what
execution needs to resume the caller, and the frame disappears once the call
has returned. A flat list of visited node-store pairs also interleaves the
steps of all activations. @fig:flat-nested displays one execution both as a flat list and
grouped by activation. For example, after `sum(2)` reaches `pp5`, execution
enters `dec(2)`, follows its body, and resumes `sum(2)` at `pp6`. The nested
view puts the steps of `dec(2)` in a separate box and marks its call in the
path of `sum(2)`. The same grouping applies to the recursive call at `pp6`. The nested boxes form
the _activation tree_ of the run, in which each activation is a child of the
activation that called it @aho06[§7.2.1].

The _activation path_ lists only the node-store pairs of one activation.
Its callees have paths of their own. To justify returns, we also retain the
caller as it was at the call and the completed callee. This records which
caller resumes even after its runtime stack frame has been removed.

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
    align(left, text(size: 7.5pt, weight: "bold", fill: vb.muted)[(a) compiled graph])
    align(center, block(width: 52%, layout(size => {
      let g = sum-graph
      scale(size.width / measure(g).width * 100%, reflow: true, g)
    })))
    v(0.6em)
    set par(first-line-indent: 0pt, justify: false, leading: 0.9em)
    set align(left)
    block(spacing: 0pt, {
      set par(leading: 0.45em)
      text(
        size: 7.5pt,
        weight: "bold",
        fill: vb.muted,
      )[(b) one run on (a), as a flat list of visited nodes]
      h(3pt)
      _flat(_run).map(((a, x)) => _chip(a, x)).join(h(2.5pt))
    })
    v(0.5em)
    text(size: 7.5pt, weight: "bold", fill: vb.muted)[(c) the same run, grouped by activation]
    v(0.2em)
    _nested(_run)
  },
  kind: image,
  placement: auto,
  caption: [(a) The compiled graph of the program in @fig:cfgmap. (b) One
    run on this graph. Each box names a node of (a), in the order the run
    visits it. After `pp5`, for example, the run follows the dashed call edge
    of (a) to the entry of `dec`, runs its body, and resumes at `pp6`. (c) The same steps in the same
    order, grouped by the activation that executes them. Colors mark each
    step's activation, which the flat list (b) itself does not record. A dashed
    tag #sym.arrow.r.hook marks a call of the named callee. This is an
    illustrative execution; stores are omitted.],
) <fig:flat-nested>

== Activation traces of graph executions <sec:traces>

=== Activation traces and their observers #thy-badge("Voblint_CFG", "Activation_Trace_Def") <sec:activation-trace>

Let $V$ be the set of graph nodes and $Sigma$ the set of stores. An activation
path $pi$ is a finite list of elements of $V times Sigma$, including the empty
list (#isatype("activation_path")). The operator $dot.op$ concatenates lists, so
$pi dot.op [(v,s)]$ appends one pair.

#definition(name: [Activation trace], isa: "activation_trace", cmd: "datatype")[
  Traces are the finite terms generated by
  $
    t ::= ctor("Root")(pi)
    | ctor("Call", thy: "Activation_Trace_Def")(t, pi)
    | ctor("Resume")(t, t', pi).
  $
  A root records the initial activation. A call records a new activation and
  its creating caller $t$. A resumption records the suspended caller $t$,
  its completed callee $t'$, and the caller's continued path $pi$.
]

For each constructor, $#isaconst("path_of") (t)$ is its last argument.
When this path is nonempty, $#isaconst("sink_node") (t)$ and
$#isaconst("sink_store") (t)$ are the node and store in its last pair. The
option-valued function #isaconst("caller_of") returns $"None"$ when there is no
creating caller, and $"Some"(t')$ when $t'$ is the creating caller:
$
  #isaconst("caller_of") (ctor("Root")(pi)) & = "None", \
  #isaconst("caller_of") (ctor("Call", thy: "Activation_Trace_Def")(t, pi)) & = "Some"(t), \
  #isaconst("caller_of") (ctor("Resume")(t,t',pi)) & = #isaconst("caller_of") (t).
$
Thus resuming `sum(2)` after `dec(2)` keeps `main` as its creating caller.
It does not make the suspended `sum(2)` trace its own caller.
We write $#isaconst("extend", thy: "Activation_Trace_Def") (t,(v,s))$ for
appending $(v,s)$ to its path while keeping its constructor and retained traces
unchanged.

A single activation may have several successive traces. Its call to a callee
freezes its current trace; its resumption retains that frozen trace and the
finished callee. Consequently, the nested activation boxes in @fig:flat-nested
summarize an execution, while the trace terms additionally record its successive
suspensions and resumptions. Calls and returns start new traces instead of
extending the current one, so a whole run is a family of traces linked by their
caller and callee fields.

This design follows the local traces of Schwarz et al. @schwarz21[§3], which
describe the view of one thread on a concurrent execution. They are defined
inductively as well, with a rule that starts a created thread from the state of
its creator and one rule per edge. Activation traces take over this scheme with
an activation in place of a thread.

=== Valid graph traces #thy-badge("Voblint_CFG", "Activation_Trace_Def") <sec:valid>

The grammar also admits terms that no execution produces. A path may contain
a step that follows no edge of the graph, such as a jump from the entry of
`sum` directly to its result node. A #ctor("Resume") may pair a caller with a
callee that another activation created, for example continue `main` after its
call `sum(2)` with the finished inner activation `sum(1)`, whose caller is
`sum(2)`. Validity rules out such terms by defining how traces arise, with one
rule for starting the program, one for a local edge, one for a call, and one
for a return. Fix a graph $g$, a global-variable classifier $cal(G)$, and
initial stores $S subset.eq Sigma$ for the remainder of the chapter, and write
$v_0$ for the graph entry (#isaconst("cfg_entry")).

The local edges $(u,a,v) in "intra"(g)$ carry an action $a$, and for a store
$s$, $sem(a)(s)$ is the set of possible successor stores
(#isaconst("edge_step")). A call edge $e=(u,a,#ctor("FunctionEntry") thin p,k) in "calls"(g)$ has the
call site $u$, call information $a$ with the return destination, formal
parameters, and actual arguments, the callee's entry node $#ctor("FunctionEntry") thin p$, and the
continuation $k$. For such an edge, $#isaconst("call_enter") _e (s)$ is the entered store, in which
the parameters are bound, and $#isaconst("combine_collect") _e (s,r)$ combines the caller's saved locals
with the callee's globals and return value. The subscript $e$ stands for the
call information of $e$, and $cal(G)$ is fixed.

The rules mirror the graph execution of @sec:cstep. A local step extends the
current trace along a local edge, as #isaconst("cstep") moves to the next
node. A call starts a new trace at the callee's entry, as #isaconst("cstep")
pushes a frame. A return resumes the caller after its callee reaches the result
node, as #isaconst("cstep") pops one. Validity, however, keeps no frame stack.
The #ctor("Call", thy: "Activation_Trace_Def") term already retains its
creating caller, so the return rule finds that caller through
#isaconst("caller_of") and takes the continuation from the call edge.

#definition(
  name: [Valid traces],
  isa: "valid_activation_trace",
  cmd: "inductive_set",
  breakable: false,
)[
  The valid traces $cal(T)=cal(T)_(cal(G),g,S)$ are defined
  inductively by the following rules. All variables range over the objects introduced
  above, and $t,t'$ range over traces.

  #block(breakable: false, width: 100%)[
    *Root.* Each initial store starts a root trace:
    $ frac(s in S, ctor("Root")([(v_0,s)]) in cal(T)). $
  ]

  #block(breakable: false, width: 100%)[
    *Local step.* Follow a local edge and append its successor:
    $
      frac(
        t in cal(T) quad (#isaconst("sink_node") (t),a,v) in "intra"(g) quad s' in sem(a)(#isaconst("sink_store") (t)),
        #isaconst("extend", thy: "Activation_Trace_Def") (t,(v,s')) in cal(T)
      ).
    $
  ]

  #block(breakable: false, width: 100%)[
    *Call.* Retain the caller and start the callee at its entry:
    $
      frac(
        t in cal(T) quad e=(#isaconst("sink_node") (t),a,#ctor("FunctionEntry") thin p,k) in "calls"(g),
        ctor("Call", thy: "Activation_Trace_Def")(t,[(#ctor("FunctionEntry") thin p,#isaconst("call_enter") _e (#isaconst("sink_store") (t)))]) in cal(T)
      ).
    $
  ]

  #block(breakable: false, width: 100%)[
    *Return.* Resume the callee's creating caller at a matching continuation:
    $
      frac(
        display(
          mat(
            delim: #none,
            t' in cal(T) quad #isaconst("caller_of") (t')="Some"(t) quad #isaconst("sink_node") (t')=#ctor("FunctionResult") thin p;
            e=(#isaconst("sink_node") (t),a,#ctor("FunctionEntry") thin p,k) in "calls"(g),
          )
        ),
        ctor("Resume")(t,t',#isaconst("path_of") (t) dot.op [(k,#isaconst("combine_collect") _e (#isaconst("sink_store") (t),#isaconst("sink_store") (t')))]) in cal(T)
      ).
    $
  ]
]

Every valid path is nonempty, so the node and store observers select an
actual final node-store pair on valid traces. Returning from `dec(2)` thus resumes its creating activation
`sum(2)`; an unrelated activation cannot be substituted merely because it
visits the same call site. The continuation and the combined store come from a
call edge from the caller's node into the callee's entry, on compiled graphs
the unique one.

=== The node collecting semantics #thy-badge("Voblint_CFG", "Activation_Trace_Collect") <sec:collect>

The trace retains the calling history. To ask which stores can occur at a
node, we project that history away.

#definition(name: [Node collecting semantics], isa: "node_collect", cmd: "definition")[
  The node collecting semantics is
  $ cal(C)(v) = {#isaconst("sink_store") (t) | t in cal(T) and #isaconst("sink_node") (t)=v}. $
]

For example, at the result node of `sum`, the execution in @fig:flat-nested
contributes stores with return values $0$, $1$, and $3$. The node collecting
semantics plays the role of the collecting semantics of @ch:background for
programs with procedures, with valid traces in place of runs. A procedure's
result node is an ordinary collected node, and the stores in which a run of the
whole program completes are those collected at #ctor("FunctionResult")
`main`.

Every store that a source execution reaches lies in this set, at the node the
simulation of @sec:csim relates the execution to.

#theorem(
  name: [Reached source stores lie in $cal(C)(v)$],
  isa: "source_reaches_node_collect",
)[
  Let $g$ be the graph compiled from a well-formed program with procedure
  table $Pi$ (#isaconst("wf_compile_input")), and let $s_0 in S$. If
  $(#isaconst("main_body") thin Pi, s_0, []) ->_p^* (r,s,F)$, then there are a
  node $v$ and a frame stack $K$ such that
  $ (r,s,F) approx (v,s,K) quad "and" quad s in cal(C)(v). $
]

The proof follows the source execution through the simulation of @sec:csim
and builds a valid trace alongside the graph execution. A local graph step
extends the current trace, a call starts a #ctor("Call", thy: "Activation_Trace_Def")
trace, and a return builds a #ctor("Resume") trace. Throughout, the trace's
chain of creating callers matches the frame stack, so a return resumes the same
caller in the trace as on the stack. Soundness needs only this direction, since
every reached source store must lie in the set that the analysis bounds.

The node collecting semantics forgets the traces, so a soundness statement over
it alone is context-insensitive. The valid traces themselves keep their
structure, so the same set of traces supports two views, collected per node
and split by context.

== Calling contexts of traces #thy-badge("Voblint_CFG", "Activation_Trace_Context") <sec:contexts>

A context groups activations whose behavior the analysis describes together.
For the `sum` execution, a context recording the argument at entry can separate
`sum(2)`, `sum(1)`, and `sum(0)`. A context recording only the most recent
call site instead groups `sum(1)` and `sum(0)`, since both are called at
`pp6`. This is a call string (@sec:interproc) bounded to one call site.

One call may have several contexts, for instance when an analysis splits an
entry state into cases. A policy therefore assigns each call a set of contexts.
The policy is a semantic assignment, separate from how the solver chooses
contexts.

#definition(name: [Context policy], isa: "context_policy", cmd: "type_synonym")[
  Let $C$ be the set of contexts and $I$ the set of call-information records.
  A context policy is a function
  $ "adm": V times C times I times Sigma times Sigma -> cal(P)(C). $
  Its arguments are the call site $u$, caller context $c$, call information $i$,
  caller store $s$, and entered store $s_e$. Its result is the set of callee
  contexts admitted for those arguments.
]

For a call edge $e$ at call site $u$, write $"adm"_e (c,s)$ for the contexts
the policy admits when the call along $e$ is made from store $s$ in context $c$.
A call trace retains its caller and entered store but not the call edge, so
$"admits"(u,c,p,s,s_e,c')$ states that some call edge from $u$ into $p$ enters
$s_e$ from $s$ and admits $c'$ (#isaconst("admits_call_context")).

#definition(name: [Contexts carried by a trace], isa: "activation_context_rel", cmd: "inductive")[
  Fix an initial context $c_0 in C$. The predicate $"carries"(t,c)$
  states that trace $t$ carries context $c$. It is defined inductively by the
  following rules.

  #block(breakable: false, width: 100%)[
    *Root.* The root activation carries the initial context:
    $ "carries"(ctor("Root")(pi),c_0). $
  ]
  #block(breakable: false, width: 100%)[
    *Call.* A callee carries every context admitted for its call from a context
    of its caller, at the entered store that starts its path:
    $
      frac(
        "carries"(t,c) quad "admits"(#isaconst("sink_node") (t),c,p,#isaconst("sink_store") (t),s_e,c'),
        "carries"(ctor("Call", thy: "Activation_Trace_Def")(t,[(#ctor("FunctionEntry") thin p,s_e)] dot.op pi),c')
      ).
    $
  ]
  #block(breakable: false, width: 100%)[
    *Resume.* A resumed caller carries the contexts it had before the call:
    $ frac("carries"(t,c), "carries"(ctor("Resume")(t,t',pi),c)). $
  ]
]

Since the call rule reads only the first pair of the callee's path, a local
step leaves the contexts of a trace unchanged
(#isathm("activation_context_rel_extend")).

For a concrete illustration, choose the policy that assigns each callee its
formal argument's integer value, and take $c_0=0$. The three `sum`
activations then carry contexts $2$, $1$, and $0$. When `sum(1)` returns to
`sum(2)`, the resumed caller carries $2$ again. Voblint offers three policies
(#isatype("context_mode")): the unit policy with one context for every
activation, call strings bounded to the $k$ most recent call sites, and
entry-state contexts @sharir81 @seidl12compiler[§§2.6, 2.9]. The traces store
no context, so the theorems take the policy as a parameter and hold for every
policy. A policy may even be defined from the analysis result, as the
entry-state policy is, since a policy only splits the collected stores among
contexts and never changes them.

A policy may admit several contexts or none, and neither the trace datatype
nor validity prevents the empty case.

#definition(name: [Activation collecting semantics], isa: "activation_collect", cmd: "definition")[
  The collecting semantics at a node $v$ and context $c$ is
  $
    cal(A)(v,c) = {#isaconst("sink_store") (t) | t in cal(T) and #isaconst("sink_node") (t)=v and "carries"(t,c)}.
  $
  Here $cal(A)$ has the fixed parameters $cal(G),"adm",c_0,g,S$.
]

The only difference from $cal(C)(v)$ is the condition $"carries"(t,c)$. Consequently,
$cal(A)(v,c) subset.eq cal(C)(v)$ for every context. If every valid trace
carries a context, then $cal(C)(v)=union.big_(c in C) cal(A)(v,c)$.
These sets may overlap: the same trace may carry several contexts, and
different traces may have the same final store.

#figure(
  table(
    columns: (auto, auto, auto, auto),
    align: (left, center, center, center),
    inset: 5pt,
    [*Activation*],
    [*Context*],
    [*Return value*],
    [*Membership at* $v=#ctor("FunctionResult") thin #raw("sum")$],

    [`sum(2)`], [$2$], [$3$], [$s_2 in cal(A)(v,2) subset.eq cal(C)(v)$],
    [`sum(1)`], [$1$], [$1$], [$s_1 in cal(A)(v,1) subset.eq cal(C)(v)$],
    [`sum(0)`], [$0$], [$0$], [$s_0 in cal(A)(v,0) subset.eq cal(C)(v)$],
  ),
  caption: [The execution of @fig:flat-nested under the illustrative concrete-argument
    policy. Here $s_i$ is the final store of `sum(i)`, not its initial store.
    The return-value column shows one component of each store. These are
    concrete execution values, not analyzer output.],
) <fig:trace-context-stores>

An analysis supplies a candidate set of stores for each $(v,c)$. In the example,
its candidate at $(#ctor("FunctionResult") thin #raw("sum"),2)$ must contain $s_2$, whose return value
is $3$. The following contract establishes such containment for every valid
trace, including recursive calls of arbitrary depth.

== The coverage contract and its soundness #thy-badge("Voblint_CFG", "Activation_Trace_Abstract") <sec:contract>

A _cover_ is a function $"cover": V times C -> cal(P)(Sigma)$ assigning a
candidate set of stores to each node and context. We want a cover to contain
the activation collecting semantics,
$ cal(A)(v,c) subset.eq "cover"(v,c) quad "for every node" v "and context" c, $
and every valid trace to carry at least one context, so that no reached store
escapes the cover. The cover may include stores that no execution reaches.

Checking the inclusion directly would mean following every trace. Valid traces,
however, grow by only four rules (@sec:valid). It therefore suffices to check
that each rule keeps the final store of the trace it builds inside the cover,
in every context that trace carries. The _coverage contract_ does this with one
local obligation per rule, each mentioning only stores and contexts. #oblig("INIT")
covers the root rule, #oblig("INTRA") the local step, #oblig("CALL") the call,
and #oblig("RETURN") the return. A fifth obligation, #oblig("TOTAL"), requires
every covered call to admit a context.

The obligations use the objects fixed in @sec:valid: the initial stores
$S$, the graph entry $v_0$, the edge sets $"intra"(g)$ and $"calls"(g)$, and the
entered and returned stores $#isaconst("call_enter") _e$ and
$#isaconst("combine_collect") _e$, together with the
initial context $c_0$, the policy $"adm"$, and the relation $"admits"$ of
@sec:contexts. They must hold for all the variables shown below. In the call
obligations, fix any edge
$e=(u,a,#ctor("FunctionEntry") thin p,k) in "calls"(g)$. The stores $s,r,s'$ range over $Sigma$, and $c,c'$
range over $C$.

#block(breakable: false, width: 100%)[
  #oblig("INIT") covers initial stores:
  $ s in S ==> s in "cover"(v_0,c_0). $
]
#block(breakable: false, width: 100%)[
  #oblig("INTRA") preserves coverage along each local edge:
  $
    (u,a,v) in "intra"(g) and s in "cover"(u,c) and s' in sem(a)(s)
    ==> s' in "cover"(v,c).
  $
]
#block(breakable: false, width: 100%)[
  #oblig("CALL") covers entry in every context admitted by this edge:
  $
    s in "cover"(u,c) and c' in "adm"_e (c,s)
    ==> #isaconst("call_enter") _e (s) in "cover"(#ctor("FunctionEntry") thin p,c').
  $
]
#block(breakable: false, width: 100%)[
  #oblig("RETURN") covers the combination of caller and callee stores:
  $
    s in "cover"(u,c) and "admits"(u,c,p',s,s_e,c')
    and r in "cover"(#ctor("FunctionResult") thin p,c') \
    ==> #isaconst("combine_collect") _e (s,r) in "cover"(k,c).
  $
]
#block(breakable: false, width: 100%)[
  #oblig("TOTAL") requires at least one admitted context for every covered call:
  $ s in "cover"(u,c) ==> "adm"_e (c,s) != emptyset. $
]

#oblig("TOTAL") is necessary because #oblig("CALL") and #oblig("RETURN") quantify only over admitted
contexts. If the policy assigns the call `sum(2)` no context, those
obligations impose no bound on its result. Yet `main` resumes in its original
context after the call, where its store still has to be covered. #oblig("TOTAL")
excludes this gap. It applies to every store in the cover at a call site,
including stores added by over-approximation; an empty cover imposes no
requirement at that site. Without #oblig("TOTAL"), the soundness theorem below
fails. A checked counterexample meets the other four obligations
(#isathm("tot_weak_obligations")), yet its cover misses a reached store
(#isathm("total_dropped_unsound")).

#let _key(pos, name, body, col: vb.neutral) = node(
  pos,
  text(size: 7pt, body),
  stroke: 0.8pt + col,
  fill: col.lighten(90%),
  corner-radius: 3pt,
  inset: 4pt,
  name: name,
)
#let _ob(o) = text(size: 7pt, oblig(upper(o)))
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
    edge(<c-u>, <c-pe>, "-|>", label: [#_ob("Call") \ #_ob("Total")], stroke: vb.called),
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
    #oblig("TOTAL") guarantees that the call arrow exists, since at least one
    callee context $c'$ is admitted. The dotted arrow is no obligation. It marks
    the caller store $s$ that #oblig("RETURN") reads.],
) <fig:contract>

In the illustrative execution, #oblig("CALL") covers the entered store of `sum(2)`
in context $2$. #oblig("RETURN") combines its final store, with result $3$, with the
saved store of `main`, so the cover at `pp10` in context $c_0$ contains the
store with `x = 3`.

#theorem(name: [Soundness of the coverage contract], isa: "activation_collect_sound")[
  If the cover and policy satisfy #oblig("INIT"), #oblig("INTRA"), #oblig("CALL"), #oblig("RETURN"), and #oblig("TOTAL"), then
  for every node $v$ and context $c$,
  $ cal(A)(v,c) subset.eq "cover"(v,c). $
]

The proof proceeds by induction over valid traces, maintaining a stronger
invariant: each trace in the
creating-caller chain carries at least one context, and its final store is
covered in every context it carries. The caller chain is needed in the return
case to recover the suspended caller's coverage. For each context of that
caller, #oblig("TOTAL") supplies a context admitted for the callee's entry. The callee
is covered in that context, and #oblig("RETURN") then covers the resumed store in the
caller's original context.

In Isabelle, a _locale_ packages fixed parameters and assumptions so that its
results can be reused for each instance. The locale
#isalocale("activation_coverage") assumes exactly these five obligations, so
every cover that meets them inherits the inclusion above and context existence
for every valid trace.

#corollary(name: [Covers contain every collected store], isa: "node_collect_covered")[
  Under the same five obligations,
  $ cal(C)(v) subset.eq union.big_(c in C) "cover"(v,c). $
]

The corollary follows from the theorem, since by #oblig("TOTAL") every valid
trace carries a context and therefore
$cal(C)(v) = union.big_(c in C) cal(A)(v,c)$
(#isathm("node_collect_eq_Union_activation_collect")).

This chapter supplies the next links of the soundness chain of
@fig:intro-nest. @ch:program-model placed every source execution in the graph.
Here, the stores of those executions are collected at each node and context,
and the question whether an analysis accounts for all of them becomes a set of
checks at single edges and calls. From now on, no argument follows a whole
execution or its call stack. An analysis result is sound for every context
policy once it meets the coverage contract.

The following chapters construct such a result. They build it from abstract
domains (@ch:domains) and transfer functions (@ch:analysis-interface), and
obtain it as the solution of an equation system (@ch:equations, @ch:solving).
