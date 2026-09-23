#import "@preview/fletcher:0.5.8" as fletcher: diagram, edge, node
#import "@preview/curryst:0.6.0": prooftree, rule
#import "../lib/math.typ": *
#import "../lib/theme.typ": vb
#import "../lib/figures.typ": *
#import "../lib/code.typ": *
#import "../lib/sources.typ": thy
#import "../lib/theorems.typ": corollary, definition, example, lemma, theorem

= Activation-Local Traces and the Coverage Contract <ch:traces>

A context-sensitive analysis claims, for a node $v$ and a calling context $c$,
a bound on the stores of the executions that reach $v$ "in context $c$". The
standard collecting semantics indexes stores by node only, and no store records
the context it belongs to, so the claim has no concrete meaning to be sound
against (@sec:why-traces). Proving only the join over all contexts sound would
never justify reading one context's value, which is the point of context
sensitivity. This chapter answers RQ2. It defines activation-local traces,
reads a calling context off a trace through a relation that may admit one call
at several contexts, and states five local obligations, the coverage contract,
under which a claim bounds each context's share of the collection. Under the
totality obligation these shares recover the context-free collection. Weakening
the return obligation or dropping totality admits claims that miss stores an
execution reaches, which shows that neither can be omitted. None of
this mentions an abstract domain, equation system or solver; @ch:domains to
@ch:solving build the machinery that discharges the obligations.

== Why reachable states are not enough <sec:why-traces>

The collecting semantics of @ch:background assigns each node $v$ of a
control-flow graph the set of stores that some run holds on reaching $v$
@cousot77, which an unknown $[v]$ per node over-approximates @apinis12. A
context-sensitive analysis splits $[v]$ into unknowns $[v, c]$, one per calling
context $c$, following Sharir and Pnueli's value-table approach @apinis12[§3].
Seidl et al. state that the invariant for $[u, c]$ "only need[s] to take into
account executions reaching $u$ that satisfy the restriction imposed by context
$c$" @seidl26[§4]. The claim has the shape

$ "at node" v", every store of an execution in context" c "is in" #sem($d_(v,c)$). $

The node-indexed sets give its left-hand side no meaning. In the running
example of @fig:program-to-equations, `bump(n)` returns `n + 1` and `main`
calls `bump(5)` and then `bump(4)`. At the result node of `bump`, the collecting
semantics contains a store with $n = 5$ and $r = 6$ and one with $n = 4$ and $r = 5$,
where $r$ is the return-value variable. With one context per entered value of
$n$, an analysis claims $r = 6$ in context $5$, which is true only if the
second store does not belong to context $5$. No store records this. The context is
a property of how the running activation was entered, namely the call site, the
caller's context and the entered store, combined by the analysis's context
policy. A configuration of the graph execution adds a stack of suspended
callers (@sec:cstep), but attaches no context to them either, and a return pops
the frame from which the finished callee was entered.

A concrete counterpart of the per-context claim therefore has two requirements.
It must retain how the activation holding each store was entered, so that a
context policy can compute the context from the call site, the caller's context
and the entered store. And the context must be read at the call that actually
happens. A semantics that indexed a callee's points by its caller's context
would leave the sets at the callee's own contexts empty, and the per-context
statement would hold there for every claim, including an entry state that
gives the callee's locals no value and so describes no entered store.

A record of the whole run meets the first requirement only implicitly. In the
program of @fig:cfgmap, `sum(2)` calls `dec` and then itself, so one run passes
through three activations of `sum` and two of `dec`, all on one copy of each
procedure's nodes. In the list of the run's steps, #raw("entry_sum") occurs
three times. On this list a call is one more step. A context that every step
preserves cannot change at the call. A context that does change there needs a
separate rule for call steps, and a return must then restore the caller's
context, which requires matching the return with its call by counting calls and returns
along the list. A witness that justifies a return by splicing in a separate
run of the callee, started from the entered store, avoids the counting but
detaches the callee from the activation that called it, and with it from the
caller's context that the callee's context is computed from. Grouped by
activation (@fig:flat-nested), each activation's steps form one path, the call
is a separate rule at which the context is chosen from the caller's, and a
returned callee stays attached to the activation that called it.

#let _acts = (vb.neutral, vb.accent, vb.sign, vb.par, vb.cong, vb.trusted)
// Colour alone does not survive greyscale printing: every box names its
// activation, and a hand-over names the callee.
#let _act-names = ("main", "sum(2)", "dec(2)", "sum(1)", "dec(1)", "sum(0)")
#let _chip(a, body) = box(
  inset: (x: 2.5pt, y: 1.5pt),
  radius: 2pt,
  fill: _acts.at(a).lighten(88%),
  stroke: 0.5pt + _acts.at(a),
  text(size: 7.5pt, font: "DejaVu Sans Mono", fill: vb.neutral, bottom-edge: "descender", body),
)
#let _mark(a) = box(
  inset: (x: 2pt, y: 1.5pt),
  radius: 2pt,
  stroke: (paint: _acts.at(a), thickness: 0.8pt, dash: "dashed"),
  text(
    size: 7pt,
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
  inset: 3pt,
  radius: 3pt,
  stroke: 0.6pt + _acts.at(a),
  below: 2pt,
)[
  #text(size: 7.5pt, weight: "bold", fill: _acts.at(a), name) #h(3pt) #path
  #inner.pos().join()
]

#figure(
  {
    set par(first-line-indent: 0pt, justify: false, leading: 0.9em)
    set align(left)
    _act(
      0,
      [main],
      _chips(
        (0, "entry_main"),
        (0, "pp9"),
        1,
        (0, "pp10"),
        (0, "pp11"),
        (
          0,
          "exit_main",
        ),
      ),
      pad(left: 8pt, _act(
        1,
        [sum(2)],
        _chips(
          (1, "entry_sum"),
          (1, "pp2"),
          (1, "pp5"),
          2,
          (1, "pp6"),
          3,
          (1, "pp7"),
          (1, "exit_sum"),
        ),
        pad(left: 8pt, _act(2, [dec(2)], _chips((2, "entry_dec"), (2, "pp0"), (2, "exit_dec")))),
        pad(
          left: 8pt,
          _act(
            3,
            [sum(1)],
            _chips(
              (3, "entry_sum"),
              (3, "pp2"),
              (3, "pp5"),
              4,
              (3, "pp6"),
              5,
              (3, "pp7"),
              (3, "exit_sum"),
            ),
            pad(left: 8pt, _act(4, [dec(1)], _chips(
              (4, "entry_dec"),
              (4, "pp0"),
              (4, "exit_dec"),
            ))),
            pad(
              left: 8pt,
              _act(5, [sum(0)], _chips((5, "entry_sum"), (5, "pp2"), (5, "pp3"), (5, "exit_sum"))),
            ),
          ),
        ),
      )),
    )
  },
  kind: image,
  caption: [One run of the program in @fig:cfgmap, its steps grouped by the
    activation that took them. Read left to right, each box lists one
    activation's steps in execution order. A dashed tag #sym.arrow.r.hook marks
    where the activation handed control to the named callee; the caller resumes
    at the call's continuation. Stores are omitted.],
) <fig:flat-nested>

The construction adapts the _local traces_ of Schwarz et al. @schwarz21, each
one thread's view of a concurrent execution, to procedure activations: here a
local trace is one activation's view of a sequential execution, and a return
composes a finished callee into its suspended caller (@sec:rel-goblint).

== Traces <sec:traces>

=== Activation-local traces <sec:ltr>

The grouping of @fig:flat-nested becomes a datatype with one constructor per
way an activation begins or continues.

#definition(name: [Activation-local trace], isa: "ltr")[
  A trace $tau$ is one of
  #set enum(numbering: "(i)")
  + $#Root($pi$)$: the initial activation of the program, with local path $pi$;
  + $#CallT($tau'$, $pi$)$: a callee created by $tau'$, whose local path $pi$ begins
    at the callee's entry store;
  + $#ResumeT($tau'$, $tau''$, $pi$)$: the activation $tau'$ continued past the call
    that produced the finished callee $tau''$, with local path $pi$.

  In each case the _local path_ $pi$ is a list of pairs $(v, s)$ of a CFG node
  and a store. The observer $#isaconst("path") thin tau$ returns it,
  $#isaconst("sink_node") thin tau$ the node of its last entry and
  $#isaconst("sink_store") thin tau$ that entry's store.
]

One trace is one activation: its local path never leaves the procedure. A
callee is a separate trace that holds its caller as a field, and when the
callee finishes, the caller continues in a third trace holding both. So a whole
run is a family of traces linked by these fields. A $ctor("Call")$ stores
its caller exactly, frozen at the call node, so a finished callee composes back
into the activation that created it, without searching a stack for a
compatible frame. The finished callee kept by a $ctor("Resume")$ is not read by
the context below. Validity forces the frozen caller to be exactly that
callee's creating caller (#isathm("valid_ltr_Resume_fields")). Both the
validity rules and the context below need the activation that created a trace.

#definition(name: [Creating caller], isa: "caller_of")[
  The creating caller is a partial function: a $ctor("Root")$ has none.
  #thy("caller_of")
]

A resumed activation is the same activation, so its creating caller is that of
the activation it resumed; the recursion descends through every call the
activation has already made and returned from. The definition mentions no
calling context: @sec:contexts reads the context off the trace instead of
storing it there. A stored context would make the concrete semantics depend on
the analysis. For entry-state routing it could not even be fixed in advance,
since the admissible contexts are those to which the entry alternatives of the
solved table route (#isaconst("routed_entry_context_rel")), and this relation exists
only after the analysis has run. Reading the context off the trace lets every
policy share one semantics.

=== Valid traces <sec:valid>

The datatype admits terms that no execution produces: a path whose step follows
no edge, or a $ctor("Resume")$ pairing a caller with a callee that another
activation created. Validity rules such terms out.

#definition(name: [Valid traces], isa: "valid_ltr")[
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

Init corresponds to the initial graph configuration and the other three rules
to the three rules of #isaconst("cstep"): intra appends a step along a local
edge, call starts a new trace holding the caller where #isaconst("cstep")
pushes a frame, and ret builds a third trace holding caller and callee where
#isaconst("cstep") pops. The two differ in what carries the context. A frame
stack records where control returns to, and a pop discards this record. The
#isaconst("caller_of") chain records which activation is running, and this
record survives the return.

For compiled programs the correspondence is proved in one direction. A graph
step from a configuration that a valid trace represents leads to a
configuration that a valid trace represents, with the trace's caller chain
matching the frame stack (#isathm("cstep_preserves_ltr_repr"), extended to runs
by #isathm("csteps_preserve_located_ltr")). The converse, that every valid trace
arises from a graph run, is not proved. Soundness needs only the forward
direction: a claim that bounds every valid trace bounds every run.

The ret rule follows no edge out of #isai("FunctionResult p"). It reads the
continuation from a #isaconst("calls") tuple that leaves the caller's call node
and enters $p$, so one result node serves every caller of $p$. On compiled
graphs each call node has a single outgoing #isaconst("calls") tuple
(#isaconst("calls_source_unique"), #isathm("compile_prog_calls_source_unique")),
so this is the tuple through which the callee was entered. Its premise
#isai("caller_of callee = Some caller") forbids composing a finished callee
into an activation that did not call it. The premise is evaluated on the
callee's own structure, so no separate matching invariant is needed.

=== The collecting semantics <sec:collect>

The traces determine which stores some activation can hold at a node, the
counterpart of the node-indexed collecting semantics of @ch:background.

#block(breakable: false)[
  #definition(name: [Collecting semantics], isa: "ltr_collect")[
    #thy("ltr_collect")
  ]
]

A store is in #isai("\<C>\<^bsub>\<G>,g,S\<^esub> v") exactly when some
activation can be at $v$ holding it. The classifier, graph and initial stores
are those of the program at hand, written #isai("\<G>"), #isai("g") and
#isai("S") from here on. In @fig:flat-nested, the three activations of `sum`
reach #raw("exit_sum") with different stores; the collected set keeps the
stores and forgets which activation held each. A procedure's result is an
ordinary collected node, and whole-program completion is collection at
$ctor("FunctionResult") italic("main")$.

#isaconst("ltr_collect") is a function from nodes to store sets, like the
intraprocedural collecting semantics of @ch:background, so a claim stated over
it alone is context-insensitive. The trace structure remains available in
#isaconst("valid_ltr"), and the next section reads the context off it.

== Calling contexts, as a relation <sec:contexts>

A _context_ is the key under which an activation is analyzed: activations with
the same key share one abstract state. The natural guess is a function from the
call site, the caller's context and the entered store to the callee's context,
as for $k$-call-strings. It is too narrow for the interface this thesis models,
where an entry operation may answer one call with _several_ abstract
alternatives, each routed to its own context (@ch:analysis-interface).

As an illustration, suppose the caller knows $x in [0, 9]$ before a call
`h(x)` and the entry operation splits the parameter's range into the
alternatives $[0, 5]$ and $[3, 9]$. The alternatives must cover the caller's
value together but need not be disjoint. Entry-state routing
(#isaconst("routed_entry_context_rel")) sends each to the context named by its
entry value, $c_1$ and $c_2$. A concrete call with $x = 4$ lies in both
alternatives, and both analyses of `h` describe it. A function would force the
concrete semantics to choose an alternative that no execution determines. A
relation admitting both $c_1$ and $c_2$ states what the analysis covers. The
situation is machine-checked: for a Sign specification whose entry operation
returns two overlapping alternatives, #isathm("ov_two_contexts_admitted")
proves one concrete call admitted under two distinct contexts. The shipped
numeric analyses answer each call with a single alternative
(#isathm("dgs_enter_local_state_st_for_lifted")), so for them a call admits at
most one context.

#definition(name: [Call-context relation], isa: "call_context_rel")[
  A call-context relation $R$ takes a call node, the caller's context, the
  call's static information, the caller's store, the entered store, and a
  candidate callee context, and says whether that candidate is admissible. A
  functional policy $f$ embeds as the relation admitting exactly $f$'s value
  (#isaconst("call_context_rel_of_fun")).
  #isaconst("admits_call_context") lifts $R$ to the graph: some
  #isaconst("calls") edge with action $a$ leaves $u$, enters $p$, produces
  the entry store #isai("es = call_enter \<G> a s"), and $R$ admits the
  candidate for it.
]

The relation receives both the caller's store and the entered store so that an
instance can admit a context only for an alternative that covers both, its
continuation half the caller's store and its entry half the entered store.
Checking the two stores against different alternatives is unsound
(@sec:calls).

The relation judges a single call. The context of a whole trace follows from
the calls that created it and its callers.

#definition(name: [Context of a trace], isa: "trace_context")[
  #isai("trace_context \<G> R startcontext g t ctx"), read "$t$ may carry
  #isai("ctx")", is inductively defined by
  #set enum(numbering: "(i)")
  + a $ctor("Root")$ carries the initial context #isai("startcontext")\;
  + a $#CallT($tau'$, $pi$)$ carries any $c'$ that #isaconst("admits_call_context")
    allows for the transition out of a context $tau'$ carries;
  + a $#ResumeT($tau'$, $tau''$, $pi$)$ carries whatever $tau'$ carries.
]

By clause (iii) an activation's context is fixed when the activation is
created: the calls it makes and returns from do not change it. We call this
property _activation-stable_. A context that also changed at returns would
break the return case below, which reads the callee's result at the context the
callee was entered with; a callee that had itself called and returned would no
longer carry that context. Goblint makes the same choice: it selects a context
only when entering a callee, from the callee's entry state
(@app:goblint-alignment). Like #isai("\<G>"),
#isai("g") and #isai("S"), the relation #isai("R") and the initial context
#isai("startcontext") are fixed per program.

#definition(name: [Context-indexed collecting semantics], isa: "activation_collect")[
  #thy("activation_collect")
]

#isaconst("activation_collect") keeps those stores of
#isai("\<C>\<^bsub>\<G>,g,S\<^esub> v") whose trace carries $c$: the concrete
set that the claim for $[v, c]$ must over-approximate, relative to the policy
#isai("R"). @tab:bump-buckets shows the sets for the example of
@sec:why-traces.

#figure(
  table(
    columns: (1.4fr, 1fr),
    [*set at the result node of `bump`*], [*stores, as $(n, r)$*],
    [#isai("\<C>\<^bsub>\<G>,g,S\<^esub> v")], [$(5, 6)$, $(4, 5)$],
    [context of entered $n$, $c = 5$], [$(5, 6)$],
    [context of entered $n$, $c = 4$], [$(4, 5)$],
    [single context $star$ admitted at every call], [$(5, 6)$, $(4, 5)$],
  ),
  caption: [#isaconst("ltr_collect") and #isaconst("activation_collect") at
    the result node $v$ of `bump` in @fig:program-to-equations, under two
    policies. Derived by hand from the semantics, with stores restricted to $n$
    and the return-value variable $r$; not analyzer output (@sec:eq-coarse
    gives the analyzer's verdicts).],
) <tab:bump-buckets>

=== Contexts cover, they do not partition <sec:cover>

#block(
  fill: vb.bg,
  stroke: 0.7pt + vb.accent,
  radius: 4pt,
  inset: 9pt,
  width: 100%,
)[
  One trace may carry several contexts, and two different activations may carry
  the same one. The sets #isai("activation_collect \<G> R startcontext g S v c"),
  as $c$ ranges over contexts, are the _buckets_ of $v$. They therefore *cover*
  #isai("\<C>\<^bsub>\<G>,g,S\<^esub> v") without *partitioning* it.
]

Under a functional policy such as call strings, the buckets are the fibres of a
function. Under entry-state routing with overlapping alternatives, as for the
call of `h` with $x = 4$ above, a trace carries several contexts. The theorems assume
neither.

Covering is not automatic. If a relation admits no context for a call, the
callee's trace carries none and lies in no bucket, while the resumed caller
keeps the caller's context and lies in a bucket at the continuation. The
following condition rules this out.

#definition(name: [Conditional totality], isa: "call_context_total_on")[
  #isai("call_context_total_on cover R \<G> g") holds when, at every call edge of
  $g$, every store that #isai("cover") admits at the call site has _some_
  admissible callee context.
]

The condition is relative to the claim: it asks nothing of a call site that the
claim considers unreachable. It can therefore be discharged against a computed
result instead of being assumed of the policy. For entry-state routing it has
to be discharged this way, since the relation is itself built from the computed result. A
functional policy always satisfies it.

== The coverage contract <sec:contract>

Suppose an analysis has produced a claim #isai("cover") mapping a node and a
context to a set of stores. Five local conditions suffice for the claim to
bound every bucket. The first four read the four rules of
#isaconst("valid_ltr") against the claim, each mentioning one step of the
concrete semantics; the fifth is needed because admissibility is a relation
that may admit nothing. None mentions a trace or how #isai("cover") was
computed, so an analysis discharges them one step at a time.

#definition(name: [Coverage contract], isa: "ltr_coverage")[
  #set enum(numbering: "1.")
  + #oblig("INIT"). Every initial store is covered at the entry node in the initial
    context.
  + #oblig("INTRA"). If $s$ is covered at $u$ in context $c$ and
    #isai("(u, a, v) \<in> intra g"), then every #isai("s' \<in> edge_step a s") is covered at
    $v$ in the *same* context $c$.
  + #oblig("CALL"). If $s$ is covered at a call site $u$ in $c$, and $c'$ is admissible
    for that call, then the entered store is covered at the callee's entry in
    $c'$.
  + #oblig("RETURN"). If $s$ is covered at a call site $u$ in $c_1$, the context $c'$ is
    admissible *from $c_1$* for a call out of $u$ (on compiled graphs, the unique
    one), and $t$ is covered at the callee's
    result in $c'$, then #isai("combine_collect \<G> dst s t") is covered at the
    continuation in $c_1$.
  + #oblig("TOTAL"). #isai("call_context_total_on cover R \<G> g").
]

#example(name: [A cover for `bump`])[
  Take the entry-value policy of @tab:bump-buckets, which admits for a call of
  `bump` exactly the context equal to the entered value of `n`. In every context
  $c$, let the claim at the nodes of `bump` be $s(n) = c$, strengthened to
  $s(n) = c and s(r) = c + 1$ at its result node, where $r$ is the return-value
  variable #isaconst("ret_var"). In the initial context, let `main` be covered
  by all stores up to the first call, by $s(a) = 6$ at the second call, and by
  $s(a) = 6 and s(b) = 5$ from there on; `main` is uncovered in every other
  context. #oblig("INIT") holds because every store is covered at `main`'s
  entry, #oblig("INTRA") because each edge preserves its predicate, and
  #oblig("CALL") because binding the argument in context $c$ establishes
  $s(n) = c$. For #oblig("RETURN") at the first call, the only context
  admissible from the initial context is $5$, so only the result claimed in
  context $5$ is combined, giving $s(a) = 6$; at the second call only context
  $4$ is admissible, giving $s(b) = 5$. #oblig("TOTAL") holds because every
  call admits the context of its entered value. The cover is checked by hand
  and uses no abstract domain or solver.
]

#oblig("INTRA") keeps the context: an ordinary edge never changes which
activation runs. Local flow therefore needs no routing, and @ch:equations
discharges #oblig("INTRA") before fixing a context policy.

#oblig("CALL") names the concrete entered store: the actuals bound to the
formals and the callee's other locals set to $0$ (@sec:pstep). An entry state
that describes only the globals and gives the locals no value fails it.

The admissibility premise of #oblig("RETURN") is what makes the claim
per-context at the caller. In the example it restricts the first call to the
result claimed in context $5$. Without the premise, #oblig("RETURN") would
also combine the result claimed in context $4$ and force $a in {5, 6}$ at the continuation.
That claim is sound, but it is the claim of the single context $star$ that
admits both calls, so indexing the callee by context would gain the caller
nothing.

The simpler #oblig("RETURN") that reads the callee's result in the caller's own context
$c_1$ is unsound. No obligation forces a claim to cover the result of `bump` in
the initial context, since no call is admitted there, so a claim may leave it
empty. The weakened #oblig("RETURN") then produces no store after the first call, and
the claim declares `b = bump(4)` and both checks unreachable. The theories
prove this for a two-call program of the same shape.

#theorem(name: [Weakened #oblig("RETURN")], isa: "return_at_caller_context_unsound")[
  Let `f(n)` return `n`, and let `main` run `a = f(1); b = f(5);` under the
  policy that admits exactly the entered value of `n`. Some claim meets
  #oblig("INIT"), #oblig("INTRA"), #oblig("CALL"), #oblig("TOTAL") and the
  weakened #oblig("RETURN") (#isathm("ret_weak_obligations")), yet the store with
  $a = 1$ reaches the second call site and lies in the claim of no context
  there.
]

The correct #oblig("RETURN") reads the callee at a context admitted from the caller's.
That this is the context the callee trace actually carries needs no extra
hypothesis: #isathm("trace_context_caller_entry") proves the correlation for
every valid trace.

#oblig("TOTAL") is needed by the per-context theorem itself, not only for
exhaustive buckets. Let the relation admit no context for either call of
`bump`. #oblig("CALL") and #oblig("RETURN") then hold for every claim, since both require an
admissible context. The claim that covers every store at `main`'s entry and at
the first call site in the initial context, and nothing elsewhere, meets #oblig("INIT"),
and #oblig("INTRA") because no local edge leaves the call site (@fig:program-to-equations).
Every run nevertheless resumes at the continuation. The resumed trace carries
the initial context by clause (iii) of the context definition, whatever its
callee carries, so its store lies in the continuation's bucket, where the
claim is empty. Of the five obligations only #oblig("TOTAL") rejects this claim.
The theory checks the same argument on the two-call program of the weakened
#oblig("RETURN") theorem above.

#theorem(name: [Dropping TOTAL], isa: "total_dropped_unsound")[
  Let `f(n)` return `n`, and let `main` run `a = f(1); b = f(5);`. Take a
  relation that admits no context, and a claim that covers every store at
  `main`'s entry and at the first call site in the initial context and nothing
  elsewhere. The claim meets #oblig("INIT"), #oblig("INTRA"), #oblig("CALL")
  and #oblig("RETURN") (#isathm("tot_weak_obligations")), yet the store with
  $a = 1$ is collected at the second call site in the initial context and lies
  outside the claim there.
]

An analyzer run shows the same failure.

#theorem(name: [An entry that admits no context], isa: "ov_empty_continuation_bot")[
  Let `p(a)` return `a`, and let `main` run `x = 1; y = p(x);`. Analyze it with
  the shipped Sign specification, changed only so that the entry operation
  answers the call with no alternative and so admits no context for it.
  The solve terminates, its table holds no context at the entry of `p`
  (#isathm("ov_empty_no_callee_context")), and it holds #ctor("Bot") at the
  continuation of the call.
]

Every run reaches that continuation, so the table declares an executed point
unreachable. The facts are proved by evaluation and trust the code generator
(@ch:background). The table is not checked against the contract. Its entry
operation violates paired entry coverage
(#isathm("ov_empty_pairs_never_cover")), the analysis-level form of #oblig("TOTAL")
(@sec:eq-routing).

=== What the contract gives <sec:consequences>

The contract is sufficient: no further property of the analysis, shape of the
claim or assumption about its computation is needed. The proof is a rule
induction over #isaconst("valid_ltr"), strengthened to every trace on the
caller chain (#isathm("caller_chain_closure")), because the ret case needs the
caller's bound and recovers it from the callee's chain. The init and intra
cases use #oblig("INIT") and #oblig("INTRA"), the call case #oblig("TOTAL") and #oblig("CALL"), and the ret case #oblig("TOTAL"),
#oblig("RETURN") and the caller correlation. #isathm("valid_ltr_covered_at") states the
result: every valid trace's final store lies in #isai("cover") at its final
node, for every context the trace carries. Over the collecting semantics this
reads as follows.

#theorem(name: [Context-indexed soundness], isa: "activation_collect_sound")[
  Assume the five obligations. Then for every node $v$ and context $c$,
  #align(center, isai("activation_collect \<G> R startcontext g S v c \<subseteq> cover v c"))
]

For the cover of the example, the theorem yields $a = 6$ and $b = 5$ whenever
an execution reaches the two checks; it does not show that any execution
reaches them. The equation system of @ch:equations computes such covers from
abstract states.

#theorem(
  name: [Exhaustive buckets],
  isa: "ltr_collect_eq_Union_activation_collect",
)[
  Under the five coverage obligations, including #oblig("TOTAL"),
  #align(
    center,
    isai(
      "\<C>\<^bsub>\<G>,g,S\<^esub> v = (\<Union>c. activation_collect \<G> R startcontext g S v c)",
    ),
  )
]

#isathm("Union_activation_collect_le_ltr_collect") places the union inside the
collection for every relation. The converse needs every valid trace to carry
a context, which the whole contract provides (#isathm("valid_ltr_has_context")):
#oblig("TOTAL") gives each covered call a context, and the other four obligations keep
every caller's store covered, so #oblig("TOTAL") applies at every call a valid trace
makes. In the counter-model above, the traces of `bump` carry no context and
the union misses their stores. So the per-context bounds together bound
#isai("\<C>\<^bsub>\<G>,g,S\<^esub> v"), while one context's bound may be
more precise: in @tab:bump-buckets it may state $r = 6$ in context $5$, whereas any
bound on the whole node admits $r = 5$. The context-insensitive analysis is the
instance at a one-element context space (#isalocale("unit_dg_analysis")).
Apinis et al. note the abstract counterpart, that a point is reached only by
values bounded by the join of its computed values over all contexts
@apinis12[§3]. Here we define the concrete set and prove both theorems about
it.

== From source executions back to programs <sec:source-bridge>

Everything above is stated about a graph. Composing the forward simulation of
@ch:program-model with the trace construction reaches VIMP programs.

#theorem(name: [Source runs are traces], isa: "source_run_has_ltr")[
  For a well-formed compiled program, every finite source execution from an
  initial store has a matching graph configuration and a valid trace ending at
  the same node with the same store, whose caller chain represents the graph's
  frame stack.
]

#corollary(name: [Source runs are collected], isa: "source_reaches_ltr_collect")[
  Under the same hypotheses, if a source run reaches the configuration
  $(c, s, italic("frs"))$, then there are a node $v$ and a stack such that #isaconst("csim") relates
  them and #isai("s \<in> \<C>\<^bsub>\<G>,g,S\<^esub> v").
]

The node is existential because #isaconst("csim") is not functional
(@sec:csim): the command about to run may match nodes in several structurally
identical procedure bodies, and the corollary asserts the store only at a node
that some valid trace reaches.

The chapter answers RQ2 and establishes K2. A calling context is a property
of an activation, read off its activation-local trace at the call that created
it and kept across the calls it makes. For every graph, initial-store set,
relation $R$ and initial context, a claim that meets the five obligations of
#isalocale("ltr_coverage") bounds every context bucket
(#isathm("activation_collect_sound")), and the buckets together are exactly the
context-free collection (#isathm("ltr_collect_eq_Union_activation_collect")).
No premise restricts $R$ to a function, so one call may be admitted at several
contexts. The condition that makes the indexing lose no executions is #oblig("TOTAL"),
stated relative to the claim. Composed with @ch:program-model, every store of a
source run is collected (#isathm("source_reaches_ltr_collect")). The witnesses
above serve K4. A machine-checked counterexample shows that #oblig("RETURN") cannot read
the callee at the caller's own context, and another that the other four
obligations do not suffice without #oblig("TOTAL")
(#isathm("total_dropped_unsound")); an evaluated analyzer run shows the second
failure on the executable. The later chapters need nothing else from the
concrete side. They must compute a claim from abstract states and prove the five obligations for it,
with #oblig("INIT") and #oblig("INTRA") from the initial state and the edge transfers
(@ch:domains, @ch:analysis-interface) and #oblig("CALL"), #oblig("RETURN") and #oblig("TOTAL") from the call
protocol and the context policy (@ch:equations).
