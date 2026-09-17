#import "@preview/fletcher:0.5.8" as fletcher: diagram, edge, node
#import "@preview/curryst:0.6.0": prooftree, rule
#import "../lib/math.typ": *
#import "../lib/theme.typ": vb
#import "../lib/figures.typ": *
#import "../lib/code.typ": *
#import "../lib/theorems.typ": corollary, definition, example, lemma, theorem

= Activation-Local Traces and the Soundness Contract <ch:traces>

@ch:program-model turned a VIMP program into a control-flow graph and showed that every
source execution is matched by an execution of that graph. This chapter answers
the question the rest of the thesis depends on:

#align(center, block(width: 92%)[
  _What concrete object must an analysis over-approximate, what does it mean for
  an execution to belong to a calling context, and which local conditions are
  enough to guarantee that an analysis over-approximates it everywhere?_
])

The answer is a single contract with five obligations. It mentions no abstract
domain, no equation system and no solver: those appear only in @ch:domains to @ch:solving,
and their entire job will be to construct something that satisfies it.

== Why reachable states are not enough <sec:why-traces>

The obvious concrete semantics of a control-flow graph is the set of pairs
$(v, s)$ such that some execution reaches node $v$ with store $s$. For an
intraprocedural analysis that is exactly right, and it is what @ch:background's
collecting semantics describes.

It stops being enough as soon as an analysis is _context-sensitive_. Such an
analysis does not keep one abstract state per program point; it keeps one per
program point _and calling context_, so that a procedure called from two places
can be described twice, separately, instead of once at the join of both. Its
claim has the shape

$ "at node" v", in context" c", every store a run can have is in" gamma(#sh($d$) _(v,c)). $

For that sentence to be either true or false, "every store a run can have _in
context $c$_" has to mean something. A set of reachable $(v, s)$ pairs cannot
say it: the pairs record where a run got to and what it held, and nothing about
how it got there. The information the claim quantifies over has already been
discarded before the claim is made.

There are two ways out. One is to leave the concrete semantics alone and treat
the context as an uninterpreted index, proving only that the union over all
contexts is sound. That is sound, and it is weak: it can never justify reading
_one_ context's entry rather than the join of all of them, which is the entire
point of context sensitivity. The other is to make the concrete semantics carry
enough structure to define the context, and then prove the per-context
statement. This chapter takes the second route.

#block(
  fill: vb.bg,
  stroke: 0.7pt + vb.frame,
  radius: 4pt,
  inset: 9pt,
  width: 100%,
)[
  *The design rule.* A property is provable only if it is expressible as a
  function of the concrete semantics. An abstraction can lose information the
  concrete semantics has; it cannot recover information the concrete semantics
  never carried. So the concrete semantics must make at least the distinctions
  that the strongest claim the analysis makes depends on.
]

What structure is enough? Not the whole execution history: recording the entire
sequence of states of a whole-program run would define the context, but it would
also make every later proof reason about objects no analysis inspects. What the
claim needs is exactly the _call history of the activation currently running_.
That suggests keeping runs of one procedure activation at a time, with a link to
the activation that created it, which is what the next section defines.

#block(inset: (left: 1em))[
  #text(0.95em)[The construction adapts the thread-modular _local trace_
    semantics of Schwarz et al. @schwarz23, where a local trace is one thread's
    view of a concurrent execution and synchronisation relates traces. Here a
    local trace is one procedure activation's view of a sequential execution and a
    return composes a finished callee into its suspended caller. The method —
    define the analysis as an observation of a concrete local-trace semantics — is
    theirs; the specialisation to activations, and its mechanization, are this
    thesis's.]
]

=== Three views of one run <sec:three-views>

Before the definition, it is worth naming what already exists. This development
says what a program does three times, at three levels, and the proofs connect
them.

#figure(
  table(
    columns: (auto, 1fr, auto),
    align: (left, left, left),
    stroke: none,
    table.hline(),
    [*view*], [*what a step is*], [*defined in*],
    table.hline(stroke: 0.5pt),
    [source, #isaconst("pstep")],
    [rewrites the remaining command, the store and a stack of caller frames],
    [@ch:program-model],
    [graph, #isaconst("cstep")],
    [moves along one CFG edge, keeping a stack of return points],
    [@ch:background],
    [trace, #isaconst("valid_ltr")],
    [extends one activation's path, nesting its caller and finished callees],
    [this chapter],
    table.hline(),
  ),
  caption: [Three definitions of what a program does. The source view is what a
    programmer means; the graph view is what the analysis is generated from; the
    trace view is what soundness is stated against. @fig:cstep-ltr relates the
    last two and @sec:source-bridge relates all three.],
) <tab:three-views>

They are not redundant. The source view is the one a reader believes, because it
is the language's own semantics. The graph view is the one the analysis is built
from, because equations are generated per CFG node. The trace view is the one
soundness is stated against, because it is the only one of the three that
records which activation a store belongs to. #isathm("csim_step") relates the
first two and #isathm("source_run_has_ltr") relates the second to the third.

== Traces <sec:traces>

=== Activation-local traces <sec:ltr>

An _activation-local trace_ is one activation of one procedure, together with
the activation that called it and the calls it has already finished.

#definition(name: [Activation-local trace], isa: "ltr")[
  A trace $tau$ is one of
  #set enum(numbering: "(i)")
  + $#Root($pi$)$ — the initial activation of the program, with local path $pi$;
  + $#CallT($tau'$, $pi$)$ — a callee created by $tau'$, whose local path $pi$ begins
    at the callee's entry store;
  + $#ResumeT($tau'$, $tau''$, $pi$)$ — the activation $tau'$ continued past the call
    that produced the finished callee $tau''$, with local path $pi$.

  In each case the _local path_ $pi$ is a non-empty list of pairs
  $(v, s)$ of a CFG node and a store. Write $#tracepath (tau)$ for it,
  $#sinknode (tau)$ for the node of its last entry and $#sinkstore (tau)$ for that
  entry's store.
]

Three points about this definition carry the chapter.

*One trace is one activation, not one run.* The local path never leaves the
procedure the activation is executing. When that procedure calls another, the
callee is a _separate_ trace that holds this one as a field; when the callee
finishes, the caller continues in a third trace that holds both. A whole-program
execution is therefore not a single object here. It is a family of traces linked
by those fields, and the one that is "currently running" is the one whose path is
being extended.

*The caller is stored, not searched for.* Because a $ctor("Call")$ carries the
exact caller value — frozen at the moment of the call, with its path ending at
the call node — a completed callee can be composed back into precisely the
activation that spawned it. Nothing has to scan a stack for a compatible frame.

#definition(name: [Creating caller], isa: "caller_of")[
  $
                      #callerof (#Root($pi$)) & = bot \
              #callerof (#CallT($tau$, $pi$)) & = tau \
    #callerof (#ResumeT($tau$, $tau'$, $pi$)) & = #callerof (tau)
  $
]

The third clause is what makes recursion work. A resumed activation is still the
same activation, so its creating caller is whatever created the activation it
resumed — descending through however many calls it has already made and returned
from.

*The context is a projection, not a field.* Nothing in the definition above mentions a
calling context. A context will be _read off_ a trace in @sec:contexts, which is
what allows several different context policies to be applied to the same
semantics without redefining it.

#let _tnode(pos, label, sub, kind) = node(
  pos,
  align(center)[#text(0.92em, weight: "bold")[#label] #v(-0.45em) #text(
      0.72em,
      fill: vb.muted,
    )[#sub]],
  stroke: 0.9pt + (if kind == "run" { vb.accent } else { vb.muted }),
  fill: if kind == "run" { vb.accent.lighten(92%) } else { white },
  corner-radius: 3pt,
  inset: 6pt,
)

#figure(
  diagram(
    spacing: (17mm, 11mm),
    _tnode((0, 0), [Resume], [running: `main` after `f(2)`], "run"),
    _tnode((-1, 1), [Call], [activation of `f`, #raw("n=2")], "sub"),
    _tnode((1, 1), [Resume], [finished callee: `f(2)`], "sub"),
    _tnode((-1, 2), [Root], [`main`], "sub"),
    _tnode((1, 2), [Call], [activation of `f`, #raw("n=1")], "sub"),
    _tnode((2, 3), [Root], [`main`], "sub"),

    edge(
      (0, 0),
      (-1, 1),
      "->",
      label: text(0.75em)[current],
      label-side: left,
      stroke: 0.8pt + vb.accent,
    ),
    edge((0, 0), (1, 1), "->", label: text(0.75em)[callee], stroke: 0.8pt + vb.muted),
    edge(
      (-1, 1),
      (-1, 2),
      "->",
      label: text(0.75em)[#callerof],
      label-side: left,
      stroke: 0.8pt + vb.accent,
    ),
    edge((1, 1), (1, 2), "->", label: text(0.75em)[caller], stroke: 0.8pt + vb.muted),
    edge((1, 2), (2, 3), "->", stroke: 0.8pt + vb.muted),
  ),
  kind: image,
  caption: [One activation-local trace for the recursive factorial
    program below, after the inner call to #raw("f(1)") has returned. The
    running activation is the outermost $ctor("Resume")$; the blue chain is
    #callerof, which descends through the $ctor("Resume")$ to the $ctor("Call")$
    that created the activation and on to $ctor("Root")$, while the finished
    callee hangs off to the right. A path through the CFG would be a single
    line. This is a tree, and the difference is exactly what lets the semantics
    tell the two activations of #raw("f") apart — both of which end at the same
    node $ctor("Result") f$.],
) <fig:ltr-tree>

=== Valid traces <sec:valid>

Not every term of the shape above describes an execution. Validity is the
inductive set of traces that the graph can actually produce, with one rule per
phenomenon the graph has.

#definition(name: [Valid traces], isa: "valid_ltr")[
  For a global classifier $italic("gs")$, a graph $cfg$ and a set $S$ of initial stores,
  $#validltr$ is the least set closed under the four rules of
  @fig:valid-rules.
]

#figure(
  grid(
    columns: 1,
    row-gutter: 1.4em,
    prooftree(rule(
      name: [Init],
      $ctor("Root") thick [(v_0, s)] in cal(V)$,
      $s in S$,
      $v_0 = italic("entry")(cal(G))$,
    )),
    prooftree(rule(
      name: [Intra],
      $tau med dot.c med (v, s') in cal(V)$,
      $tau in cal(V)$,
      $italic("node")(tau) attach(arrow.r.long, t: a) v$,
      $s' in italic("step")(a, italic("state")(tau))$,
    )),
    prooftree(rule(
      name: [Call],
      $ctor("Call") thick tau thick [(ctor("Entry") thin p, e)] in cal(V)$,
      $tau in cal(V)$,
      $italic("node")(tau) attach(arrow.r.dashed, t: a) ctor("Entry") thin p$,
      $e = italic("enter")(a, italic("state")(tau))$,
    )),
    prooftree(rule(
      name: [Return],
      $ctor("Resume") thick tau thick tau' thick (italic("path")(tau) med dot.c med (k, s'')) in cal(V)$,
      $tau' in cal(V)$,
      $italic("caller")(tau') = tau$,
      $italic("node")(tau') = ctor("Result") thin p$,
      $italic("node")(tau) attach(arrow.r.dashed, t: a) ctor("Entry") thin p med [k]$,
      $s'' = italic("combine")(a, italic("state")(tau), italic("state")(tau'))$,
    )),
  ),
  kind: image,
  caption: [The four rules of #isaconst("valid_ltr"), writing $cal(V)$ for
    #isaconst("valid_ltr") itself and $[k]$ for the continuation the call edge
    carries. Each rule reads exactly the relation for its own phenomenon:
    #isaconst("intra") for local flow (solid), #isaconst("calls") for entering a
    callee and for recovering a continuation (dashed). An induction over this
    set has exactly four cases, which is the shape every proof in this chapter
    takes.],
) <fig:valid-rules>

Each rule corresponds to one rule of the graph's own execution relation
#isaconst("cstep"), and @fig:cstep-ltr sets the two side by side. Three details
are worth extracting, because later proofs turn on them.

#figure(
  table(
    columns: (auto, 1fr, 1fr),
    align: (left, left, left),
    stroke: none,
    inset: (x: 6pt, y: 5pt),
    table.hline(),
    [*phenomenon*],
    [*graph step* (#isaconst("cstep"))],
    [*trace rule* (#isaconst("valid_ltr"))],
    table.hline(stroke: 0.5pt),

    [start],
    [begin at #FunEntry($italic("main")$) with an empty frame stack],
    [Init: $Root([(v_0, s)])$],

    [local flow],
    [follow an #isaconst("intra") edge and apply its transfer],
    [Intra: append $(v, s')$ to the running path],

    [call],
    [follow a #isaconst("calls") edge, enter the callee, *push* a frame],
    [Call: a *new* trace, holding the caller],

    [return],
    [at $ctor("Result") p$, *pop* the top frame and combine],
    [Resume: a *third* trace, holding caller and callee],

    table.hline(stroke: 0.5pt),
    [what carries \ the context],
    [the frame stack — flat, and destroyed on pop],
    [the #callerof chain — structural, and retained],
    table.hline(),
  ),
  caption: [The graph's execution and the trace semantics, phenomenon by
    phenomenon. The rules match one for one, which is what makes
    #isathm("source_run_has_ltr") a step-by-step correspondence rather than a
    reconstruction. The last row is the whole reason for the second column: a
    frame stack answers "where do I return to", and once popped the information
    is gone; the caller chain answers "which activation am I", and is still
    there after the call returns. That is what @sec:contexts reads a context off.],
) <fig:cstep-ltr>

*Calls cannot be taken as ordinary steps.* The Intra rule reads
#isaconst("intra") and the Call rule reads #isaconst("calls"), and these are
disjoint relations with incompatible types (@ch:background). A call therefore
cannot be mistaken for a local edge by a side condition failing to hold; it
cannot be expressed as one at all.

*A return follows no edge.* The Return rule does not look for an edge out of
$ctor("Result") p$. It recovers the continuation $k$ from the very
#isaconst("calls") tuple that created the activation. One $ctor("Result") p$ node
therefore serves every caller of $p$, and recursion needs no duplicated nodes.

*The caller is recovered structurally.* The premise $#callerof (tau') = tau$ is
what forbids composing a finished callee into an activation that did not call
it. It is not a side condition to be discharged; it is a projection of the
callee's own structure.

#example(name: [Factorial], isa: none)[
  The program

  #listing(lang: "c", ```
  fun f(n) {
    if (n < 2) { return 1; } else { r = f(n - 1); return n * r; }
  }
  fun main() { a = f(2); __voblint_check(a == 2); }
  ```)

  produces the trace drawn in @fig:ltr-tree. Both activations of #raw("f")
  reach the same node $ctor("Result") f$, with different stores, under different
  caller chains. No set of reachable $(v, s)$ pairs distinguishes them; the two
  traces do.
]

=== The collecting semantics <sec:collect>

With validity fixed, the set an analysis must over-approximate is immediate.

#definition(name: [Collecting semantics], isa: "ltr_collect")[
  $ #ltrcollect (v) = #setcomp($#sinkstore (tau)$, $tau in #validltr ", " #sinknode (tau) = v$) $
]

That is: take every valid trace that ends at $v$ and keep its final store. A
store is in $#ltrcollect (v)$ exactly when some activation can be at $v$
holding it. Membership is introduced and eliminated by
#isathm("ltr_collect_I") and #isathm("ltr_collect_E"), which are the only two
facts the rest of the development uses about it.

Two consequences of the definition are easy to miss.

There is *no global exit node*. Whole-program completion is collection at
$ctor("Result") italic("main")$, and a procedure's result is an ordinary collected
node rather than a separate summary mechanism. Whatever the analysis says about
$ctor("Result") p$ it says in the same way it speaks about any other node.

And $#ltrcollect$ *forgets the structure it was built from*. It is a
function from nodes to store sets, exactly like the intraprocedural collecting
semantics of @ch:background. Everything gained in @sec:ltr is still available —
in $#validltr$ — but a claim stated over $#ltrcollect$ alone is
context-insensitive. Recovering the context is the next section's business.

== Calling contexts, as a relation <sec:contexts>

A _context_ is the key under which an activation is analyzed: activations with
the same key share one abstract state, activations with different keys stay
apart. To state a per-context claim, the semantics must say which contexts are
admissible for a given concrete call.

The natural guess is a function — the call site and the caller's context
determine the callee's. That is what a $k$-call-string policy does. But it is
too narrow for the interface this thesis models. An analysis supplies an entry
operation that may answer with _several_ alternatives for one call, each routed
to its own context (@ch:analysis-interface), so one concrete call can legitimately
be admitted at more than one context. A function cannot express that; a relation
can.

#definition(name: [Call-context relation], isa: "call_context_rel")[
  A call-context relation $#ctxrel$ takes a call node, the caller's context, the
  call's static information, the caller's store, the entered store, and a
  candidate callee context, and says whether that candidate is admissible.

  A functional policy $f$ embeds as the relation admitting exactly $f$'s value
  (#isaconst("call_context_rel_of_fun")).
]

#definition(name: [Admissible context of a call], isa: "admits_call_context")[
  $#admits (u, c, p, s, e, c')$ holds when some
  #isaconst("calls") edge of $cfg$ leaves $u$, enters $p$, produces exactly the
  entry store $e = #callenter (a, s)$, and $#ctxrel$ admits $c'$ for it.
]

Naming the edge by its _effect_ rather than assuming it unique is deliberate: a
graph may have two call edges out of one node, and the semantics stays honest
about that, exactly as the Return rule of @fig:valid-rules does.

A trace's context is then read off its structure.

#definition(name: [Context of a trace], isa: "trace_context")[
  $#tracectx (tau, c)$ — "$tau$ may carry $c$" — is
  inductively defined by
  #set enum(numbering: "(i)")
  + a $ctor("Root")$ carries the initial context $#startctx$;
  + a $#CallT($tau'$, $pi$)$ carries any $c'$ that $#admits$ allows for the transition
    out of a context $tau'$ carries;
  + a $#ResumeT($tau'$, $tau''$, $pi$)$ carries whatever $tau'$ carries.
]

Clause (iii) is the one that makes contexts usable. A completed call does not
repartition its caller: the caller resumes in the context it already had. The
context of an activation is therefore fixed when the activation is created and
unchanged by every call it later makes and returns from — _activation-stable_,
in the terminology of @ch:equations.

#definition(name: [Context-indexed collecting semantics], isa: "activation_collect")[
  $
    #actcollect (v, c) = #setcomp($#sinkstore (tau)$, $tau in #validltr ", " #sinknode (tau) = v ", " #tracectx (tau, c)$)
  $
]

=== Contexts cover, they do not partition <sec:cover>

The relational definition has a consequence that must be stated plainly, because
every later theorem's shape depends on it.

#block(
  fill: vb.bg,
  stroke: 0.7pt + vb.accent,
  radius: 4pt,
  inset: 9pt,
  width: 100%,
)[
  One trace may carry several contexts, and two different activations may carry
  the same one. The sets $#actcollect (v, c)$, as $c$ ranges over contexts,
  therefore *cover* $#ltrcollect (v)$ without *partitioning* it.
]

Under a functional policy such as call strings the buckets are the fibres of a
function and a trace carries exactly one context. Under entry-state routing,
where the context is derived from the abstract entry value and a call may be
answered by several alternatives, a trace can carry several. Both are admitted,
and no theorem may assume the first.

Covering is not automatic. An empty relation admits nothing, so every
$#actcollect (v, c)$ would be empty — vacuously safe and useless. The
condition that rules this out is:

#definition(name: [Conditional totality], isa: "call_context_total_on")[
  $#ctxtotal$ holds when, at every call edge of $cfg$,
  every store that $#cover$ admits at the call site has _some_ admissible callee
  context.
]

It is conditional — a call site the claim itself considers unreachable owes
nothing — which is what lets it be discharged against a computed result rather
than assumed of the policy. The graph of a function satisfies it outright.

== The soundness contract <sec:contract>

Everything so far is concrete: traces, stores, graphs. Now suppose an analysis
has produced a claim — a function $#cover$ from a node and a context to a set of
stores, asserting "at $v$ in context $c$, only these stores occur". What must
$#cover$ satisfy for the assertion to be true?

Five local conditions suffice. They are local in the strong sense: each mentions
one step of the concrete semantics, none mentions a trace, and none mentions how
$#cover$ was computed.

#definition(name: [Coverage contract], isa: "ltr_coverage")[
  #set enum(numbering: "1.")
  + #oblig("INIT"). Every initial store is covered at the entry node in the initial
    context.
  + #oblig("INTRA"). If $s$ is covered at $u$ in context $c$ and
    $cfgedge(u, a, v) in cfg$, then every $s' in #edgecollect (a, s)$ is covered at
    $v$ in the *same* context $c$.
  + #oblig("CALL"). If $s$ is covered at a call site $u$ in $c$, and $c'$ is admissible
    for that call, then the entered store is covered at the callee's entry in
    $c'$.
  + #oblig("RETURN"). If $s$ is covered at a call site $u$ in $c_1$, the context $c'$ is
    admissible for that call *from $c_1$*, and $t$ is covered at the callee's
    result in $c'$, then $#combinecollect (a, s, t)$ is covered at the
    continuation in $c_1$.
  + #oblig("TOTAL"). $#ctxtotal$.
]

Four of these are unsurprising; two deserve argument.

*#oblig("INTRA") preserves the context.* An ordinary edge never changes which activation
is running, so it never changes the context. This is why intra-procedural flow
needs no routing machinery at all, and why @ch:equations's generator can discharge
INTRA generically before it knows what the context policy is.

*#oblig("RETURN") is the load-bearing obligation.* Read it again: the callee is read at a
context admissible *for the transition out of the caller's own context $c_1$* —
not at any context that happens to cover that callee's result. Without that
correlation, a claim could satisfy the other four obligations and still be
false: it could compose the result of `f` analyzed under one caller's context
into a different caller, which is precisely the unsoundness context sensitivity
is supposed to prevent. The correlation is not an extra hypothesis to assume;
#isathm("trace_context_caller_entry") makes it a theorem about $#validltr$.

*#oblig("TOTAL") makes the buckets meaningful rather than merely safe.* Without it a
resumed caller may carry a context under which its callee was never assigned
one. The callee's result would then be bounded by no bucket, and the combined
store by nothing — and the claim would still be "sound", because it would be
claiming nothing. With it, every valid trace carries some context, and the
context-insensitive collection is exactly the union of the buckets.

#let _sq(tl, tr, bl, br, lab) = diagram(
  spacing: (30mm, 12mm),
  node((0, 0), text(0.82em, tl)),
  node((1, 0), text(0.82em, tr)),
  node((0, 1), text(0.82em, bl)),
  node((1, 1), text(0.82em, br)),
  edge((0, 0), (1, 0), "->", label: text(0.72em, lab), stroke: 0.8pt + vb.neutral),
  edge((0, 1), (1, 1), "->", label: text(0.7em)[must hold], label-side: right, stroke: (
    paint: vb.proved,
    thickness: 0.8pt,
    dash: "dashed",
  )),
  edge((0, 0), (0, 1), "->", label: text(0.8em)[$in$], label-side: left, stroke: 0.7pt + vb.muted),
  edge((1, 0), (1, 1), "->", label: text(0.8em)[$in$], stroke: 0.7pt + vb.muted),
)

#figure(
  stack(
    dir: ttb,
    spacing: 1.5em,
    [#text(0.8em, weight: "bold")[INTRA] #h(0.6em) #text(
        0.78em,
        fill: vb.muted,
      )[the context is unchanged]
      #v(0.2em)
      #_sq($s$, $s'$, $italic("cov")(u, c)$, $italic("cov")(v, c)$, $italic("step")(a)$)],
    [#text(0.8em, weight: "bold")[CALL] #h(0.6em) #text(
        0.78em,
        fill: vb.muted,
      )[$c'$ admissible for this call from $c$]
      #v(0.2em)
      #_sq(
        $s$,
        $italic("enter")(a, s)$,
        $italic("cov")(u, c)$,
        $italic("cov")(ctor("Entry") thin p, c')$,
        $italic("enter")(a)$,
      )],
    [#text(0.8em, weight: "bold")[RETURN] #h(0.6em) #text(
        0.78em,
        fill: vb.muted,
      )[$c'$ admissible *from $c_1$*; result lands back in $c_1$]
      #v(0.2em)
      #_sq(
        $(s, t)$,
        $italic("combine")(a, s, t)$,
        $italic("cov")(u, c_1) times italic("cov")(ctor("Result") p, c')$,
        $italic("cov")(k, c_1)$,
        $italic("combine")(a)$,
      )],
  ),
  kind: image,
  caption: [Three of the five obligations as commuting squares, writing
    $italic("cov")$ for the claimed cover. The concrete semantics moves along
    the top; membership in the claim is inherited down the sides; the dashed
    arrow is what the obligation demands. INTRA keeps the context $c$ fixed,
    which is why local flow needs no routing at all. CALL moves to a context
    $c'$ the admissibility relation allows. RETURN is the constrained one: $c'$
    must be admissible *for the transition out of $c_1$*, and the combined
    store lands back in the caller's own $c_1$. Reading the callee at some
    other covering context is exactly the unsoundness that context sensitivity
    exists to prevent. INIT is the degenerate square with no top edge — a seed
    store at the entry node, in the initial context — and TOTAL is not a square
    at all: it is the side condition that the CALL square can always be
    entered.],
) <fig:obligations>

=== What the contract buys <sec:consequences>

The point of the contract is that it is _sufficient_. Nothing further is needed:
no property of the analysis, no shape of the claim, no assumption about how it
was computed.

#theorem(name: [Coverage], isa: "valid_ltr_covered_at")[
  Assume the five obligations. Then for every valid trace $tau$ and every
  context $c$ that $tau$ carries,
  $ #sinkstore (tau) in #cover (#sinknode (tau), c). $
]

The proof is an induction over $#validltr$ with one case per rule of
@fig:valid-rules, each discharged by the obligation of the same name; the Return
case additionally uses the caller-correlation theorem mentioned above. Stated
over the collecting semantics rather than over traces, the same fact reads:

#theorem(name: [Context-indexed soundness], isa: "activation_collect_sound")[
  Assume the five obligations. Then for every node $v$ and context $c$,
  $ #actcollect (v, c) subset.eq #cover (v, c). $
]

#theorem(
  name: [The buckets exhaust the collection],
  isa: "ltr_collect_eq_Union_activation_collect",
)[
  Under TOTAL,
  $ #ltrcollect (v) = union.big_c #actcollect (v, c). $
]

The third theorem is what connects the two readings of a program point. A
context-sensitive result bounds each bucket; the buckets exhaust the
context-insensitive collection; so a context-sensitive result bounds the
context-insensitive collection too, without a separate argument. The
context-insensitive case is then not a different theory but the instance at a
one-element context space — which is exactly how @ch:results obtains it.

#block(
  fill: vb.bg,
  stroke: 0.7pt + vb.proved,
  radius: 4pt,
  inset: 9pt,
  width: 100%,
)[
  *The message of this chapter.* None of the three theorems mentions an abstract
  domain, an equation system, or a solver. They hold for any $#cover$ whatsoever
  that satisfies five local conditions. @ch:domains to @ch:solving build machinery whose
  only purpose is to produce such a $#cover$ and to compute it; @ch:results checks
  the obligations off one at a time. Whenever a later design decision looks
  arbitrary, the question to ask is which of INIT, INTRA, CALL, RETURN or TOTAL
  it exists to discharge.
]

== From source executions back to programs <sec:source-bridge>

One gap remains. Everything above is stated about a CFG, and a reader cares
about VIMP programs. @ch:program-model supplied the forward simulation
#isathm("csim_step"); composing it with the trace construction closes the
distance.

#theorem(name: [Source runs are traces], isa: "source_run_has_ltr")[
  For a well-formed compiled program, every finite source execution from an
  initial store has a matching graph configuration and a valid trace ending at
  the same node with the same store.
]

#corollary(name: [Source runs are collected], isa: "source_reaches_ltr_collect")[
  Under the same hypotheses, if a source run reaches the configuration
  $(c, s, kappa)$, then there are a node $v$ and a stack such that #isaconst("csim") relates
  them and $ s in #ltrcollect (v). $
]

The node is *existential*, and it has to be. A source configuration does not
determine a CFG node: in a program with two structurally identical procedure
bodies, the command about to run matches a node in each, and only the reachable
one is the right answer. #isaconst("csim") records the structural match and
$#ltrcollect$ picks the witness that a run actually reaches.

Only the forward direction is proved, and only the forward direction is needed.
Soundness requires every real execution to appear in the graph; it does not
require every graph execution to come from a real one. @sec:asymmetry discusses what
that asymmetry costs.

== Notation and summary <sec:closing>

=== Notation, and what it stands for <sec:notation>

The theorem environments above carry the Isabelle name each result is stated
under, and `thesis-refs` checks that the name exists. That check guarantees the
endpoint; it says nothing about whether the mathematical notation faithfully
denotes it. This table is the human half of the translation.

#figure(
  table(
    columns: (auto, auto, 1fr),
    align: (left, left, left),
    stroke: none,
    inset: (x: 7pt, y: 4pt),
    table.hline(),
    [*thesis*], [*Isabelle*], [*note*],
    table.hline(stroke: 0.5pt),

    $tau$, [a value of #isatype("ltr")], [a trace is a term, not a set],
    $#tracepath (tau)$, [#isaconst("path")], [the activation-local path],
    $#sinknode (tau)$, [#isaconst("sink_node")], [node of the last entry],
    $#sinkstore (tau)$, [#isaconst("sink_store")], [store of the last entry],
    $#callerof (tau)$, [#isaconst("caller_of")], [partial; #sym.bot at a $ctor("Root")$],
    $cal(V)$, [#isaconst("valid_ltr")], [written $#validltr$ in prose],
    $#ltrcollect (v)$, [#isaconst("ltr_collect")], [classifier, graph and seed set suppressed],
    $#actcollect (v, c)$,
    [#isaconst("activation_collect")],
    [likewise, plus the relation and initial context],
    $#ctxrel$,
    [#isatype("call_context_rel")],
    [six arguments in Isabelle; applied as a relation here],
    $#admits (...)$, [#isaconst("admits_call_context")], [names the call edge by its effect],
    $#tracectx (tau, c)$, [#isaconst("trace_context")], [inductive, not a function],
    $#ctxtotal$, [#isaconst("call_context_total_on")], [conditional on the claim itself],
    $#cover (v, c)$,
    [the #isalocale("ltr_coverage") locale's `cover` parameter],
    [an arbitrary claim, not yet an abstract state],
    $#edgecollect (a, s)$,
    [#isaconst("edge_collect")],
    [lifted pointwise from the single-store step],
    $#callenter (a, s)$, [#isaconst("call_enter")], [the callee's opening store],
    $#combinecollect (a, s, t)$,
    [#isaconst("combine_collect")],
    [caller locals, callee globals, result],
    table.hline(),
  ),
  caption: [Thesis notation and the Isabelle declaration it denotes. Where a
    row says an argument is "suppressed", the Isabelle constant takes it
    explicitly and this chapter fixes it once — the global classifier, the
    graph, the set of initial stores, the call-context relation and the initial
    context are constant throughout, and carrying them through every formula
    would obscure the ones that vary.],
) <tab:notation>

=== Summary

The concrete object an analysis must over-approximate is
$#ltrcollect$, the stores that valid activation-local traces hold at each
node, or $#actcollect$ when contexts are wanted. A calling context is a
projection of a trace, admitted by a relation rather than computed by a
function, so that one concrete call may be described under several contexts and
the buckets cover rather than partition. And a claim about either is true as
soon as it satisfies INIT, INTRA, CALL, RETURN and TOTAL.

What is still missing is any way to produce such a claim. The next chapter
introduces abstract domains — what a set of stores is described _by_ — and
@ch:analysis-interface to @ch:solving build the machinery that turns a program into a claim and
computes it.
