#import "@preview/fletcher:0.5.8" as fletcher: diagram, edge, node
#import "@preview/curryst:0.6.0": prooftree, rule
#import "../lib/math.typ": *
#import "../lib/theme.typ": vb
#import "../lib/figures.typ": *
#import "../lib/code.typ": *
#import "../lib/theorems.typ": corollary, definition, example, lemma, theorem

= Programs, Compilation, and Control-Flow Semantics <ch:program-model>

An analyzer does not work on program text. It works on a graph, because that is
what its equations are indexed by: one unknown per program point, one transfer
per edge. Everything this thesis proves is therefore proved about the graph, and
everything a reader cares about is a property of the source program. This
chapter closes that distance. It answers:

#align(center, block(width: 92%)[
  _How is an execution of a VIMP source program represented by the
  procedure-aware control-flow graph on which Voblint performs its analysis?_
])

The answer comes in three parts: a source language with an operational
semantics, a compiler into a graph, and a simulation relating the two. The last
of these — that every source execution is matched in the graph — is the only
fact @ch:traces needs from this chapter, and @sec:asymmetry explains why the
converse is neither proved nor wanted.

== VIMP, and what it leaves out <sec:vimp>

VIMP is a small imperative language, deliberately so. Every construct it has
must be given a semantics, compiled, and have its transfer function proved sound
in every abstract domain; every construct it lacks is a proof obligation that
does not exist.

#figure(
  table(
    columns: (1fr, 1fr),
    align: (left, left),
    stroke: none,
    inset: (x: 7pt, y: 5pt),
    table.hline(),
    [*modelled*], [*deliberately absent*],
    table.hline(stroke: 0.5pt),
    [integer variables, mathematical #Val], [machine integers, overflow, wrapping],
    [a locals/globals split], [pointers, addresses, the heap],
    [procedures with value parameters], [arrays, structs, aggregate values],
    [direct calls and an optional result], [indirect and virtual calls],
    [recursion, to any depth], [threads and concurrency],
    [assignment, sequencing], [floating point],
    [conditionals and `while` loops], [`goto`, `break`, `continue`],
    [nondeterministic input], [dynamic allocation],
    [assertion checks], [exceptions],
    table.hline(),
  ),
  caption: [What VIMP models and what it does not. The right column is not a
    list of future work: each entry would need its own semantics, compiler
    clauses and per-domain transfer proofs, and @ch:evaluation returns to what
    admitting one would actually cost.],
) <tab:vimp-scope>

#figure(
  block(
    fill: vb.bg,
    stroke: (paint: vb.muted, thickness: 0.7pt, dash: "dashed"),
    radius: 4pt,
    inset: 12pt,
    width: 100%,
  )[
    #set align(left)
    #text(0.9em)[*Figure to draw: VIMP inside C.*

      Must show: one enclosing region for C, an inner region for VIMP naming what it does model (integers, globals, procedures, recursion, branching, loops, nondeterministic input, checks), and the excluded features of @tab:vimp-scope as separate regions outside it

      Draw from: @tab:vimp-scope; the explainer's `island` figure is a composition reference only]
  ],
  kind: image,
  caption: [VIMP inside C],
) <fig:scope>

=== Where VIMP differs from C <sec:vimp-vs-c>

The table above is about what VIMP omits. A second question matters more, and is
easier to overlook: where VIMP models a construct that C also has, but models it
*differently*. Every such row is a place where a true statement about a VIMP
program is not a statement about the C program with the same text.

#figure(
  table(
    columns: (auto, 1fr, 1fr),
    align: (left, left, left),
    stroke: none,
    inset: (x: 7pt, y: 4.5pt),
    table.hline(),
    [], [*VIMP*], [*C*],
    table.hline(stroke: 0.5pt),
    [integers], [mathematical, unbounded], [`ikind`-sized; wraps or undefined],
    [`a / 0`], [defined as $0$], [undefined behaviour],
    [`a % 0`], [defined as $a$], [undefined behaviour],
    [`/` rounding], [truncates toward zero], [the same, since C99],
    [`&&`, `||`], [both operands evaluated], [short-circuits],
    [uninitialised local], [an arbitrary integer], [undefined behaviour],
    [global at entry], [zero], [zero],
    [`main`], [may not `return` explicitly], [may],
    table.hline(),
  ),
  caption: [Constructs both languages have, modelled differently. Absences —
    pointers, arrays, threads — are @tab:vimp-scope; these are divergences,
    which are harder to notice because the syntax matches.],
) <tab:vimp-vs-c>

Three rows need their consequence stated rather than left to the reader.

*Division is the sharpest divergence in the table.* VIMP defines what C leaves
undefined, and a definition is not a conservative choice: it makes provable
things that are not true of the C program. A `PROVED` verdict on a VIMP program
that divides by zero is a true statement about VIMP and says nothing whatever
about the C program with the same text. The analyzer mitigates this with a
separate arithmetic diagnostic, carrying its own theorem
(#isathm("run_voblint_arithmetic_safe"), @ch:results) — but that is a second
claim beside the check column, not a property of the verdict.

*Short-circuiting diverges in the report, not in the semantics.* Because VIMP
expressions are total and have no effects, evaluating both operands of `&&`
yields the same value as short-circuiting would; there is no semantic
difference, and none is claimed. The difference appears in the diagnostic, which
traverses both operands: `x != 0 && 10 / x > 1` draws a divisor warning where a
C reader expects the guard to have protected it.

*Arbitrary uninitialised locals are more general than C, and therefore safe.*
C leaves an uninitialised local undefined; VIMP admits any integer. The analyzer
must handle a strictly larger set of initial states than C requires, which can
cost precision and cannot cost soundness.

Two of the *absences* also deserve a sentence, being the ones a reader familiar
with C analyzers reaches for first. VIMP integers are mathematical, so no
soundness theorem in this development covers a wrapping integer. And VIMP has no
pointers, which is why the abstract states of @ch:domains can be one value per
variable with no question of aliasing.

=== Expressions and commands

Expressions are integer-valued, in the C manner: there is no separate Boolean
type, comparisons and logical operators evaluate to $0$ or $1$, and a condition
is true when it is non-zero.

#definition(name: [Expressions], isa: "exp")[
  $
    e ::= n | x | e + e | e - e | e * e | e "/" e | e % e
    | e < e | e <= e | e = e | e != e | not e | e and e | e or e
  $
]

Evaluation, written $#sem($e$) _s$, is _total_ and has no effects. Totality is
bought with two conventions: division by zero yields $0$ and remainder by zero
yields the dividend. These are VIMP conventions, not a model of C's undefined
behaviour, and @ch:results returns to them when the analyzer reports a possible
division by zero as a diagnostic rather than as a check.

Totality matters more than it looks. Because evaluating a guard has no effect
and cannot fail, a transfer function may re-evaluate it freely — which is what
lets the backward filtering of @ch:domains narrow a state against a condition
that has already been tested.

#definition(name: [Commands], isa: "com")[
  $
    c ::= & #skipC | x := e | #keyw("check") (e) | c";" c
            | #keyw("if") (e) {c} #keyw("else") {c} | #keyw("while") (e) {c} \
        | & x := p(e, ..., e) | #keyw("return") e? | #keyw("Restore") | #keyw("Unwind")
  $
]

The last two are not source syntax. #keyw("Restore") marks an activation
boundary inside the sequential structure, and #keyw("Unwind") is the state after
a #keyw("return") has published its value and is discarding the commands that
follow it. A source program contains neither — #isaconst("source_com") excludes
them — and they exist only as intermediate states of the semantics below.

A program is a table of procedure declarations, each a list of formal parameters
and a body, together with a list of declared global variables. The entry
procedure is an ordinary declaration named `main`, not a separate field.

== Executing a source program <sec:execution>

=== Configurations and frames <sec:pstep>

#definition(name: [Source configuration], isa: "pstep")[
  A configuration is a triple $#config($c$, $s$, $#frstack$)$ of the command
  that remains to run, a store $s : #Var -> #Val$, and a stack #frstack of
  suspended activations. Each frame records the caller's store and the variable,
  if any, that is to receive the result.
]

The store is one total function, and the locals/globals split is a _classifier_
$italic("gs") : #Var -> "Bool"$ laid over it rather than a second component.
That choice is carried through the whole development: nothing ever holds two
stores, and "global" is a property of a name.

Execution is the small-step relation #pstep. Most of its rules are the
expected ones — the interesting behaviour is at a call and at a return.

#figure(
  grid(
    columns: 1,
    row-gutter: 1.3em,
    prooftree(rule(
      name: [Assign],
      $(x := e, s, kappa) arrow.r_p (keyw("skip"), s[x |-> #sem($e$) _s], kappa)$,
    )),
    prooftree(rule(
      name: [Call],
      $(x := p(overline(e)), s, kappa) arrow.r_p (italic("body")(p) ";" ctor("Restore"), s_"in", lr(⟨ s, x ⟩) "::" kappa)$,
      $Pi(p) = lr(⟨ overline(y), italic("body")(p) ⟩)$,
      $s_"in" = italic("bind")(overline(y), #sem($overline(e)$) _s, italic("enter")(s))$,
    )),
    prooftree(rule(
      name: [Return],
      $(keyw("return") med e, s, kappa) arrow.r_p (ctor("Unwind"), s[italic("ret") |-> #sem($e$) _s], kappa)$,
    )),
    prooftree(rule(
      name: [Restore],
      $(ctor("Restore"), s, lr(⟨ f, x ⟩) "::" kappa) arrow.r_p (keyw("skip"), italic("combine")(f, s, x), kappa)$,
    )),
  ),
  kind: image,
  caption: [Four of the twelve rules of #isaconst("pstep"), chosen because they
    are the ones the compiler has to reproduce. A call evaluates its actuals in
    the caller's store, resets the locals and binds the formals
    (#isaconst("enter_state"), #isaconst("bind_formals")), pushes a frame, and
    continues with the callee's body followed by #keyw("Restore"). A return
    publishes its value into the reserved variable #isaconst("ret_var") and
    becomes #keyw("Unwind"), which discards the commands between it and the
    nearest #keyw("Restore"). #keyw("Restore") pops the frame and merges:
    caller's locals, callee's globals, result into the destination
    (#isaconst("combine_env"), #isaconst("combine_assign")).],
) <fig:pstep>

#block(
  fill: vb.bg,
  stroke: 0.7pt + vb.trusted,
  radius: 4pt,
  inset: 9pt,
  width: 100%,
)[
  *This is the anchor, and it is anchored to nothing else.*
  #isaconst("pstep") does not approximate some prior notion of what a VIMP
  program does: it *is* that notion. No external reference semantics
  cross-checks it. An earlier version of this development embedded VIMP into
  the AFP's `IMP2` and restated soundness against its big-step semantics; that
  bridge was removed, and @ch:conclusion gives the reasons it has not been
  rebuilt.

  Every theorem in this thesis therefore rests on the reader accepting these
  rules as the language. That is not a gap to be closed by more proof — a proof
  is stated over its definitions and cannot vouch for them — but it is a
  claim the reader is entitled to see stated rather than discover.
  @sec:vimp-vs-c is the part of it that can be made precise: exactly where these
  rules disagree with C. The rest is the ordinary obligation of any
  formalization, and @ch:results returns to it once the theorems are in view.
]

Two design points in @fig:pstep matter later.

*The callee's opening store is built at the call site.* A procedure declares no
locals beyond its formals, so entering one is exactly: keep the globals, reset
everything else, bind the formals to the evaluated actuals. @ch:analysis-interface
will ask each abstract domain for its own version of that operation, and the
concrete one here is what the abstract one must over-approximate.

*Returning is two steps and two operations.* #keyw("return") publishes; the
matching #keyw("Restore") merges. The merge itself splits into an environment
part — caller's locals, callee's globals — and the write of the result into the
destination. That split is not an accident of this presentation; it mirrors the
analyzer interface being modelled, and @ch:analysis-interface keeps both halves
as separate operations a domain supplies.

== The procedure-aware control-flow graph <sec:graph>

=== Why a graph at all <sec:why-graph>

The semantics of @sec:pstep is a perfectly good definition of what a program
does. It is a poor basis for an analysis, for four reasons that together
determine the shape of the rest of this thesis.

/ Analysis is indexed by program points: an abstract state is attached to a
  location in the program, and a source configuration's "location" is the whole
  remaining command — a syntactic object that changes shape at every step. There
  are infinitely many of them for a loop.
/ Transfer functions attach to transitions: an analysis says what an assignment
  does to an abstract state. In #pstep that information is spread across the
  congruence rules that walk down to the redex.
/ Procedures need stable locations: an interprocedural analysis has to name "the
  entry of $p$" and "the result of $p$" to route information into and out of a
  call. Source syntax offers no such names.
/ A call site needs its continuation: to combine a callee's result back, the
  analysis must know where the caller resumes — again not something the source
  form makes available at the call.

A control-flow graph supplies all four: finitely many nodes, one transfer per
edge, distinguished entry and result nodes per procedure, and a call edge that
records its own continuation.

#block(
  fill: vb.bg,
  stroke: 0.7pt + vb.frame,
  radius: 4pt,
  inset: 9pt,
  width: 100%,
)[
  This is the point at which this development parts company with the other
  mechanized abstract interpreters a reader may know. A _syntax-directed_
  analyzer recurses over the command structure and iterates loops in place, so
  it needs no graph and its soundness proof is an induction over the syntax.
  Voblint is _constraint-based_: the program becomes unknowns and equations, and
  a separate solver — which knows nothing about programs — finds a solution. The
  cost is this chapter and the next; the benefit is that the solver is
  replaceable and the interprocedural machinery is not special-cased.
  @ch:related returns to the comparison.
]

=== Nodes, edges, and the two relations <sec:cfg>

#definition(name: [Control-flow graph], isa: "cfg")[
  A graph #cfg consists of
  #set enum(numbering: "(i)")
  + a set #isaconst("intra") of _local edges_ $(u, a, v)$, each labelled by an
    #isatype("edge_action") $a$;
  + a set #isaconst("calls") of _call edges_ $(u, italic("ca"), ctor("Entry") thin q, k)$,
    naming the call site $u$, the call's information $italic("ca")$, the callee's
    entry node, and the node $k$ at which the caller resumes;
  + an entry node, and a set of checks.

  Nodes are $ctor("Stmt") thin n$, $ctor("Entry") thin p$ or $ctor("Result") thin p$.
]

#figure(
  table(
    columns: (auto, 1fr),
    align: (left, left),
    stroke: none,
    inset: (x: 7pt, y: 4pt),
    table.hline(),
    [*edge action*], [*what it does to the store*],
    table.hline(stroke: 0.5pt),
    [#isaconst("EA_Nop")], [nothing; pure control flow],
    [#isaconst("EA_Assign")], [evaluates an expression and writes one variable],
    [#isaconst("EA_Assume")], [lets the store through if the condition is true],
    [#isaconst("EA_AssumeNot")], [lets the store through if the condition is false],
    [#isaconst("EA_Special")], [a recognised library call: nondeterministic input, $min$, $max$],
    [#isaconst("EA_Body")], [the single edge leaving $ctor("Entry") thin p$; the identity],
    [#isaconst("EA_Ret")], [writes the returned value into the reserved variable],
    [#isaconst("EA_Check")], [nothing; marks an assertion for the report],
    table.hline(),
  ),
  caption: [The eight edge actions. Each is a _total store transformer inside one
    activation_ — which is exactly why none of them is a call. #isaconst("EA_Body")
    is the identity and exists only so that an analysis has a transition to
    attach procedure-entry work to. #isaconst("EA_Check") is likewise inert: it
    gives an assertion a first-class place in the graph rather than treating it
    as a library call.],
) <tab:edge-actions>

*Local edges and call edges are different relations, and that is load-bearing.*
An #isatype("edge_action") cannot denote a call: there is no constructor for
one, so a call cannot be misread as a local step by some side condition failing
to hold — it cannot be expressed as a local step at all. @ch:traces relies on
this when its four trace rules each read exactly one of the two relations.

*There is no global exit node.* A procedure's result is the ordinary node
$ctor("Result") thin p$, and a #keyw("return") compiles to an ordinary local
edge into it. One such node serves every caller of $p$, which is what allows
recursion without duplicating nodes.

*A call edge carries its own continuation.* The node $k$ in a call tuple is
where the caller resumes. Nothing has to be recovered by matching a return
against a call later: the information is in the edge that created the
activation. @ch:traces uses exactly this when it composes a finished callee back
into its caller.

#figure(
  block(
    fill: vb.bg,
    stroke: (paint: vb.muted, thickness: 0.7pt, dash: "dashed"),
    radius: 4pt,
    inset: 12pt,
    width: 100%,
  )[
    #set align(left)
    #text(0.9em)[*Figure to draw: A compiled two-procedure graph.*

      Must show: both node kinds that are not statements ($ctor("Entry") thin p$, $ctor("Result") thin p$), solid local edges, a call edge entering $ctor("Entry") thin f$, the dotted continuation it carries, and one $ctor("Result") thin f$ serving both call sites

      Draw from: the recursive factorial program of @ch:traces, through `voblint --graph-snapshot`]
  ],
  kind: image,
  caption: [A compiled two-procedure graph],
) <fig:run-cfg>

== Compilation <sec:compilation>

=== Compiling a command <sec:compile>

The compiler walks a command and emits nodes and edges. It is
_continuation-passing_: the node a fragment falls through to is an _input_, not
a result. So a fragment never invents a node to hold a control flow its own
construct does not have — there is no join node after a conditional, because the
two branches are simply compiled against the same continuation.

#figure(
  block(
    fill: vb.bg,
    stroke: (paint: vb.muted, thickness: 0.7pt, dash: "dashed"),
    radius: 4pt,
    inset: 12pt,
    width: 100%,
  )[
    #set align(left)
    #text(0.9em)[*Figure to draw: Compiling a counted loop, statement by statement.*

      Must show: each source statement beside the node it becomes and the edges leaving it, with the continuation each statement was compiled against made visible

      Draw from: @tab:compile and the running example of @sec:running-example]
  ],
  kind: image,
  caption: [Compiling a counted loop, statement by statement],
) <fig:source-morph>

#figure(
  table(
    columns: (auto, 1fr),
    align: (left, left),
    stroke: none,
    inset: (x: 7pt, y: 5pt),
    table.hline(),
    [*source*], [*emitted, against continuation $k$*],
    table.hline(stroke: 0.5pt),
    [$x := e$], [one node, one #isaconst("EA_Assign") edge to $k$],
    [$c_1 ";" c_2$], [$c_2$ against $k$, then $c_1$ against $c_2$'s entry],
    [#keyw("if")],
    [one node, an #isaconst("EA_Assume") edge to the compiled
      _then_ branch and an #isaconst("EA_AssumeNot") edge to the _else_ branch,
      both compiled against $k$],
    [#keyw("while")],
    [a head node, an #isaconst("EA_Assume") edge into the
      compiled body — itself compiled against the head — and an
      #isaconst("EA_AssumeNot") edge to $k$],
    [$x := p(overline(e))$],
    [no local edge: a #isaconst("calls") tuple naming
      $ctor("Entry") thin p$ and the continuation $k$],
    [#keyw("return") $e$],
    [an #isaconst("EA_Ret") edge to $ctor("Result") thin p$,
      ignoring $k$ entirely],
    table.hline(),
  ),
  caption: [Compilation, by construct. Two entries carry the chapter's point. A
    call emits _only_ a call tuple, so a call never appears as an executable
    local edge. And a #keyw("return") ignores its continuation, which is why an
    early return leaves no unreachable node behind — the statements after it are
    still compiled, but nothing reaches them, and
    #isaconst("prog_live") identifies exactly those.],
) <tab:compile>

Compiling a whole procedure wraps its body: an #isaconst("EA_Body") edge from
$ctor("Entry") thin p$ into the body, the body compiled against an epilogue
node, and an #isaconst("EA_Ret") edge from the epilogue to
$ctor("Result") thin p$ for the fall-through case.

The compiler's output is not assumed to be well-formed; it is proved so.

#theorem(name: [The compiled graph is well formed], isa: "compile_prog_wf")[
  For an accepted program, #isaconst("compile_prog") produces a graph
  satisfying the structural contract #isaconst("wf_cfg"): return edges land at
  the result node of their own procedure, call edges name declared callees, and
  the entry node is the entry of `main`.
]

Two further facts about the output are used later, and are worth naming here
because they are easy to assume rather than prove. The graph is _finite_
(#isathm("compile_prog_finite")), which every solver instantiation needs. And no
two call edges leave the same node (#isathm("compile_prog_calls_source_unique")),
because each compiled fragment claims fresh statement indices — which is what
lets a context-sensitive analysis read a call site's callee off the graph.

=== Which programs are accepted

Not every VIMP program is compiled. #isaconst("wf_source_program") is a static
contract — distinct procedure names, declared callees, matching arities, no use
of the reserved return variable, a return discipline, and an argument-free
`main` that completes only by falling through — and it is a premise of every
theorem in this thesis. #isaconst("wf_compile_input") adds the finite,
duplicate-free procedure enumeration that executable compilation needs, and
#isaconst("wf_program_compile_input_exec") is the executable form of the same
contract, which is the check the command-line tool actually runs.

Some of these rejections are representational rather than semantic: a `main`
with an explicit #keyw("return") is rejected, though nothing about it is
unsound. @ch:conclusion lists them.

=== Graph execution <sec:cstep>

The graph has its own operational semantics, independent of the compiler. This
matters more than it may seem: because #isaconst("cstep") is defined for an
_arbitrary_ graph, every soundness result in @ch:traces and after holds for any
graph, not only for one this compiler produced.

#definition(name: [Graph execution], isa: "cstep")[
  A graph configuration is a triple of a node, a store, and a stack of suspended
  callers, each recording where to resume, which variable receives the result,
  and the caller's store. #isaconst("cstep") has three rules:
  #set enum(numbering: "(i)")
  + follow a local edge and apply its transfer;
  + follow a call edge: enter the callee and push a frame;
  + at $ctor("Result") thin p$: pop the top frame and combine.
]

#figure(
  table(
    columns: (auto, 1fr, 1fr),
    align: (left, left, left),
    stroke: none,
    inset: (x: 6pt, y: 5pt),
    table.hline(),
    [*phenomenon*], [*source* (#isaconst("pstep"))], [*graph* (#isaconst("cstep"))],
    table.hline(stroke: 0.5pt),
    [ordinary step],
    [rewrite the redex; the remaining command shrinks],
    [follow an #isaconst("intra") edge; the node moves],

    [call],
    [push $lr(⟨ s, x ⟩)$; continue with $italic("body")(p) ";" ctor("Restore")$],
    [push $(k, x, s)$; jump to $ctor("Entry") thin p$],

    [return],
    [#keyw("return") publishes, #keyw("Unwind") discards, #keyw("Restore") pops],
    [reach $ctor("Result") thin p$ by an #isaconst("EA_Ret") edge, then pop],

    [where the \ continuation lives],
    [nested in the command, as #keyw("Restore") wrappers],
    [in the frame stack, as the node $k$],
    table.hline(),
  ),
  caption: [The two executions, phenomenon by phenomenon. The last row is the
    whole difficulty of @sec:csim: the source nests a suspended caller's
    remaining work _inside the single command_ being executed, while the graph
    keeps it as a node on a stack. Relating the two means pairing off those two
    representations, one layer per suspended caller.],
) <fig:pstep-cstep>

Note that a return follows no edge out of $ctor("Result") thin p$: the
continuation comes from the frame, which came from the call edge. @ch:traces
reproduces this exactly.

== Relating the two executions <sec:relating>

=== Relating source and graph configurations <sec:csim>

#definition(name: [Simulation relation], isa: "csim")[
  #isaconst("csim") relates a source configuration $#config($c$, $s$, $#frstack$)$
  to a graph configuration $(v, s, italic("stk"))$ _holding the very same store_.
  It has three constructors: $sans("Base")$ relates a single activation with
  nothing beneath it; $sans("Nested")$ peels one suspended caller, pairing a
  #keyw("Restore") wrapper in the command against a frame on the stack; and
  $sans("Returning")$ covers the skew just after a callee finishes, where the
  graph has already reached $ctor("Result") thin p$ while the source is still
  propagating #keyw("Restore") or #keyw("Unwind") towards its frame-pop rule.
]

Both nestings run outermost-first, so the top command layer pairs with the
_last_ frame. After `main` calls `f` calls `g`, the source command is
$((((C ";" ctor("Restore")) ";" B) ";" ctor("Restore")) ";" A)$ — where $A$ is
`main`'s continuation and $C$ the running residual of `g` — while the graph sits
at `g`'s node with continuation frames $[B"'s node", A"'s node"]$.

*The relation is not functional, and must not be.* #isaconst("csim") is a
_structural_ correspondence: it asks that the command about to run correspond to
a node of some procedure compiled into the graph, never that the procedure is
ever called. A program whose `main` body also appears as an uncalled procedure
therefore relates one source configuration to two nodes, one of them in dead
code.

#block(
  fill: vb.bg,
  stroke: 0.7pt + vb.accent,
  radius: 4pt,
  inset: 9pt,
  width: 100%,
)[
  This is why every source-level theorem in this thesis is _existential_ in its
  node. There is no theorem saying "the node is unique", because it is not.
  @ch:traces supplies what actually pins the node down: reachability. Among the
  nodes #isaconst("csim") allows, the collecting semantics selects those a run
  really reaches.
]

=== Forward simulation <sec:simulation>

#theorem(name: [One step is matched], isa: "csim_step")[
  Let the program be well formed and every declared procedure be compiled into
  the graph. If #isaconst("csim") relates a source configuration to a graph
  configuration, and the source takes one #pstep step, then the graph can take
  zero or more #isaconst("cstep") steps to a configuration that #isaconst("csim")
  relates to the new one, with the same store.
]

#corollary(name: [A whole run is matched], isa: "csim_star")[
  The same holds for a finite run: any sequence of source steps is matched by a
  sequence of graph steps, preserving #isaconst("csim") throughout.
]

The proof does not proceed by induction on the command. It proceeds by cases on
what the source redex is — a call, a return being initiated, a return already in
progress, or an ordinary step inside the current activation — with one
completion argument per case. The machinery underneath is a predicate locating a
partly executed command in the graph: running a command part way leaves a
_residual_, the piece still to execute, and the predicate says which node that
residual corresponds to. The bulk of the session is the lemmas showing that when
a located residual is about to run a base command, the edge the compiler emitted
for it really is in the graph, and taking the source step relocates the successor
residual at that edge's target.

One side condition is worth naming because it is deliberately _not_ part of
#isaconst("csim"): that every declared procedure's body has been compiled into
this graph, with its entry and exit wiring present. Keeping it out of the
relation is what lets the returning phase proceed without it.

=== What the simulation does not establish <sec:asymmetry>

Only the forward direction is proved. There is no theorem saying that every
graph execution comes from a source execution, and none is wanted.

The reason is what soundness needs. A sound analysis must over-approximate every
real execution; it is allowed to describe behaviour that no real execution has.
If the graph admits runs the source does not, the analysis computes a larger set
of states than necessary — it loses precision, and stays sound. The converse
would be needed only for a _completeness_ claim, which this thesis does not
make.

#block(
  fill: vb.bg,
  stroke: 0.7pt + vb.trusted,
  radius: 4pt,
  inset: 9pt,
  width: 100%,
)[
  *Claim discipline.* This chapter establishes a forward simulation, not an
  equivalence. Nowhere may the thesis say that the CFG "is" the program's
  semantics, or that graph and source executions correspond one to one. What is
  proved is one-directional and is exactly what @ch:traces consumes.
]

=== The running example <sec:running-example>

The program below is used from here on and returns in later chapters. It
exercises a loop, a procedure call with a result, and a check, and is small
enough to hold in mind. Its compiled graph has the shape of @fig:run-cfg's
`main` half, with `bump` in place of `f` and no recursive edge.

#listing(lang: "c", ```
fun bump(n) {
  return n + 1;
}

fun main() {
  a = bump(5);
  x = 0;
  while (x < 10) { x = x + 1; }
  __voblint_check(0 < x);
}
```)

@ch:traces changes example. Activation-local traces are about telling two
activations of _the same_ procedure apart, and the shortest program that shows
it is a recursive one; `bump` is called once and cannot. The switch is
deliberate and local to that chapter.

== Where this leaves us

The chapter has produced one fact for the rest of the thesis:

#align(center, block(width: 84%)[
  #set text(0.95em)
  source execution (#isaconst("pstep")) \
  #sym.arrow.b #h(0.4em) #text(fill: vb.muted)[forward simulation, #isathm("csim_star")] \
  graph execution (#isaconst("cstep"))
])

The graph is now a legitimate object to reason about: whatever a run of the
source program does, the graph does too. What the graph execution does _not_
yet provide is any way to say which activation a store belongs to — its frame
stack answers "where do I return to", and is destroyed on the way out. That is
the gap @ch:traces opens with.
