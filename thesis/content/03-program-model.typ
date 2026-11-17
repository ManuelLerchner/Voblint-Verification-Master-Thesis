#import "@preview/fletcher:0.5.8" as fletcher: diagram, edge, node
#import "@preview/curryst:0.6.0": prooftree, rule
#import "@preview/cetz:0.5.2"
#import "../lib/math.typ": *
#import "../lib/theme.typ": vb
#import "../lib/figures.typ": *
#import "../lib/code.typ": *
#import "../lib/sources.typ": proved, stated, thy
#import "../lib/theorems.typ": corollary, definition, example, lemma, theorem
#import "../lib/cfg-graphs.typ": dot-edge-line, dot-label, dot-node-line, sum-graph

= VIMP and Its Control-Flow Graphs <ch:program-model>

Voblint's soundness theorem speaks about executions of a VIMP program, while
its analysis computes on a control-flow graph. This chapter connects the two.
Its result is the first inclusion of the chain of @fig:intro-nest. Every
source execution of a well-formed program is matched by a graph execution that
holds the same store.

@ch:background analyzed a single loop through its control-flow graph. VIMP
programs also have procedures and recursion, and their meaning is given by a
source semantics that executes the program text directly. To
generate its equations, however, an analysis needs a fixed,
finite set of program points, because its constraint system attaches one
abstract state to each of them. The source semantics, a small-step semantics
in the style of Nipkow and Klein @nipkow14[§7.3] (@sec:pstep), provides no such
set. It locates an execution only by the command that still has to run, and under
recursion these commands nest arbitrarily deep. Voblint therefore compiles a
program to a procedure-aware control-flow graph, whose nodes serve as the
program points, and generates its equations from the graph
(@fig:program-to-equations). The compilation step must then be part of the
proof. If soundness held only for the graph, the compiler would stay outside
the theorem, and a verdict would say nothing about the source program. The running example is the program of
@fig:program-to-equations, in which `main` calls `bump(5)` and `bump(4)`.

// Node names and edge labels come from registered `--dot` output
// (lib/cfg-graphs.typ).
#let _dot-label = dot-label
#let _dot-edge-line = dot-edge-line
#let _dot-node-line = dot-node-line
#let _snap = read("/shared/generated/cfg-contexts-dot.txt").split("\n")
#let _snap-label(src, dst) = _dot-label(_dot-edge-line(_snap, "cfg-contexts-dot", src, dst))
#let _snap-node(id) = _dot-label(_dot-node-line(_snap, "cfg-contexts-dot", id))
#let _fig_node(pos, id, boundary: false) = node(
  pos,
  text(size: 7pt, font: "DejaVu Sans Mono", _snap-node(id)),
  stroke: 0.8pt + (if boundary { vb.accent } else { vb.neutral }),
  fill: if boundary { vb.accent.lighten(90%) } else { white },
  corner-radius: if boundary { 2pt } else { 6pt },
  inset: 3.5pt,
)
#let _fig_edge(src, dst, a, b, ..args) = edge(
  a,
  b,
  "-|>",
  stroke: 0.7pt + vb.neutral,
  label: text(size: 7pt, font: "DejaVu Sans Mono", _snap-label(src, dst)),
  label-sep: 2pt,
  ..args,
)
#let _pc(src, dst, a, b, ..args) = edge(
  a,
  b,
  "-|>",
  stroke: (paint: vb.called, thickness: 0.8pt, dash: "dashed"),
  label: text(size: 7pt, font: "DejaVu Sans Mono", fill: vb.called, _snap-label(
    src,
    dst,
  )),
  label-sep: 2pt,
  ..args,
)
#let _pk(src, dst, a, b) = edge(
  a,
  b,
  "-|>",
  stroke: (paint: vb.called, thickness: 0.7pt, dash: "dotted"),
  label: text(size: 7pt, font: "DejaVu Sans Mono", fill: vb.called, _snap-label(
    src,
    dst,
  )),
  label-side: right,
  label-sep: 2pt,
  bend: -40deg,
)

#figure(
  {
    set text(size: 8pt)
    set par(first-line-indent: 0pt, justify: false)
    grid(
      columns: (auto, 1fr),
      column-gutter: 6pt,
      align: horizon,
      block(width: 58mm, playground-program("contexts")),
      align(center, diagram(
        spacing: (7mm, 4.6mm),
        _fig_node((0, 0), "main_entry_main", boundary: true),
        _fig_node((0, 1), "main_pp2"),
        _fig_node((0, 2), "main_pp3"),
        _fig_node((0, 3), "main_pp4"),
        _fig_node((0, 4), "main_pp5"),
        _fig_node((0, 5), "main_pp6"),
        _fig_node((0, 6), "main_exit_main", boundary: true),
        _fig_node((2.6, 1), "bump_entry_bump", boundary: true),
        _fig_node((2.6, 2.4), "bump_pp0"),
        _fig_node((2.6, 3.8), "bump_exit_bump", boundary: true),
        _fig_edge("main_entry_main", "main_pp2", (0, 0), (0, 1)),
        _fig_edge("main_pp4", "main_pp5", (0, 3), (0, 4)),
        _fig_edge("main_pp5", "main_pp6", (0, 4), (0, 5)),
        _fig_edge("main_pp6", "main_exit_main", (0, 5), (0, 6)),
        _fig_edge(
          "bump_entry_bump",
          "bump_pp0",
          (2.6, 1),
          (2.6, 2.4),
          label-side: left,
        ),
        _fig_edge(
          "bump_pp0",
          "bump_exit_bump",
          (2.6, 2.4),
          (2.6, 3.8),
          label-side: left,
        ),
        _pc("main_pp2", "bump_entry_bump", (0, 1), (2.6, 1), label-side: left),
        _pc(
          "main_pp3",
          "bump_entry_bump",
          (0, 2),
          (2.6, 1),
          label-side: right,
          label-pos: 0.45,
          label-sep: 3pt,
          label-anchor: "north",
          bend: -25deg,
        ),
        _pk("main_pp2", "main_pp3", (0, 1), (0, 2)),
        _pk("main_pp3", "main_pp4", (0, 2), (0, 3)),
      )),
    )
  },
  kind: image,
  placement: none,
  caption: [The running example and its procedure-aware graph, with node and
    edge labels as `voblint --dot` prints them. Solid arrows are local edges and
    dashed arrows are call edges (@sec:cfg). Dotted connectors are not edges. They show the
    continuation of a call edge, that is, the node where the caller resumes. @fig:eq-unknowns shows the unknowns
    that @ch:equations generates around the first call.],
) <fig:program-to-equations>

== VIMP syntax and well-formed programs <sec:vimp>

VIMP is kept small because every construct needs a semantics, compiler
clauses, and a transfer function proved sound in every abstract domain. It has
unbounded integer variables, locals and globals, procedures with value
parameters, direct calls with an optional result, recursion, assignment,
sequencing, conditionals, `while` loops, nondeterministic input, and checks.

Expressions are integer-valued. Comparisons and logical operators yield $0$
or $1$, and a condition holds when it is nonzero (#isaconst("truthy")).

#definition(name: [Expressions], isa: "exp", cmd: "datatype")[
  $
    e ::= & n | x | e #vop("+") e | e #vop("−") e | e #vop("*") e | e #vop("/") e
            | e #vop("%") e \
        | & e #vop("<") e | e #vop("<=") e | e #vop(">") e | e #vop(">=") e
            | e #vop("!=") e | e #vop("==") e \
        | & #vop("!", unary: true) e | e #vop("&&") e | e #vop("||") e
  $
]

Each operator has its own constructor, because an abstract domain chooses its
abstract operation by the operator, and the executable analyzer has to make
this choice by inspecting the syntax. We considered two languages with
procedures from Isabelle's Archive of Formal Proofs (AFP), IMP2 and Simpl.
Both represent operators semantically instead. IMP2 @lammich19imp2 represents a binary operator by a HOL
function of type #isai("int \<Rightarrow> int \<Rightarrow> int"). Concrete
evaluation can apply such a function, but executable code cannot compare it
with another one, so it cannot tell `+` from `*`. IMP2's semantics is also deterministic, so it
has no input, and its call command takes no arguments and returns no value.
Parameters and results pass through variables set by generated code
(@ch:related). Schirmer's Simpl @schirmer08simpl is more expressive, with
nondeterministic specifications and a derived call command that passes
parameters, but its basic commands and conditions are likewise HOL functions
and sets of states. Both languages target program verification, where such
semantic objects are convenient. VIMP is therefore defined from scratch, with
a syntax that the analyzer can inspect and that code generation can export.

VIMP represents a store $s$ as a total function from variable names to
integers (#isatype("store")). Evaluation $sem(e)_e thin s$ (#isaconst("aval"))
is a function defined by one equation per constructor, for example
$
  sem(n)_e thin s = n, quad
  sem(x)_e thin s = s(x), quad
  sem(e_1 #vop("/") e_2)_e thin s = #isaconst("c_div") (sem(e_1)_e thin s, sem(e_2)_e thin s), \
  sem(e_1 #vop("<") e_2)_e thin s = cases(1 & "if" sem(e_1)_e thin s < sem(e_2)_e thin s, 0 & "otherwise".)
$
Every expression has a value, because VIMP fixes the results of division and
remainder by zero (#isaconst("c_div"), #isaconst("c_mod"), @sec:vimp-vs-c). It also has no
effects, so a transfer function may evaluate a guard again, as the backward
filtering of guards in an analysis does. Input enters only through the statement
`x = __voblint_nondet_int();` and never inside an expression. Restricting input to this statement keeps #isaconst("aval") a function.

Commands are built from expressions. Besides the structured statements, there
are calls, which may store a result, and two markers that appear only during
execution.

#definition(name: [Commands], isa: "gcom", cmd: "datatype")[
  $
    c ::= & #skipC | x := e | #keyw("check") (e) | c";" c
            | #keyw("if") (e) {c} #keyw("else") {c} | #keyw("while") (e) {c} \
        | & [x :=] thin p(e, ..., e) | #keyw("return") e? | #ctor("Restore") | #ctor("Unwind")
  $
]

As in @sec:intro-static, a check states a condition
for the analyzer to decide. It does not influence the
execution. It behaves like
#skipC whatever value $e$ has, so it neither stops the execution nor refines the
store.

Calls come in two kinds. A call of a declared procedure starts an activation
of that procedure (@sec:interproc).
VIMP also has three built-in _library calls_, `__voblint_nondet_int`, `min`,
and `max`, which a program calls but does not declare. A fixed table recognizes
their names, and a result relation gives the values they may return, any
integer for `__voblint_nondet_int` and the minimum or maximum of the arguments
for `min` and `max` (#isaconst("special_table"), #isaconst("special_result")).
A library call finishes in one step and stores its value without starting an
activation. The
remaining constructors, #ctor("Restore") and #ctor("Unwind"), are not source
syntax (#isaconst("source_com") excludes them). They appear only during
execution, where @sec:pstep uses them for calls and returns.

A program is a list of procedure declarations, each with formal parameters and
a body, plus a list of global variables (#isatype("imp_prog")). Its procedure
table $Pi$ looks up a name in that list, and the classifier $cal(G)$ tests
membership in the globals (#isaconst("declared_global")). The entry procedure
is the declaration named `main`, and #isaconst("main_body") $Pi$ is its body. @fig:vimp-ast shows the running example in this form. The formal
development starts from this parsed program, and the parser lies outside the
theorem (@fig:intro-trust).

// The tree is read from the parser's own output (claim ast-contexts), the JSON
// the playground hands to the analyzer, so it cannot drift from the frontend.
#let _ast = json(bytes(read("/shared/generated/ast-contexts.txt")))
#let _ast-tree(t) = {
  let lit(x) = text(font: "DejaVu Sans Mono", size: 0.9em, str(x))
  if type(t) == str { return ctor(t) }
  let (tag, args) = t.pairs().first()
  let node(..xs) = (ctor(tag), ..xs.pos().map(_ast-tree))
  if tag == "N" or tag == "V" { ctor(tag) + [ ] + lit(args) } else if tag == "Seq" {
    node(..args)
  } else if tag == "Call" {
    let (dst, callee, actuals) = args
    (
      [#ctor(tag) #lit(if dst == none { "_" } else { dst }) #lit(callee)],
      ..actuals.map(_ast-tree),
    )
  } else if tag == "Check" {
    ([#ctor(tag) #lit(args.at(0).map(str).join(":"))], _ast-tree(args.at(1)))
  } else if type(args) == array { node(..args) } else { node(args) }
}
#let _ast-draw(t) = cetz.canvas(length: 1cm, {
  import cetz.draw: *
  set-style(content: (padding: 1.5pt), stroke: 0.5pt + vb.neutral)
  cetz.tree.tree(
    _ast-tree(t),
    spread: 0.95,
    grow: 0.36,
  )
})
#figure(
  {
    set text(size: 6.8pt)
    // The parser prints globals, main's body and the procedure table, in order.
    let (_, main-body, table) = _ast.values()
    let (name, decl) = table.first()
    grid(
      columns: (auto, auto),
      column-gutter: 16pt,
      row-gutter: 6pt,
      align: (center + bottom, center + bottom),
      _ast-draw(main-body), _ast-draw(decl.body),
      [`main`'s body (#isaconst("prog_main"))],
      [#raw(name)'s body, formals #raw(decl.formals.join(", "))],
    )
  },
  kind: image,
  placement: none,
  caption: [The running example as the parser returns it, with the `main` body,
    the one callee declaration, and no globals. A
    #ctor("Call", thy: "VIMP_Proc") names its destination and callee, and a
    #ctor("Check") names its source position.],
) <fig:vimp-ast>

Not every parsed program can run meaningfully. The theorems therefore
assume the _source contract_ #isaconst("wf_source_program"), which excludes programs in which a call cannot step or a result is undefined. It requires
that

- every call names either a declared procedure with matching arity or a
  library call with suitable arguments and a destination,
- formals are distinct valid locals, and `main` is declared, takes no
  arguments, and contains no #keyw("return") (@sec:pstep),
- bodies contain no runtime markers #ctor("Restore") or #ctor("Unwind"),
- no declared name is a library name,
- the result variable #isaconst("ret_var") is reserved, so it is not global,
  no source expression reads it, and no assignment or call destination writes
  it,
- a call that stores a result names a _value-providing_ callee, one that ends
  every completed execution of its body with a #keyw("return") of a value.

A body _falls through_ when execution reaches its end without a
#keyw("return"). Value-providing is a syntactic condition
(#isaconst("value_providing")). It requires that the body cannot fall through,
that it cannot reach a #keyw("return") without a value, and that it can reach a
#keyw("return") with a value. So every path through the callee that completes returns a value,
although the callee may still diverge. C11 makes using the value of a call that
falls through undefined (#c11("6.9.1p12")). Without the condition, VIMP would
silently store the $0$ that the reset on entry left in #isaconst("ret_var").

== Small-step source semantics #thy-badge("Voblint_VIMP", "VIMP_Proc") <sec:pstep>

An _operational semantics_ defines the meaning of a program by how it
executes. A _small-step_ operational semantics does so one step at a time. A
step relation leads from one configuration to the next, and a run is a
sequence of steps @plotkin04[§3.2]. VIMP's semantics #isaconst("pstep") is of
this kind. It is called the _source semantics_, to distinguish it from the graph
semantics of @sec:cstep, which is also a small-step semantics.

Without calls, a configuration is a pair $(c, s)$ of the command that remains
to run and the store, as in the semantics of IMP by Nipkow and Klein
@nipkow14[§7.3]. An assignment updates the store and leaves #skipC, and a
check leaves the store unchanged. A sequence steps its first command until it
is #skipC, a conditional selects a branch by #isaconst("truthy"), and a loop
unfolds into a conditional that runs the body and then the loop again. After
each step, the remaining command describes the remainder of the execution
@plotkin04[§3.2], here called a _residual_.

Calls raise two questions. While a callee runs, the caller's remaining work
has to wait somewhere, and a #keyw("return") has to skip the rest of the
callee's body. VIMP keeps the waiting work inside the residual command and
saves only data on a stack. A call continues with the callee's body followed
by #ctor("Restore"), a marker that exists only at run time and hands control
back to the caller once the body falls through. A #keyw("return"), possibly
before the end of the body, becomes the marker #ctor("Unwind"), which
discards the commands after it until it meets the #ctor("Restore") of its
call. Each suspended activation keeps its data in a _frame_.

#definition(name: [Source execution], isa: "pstep", cmd: "inductive")[
  A source configuration is a triple $(c, s, italic("frs"))$ of the command that
  remains to run, a store $s$, and a list $italic("frs")$ of
  #isatype("frame") values for the suspended activations. Each frame records
  the caller's store and the variable, if any, that receives the result. The
  step relation #isaconst("pstep") relates a configuration to its successor.
]

Fix the global-variable classifier $cal(G)$ and procedure table $Pi$.
Write $kappa ->_p kappa'$ for one step and $->_p^*$ for its reflexive
transitive closure. The rules below define the step relation.
We write $c_1 ; c_2$ for sequencing and $(s_c,italic("dst")) :: F$ for pushing
a frame. The optional destination $italic("dst")$ is either $"None"$ or
$"Some"(x)$.

*Local commands.* Assignment updates one variable; a check records no runtime
failure and leaves the store unchanged:
$
  ("assign" (x,e),s,F) & ->_p ("skip",s[x mapsto sem(e)_e s],F), \
   ("check" (l,e),s,F) & ->_p ("skip",s,F), \
      ("skip" ; c,s,F) & ->_p (c,s,F).
$
A sequence propagates a step of its first command:
$
  frac(
    (c_1,s,F) ->_p (c_1',s',F'),
    (c_1 ; c_2,s,F) ->_p (c_1' ; c_2,s',F')
  ).
$
A conditional $"if" (b,c_1,c_2)$ steps to $(c_1,s,F)$ if
$sem(b)_e s != 0$, and to $(c_2,s,F)$ otherwise. A loop unfolds as
$
  ("while" (b,c),s,F) ->_p
  ("if" (b,c ; "while" (b,c),"skip"),s,F).
$

*Procedure calls.* Suppose $Pi(p)="Some"(d)$, the actual-argument list
$italic("es")$ has the same length as the formal-parameter list $italic("xs")$ of $d$, and $italic("xs")$
contains no duplicate. Let $s_e$ reset the caller's local variables to zero,
retain its globals, and then bind $italic("xs")$ to the values of $italic("es")$ evaluated in $s$
(#isaconst("enter_state"), #isaconst("bind_formals")). Then
$
  ("call" (italic("dst"),p,italic("es")),s,F) ->_p
  ("body"(d) ; "restore",s_e,(s,italic("dst")) :: F).
$
The frame retains the caller's store even while the callee changes its own.
#block(breakable: false, width: 100%)[
  Library calls (@sec:vimp) need a rule of their own. A program does not
  declare them, so the procedure table has no body for them and the rule above
  does not apply. A fixed library table gives their meaning instead. Since no
  body runs, the call finishes in one step and pushes no frame. The result
  relation can admit more than one value, which is how `__voblint_nondet_int`
  supplies an arbitrary input. Formally, if the library table maps $p$ to
  $"Some"(italic("desc"))$, classifying the arguments $italic("es")$ against
  $italic("desc")$ yields $"Some"(italic("sc"))$, and $italic("sc")$ can return
  $z$ in $s$, then
  $
    ("call" ("Some"(x),p,italic("es")),s,F) ->_p ("skip",s[x mapsto z],F).
  $
  The classification fails when the number of arguments does not match
  (#isaconst("special_table"), #isaconst("classify_special"),
  #isaconst("special_result")). The rule requires a destination $x$.
]

*Returns and restoration.* Let $r_v$ be the reserved return variable
(#isaconst("ret_var")). The returned store $#isaconst("combine_collect") _(italic("dst")) (s_c,s_r)$
takes locals from $s_c$ and globals from $s_r$, and then, when
$italic("dst")="Some"(x)$, assigns $s_r (r_v)$ to $x$. For $italic("dst")="None"$, this
final assignment is omitted. Then
$
  ("return" ("Some"(e)),s,F) & ->_p ("unwind",s[r_v mapsto sem(e)_e s],F), \
  ("return" ("None"),s,F) & ->_p ("unwind",s,F), \
  ("restore",s_r,(s_c,italic("dst")) :: F) & ->_p ("skip",#isaconst("combine_collect") _(italic("dst")) (s_c,s_r),F).
$
When $c$ is not a restoration marker,
$ ("unwind" ; c,s,F) ->_p ("unwind",s,F). $
At the restoration marker, unwinding instead pops the caller's frame:
$
  ("unwind" ; "restore",s_r,(s_c,italic("dst")) :: F)
  ->_p ("skip",#isaconst("combine_collect") _(italic("dst")) (s_c,s_r),F).
$

In Isabelle, these rules form one inductive definition, with one named
introduction rule per case above. There the commands are capitalized
constructors, a frame is written #ctor("Frame") $s_c$ $italic("dst")$, and
$#isaconst("combine_collect") _(italic("dst")) (s_c,s_r)$ appears unfolded into
#isaconst("combine_env") and #isaconst("combine_assign")
(#isaconst("pstep")).

The root activation is modeled without a #ctor("Restore"), since `main` has no
caller to return to, and a bare #ctor("Unwind") has no step
(#isathm("pstep_Unwind_stuck")). The source contract therefore rejects
#keyw("return") in `main` (#isaconst("no_return")). A source execution starts from
the configuration $(#isaconst("main_body") thin Pi, s_0, [])$, with an initial
store $s_0$ in #isaconst("cinit_stores") (@sec:vimp-vs-c).

Just as Nipkow and Klein show that well-typed programs do not get stuck
@nipkow14[§9.1.2], Voblint proves that well-formed VIMP programs do not. Otherwise,
claims about the points after a stuck execution would hold vacuously. For a program satisfying
#isaconst("wf_source_program"), every reachable configuration has either
finished, as #skipC with an empty frame stack, or can step:

#theorem(name: [Progress of source execution], isa: "source_progress")[
  Assume the source program is well formed. Every configuration $kappa=(c,s,F)$
  reached by finitely many source steps from the main body and an empty stack,
  starting in any store, satisfies
  $ (c = #skipC and F=[]) or exists kappa'. kappa ->_p kappa'. $
]

== The procedure-aware control-flow graph <sec:graph>

The analysis attaches an abstract state to each program point and a transfer
function to each transition between points. Voblint takes both from a
procedure-aware control-flow graph, whose nodes are the program points and
whose local edges and call edges carry the transfers. The source semantics
cannot play this role (@sec:why-graph).

=== Program points for the analysis <sec:why-graph>

The source semantics #isaconst("pstep") offers neither program points nor
transitions in a usable form. Its only
notion of location is the command that remains to run. Without recursion, only finitely many distinct residual commands arise,
because a loop may run arbitrarily often, but its unfolding revisits the same
command forms. Recursion is different, because a recursive call can nest
another #ctor("Restore") marker at every call depth. Residual commands
therefore do not form the finite, fixed set of locations that Voblint needs. An assignment is also not a transition between fixed program points. Inside a sequence, it steps through the rule
#isathm("pstep.Seq2"), which rebuilds the surrounding residual command. So the same assignment is executed by a different derivation inside every surrounding command.
Finally, nothing names the entry of a procedure, its result, or the point where
a caller resumes.

The schematic control-flow graph of @fig:counting-loop solves
the first two problems. It has finitely many nodes and one transfer per edge.
The procedure-aware graph then solves the third. It adds an entry node and a result
node per procedure, and call edges that record their continuations. Each gives
the analysis a place for one fact about a call. The entry node holds the state
a callee starts from, the result node the state it returns with, and the
continuation names the node where the caller resumes. A call can therefore be
analyzed by connecting the call site, the callee's entry and result nodes, and
the continuation, instead of by following the callee's body (@ch:equations).

Introducing a graph is a design choice. A _syntax-directed_ analyzer, such as
that of Nipkow and Klein @nipkow14[Ch. 13], computes its result by recursion
over the command structure and needs no graph. Voblint instead follows Goblint
and is _constraint-based_ @apinis12: it turns the program into a system of
inequalities over unknowns indexed by the graph's nodes. A generic solver,
independent of the programming language, then solves this system. Calls need
no support in the solver, because a call contributes right-hand sides and side
effects to the same system. In turn, a simulation must show that the compiler preserves the program's executions (@sec:csim), and @ch:traces must
relate the inequalities to those executions. In exchange, the reasoning about
programs ends at a post-solution on the solved set, a certificate that does not
depend on which solver produced it.

=== Nodes, local edges, and call edges #thy-badge("Voblint_CFG", "CFG_Def") <sec:cfg>

#definition(name: [Control-flow graph], isa: "cfg", cmd: "record")[
  A graph consists of a local-edge relation, a call-edge relation, and an entry
  node. Its Isabelle representation is a record of type #isatype("cfg"):
  #{
    show raw.where(block: true): set text(size: 6.5pt)
    thy("cfg")
  }
  The field #isaconst("intra") holds the _local edges_ $(u, a, v)$, each labeled
  by an action $a$. The field #isaconst("calls") holds the _call edges_
  $(u, italic("ca"), w, k)$. A call edge consists of the call site $u$, the
  call information $italic("ca")$, a node $w$, which in a well-formed graph is
  the callee's entry $ctor("FunctionEntry") thin q$ (#isaconst("wf_cfg")), and
  the node $k$ where the caller resumes. Nodes are
  $ctor("Statement") thin n$, $ctor("FunctionEntry") thin p$, or
  $ctor("FunctionResult") thin p$, and the third field holds the entry node.
]

The call information $ctor("CallEdge") thin italic("dst") thin
italic("formals") thin italic("args")$ (#isatype("call_action")) copies the
callee's formals onto the edge, so the graph semantics binds actuals to formals
without looking up the procedure table. VIMP has no function pointers (@sec:vimp), so
every call names its callee, and the compiler can fix the target of each call
edge. Supporting indirect calls would require discovering call targets during the analysis, which is left for future work.
The node kinds match Goblint's
(#link("https://github.com/goblint/analyzer/blob/5320a6b741e50dc049f7a1b85e1709e9565cc54a/src/common/framework/node0.ml")[`node0.ml`]),
which also has statement and function-entry nodes and calls Voblint's
$ctor("FunctionResult")$ node `Function`.

The graph keeps local edges and call edges apart, in its fields
#isaconst("intra") and #isaconst("calls"), because they execute differently. A
local edge changes the store within one activation, while a call edge starts a
new one. No edge action denotes a call, so a call can never be taken as a
local step, and each rule of the trace semantics in @ch:traces reads at most
one of the two relations.

Returns, in contrast, are ordinary local edges. A #keyw("return") in $p$ leads
to the result node $ctor("FunctionResult") thin p$, which all callers of $p$
share, so recursion needs no copies of nodes. A shared result node does not determine where to continue, and in a compiled graph, no edge leaves it. The call edge
records that place instead, as its continuation $k$. After a return, execution
resumes at the continuation saved in the frame, and an analysis connects the
callee's exit state to the correct caller through the call edge. The matching
caller is explicit in the graph, so no separate return-to-call matching is
needed. A completed program ends at
$ctor("FunctionResult") thin #raw("main")$ (#isaconst("cfg_exit")), so there
is no separate global exit node.

== Compilation to a control-flow graph <sec:compilation>

The compiler turns a VIMP program into a procedure-aware graph. Its design
decides which program points exist, and the simulation of @sec:csim relies on
how it lays out the code of each command.

=== Compilation with continuations #thy-badge("Voblint_Compile", "VIMP_Proc_to_CFG") <sec:compile>

To emit the edges of a command, a compiler has to know where control goes
after it. Compilers commonly pass this target down, so that each statement
receives the label of the code that follows it, the inherited attribute
$S."next"$ of the dragon book @aho06[§6.6.3]. Voblint's compiler works the
same way and is therefore called _continuation-passing_. Besides the command,
it takes the node $k$ at which control continues afterward, and it emits the
command's edges so that they end at $k$ (#isaconst("compile") for commands,
#isaconst("compile_proc") and #isaconst("compile_prog") for procedures and
programs). Schematically, writing $#isaconst("compile") (c, k)$ for the edges of $c$
against the continuation $k$, and $n$ and $h$ for fresh nodes,
$
  #isaconst("compile") (x = e, k) & = {n ->^(x = e) k}, \
  #isaconst("compile") (c_1";" c_2, k) & = #isaconst("compile") (c_1, "entry"(c_2)) union #isaconst("compile") (c_2, k), \
  #isaconst("compile") (#keyw("if") (e) {c_1} #keyw("else") {c_2}, k) & = {n ->^e "entry"(c_1), n ->^(not e) "entry"(c_2)} \
  & quad union #isaconst("compile") (c_1, k) union #isaconst("compile") (c_2, k), \
  #isaconst("compile") (#keyw("while") (e) {c}, k) & = {h ->^e "entry"(c), h ->^(not e) k} union #isaconst("compile") (c, h), \
  #isaconst("compile") (x = q(overline(e)), k) & = {(n, x = q(overline(e)), ctor("FunctionEntry") thin q, k)}, \
  #isaconst("compile") (#keyw("return") e, k) & = {n ->^(#keyw("return") e) ctor("FunctionResult") thin p}.
$
A #skipC and a check compile like the assignment, to one edge from a fresh node
to $k$. The alternative would give every fragment an exit node of its own, and
sequencing two fragments would then need a no-op edge between two nodes that
denote the same program point. With continuations, a node is a program point
between two transfers, as in Goblint's CFG. A conditional needs no join node,
because both branches end at the same $k$. A loop compiles its body against
its own head, so the compiled counting loop of @fig:counting-loop has no node
$t$ and no edge $t -> h$. A #skipC branch adds no node, and its guard edge
leads to $k$.

Calls and returns leave the current fragment. A call $x = q(overline(e))$ of a
declared procedure $q$ adds no local edge. It becomes a single call edge in
#isaconst("calls"), from the call site $n$ to the callee's entry, with $k$ as
its continuation. A library call finishes in one step (@sec:vimp) and
compiles to a local edge to $k$ instead. A #keyw("return") becomes an
#isaconst("EA_Ret") edge to the result node of its procedure, and a body that
can reach its end without a #keyw("return") needs such an edge as well.
#isaconst("compile_proc") therefore compiles the body $c$ of a procedure $p$
against an extra node $r$ and connects both to the procedure's own nodes,
$
  #isaconst("compile_proc") (p) & = {ctor("FunctionEntry") thin p ->^(sans("body")) "entry"(c)}
                                  union #isaconst("compile") (c, r) \
                                & quad union {r ->^(#keyw("return")) ctor("FunctionResult") thin p}.
$
The #isaconst("EA_Body") edge marks the start of an activation and changes no
store. The return edge from $r$ carries no value. It is emitted for every body,
so in a body that always returns, $r$ and its edge are dead code.
@sec:certificate explains why the compiler keeps them. Every edge into
$ctor("FunctionResult") thin p$ is therefore a return edge.

These rules give every compiled graph a fixed shape. Call edges always enter an
entry node, no local edge enters one, and every return edge ends at the
result node of its own procedure. The structural contract #isaconst("wf_cfg")
collects these properties, and every compiled graph satisfies it without
premises (#isathm("compile_prog_wf")). The graph's entry is
$ctor("FunctionEntry") thin #raw("main")$ (#isathm("cfg_entry_compile_prog")),
and its edge sets are finite (#isathm("compile_prog_finite")). Later chapters
rely on this shape to route calls (@ch:equations) and to enumerate edges in the
executable analyzer.
@fig:cfgmap shows the graph compiled from a recursive program.

#let _sum-program = read("/shared/programs/sum-dec.vimp").trim()
#let _sum-graph = sum-graph

#figure(
  layout(size => {
    let code = block(width: 47mm, {
      show raw: set text(size: 7pt)
      listing(lang: "c", ctx: "none", _sum-program)
    })
    let graph = _sum-graph
    let gutter = 12pt
    // As tall as the code, unless that would overrun the text width.
    let room = size.width - measure(code).width - gutter
    let f = calc.min(
      measure(code).height / measure(graph).height,
      room / measure(graph).width,
    )
    grid(
      columns: (auto, auto),
      column-gutter: gutter,
      align: horizon,
      code, scale(f * 100%, reflow: true, graph),
    )
  }),
  kind: image,
  placement: none,
  caption: [A recursive program and its compiled graph, labeled as
    `voblint --dot` prints it, where $sans("pp") thin n$ is
    $ctor("Statement") thin n$. Solid arrows are local edges and dashed arrows
    call edges. Dotted connectors mark the continuation of a call, and thin
    arrows the return to it. Each procedure has one copy of its nodes,
    whatever the recursion depth.],
) <fig:cfgmap>


A program is compiled one procedure after another, each over fresh node
numbers. Since the procedure table $Pi$ cannot enumerate its domain, the
compiler also takes a list $italic("ps")$ of the procedures. Its contract
#isaconst("wf_compile_input") $cal(G)$ $Pi$ $italic("ps")$ extends
#isaconst("wf_source_program") by requiring $italic("ps")$ to list every declared
procedure except `main` exactly once.

=== Graph execution with a frame stack #thy-badge("Voblint_CFG", "CFG_Exec") <sec:cstep>

The compiler produces a static object. To say that it preserves the behavior
of a program, the graph needs an execution of its own, which @sec:csim then
compares with #isaconst("pstep"). Within one procedure, an execution follows
edges, so a node and a store would describe its state. Calls break this
picture. A call edge leads to the callee's entry, but the callee ends at its
result node, which all callers share and which no edge leaves (@sec:cfg). The
graph alone thus cannot say where execution continues after a return. Graph
execution therefore keeps a stack of suspended callers, like the call stack of
a machine. A call pushes a frame that remembers the continuation $k$ of its
call edge, the variable that receives the result, and the caller's store,
whose local variables the return restores. A return pops the frame and
continues at $k$. In the running example (@fig:program-to-equations), the call
`bump(5)` pushes a frame, runs the body of `bump` with $n = 5$, and pops the
frame at the result node, after which `main` continues at the call's
continuation with `a` holding $6$. The second call `bump(4)` pushes a frame of
its own, with a different continuation, so the shared result node of `bump`
returns each activation to the right place.

A frame saves the caller's whole store. The return takes the local variables
from it and the globals from the callee's final store, and then assigns the
result to the destination (#isaconst("combine_collect")). A source frame
(@sec:pstep) records the same data except the continuation, which the source
semantics keeps in the residual command instead, behind the #ctor("Restore")
marker.

#block(breakable: false)[
  #definition(name: [Graph execution], isa: "cstep", cmd: "inductive")[
    A graph configuration $(v,s,K)$ (#isatype("cconf")) consists of a node
    $v$, a store $s$, and a frame stack $K$. Each frame $(k,italic("dst"),s_c)$
    (#isatype("cframe")) records the continuation node $k$, the optional
    destination $italic("dst")$, and the caller's store $s_c$. The step
    relation $kappa ->_c kappa'$ (#isaconst("cstep")) is defined by the rules
    below, and $->_c^*$ is its reflexive transitive closure.
  ]

  Fix $cal(G)$ and $g$.
  For a call edge $e=(u,a,#ctor("FunctionEntry") thin p,k)$ with destination $italic("dst")$,
  $#isaconst("call_enter") _e (s)$ is its entered store, and $#isaconst("combine_collect") _(italic("dst")) (s,t)$
  the returned store. The rules are
  $
    frac(
      (u,a,v) in "intra"(g) quad s' in sem(a)(s),
      (u,s,K) ->_c (v,s',K)
    ),
  $
  $
    frac(
      e=(u,a,#ctor("FunctionEntry") thin p,k) in "calls"(g),
      (u,s,K) ->_c (#ctor("FunctionEntry") thin p,#isaconst("call_enter") _e (s),(k,italic("dst"),s) :: K)
    ),
  $
  $
    (#ctor("FunctionResult") thin p,t,(k,italic("dst"),s) :: K) ->_c (k,#isaconst("combine_collect") _(italic("dst")) (s,t),K).
  $
  Here $sem(a)(s)$ is the set of local successors (#isaconst("edge_step")).
]

Calls and returns
change the store through #isaconst("call_enter") and
#isaconst("combine_collect"), which are built from the same functions as
#isaconst("pstep") (@sec:pstep), so both executions can hold the same store. Like the trace semantics of
@ch:traces, #isaconst("cstep") is defined for an arbitrary graph, not only for
compiled ones.

== Simulation of source executions <sec:csim>

Nothing yet says that a compiled graph behaves like its program. The soundness
theorem is stated over #isaconst("pstep"), but the analysis solves equations
generated from the graph, so every source execution must be matched by an execution of the
compiled graph that holds the same store at corresponding points. The matching is proved with a _forward simulation_, a
relation between source and graph configurations that every source step
preserves.

The relation cannot simply pair each command with a node. When one procedure
calls another, the source keeps the caller's remaining work inside the running
command, behind a #ctor("Restore") marker, while the graph keeps it on the frame
stack as the continuation node $k$. The relation therefore has to match a
nested command against a stack of frames. A source step also does not
always match exactly one graph step. Some source steps only rearrange the command, such as unfolding a
loop into a conditional, discarding a finished #skipC, or propagating
#ctor("Unwind") past the commands it skips. They have no graph counterpart, so
the graph answers one source step with zero or more steps. Only this direction
is proved. An analysis that covers every graph execution from the entry (@ch:traces)
then also covers every source execution, so soundness needs no converse.

=== Simulation relation and step matching <sec:csim-step>

#definition(name: [Simulation relation], isa: "csim", cmd: "inductive")[
  A _block_ $B=(p,b,k,n)$ consists of a procedure $p$, a body $b$, the number
  $n$ of the body's first node, and its exit node $k$. The predicate $#isaconst("compiled_at") (B)$ holds if
  $b$ is the body of $p$ in $Pi$, the edges of $b$ compiled from node $n$
  against continuation $k$ lie in $g$, together with the entry edge from
  $ctor("FunctionEntry") thin p$ to node $n$ and the fall-through return edge
  from $k$ to $ctor("FunctionResult") thin p$, and $k$ is the node directly
  after the body. The predicate $#isaconst("control_at") _B (c,v)$ holds
  if the command $c$ is what remains of $b$ and the compiler placed it at node
  $v$. Write $c ; A$ for a command $c$ followed by the
  list $A$ of commands after it, and $F dot.op F'$ for the concatenation of
  frame stacks. The predicate $#isaconst("pop_ready") (w)$ says that the source
  command $w$ is ready to pop its frame.
  The relation $kappa approx lambda$ relates a source configuration
  $kappa = (c,s,F)$ (@sec:pstep) to a graph configuration $lambda = (v,s,K)$
  (@sec:cstep) with the same store $s$. It is defined by the
  following rules, where $B=(p,b,k,n)$ is
  a block of a procedure $p$, and $u$ and $italic("es")$ are arbitrary.

  $
    sans("Base") quad frac(
      #isaconst("control_at") _B (c,v) quad #isaconst("compiled_at") (B),
      (c,s,[]) approx (v,s,[])
    )
  $
  $
    sans("Nested") quad frac(
      display(
        mat(
          delim: #none,
          (c,s,F) approx (v,s,K) quad #isaconst("compiled_at") (B);
          #isaconst("control_at") _B ("skip" ; A, k') quad
          #isaconst("control_at") _B ("call" (italic("dst"),q,italic("es")) ; A, u),
        )
      ),
      ((c ; "restore") ; A, s, F dot.op [(s_c,italic("dst"))])
      approx (v,s,K dot.op [(k',italic("dst"),s_c)])
    )
  $
  $
    sans("Returning") quad frac(
      display(
        mat(
          delim: #none,
          #isaconst("pop_ready") (w) quad #isaconst("compiled_at") (B);
          #isaconst("control_at") _B ("skip" ; A, k') quad
          #isaconst("control_at") _B ("call" (italic("dst"),q,italic("es")) ; A, u),
        )
      ),
      (w ; A, s, [(s_c,italic("dst"))])
      approx (#ctor("FunctionResult") thin q, s, [(k',italic("dst"),s_c)])
    )
  $
]

Each rule relates one activation at a time. $sans("Base")$ covers an execution
without suspended callers, where both stacks are empty. $sans("Nested")$ wraps
one suspended caller around an activation that is already related. In the
source, the caller's remaining work $A$ follows the restoration marker. In the
graph, it starts at the continuation node $k'$ of the new frame. The premise
about the call locates the call $"call" (italic("dst"),q,italic("es"))$ in
the caller. The inner activation therefore runs the body of the procedure $q$
it names. $sans("Returning")$
covers the moment after a callee finishes. The graph is already at the
callee's result node, while the source command $w$ is ready to pop its frame.

The relation is useful only if every source step preserves it, as drawn in
@fig:csim-square.

#block(breakable: false, width: 100%)[
  #theorem(name: [Graph executions simulate source steps], isa: "csim_step")[
    Assume that the body of every declared procedure is compiled into $g$
    (#isaconst("procs_embedded")), and that the command of $kappa$ returns only
    inside an activation that a call opened (#isaconst("return_safe")). If
    $kappa approx lambda$ and $kappa ->_p kappa'$, then
    $ exists lambda'. lambda ->_c^* lambda' and kappa' approx lambda'. $
  ]
]

#figure(
  {
    set text(size: 11pt)
    let dashed = (dash: "dashed")
    diagram(
      spacing: (36mm, 18mm),
      node((0, 0), $kappa$, name: <k>),
      node((1, 0), $kappa'$, name: <k2>),
      node((0, 1), $lambda$, name: <l>),
      node((1, 1), $lambda'$, name: <l2>),
      edge(<k>, <k2>, "-|>", isaconst("pstep")),
      edge(<k>, <l>, "-", $approx$, label-side: right),
      edge(<l>, <l2>, "-|>", [#isaconst("cstep")#super[\*]], label-side: right, stroke: dashed),
      edge(<k2>, <l2>, "-", $approx$, label-side: left, stroke: dashed),
    )
  },
  kind: image,
  caption: [Step matching (#isathm("csim_step")): given the solid part, the
    dashed part exists. The graph may answer a source step with zero, one, or
    several #isaconst("cstep") steps.],
) <fig:csim-square>

In a well-formed program, every procedure body is compiled into the graph,
and a #keyw("return") occurs only inside an activation that a call opened.
Source steps keep the second condition true, so the theorem applies at every
step of a run. Induction over the run places one square of @fig:csim-square after another
and so extends the theorem to finite source executions (#isathm("csim_star")), as in
CompCert's simulation diagrams @leroy09[§4.3]. Every finite source
execution of a well-formed program is therefore matched by a graph execution
from the entry that holds the same store at corresponding nodes. This matching
gives the first inclusion of the soundness chain of @fig:intro-nest.

=== Source configurations at graph nodes #thy-badge("Voblint_Compile", "Elaborated_Compilation") <sec:at-node>

The analyzer states its verdicts per graph node. A #verdict("PROVED") check at
node $v$ promises that its condition holds whenever an execution is at $v$. To
prove this, @ch:results must say when a source execution is at $v$. The
simulation does not answer this, because equal commands can occur at
different places. In
`if (b) { x = 1; } else { x = 1; }`, both branches leave the residual `x = 1`,
so the configuration does not show which branch the run took, and the
simulation relates it to both branch nodes. A verdict at the else-branch
node, however, speaks only about runs that took the else-branch, so the node
must come from the run.

The proof therefore works on an _annotated copy_ $E$ of the program, which
labels each command $c$ with the node $"point"(c)$ that the compiler emits for
it; $"erase"(c)$ removes the labels again. For a well-formed program
(#isaconst("wf_compile_input")), $E$ compiles to the same graph as the program
(#isathm("compile_prog_elab_pt")), and every run of the program lifts to a run
of $E$ whose commands erase to the program's commands (#isathm("psteps_lift")).
On $E$, the simulation relates a configuration with command $c$ only to the
node $"point"(c)$ (#isathm("csim_point_compile_prog")).

#definition(name: [Graph nodes of a source configuration], isa: "at_node", cmd: "fun")[
  Let $E$ be the annotated copy of a program $p$ and $s_0$ an initial store. A
  source configuration $(r,s,F)$ of $p$ is _observed_ at node $v$, written
  $p, s_0 tack.r (r,s,F) gt.closed v$, if some annotated command $c$ and graph
  stack $K$ satisfy
  $
    "erase"(c) = r, quad "point"(c) = v, \
    (#isaconst("main_body") thin E, s_0, []) ->_p^* (c,s,F) "in" E, quad
    (c,s,F) approx (v,s,K).
  $
]

#figure(
  {
    set text(size: 11pt)
    diagram(
      spacing: (22mm, 16mm),
      node((0, 0), $(#isaconst("main_body") thin E, s_0, [])$, name: <init>),
      node((1, 0), $(c,s,F)$, name: <c>),
      node((2, 0), $(v,s,K)$, name: <v>),
      node((1, 1), $(r,s,F)$, name: <r>),
      edge(<init>, <c>, "-|>", [#isaconst("pstep")#super[\*] in $E$]),
      edge(<c>, <v>, "-", $approx$),
      edge(<c>, <r>, "-|>", $"erase"$, label-side: right),
      edge(<r>, <v>, "-|>", $gt.closed$, label-side: right, stroke: (dash: "dashed")),
    )
  },
  kind: image,
  caption: [Observing a source configuration at a node (#isaconst("at_node")):
    a run of the annotated copy $E$ reaches a configuration that erases to
    $(r,s,F)$ and that the simulation relates to the node $v = "point"(c)$.],
) <fig:at-node>

In the example above, let $v_1$ and $v_2$ be the nodes of `x = 1` in the
then- and the else-branch (@fig:at-node). If $s_0 (b) != 0$, the run of $E$
from $s_0$ reaches `x = 1` labeled $v_1$, so
$p, s_0 tack.r (#raw("x = 1"), s_0, []) gt.closed v_1$ holds and the
configuration is not observed at $v_2$. If $s_0 (b) = 0$, it is observed at
$v_2$ only. Two runs from $s_0$ that reach one configuration through different
occurrences observe it at both nodes. @ch:results states the end-to-end theorem
for each node at which a reached configuration is observed, and shows that one
exists.

== Comparison of VIMP with C <sec:vimp-vs-c>

Every source-level guarantee in this thesis is stated over the executions of
#isaconst("pstep"). Whether #isaconst("pstep") describes the intended language,
its _adequacy_, therefore lies outside the proof (@ch:intro). This section
argues adequacy by comparing VIMP with C11 @iso-c11 (committee draft N1570).
The comparison is not
complete.

VIMP covers a small fragment of C (@fig:vimp-island), and the constructs it
keeps behave as they do in C. Comparisons and logical operators yield $0$ or
$1$ (#c11("6.5.8p6"), #c11("6.5.9p3"), #c11("6.5.3.3p5"), #c11("6.5.13p3"),
#c11("6.5.14p3")), and conditions hold when nonzero (#c11("6.8.4.1p2"),
#c11("6.8.5p4")). Assignment, loops, and procedures with value parameters,
results, and recursion follow C as well, as detailed below. It omits machine
integers, pointers and the heap, arrays and structs, and indirect calls. It
also lacks threads, floating point, `goto`, `break`, `continue`, and exceptions
(@ch:conclusion discusses the heap).

#figure(
  image("/shared/generated/svg/island.svg", width: 75%),
  kind: image,
  placement: none,
  caption: [Constructs of Goblint's C input that VIMP represents, after the
    project website's explainer. Dashed regions are omitted; sizes and positions
    are schematic.],
) <fig:vimp-island>

#figure(
  {
    set text(size: 9pt)
    table(
      columns: (auto, auto, 1fr),
      align: (left, left, left),
      stroke: none,
      inset: (x: 3.5pt, y: 2.2pt),
      table.hline(),
      [], [*VIMP*], [*C11*],
      table.hline(stroke: 0.5pt),
      [integers], [unbounded],
      [signed overflow undefined (#c11("6.5p5"))],
      [], [], [unsigned arithmetic wraps (#c11("6.2.5p9"))],
      [`a / 0`, `a % 0`], [$0$ and $a$], [undefined (#c11("6.5.5p5"))],
      [`/`, `%`, $b != 0$], [truncated; $(a "/" b) dot b + a % b = a$],
      [the same where $a "/" b$ is representable (#c11("6.5.5p6"))],
      [`&&`, `||`], [both operands evaluated],
      [second operand only if needed (#c11("6.5.13p4"), #c11("6.5.14p4"))],
      [initial values], [globals $0$, `main`'s locals arbitrary],
      [uninitialized: static $0$, automatic indeterminate (#c11("6.7.9p10"))],
      [callee locals],
      [$0$ on every entry],
      [uninitialized automatic: indeterminate (#c11("6.7.9p10"))],
      [checks], [never stop the execution, never refine],
      [`assert` aborts on $0$ unless `NDEBUG` (#c11("7.2p1"), #c11("7.2.1.1"))],
      [`min`, `max`], [library calls (#isaconst("special_table"))], [no counterpart],
      [`main`], [no explicit `return`], [`return` gives the exit status (#c11("5.1.2.2.3"))],
      table.hline(),
    )
  },
  placement: none,
  caption: [Constructs that both languages have but model differently. The VIMP
    rows restate #isaconst("c_div"), #isaconst("c_mod"), #isaconst("aval"),
    #isaconst("cinit_stores"), #isaconst("enter_state") and #isaconst("pstep").],
) <tab:vimp-vs-c>

In each row of @tab:vimp-vs-c, a statement true of a VIMP program may fail for the
corresponding C program. Unbounded integers and defined division by zero
can flip a verdict. After `z = 5 / 0;` the check `z == 0` holds in VIMP, so a
#verdict("PROVED") verdict on a program that divides by zero says nothing about C.

Every source-level theorem assumes an initial store from
#isaconst("cinit_stores"). Globals start at $0$, as C's static objects do, and
the locals of `main` are arbitrary. C leaves automatic objects indeterminate,
and some reads of them are undefined (#c11("6.3.2.1p2")); VIMP does not model
this. Callee locals start at $0$ (#isaconst("enter_state")).

Calls and storage follow C closely. A VIMP call evaluates its arguments in the
caller's
store and assigns each value to the corresponding parameter, as in C
(#c11("6.5.2.2p4")). C requires the number of arguments to match the number of
parameters when a prototype is visible (#c11("6.5.2.2p2")), and the source
contract of @sec:vimp requires the same of every call. Both languages permit
recursion (#c11("6.5.2.2p11")). In C, each recursive activation has its own
instance of every automatic object (#c11("6.2.4p6")). In VIMP, the frame saves
the caller's locals and the callee starts with its own, so no activation can
change the locals of another. Globals correspond to C's objects of static
storage duration, which keep their stored value for the entire execution
(#c11("6.2.4p3")). A callee therefore reads the globals its caller wrote, and
after the return the caller reads the globals the callee wrote.

In C, reaching the closing brace of a function whose value the caller uses is
undefined (#c11("6.9.1p12")). The source contract rejects such programs,
since a call that stores a result must name a value-providing callee. A
#keyw("return") with a value hands that value to the caller, as in C
(#c11("6.8.6.4p3")).

VIMP thus keeps integer expressions, structured control flow, and procedures with value
parameters, recursion, and separate locals, and gives them their C meaning. It
departs from C where C leaves the behavior undefined or open. A verdict
therefore says nothing about a C program whose executions overflow, divide by
zero, or read an uninitialized local.

This chapter has fixed the program model. A VIMP program has a source
semantics, compiles to a procedure-aware graph, and every source execution has a
graph execution with the same store, the first inclusion of the soundness chain
in @fig:intro-nest. The remaining chapters reason about the
graph, and @ch:traces begins by structuring its executions for
context-sensitive analyses.
