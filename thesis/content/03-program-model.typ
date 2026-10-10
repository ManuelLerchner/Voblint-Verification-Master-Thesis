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

= Programs and Control-Flow Graphs <ch:program-model>

@ch:background analyzed a single loop through its control-flow graph. The
soundness theorem, however, should talk about the programs a user writes, and
these have procedures and recursion. This chapter defines two views of such a
program and connects them. The source semantics executes a program directly
(@sec:pstep). An analysis cannot generate its equations from it, because its
constraint system needs a fixed, finite set of program points to attach
abstract states to. The source semantics locates execution only by the command
that still has to run, and under recursion these commands can nest arbitrarily
deep, so they form no such set (@sec:why-graph). Voblint
therefore compiles a program to a procedure-aware control-flow graph and
generates its equations from the graph (@fig:program-to-equations). If
soundness were proved only for the graph, the compiler would stay outside the
theorem, and a verdict would say nothing about the source program. This
chapter therefore proves the first link of the soundness chain: every source
run of a well-formed program is matched by a graph run that holds the same
store (@sec:csim). The program of @fig:program-to-equations, in which `main`
calls `bump(5)` and `bump(4)`, is a running example throughout the remaining chapters.

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
    dashed arrows are call edges. Dotted connectors are not edges. They show the
    continuation of a call edge, that is, the node where the caller resumes. @fig:eq-unknowns shows the unknowns
    that @ch:equations generates around the first call.],
) <fig:program-to-equations>

== VIMP, and what it leaves out <sec:vimp>

VIMP (@fig:vimp-island) is the small imperative language with C-like syntax
that the formalization analyzes. It is kept small because every construct needs a
semantics, compiler clauses, and a transfer function proved sound in every
abstract domain. It has unbounded integer variables, locals and globals,
procedures with value parameters, direct calls with an optional result,
recursion, assignment, sequencing, conditionals, `while` loops,
nondeterministic input, and checks. It omits machine integers, pointers and the
heap, arrays and structs, indirect calls, threads, floating point, `goto`,
`break`, `continue`, and exceptions. Each of these would need its own
preservation argument at every layer (@ch:conclusion discusses the heap).
@sec:vimp-vs-c compares the fragment with C and with Goblint's input.

#figure(
  image("/shared/generated/svg/island.svg", width: 75%),
  kind: image,
  placement: auto,
  caption: [Constructs represented in VIMP relative to Goblint's C input,
    taken from the explainer page. Dashed regions are constructs that VIMP
    omits. Sizes and positions are schematic. The figure compares only syntax.
    @sec:vimp-vs-c lists where shared constructs have different meanings.],
) <fig:vimp-island>

One of these omissions matters in later chapters. Without pointers, concrete
memory is a store from variable names to integers. The non-relational analyses
of @ch:domains lift it pointwise to one abstract value per variable.
@sec:rel-state gives a carrier that is not pointwise.

Expressions are integer-valued. As in C11, comparisons and logical operators
yield $0$ or $1$ (#c11("6.5.8p6"), #c11("6.5.9p3"), #c11("6.5.3.3p5"), #c11("6.5.13p3"), #c11("6.5.14p3")), and a
condition holds when it is nonzero (#isaconst("truthy"), #c11("6.8.4.1p2"),
#c11("6.8.5p4")).

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
transformer by the operator, and the executable analyzer has to make this
choice by inspecting the syntax. The two AFP languages with procedures that we
considered, IMP2 and Simpl, do not allow this. IMP2 @lammich19imp2 represents a binary operator by a HOL
function of type #isai("int \<Rightarrow> int \<Rightarrow> int"). Concrete
evaluation can apply such a function, but executable code cannot compare it
with another one, so it cannot tell `+` from `*`. IMP2 also matches Voblint's
programs poorly in other respects. Its semantics is deterministic, so it has
no input, and its call command takes no arguments and returns no value, so
parameters and results pass through variables set by generated code
(@ch:related). Schirmer's Simpl @schirmer08simpl is more expressive, with
nondeterministic specifications and a derived call command that passes
parameters, but its basic commands and conditions are likewise HOL functions
and sets of states. Both languages target program verification, where semantic objects are
convenient, whereas an analyzer needs syntax that it can inspect. VIMP is therefore defined from scratch, with such a syntax, which code
generation can also export.

An expression is evaluated in a _store_ $s$ of type #isatype("store"), a total
function #isai("vname \<Rightarrow> int") from variable names to integers.
Evaluation #isaconst("aval"), written #isai("\<lbrakk>e\<rbrakk>\<^sub>e s"), is
a function defined by one equation per constructor, for example
$
  sem(n)_e thin s = n, quad
  sem(x)_e thin s = s(x), quad
  sem(e_1 #vop("/") e_2)_e thin s = #isaconst("c_div") (sem(e_1)_e thin s, sem(e_2)_e thin s), \
  sem(e_1 #vop("<") e_2)_e thin s = cases(1 & "if" sem(e_1)_e thin s < sem(e_2)_e thin s, 0 & "otherwise".)
$
Every expression has a value, because VIMP fixes the results of division and
remainder by zero (#isaconst("c_div"), #isaconst("c_mod"), @sec:vimp-vs-c). It also has no
effects, so a transfer function may evaluate a guard again, as the backward
filtering of @ch:domains does. Input enters only through the statement
`x = __voblint_nondet_int();` and never inside an expression. This keeps
#isaconst("aval") a function.

Commands are built from expressions. Besides the structured statements, there
are calls, which may store a result, and two markers that appear only during
execution.

#definition(name: [Commands], isa: "com", cmd: "datatype")[
  $
    c ::= & #skipC | x := e | #keyw("check") (e) | c";" c
            | #keyw("if") (e) {c} #keyw("else") {c} | #keyw("while") (e) {c} \
        | & [x :=] thin p(e, ..., e) | #keyw("return") e? | #ctor("Restore") | #ctor("Unwind")
  $
]

In concrete syntax, an assignment is written `x = e;` and a check
`__voblint_check(e);`. The parser lowers `true`, `false`, and unary minus to the
expression grammar above. A check states a condition for the analyzer to
decide (@sec:verdicts) and does not influence the execution. It behaves like
#skipC whatever value $e$ has, so it neither stops the run nor refines the
store. Its constructor also carries the source position. The semantics ignores it,
and the analyzer's report uses it to name the check.

Calls come in two kinds. A call of a declared procedure starts an
_activation_, one execution of the procedure body from its call to its return.
VIMP also has three built-in _library calls_, `__voblint_nondet_int`, `min`, and `max`, which a program calls but does not declare. The fixed table
#isaconst("special_table") recognizes their names, and
#isaconst("special_result") gives the values they may return: any integer for
`__voblint_nondet_int`, and the minimum or maximum of the arguments for `min`
and `max`. A library call finishes in one step and stores its value, so, unlike a call of a declared procedure, it enters no activation and pushes no frame (@sec:pstep). The
remaining constructors, #ctor("Restore") and #ctor("Unwind"), are not source
syntax (#isaconst("source_com") excludes them). They appear only during
execution, where @sec:pstep uses them for calls and returns.

A program (#isatype("imp_prog")) is a list of procedure declarations
(#isaconst("proc_rep")), each with formal parameters and a body, plus a list of
global variables (#isaconst("declared_global_vars")). Its procedure table
(#isatype("proc_table")) looks up a name in that list, and the classifier
#isaconst("declared_global") tests membership in the globals. The entry
procedure is the declaration named `main`, and #isaconst("main_body") is its
body. @fig:vimp-ast shows the running example in this form. The formal
development starts from this parsed program, and the parser lies outside the
theorem (@sec:trust-boundary).

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
  caption: [The running example as the parser returns it. It consists of the
    `main` body and the one callee declaration (#isaconst("proc_rep")) and
    declares no globals. The playground passes this value to
    #isaconst("run_voblint") and shows it in the panel for the call and answer
    of #isaconst("run_voblint"). For
    this program the panel is reached via the `VIMP` link of
    @fig:program-to-equations. A #ctor("Call", thy: "VIMP_Proc") names its destination and
    callee, and a #ctor("Check") names its source position.],
) <fig:vimp-ast>

Not every parsed program can run meaningfully. The theorems must exclude
programs whose calls cannot step or whose results are undefined, and the
_source contract_ #isaconst("wf_source_program") does this. It requires that

- every call names either a declared procedure with matching arity or a
  library function with suitable arguments and a destination,
- formals are distinct valid locals, and `main` is declared, takes no
  arguments and contains no #keyw("return") (@sec:pstep),
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
that it cannot reach a #keyw("return") without a value, and that it contains a
#keyw("return") with a value. So every path through the callee that completes returns a value,
although the callee may still diverge. C11 makes using the value of a call that
falls through undefined (#c11("6.9.1p12")). Without the condition, VIMP would
silently store the $0$ that the reset on entry left in #isaconst("ret_var").

== Executing a source program #thy-badge("Voblint_VIMP", "VIMP_Proc") <sec:pstep>

An _operational semantics_ defines the meaning of a program by how it
executes. A _small-step_ operational semantics does so one step at a time. A
step relation leads from one configuration to the next, and a run is a
sequence of steps @plotkin04[§3.2]. VIMP's semantics #isaconst("pstep") is of
this kind. We call it the _source semantics_, to distinguish it from the graph
semantics of @sec:cstep, which is also a small-step semantics.

Without calls, a configuration is a pair $(c, s)$ of the command that remains
to run and the store, as in the semantics of IMP by Nipkow and Klein
@nipkow14[§7.3]. An assignment updates the store and leaves #skipC, and a
check leaves the store unchanged. A sequence steps its first command until it
is #skipC, a conditional selects a branch by #isaconst("truthy"), and a loop
unfolds into a conditional that runs the body and then the loop again. After
each step the remaining command describes the remainder of the execution
@plotkin04[§3.2], which we call a _residual_.

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

#figure(
  {
    show raw.where(block: true): set text(size: 6.2pt)
    thy("pstep")
  },
  kind: image,
  placement: none,
  caption: [The declaration of #isaconst("pstep"), lifted from the theory.],
) <fig:pstep>

A classifier #isai("\<G> :: vname \<Rightarrow> bool"), separate from the
store, says which names are global. A call needs this information because it resets only the locals. For a program it is #isaconst("declared_global"). The relation is written
#isai("\<G>, \<Pi> \<turnstile> \<kappa> \<rightarrow>\<^sub>p \<kappa>'") for
configurations $kappa$, $kappa'$, and a procedure table #isai("\<Pi>"). Its
closure is #isai("\<rightarrow>\<^sub>p\<^sup>*"), and @fig:pstep lists its
rules. The
#link(
  "https://manuellerchner.github.io/Voblint-Verification-Master-Thesis/index.html#semantics",
)[explainer page]
animates these steps.

A call evaluates the actuals in the caller's store, resets the locals, binds
the formals (#isaconst("enter_state"), #isaconst("bind_formals")), and pushes a
frame. A `return e` writes the value of $e$ to #isaconst("ret_var"), and
popping the frame merges the caller's locals, the callee's globals, and the
result. These operations select by name and are polymorphic in the value type (#isaconst("enter_binding"),
#isaconst("combine_env"), #isaconst("combine_assign")). Therefore the
non-relational analyses reuse the concrete definitions at their abstract state types, with $top$ in place of the reset
value $0$.

We model the root activation without a #ctor("Restore"), since `main` has no
caller to return to, and a bare #ctor("Unwind") has no step
(#isathm("pstep_Unwind_stuck")). This is why the source contract rejects
#keyw("return") in `main` (#isaconst("no_return")). A source run starts from
the configuration $(#isaconst("main_body") thin Pi, s_0, [])$, with an initial
store $s_0$ in #isaconst("cinit_stores") (@sec:vimp-vs-c).

Just as Nipkow and Klein show that well-typed programs do not get stuck
@nipkow14[§9.1.2], we show that well-formed VIMP programs do not get stuck. A
stuck run would never reach the program points after it, so every claim about
those points would hold vacuously. For a program satisfying
#isaconst("wf_source_program"), every reachable configuration has either
finished, as #skipC with an empty frame stack, or can step:

#proved("source_progress")

The source contract rules out every reason a call could fail to step, and every
library call has a result (#isathm("special_result_ex")).

== Scope and adequacy of the source semantics <sec:vimp-vs-c>

A source-level guarantee means only as much as the semantics it is stated
over. Every source-level guarantee in this thesis is interpreted against the
executions of
#isaconst("pstep"), the reference semantics of VIMP, so the guarantees cannot
show that #isaconst("pstep") describes the intended language. This can only be
argued, and this section collects the argument. @tab:vimp-vs-c compares VIMP
with C11 @iso-c11, citing clauses of the committee draft N1570, wherever both
languages have a construct but model it differently.

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
      [static $0$, automatic indeterminate (#c11("6.7.9p10"))],
      [callee locals], [$0$ on every entry], [indeterminate (#c11("6.7.9p10"))],
      [checks], [never stop the run, never refine],
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

Each row is a place where a statement true of a VIMP program does not necessarily hold for
the corresponding C program. Unbounded integers and defined division by zero
can flip a verdict. After `z = 5 / 0;` the check `z == 0` holds in VIMP, so a
#verdict("PROVED") verdict on a program that divides by zero says nothing about C. The
analyzer therefore reports a possible zero divisor as a separate diagnostic,
and its absence at a reached node proves the divisor nonzero there
(#isathm("run_voblint_arithmetic_safe"), @sec:verdict-meaning). Division and
remainder truncate toward zero as in C11. Goblint once got the remainder wrong,
and issue #link("https://github.com/goblint/analyzer/issues/1156")[1156]
@goblint1156 reports that it claimed `c % 2 == 1` for $c in {-5, -7}$
(@sec:eval-1161). Evaluating both
operands of `&&` is harmless, because expressions are total and have no
effects. It gives the short-circuit value. Only the division diagnostic differs. It warns about the divisor in `x != 0 && 10 / x > 1`.

The initial values that VIMP fixes are ones C leaves open. Every source-level
theorem assumes an initial store from #isaconst("cinit_stores"), with globals
$0$ as for C's static objects and the locals of `main` arbitrary. VIMP does not
model C's indeterminate values, some reads of which are undefined
(#c11("6.3.2.1p2")). Callee locals start at $0$ (#isaconst("enter_state")), but
no shipped analysis relies on this, because every abstract entry describes
callee locals by $top$ (#isaconst("enter_binding") for the non-relational
analyses). A check `y == 0` on an unassigned
callee local `y` is therefore
#raw(check-row("callee-uninit-local", cond: "y == 0").verdict). Checks never
prune executions, so the verdict for one check does not depend on an earlier
one. Goblint's `__goblint_check` behaves the same way, and its library table
classifies it as checked and not used for refinement
(#link("https://github.com/goblint/analyzer/blob/5320a6b741e50dc049f7a1b85e1709e9565cc54a/src/util/library/libraryFunctions.ml")[`libraryFunctions.ml`]).

*A fragment of Goblint's input.* Goblint analyzes C after its CIL front end
@necula02 has normalized it, so that expressions have no side effects and a
call is a separate instruction with an optional destination
(#link("https://github.com/goblint/cil/blob/d97418f2e8d2aa88a36c22397c38ccf4d3ffbcde/src/cil.mli")[`cil.mli`]
at the revision Goblint pins). VIMP makes the same choice, and every edge kind
of Goblint's CFG, except inline assembly and in-place declarations, has a VIMP
counterpart (@tab:cfg-edges). No translation from C to VIMP is formalized.

*No second semantics.* No external semantics cross-checks #isaconst("pstep").
For C, Isabelle offers the C parser of AutoCorres2 @brecknell24autocorres2,
which translates a subset of C into Simpl programs @schirmer08simpl, and Coq
has the Clight semantics of CompCert @leroy09. Relating VIMP to either of
them, or to IMP2 or Simpl directly, would need a translation and its own
adequacy argument. Establishing such a correspondence is left as future
work.

== The procedure-aware control-flow graph <sec:graph>



=== Why a graph <sec:why-graph>

An analysis attaches abstract states to program points and transfer functions
to transitions. #isaconst("pstep") offers neither in a usable form. Its only
notion of location is the command that remains to run. Without recursion, only finitely many distinct residual commands arise,
because a loop may run arbitrarily often, but its unfolding revisits the same
command forms. Recursion is different, because a recursive call can nest
another #ctor("Restore") wrapper at every call depth. Residual commands
therefore do not form the finite, fixed set of locations that Voblint needs. An assignment is also not a transition between fixed program points. Inside a sequence it steps through the rule
#isathm("pstep.Seq2"), which rebuilds the surrounding residual command. So the same assignment is executed by a different derivation inside every surrounding command.
Finally, nothing names the entry of a procedure, its result, or the point where
a caller resumes. The schematic control-flow graph of @fig:counting-loop solves
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
inequalities over unknowns indexed by the graph's nodes and leaves the
solution to a generic solver that knows nothing about programs. The solver
needs no knowledge of calls, because a call contributes right-hand sides and
side effects to the same system (@ch:equations). The choice costs the compiler
and simulation proof of this chapter and the coverage layer of @ch:traces,
which says what the inequalities mean. In return, the argument about programs
ends at a solver-independent certificate, a post-solution on the solved set
(@sec:certificate). Voblint does not
implement the solver itself. It uses the verified top-down solver of Tilscher
et al. @tilscher26, which Voblint includes as a submodule with a few changes
(@sec:upstream-td). @ch:related returns to the comparison.

=== Nodes and edges #thy-badge("Voblint_CFG", "CFG_Def") <sec:cfg>

#definition(name: [Control-flow graph], isa: "cfg", cmd: "record")[
  A graph $g$ is a record of type #isatype("cfg"):
  #{
    show raw.where(block: true): set text(size: 6.5pt)
    thy("cfg")
  }
  #isaconst("intra") holds the _local edges_ $(u, a, v)$, each labeled by an
  #isatype("edge_action") $a$. #isaconst("calls") holds the _call edges_
  $(u, italic("ca"), ctor("FunctionEntry") thin q, k)$. Such an edge consists
  of the call site $u$, the call information $italic("ca")$, the entry node of
  the callee (by #isaconst("wf_cfg")), and the node $k$ where the caller
  resumes. Nodes (#isatype("cfg_node")) are $ctor("Statement") thin n$,
  $ctor("FunctionEntry") thin p$ or $ctor("FunctionResult") thin p$.
  #isaconst("cfg_entry") is the root node. #isaconst("checks") pairs the node
  of each check with its condition. For a compiled graph it is computed from the #isaconst("EA_Check") edges, so it cannot drift from them, and the report
  classifies the same edges (#isaconst("classify_checks")).
]

The call information $ctor("CallEdge") thin italic("dst") thin
italic("formals") thin italic("args")$ (#isatype("call_action")) copies the
callee's formals onto the edge, so the graph semantics binds actuals to formals
without looking up the procedure table. VIMP has no function pointers (@sec:vimp), so
every call names its callee, and the compiler can fix the target of each call
edge. Supporting indirect calls would require discovering call targets during the analysis, which is left for future work.
The node kinds match Goblint's
(#link("https://github.com/goblint/analyzer/blob/5320a6b741e50dc049f7a1b85e1709e9565cc54a/src/common/framework/node0.ml")[`node0.ml`]),
which also has statement and function-entry nodes and calls our
$ctor("FunctionResult")$ node `Function`.

#figure(
  {
    set text(size: 9pt)
    table(
      columns: (auto, 1fr, auto),
      align: (left, left, left),
      stroke: none,
      inset: (x: 7pt, y: 3pt),
      table.hline(),
      [*VIMP*], [*transition*], [*Goblint*],
      table.hline(stroke: 0.5pt),
      [#isaconst("EA_Assign")], [assignment], [`Assign`],
      [#isaconst("EA_Assume")], [guard holds], [`Test`],
      [#isaconst("EA_AssumeNot")], [guard fails], [`Test`],
      [#isaconst("EA_Special")], [`min`, `max`, nondeterministic input], [`Proc`],
      [#isaconst("EA_Check")], [check, identity on the store], [`Proc`],
      [#isaconst("EA_Body")], [leave a procedure entry, identity], [`Entry`],
      [#isaconst("EA_Ret")], [return, writes #isaconst("ret_var")], [`Ret`],
      [#isaconst("EA_Nop")], [#skipC, runtime markers, unusable library calls], [`Skip`],
      [call edge], [call of a declared procedure], [`Proc`],
      [none], [inline assembly, in-place declaration], [`ASM`, `VDecl`],
      table.hline(),
    )
  },
  placement: auto,
  caption: [Transitions of the graph and their counterparts among the edges of
    Goblint's CFG at the pinned revision
    (#link("https://github.com/goblint/analyzer/blob/5320a6b741e50dc049f7a1b85e1709e9565cc54a/src/common/framework/edge.ml")[`edge.ml`]).
    All rows except the last two are #isatype("edge_action") constructors on
    #isaconst("intra") edges. Goblint routes library calls and
    `__goblint_check` through `Proc`. It skips empty statements and uses
    `Skip` only for the self-loop of an empty loop.],
) <tab:cfg-edges>

The graph keeps local edges and call edges apart, in its fields
#isaconst("intra") and #isaconst("calls"), because they execute differently. A
local edge changes the store within one activation, while a call edge starts a
new one. No edge action denotes a call, so a call can never be taken as a
local step, and each rule of the trace semantics in @ch:traces reads at most
one of the two relations.

Returns, in contrast, are ordinary local edges. A #keyw("return") in $p$ leads
to the result node $ctor("FunctionResult") thin p$, which all callers of $p$
share, so recursion needs no copies of nodes. A shared result node cannot know
where to continue, and in a compiled graph no edge leaves it. The call edge
records that place instead, as its continuation $k$. After a return, execution
resumes at the continuation saved in the frame, and an analysis connects the
callee's result to the correct caller through the call edge. The matching
caller is explicit in the graph, so no separate return-to-call matching is
needed. A completed program ends at
$ctor("FunctionResult") thin #raw("main")$ (#isaconst("cfg_exit")), so there
is no separate global exit node. @fig:cfgmap shows these properties on a
recursive program.

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
    `voblint --dot` prints it. Here $sans("pp") thin n$ is
    $ctor("Statement") thin n$, and $sans("entry")_p$, $sans("exit")_p$ are
    $ctor("FunctionEntry") thin p$, $ctor("FunctionResult") thin p$. As in
    @fig:program-to-equations, solid gray arrows are #isaconst("intra") edges,
    and dashed purple arrows are #isaconst("calls") tuples. Dotted connectors
    and thin blue arrows are not edges. Dotted connectors show the continuation
    of a call tuple. Thin blue arrows show where execution continues after a
    result node. Each procedure has one copy of its nodes, whatever the
    recursion depth. Reserved node numbers without edges,
    such as $sans("pp") thin 4$, are not nodes of the graph.],
) <fig:cfgmap>

== Compilation <sec:compilation>

The compiler turns a VIMP program into a procedure-aware graph. Its design
decides which program points exist, and the simulation of @sec:csim relies on
how it lays out the code of each command.

=== Compiling a command #thy-badge("Voblint_Compile", "VIMP_Proc_to_CFG") <sec:compile>

To emit the edges of a command, a compiler has to know where control goes
after it. Compilers commonly pass this target down, so that each statement
receives the label of the code that follows it, the inherited attribute
$S."next"$ of the dragon book @aho06[§6.6.3]. Voblint's compiler works the
same way and is therefore called _continuation-passing_. Besides the command,
it takes the node $k$ at which control continues afterward, and it emits the
command's edges so that they end at $k$ (#isaconst("compile") for commands,
#isaconst("compile_proc") and #isaconst("compile_prog") for procedures and
programs). Schematically, writing $"compile"(c, k)$ for the edges of $c$
against the continuation $k$, and $n$ and $h$ for fresh nodes,
$
  "compile"(c_1";" c_2, k) & = "compile"(c_1, "entry"(c_2)) union "compile"(c_2, k), \
  "compile"(#keyw("if") (e) {c_1} #keyw("else") {c_2}, k) & = {n ->^e "entry"(c_1), n ->^(not e) "entry"(c_2)} \
  & quad union "compile"(c_1, k) union "compile"(c_2, k), \
  "compile"(#keyw("while") (e) {c}, k) & = {h ->^e "entry"(c), h ->^(not e) k} union "compile"(c, h), \
  "compile"(#keyw("return") e, k) & = {n ->^(#keyw("return") e) ctor("FunctionResult") thin p}.
$
The alternative would give every fragment an exit node of its own. Sequencing
two fragments would then need a no-op edge from the exit of the first to the
entry of the second, so a sequence of $m$ commands would produce $m - 1$ such
edges between nodes that denote the same program point. With continuations, a
node is a program point between two transfers, as in Goblint's CFG, and a
#keyw("return") simply ignores its continuation. A conditional needs
no join node, because both branches end at the same $k$. A loop compiles its
body against its own head, so the compiled counting loop of
@fig:counting-loop has no node $t$ and no edge $t -> h$. A #skipC branch adds
no node, and its guard edge leads directly to $k$. To compile $c_1$ against
the entry of $c_2$, the compiler must know how many nodes $c_1$ allocates
(#isaconst("csize"), #isathm("compile_next_id")).

Calls and returns leave the current fragment. A call to a declared procedure
becomes a call edge from the call site to the callee's entry, with $k$ as its
continuation, and adds no local edge. A #keyw("return") becomes an
#isaconst("EA_Ret") edge to the result node of its procedure. A body that can
reach its end without a #keyw("return") needs such an edge as well.
#isaconst("compile_proc") compiles the body against one extra node, from which
a return edge without a value leads to the result node (@fig:compile-proc). It
emits this edge for every body, so in a body that always returns, the extra
node and its edge are dead code. @sec:cert-forward explains why the compiler
keeps them. Every edge into $ctor("FunctionResult") thin p$ is therefore a
return edge.

#figure(
  {
    show raw.where(block: true): set text(size: 5.8pt)
    thy("compile_proc")
  },
  kind: image,
  placement: auto,
  caption: [The declaration of #isaconst("compile_proc"), lifted from the theory.],
) <fig:compile-proc>

These rules give every compiled graph a fixed shape. Call edges always enter a
procedure entry, no local edge enters one, and every return edge ends at the
result node of its own procedure. The structural contract #isaconst("wf_cfg")
collects these properties, and every compiled graph satisfies it without
premises (#isathm("compile_prog_wf")). The graph's entry is
$ctor("FunctionEntry") thin #raw("main")$ (#isathm("cfg_entry_compile_prog")),
and its edge sets are finite (#isathm("compile_prog_finite")). Later chapters
rely on this shape to route calls (@ch:equations) and to enumerate edges in the
executable analyzer.

The compiler reads the program as a table $Pi$ and a list $italic("ps")$ of
the declared procedures other than `main`. Its input contract
#isaconst("wf_compile_input") $cal(G)$ $Pi$ $italic("ps")$ is
#isaconst("wf_source_program") plus the condition that $italic("ps")$ lists
exactly those procedures, without repetition.

=== Graph execution #thy-badge("Voblint_CFG", "CFG_Exec") <sec:cstep>

#block(breakable: false)[
  #definition(name: [Graph execution], isa: "cstep", cmd: "inductive")[
    A graph configuration (#isatype("cconf")) is a triple of a node, a store,
    and a stack of suspended callers (#isatype("cframe")). Each entry records
    where to resume, which variable receives the result, and the caller's store.
    The step relation #isaconst("cstep") is written
    #isai("\<G>, g \<turnstile> \<kappa> \<rightarrow>\<^sub>c \<kappa>'"), and
    #isai("\<rightarrow>\<^sub>c\<^sup>*") is its closure.
  ]

  #figure(
    {
      show raw.where(block: true): set text(size: 6.2pt)
      thy("cstep")
    },
    kind: image,
    placement: none,
    caption: [The declaration of #isaconst("cstep"), lifted from the theory.],
  ) <fig:cstep>
]

@fig:cstep lists the rules, one per kind of step. A local edge applies its
transfer #isaconst("edge_step"), a call edge enters the callee and pushes a
frame, and a result node pops the top frame. In the running example
(@fig:program-to-equations), a run of `main` reaches the call site of
`bump(5)`, takes the call edge to the entry of `bump` with $n = 5$, and pushes a
frame that names the continuation. It then follows the local edges of `bump`
to its result node, where the frame is popped. Execution resumes at the
continuation, and `a` holds $6$. The entry and exit transfers are
built from the same functions that #isaconst("pstep") uses (@fig:pstep).
#isaconst("call_enter") binds the formals in #isaconst("enter_state") of the
caller's store, and #isaconst("combine_collect") applies
#isaconst("combine_assign") to #isaconst("combine_env"). For this reason both
executions can hold the same store. #isaconst("cstep"), the trace semantics and
the coverage contract of @ch:traces are defined for an arbitrary graph, not
only for compiled ones.

== Relating the two executions <sec:csim>

So far #isaconst("pstep") and #isaconst("cstep") are two separate
definitions. One describes source programs, the other arbitrary graphs, and
nothing yet says that a compiled graph behaves like its program. The soundness
theorem is stated over #isaconst("pstep"), but the analysis solves equations
generated from the graph, so every source run must be matched by a run of the
compiled graph that holds the same store at corresponding points. We prove this with a _forward simulation_, a
relation between source and graph configurations that every source step
preserves.

Two differences make the relation nontrivial. The source stores the remaining work of a suspended caller inside the running command, behind a
#ctor("Restore") marker. The graph, in contrast, stores it on the frame stack as the
continuation node $k$. The two also step at different places. Unfolding a loop
into a conditional, discarding a finished #skipC, and propagating
#ctor("Unwind") past the commands it skips have no corresponding graph step. As a result,
the graph answers one source step with zero or more steps. We prove only this
direction, because soundness needs no converse. The analysis is proved to cover every
run of the graph from its entry (@ch:traces), and every source run is matched by such a graph run.

#definition(name: [Simulation relation], isa: "csim", cmd: "inductive")[
  #isaconst("csim"), written
  #isai("\<Pi>, g \<turnstile> (c, s, frs) \<approx> (v, s, stk)"), relates a
  source configuration to a graph configuration holding the same store.
]

#figure(
  {
    show raw.where(block: true): set text(size: 6.2pt)
    thy("csim")
  },
  kind: image,
  placement: none,
  caption: [The declaration of #isaconst("csim"), lifted from the theory.],
) <fig:csim>

@fig:csim lists the three rules. Each rule locates one activation with two
predicates. #isaconst("control_at") $Pi$ $p$ $b$ $k$ $n$ $r$ $v$ says that the
residual $r$ of the body $b$, compiled at offset $n$ with continuation node
$k$, is at node $v$. #isaconst("compiled_at") $Pi$ $g$ $p$ $b$ $k$ $n$ says
that $b$ is the body of procedure $p$ and that its compilation at that offset
lies in $g$.
The rules differ in the stacks. $sans("Base")$ relates a single
activation with both stacks empty. $sans("Nested")$ adds one suspended caller
beneath both stacks. On the source side the caller is the wrapper
#ctor("Restore") around the running command, followed by the caller's pending
commands $italic("afters")$, which #isaconst("seq_after") sequences after it. On
the graph side it is a frame, and the caller's remaining work
#isaconst("seq_after") #skipC $italic("afters")$ lies at the frame's
continuation node $italic("cont")$. $sans("Returning")$ covers
the moment after a callee finishes. The graph has reached
$ctor("FunctionResult") thin p$, while the source still holds the
#ctor("Restore") of the activation, possibly behind an #ctor("Unwind") that is
propagating toward it (#isaconst("pop_ready")).

The relation is not functional. It only asks that the running command belong
to some compiled body, so the same source configuration can be related to
several nodes, for instance to a second, uncalled copy of a body. The simulation therefore yields _some_ related graph node, and the
source-level theorem inherits this and states its conclusions at an
existentially chosen node (@sec:headline). @sec:source-bridge pairs the
relation with a trace that starts at the entry, so the chosen node is
reachable. As future work, an elaboration phase could annotate every statement
with the node the compiler emits for it, which would determine the node and
remove the existential (@sec:outlook-extending).

#theorem(name: [One step is matched], isa: "csim_step")[
  If a source configuration and a graph configuration are related by
  #isaconst("csim") and the source takes one step, the graph takes zero or more
  steps to a configuration related to the new source configuration.
]

#proved("csim_step")

The theorem has two premises beyond the related pair and the source step.
#isaconst("procs_embedded") $Pi$ $g$ says that every declared body is source
syntax under a non-library name and lies in $g$ with its entry edge and, if the body can fall
through, its final return edge. Without it, a source call could enter a body that the graph
does not contain. #isaconst("return_safe") $c$ says that the running command
returns only inside an activation that a call opened. It is the runtime form
of the rule that `main` contains no #keyw("return") (@sec:pstep). Both premises hold for every well-formed program
(#isathm("procs_embedded_compile_prog"),
#isathm("wf_compile_input_return_safe")), and every source step preserves the
second (#isathm("return_safe_pstep")). By induction on the run,
#isathm("csim_star") extends the theorem to finite source runs.

The proof follows CompCert's simulation diagrams @leroy09[§4.3], in which each
source step corresponds to a sequence of graph steps, here possibly empty.

The initial source configuration is related to the node after the
#isaconst("EA_Body") edge of `main` (#isathm("compile_prog_main_base")), and
prepending that edge lets the matching graph run start at the entry. Every finite source run of a well-formed program is therefore
matched by a run of the compiled graph from its entry,
and the two runs reach corresponding nodes with the same store. This is the
first inclusion of the soundness chain of @fig:intro-nest. Every store the
source program can reach at a point is also reached by the graph, so an
analysis that covers all graph runs covers all source runs. The executable
analyzer checks well-formedness before it runs and declines to analyze
programs that violate it (#isaconst("wf_program_compile_input_exec")), so the
end-to-end theorem needs no separate premise for it.

Graph runs suffice for an analysis with one abstract state per node.
A context-sensitive analysis, however, computes separate states for the activations of a
procedure entered in different calling contexts, and for this purpose the runs are too _flat_. A run is one long sequence of steps across all
activations, so it does not group the steps of one activation or link each step to
the store with which its activation started. @ch:traces therefore regroups graph runs into activation
traces, one per procedure activation
(#isathm("source_run_has_activation_trace")), and defines on them the
coverage obligations used to establish soundness.
