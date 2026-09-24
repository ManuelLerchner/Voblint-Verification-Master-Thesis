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

The soundness theorem should talk about the programs a user writes. Voblint,
however, does not generate its equations from source configurations. Its
constraint system needs a finite and stable set of control locations. Under
recursion, the residual commands of the small-step semantics do not give such a
set (@sec:why-graph). For this reason Voblint generates its equations from a
procedure-aware control-flow graph (@fig:program-to-equations). If we proved
soundness only for the graph, the compiler would stay outside the theorem, and
a verdict would say nothing about the source program. This chapter defines both
executions and proves the first link of the chain. Every source run of an
accepted program is matched by a graph run that holds the same store. The program of @fig:program-to-equations, in which `main` calls
`bump(5)` and `bump(4)`, is the running example of the thesis.

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
    @ch:equations generates for it.],
) <fig:program-to-equations>

== VIMP, and what it leaves out <sec:vimp>

VIMP (@fig:vimp-island) is kept small because every construct needs a
semantics, compiler clauses and a transfer function proved sound in every
abstract domain. It has unbounded integer variables, locals and globals,
procedures with value parameters, direct calls with an optional result,
recursion, assignment, sequencing, conditionals, `while` loops,
nondeterministic input and checks. It omits machine integers, pointers and the
heap, arrays and structs, indirect calls, threads, floating point, `goto`,
`break`, `continue` and exceptions. Each of these would need its own
preservation argument at every layer (@ch:conclusion discusses the heap).
@sec:vimp-vs-c argues why the fragment is enough for our purpose.

#figure(
  image("/shared/generated/svg/island.svg", width: 75%),
  kind: image,
  placement: none,
  caption: [Constructs represented in VIMP relative to Goblint's C input,
    taken from the explainer page. Dashed regions are constructs that VIMP
    omits. Sizes and positions are schematic. The figure compares only syntax.
    @sec:vimp-vs-c lists where shared constructs have different meanings.],
) <fig:vimp-island>

Two of these omissions matter in later chapters. Without pointers, concrete
memory is a store from variable names to integers. The non-relational analyses
of @ch:domains lift it pointwise to one abstract value per variable.
@sec:relational gives a carrier that is not pointwise. Without `break`,
`continue` and `goto`, every command has at most one normal continuation. So
the compiler of @sec:compile passes down a single continuation, and a
#keyw("return") ignores it.

=== Expressions and commands

Expressions are integer-valued. As in C11, comparisons and logical operators
yield $0$ or $1$ (#c11("6.5.8p6"), #c11("6.5.9p3"), #c11("6.5.3.3p5"), #c11("6.5.13p3"), #c11("6.5.14p3")), and a
condition holds when it is non-zero (#isaconst("truthy"), #c11("6.8.4.1p2"),
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
choice. IMP2 from the AFP @lammich19imp2 instead represents a binary operator
by a HOL function of type #isai("int \<Rightarrow> int \<Rightarrow> int").
Concrete evaluation can apply such a function, but executable code cannot
compare it. Schirmer's Simpl @schirmer08simpl adds nondeterminism and parameter
passing. Its basic commands and conditions are HOL functions and sets of
states, so it has the same problem.

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
It is total because VIMP defines division and remainder by zero
(#isaconst("c_div"), #isaconst("c_mod"), @sec:vimp-vs-c). It also has no
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

In a program, an assignment is written `x = e;` and a check
`__voblint_check(e);`. The parser lowers `true`, `false` and unary minus to the
expression grammar above. The constructor of a check also carries its source
position, which the semantics ignores. A check steps to #skipC whatever value
$e$ has. So it does not stop the run and does not refine the store. An
_activation_ is one execution of a procedure body, from its call to its return.
VIMP has three built-in _library calls_, `__voblint_nondet_int`, `min` and
`max`. A program calls them but does not declare them. The fixed table
#isaconst("special_table") recognizes their names, and
#isaconst("special_result") gives the values they may return. For
`__voblint_nondet_int` this is any integer, and for `min` and `max` it is the
minimum or maximum of the arguments. A library call finishes in one step and
stores its value. Unlike a call of a declared procedure, it therefore enters no
activation and pushes no frame. #ctor("Restore") and #ctor("Unwind") are not
source syntax (#isaconst("source_com") excludes them). @sec:pstep introduces
them for calls and returns. A program (#isatype("imp_prog")) is a list of procedure declarations
(#isaconst("proc_rep")), each with formal parameters and a body, plus a list of
global variables (#isaconst("declared_global_vars")). Its procedure table
(#isatype("proc_table")) looks a name up in that list, and the classifier
#isaconst("declared_global") tests membership in the globals. The entry
procedure is the declaration named `main`, and #isaconst("main_body") is its
body.

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
    `main` body and the one callee declaration (#isaconst("prog_procs")) and
    declares no globals. The playground passes this value to
    #isaconst("run_voblint") and shows it in its _Generated core_ panel. For
    this program the panel is reached via the `VIMP` link of
    @fig:program-to-equations. A #ctor("Call") names its destination and
    callee, and a #ctor("Check") names its source position.],
) <fig:vimp-ast>

The static contract #isaconst("wf_source_program") on a program has several
parts. Every call names either a declared procedure with matching arity or a
library function with suitable arguments and a destination. Formals are
distinct valid locals (#isaconst("valid_formal")). `main` takes no arguments
and contains no #keyw("return"). No declared name is a library name. The
result variable #isaconst("ret_var") is reserved. It is not global
(#isaconst("reserved_ret_var")), and no source expression reads it or
assignment writes it (#isaconst("source_exp")). Finally, a call that stores a
result names a _value-providing_ callee (#isaconst("value_providing")). This
syntactic condition forbids falling through and #keyw("return") without a
value, and it requires a #keyw("return") with a value. So every completed
activation of the callee supplies a value. The callee may still diverge. In
C11, using the value of a call that falls through is undefined
(#c11("6.9.1p12")). Without this condition, such a call would store the $0$
that the reset on entry left in #isaconst("ret_var"). @fig:vimp-ast shows the
program of @fig:program-to-equations in this form. The formal development
starts from this parsed program. The parser lies outside the theorem
(@sec:trust-boundary).

== Executing a source program <sec:pstep>

A small-step semantics over commands has to say where the remaining work of a
caller waits while its callee runs. It also has to say how a #keyw("return")
skips the rest of the callee's body. VIMP keeps the remaining work inside the command and saves
only data on a stack.

#definition(name: [Source configuration], isa: "pstep", cmd: "inductive")[
  A configuration is a triple $(c, s, italic("frs"))$ of the command that
  remains to run, a store $s$, and a list $italic("frs")$ of
  #isatype("frame") values for the suspended activations. Each frame records
  the caller's store and the variable, if any, that receives the result.
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

Whether a variable is global depends only on its name. A classifier
#isai("\<G> :: vname \<Rightarrow> bool"), separate from the store, decides
it. For a program the classifier is #isaconst("declared_global"). The relation
is written
#isai("\<G>, \<Pi> \<turnstile> \<kappa> \<rightarrow>\<^sub>p \<kappa>'") for
configurations $kappa$, $kappa'$ and a procedure table #isai("\<Pi>"). Its
closure is #isai("\<rightarrow>\<^sub>p\<^sup>*"), and @fig:pstep lists its
rules. An assignment updates the store, and a check leaves it unchanged. A
sequence steps its first command until it is #skipC. A conditional selects a
branch by #isaconst("truthy"). A loop unfolds into a conditional. A call continues
with the callee's body followed by the marker #ctor("Restore"), which pops the
frame once the body falls through.
A #keyw("return") becomes #ctor("Unwind"), which discards the commands after
it until it meets the #ctor("Restore") of its call. A frame therefore saves
only a store and a destination. The
#link(
  "https://manuellerchner.github.io/Voblint-Verification-Master-Thesis/index.html#semantics",
)[explainer page]
animates these steps.


A call evaluates the actuals in the caller's store, resets the locals, binds
the formals (#isaconst("enter_state"), #isaconst("bind_formals")) and pushes a
frame. A `return e` writes the value of $e$ to #isaconst("ret_var").
Both pops merge the caller's locals, the callee's globals and the result. The
running activation has one store, so entering a callee and merging its result
back are pointwise selections by name. Formal binding, the environment merge
and the write of the result are polymorphic in the value type
(#isaconst("enter_binding"), #isaconst("combine_env"),
#isaconst("combine_assign")). Therefore the analyses of
@ch:analysis-interface reuse the concrete definitions at their abstract value
types, with $top$ in place of the reset value $0$.

The root activation has no #ctor("Restore"), and a bare #ctor("Unwind") has no
step (#isathm("pstep_Unwind_stuck")). For this reason the contract rejects
#keyw("return") in `main` (#isaconst("no_return")). The simulation of
@sec:csim carries a runtime form of this condition, #isaconst("return_safe").

A source run starts from the configuration $(#isaconst("main_body") thin Pi,
  s_0, [])$, with an initial store $s_0$ in #isaconst("cinit_stores") (@sec:vimp-vs-c).

=== Adequacy of the source semantics <sec:vimp-vs-c>

#isaconst("pstep") is the reference semantics of VIMP. We interpret every
source-level guarantee in this thesis against the executions that it
generates. These guarantees therefore cannot show that #isaconst("pstep")
describes the intended language. This can only be argued.

*Where shared constructs diverge.* A statement that is true of a VIMP program
need not hold for the corresponding C program. @tab:vimp-vs-c compares VIMP
with C11 @iso-c11 and cites clauses of the committee draft N1570.

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
      [checks], [never stop the run],
      [`assert` aborts on $0$ unless `NDEBUG` (#c11("7.2p1"), #c11("7.2.1.1"))],
      [`main`], [no explicit `return`], [`return` gives the exit status (#c11("5.1.2.2.3"))],
      table.hline(),
    )
  },
  placement: none,
  caption: [Constructs that both languages have but model differently. The VIMP
    rows restate #isaconst("c_div"), #isaconst("c_mod"), #isaconst("aval"),
    #isaconst("cinit_stores"), #isaconst("enter_state") and #isaconst("pstep").],
) <tab:vimp-vs-c>


*Division by zero.* Division by zero can flip a verdict, and so can integer
overflow: C11 leaves signed overflow undefined
(#c11("6.5p5")), while the integers of VIMP are unbounded. For division by
zero, VIMP defines what C11 leaves undefined (#c11("6.5.5p5")). After `z = 5 / 0;` the check `z == 0`
holds in VIMP. So a `PROVED` verdict on a program that divides by zero says
nothing about the corresponding C program. A separate arithmetic diagnostic
reports when the analysis cannot exclude a zero divisor; its absence at a
reached node proves the divisor nonzero there
(#isathm("run_voblint_arithmetic_safe"), @sec:verdicts). As expressions are total and effect-free,
evaluating both operands of `&&` gives the short-circuit value; only the
diagnostic differs: it warns about the divisor in `x != 0 && 10 / x > 1` (claim
`and-divisor-warning`). In Goblint's CFG the division lies behind the guard's
`Test` edge: CIL lowers `&&` and `||` to branches unless `useLogicalOperators`
is set, which Goblint does only for witnesses.

*Initial values.* At program entry the globals are $0$, as C11 initializes
static objects, and the locals of `main` are arbitrary mathematical integers
(#isaconst("cinit_stores")). We do not model the indeterminate values of C11,
some reads of which are undefined (#c11("6.3.2.1p2")). Every source-level theorem assumes an initial store from
this set. The locals of a callee start at $0$ on every entry
(#isaconst("enter_state")), a value C11 does not fix. No shipped analysis uses
it. The abstract
entry resets locals to $top$ (#isaconst("enter_binding")), so a check `y == 0`
on an unassigned callee local `y` is
#raw(check-row("callee-uninit-local", cond: "y == 0").verdict). An analysis
that proved it would still be sound for VIMP, but the claim would not follow
for C.

*Checks do not prune executions.* A failing check does not end the run. So
VIMP continues executions that an aborting `assert` would stop, and the verdict
for one check does not depend on an earlier one. Goblint's `__goblint_check`
behaves the same way. Its library table classifies it as checked and not used
for refinement
(#link("https://github.com/goblint/analyzer/blob/5320a6b741e50dc049f7a1b85e1709e9565cc54a/src/util/library/libraryFunctions.ml")[`libraryFunctions.ml`]).
VIMP has no `assume`; only the guards of `if` and `while` prune executions.
`min` and `max` have no C11 counterpart and are defined by
#isaconst("special_table") alone.

*Well-formed runs do not get stuck.* A stuck configuration would make every later program
point unreachable under #isaconst("pstep"), so `DEAD` verdicts and
reachability-conditional `PROVED` verdicts there would hold vacuously. For a
program satisfying #isaconst("wf_source_program"), every reachable
configuration has either finished, as #skipC with an empty frame stack, or can
step:

#proved("source_progress")

The theorem is about the source alone; its premise mentions no compiled graph.
The contract rules out the structural reasons why a call rule can fail: an
undeclared callee, an arity mismatch, repeated formals, and a library call with
unsuitable arguments or without a destination.
Every classified library call has a result (#isathm("special_result_ex")). The
proof reuses the invariant behind the simulation relation of @sec:csim.

*A fragment of Goblint's input.* Goblint analyzes C after its CIL front end
@necula02 has normalized it. Expressions in CIL have no side effects. A call is
a separate instruction, `Call`, with an optional destination, a callee and its
actuals
(#link("https://github.com/goblint/cil/blob/d97418f2e8d2aa88a36c22397c38ccf4d3ffbcde/src/cil.mli")[`cil.mli`]
at the revision Goblint pins). VIMP makes the same choice. Every edge kind of
Goblint's CFG except inline assembly and in-place declarations has a VIMP
counterpart (@tab:cfg-edges), so calls and returns are represented by
corresponding kinds of CFG edges. The local/global split lives in the call and
return transfers. No translation from C to VIMP is formalized.

*No second semantics.* No external semantics cross-checks #isaconst("pstep");
IMP2 and Simpl would each need a translation and its own adequacy argument
(@ch:related).



== The procedure-aware control-flow graph <sec:graph>

=== Why a graph <sec:why-graph>

An analysis attaches abstract states to program points and transfer functions
to transitions. #isaconst("pstep") offers neither in a usable form. Its only
notion of location is the command that remains to run. Recursion can generate
arbitrarily many residual commands, because each pending call adds another
#ctor("Restore") wrapper. They do not form the finite, fixed set of locations
that Voblint needs. An assignment is also not a transition between stable
program points. Inside a sequence it steps through the rule
#isathm("pstep.Seq2"), which rebuilds the surrounding residual command. So the
same assignment is executed by a different derivation in every context.
Finally, nothing names the entry of a procedure, its result, or the point where
a caller resumes. The schematic control-flow graph of @fig:counting-loop solves
the first two problems. It has finitely many nodes and one transfer per edge.
The procedure-aware graph adds an entry node and a result node per procedure,
and call edges that record their continuations.

A _syntax-directed_ analyzer computes its transfer by recursion over the
command structure @nipkow14[Ch. 13]. Voblint is _constraint-based_, like
Goblint @apinis12. The program becomes unknowns and equations, a call adds
equations to the same system, and a solver that knows nothing about programs
finds a solution. This design requires the compiler, the simulation proof of
this chapter and the coverage layer of @ch:traces. The benefit is that the
argument about programs ends at a certificate, namely a post-solution of the
equations (@sec:certificate). The solver that produces it is a verified
component @tilscher26. We reuse it with two local changes. It was ported to
Isabelle2025, and an unused class assumption was removed
(@sec:trust-boundary). @ch:related returns to the comparison.

=== Nodes and edges <sec:cfg>

#definition(name: [Control-flow graph], isa: "cfg", cmd: "record")[
  A graph $g$ is a record of type #isatype("cfg"):
  #{
    show raw.where(block: true): set text(size: 6.5pt)
    thy("cfg")
  }
  #isaconst("intra") holds the _local edges_ $(u, a, v)$, each labelled by an
  #isatype("edge_action") $a$. #isaconst("calls") holds the _call edges_
  $(u, italic("ca"), ctor("FunctionEntry") thin q, k)$. Such an edge consists
  of the call site $u$, the call information $italic("ca")$, the entry node of
  the callee (by #isaconst("wf_cfg")) and the node $k$ where the caller
  resumes. Nodes (#isatype("cfg_node")) are $ctor("Statement") thin n$,
  $ctor("FunctionEntry") thin p$ or $ctor("FunctionResult") thin p$.
  #isaconst("cfg_entry") is the root node. #isaconst("checks") pairs the node
  of each check with its condition. For a compiled graph it is read off the
  #isaconst("EA_Check") edges.
]

The call information $ctor("CallEdge") thin italic("dst") thin
italic("formals") thin italic("args")$ (#isatype("call_action")) copies the
callee's formals onto the edge, so the graph semantics binds actuals to formals
without looking up the procedure table. Every VIMP call names its callee in
the source, so the compiler fixes each call edge's target and the call graph
is known before the analysis starts. A C call through a function pointer names
no callee, and an analyzer of C has to determine the possible targets during
the analysis. Edge actions are procedure-local
(@tab:cfg-edges). The node kinds match Goblint's
(#link("https://github.com/goblint/analyzer/blob/5320a6b741e50dc049f7a1b85e1709e9565cc54a/src/common/framework/node0.ml")[`node0.ml`]).
Goblint's `Function` node is our $ctor("FunctionResult")$. The correspondence
is only between constructors, which is all that @sec:vimp-vs-c needs. No
translation from Goblint's CFG is formalized.

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
    `__goblint_check` through `Proc`.],
) <tab:cfg-edges>

Local edges and call edges are different relations. No edge action denotes a
call, so a call cannot be taken as a local step. Each trace rule of @ch:traces
reads at most one of the two relations. There is no separate global exit node.
A completed program ends at $ctor("FunctionResult") thin #raw("main")$
(#isaconst("cfg_exit")). A #keyw("return") is an ordinary local edge into
$ctor("FunctionResult") thin p$. Every caller of $p$ shares this one node, so
recursion needs no duplicated nodes. Finally, a call edge carries its
continuation $k$, so nothing has to match a return against a call later. By
construction, no edge leaves $ctor("FunctionResult") thin p$ in a compiled
graph. @fig:cfgmap shows each of these properties.

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
  caption: [A recursive program and its compiled graph, labelled as
    `voblint --dot` prints it. Here $sans("pp") thin n$ is
    $ctor("Statement") thin n$, and $sans("entry")_p$, $sans("exit")_p$ are
    $ctor("FunctionEntry") thin p$, $ctor("FunctionResult") thin p$. As in
    @fig:program-to-equations, solid grey arrows are #isaconst("intra") edges,
    and dashed purple arrows are #isaconst("calls") tuples. Dotted connectors
    and thin blue arrows are not edges. Dotted connectors show the continuation
    of a call tuple. Thin blue arrows show where execution continues after a
    result node. Each procedure has one copy of its nodes, whatever the
    recursion depth. Reserved node numbers without edges,
    such as $sans("pp") thin 4$, are not nodes of the graph.],
) <fig:cfgmap>

== Compilation <sec:compilation>

=== Compiling a command <sec:compile>

The compiler (#isaconst("compile") for commands, #isaconst("compile_proc")
and #isaconst("compile_prog") for procedures and programs) is
_continuation-passing_. The node that a fragment falls through to is an input.
A straightforward compiler that insists on one normal exit node per fragment
has two problems.
First, it needs either a more complex result type or a synthetic exit for
#keyw("return"). A #keyw("return") has no exit, and no execution reaches such
a synthetic exit. Second, it joins sequenced fragments by no-op edges between
two nodes that denote the same program point. With the continuation as input,
a node is a program point between two transfers, as in Goblint's CFG. There is
no join node after a conditional, because both branches are compiled against
the same continuation. A loop compiles its body against the loop head. The
compiled counting loop of @fig:counting-loop therefore has no node $t$ and no
edge $t -> h$. The continuation of the body is the loop head itself. To pass
the entry of `c2` to `c1` as its continuation, the compiler must know how many
nodes `c1` allocates before compiling it (#isaconst("csize"),
#isathm("compile_next_id")). @fig:compile-clauses shows these clauses. A
#skipC branch adds no node to the graph. Its guard edge leads directly to $k$.

A call to a declared procedure emits only a #isaconst("calls") tuple, never a
local edge. A #keyw("return") emits an #isaconst("EA_Ret") edge to its
procedure's result node and ignores the continuation. A procedure body is
compiled against an _epilogue_ node. The #isaconst("EA_Ret") edge of the
epilogue has no value and leads to the result node. In this way every edge into
$ctor("FunctionResult") thin p$ is a return edge. The epilogue is added only
when the body can fall through (#isaconst("falls_through")), as
@fig:compile-proc shows.

Every compiled graph satisfies the structural contract #isaconst("wf_cfg"),
without premises (#isathm("compile_prog_wf")). Call edges enter procedure
entries, no local edge enters one, and a return edge ends at the result node of
its own procedure. The entry of the graph is the $ctor("FunctionEntry")$ node
of `main` (#isathm("cfg_entry_compile_prog")). Its edge sets are finite
(#isathm("compile_prog_finite")). The routing and the executable enumeration
of edges need finite edge sets.

The compiler reads the program as a table $Pi$ and a callee list $italic("ps")$,
the declared procedures other than `main`. The contract
#isaconst("wf_compile_input") $cal(G)$ $Pi$ $italic("ps")$ is
#isaconst("wf_source_program") plus the condition that $italic("ps")$ lists
exactly those procedures, without repetition. #isaconst("run_voblint") analyzes
a program only after a sufficient executable form of this contract holds
(#isaconst("wf_program_compile_input_exec")). The source-level theorems
therefore discharge the contract from the analyzer's own answer.

#figure(
  {
    show raw.where(block: true): set text(size: 5.8pt)
    thy("compile_proc")
  },
  kind: image,
  placement: none,
  caption: [The declaration of #isaconst("compile_proc"), lifted from the theory.],
) <fig:compile-proc>

#figure(
  {
    show raw.where(block: true): set text(size: 7.8pt)
    set align(left)
    stated("compile.simps(4)")
    stated("compile.simps(5)")
    stated("compile.simps(6)")
    stated("compile.simps(8)")
  },
  kind: image,
  placement: none,
  caption: [The #isaconst("compile") equations for sequence, conditional, loop
    and return, as the built session states them. Each returns the next free
    node number, the fragment's entry node, its #isaconst("intra") edges and its
    #isaconst("calls") tuples.],
) <fig:compile-clauses>

=== Graph execution <sec:cstep>

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
frame, and a result node pops the top frame. The entry and exit transfers are
the same operations that the source semantics uses (@fig:pstep).
#isaconst("call_enter") binds the formals in #isaconst("enter_state") of the
caller's store, and #isaconst("combine_collect") applies
#isaconst("combine_assign") to #isaconst("combine_env"). For this reason both
executions can hold the same store. #isaconst("cstep"), the trace semantics and
the coverage contract of @ch:traces are defined for an arbitrary graph.
Properties of the compiler are used only where the analyzer is applied to
compiled programs.

== Relating the two executions <sec:csim>

So far #isaconst("pstep") and #isaconst("cstep") are two separate
definitions. One describes source programs, the other arbitrary graphs.
Nothing yet says that a compiled graph behaves like its program. The soundness
theorem is stated over #isaconst("pstep"), but the analysis solves equations
generated from the graph. So the chain needs a link between the two. Every
source run must be matched by a run of the compiled graph that holds the same
store at corresponding points. We prove this with a _forward simulation_, a
relation between source and graph configurations that every source step
preserves.

Two differences make the relation nontrivial. The source keeps the remaining
work of a suspended caller inside the running command, behind a
#ctor("Restore") marker. The graph keeps it on the frame stack as the
continuation node $k$. The two also step at different places. Unfolding a loop
into a conditional, discarding a finished #skipC, and propagating
#ctor("Unwind") past the commands it skips have no graph counterpart. So the
graph answers one source step with zero or more steps. We prove only this
direction. Soundness needs no converse, because a graph run without a source
counterpart can only make the analysis less precise.

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
predicates. #isaconst("control_at") $Pi$ $p$ $c_0$ $k$ $n$ $r$ $v$ says that the
residual $r$ of the body $c_0$, compiled at offset $n$ with continuation node
$k$, is at node $v$. #isaconst("compiled_at") $Pi$ $g$ $p$ $c_0$ $k$ $n$ says
that $c_0$ is the body of procedure $p$ and that its compilation at that offset
lies in $g$, together with its epilogue edge when the body can fall through.
The rules differ in the stacks. $sans("Base")$ relates a single
activation with both stacks empty. $sans("Nested")$ adds one suspended caller
beneath both stacks. On the source side the caller is the wrapper
#ctor("Restore") around the running command, followed by the caller's pending
commands $italic("afters")$, which #isaconst("seq_after") sequences after it. On
the graph side the caller is a frame. The remaining work of the caller,
#isaconst("seq_after") #skipC $italic("afters")$, is located at the
continuation node $italic("cont")$ of this frame. $sans("Returning")$ covers
the moment after a callee finishes. The graph has reached
$ctor("FunctionResult") thin p$, while the source still holds the
#ctor("Restore") of the activation, possibly behind an #ctor("Unwind") that is
propagating towards it (#isaconst("pop_ready")).

The relation is not functional. It only asks that the command belongs to some
compiled body. So a second, uncalled copy of a body gives a second related
node. @sec:source-bridge pairs the relation with a trace that starts at the
entry, so the chosen witness node is reachable.

#theorem(name: [One step is matched], isa: "csim_step")[
  If a source configuration and a graph configuration are related by
  #isaconst("csim") and the source takes one step, the graph takes zero or more
  steps to a configuration related to the new source configuration.
]

#proved("csim_step")

The theorem has two premises beyond the related pair and the source step.
#isaconst("procs_embedded") $Pi$ $g$ says that every declared body is source
syntax under a non-library name and is part of $g$ with its entry and epilogue
edges. #isaconst("return_safe") $c$ says that the running command returns only
inside an activation that a call opened.

The proof is a forward simulation in the style of CompCert @leroy09[§4.3],
with zero or more graph steps per source step. Only finite runs are simulated,
so no measure has to rule out infinite stuttering. #isaconst("control_at")
locates the running residual at a node. A source step corresponds to the edge
that the compiler emits for the next base command of the residual. By induction
on the run, #isathm("csim_star") extends the theorem to finite source runs. For
a program satisfying #isaconst("wf_compile_input"),
#isathm("procs_embedded_compile_prog") discharges the first premise.
#isathm("wf_compile_input_return_safe") derives the second premise for the body
of `main` from #isaconst("no_return"). Every source step preserves this premise
(#isathm("return_safe_pstep")).

A run starts in a related pair. #isathm("compile_prog_main_base") provides the
#isaconst("EA_Body") edge from $ctor("FunctionEntry") thin #raw("main")$ to a
node $e$. It relates the initial configuration
$(#isaconst("main_body") thin Pi, s, [])$ to $e$, which is one edge after the
entry of the graph. The simulated graph run of #isathm("csim_star") therefore
starts at $e$. #isathm("source_run_has_ltr") prepends the #isaconst("EA_Body")
step when it turns the graph run into an activation-local trace. This trace
therefore starts at the graph entry (@sec:source-bridge). This is the first
inclusion of the soundness chain. Every finite source run of such a program is
matched by a graph run that holds the same store. Because
#isaconst("run_voblint") returns an analysis result only after its executable
well-formedness check succeeds, the end-to-end theorem needs no separate
#isaconst("wf_compile_input") premise.
