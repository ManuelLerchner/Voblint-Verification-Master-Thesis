#import "@preview/fletcher:0.5.8" as fletcher: diagram, edge, node
#import "@preview/curryst:0.6.0": prooftree, rule
#import "../lib/math.typ": *
#import "../lib/theme.typ": vb
#import "../lib/figures.typ": *
#import "../lib/code.typ": *
#import "../lib/sources.typ": stated
#import "../lib/theorems.typ": corollary, definition, example, lemma, theorem

= Programs, Compilation, and Control-Flow Semantics <ch:program-model>

RQ1 asks for a soundness theorem about the programs a user writes, and the
analysis cannot work on those programs directly: under recursion, a
small-step source semantics has no finite set of program points to which
abstract states could be attached (@sec:why-graph). Voblint therefore
generates its equations from a procedure-aware control-flow graph
(@fig:program-to-equations). Proving soundness for the graph alone would leave
the compiler outside the theorem, and a verdict would then say nothing about
the source program. This chapter defines both executions and proves the first
link of the chain: every source run is matched by a graph run holding the same
store. The program of @fig:program-to-equations, in which `main` calls
`bump(5)` and `bump(4)`, is the running example of the thesis.

// Node names and edge labels are read from registered `--dot` output (claims
// cfg-contexts-dot and cfg-sum-dec-dot), so a drawing fails to build when the
// compiler's output changes. Lines are matched up to the context suffix, which
// numbers the analysis contexts and does not change the graph.
#let _dot-label(line) = (
  line.match(regex("[\\[,]label=\"([^\"\\\\]*)")).captures.at(0)
)
#let _dot-edge-line(snap, claim, src, dst) = {
  let pat = regex("^  " + src + "_ctx[0-9]+ -> " + dst + "_ctx[0-9]+ \\[")
  let line = snap.find(l => l.match(pat) != none)
  assert(line != none, message: claim + " has no edge " + src + " -> " + dst)
  line
}
#let _dot-node-line(snap, claim, id) = {
  let pat = regex("^    " + id + "_ctx[0-9]+ \\[")
  let line = snap.find(l => l.match(pat) != none)
  assert(line != none, message: claim + " has no node " + id)
  line
}
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
        spacing: (7mm, 6.4mm),
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
  placement: auto,
  caption: [The running example and its procedure-aware graph, with node and
    edge labels as `voblint --dot` prints them. Solid arrows are local edges,
    dashed arrows call edges, and dotted arrows join a call site to the node at
    which the caller resumes. @fig:eq-unknowns shows the unknowns
    @ch:equations generates for it.],
) <fig:program-to-equations>

== VIMP, and what it leaves out <sec:vimp>

VIMP is deliberately small. Every construct needs a semantics, compiler clauses
and a transfer function proved sound in every abstract domain. VIMP has integer
variables over the mathematical integers, a split between locals and globals,
procedures with value parameters, direct calls with an optional result,
recursion to any depth, assignment, sequencing, conditionals, `while` loops,
nondeterministic input and assertion checks. It omits machine integers,
pointers and the heap, arrays and structs, indirect calls, threads, floating
point, `goto`, `break` and `continue`, dynamic allocation and exceptions. Each
omitted construct would change the concrete states or the control effects and
would need its own preservation argument at every layer; @ch:conclusion takes
the heap as the example, and @sec:vimp-vs-c argues that this fragment is the
right one.

Three absences shape later chapters. No theorem here covers wrapping
arithmetic. Without pointers, the abstract states of @ch:domains hold one
value per variable. Without `break`, `continue` and `goto`, every command has
one normal continuation, the only one the compiler of @sec:compile passes
down.

=== Expressions and commands

Expressions are integer-valued. As in C11, comparisons and logical operators
yield $0$ or $1$ (§6.5.8p6, §6.5.9p3, §6.5.3.3p5, §6.5.13p3, §6.5.14p3), and a
condition holds when it is non-zero (§6.8.4.1p2, §6.8.5p4).

#definition(name: [Expressions], isa: "exp")[
  $
    e ::= & n | x | e #vop("+") e | e #vop("−") e | e #vop("*") e | e #vop("/") e
            | e #vop("%") e \
        | & e #vop("<") e | e #vop("<=") e | e #vop(">") e | e #vop(">=") e
            | e #vop("!=") e | e #vop("==") e \
        | & #vop("!", unary: true) e | e #vop("&&") e | e #vop("||") e
  $
]

Each operator is a constructor of its own, because an abstract domain chooses
its transformer by the operator and the executable analyzer has to make that
choice. The AFP's IMP2 @lammich19imp2 instead represents a binary operator by a
HOL function of type #isai("int \<Rightarrow> int \<Rightarrow> int"), which
concrete evaluation can apply but executable code cannot compare. Schirmer's
Simpl @schirmer08simpl has what IMP2 lacks (recursive procedures, local and
global variables, nondeterminism), but its basic commands and conditions are
HOL functions and sets of states, so it has the same obstacle. The parser
lowers `true`, `false` and unary minus to these productions. Evaluation,
#isai("\<lbrakk>e\<rbrakk>\<^sub>e s"), is total, because VIMP defines division
and remainder by zero (@sec:vimp-vs-c), and has no effects, so a transfer
function may re-evaluate a guard, as the backward filtering of @ch:domains
does. Input enters only through the statement `x = __voblint_nondet_int();`.
This keeps #isaconst("aval") a function and limits the nondeterminism of
#isaconst("pstep") to the rule for library calls.

#definition(name: [Commands], isa: "com")[
  $
    c ::= & #skipC | x := e | #keyw("check") (e) | c";" c
            | #keyw("if") (e) {c} #keyw("else") {c} | #keyw("while") (e) {c} \
        | & [x :=] thin p(e, ..., e) | #keyw("return") e? | #ctor("Restore") | #ctor("Unwind")
  $
]

A program writes an assignment as `x = e;` and a check as
`__voblint_check(e);`. A check steps to #skipC whatever $e$ evaluates to, so
it neither stops the run nor refines the store. Besides `__voblint_nondet_int`,
the library calls are `min` and `max`; they come from a closed table
(#isaconst("special_table")) and enter no activation. #ctor("Restore") and
#ctor("Unwind") are not source syntax (#isaconst("source_com") excludes them);
@sec:pstep introduces them for calls and returns. A program is a table of
procedures, each with formal parameters and a body, plus a list of global
variables; the entry procedure is the declaration named `main`.

== Executing a source program <sec:pstep>

A small-step semantics over commands has to say where a caller's remaining
work waits while its callee runs, and how a #keyw("return") skips the rest of
the callee's body. VIMP keeps the remaining work inside the command and saves
only data on a stack.

#definition(name: [Source configuration], isa: "pstep")[
  A configuration is a triple $(c, s, italic("frs"))$ of the command that
  remains to run, a store $s$ of type #isatype("store"), a total function
  #isai("vname \<Rightarrow> int"), and a list $italic("frs")$ of
  #isatype("frame") values for the suspended activations. Each frame records
  the caller's store and the variable, if any, that is to receive the result.
]

A call continues with the callee's body followed by the marker
#ctor("Restore"), which pops the frame once the body falls through. A
#keyw("return") becomes #ctor("Unwind"), which discards the commands after it
until it meets the #ctor("Restore") of its call. A frame therefore saves only a
store and a destination, and #isaconst("pstep") remains a structural small-step
relation over a single command. It is written
#isai("\<G>, \<Pi> \<turnstile> cfg \<rightarrow>\<^sub>p cfg'") for a
procedure table #isai("\<Pi>"), with closure
#isai("\<rightarrow>\<^sub>p\<^sup>*"); @fig:pstep shows the rules for calls and
returns.

#figure(
  grid(
    columns: 1,
    row-gutter: 0.9em,
    stated("pstep.Call"),
    stated("pstep.ReturnSome"),
    stated("pstep.RestoreStep"),
    stated("pstep.UnwindAct"),
  ),
  kind: image,
  caption: [The rules of #isaconst("pstep") for calls and returns, as the
    built session prints them. A call evaluates the actuals in the caller's
    store, resets the locals, binds the formals (#isaconst("enter_state"),
    #isaconst("bind_formals")) and pushes a frame. A return writes its value to
    #isaconst("ret_var"). Both pops merge the caller's locals, the callee's
    globals and the result (#isaconst("combine_env"),
    #isaconst("combine_assign")).],
) <fig:pstep>

The running activation has one store. Being global is a property of a name,
given by a classifier #isai("\<G> :: vname \<Rightarrow> bool") separate from the
store. Entering a callee and merging its result back are then pointwise
selections by name. Formal binding, the
environment merge and the write of the result are polymorphic in the value type
(#isaconst("enter_binding"), #isaconst("combine_env"),
#isaconst("combine_assign")), so the analyses of @ch:analysis-interface reuse
the concrete definitions at their abstract value types, with $top$ in place of
the reset value $0$.

The root activation has no #ctor("Restore"), and a bare #ctor("Unwind") has no
step (#isathm("pstep_Unwind_stuck")). VIMP therefore rejects #keyw("return") in
`main` (#isaconst("no_return")); the simulation
of @sec:csim carries the same condition as its premise #isaconst("return_safe").


=== Adequacy of the source semantics <sec:vimp-vs-c>

#isaconst("pstep") is the definition of VIMP. Every theorem in this thesis is
stated over it, so whether it describes the intended language can only be
argued. This section gives that argument.

*A fragment of Goblint's input.* Goblint analyzes C after its CIL front end
has normalized it. CIL's expressions are side-effect free, and a call is an
instruction of its own, `Call of lval option * exp * exp list`, with an
optional destination
(#link("https://github.com/goblint/cil/blob/d97418f2e8d2aa88a36c22397c38ccf4d3ffbcde/src/cil.mli")[`cil.mli`]
at the revision Goblint pins). VIMP makes the same choice, and every edge kind of
Goblint's CFG except inline assembly and in-place declarations has a VIMP
counterpart (@tab:cfg-edges). Parameters, return values, recursion, the split
between locals and globals, and calling contexts, the mechanisms this thesis
verifies, therefore occur in VIMP in the form Goblint analyzes them.

*Where shared constructs diverge.* Matching syntax can hide a divergence. A
statement that is true of a VIMP program need not hold for the C program with
the same text. @tab:vimp-vs-c compares VIMP with C11 @iso-c11, citing clauses of
the committee draft N1570.

#figure(
  {
    table(
      columns: (auto, 1fr, 1.3fr),
      align: (left, left, left),
      stroke: none,
      inset: (x: 7pt, y: 3.5pt),
      table.hline(),
      [], [*VIMP*], [*C11*],
      table.hline(stroke: 0.5pt),
      [integers],
      [mathematical, unbounded],
      [finite range per type (§5.2.4.2.1); signed overflow undefined (§6.5p5);
        unsigned results reduced modulo the type's maximum plus one (§6.2.5p9)],

      [`a / 0`], [defined as $0$], [undefined (§6.5.5p5)],
      [`a % 0`], [defined as $a$], [undefined (§6.5.5p5)],
      [`/`, `%`, $b != 0$],
      [quotient truncated toward zero; $(a "/" b) dot b + a % b = a$],
      [the same, where $a "/" b$ is representable (§6.5.5p6)],

      [`&&`, `||`],
      [both operands evaluated],
      [second operand evaluated only if the first does not decide (§6.5.13p4, §6.5.14p4)],

      [initial values],
      [globals $0$ and `main`'s locals arbitrary at program entry; a callee's
        locals $0$ on every procedure entry],
      [static objects $0$, automatic objects indeterminate (§6.7.9p10)],

      [assertions],
      [a check never stops the run],
      [`assert` aborts when its argument is $0$ (§7.2.1.1)],

      [`main`],
      [may not `return` explicitly],
      [may; the value is the exit status (§5.1.2.2.3)],
      table.hline(),
    )
  },
  placement: auto,
  caption: [Constructs both languages have, modelled differently. The VIMP
    rows restate #isaconst("c_div"), #isaconst("c_mod"), #isaconst("aval"),
    #isaconst("cinit_stores"), #isaconst("enter_state") and the rules of
    #isaconst("pstep").],
) <tab:vimp-vs-c>

Division is the largest divergence. VIMP defines what C11 leaves undefined
(§6.5.5p5): after `z = 5 / 0;` the check `z == 0` holds in VIMP, so a `PROVED`
verdict on a program that divides by zero says nothing about the C program
with the same text. A separate arithmetic diagnostic with its own theorem
(#isathm("run_voblint_arithmetic_safe"), @sec:verdicts) reports such divisors;
only its absence at a point excludes a zero divisor there. Because expressions
are total and effect-free, evaluating both operands of `&&` yields the value
short-circuiting would; the difference shows only in the diagnostic, which
warns about the divisor in `x != 0 && 10 / x > 1` (claim
`and-divisor-warning`). In Goblint's CFG that division lies behind the guard's
`Test` edge, since CIL lowers `&&` and `||` to branches unless its option
`useLogicalOperators` is set, which Goblint does only in its witness code.

Initial values are a second definitional choice. At program entry the globals
are $0$, as C11 initializes static objects, and `main`'s locals are
unconstrained (#isaconst("cinit_stores")), which over-approximates C's
indeterminate values; every source-level theorem assumes an initial store from
this set. A callee's locals start at $0$ on every entry
(#isaconst("enter_state")), which, like the quotient of a division by zero,
fixes a value where C11 fixes none. No shipped analysis uses it: the abstract
entry resets locals to $top$ (#isaconst("enter_binding")), so a check `y == 0`
on an unassigned callee local `y` is
#raw(check-row("callee-uninit-local", cond: "y == 0").verdict). The soundness
theorem, stated over #isaconst("pstep"), would nevertheless accept an analysis
that proved it.

*No hidden executions, no vacuous checks.* A failing check does not end the
run, so VIMP keeps and continues every execution an aborting `assert` would
allow, and the verdict for one check does not depend on an earlier one.
Goblint's `__goblint_check` behaves the same way: its library table classifies
it as checked and not used for refinement
(#link("https://github.com/goblint/analyzer/blob/5320a6b741e50dc049f7a1b85e1709e9565cc54a/src/util/library/libraryFunctions.ml")[`libraryFunctions.ml`]).
VIMP has no `assume`; only the guards of `if` and `while` prune executions. The
library calls `min` and `max` have no C11 counterpart for integers and are
defined by #isaconst("special_table") alone.

A program satisfying the static contract of @sec:compile does not get stuck
before it completes: #isaconst("wf_source_program") excludes each premise
failure of the call rules (an undeclared callee, an arity mismatch, repeated
formals, a library call with unsuitable arguments or without a destination)
and a return from `main`. No progress lemma states this. In any case, a stuck configuration
could only cut off later executions, since the source-level theorems quantify
over every finite run prefix, so no claim about an earlier point becomes
vacuous.

*No second semantics.* No external reference semantics cross-checks
#isaconst("pstep"). Stating the theorem against IMP2 instead would weaken it,
since IMP2's semantics is deterministic and its program logic relates only
terminating runs (@ch:related); Simpl avoids both restrictions but not the
opaque operators above. Regression programs exercise the conventions
of @tab:vimp-vs-c, among them truncating division and remainder for every sign
combination and by zero (@sec:eval-corpus). The components the delivered
analyzer trusts beyond #isaconst("pstep") are listed in @sec:trust-boundary.



== The procedure-aware control-flow graph <sec:graph>

=== Why a graph <sec:why-graph>

#isaconst("pstep") is a poor basis for an analysis, which attaches abstract
states to program points and transfer functions to transitions. Under recursion
the remaining commands that serve as source locations are unbounded, an
assignment's effect is spread across congruence rules, and nothing names a
procedure's entry, its result or a caller's resumption point. A control-flow
graph provides finitely many nodes, one transfer per edge, an entry and a
result node per procedure, and call edges that record their continuations.

The graph is a design decision. A _syntax-directed_ analyzer recurses over the
command structure and iterates loops in place. Voblint is _constraint-based_,
as Goblint is: the program becomes unknowns and equations, a call contributes
equations to the same system, and a solver that knows nothing about programs
finds a solution. The cost is the compiler, the simulation proof of this
chapter and the coverage layer of @ch:traces. In return, the argument about
programs ends at a certificate, a post-solution of the equations
(@sec:certificate), and the solver that produces it is a verified component
reused unchanged @tilscher26. @ch:related
returns to the comparison.

=== Nodes and edges <sec:cfg>

#definition(name: [Control-flow graph], isa: "cfg")[
  A graph $g$ of type #isatype("cfg") consists of
  #set enum(numbering: "(i)")
  + a set #isaconst("intra") of _local edges_ $(u, a, v)$, each labelled by an
    #isatype("edge_action") $a$;
  + a set #isaconst("calls") of _call edges_ $(u, italic("ca"), ctor("FunctionEntry") thin q, k)$,
    naming the call site $u$, the call's information $italic("ca")$, the callee's
    entry node, and the node $k$ at which the caller resumes;
  + an entry node, and a set of checks.

  Nodes are $ctor("Statement") thin n$, $ctor("FunctionEntry") thin p$ or $ctor("FunctionResult") thin p$.
]

The call information $ctor("CallEdge") thin italic("dst") thin
italic("formals") thin italic("args")$ (#isatype("call_action")) copies the
callee's formals onto the edge, so the graph semantics binds actuals to formals
without looking up the procedure table. Edge actions are procedure-local
(@tab:cfg-edges). The node kinds match Goblint's
(#link("https://github.com/goblint/analyzer/blob/5320a6b741e50dc049f7a1b85e1709e9565cc54a/src/common/framework/node0.ml")[`node0.ml`]),
whose `Function` is $ctor("FunctionResult")$. The correspondence is one of
constructors, which is what @sec:vimp-vs-c uses it for; no translation from
Goblint's CFG is formalized.

#figure(
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
    [#isaconst("EA_Nop")], [#skipC], [`Skip`, unused],
    [call edge], [call of a declared procedure], [`Proc`],
    [none], [inline assembly, in-place declaration], [`ASM`, `VDecl`],
    table.hline(),
  ),
  placement: auto,
  caption: [Transitions of the graph and their counterparts among the edges of
    Goblint's CFG at the pinned revision
    (#link("https://github.com/goblint/analyzer/blob/5320a6b741e50dc049f7a1b85e1709e9565cc54a/src/common/framework/edge.ml")[`edge.ml`]).
    All rows but the last two are #isatype("edge_action") constructors on
    #isaconst("intra") edges; Goblint routes library calls and
    `__goblint_check` through `Proc`.],
) <tab:cfg-edges>

Three structural choices matter later. Local edges and call edges are
different relations. No edge action denotes a call, so a call cannot be taken
as a local step, and each trace rule of @ch:traces reads exactly one relation.
There is also no global exit. A #keyw("return") is an ordinary local edge into
$ctor("FunctionResult") thin p$, one node shared by every caller of $p$, so
recursion needs no duplicated nodes. Finally, a call edge carries its
continuation $k$, so nothing has to match a return against a call later, and
no edge leaves $ctor("FunctionResult") thin p$. @fig:cfgmap shows all three.

#let _sum-procs = ```
fun dec(x) {
  return x - 1;
}

fun sum(n) {
  if (n < 1) { return 0; }
  m = dec(n);
  r = sum(m);
  return r + n;
}
```
#let _sum-main = ```
fun main() {
  x = sum(2);
  __voblint_check(x == 3);
}
```
#let _sum-program = _sum-procs.text + "\n\n" + _sum-main.text
#figure(
  stack(
    spacing: 8pt,
    grid(
      columns: (1fr, 1fr),
      column-gutter: 8pt,
      listing(lang: "c", ctx: "entry-state", program: _sum-program, _sum-procs),
      listing(lang: "c", ctx: "entry-state", program: _sum-program, _sum-main),
    ),
    {
      set text(size: 7.5pt, font: "DejaVu Sans Mono")
      let dot = read("/shared/generated/cfg-sum-dec-dot.txt").split("\n")
      let edge-line(a, b) = _dot-edge-line(dot, "cfg-sum-dec-dot", a, b)
      let n(pos, id, boundary: false) = node(
        pos,
        _dot-label(_dot-node-line(dot, "cfg-sum-dec-dot", id)),
        stroke: 0.8pt + (if boundary { vb.accent } else { vb.neutral }),
        fill: if boundary { vb.accent.lighten(90%) } else { white },
        corner-radius: if boundary { 2pt } else { 6pt },
        inset: 3.5pt,
        name: label(id),
      )
      let lab(body, fill: vb.neutral) = text(size: 7pt, fill: fill, body)
      let intra(a, b, ..args) = edge(
        label(a),
        label(b),
        "-|>",
        stroke: 0.7pt + vb.neutral,
        label: lab(_dot-label(edge-line(a, b))),
        label-sep: 2pt,
        ..args,
      )
      let call(a, b, via: (), ..args) = edge(
        label(a),
        ..via,
        label(b),
        "-|>",
        stroke: 0.9pt + vb.called,
        label: lab(_dot-label(edge-line(a, b)), fill: vb.called),
        label-sep: 2pt,
        ..args,
      )
      let cont(a, b, ..args) = {
        assert(edge-line(a, b).contains("label=\"continuation\""))
        edge(
          label(a),
          label(b),
          stroke: (paint: vb.called, thickness: 0.8pt, dash: "dotted"),
          ..args,
        )
      }
      let resume(a, b, via: (), ..args) = {
        assert(edge-line(a, b).contains("xlabel=\"resume"))
        edge(
          label(a),
          ..via,
          label(b),
          "-|>",
          stroke: (paint: vb.accent, thickness: 0.8pt, dash: "dashed"),
          ..args,
        )
      }
      let head(pos, name) = node(pos, text(weight: "bold", fill: vb.muted, name), stroke: none)
      diagram(
        spacing: (13mm, 7.5mm),
        head((0, -0.7), "main"),
        head((2.5, -0.7), "sum"),
        head((6, 1.3), "dec"),
        n((0, 0), "main_entry_main", boundary: true),
        n((0, 1), "main_pp9"),
        n((0, 3), "main_pp10"),
        n((0, 4), "main_pp11"),
        n((0, 5), "main_exit_main", boundary: true),
        n((2.5, 0), "sum_entry_sum", boundary: true),
        n((2.5, 1), "sum_pp2"),
        n((1.8, 2), "sum_pp3"),
        n((3.2, 2), "sum_pp5"),
        n((3.2, 3), "sum_pp6"),
        n((3.2, 4), "sum_pp7"),
        n((2.5, 5), "sum_exit_sum", boundary: true),
        n((6, 2), "dec_entry_dec", boundary: true),
        n((6, 3), "dec_pp0"),
        n((6, 4), "dec_exit_dec", boundary: true),
        intra("main_entry_main", "main_pp9", label-side: right),
        cont("main_pp9", "main_pp10"),
        intra("main_pp10", "main_pp11", label-side: left),
        intra("main_pp11", "main_exit_main", label-side: left),
        intra("sum_entry_sum", "sum_pp2", label-side: left),
        intra("sum_pp2", "sum_pp3", label-side: right),
        intra("sum_pp2", "sum_pp5", label-side: left),
        intra("sum_pp3", "sum_exit_sum", label-side: right),
        cont("sum_pp5", "sum_pp6"),
        cont("sum_pp6", "sum_pp7"),
        intra("sum_pp7", "sum_exit_sum", label-side: left, label-pos: 0.6),
        intra("dec_entry_dec", "dec_pp0", label-side: left),
        intra("dec_pp0", "dec_exit_dec", label-side: left),
        call(
          "main_pp9",
          "sum_entry_sum",
          label-side: left,
          label-pos: 0.45,
          label-sep: 3pt,
          bend: 12deg,
        ),
        call("sum_pp5", "dec_entry_dec", label-side: right, label-pos: 0.62),
        call(
          "sum_pp6",
          "sum_entry_sum",
          via: ((4.2, 3), (4.2, 0)),
          corner-radius: 4pt,
          label-pos: 0.5,
          label-side: right,
        ),
        resume(
          "sum_exit_sum",
          "main_pp10",
          via: ((2.5, 5.8), (1.2, 5.8), (1.2, 3)),
          corner-radius: 4pt,
        ),
        resume("sum_exit_sum", "sum_pp7", bend: 50deg),
        resume("dec_exit_dec", "sum_pp6", bend: 25deg),
      )
    },
  ),
  kind: image,
  placement: auto,
  caption: [A recursive program and its compiled graph, labelled as
    `voblint --dot` prints it: $sans("pp")n$ is $ctor("Statement") thin n$, and
    $sans("entry")_p$, $sans("exit")_p$ are $ctor("FunctionEntry") thin p$,
    $ctor("FunctionResult") thin p$. Grey arrows are #isaconst("intra") edges,
    purple arrows #isaconst("calls") tuples, and a dotted line joins a call
    site to its continuation. Dashed blue arrows are not edges: they show where
    execution continues after a result node. Each procedure has one copy of its
    nodes whatever the recursion depth; nodes without edges are not drawn.],
) <fig:cfgmap>

== Compilation <sec:compilation>

=== Compiling a command <sec:compile>

The compiler is _continuation-passing_: the node a fragment falls through to is
an input. A compiler that returns each fragment's exit node as an output has to
invent an exit for #keyw("return"), which has none, and has to join sequenced
fragments by no-op edges between two nodes that denote the same program point;
both leave nodes and edges in the graph that no execution reaches. With the
continuation as input, a node is a program point between two transfers, as in
Goblint's CFG. There is no join node after a conditional, because both branches
compile against the same continuation, and a loop compiles its body against the
loop head (@fig:source-morph). The cost is a node count: to hand `c1`
the entry of `c2` as its continuation, the compiler must know how many nodes
`c1` allocates before compiling it (#isaconst("csize")).

A call to a declared procedure emits only a #isaconst("calls") tuple, never a
local edge. A #keyw("return") emits an #isaconst("EA_Ret") edge to its
procedure's result node and ignores the continuation. A procedure body is
compiled against an _epilogue_ node, whose #isaconst("EA_Ret") edge without a
value leads to the result node, so that every edge into
$ctor("FunctionResult") thin p$ is a return edge; it is added only when the body
can fall through (#isaconst("falls_through")).

#figure(
  grid(
    columns: (1fr, auto),
    column-gutter: 14pt,
    align: horizon,
    listing(lang: "c", ctx: "none", ```
    fun main() {
      i = 0;
      while (i < 5) {
        i = i + 1;
      }
      __voblint_check(i == 5);
    }
    ```),
    // 0.62pt per viewBox unit sets the 11.5-unit edge labels at 7.1pt.
    image("/shared/generated/svg/source-morph.svg", width: 380 * 0.62pt),
  ),
  kind: image,
  placement: auto,
  caption: [A counting loop and its compiled graph. The loop head
    $sans("pp")1$ is the continuation of the body $sans("pp")2$; its false
    guard leads to the check $sans("pp")3$. The epilogue $sans("pp")4$ handles
    fall-through with the #isaconst("EA_Ret") edge labelled `return`.],
) <fig:source-morph>

Every compiled graph satisfies the structural contract #isaconst("wf_cfg")
(#isathm("compile_prog_wf")) without premises: call edges enter procedure
entries, no local edge does, and a return edge lands at its own procedure's
result node. The graph's entry is `main`'s $ctor("FunctionEntry")$ node
(#isathm("cfg_entry_compile_prog")), and the graph is finite
(#isathm("compile_prog_finite")), as every solver instantiation needs.

The simulation of @sec:csim depends on a static contract on the source,
#isaconst("wf_source_program"): every call names a declared procedure with
matching arity, formals are distinct, `main` takes no arguments and contains no
#keyw("return"), and a call that stores a result names a _value-providing_
callee (#isaconst("value_providing")), one whose every path ends in a
#keyw("return") with a value. Without the last condition, a callee that falls
through would hand its caller the $0$ that the entry reset left in
#isaconst("ret_var")\; C11 leaves using the value of such a call undefined
(§6.9.1p12). #isaconst("run_voblint") analyzes a program only after a
sufficient executable form of this contract holds
(#isaconst("wf_program_compile_input_exec")), so the source-level theorems
discharge the premise from the analyzer's own answer.

=== Graph execution <sec:cstep>

#definition(name: [Graph execution], isa: "cstep")[
  A graph configuration is a triple of a node, a store, and a stack of suspended
  callers, each recording where to resume, which variable receives the result,
  and the caller's store. #isaconst("cstep"), written
  #isai("\<G>, g \<turnstile> cfg \<rightarrow>\<^sub>c cfg'") with closure
  #isai("\<rightarrow>\<^sub>c\<^sup>*"), has three rules:
  #set enum(numbering: "(i)")
  + follow a local edge and apply its transfer;
  + follow a call edge: enter the callee and push a frame;
  + at $ctor("FunctionResult") thin p$: pop the top frame and combine.
]

#isaconst("cstep"), the trace semantics and the coverage contract of
@ch:traces are defined for an arbitrary graph; compiler properties enter only
where the analyzer meets compiled programs.

== Relating the two executions <sec:csim>

The source keeps a suspended caller's remaining work inside the running
command, behind a #ctor("Restore") marker; the graph keeps it on the frame
stack, as the continuation node $k$. The two also step at different places.
Unfolding a loop into a conditional, discarding a finished #skipC and
propagating #ctor("Unwind") past the commands it skips have no graph
counterpart, so the graph answers one source step with zero or more steps.

#definition(name: [Simulation relation], isa: "csim")[
  #isaconst("csim"), written
  #isai("\<Pi>, g \<turnstile> (c, s, frs) \<approx> (v, s, stk)"), relates a
  source configuration to a graph configuration _holding the same store_.
  It has three constructors: $sans("Base")$ relates a single activation with
  nothing beneath it; $sans("Nested")$ removes one suspended caller, pairing a
  #ctor("Restore") wrapper in the command against a frame on the stack; and
  $sans("Returning")$ covers the mismatch just after a callee finishes, where the
  graph has already reached $ctor("FunctionResult") thin p$ while the source is still
  propagating #ctor("Restore") or #ctor("Unwind") towards its frame-pop rule.
]

The relation is not functional: it asks only that the command belong to some
compiled body, so a second, uncalled copy of a body yields a second related
node (@sec:source-bridge).

#theorem(name: [One step is matched], isa: "csim_step")[
  Assume #isaconst("procs_embedded") $Pi$ $g$: the body of every declared
  procedure, with its entry and epilogue edges, is part of $g$. Assume
  #isaconst("return_safe") $c$: the running command returns only inside an
  activation that a call opened. If
  #isai("\<Pi>, g \<turnstile> (c, s, frs) \<approx> cfg\<^sub>g") and
  #isai("\<G>, \<Pi> \<turnstile> (c, s, frs) \<rightarrow>\<^sub>p cfg'"), then
  some #isai("cfg\<^sub>g'") satisfies
  #isai("\<G>, g \<turnstile> cfg\<^sub>g \<rightarrow>\<^sub>c\<^sup>* cfg\<^sub>g'") and
  #isai("\<Pi>, g \<turnstile> cfg' \<approx> cfg\<^sub>g'").
]

The proof locates every partly executed command, its _residual_, at the graph
node the compiler emitted for it; a source step then corresponds to the edge
emitted for the residual's next base command. By induction on the run,
#isathm("csim_star") extends the theorem to finite source runs. For a compiled
well-formed program,
#isathm("procs_embedded_compile_prog") discharges the first, and
#isathm("wf_compile_input_return_safe") derives the second for `main`'s body
from #isaconst("no_return")\; every source step preserves it
(#isathm("return_safe_pstep")). Only this forward direction is proved;
soundness needs no converse, because extra graph runs only lose precision.

This is the first inclusion of the chain for RQ1: every finite source run of a
program satisfying #isaconst("wf_source_program") is matched by a graph run
holding the same store (#isathm("csim_star")). Because #isaconst("run_voblint")
checks well-formedness itself, the end-to-end theorem of K1 inherits no premise
from this link. @ch:traces turns that graph run into an activation-local trace
(@sec:source-bridge).
