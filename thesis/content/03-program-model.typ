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
#import "../lib/claims.typ": claim-ref

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
abstract domain. It has integer variables of C's machine integer types, locals
and globals, procedures with value
parameters, direct calls with an optional result, recursion, assignment,
sequencing, conditionals, `while` loops, nondeterministic input, and checks. It
omits pointers and the heap, arrays and structs, indirect calls, threads, floating point, `goto`,
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
memory is a store from variable identities to integers, each within its kind
(@sec:elaboration). The non-relational analyses
of @ch:domains lift it pointwise to one abstract value per variable.
@sec:rel-state gives a carrier that is not pointwise.

Expressions are integer-valued. As in C11, comparisons and logical operators
yield $0$ or $1$ (#c11("6.5.8p6"), #c11("6.5.9p3"), #c11("6.5.3.3p5"), #c11("6.5.13p3"), #c11("6.5.14p3")), and a
condition holds when it is nonzero (#isaconst("truthy"), #c11("6.8.4.1p2"),
#c11("6.8.5p4")).

#definition(name: [Surface expressions], isa: "src_exp", cmd: "datatype")[
  $
    e ::= & n | x | e #vop("+") e | e #vop("−") e | e #vop("*") e | e #vop("/") e
            | e #vop("%") e \
        | & e #vop("<") e | e #vop("<=") e | e #vop(">") e | e #vop(">=") e
            | e #vop("!=") e | e #vop("==") e \
        | & #vop("!", unary: true) e | e #vop("&&") e | e #vop("||") e | (k) thin e
  $
  Here $k$ is a machine kind (#isatype("ikind"), @sec:elaboration), and
  $(k) thin e$ converts explicitly.
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

Every constructor except sequencing also carries an _annotation_, whose type is
a parameter of #isatype("gcom"), as are the types of variables and expressions.
The commands of a parsed program carry the unit annotation and have type
#isatype("src_com"), over names and the _surface_ expressions above, which
have no evaluation of their own. Elaboration (@sec:elaboration) turns them
into core commands (#isatype("com")) over identities and core expressions, in
which every operation carries the width it computes at. The grammar above omits annotations, which @fig:pstep writes as $i$.

In concrete syntax, an assignment is written `x = e;` and a check
`__voblint_check(e);`. The parser lowers `true`, `false`, and unary minus to the
expression grammar above. A check states a condition for the analyzer to
decide (@sec:verdicts) and does not influence the execution. It behaves like
#skipC whatever value $e$ has, so it neither stops the run nor refines the
store. Its constructor also carries the source position, which only the report
uses, to name the check.

Calls come in two kinds. A call of a declared procedure starts an
_activation_, one execution of the procedure body from its call to its return.
VIMP also has three built-in _library calls_, `__voblint_nondet_int`, `min`, and `max`, which a program calls but does not declare. The fixed table
#isaconst("special_table") recognizes their names, and
#isaconst("special_result") gives the values they may return: any integer for
`__voblint_nondet_int`, and the minimum or maximum of the arguments for `min`
and `max`. A library call finishes in one step and stores its value, converted
to the destination's kind (@sec:elaboration), without an activation or a
frame (@sec:pstep). The
remaining constructors, #ctor("Restore") and #ctor("Unwind"), are not source
syntax (#isaconst("source_com") excludes them). They appear only during
execution, where @sec:pstep uses them for calls and returns.

A program (#isatype("imp_prog")) is a list of procedure declarations
(#isaconst("proc_rep")), each with formal parameters and a body, plus a list of
global variables (#isaconst("declared_global_vars")). Its procedure table
(#isatype("proc_table")) looks up a name in that list, and the classifier
#isaconst("declared_global") tests membership in the globals. The entry
procedure is the declaration named `main`, and #isaconst("main_body") is its
body. @fig:vimp-ast shows the running example in this form. The running
example declares no kinds, so it computes at `i32` (@sec:elaboration).

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

== Machine integers and elaboration #thy-badge("Voblint_VIMP", "Core_Exp") <sec:elaboration>

A VIMP program is written like C. It declares its variables with integer types
and leaves most conversions implicit. Its value, however, depends on the width
at which each operation is computed. In the program below, `x` and `y` are
8-bit unsigned variables.

#listing(lang: "c", claim: "kinds-promotion", ```
fun main() {
  u8 x = 200;
  u8 y = 100;
  u8 z = x + y;
  __voblint_check(x + y < 250);
  __voblint_check(z < 250);
}
```)

Read over mathematical integers, both checks compare $300$ with $250$ and fail.
Read at the variables' own width, both compare $44$, the sum $300$ wrapped to
8 bits, and hold. C answers differently for the two checks. It first
converts both 8-bit operands to `int` (the integer promotions) and adds at
that width, so the first check compares $300 < 250$ and fails. The assignment
to `z` then converts $300$ back to 8 bits, so `z` holds $44$ and the second
check holds. The analyzer agrees. The first check is
#verdict(check-row("kinds-promotion", cond: "(i32) x + (i32) y < 250").verdict)
and the second
#verdict(check-row("kinds-promotion", cond: "(i32) z < 250").verdict). It
also reports the conversion of $300$ to `u8` as an error, because the
conversion changes the value in every run, although C defines its result
(@sec:vimp-vs-c). A program that declares no types makes every variable 32 bits wide, so `z` holds
$300$ and the second check is
#verdict(check-row("kinds-untyped", cond: "z < 250").verdict) (claim
#claim-ref("kinds-untyped")). A verdict is therefore only meaningful
together with the width at which each operation computes. This section fixes
that width for every operation, and states the result as a translation of the
program into a form in which every width is explicit.

*Machine kinds.* A variable has one of eight _machine kinds_
(#isatype("ikind")): `i8`, `u8`, `i16`, `u16`, `i32`, `u32`, `i64` and `u64`,
the signed and unsigned integers of 8, 16, 32 and 64 bits. A kind $k$ of width
$w$ fixes a range #isaconst("ik_range") $k$, the interval from
#isaconst("ik_min") $k$ to #isaconst("ik_max") $k$, which is
$[-2^(w-1), 2^(w-1) - 1]$ for a signed kind and $[0, 2^w - 1]$ for an unsigned
one. Values stay mathematical integers, and the kind only says which of them
a variable may hold. Wraparound #isaconst("ik_norm") maps every integer into
the range by two's complement,
$
  #isaconst("ik_norm") thin k thin n = ((n - #isaconst("ik_min") thin k) mod 2^w) + #isaconst("ik_min") thin k
$
(#isathm("ik_norm_mod")), so that $#isaconst("ik_norm") thin #ctor("U8") thin 300 = 44$.
Wraparound applies to signed kinds too. C leaves signed overflow undefined
(#c11("6.5p5")), and VIMP gives it this defined meaning instead
(@sec:vimp-vs-c).

A program declares kinds in C's style: `global u8 g;` for a global,
`fun u16 f(u8 n)` for a formal and a return value, and `i32 x;` or
`i32 x = 0;` for a local, which may appear anywhere in a body and whose scope
ends with its enclosing block. VIMP has no keyword `int`. A program that
declares no kind at all is _untyped_, and each of its variables is `i32`, the
role of C's `int`. A program that declares one kind must declare every global,
formal and local, and a return kind for every procedure that returns a value.

*Identities and stores.* A kind belongs to a variable, but a name does not
determine the variable. Two procedures may both have a formal `n`, one of kind
`i8` and one of kind `u32`, so a table from names to kinds cannot hold both.
The semantics therefore stores values under _identities_
(#isatype("var_id")): #ctor("GlobalId", thy: "Var_Id") $x$ for a global and
#ctor("ScopedId", thy: "Var_Id") $q$ $x$ for a formal or local $x$ of
procedure $q$. Two further identities serve the call mechanism, and no program
can name them. #ctor("ReturnId", thy: "Var_Id") $q$ carries the return kind of
$q$, and the single slot #ctor("ReturnVar", thy: "Var_Id") carries a returned
value back to the caller. Within one procedure, distinct names resolve to
distinct identities, and two procedures share an identity only for a global
(#isaconst("resolve_var"), #isathm("resolve_var_eq_iff")). The formal language
has no block scopes. The parser removes them. It renames every declaration that
shadows a name already in use in its procedure to a fresh name such as `x#2`,
which no source program can write, and resolves every use to the innermost
declaration in scope (#fixture("26-machine-kinds/15-block_scopes.vimp")).

A store $s$ (#isatype("store")) is a total function from identities to
integers. The parser hands the kinds over as a list of declarations
(#isatype("kind_decls")), and #isaconst("kenv_of") turns it into a kind
environment $kappa$ (#isatype("kenv")) that gives an undeclared identity the
kind `i32`. For an untyped program the list is empty.

*Elaboration.* What the parser builds is _surface_ VIMP, the expressions of
@sec:vimp over names, with implicit conversions. What executes is _core_ VIMP
(#isatype("exp")), in which every arithmetic node carries the kind it computes
at, every variable read names an identity, and every conversion is an explicit
node #ctor("TCast", thy: "Core_Exp"). _Elaboration_ (#isaconst("elaborate"))
translates a surface expression of procedure $q$, at the kind $k$ its context
expects, into core VIMP. It follows C's rules
(#c11("6.3.1.1p2"), #c11("6.3.1.8p1")). An arithmetic operator computes at the
common kind of its operands, which the integer promotions and the usual
arithmetic conversions determine (#isaconst("usual_kind")). Promotion turns
every kind narrower than 32 bits into `i32` (#isaconst("ik_promote")), so
`x + y` above computes at `i32`. A comparison converts both operands to their
common kind and yields $0$ or $1$ at `i32`. A logical operator tests each
operand at its own kind. A conversion node is inserted wherever a value meets
a context of another kind, and omitted where the kinds agree, because a
conversion that changes no value would still cost precision in a domain
without magnitudes such as Sign, which can only answer $top$ for it. With
$x$ and $y$ standing for the identities of `main`, the assignment to `z` above
becomes
$
  z := #ctor("TCast", thy: "Core_Exp") thin #ctor("U8") thin (#ctor("TArith", thy: "Core_Exp") thin #ctor("I32") thin #ctor("AAdd") thin (#ctor("TCast", thy: "Core_Exp") thin #ctor("I32") thin (#ctor("TVar", thy: "Core_Exp") thin #ctor("U8") thin x)) thin (#ctor("TCast", thy: "Core_Exp") thin #ctor("I32") thin (#ctor("TVar", thy: "Core_Exp") thin #ctor("U8") thin y))).
$
The analyzer prints the check conditions of the listing in this elaborated
form, #raw(check-row("kinds-promotion", cond: "(i32) x + (i32) y < 250").cond)
and #raw(check-row("kinds-promotion", cond: "(i32) z < 250").cond).

A literal is placed directly at the kind of its context, so `u8 z = 300;`
stores $44$. Its own kind matters only where it chooses the kind of the
operation it is an operand of. An unsuffixed literal is an `i32` if it fits
and an `i64` otherwise, which is C's rule for a decimal constant when `long`
has 64 bits (#isaconst("ik_of_lit"),
#c11("6.4.4.1p5")). The parser folds a leading minus sign into the literal and
the kind is chosen by magnitude, so `-2147483648` is an `i64`, as the C
expression `-2147483648`, the negation of a `long` constant, is under that
assumption. The analyzer
rejects a program with a literal outside the range of `i64`
(#isaconst("lits_fit"), #isaconst("wf_program_compile_input_exec")).

Commands are elaborated by #isaconst("elab_com"), which inserts the
conversions C performs where a value is written: to the variable's kind at an
assignment, to the formal's kind at an argument (#isaconst("elab_args")), and
to the procedure's return kind #isai("\<kappa> (ReturnId q)") at a
#keyw("return"). A condition or a check is evaluated at the kind it
synthesizes. The arguments of `min` and `max` have no formals. They convert
to their common kind, as the operands of C's usual `MIN` macro do, so
`min(x, u)` with `x = -1` and `u` a `u32` compares $2^32 - 1$ with `u`.
Elaborating every body
gives the program's core procedure table
$Pi = #isaconst("elab_ptable") thin p thin italic("ds")$. Its expressions are
well-typed. The operands of an arithmetic node carry its kind, and every
written value has the kind of its target (#isathm("wt_exp_elaborate"),
#isathm("wt_com_elab_com")).

*Evaluation.* Since every kind is written on its node, evaluation
#isaconst("eval", thy: "Core_Exp") needs no kind environment. It is a function
defined by one equation per constructor. An arithmetic node computes the
mathematical result of its operator (#isaconst("aop_eval")) and wraps it into its
kind, a conversion wraps, and a
variable read returns the stored value unchanged:
$
  #isaconst("eval", thy: "Core_Exp") (#ctor("TArith", thy: "Core_Exp") thin k thin italic("op") thin e_1 thin e_2, s) & = #isaconst("ik_norm") thin k thin (italic("op")(#isaconst("eval", thy: "Core_Exp") (e_1, s), #isaconst("eval", thy: "Core_Exp") (e_2, s))), \
  #isaconst("eval", thy: "Core_Exp") (#ctor("TCast", thy: "Core_Exp") thin k thin e, s) & = #isaconst("ik_norm") thin k thin (#isaconst("eval", thy: "Core_Exp") (e, s)), \
  #isaconst("eval", thy: "Core_Exp") (#ctor("TVar", thy: "Core_Exp") thin k thin x, s) & = s(x).
$
Division and remainder are #isaconst("c_div") and #isaconst("c_mod"), which
truncate toward zero and give $0$ and the dividend for a zero divisor
(@sec:vimp-vs-c). Every expression therefore has a value and no effect, so a
transfer function may evaluate a guard again, as the backward filtering of
@ch:domains does. Input enters only through the statement
`x = __voblint_nondet_int();`, never inside an expression.

Elaboration is the definition of what a surface expression means, so it
deserves a check against a second reading. #isaconst("src_eval") states the
meaning directly on the surface expression, given a kind for every name, in
the shape in which the C standard describes it: convert the operands to their
common kind, compute there with wraparound, and convert the result to the kind
the context expects. Elaboration agrees with it on every store whose values
lie in their kinds (#isaconst("all_in_kinds")).

#theorem(name: [Elaboration preserves meaning], isa: "eval_elaborate")[
  Let $rho$ resolve the names of a procedure to identities and let $t$ hold
  every identity within its kind under $kappa$. Then the elaborated expression
  evaluates in $t$ to the value that #isaconst("src_eval") gives the surface
  expression in the procedure's view $t compose rho$ of the store.
]


The premise is needed at variable reads. #isaconst("src_eval") wraps a
variable's value into its kind, while #isaconst("eval", thy: "Core_Exp") reads
it unchanged, and the two agree only when the stored value already lies in
the range. The theorem relates two definitions in Isabelle. It does not show
either of them to be C, which @sec:vimp-vs-c argues instead.

*Initial values.* A run starts from a store in #isaconst("init_stores")
$kappa$, in which every global is $0$, as C's static objects are, and every
other identity holds some value of its kind. The parser rewrites a local
declared without an initializer, `u8 x;`, into `x = __voblint_nondet_int();`
at the declaration, and one with an initializer into an assignment. The call
leaves an arbitrary value of the kind in `x` and changes nothing else
(#isathm("pstep_declare")). Its outcomes do not depend on what `x` held before
(#isathm("pstep_declare_forgets")), so a declaration in a loop body or in a
procedure called twice starts its variable afresh each time it executes
(#fixture("26-machine-kinds/21-fresh_local_each_call.vimp")).

*The step relation.* @sec:pstep defines execution by a generic step relation
#isaconst("gpstep"), parametric in four choices: the evaluator, the classifier
of the globals, the return slot, and the conversion applied when the
semantics writes a value. The semantics of VIMP, #isaconst("pstep") $kappa$,
is its instance at #isaconst("eval", thy: "Core_Exp"), the
#ctor("GlobalId", thy: "Var_Id") identities (#isaconst("is_global")),
#ctor("ReturnVar", thy: "Var_Id") and #isaconst("kind_conv") $kappa$, which
wraps a value written to $x$ into #isai("\<kappa> x"). It is the only
instance, and the graph and trace semantics of later sections are
instantiated at the same choices. The relation converts at assignments and
argument bindings, where elaboration has already converted, and at the two
writes elaboration cannot see: the result of a call stored in its destination,
and the result of a library call. A returned value is written to
#ctor("ReturnVar", thy: "Var_Id") without conversion, because elaboration
already converted it to the procedure's return kind.

These conversions keep every store typed. For a well-formed program
(#isaconst("wf_program_compile_input")), every store that a run of
#isaconst("pstep") reaches from a store in #isaconst("init_stores") holds
every identity other than #ctor("ReturnVar", thy: "Var_Id") within its kind
(#isaconst("in_kinds"), #isathm("run_from_init_in_kinds")). The return slot is
excluded because procedures with different return kinds share it. The proof
goes through the graph semantics of @sec:cstep and the traces of @ch:traces,
where the invariant holds for every collected store
(#isathm("node_collect_in_kinds")). Its key step is that every call edge of
the compiled graph passes arguments of its formals' kinds
(#isathm("calls_in_kinds_elab_cfg")). The kind-aware domains of @ch:domains
rely on this invariant.

The formal development starts from the parsed program and its kind
declarations. The parser's scope resolution, its rewriting of declarations,
and the kinds it declares are trusted (@sec:trust-boundary). Whether the
resulting meaning is the one a C programmer intends is argued in
@sec:vimp-vs-c.

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

#definition(name: [Source execution], isa: "gpstep", cmd: "inductive")[
  A source configuration is a triple $(c, s, italic("frs"))$ of the command that
  remains to run, a store $s$, and a list $italic("frs")$ of
  #isatype("gframe") values for the suspended activations. Each frame records
  the caller's store and the variable, if any, that receives the result. The
  step relation #isaconst("pstep") relates a configuration of a core program to
  its successor. It is the instance of the generic relation in @fig:pstep at the
  choices of @sec:elaboration.
]

#figure(
  {
    show raw.where(block: true): set text(size: 6.2pt)
    thy("gpstep")
  },
  kind: image,
  placement: none,
  caption: [The declaration of the generic step relation, lifted from the theory.],
) <fig:pstep>

The generic relation takes a classifier of the global variables, separate from
the store, because a call resets only the locals. The relation is written
#isai("\<kappa>, \<Pi> \<turnstile> c \<rightarrow>\<^sub>p c'") for
configurations $c$, $c'$, and a procedure table #isai("\<Pi>"). Its
closure is #isai("\<rightarrow>\<^sub>p\<^sup>*"), and @fig:pstep lists its
rules. No rule inspects an annotation. The rules only copy annotations, from
the rewritten command or from the procedure table. The
#link(
  "https://manuellerchner.github.io/Voblint-Verification-Master-Thesis/index.html#semantics",
)[explainer page]
animates these steps.

A call evaluates the actuals in the caller's store, resets the locals, binds
the formals, each converted to its formal's kind (#isaconst("enter_state"),
#isaconst("bind_formals")), and pushes a frame. A `return e` writes the value
of $e$ to the return slot, and popping the frame merges the caller's locals,
the callee's globals, and the result, converted to the kind of the call's
destination. These operations select by variable and are polymorphic in the value type (#isaconst("enter_binding"),
#isaconst("combine_env"), #isaconst("combine_assign")). Therefore the
non-relational analyses reuse the concrete definitions at their abstract state types, with $top$ in place of the reset
value $0$.

We model the root activation without a #ctor("Restore"), since `main` has no
caller to return to, and a bare #ctor("Unwind") has no step
(#isathm("pstep_Unwind_stuck")). This is why the source contract rejects
#keyw("return") in `main` (#isaconst("no_return")). A source run of a program
$p$ with declarations $italic("ds")$ is a run of #isaconst("pstep") on its
elaboration $Pi = #isaconst("elab_ptable") thin p thin italic("ds")$. It starts
from the configuration $(#isaconst("main_body") thin Pi, s_0, [])$, with an
initial store $s_0$ in #isaconst("init_stores") (@sec:elaboration).

Just as Nipkow and Klein show that well-typed programs do not get stuck
@nipkow14[§9.1.2], we show that well-formed VIMP programs do not, since claims
about the points after a stuck run would hold vacuously. For a program satisfying
#isaconst("wf_source_program"), every reachable configuration has either
finished, as #skipC with an empty frame stack, or can step:

#proved("source_progress")

The source contract rules out every reason a call could fail to step, and every
library call has a result (#isathm("special_result_ex")). The theorem is
stated for the generic relation, and elaboration carries the source contract
over to the core program (#isathm("elab_wf_compile_input")), so it covers the
runs of #isaconst("pstep").

== Scope and adequacy of the source semantics <sec:vimp-vs-c>

Every source-level guarantee in this thesis is interpreted against the
executions of #isaconst("pstep") on the elaborated program, from a store in
#isaconst("init_stores") (@sec:elaboration, @sec:pstep). No guarantee can show
that these are the executions the programmer intended. This can only be
argued, and this section collects the argument. A surface program has no
semantics of its own, so the argument covers every definition that gives it a
meaning: elaboration, the evaluation of core expressions, wraparound, the
conversions on writes, the kinds of undeclared variables, the initial stores
and #isaconst("pstep") itself. The one proved consistency check,
#isathm("eval_elaborate"), relates two of these definitions to each other
(@sec:elaboration) and shows neither of them to be C. @tab:vimp-vs-c compares
VIMP with C11 @iso-c11 (committee draft N1570) wherever both languages have a
construct but model it differently.

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
      [integers], [every result wraps at its kind],
      [signed overflow undefined (#c11("6.5p5"))],
      [], [], [unsigned arithmetic wraps (#c11("6.2.5p9"))],
      [conversions], [wrap into the target kind], [to unsigned: modulo $2^w$ (#c11("6.3.1.3p2"))],
      [], [], [to signed: implementation-defined (#c11("6.3.1.3p3"))],
      [literals], [a leading `-` belongs to the literal],
      [`-` is unary minus (#c11("6.4.4.1p2"), #c11("6.5.3.3p3"))],
      [], [`i32` if it fits, else `i64`], [first type of its list that fits (#c11("6.4.4.1p5"))],
      [], [$-2^63$ is an `i64`], [$2^63$ has no standard type (#c11("6.4.4.1p6"))],
      [`a / 0`, `a % 0`], [$0$ and $a$], [undefined (#c11("6.5.5p5"))],
      [`/`, `%`, $b != 0$], [truncated; $(a "/" b) dot b + a % b = a$],
      [the same where $a "/" b$ is representable (#c11("6.5.5p6"))],
      [`&&`, `||`], [both operands evaluated],
      [second operand only if needed (#c11("6.5.13p4"), #c11("6.5.14p4"))],
      [initial values], [globals $0$, others arbitrary],
      [static $0$, automatic indeterminate (#c11("6.7.9p10"))],
      [`u8 x;`], [any value of its kind, each time], [indeterminate (#c11("6.7.9p10"))],
      [callee locals], [undeclared ones $0$ on entry], [indeterminate (#c11("6.7.9p10"))],
      [checks], [never stop the run, never refine],
      [`assert` aborts on $0$ unless `NDEBUG` (#c11("7.2p1"), #c11("7.2.1.1"))],
      [`min`, `max`], [library calls (#isaconst("special_table"))], [no counterpart],
      [`main`], [no explicit `return`], [`return` gives the exit status (#c11("5.1.2.2.3"))],
      table.hline(),
    )
  },
  placement: none,
  caption: [Constructs that both languages have but model differently. The VIMP
    rows restate #isaconst("ik_norm"), #isaconst("kind_conv"),
    #isaconst("ik_of_lit"), #isaconst("lits_fit"), #isaconst("c_div"),
    #isaconst("c_mod"), #isaconst("eval", thy: "Core_Exp"),
    #isaconst("init_stores"), #isathm("pstep_declare"),
    #isaconst("enter_state") and #isaconst("pstep").],
) <tab:vimp-vs-c>

Each row is a place where a statement true of a VIMP program does not
necessarily hold for the corresponding C program. Wrapping signed overflow,
wrapping conversions and defined division by zero can flip a verdict. After
`z = 5 / 0;` the check `z == 0` holds in VIMP, so a #verdict("PROVED") verdict
on a program that divides by zero says nothing about C. The analyzer therefore
reports possible hazards as separate diagnostics. It reports every possible
zero divisor of `/` and `%`, every signed `+`, `-`, `*` and `/` whose
mathematical result may leave its kind, and every signed `%` whose quotient
may leave its kind, as for `INT_MIN % -1`. It also reports every conversion
that may change its value, whether implicit or explicit inside an expression,
of a returned value, or of a `min` or `max` result. At a point without a
diagnostic, none of these hazards occurs at any store that reaches the point
(#isathm("run_voblint_arithmetic_safe"),
#isathm("run_voblint_no_signed_overflow"),
#isathm("run_voblint_no_remainder_overflow"),
#isathm("run_voblint_no_conversion_overflow"), @sec:verdict-meaning). A
diagnostic is an error when its condition fails at every store that reaches its
point (#isathm("run_voblint_arithmetic_refuted")), and a warning otherwise.
How a domain bounds a signed operation that may overflow, by any value of the
kind or by following the wraparound, is a run option, after Goblint's
`sem.int.signed_overflow` (@sec:domain-kinds). The semantics wraps under both
settings, and the theorems hold for both. A point without diagnostics is still
not shown free of undefined behavior in C. The diagnostics concern arithmetic
only, and VIMP does not model C's indeterminate values, some reads of which are
undefined (#c11("6.3.2.1p2")).

The conversion diagnostic also covers conversions that C defines. C reduces a
value converted to an unsigned type modulo $2^w$ (#c11("6.3.1.3p2")), as VIMP
does, so the conversion of $300$ to `u8` in the listing of @sec:elaboration
stores $44$ in both languages. The analyzer reports it as an error all the
same, because its obligation is that a conversion keeps its value, and this
conversion changes the value in every run. For a conversion to a signed kind
that cannot represent the value, C leaves the result implementation-defined
(#c11("6.3.1.3p3")), and VIMP wraps. A declaration without an initializer
raises no diagnostic, because `__voblint_nondet_int` yields a value of the
destination's kind.

Literals differ at one value. VIMP reads a leading minus sign as part of the
literal (@sec:elaboration), so `-9223372036854775808` is an `i64`. In C it is
unary minus applied to `9223372036854775808`, which no standard type
represents when `long long` has 64 bits (#c11("6.4.4.1p6")). Division and
remainder truncate toward zero as in C11. Goblint once got the remainder
wrong, and issue
#link("https://github.com/goblint/analyzer/issues/1156")[1156] @goblint1156
reports that it claimed `c % 2 == 1` for $c in {-5, -7}$ (@sec:eval-1161).
Evaluating both operands of `&&` is harmless, because expressions are total
and have no effects. It gives the short-circuit value. Only the arithmetic
diagnostics differ, because they cover both operands. The analyzer warns about
the divisor in `x != 0 && 10 / x > 1` (claim
#claim-ref("and-divisor-warning")), and it reports an overflow or a conversion
in an operand that C would skip in the same way.

The initial values that VIMP fixes are ones C leaves open. Every source-level
theorem assumes an initial store from #isaconst("init_stores"), with globals
$0$ as for C's static objects and every other identity, the locals of `main`
among them, holding some value of its kind. A declared local starts at some
value of its kind each time its declaration executes
(#isathm("pstep_declare_forgets"), @sec:elaboration), and that the parser
rewrites every declaration this way is trusted (@sec:trust-boundary). A call
also resets the callee's locals to $0$ (#isaconst("enter_state")). The reset is
observable only for an undeclared local of an untyped program, because in a
typed program every local is declared and its declaration forgets the $0$. No
shipped analysis relies on the reset, because every abstract entry assumes
nothing about callee locals beyond their kinds
(#isaconst("nonrel_enter_frame") for the non-relational analyses,
#isaconst("ord_enter") for the order analysis). A check `y == 0` on an
unassigned local `y` of an untyped callee is therefore
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
#isathm("gpstep.Seq2"), which rebuilds the surrounding residual command. So the same assignment is executed by a different derivation inside every surrounding command.
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

#definition(name: [Control-flow graph], isa: "gcfg", cmd: "record")[
  A graph $g$ is a record of the type below. The graph of a program $p$ with
  declarations $italic("ds")$, #isaconst("elab_cfg") $p$ $italic("ds")$, is its
  instance at identities and core expressions:
  #{
    show raw.where(block: true): set text(size: 6.5pt)
    thy("gcfg")
  }
  #isaconst("intra") holds the _local edges_ $(u, a, v)$, each labeled by an
  #isatype("gedge_action") $a$. #isaconst("calls") holds the _call edges_
  $(u, italic("ca"), ctor("FunctionEntry") thin q, k)$. Such an edge consists
  of the call site $u$, the call information $italic("ca")$, the entry node of
  the callee (by #isaconst("wf_cfg")), and the node $k$ where the caller
  resumes. Nodes (#isatype("cfg_node")) are $ctor("Statement") thin n$,
  $ctor("FunctionEntry") thin p$ or $ctor("FunctionResult") thin p$.
  #isaconst("cfg_entry") is the root node. A check is a local edge labeled
  #isaconst("EA_Check") with its condition, and the report classifies exactly
  these edges (#isaconst("classify_checks")).
]

The call information $ctor("CallEdge") thin italic("dst") thin
italic("formals") thin italic("args")$ (#isatype("gcall_action")) copies the
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
    All rows except the last two are #isatype("gedge_action") constructors on
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
#isaconst("wf_compile_input") of the program's globals classifier, $Pi$ and $italic("ps")$ is
#isaconst("wf_source_program") plus the condition that $italic("ps")$ lists
exactly those procedures, without repetition.

=== Graph execution #thy-badge("Voblint_CFG", "CFG_Exec") <sec:cstep>

#block(breakable: false)[
  #definition(name: [Graph execution], isa: "gcstep", cmd: "inductive")[
    A graph configuration (#isatype("gcconf")) is a triple of a node, a store,
    and a stack of suspended callers (#isatype("gcframe")). Each entry records
    where to resume, which variable receives the result, and the caller's store.
    The step relation #isaconst("cstep") is the instance at the same
    parameters as #isaconst("pstep"), written
    #isai("\<kappa>, g \<turnstile> c \<rightarrow>\<^sub>c c'"), and
    #isai("\<rightarrow>\<^sub>c\<^sup>*") is its closure.
  ]

  #figure(
    {
      show raw.where(block: true): set text(size: 6.2pt)
      thy("gcstep")
    },
    kind: image,
    placement: none,
    caption: [The declaration of the generic graph step, whose instance is #isaconst("cstep").],
  ) <fig:cstep>
]

@fig:cstep lists the rules, one per kind of step. A local edge applies its
transfer #isaconst("gedge_step"), a call edge enters the callee and pushes a
frame, and a result node pops the top frame. In the running example
(@fig:program-to-equations), a run of `main` reaches the call site of
`bump(5)`, takes the call edge to the entry of `bump` with $n = 5$, and pushes a
frame that names the continuation. It then follows the local edges of `bump`
to its result node, where the frame is popped. Execution resumes at the
continuation, and `a` holds $6$. The entry and exit transfers are
built from the same functions that #isaconst("pstep") uses (@fig:pstep).
#isaconst("gcall_enter") binds the formals in #isaconst("enter_state") of the
caller's store, and #isaconst("gcombine_collect") applies
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
  #isai("\<Pi>, g, p \<turnstile> (c, s, frs) \<approx> (v, s, stk)"), relates a
  source configuration to a graph configuration holding the same store, where
  $p$ is the procedure of the outermost activation, `main` for a run of the
  program.
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
continuation node $italic("cont")$. Both suspended-caller rules also locate the
call that opened the activation. A second #isaconst("control_at") premise
places #isaconst("seq_after") $(ctor("Call", thy: "VIMP_Proc") thin q ...)$ $italic("afters")$ in
the caller's body. This premise names the callee $q$, whose body the inner activation runs. In
$sans("Nested")$, the index changes from $q$ to the caller's procedure. $sans("Returning")$ covers
the moment after a callee finishes. The graph has reached
$ctor("FunctionResult") thin q$ of that callee, while the source still holds the
#ctor("Restore") of the activation, possibly behind an #ctor("Unwind") that is
propagating toward it (#isaconst("pop_ready")). The #ctor("Restore") carries the
annotation of its call (#isaconst("pop_ann")), which is the annotation that the
call-site premise refers to.

Equal commands can occur at different places, so the relation does not
determine the node. In `if (b) { x = 1; } else { x = 1; }`, the residual
`x = 1` is related to both branch nodes. The simulation theorems therefore
state that some related graph configuration exists, and the source-level
theorems of @sec:verdict-meaning quantify existentially over the node that
simulates a configuration. A configuration reachable along two paths can be
related to two nodes.

#theorem(name: [One step is matched], isa: "csim_step")[
  If a source configuration and a graph configuration are related by
  #isaconst("csim") and the source takes one step, the graph takes zero or more
  steps to a configuration related to the new source configuration.
]

#proved("csim_step")

The theorem has two premises beyond the related pair and the source step.
#isaconst("procs_embedded") $Pi$ $g$ says that every declared body is source
syntax under a non-library name and lies in $g$ with its entry and return
edges, so no source call enters a body missing from the graph. #isaconst("return_safe") $c$ says that the running
command returns only inside an activation that a call opened, which is the
runtime form of the rule that `main` contains no #keyw("return") (@sec:pstep).
Both premises hold for every well-formed program
(#isathm("procs_embedded_compile_prog"),
#isathm("wf_compile_input_return_safe")), and every source step preserves the
second (#isathm("return_safe_pstep")). By induction on the run,
#isathm("csim_star") extends the theorem to finite source runs, as in
CompCert's simulation diagrams @leroy09[§4.3].

The initial source configuration is related to the node after the
#isaconst("EA_Body") edge of `main` (#isathm("compile_prog_main_base")).
Every finite source run of a well-formed program is therefore matched by a
graph run from the entry that reaches corresponding nodes with the same store. This gives the first inclusion of the soundness chain of
@fig:intro-nest, so an analysis that covers all graph runs covers all source
runs. The executable analyzer rejects ill-formed programs
(#isaconst("wf_program_compile_input_exec")), so the end-to-end theorem needs
no such premise. A context-sensitive analysis needs more structure than these
flat runs offer.
@ch:traces therefore regroups graph runs into activation traces
(#isathm("source_run_has_activation_trace")) and defines on them the coverage
obligations used to establish soundness.
