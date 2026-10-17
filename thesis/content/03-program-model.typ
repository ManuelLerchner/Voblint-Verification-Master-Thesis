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
#import "../lib/claims.typ": claim-check, claim-ref, claim-text

= Programs and Control-Flow Graphs <ch:program-model>

@ch:background analyzed a single loop through its control-flow graph. The
soundness theorem, however, should talk about the programs a user writes, and
these have procedures and recursion. This chapter defines two views of such a
program and connects them. The source semantics executes a program directly
(@sec:pstep). An analysis cannot generate its equations from it, because its
equations need a fixed, finite set of program points, which contexts may then
refine (@sec:constraints), and under recursion the commands that remain to run
nest arbitrarily deep
(@sec:why-graph). Voblint therefore compiles the elaborated program to a
procedure-aware control-flow graph and generates its equations from the graph
(@fig:program-to-equations). A soundness proof for the graph alone would leave
the compiler outside the theorem. This chapter therefore proves the first link
of the soundness chain: every source run of a well-formed program is matched
by a graph run that holds the same store (@sec:csim). The program of
@fig:program-to-equations, in which `main` calls `bump(5)` and `bump(4)`, is
the running example of the remaining chapters.

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
    continuation of a call edge, that is, the node where the caller resumes.
    The edge `return` into the result node of `main` is the return without a
    value by which
    `main` falls through (@sec:compile). The drawing omits the corresponding
    node `pp1` of `bump` and its edge, which no run reaches because `bump`
    always returns explicitly.],
) <fig:program-to-equations>

== VIMP, and what it leaves out <sec:vimp>

VIMP (@fig:vimp-island) is the small imperative language with C-like syntax
that the formalization analyzes. It is kept small because every construct needs a
semantics, compiler clauses, and a transfer function proved sound in every
abstract domain. It has integer variables of C's machine integer types, locals
and globals, procedures with value
parameters, direct calls with an optional result, recursion, assignment,
sequencing, conditionals, `while` loops, nondeterministic input, and checks. It
omits pointers and the heap, arrays and structs, indirect calls, threads,
floating point, `goto`,
`break`, `continue`, and exceptions. Because VIMP has no pointers, concrete
memory is a store that maps variables to integers.

#figure(
  image("/shared/generated/svg/island.svg", width: 75%),
  kind: image,
  placement: auto,
  caption: [Constructs represented in VIMP relative to Goblint's C input,
    taken from the explainer page. Dashed regions are constructs that VIMP
    omits. Sizes and positions are schematic. The figure compares only syntax.
    @sec:vimp-vs-c lists where shared constructs have different meanings.],
) <fig:vimp-island>

Expressions are integer-valued. As in C11, comparisons and logical operators
yield $0$ or $1$ (#c11("6.5.8p6"), #c11("6.5.9p3"), #c11("6.5.3.3p5"), #c11("6.5.13p3"), #c11("6.5.14p3")), and a
condition holds when it is nonzero (#isaconst("truthy"), #c11("6.8.4.1p2"),
#c11("6.8.5p4")).

From here on, we show definitions and theorems in Isabelle/HOL @nipkow14,
a typed logic of total functions. We write $x :: tau$ for "$x$ has type
$tau$", $tau_1 => tau_2$ for the type of functions from $tau_1$ to $tau_2$,
#isai("'a") for a type variable, and $lambda x. t$ for the function that maps
$x$ to $t$. A _datatype_ declares a type by its constructors and comes with
case distinction and structural induction, and a _record_ is a tuple with
named fields. A theorem declares its variables after #isai("fixes"), local
abbreviations after #isai("defines"), its premises after #isai("assumes"),
and its conclusion after #isai("shows"). Inside a proposition, $A ==> B$ is
an implication. Subscripts, superscripts, and symbols such as $tack.r$ are
notation for a constant applied to its arguments, and the text names the
constant at first use.

#definition(name: [Surface expressions], isa: "src_exp", cmd: "datatype")[
  $
    e ::= & n | x | e #vop("+") e | e #vop("−") e | e #vop("*") e | e #vop("/") e
            | e #vop("%") e \
        | & e #vop("<") e | e #vop("<=") e | e #vop(">") e | e #vop(">=") e
            | e #vop("!=") e | e #vop("==") e \
        | & #vop("!", unary: true) e | e #vop("&&") e | e #vop("||") e | (k) med e
  $
  Here $k$ is a C integer type such as `u8` or `i32`, and $(k) med e$
  converts $e$ to it explicitly.
]

Each operator has its own constructor, because an abstract domain chooses its
transformer by the operator, and the executable analyzer makes this choice by
inspecting the syntax. The two AFP languages with procedures that we
considered do not allow this. IMP2 @lammich19imp2 represents a binary operator
by a HOL function of type #isai("int \<Rightarrow> int \<Rightarrow> int"),
which executable code cannot compare with another one, so it cannot tell `+`
from `*`. Its semantics is also deterministic, without input, and its calls
take no arguments and return no value. Schirmer's Simpl @schirmer08simpl is
more expressive, but its basic commands and conditions are likewise HOL
functions and sets of states. Both languages target program verification,
where semantic objects are convenient. An analyzer needs syntax that it can
inspect, so VIMP is defined from scratch with such a syntax, which code
generation can also export.

Besides the structured statements, commands include calls, which may store a
result, and two markers that appear only during execution.

#definition(name: [Commands], isa: "gcom", cmd: "datatype")[
  $
    c ::= & #skipC | x := e | #keyw("check") (e) | c";" c
            | #keyw("if") (e) {c} #keyw("else") {c} | #keyw("while") (e) {c} \
        | & [x :=] med p(e, ..., e) | #keyw("return") e? | #ctor("Restore") | #ctor("Unwind")
  $
]

Every constructor except sequencing also carries an annotation $i$, omitted
above. The semantics never reads it, and parsed and elaborated programs carry
the trivial annotation $()$. A step copies the annotation of the command
it reduces onto what it leaves behind, so the #ctor("Restore") marker of a call
and the #skipC that the finished call leaves carry the annotation of that call.
The simulation of @sec:csim uses this to recognize a finished call.

The command type #isatype("gcom") is generic in the variables and expressions
it contains, which the prefix _g_ marks, and two instances matter. A parsed program is a
#isatype("src_com"), with names as variables and surface expressions. A
translation called elaboration turns it into a core command
(#isatype("com")), in which every operation carries its integer type.

In concrete syntax, an assignment is written `x = e;` and a check
`__voblint_check(e);`. The parser lowers `true`, `false`, and unary minus to the
expression grammar above. A check states a condition for the analyzer to
decide. It behaves like #skipC whatever value $e$ has, so it neither stops the
run nor refines the store. It also carries its source position as a label,
which the semantics ignores and the report uses to name the check.

A call of a declared procedure starts an
_activation_, one execution of the procedure body from its call to its return.
VIMP also has three built-in _library calls_, `__voblint_nondet_int`, `min`,
and `max`, which a program calls without declaring. A library call finishes in
one step without starting an activation. It stores a value the call may return
(#isaconst("special_result")), any integer for `__voblint_nondet_int` and the
minimum or maximum of the arguments for `min` and `max`, converted to the
destination's integer type. #ctor("Restore") and #ctor("Unwind") are not
source syntax. They appear only during execution, where they implement calls
and returns (@sec:pstep).

A program (#isatype("imp_prog")) is a list of procedure declarations, each
with formal parameters and a body, plus a list of global variables. Its
procedure table (#isatype("proc_table")) looks up a name in that list. The
entry procedure is the declaration named `main`, and #isaconst("main_body") is
its body.

== Machine integers and elaboration #thy-badge("Voblint_VIMP", "Core_Exp") <sec:elaboration>

Like a C program, a VIMP program declares its variables with integer types and
leaves most conversions implicit, so the result of an operation depends on the
width at which it is computed. In the program below, `x` and `y` are
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
Read at the variables' own width, both compare $(200 + 100) mod 2^8 = 44$ and
hold. C answers differently for the two checks. It first
converts both 8-bit operands to `int` (the integer promotions) and adds at
that width, so the first check compares $300 < 250$ and fails. The assignment
to `z` then converts $300$ back to 8 bits, so `z` holds $44$ and the second
check holds. The analyzer reports the same, the first check
as #verdict(check-row("kinds-promotion", cond: "(i32) x + (i32) y < 250").verdict)
and the second as
#verdict(check-row("kinds-promotion", cond: "(i32) z < 250").verdict), and it
reports an arithmetic diagnostic for the conversion of $300$ to `u8`, of
severity error because every run that reaches the assignment overflows
(@sec:verdict-meaning).
Had the program declared all three variables `i32`, `z`
would hold $300$ and the second check would be
#verdict(check-row("kinds-i32", cond: "z < 250").verdict) (claim
#claim-ref("kinds-i32")). A verdict is therefore only meaningful
together with the width at which each operation computes.

*Machine kinds.* A variable has one of eight _machine kinds_ (#isatype("ikind")): the signed and unsigned integers of 8, 16, 32 and 64 bits,
written `i8`, `u8`, `i16`, `u16`, `i32`, `u32`, `i64` and `u64`. A kind $k$ of
width $w$ fixes a range, $[-2^(w-1), 2^(w-1) - 1]$ if $k$ is signed and
$[0, 2^w - 1]$ if it is unsigned. Values remain mathematical integers, and a
kind restricts which of them a variable may hold. Wraparound maps every
integer $n$ into the range of $k$ by two's complement. With $m$ the least
value of the range,
$
  #isaconst("ik_norm") med k med n = ((n - m) mod 2^w) + m
$
(#isathm("ik_norm_mod")). For example, $300$ wraps to $44$ at `u8`. Wraparound applies
to signed kinds too, whose overflow C leaves undefined (#c11("6.5p5")).

A program declares kinds in C's style, for instance `global u8 g;` for a
global, `fun u16 f(u8 n)` for a formal and a return value, and `i32 x = 0;`
for a local, which may appear anywhere in a body and whose scope ends with its
enclosing block. Every variable and every procedure that returns a value
declares its kind, and the parser rejects a name that no declaration in scope
introduces.

*Identities and stores.* A name alone does not determine a kind, because two
procedures may both have a formal `n`, one of kind `i8` and one of kind `u32`.
The semantics therefore stores values under _identities_ (#isatype("var_id")),
which qualify a formal or local by its procedure and leave a global
unqualified. Two further identities cannot be named by any program. The
_return slot_ #ctor("ReturnVar") carries a returned value back to the caller.
The identity #ctor("ReturnId") $p$
holds no value. The kind environment uses it to record the kind that $p$
returns. Two procedures share an identity only for a global
(#isathm("resolve_var_eq_iff")).
Block scopes never reach the formal language, because the parser renames every
shadowing declaration to a fresh name such as `x#2` and resolves every use to
the innermost declaration in scope
(#fixture("26-machine-kinds/15-block_scopes.vimp")). The parser's scope
resolution and the kinds it declares are trusted, since no theorem covers the
parser (@sec:trust-boundary). A store $s$ (#isatype("store")) is a total
function from identities to integers, and a kind environment $kappa$
(#isatype("kenv")) gives each identity its kind.

*Elaboration.* The parser builds _surface_ VIMP, the expressions of
@sec:vimp over names, with implicit conversions. The semantics executes _core_
VIMP (#isatype("exp")), in which every operation carries the kind it computes
at, every variable read names an identity, and every conversion inside an
expression is explicit. Only a call's result has no conversion expression,
and the semantics converts it to the kind of the call's destination
(@sec:pstep).
_Elaboration_ (#isaconst("elaborate")) translates surface into core VIMP by
C's rules (#c11("6.3.1.1p2"), #c11("6.3.1.8p1")). An arithmetic operator
computes at the common kind that the integer promotions and the usual
arithmetic conversions determine, and promotion turns every kind narrower than
32 bits into `i32`. A comparison converts both operands to their common kind
and yields $0$ or $1$ at `i32`, and a logical operator tests each operand at
its own kind. A conversion is inserted wherever a value meets a context of
another kind and omitted where the kinds agree, because even a conversion that
changes no value costs precision in a domain that records only signs. assignment to `z` above thus becomes `z := (u8) ((i32) x + (i32) y)`.

Goblint's front end CIL makes the same translation for C @necula02
(#link("https://github.com/goblint/cil/blob/d97418f2e8d2aa88a36c22397c38ccf4d3ffbcde/src/frontc/cabs2cil.ml#L5111")[`doBinOp`],
#link("https://github.com/goblint/cil/blob/d97418f2e8d2aa88a36c22397c38ccf4d3ffbcde/src/cil.ml#L6137")[`mkCastT`]).
It differs in lowering `&&` and `||` into branches, where VIMP evaluates both
operands, and in being unverified OCaml.

A literal takes the kind of its context, so `u8 z = 300;` stores $44$. The
literal keeps its value $300$ in the core expression, so the analyzer still
reports the conversion as an arithmetic error. Where a literal decides the kind of an operation, it counts as `i32` or, if it does not fit, as `i64` (#c11("6.4.4.1p5")). Commands are
elaborated in the same way. A written value is converted to the kind of its
target, the variable at an assignment, the formal at an argument, and the
return kind at a #keyw("return"). A condition or a check is evaluated at its
own kind, and the arguments of `min` and `max` convert to their common kind,
as the operands of C's `MIN` macro do. @fig:elab-stages shows each rule on one
program. Elaborating every body gives the program's core procedure table $Pi = #isaconst("elab_ptable") med p med italic("ds")$, in which every
operation receives operands of its own kind and every written value has the
kind of its target (#isathm("wt_com_elab_com")).

// The three stages of one program, each read from the analyzer: the source
// file, the surface program the parser passes on (--ast), and the core
// statement of each edge (--dot).
#let _tour-src = read("/shared/programs/elab-tour.vimp")
#let _tour-core = claim-text("elab-tour-dot")
#let _sops = (
  "Plus": "+",
  "Minus": "-",
  "Times": "*",
  "Div": "/",
  "Mod": "%",
  "Less": "<",
  "Greater": ">",
  "Eq": "==",
  "And": "&&",
  "Or": "||",
)
// A compound comparison tag is its base comparison followed by `Eq`.
#let _ssym(op) = if op in _sops { _sops.at(op) } else if op.starts-with("Not") { "!=" } else {
  _sops.at(op.slice(0, -2)) + "="
}
#let _sexp(e, top: true) = {
  let (op, args) = e.pairs().first()
  if op == "N" { str(args).replace("−", "-") } else if op == "V" { args } else if op == "Not" {
    "!" + _sexp(args, top: false)
  } else {
    let t = _sexp(args.at(0), top: false) + " " + _ssym(op) + " " + _sexp(args.at(1), top: false)
    if top { t } else { "(" + t + ")" }
  }
}
#let _scom(c) = {
  if type(c) == str { return ((none, "skip", "skip"),) }
  let (op, a) = c.pairs().first()
  if op == "Seq" { _scom(a.at(0)) + _scom(a.at(1)) } else if op == "Assign" {
    ((a.at(0), "x", a.at(0) + " := " + _sexp(a.at(1))),)
  } else if op == "Call" {
    let call = a.at(1) + "(" + a.at(2).map(_sexp).join(", ") + ")"
    ((a.at(0), "call", if a.at(0) == none { call } else { a.at(0) + " := " + call }),)
  } else if op == "Check" { ((none, "check", "check(" + _sexp(a.at(1)) + ")"),) } else if (
    op == "Return"
  ) { ((none, "return", "return " + _sexp(a)),) } else { ((none, op, op),) }
}
// The core label of the edge that executes a surface statement.
#let _ccore((x, kind, _)) = {
  let pre = if kind == "x" { x + " := " } else if kind == "call" { "resume / " } else if (
    kind == "check"
  ) { "check\(" } else { "return " }
  let m = _tour-core.match(regex("label=\"(" + pre + "[^\"]*)\""))
  if m == none { "?" } else { m.captures.first().trim("resume / ", at: start) }
}
#let _tour-ast = json(bytes(claim-text("elab-tour-ast")))
#let _tour-procs = (
  ("f", _tour-ast.at("prog_" + "table").first().at(1).body),
  ("main", _tour-ast.at("prog_" + "main")),
)
#let _tour-kinds = {
  let rows = ()
  for chunk in _tour-src.split("fun ").slice(1) {
    let m = chunk.match(regex("^(?:(\\w+) )?(\\w+)\\("))
    let q = m.captures.at(1)
    let ks = if m.captures.at(0) != none { ("return " + m.captures.at(0),) } else { () }
    // A kind followed by a name and `(` declares the procedure, not a variable.
    ks += chunk
      .matches(regex("\\b([iu](?:8|16|32|64)) (\\w+)"))
      .filter(d => not chunk.slice(d.end).starts-with("("))
      .map(d => d.captures.at(1) + " " + d.captures.at(0))
    rows += ks
      .chunks(2)
      .enumerate()
      .map(((i, c)) => (if i == 0 { q + ": " } else { " " * (q.len() + 2) }) + c.join(", "))
  }
  rows
}
// The derived columns are printed by the analyzer, not source lines, so they
// carry no line numbers.
#let _plain(t) = codly-local(number-format: none, raw(block: true, t))
#let _stage(title, body) = block(width: 100%)[
  #align(center, text(size: 8pt, weight: "bold", title))
  #v(-2pt)
  #set text(size: 6.5pt)
  #body
]
#figure(
  grid(
    columns: (1.1fr, 0.8fr, 1.2fr),
    column-gutter: 6pt,
    _stage[source text][#listing(_tour-src, lang: "c", claim: "elab-tour")],
    _stage[surface VIMP (parser)][
      #_plain(
        _tour-procs
          .map(((q, b)) => q + ":\n" + _scom(b).map(r => "  " + r.at(2)).join("\n"))
          .join("\n"),
      )
      #_plain("kinds:\n" + _tour-kinds.join("\n"))
    ],
    _stage[core VIMP (elaboration)][
      #_plain(
        _tour-procs
          .map(((q, b)) => q + ":\n" + _scom(b).map(r => "  " + _ccore(r)).join("\n"))
          .join("\n"),
      )
    ],
  ),
  caption: [One program in its three forms. The trusted parser lowers each
    declaration to an assignment, `u8 x;` to `x = __voblint_nondet_int();`, and
    collects the declared kinds into #isatype("kind_decls"). Elaboration computes
    every operation at its C kind and inserts each conversion, so `x + 100`
    wraps to $44$, `s < u` compares $2^32 - 1$ with $1$, and the check `b == 0`
    is #verdict(claim-check("elab-tour", "b == 0").at(3)). The surface and core
    columns are the analyzer's `--ast` and `--dot` output (claims
    #claim-ref("elab-tour*")).],
  kind: image,
  placement: none,
) <fig:elab-stages>

*Evaluation.* Since every kind is written in the core expression, evaluation
#isaconst("eval", thy: "Core_Exp") needs no kind environment. An operation
computes its mathematical result and wraps it into its kind with
#isaconst("ik_norm"), a conversion wraps its operand, and a variable read
returns the stored value. Division and remainder truncate toward zero and give
$0$ and the dividend for a zero divisor (#isaconst("c_div"),
#isaconst("c_mod")). Every expression therefore has a value and no effect, so
a transfer function may evaluate a guard more than once. Input enters only
through the statement `x = __voblint_nondet_int();`, never inside an
expression.

To check elaboration, #isaconst("src_eval") gives a surface expression its
meaning directly, given a kind for every name, in the shape the C standard
describes. It converts the operands to their common kind, computes there with
wraparound, and converts the result to the kind the context expects.
Elaboration agrees with it on every store whose values lie in their kinds
(#isaconst("all_in_kinds")).

In the statement below, $rho$ resolves the names of a procedure to identities,
$t compose rho$ is the procedure's view of a core store $t$, $kappa compose rho$
gives each name its kind, and $italic("ik")$ is the kind that the context
expects of the expression's value.

#theorem(name: [Elaboration preserves meaning], isa: "eval_elaborate", statement: true)[]

== Executing a source program #thy-badge("Voblint_VIMP", "VIMP_Proc") <sec:pstep>

A _small-step_ operational semantics defines the meaning of a program by a
step relation from one configuration to the next, and a run is a sequence of
steps @plotkin04[§3.2]. VIMP's _source semantics_ #isaconst("pstep") is of
this kind, and so is the semantics of the control-flow graph.

Without calls, a configuration is a pair $(c, s)$ of the command that remains
to run and the store, as in the semantics of IMP by Nipkow and Klein
@nipkow14[§7.3]. An assignment updates the store and leaves #skipC, and a
check leaves the store unchanged. A sequence steps its first command until it is #skipC. A conditional selects a branch by #isaconst("truthy"), and a loop
unfolds into a conditional that runs the body and then the loop again. The
command that remains after a step, which describes the remainder of the
execution @plotkin04[§3.2], is the _residual_.

While a callee runs, the caller's remaining work has to wait, and a
#keyw("return") has to skip the rest of the callee's body. VIMP keeps the
waiting work inside the residual and saves only data on a stack. A call
continues with the callee's body followed by #ctor("Restore"), a runtime
marker that hands control back to the caller once the body reaches its end
without a #keyw("return"), that is, once it _falls through_. A
#keyw("return") becomes the marker #ctor("Unwind"), which discards the
commands after it until it meets the #ctor("Restore") of its call. Each
suspended activation keeps its data in a _frame_.

Isabelle defines step relations such as this one inductively. An _inductive
definition_ is the least relation closed under its rules, and its _rule
induction_ proves a property of every element with one case per rule.

#definition(
  name: [Source execution],
  isa: "pstep",
  cmd: "inductive",
  snippet: thy("pstep"),
  snippet-caption: [The declaration of the step relation #isaconst("pstep"), lifted from the theory.],
  snippet-label: <fig:pstep>,
)[
  A source configuration is a triple $(c, s, italic("frs"))$ of the command that
  remains to run, a store $s$, and a list $italic("frs")$ of
  frames (#isatype("frame")) for the suspended activations. Each frame
  records the caller's store and the variable, if any, that receives the
  result. The step relation #isaconst("pstep") of @fig:pstep relates a configuration of a core program to its successor.
]

Expressions are evaluated by #isaconst("eval", thy: "Core_Exp"), and every
written value is converted to the kind that a kind environment $kappa$ assigns
to its target. Evaluation needs no kinds, but this conversion does, so for a
procedure table #isai("\<Pi>") and configurations $c$, $c'$ a step is written
#isai("\<kappa>, \<Pi> \<turnstile> c \<rightarrow>\<^sub>p c'"), and
#isai("\<rightarrow>\<^sub>p\<^sup>*") is its closure.#footnote[The
  #link("https://manuellerchner.github.io/Voblint-Verification-Master-Thesis/index.html#semantics")[explainer page] animates the source execution, the graph execution and the
  activation trace of @ch:traces side by side for one program.]

A call evaluates the actuals in the caller's store, resets every local of the
callee to $0$ (#isaconst("enter_state")), binds the formals, each converted to
its formal's kind, and pushes a frame. A `return e` writes the value of $e$ to
the return slot. Popping the frame merges the caller's locals with the
callee's globals (#isaconst("combine_env")) and writes the result, converted
to the kind of the call's destination, to that destination
(#isaconst("combine_assign")). The remaining
helpers of @fig:pstep recognize a library call and its arguments and test for the
#ctor("Restore") marker.

The root activation has no #ctor("Restore"), since `main` has no caller to
return to, and a bare #ctor("Unwind") has no step
(#isathm("pstep_Unwind_stuck")), so `main` must contain no #keyw("return").
A source run of a program $p$ with
declarations $italic("ds")$ is a run of #isaconst("pstep") on its elaboration
$Pi = #isaconst("elab_ptable") med p med italic("ds")$ from the configuration
$(#isaconst("main_body") med Pi, s_0, [])$. Its initial store $s_0$ lies in
#isaconst("init_stores") $kappa$, where every global is $0$, as C's static
objects are, and every other identity holds some value of its kind. The
semantics converts every value it writes to the kind of its target, so every
store a run reaches keeps each variable within its kind
(#isathm("run_from_init_in_kinds")).

The _source contract_ #isaconst("wf_source_program") excludes programs whose calls cannot step or
whose results are undefined. It requires that

- every call names a declared procedure with matching arity or a library
  function with suitable arguments and a destination, and no declared name is
  a library name,
- the formals of a procedure are distinct and none of them is a global or the
  return slot, and `main` is declared, takes no arguments and contains no
  #keyw("return") (#isaconst("no_return")),
- bodies contain no #ctor("Restore") or #ctor("Unwind"),
- the name #isaconst("ret_var") of the return slot is reserved, so no global,
  source expression, assignment, or call destination names it,
- a call that stores a result names a _value-providing_ callee
  (#isaconst("value_providing")), whose body cannot fall through, cannot reach
  a #keyw("return") without a value, and contains a #keyw("return") with a
  value.

C11 makes using the value of a call that falls through undefined
(#c11("6.9.1p12")). Without the last condition, VIMP would silently store the
$0$ to which a call resets the return slot on entry. A value-providing
callee may still diverge.

Just as Nipkow and Klein show that well-typed programs do not get stuck
@nipkow14[§9.1.2], we show that well-formed VIMP programs do not, since claims
about the points after a stuck run would hold vacuously. For a program satisfying
#isaconst("wf_source_program"), every reachable configuration has either
finished, as #skipC with an empty frame stack, or can step. This progress result
does not imply termination, since a run may still diverge:

#proved("source_progress")

The compiler of @sec:compilation also reads a list of the procedures other
than `main`, and its input contract #isaconst("wf_compile_input") is
#isaconst("wf_source_program") plus the condition that this list contains
each of these procedures exactly once. Elaboration preserves this contract
(#isathm("elab_wf_compile_input")), so the theorem covers every run of an
elaborated program.

== Scope and adequacy of the source semantics <sec:vimp-vs-c>

Every source-level guarantee in this thesis is interpreted against the
executions of #isaconst("pstep") on the elaborated program, from a store in
#isaconst("init_stores") (@sec:pstep). Whether these are the executions the
programmer intended cannot be proved from the same definitions, so this
section argues it. A surface program has no semantics of its own, so the
argument covers every definition that gives it a meaning: elaboration, the
evaluation of core expressions, wraparound, the conversions on writes, the
initial stores and #isaconst("pstep") itself. The one proved consistency
check, #isathm("eval_elaborate"), relates two of these definitions to each
other and neither of them to C. @tab:vimp-vs-c compares
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
      [],
      [`i32` if $|n| <= 2^31 - 1$, else `i64`],
      [first type of its list that fits (#c11("6.4.4.1p5"))],
      [], [$-2^63$ is an `i64`], [$2^63$ has no standard type (#c11("6.4.4.1p6"))],
      [`a / 0`, `a % 0`], [$0$ and $a$], [undefined (#c11("6.5.5p5"))],
      [`/`, `%`, $b != 0$], [truncated; $(a "/" b) dot b + a % b = a$],
      [the same where $a "/" b$ is representable (#c11("6.5.5p6"))],
      [`&&`, `||`], [both operands evaluated],
      [second operand only if needed (#c11("6.5.13p4"), #c11("6.5.14p4"))],
      [initial values], [globals $0$, others arbitrary],
      [static $0$, automatic indeterminate (#c11("6.7.9p10"))],
      [`u8 x;`], [any value of its kind, each time], [indeterminate (#c11("6.7.9p10"))],
      [callee locals], [$0$ on entry, never read], [indeterminate (#c11("6.7.9p10"))],
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
reports possible arithmetic hazards as separate diagnostics
(@sec:verdict-meaning).

The parser folds a leading minus sign into the literal and chooses its kind by
magnitude, so `-9223372036854775808`, the one literal on which VIMP and C
differ, is an `i64`. In C, it is unary minus applied to
`9223372036854775808`, which no standard type represents when `long long` has
64 bits (#c11("6.4.4.1p6")). Division and remainder truncate toward zero as in
C11. Goblint once got the remainder wrong, and issue
#link("https://github.com/goblint/analyzer/issues/1156")[1156] @goblint1156
reports that it claimed `c % 2 == 1` for $c in {-5, -7}$. Because expressions
are total and have no effects, evaluating both operands of `&&` gives the
short-circuit value. Only the arithmetic diagnostics differ, because they
cover both operands. The analyzer warns about the divisor in
`x != 0 && 10 / x > 1` (claim #claim-ref("and-divisor-warning")).

VIMP fixes initial values that C leaves open. Every source-level theorem
assumes an initial store from #isaconst("init_stores"), in which the locals of
`main` hold some value of their kinds. The parser lowers a declaration without
an initializer, such as `u8 x;`, to the library call
`x = __voblint_nondet_int();`, which stores some value of the kind of `x`
whatever `x` held before (#isathm("pstep_declare"),
#isathm("pstep_declare_forgets")). A declared local thus starts at some value
of its kind each time its declaration executes, and that the parser lowers
every declaration this way is trusted. A call also resets the callee's locals to $0$
(#isaconst("enter_state")). However, no program the parser accepts observes the
reset, because the parser rejects a use before the declaration and the
declaration writes the local before any read. No shipped analysis relies on the
reset either, because
every abstract entry assumes nothing about callee locals beyond their kinds
(#isaconst("nonrel_enter_frame") for the analyses that track each variable separately). Checks never
prune executions, so the verdict for one check does not depend on an earlier
one. Goblint's `__goblint_check` behaves the same way, and its library table
classifies it as checked and not used for refinement
(#link("https://github.com/goblint/analyzer/blob/5320a6b741e50dc049f7a1b85e1709e9565cc54a/src/util/library/libraryFunctions.ml")[`libraryFunctions.ml`]).

*No second semantics.* No external semantics cross-checks #isaconst("pstep").
For C, Isabelle offers the C parser of AutoCorres2 @brecknell24autocorres2,
which translates a subset of C into Simpl programs @schirmer08simpl, and Coq
has the Clight semantics of CompCert @leroy09. Relating VIMP to either of
them, or to IMP2 or Simpl directly, would need a translation and its own
adequacy argument, which is left as future work.

== The procedure-aware control-flow graph <sec:graph>

=== Why a graph <sec:why-graph>

An analysis attaches abstract states to program points and transfer functions
to transitions. #isaconst("pstep") offers neither in a usable form. Its only
notion of location is the residual. Without recursion, only finitely many
residuals arise, because a loop's unfolding revisits the same command forms,
but a recursive call can nest another #ctor("Restore") wrapper at every call
depth. An assignment is also not a transition between fixed program points,
because inside a sequence, it steps through the rule #isathm("pstep.Seq2"),
which rebuilds the surrounding residual. Finally, nothing names the entry of a
procedure, its result, or the point where a caller resumes. The schematic
control-flow graph of @fig:counting-loop solves the first two problems, with
finitely many nodes and one transfer per edge. The procedure-aware graph
solves the third. It adds an entry node and a result node per procedure, and
call edges that record their continuations. The entry node holds the state a
callee starts from, the result node the state it returns with, and the
continuation names the node where the caller resumes. A call can therefore be
analyzed by connecting these nodes instead of by following the callee's body.

A _syntax-directed_ analyzer, such as that of Nipkow and Klein
@nipkow14[Ch. 13], needs no graph, because it recurses over the command
structure. Voblint instead follows Goblint and is _constraint-based_
@apinis12. It turns the program into a system of inequalities over unknowns
indexed by the graph's nodes and leaves the solution to a generic solver that
knows nothing about programs. Calls need no special treatment by the solver,
because a call contributes ordinary right-hand sides and side effects
(@sec:side-effects) to the same system. This choice requires the
compiler and simulation proof of this chapter, and a semantics of traces that
says what the inequalities mean (@ch:traces). The solver is the verified
top-down solver of @sec:td.

=== Nodes and edges #thy-badge("Voblint_CFG", "CFG_Def") <sec:cfg>

#definition(name: [Control-flow graph], isa: "gcfg", cmd: "record")[
  A graph $g$ is a record of the type below. The graph of a program $p$ with
  declarations $italic("ds")$, #isaconst("elab_cfg") $p$ $italic("ds")$, is its
  instance at identities and core expressions:
  #{
    show raw.where(block: true): set text(size: 6.5pt)
    thy("gcfg")
  }
  The field #isaconst("intra") holds the _local edges_ $(u, a, v)$, each labeled by a #isatype("gedge_action") $a$. The field #isaconst("calls") holds the _call edges_
  $(u, italic("ca"), ctor("FunctionEntry") med q, k)$. Such an edge consists
  of the call site $u$, the call information $italic("ca")$, the entry node of
  the callee (by #isaconst("wf_cfg")), and the node $k$ where the caller
  resumes. Nodes (#isatype("cfg_node")) are $ctor("Statement") med n$,
  $ctor("FunctionEntry") med p$ or $ctor("FunctionResult") med p$. A check is
  a local edge labeled #isaconst("EA_Check") with its condition.
]

The call information $ctor("CallEdge") med italic("dst") thin
italic("formals") med italic("args")$ (#isatype("gcall_action")) copies the
callee's formals onto the edge, so the graph semantics binds actuals to formals
without the procedure table. VIMP has no function pointers (@sec:vimp), so
every call names its callee, and the compiler fixes the target of each call
edge. Indirect calls would require discovering call targets during the
analysis and are left for future work. The node kinds match Goblint's
(#link("https://github.com/goblint/analyzer/blob/5320a6b741e50dc049f7a1b85e1709e9565cc54a/src/common/framework/node0.ml")[`node0.ml`]),
which calls our $ctor("FunctionResult")$ node `Function`.

#figure(
  {
    set text(size: 9pt)
    table(
      columns: (auto, 1fr, auto),
      align: (left, left, left),
      stroke: none,
      inset: (x: 7pt, y: 3pt),
      table.hline(),
      [*VIMP*], [*transition and its effect on the store $s$*], [*Goblint*],
      table.hline(stroke: 0.5pt),
      [#isaconst("EA_Assign") $x$ $e$],
      [assignment, sets $x$ to the converted value of $e$],
      [`Assign`],
      [#isaconst("EA_Assume") $e$], [guard, keeps $s$ if $e$ holds, else no successor], [`Test`],
      [#isaconst("EA_AssumeNot") $e$], [guard, keeps $s$ if $e$ fails, else no successor], [`Test`],
      [#isaconst("EA_Special")], [`min`, `max` or input, stores a possible result], [`Proc`],
      [#isaconst("EA_Check")], [check, keeps $s$], [`Proc`],
      [#isaconst("EA_Body") $p$], [enters the body of $p$, keeps $s$], [`Entry`],
      [#isaconst("EA_Ret")], [return, writes a returned value to the return slot], [`Ret`],
      [#isaconst("EA_Nop")], [no-op, keeps $s$], [`Skip`],
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
    #isaconst("intra") edges, with the effect that #isaconst("edge_step")
    gives them. Goblint routes library calls and `__goblint_check` through
    `Proc`. It skips empty statements and uses `Skip` only for the self-loop of
    an empty loop.],
) <tab:cfg-edges>

Each edge action $a$ denotes a transfer #isaconst("edge_step") $a$, which
maps a store to the set of stores after the edge. The set is empty when a
guard fails and has more than one element for nondeterministic input. #isaconst("EA_Body")
labels the edge from the entry node of a procedure into its body, and
#isaconst("EA_Nop") labels a #skipC. The compiler also emits
#isaconst("EA_Nop") for a library call that stores no result or whose
arguments do not fit the library function, but the source contract excludes
such calls (@sec:pstep).

*A fragment of Goblint's input.* Goblint analyzes C after its CIL front end
@necula02 has normalized it, so that expressions have no side effects and a
call is a separate instruction with an optional destination
(#link("https://github.com/goblint/cil/blob/d97418f2e8d2aa88a36c22397c38ccf4d3ffbcde/src/cil.mli")[`cil.mli`]
at the revision Goblint pins). VIMP makes the same choice, and every edge kind
of Goblint's CFG, except inline assembly and in-place declarations, has a VIMP
counterpart (@tab:cfg-edges). No translation from C to VIMP is formalized.

The graph keeps local edges and call edges in separate fields, because a local
edge changes the store within one activation, while a call edge starts a new
one. No edge action denotes a call, so a call can never be taken as a local
step.

Returns, in contrast, are ordinary local edges. A #keyw("return") in $p$ leads
to the result node $ctor("FunctionResult") med p$, which all callers of $p$
share, so recursion needs no copies of nodes. A shared result node has no
single continuation, and in a compiled graph no edge leaves it. The call edge
records the continuation $k$ instead. After a return, execution resumes at the
continuation saved in the frame, and an analysis connects the callee's result to
the correct caller through the call edge. The saved frame identifies the
matching call, so the graph needs no return edges to individual callers. A
completed program ends at
$ctor("FunctionResult") med #raw("main")$ (#isaconst("cfg_exit")).
@fig:cfgmap shows these properties on a recursive program.

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
    `voblint --dot` prints it. Here $sans("pp") med n$ is
    $ctor("Statement") med n$, and $sans("entry")_p$, $sans("exit")_p$ are
    $ctor("FunctionEntry") med p$, $ctor("FunctionResult") med p$. As in
    @fig:program-to-equations, solid gray arrows are #isaconst("intra") edges,
    and dashed purple arrows are #isaconst("calls") tuples. Dotted connectors
    and thin blue arrows are not edges. Dotted connectors show the continuation
    of a call tuple. Thin blue arrows show where execution continues after a
    result node. Each procedure has one copy of its nodes, whatever the
    recursion depth. The drawing omits the fall-through nodes $sans("pp") med 1$
    of `dec` and $sans("pp") med 8$ of `sum` and their return edges, which no
    run reaches because both bodies always return explicitly. The number
    $sans("pp") med 4$ belongs to the empty `else` branch of the conditional,
    which receives no edge (@sec:compile).],
) <fig:cfgmap>

== Compilation <sec:compilation>

The compiler turns a VIMP program into a procedure-aware graph. Its design
decides which program points exist and where the code of each command lies in
the graph.

=== Compiling a command #thy-badge("Voblint_Compile", "VIMP_Proc_to_CFG") <sec:compile>

To emit the edges of a command, a compiler has to know where control goes
after it. Compilers commonly pass this target down, as the inherited attribute
$S."next"$ of the dragon book @aho06[§6.6.3]. Voblint's _continuation-passing_
compiler does the same. It takes the command and the node $k$ at which control
continues afterward, and emits the command's edges so that they end at $k$
(#isaconst("compile"), #isaconst("compile_prog")). Nodes are numbered
consecutively. A command $c$ occupies a block of #isaconst("csize") $c$
numbers, a count computed from its syntax alone, and it is entered at the
first of them, $"entry"(c)$. The compiler therefore knows the entry of $c_2$
in $c_1";" c_2$ before it compiles $c_2$. Schematically, writing
$"compile"(c, k)$ for the edges of $c$ against the continuation $k$, $n$ for
$"entry"(c)$ and $h$ for the entry of a loop,
$
  "compile"(x := e, k) & = {n ->^(x := e) k}, \
  "compile"(p(e_1, ..., e_m), k) & = {n ->^"call" ctor("FunctionEntry") med p "with continuation" k}, \
  "compile"(c_1";" c_2, k) & = "compile"(c_1, "entry"(c_2)) union "compile"(c_2, k), \
  "compile"(#keyw("if") (e) {c_1} #keyw("else") {c_2}, k) & = {n ->^e "entry"(c_1), n ->^(not e) "entry"(c_2)} \
  & quad union "compile"(c_1, k) union "compile"(c_2, k), \
  "compile"(#keyw("while") (e) {c}, k) & = {h ->^e "entry"(c), h ->^(not e) k} union "compile"(c, h), \
  "compile"(#keyw("return") e, k) & = {n ->^(#keyw("return") e) ctor("FunctionResult") med p}.
$
The alternative would give every fragment an exit node of its own, and
sequencing two fragments would need a no-op edge between two nodes that denote
the same program point. With continuations, a node is a program point between
two transfers, as in Goblint's CFG. A conditional needs no join node, because
both branches end at the same $k$, and a loop compiles its body against its
own head, so the compiled counting loop of @fig:counting-loop has no node $t$
and no edge $t -> h$. A #keyw("return") ignores its continuation. An empty
branch #skipC of a conditional keeps its number but receives no edge, because
the guard edge leads directly to $k$.

A call to a declared procedure becomes a call edge from the call site to the
callee's entry, with $k$ as its continuation, and adds no local edge. A
#keyw("return") becomes an #isaconst("EA_Ret") edge to the result node of its
procedure. A body that falls through needs such an edge as well, so
#isaconst("compile_proc") compiles every body against one extra node, the
_fall-through node_, from which a return edge without a value leads to the
result node (@fig:compile-proc). Compiling the body directly against the
result node would let a final assignment end there, and the extra node keeps
every edge into $ctor("FunctionResult") med p$ a return edge. In a body that
always returns, the fall-through node and its edge are dead code.

#figure(
  {
    show raw.where(block: true): set text(size: 5.8pt)
    thy("compile_proc")
  },
  kind: image,
  placement: none,
  caption: [The declaration of #isaconst("compile_proc"), lifted from the theory.],
) <fig:compile-proc>

These rules give every compiled graph a fixed shape. Call edges always enter a
procedure entry, no local edge enters one, and every return edge ends at the
result node of its own procedure. The structural contract #isaconst("wf_cfg")
collects these properties, and every compiled graph satisfies it without
premises (#isathm("compile_prog_wf")). The graph's entry is
$ctor("FunctionEntry") med #raw("main")$, and its edge sets are finite
(#isathm("compile_prog_finite")), so the executable analyzer can enumerate
them.

=== Graph execution #thy-badge("Voblint_CFG", "CFG_Exec") <sec:cstep>

#block(breakable: false)[
  #definition(
    name: [Graph execution],
    isa: "cstep",
    cmd: "inductive",
    snippet: thy("cstep"),
    snippet-caption: [The declaration of the graph step #isaconst("cstep"), lifted from the theory.],
    snippet-label: <fig:cstep>,
  )[
    A graph configuration (#isatype("cconf")) is a triple of a node, a store,
    and a stack of suspended callers (#isatype("cframe")). Each entry records
    where to resume, which variable receives the result, and the caller's store.
    The step relation #isaconst("cstep") is the instance at the same
    parameters as #isaconst("pstep"), written
    #isai("\<kappa>, g \<turnstile> c \<rightarrow>\<^sub>c c'"), and
    #isai("\<rightarrow>\<^sub>c\<^sup>*") is its closure.
  ]
]

@fig:cstep lists the rules, one per kind of step. A local edge applies its
transfer #isaconst("edge_step"), a call edge enters the callee and pushes a
frame, and a result node pops the top frame. In the running example
(@fig:program-to-equations), a run of `main` takes the call edge of `bump(5)`
to the entry of `bump` with $n = 5$ and pushes a frame that names the
continuation. It follows the local edges of `bump` to its result node, pops
the frame, and resumes at the continuation, where `a` holds $6$. The entry and
exit transfers (#isaconst("call_enter"), #isaconst("combine_collect")) are
built from the functions that #isaconst("pstep") uses, so both executions can
hold the same store. #isaconst("cstep") is defined for an arbitrary graph, not
only for compiled ones.

== Relating the two executions <sec:csim>

The soundness theorem is stated over #isaconst("pstep"), but the analysis
solves equations generated from the graph. Every finite source run must
therefore be matched by a run of the compiled graph that ends with the same
store at a related node. We prove this with a _forward simulation_, a relation
between source and graph configurations such that every source step can be
matched by zero or more graph steps that preserve it.

The source keeps the remaining work of a suspended caller inside the running
command, behind a #ctor("Restore") marker, while the graph keeps it on the
frame stack as the continuation node of the call. The two also step at different
places. Unfolding a loop, discarding a finished #skipC, and propagating
#ctor("Unwind") have no corresponding graph step, so the graph answers one
source step with zero or more steps. We prove only this direction, because
soundness needs no converse.

The relation has to say where a residual is in the graph and how the two
stacks correspond. The first part is #isaconst("control_at"). It relates a
residual of a procedure body to the node of the body's compiled code at which
the graph stands when the source has that residual left to run. A residual that starts
with a command is at the entry node of that command, and a command that has
just finished, leaving #skipC, is at its continuation. For the stacks,
consider the running example while `bump(5)` runs. The source command has the
form $(r";" ctor("Restore") med i)";" a_1";" ...";" a_m$. Here $r$ is the
residual of the body of `bump`, $i$ is the annotation of the call, and
$a_1, ..., a_m$ are the commands of `main` still to run after the call,
written $italic("afters")$ in @fig:csim. The graph is at a node of `bump`, and
its stack holds one frame $(italic("cont"), italic("dst"), italic("caller"))$
with the continuation node of the call. The invariant connecting the two is
that the commands after the #ctor("Restore") are exactly the code that the
graph runs from $italic("cont")$ on. Once the call has finished, it leaves
$#skipC med i";" a_1";" ...";" a_m$, and this residual is at
$italic("cont")$.

#definition(
  name: [Simulation relation],
  isa: "csim",
  cmd: "inductive",
  snippet: thy("csim"),
  snippet-caption: [The declaration of #isaconst("csim"), lifted from the theory.],
  snippet-label: <fig:csim>,
)[
  #isaconst("csim"), written
  #isai("\<Pi>, g, p \<turnstile> (c, s, frs) \<approx> (v, s, stk)"), relates a
  source configuration to a graph configuration holding the same store, where
  $p$ is the procedure of the outermost activation, `main` for a run of the
  program.
]

In @fig:csim, #isaconst("compiled_at") states that $italic("body_p")$ is the
body of $p$ and that its compiled edges, together with its entry edge and its
fall-through edge, lie in $g$. As in @sec:compile, $k$ is the continuation
against which the body is compiled, here its fall-through node, and $n$ is the
first node number of the body. The suffix $c$ in
$italic("kc")$, $italic("nc")$ and $italic("body_pc")$ marks the caller.
#isaconst("seq_after") $c$ $italic("afters")$ appends the list
$italic("afters")$ to $c$ by sequencing. $sans("Base")$ relates a single
activation with both stacks empty. $sans("Nested")$ adds one suspended caller
beneath a related callee configuration and states the invariant above with two
#isaconst("control_at") premises for the same $italic("afters")$. The call
with annotation $i$, followed by $italic("afters")$, is at the call site, and
the finished call $#skipC med i";" italic("afters")$ is at $italic("cont")$. The
list is the same in both because a call does not change what its caller does
afterwards, and the shared annotation $i$ marks the #skipC as the remainder of
this call. $sans("Returning")$ covers the moment after the callee has finished.
The graph is already at the callee's result node, while the source still holds
the #ctor("Restore") of the call, possibly behind a propagating
#ctor("Unwind") (#isaconst("pop_ready")). The condition
#isaconst("pop_ann") $w = "Some" i$ says that this #ctor("Restore") belongs to
the call with annotation $i$.

Equal commands can occur at different places, so the relation does not
determine the node. In `if (b) { x = 1; } else { x = 1; }`, the residual
`x = 1` is related to both branch nodes. The simulation theorems therefore
state that some related graph configuration exists.

#theorem(name: [One step is matched], isa: "csim_step", statement: true)[
  If a source configuration and a graph configuration are related by
  #isaconst("csim") and the source takes one step, the graph takes zero or more
  steps to a configuration related to the new source configuration.
]

The theorem also assumes that every declared body lies in the graph with its
entry and return edges, and that the running command returns only inside an
activation that a call opened. Both hold for every well-formed program, and
every source step preserves the second.

The proof distinguishes calls, returns, return propagation and all other
steps. The hard cases are the ones that change the stacks. At a call, the
graph takes the call edge, and the new $sans("Nested")$ layer gets its
location of the finished call from the location of the call itself, since the
compiler gave the call edge the continuation node of the call. The return is
the hardest case. The source writes the return slot, and the graph follows
along the return edge to the result node. The source then propagates
#ctor("Unwind") through the dead code of the callee, and the graph stays at the
result node, which $sans("Returning")$ allows. The final pop of the frame is
matched by the graph's return to $italic("cont")$, and there the caller's
residual
$#skipC med i";" italic("afters")$ is related to $italic("cont")$ because the
$sans("Nested")$ layer recorded this location at the call. By induction on the
run,
#isathm("csim_star") extends the theorem to finite source runs, as in
CompCert's simulation diagrams @leroy09[§4.3].

The initial source configuration is related to the node after the
#isaconst("EA_Body") edge of `main` (#isathm("compile_prog_main_base")).
Therefore, if a finite source run of a well-formed program reaches
$(c, s, italic("frs"))$, a graph run from the entry reaches some
$(v, s, italic("stk"))$ that #isaconst("csim") relates to it. The program
points of a source configuration are the nodes $v$ related to it in this way.
At each of them, the store $s$ of the source execution is a store of a graph
run, which is the first inclusion of the soundness chain of @fig:intro-nest. A
check is found in the graph by its label, the source position it carries. If
the residual is about to run a check, every node related to it has an
#isaconst("EA_Check") edge with the same label and condition
(#isathm("csim_next_check_edge")). Flat
runs, however, do not record which activation a store belongs to, and a
context-sensitive analysis needs this. @ch:traces therefore regroups graph
runs into activation traces.
