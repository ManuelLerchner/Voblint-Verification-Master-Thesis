#import "@preview/fletcher:0.5.8": diagram, node
#import "../lib/math.typ": *
#import "../lib/theme.typ": vb
#import "../lib/figures.typ": *
#import "../lib/code.typ": *
#import "../lib/sources.typ": thy

// A row of a registered CLI claim (shared/claims.toml), so a verdict or state
// quoted in prose is read from the checked output rather than typed.
#let cli-row(name, cond) = {
  let cells = read("/shared/generated/" + name + ".txt")
    .split("\n")
    .map(l => l.trim().split(regex("\s{2,}")))
    .find(c => c.len() == 5 and c.at(2) == cond)
  assert(cells != none, message: "claim " + name + " has no check " + cond)
  cells
}
#let cli-verdict(name, cond) = raw(cli-row(name, cond).at(3))
// One verdict shared by several (claim, condition) rows; fails if they differ.
#let cli-same(..rows) = {
  let vs = rows.pos().map(((name, cond)) => cli-row(name, cond).at(3))
  assert(vs.dedup().len() == 1, message: "verdicts differ: " + repr(vs))
  raw(vs.first())
}

= From Formalization to Executable Analyzer <ch:executable>

The theorems of @ch:results are about #isaconst("run_voblint"), a HOL function
from a VIMP syntax tree and a configuration to an analysis answer. A user has
source text and wants a report. Code generation, a compiler, a parser, and a renderer lie
between the two, and the theorem covers none of them. The delivered tools run
the constant the theorem is about, which gives the executable half of the
end-to-end result. @sec:trust-boundary states where the proof ends and which
trusted components remain.

== Code generation and the public interface <sec:codegen>

The source-level theorem is stated about one HOL function, and the delivered
tools call that function:

#thy("run_voblint")

The first three arguments are the configuration: the domain
(#isatype("analysis_domain")), the global update rule
(#isatype("globals_rule")), and the context policy (#isatype("context_mode"): no
contexts, entry states, or call strings of a given depth). The fourth is the
syntax tree, of type #isatype("imp_prog"). #isaconst("analyse_program") first
checks the structural conditions compilation requires
(#isaconst("wf_program_compile_input_exec")) and returns
#isaconst("Malformed_Program") on failure. Otherwise it compiles and solves, and
#isaconst("Analysed") carries a #isatype("run_result") record: the CFG, the
contexts, one state per solved point and context with its verdicts and
arithmetic diagnostics, the call routes, the check rows, and the solved global
unknowns.

The verdicts are values of a HOL datatype, computed in HOL and constrained by
the theorem. The abstract values are not: #isaconst("run_voblint") maps each
through #isaconst("string_of_abstract_value"), and the coverage half of the
source theorem is stated about the result before this map
(#isaconst("analysis_result_covers")). No theorem constrains the strings.

Export requires executable code equations for the whole dependency closure. Two
objects of the soundness argument have none, and @ch:solving replaces both. The
semantic state, a function on an infinite set of variables, becomes the finite
carrier #isatype("resolved_st_q"). The solver specification, a recursion whose
termination is not known in general, gets the vendored solver's executable
version as its code equation, which the vendored library proves from their
agreement wherever the specification is defined @tilscher26. Outside that
domain the equation aborts. Both replacements are proved, and neither proves
termination (@sec:termination). One #isacmd("export_code")
declaration then emits #isaconst("run_voblint") and the constructors and
selectors a caller needs as the OCaml module `Generated`.

Because the export is the theorem's own constant, no handwritten entry point
needs an agreement argument. One exported entry point per domain and context
policy would need a lemma relating each of them to the theorem's constant. The single
dispatcher answers every combination of its three configuration arguments, so
the command-line tool never decides which combination is legal.

== Interfaces that separate execution from proof <sec:engineering>

Two requirements of code generation shape the interfaces between execution and
proof. First, a type-class constraint becomes a dictionary of operations passed
at run time. A class holding both the operations of a domain and its
concretization would put the concretization into every dictionary, and a
function into sets of integers, such as the residue class of a congruence, has
no executable code equation in general. The domain classes therefore split
(@fig:domain-contract): #isalocale("executable_domain") holds the runtime
operations and #isalocale("sound_domain") adds the concretization and its
laws. The executable pipeline and the solver's class
#isalocale("bounded_warrowing") mention only the former. A type has at most one
instance of each class, while transfer functions, routing policy and solver
vary over one carrier. They are therefore locale parameters.

Second, code generation needs unconditional equations, and theorems about the
result need semantic premises. #isalocale("routed_dg_pipeline") fixes the
executable ingredients (transfer, entry, initial state, routing, solver, check
classifier) and assumes nothing, so its definitions become code equations
directly. Even the bottom state is a parameter, because a least element taken
from a type class would have to be executable at a function type.
#isalocale("routed_dg_analysis") imports it, strengthens the value type to
#isalocale("sound_domain"), and adds the contracts, among them soundness of the
abstract transfer and of the initial state, agreement of the executable
transfer, entry and routing with their abstract counterparts, the solver
certificate, discharge of the termination premise by a finished executable
run, and correctness of the check classifier. Each domain interprets this
locale once per context family (@fig:assembly) and inherits the argument of
@ch:results. The assembly fixes a reachability-lifted whole-store carrier, so
the relational witness of @ch:instances is not selectable through it.

#figure(
  {
    set text(size: 8pt)
    set par(first-line-indent: 0pt, justify: false)
    let loc(pos, name, note, color: vb.neutral) = node(
      pos,
      align(center)[#name \ #text(size: 7.5pt, fill: vb.muted, note)],
      stroke: 0.8pt + color,
      fill: color.lighten(93%),
      corner-radius: 2pt,
      inset: 5pt,
    )
    let inst(pos, body) = node(
      pos,
      align(center, text(size: 7.5pt, body)),
      stroke: (paint: vb.proved, thickness: 0.7pt, dash: "dotted"),
      corner-radius: 2pt,
      inset: 4pt,
    )
    let lab(body) = text(size: 7pt, fill: vb.muted, body)
    diagram(
      spacing: (9mm, 8mm),
      loc((1, 0), isalocale("routed_dg_pipeline"), [executable ingredients, no assumptions \
        definitions exported as code equations]),
      loc(
        (1, 1),
        isalocale("routed_dg_analysis"),
        [adds the contracts; value type \
          strengthened to #isalocale("sound_domain")],
        color: vb.proved,
      ),
      loc(
        (2.3, 1),
        isalocale("unit_dg_analysis"),
        [the same at the one-element \
          context space],
        color: vb.proved,
      ),
      inst((0.3, 2), [five domains \ entry-state contexts]),
      inst((1.5, 2), [five domains \ call strings of depth $k$]),
      inst((2.7, 2), [five domains \ no contexts]),
      import-edge((1, 0), (1, 1), label: lab[extends], label-side: left),
      import-edge((1, 1), (2.3, 1), label: lab[specializes]),
      interp-edge((1, 1), (0.3, 2)),
      interp-edge((1, 1), (1.5, 2)),
      interp-edge((2.3, 1), (2.7, 2)),
    )
  },
  kind: image,
  caption: [The analysis assembly. Solid arrows are locale extension, dotted
    ones global interpretations, one per domain and context family. Each
    interpretation keeps the global update rule, and for call strings the
    depth $k$, as a parameter, so one registration serves every rule and
    every depth.],
) <fig:assembly>

== The OCaml and browser boundary <sec:ocaml-boundary>

The generated module takes a syntax tree and returns a typed answer, so
unverified OCaml surrounds it on both sides (@fig:intro-trust). Before it, an `ocamllex` lexer and a Menhir parser, which a
project script emits from a grammar description, turn source text into an
#isatype("imp_prog") and write each check's source position into its label.
After it, rendering code prints values, builds the contextual graph from the
published routes, prints each check row at the position its label carries, and
places arithmetic diagnostics by statement order. For a
#isaconst("Malformed_Program") answer it names the first well-formedness
conjunct the program breaks. The rejection itself is decided by the generated test.
Integers in the export are arbitrary-precision Zarith integers, matching VIMP's
mathematical integers and not C11's finite ones (@sec:vimp-vs-c).

The command-line tool and the browser adapter link the same generated module
and frontend. The command-line tool runs the analysis in a child process with a
wall-clock budget and reports a run that exceeds it as unfinished, with no
verdicts. For the browser, #raw("wasm_of_ocaml", lang: "sh") compiles the
adapter into a WebAssembly module that runs in a Web Worker the user can
cancel. Its only exported function calls #isaconst("run_voblint") once and
returns the report, the graph, and the raw typed answer as one JSON string.
No theorem states that the graph and the report come from the same answer. We
establish this by reading the adapter.

== An interactive analyzer artifact <sec:playground>

The playground,
#link("https://manuellerchner.github.io/Voblint-Verification-Master-Thesis/playground.html")[`manuellerchner.github.io/Voblint-Verification-Master-Thesis/playground.html`],
is a static page that runs the generated analyzer in the reader's browser. Its
toolbar selects exactly the arguments of #isaconst("run_voblint"), so every
selectable run lies within the configurations covered by
#isathm("run_voblint_certified_source_sound"), subject to its input and
termination premises. Verdicts and value hints appear in the source, a state
inspector shows the abstract state under the cursor in every context it was
solved at, and the graph draws one box per procedure and context, the unknown
space of @ch:equations.

The figures below are captured runs of the page, each linked to the run it
shows. They are illustrative evidence (@ch:evaluation): the build checks each
screenshot and program against the captured copy, not against the analyzer.
Verdicts, states and diagnostics quoted in the prose come from command-line
runs of the same generated core, registered as claims `pg-*` and re-executed by
the build.

#let _wl = cli-row("pg-while-loop", "0 < x")

*One run, three views.* @fig:pg-while-loop relates the source of one run to
the graph the theorems are about. The check after the loop is
#raw(_wl.at(3)), the inspector shows the state #raw(_wl.at(4)) at the check's
node #raw(_wl.at(1)), and the graph names the same node.

#playground-program("while-loop")

#playground-figure(
  "while-loop",
  width: 88%,
  [A counted loop: the proved check and the inline values in the source, the
    state inspector at the check's node, and the solved graph. Settings #playground-settings("while-loop")],
) <fig:pg-while-loop>

*Every kind of answer.* @fig:pg-overview shows in the editor what
@fig:intro-answers tabulates, for the default program under call strings of
depth one: a #cli-verdict("pg-overview", "i == 5") check, a
#cli-verdict("pg-overview", "i < 5") check, an
#cli-verdict("pg-overview", "a == 2") check, a possible division by zero, and a
`DEAD` statement whose solved state is empty in every context. At this depth the
two calls of `wrap` share one context of `scale`, so `a == 2` stays undecided
although it holds in every execution.

#playground-figure(
  "overview",
  crop: (0.005, 0.005, 0.52, 0.7),
  width: 100%,
  placement: auto,
  [The editor pane of one run: every verdict kind in the badges after the
    checks, the `DEAD` call `record(100)`, and the arithmetic warning at
    `share = 10 / (a - 2)`.
    The run's graph pane and panels are omitted. Settings
    #playground-settings("overview")],
) <fig:pg-overview>

*Diagnostics and verdicts are separate claims.* In @fig:pg-division-definite
the divisor is zero in every live context. Both operations carry the
diagnostic #raw(check-row("pg-division-definite", cond: "ERROR").cond), and
both checks are
#cli-same(("pg-division-definite", "quotient == 0"), ("pg-division-definite", "remainder == 7")),
because VIMP defines `7 / 0` as $0$ and `7 % 0` as $7$ (@sec:vimp-vs-c). Only
the absence of a diagnostic excludes a zero divisor
(#isathm("run_voblint_arithmetic_safe"), @sec:verdicts). In
@fig:pg-division-possible the divisor is a nondeterministic input, so the
division carries a #raw(check-row("pg-division-possible", cond: "WARNING").cond)
and `divisor != 0` is #cli-verdict("pg-division-possible", "divisor != 0"), the
only sound answer, because runs with a zero and with a nonzero divisor both
exist.

#playground-program("division-definite")

#playground-figure(
  "division-definite",
  crop: (0, 0, 0.52, 0.53),
  width: 72%,
  [The editor pane for a divisor that is zero in every live context: two
    errors, and both checks proved; the diagnostics panel is omitted. Settings
    #playground-settings("division-definite")],
) <fig:pg-division-definite>

#playground-program("division-possible")

#playground-figure(
  "division-possible",
  crop: (0, 0, 0.505, 0.47),
  width: 72%,
  [The editor pane for a divisor the state cannot exclude from being zero: a
    warning and an `UNKNOWN` check. Settings #playground-settings("division-possible")],
) <fig:pg-division-possible>

*Contexts in the result.* @fig:pg-contexts runs the program of
@fig:program-to-equations without and with entry-state contexts; the verdicts
are those of @sec:eq-coarse and @sec:eq-call. The inline values list the
callee's state once per context (`#0` for the argument 4, `#1` for 5), and the
graph draws one box of `bump` per context, with the call and return edges
between them.

#playground-figure(
  "contexts",
  width: 100%,
  placement: auto,
  [The running example without contexts, where both checks are `UNKNOWN`, and
    with entry-state contexts, where both are `PROVED`, with the per-context
    values in the source and one graph box per context of `bump`. Settings of
    the lower run and the graph #playground-settings("contexts")],
) <fig:pg-contexts>

*Which component inverts a guard.* In @fig:pg-int-refinement the check
`y == 2` follows from the guard `y + 1 == 3`. Sign, Interval and Parity each
answer #cli-same(
  ("pg-int-refinement-sign", "y == 2"),
  ("pg-int-refinement-interval", "y == 2"),
  ("pg-int-refinement-parity", "y == 2"),
): their backward step for `+` is the identity or, for Parity, absent
(@ch:instances). Congruence inverts the addition, and the product Int, which
contains it, answers #cli-verdict("pg-int-refinement-int", "y == 2").
Congruence alone also answers
#cli-verdict("pg-int-refinement-congruence", "y == 2")\; the screenshot omits
that run.

#playground-program("int-refinement")

#playground-figure(
  "int-refinement",
  width: 88%,
  [The product domain proving `y == 2`, and Sign, Interval and Parity, each run
    alone, answering `UNKNOWN`. Settings
    #playground-settings("int-refinement") for the product; the other panes
    change only the domain.],
) <fig:pg-int-refinement>

== What remains outside the proof <sec:trust-boundary>

Three questions determine what a run of the delivered analyzer establishes, and
@fig:intro-trust places each component under one of them.

*What is proved.* Take an initial store from #isaconst("cinit_stores"), a
finite source execution from it to any point, the termination premise
#isaconst("config_terminates"), and an #isaconst("Analysed") answer of
#isaconst("run_voblint"). Then #isathm("run_voblint_certified_source_sound")
(@sec:headline) gives a graph node that simulates the reached configuration,
at which the store is collected and covered by the typed result table in some
context (#isaconst("analysis_result_covers")), and at which no listed check is
`DEAD`, every `PROVED` condition holds and every `REFUTED` condition fails
(#isaconst("checks_sound_at")). #isathm("run_voblint_dead_check_unreached") and
#isathm("run_voblint_arithmetic_safe") give `DEAD` and the absence of an
arithmetic diagnostic their meaning. The proved side includes the compiler,
the well-formedness test, the vendored solver with its executable refinement,
and the finite carrier. The vendored solver is a local fork of the development of @tilscher26
with two changes: a port to Isabelle2025 and the removal of an unused
assumption from its widening and narrowing classes. Isabelle checks the
modified theories like every other theory, so the changes are recorded for
provenance and add nothing to what is trusted. It ends at three points: the syntax tree
#isaconst("run_voblint") receives, the typed result before its abstract values
are printed by #isaconst("string_of_abstract_value") (@sec:codegen), and the
termination premise, which only a finished run discharges (@sec:termination).
No theorem constrains `UNKNOWN` verdicts or warnings.

*What is trusted.* The delivered guarantee also relies on the following
components, which the theorem does not mention.

- The lexer and parser. A fault builds a syntax tree other than the one the
  text denotes, and the verdicts then describe another program.
- Isabelle's kernel, and its code generator with the library's target
  mappings, which send HOL integers to Zarith and HOL strings to OCaml strings.
  The code equations of the development are theorems. The translation to OCaml
  and these mappings are not. Witness theorems proved by `eval`, such as the
  non-vacuity instances of @sec:nonvacuity and the one-program bound of
  @sec:mixed-flow, trust the same generator inside Isabelle
  (@tab:oracles-audit).
- The OCaml compiler and runtime, #raw("wasm_of_ocaml", lang: "sh"), Zarith
  with its JavaScript stubs, and the browser. They run the generated code.
- The handwritten adapter and rendering code. They print values, draw the
  graph, print each check row at its label and place arithmetic diagnostics
  at statement positions. A fault in the parser's labels or in this placement
  can show a correct answer at the wrong line, and a rendering fault can show
  a wrong state in the inspector. The page's editor and graph libraries only display their output.

Only tests cover these components. A regression can detect a lost source
position, which no proof obligation mentions (@sec:eval-corpus). An earlier renderer paired check rows with positions by
order of occurrence and put verdicts on the wrong lines when `main` precedes a
procedure it calls, because the compiler lays out procedures first. Checks now
carry their positions as labels, and
#fixture("05-checks/precision/03-same_condition_main_first.vimp") pins the
case.

*Whether the definitions are adequate.* Machine checking proves consequences of
the chosen execution rules. It cannot establish that #isaconst("pstep") matches
the language a reader has in mind, or that the verdict semantics of
@sec:verdicts is the guarantee a reader wants. @sec:vimp-vs-c gives the
adequacy argument for the source semantics: which fragment of C VIMP models,
where it departs from C11, and why no external reference semantics anchors it.

*Outputs the theorem says nothing about.* A parse error says nothing about the
program's executions. A #isaconst("Malformed_Program") answer says that the
input failed the generated well-formedness test. A run that does not return
contradicts nothing, since termination is a premise. A timeout establishes only
that the run did not finish within its budget. It yields no verdict and does
not show that the solver diverges. A hang may come from the solve, from the
fixpoint reduction of the Int product (@ch:instances), or from the toolchain
and the browser. An abort branch of a code equation, such as the solver's
outside its domain, raises an exception and yields no answer.

The delivered tools run the constant the source-level theorem is about, through
code equations that are theorems. The trust boundary consists of the frontend, the code generator's
translation and target mappings, the compilers and runtimes, and the rendering
code, together with the argued adequacy of #isaconst("pstep").
