#import "@preview/fletcher:0.5.8": diagram, edge, node
#import "../lib/math.typ": *
#import "../lib/theme.typ": vb
#import "../lib/figures.typ": *
#import "../lib/code.typ": *
#import "../lib/sources.typ": proved, thy

// A row of a registered CLI claim (shared/claims.toml), so a verdict or state
// quoted in prose is read from the checked output rather than typed.
#let cli-row(name, cond) = {
  let cells = read("/shared/generated/" + name + ".txt")
    .split("\n")
    .map(l => l.trim().split(regex("\s{2,}")))
    // A DEAD row has no state column.
    .find(c => c.len() >= 4 and c.at(2) == cond)
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

What does a user actually run, and where does the proof stop? The theorems of
@ch:results are about #isaconst("run_voblint"), a HOL function from a VIMP
syntax tree and an analysis configuration to an analysis answer. A user has source text
and wants a report. Code generation, a compiler, a parser, and a renderer lie
between the two, and the theorem covers none of them. The delivered tools run
the constant the theorem is about, which gives the executable half of the
end-to-end result. @sec:trust-boundary states where the proof ends and which
trusted components remain.

== Code generation and the public interface <sec:codegen>

The theorems of @ch:results are about a HOL function, but a user runs an OCaml
program. Voblint closes this gap by exporting the theorem's own constant: the
command-line tool and the playground call the generated code of
#isaconst("run_voblint"), so the theorems speak about the function they run,
up to the code generator and the OCaml toolchain (@sec:trust-boundary).

#thy("run_voblint")

Without a report, the result says why: #isaconst("Invalid_Activation") for an
empty or duplicated list of analyses, #isaconst("Malformed_Program") for a
program that fails the structural conditions of compilation, and
#isaconst("No_Answer"), the logical case in which the solver returns nothing.
#isaconst("Analysed") carries an #isatype("analysis_report") of semantic
values, one combined state per solved point and context with its verdicts.
#isaconst("render_report") turns them into strings, which no theorem reads.

What a user reads off a report, one check verdict or diagnostic at a time, is
stated by the theorems of @sec:verdicts, all derived from
#isathm("run_voblint_source_sound").

Export needs code equations for everything #isaconst("run_voblint") uses.
Two objects of the soundness argument have none, and @ch:solving replaces
both: the semantic state by the finite carrier #isatype("default_st"), and the
solver specification by the vendored solver's executable version
@tilscher26. One #isacmd("export_code") declaration emits
#isaconst("run_voblint"), #isaconst("render_report") and the constructors a
caller needs into
#link(repo-blob + "codegen/generated/ml/Voblint_Generated.ml")[`Voblint_Generated.ml`].
Handwritten OCaml reaches it only through the facade
#link(repo-blob + "cli/voblint.ml")[`cli/voblint.ml`]. One entry point for
every analysis configuration also means no handwritten code chooses between analyses or
policies.

The same constraint splits the interfaces. A concretization into sets of
integers has no code equation, so it must stay out of the generated code. The
domain classes therefore separate the runtime operations
(#isalocale("executable_domain")) from the concretization and its laws
(#isalocale("numeric_domain"), @fig:domain-carrier). Likewise
#isalocale("dg_pipeline") fixes the executable ingredients without
assumptions, so its definitions become code equations, and
#isalocale("dg_analysis") adds the soundness contracts (@sec:cert-param). The
analyzer interprets #isalocale("dg_analysis") once per context family and
placement of program globals, for any activation list, so every run inherits
the argument of @ch:results.

== The frontend and the browser artifact <sec:ocaml-boundary>

The generated module takes a syntax tree and returns a typed answer, so
unverified OCaml surrounds it on both sides (@fig:intro-trust). Before it, an
`ocamllex` lexer and a Menhir parser turn source text into an
#isatype("imp_prog") and write each check's source position into its label.
After it, #isaconst("render_report") turns the report into displayed values,
and handwritten code builds the contextual graph from the routes the answer
reports, prints each check row at the position its label carries, and places
arithmetic diagnostics by statement order. For a
#isaconst("Malformed_Program") answer it names the first well-formedness
conjunct the program breaks. The rejection itself is decided by the generated
test. Integers in the export are arbitrary-precision Zarith integers, matching
VIMP's mathematical integers (@sec:vimp-vs-c).

The command-line tool and the browser adapter link the same generated module
and frontend, and they check a request the same way: one
function turns analysis, update-rule and context names into an analysis configuration,
and each entry words its own error messages. The two stay separate programs,
because the command-line tool runs each analysis in a killable subprocess and
writes report directories, while the adapter is a WebAssembly worker that talks
to the page. The adapter's only exported function calls
#isaconst("run_voblint") once and returns the report, the graph and the typed
answer, decoded by handwritten code, as one JSON string. No theorem states that the graph and the
report come from the same answer. We establish this by reading the adapter.

The playground,
#link("https://manuellerchner.github.io/Voblint-Verification-Master-Thesis/playground.html")[`manuellerchner.github.io/Voblint-Verification-Master-Thesis/playground.html`],
is a static page that runs this adapter in the reader's browser. Its toolbar
selects exactly the arguments of #isaconst("run_voblint"), so every selectable
run lies within the analysis configurations covered by
#isathm("run_voblint_source_sound"), subject to its input premises.
@fig:pg-overview shows the default program, analyzed with Interval and the
order analysis under call strings of depth one. It contains a
#cli-verdict("pg-overview", "i == 3") check, a
#cli-verdict("pg-overview", "n == 7") check, a
#cli-verdict("pg-overview", "i == 0") check inside a branch no run takes, and a
possible division by zero. The screenshot is illustrative evidence
(@ch:evaluation). The verdicts quoted here come from command-line runs of the
same generated core, registered as claims and re-executed by the build.

#playground-figure(
  "overview",
  crop: (0.005, 0.005, 0.61, 0.795),
  width: 70%,
  placement: auto,
  [The editor pane of one run: the verdicts in the badges after the checks,
    the abstract values after each assignment, and the arithmetic warning at
    `q = 100 / x`. The run's graph pane and state inspector are omitted.
    Settings #playground-settings("overview")],
) <fig:pg-overview>

== Watching the solve <sec:tracing>

A post-solution certificate states that the solver's result bounds the
equations; it says nothing about how the solver reached it. For explaining a
run and for debugging an analysis, the order of the steps matters: which
unknown is queried when, which update destabilizes whom, where widening sets
in. @tab:eq-trace shows such a sequence for the calls of `bump` in the running
example of @ch:equations (@sec:eq-example), where each call publishes its
entry state to the callee's seed before the callee is read.

*Tracing inside the export.* The executable solver reports its steps through
one constant, #isaconst("trace_event"), which takes a channel name and a
suspended event and is $()$ in the logic. Alternative code equations for the
solver call it at each step, and because it is $()$, each is proved equal to
the vendored equation it replaces by unfolding it
(#isathm("solve_rec_c_traced")); the context policies and the reading of the
result are traced the same way (#isathm("trace_route"), #isathm("trace_run")). Code export
uses the traced equations and drops the originals, so the vendored definitions
and proofs stay untouched, and a traced and an untraced run execute the same
generated code. The only addition to the trusted base (@sec:trust-boundary) is
the target-language mapping that sends #isaconst("trace_event") to an OCaml
hook. Like every other such mapping, the hook must return, raise nothing and
leave the solver's values alone; it forces the suspended event only when
tracing is on. Evaluation inside Isabelle has no mapping and runs the
equation, so proofs by evaluation see no hook. A gate checks after each code
export that the trace calls survive in the generated module and that traced
and untraced runs print the same result on the regression corpus.

*Events.* The events (#isatype("solver_event")) follow the steps Goblint's
tracing of its top-down solvers reports: queries and their answers, iterations,
evaluations of a right-hand side, updates with their widening, side effects,
influences and destabilizations. A few have no counterpart there, among them
the value a right-hand side returns and the start and end of a solve. The
verbose output prints them in Goblint's tracing format, indented by query
depth; the CLI documentation maps each line to its Goblint counterpart. As in
Goblint, a query names the unknown that asks it, and a program point carries
its statement and source line.

*Replay.* The playground records the trace in the same solve that computes the
result shown. It folds the run's events, as JSON Lines, through one reducer
into the state at every step: node values, the stack of open queries,
the stable set, influences, widening points and the global unknowns, which are
the seeds and, under flow-insensitive program globals, one unknown per global. It draws that state
on the graph beside the verbose trace, and each step names the trace line it
comes from. @fig:replay-still shows one step; @fig:eq-walk is drawn from the
same events.

#playground-figure(
  "solve-replay-still",
  width: 100%,
  placement: auto,
  [One step of the solve replay on the example of @tab:eq-trace: the first call
    of `bump` asks for the callee's result, and the callee's entry reads its
    seed. The
    graph shows each unknown's value at this step, and the trace beside it marks
    the step's line under a banner naming the call. Captured from the
    playground; the project site shows the whole replay as an animation
    (#link("https://manuellerchner.github.io/Voblint-Verification-Master-Thesis/#verified")[site]).
    Settings #playground-settings("solve-replay-still")],
) <fig:replay-still>

*What the trace is.* The result is the exported computation of proved
equations. The trace is an unverified observation of that computation, and
the replay an unverified visualization of the trace. Neither feeds back into a
result.

The command-line tool records the same trace (#raw("voblint --trace", lang: "sh")),
as text or as JSON Lines. @tab:eq-trace and @fig:eq-walk are generated from
such a trace, registered as a claim.

== What remains outside the proof <sec:trust-boundary>

Three questions determine what a run of the delivered analyzer establishes, and
@fig:intro-trust places each component under one of them.

*What is proved.* #isathm("run_voblint_source_sound") (@sec:headline) and the
verdict theorems of @sec:verdicts hold for every report #isaconst("run_voblint")
returns, so termination is not a premise. The proved side includes the compiler,
the well-formedness test, the vendored solver with its executable refinement,
and the finite carrier. The vendored solver's changes (@sec:upstream-td) are
checked by Isabelle like every other theory. The proved side ends at two
points: the syntax tree #isaconst("run_voblint") receives, and the semantic
report it returns, before #isaconst("render_report") turns its states into text
(@sec:codegen). No theorem constrains `UNKNOWN` verdicts or
warnings.

*What is trusted.* The delivered guarantee also relies on the following
components, which the theorem does not mention.

- The lexer and parser. A fault builds a syntax tree other than the one the
  text denotes, and the verdicts then describe another program.
- Isabelle's kernel, and its code generator with the library's target
  mappings (#isacmd("code_printing")), which send HOL integers to Zarith and
  HOL strings to OCaml strings. The code equations of the development are
  theorems. The translation to OCaml and these mappings are not, although
  Haftmann and Nipkow give the generator's source and intermediate language a
  semantics and prove the translation of type classes correct on paper
  @haftmann10. Witness theorems proved by `eval`, such as the
  non-vacuity instances of @sec:nonvacuity, trust the same generator inside
  Isabelle.
- The mapping of #isaconst("trace_event") to the tracer's OCaml hook
  (@sec:tracing). The traced code equations are theorems; the hook must return,
  raise nothing and leave the solver's values alone, like every other target
  mapping.
- The OCaml compiler and runtime, #raw("wasm_of_ocaml", lang: "sh") with the
  #raw("js_of_ocaml", lang: "sh") runtime library, Zarith with its JavaScript stubs, and the
  browser. They run the generated code.
- #isaconst("render_report"), the display functions of the analyses and
  #isaconst("string_of_abstract_value"). They are HOL code, but no theorem says
  the text they produce describes the state it was produced from.
- The handwritten adapter and rendering code. They decode the answer, draw the
  graph, print each check row at its label and place
  arithmetic diagnostics at statement positions. The message naming the first
  broken well-formedness conjunct restates the conjuncts by hand. A fault in the parser's labels or in this placement
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
contradicts nothing, since the theorem speaks only about returned reports. A
timeout establishes only
that the run did not finish within its budget. It yields no verdict and does
not show that the solver diverges. A hang may come from the solve, from the
fixpoint reduction of Int (@ch:instances), or from the toolchain
and the browser. An abort branch of a code equation, such as the query
recursion exceeding #isaconst("query_depth"), raises an
exception and yields no answer.

The delivered tools thus run the proved constant. The trust boundary consists
of the frontend, the code generator's translation and target mappings, the
compilers and runtimes, the rendering, and the argued adequacy of
#isaconst("pstep").
