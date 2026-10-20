#import "@preview/fletcher:0.5.8": diagram, edge, node
#import "../lib/math.typ": *
#import "../lib/figures.typ": *
#import "../lib/code.typ": *
#import "../lib/claims.typ": claim-ref
#import "../lib/stats.typ": stat
#import "../lib/sources.typ": thy

// The call run_voblint received and the answer it returned (claim shell-json),
// folded for print: `rule(path)` keeps a value "open" (one key per line),
// prints it "full" on one line, or "fold"s it to {…} or […×n]. The excerpt is
// derived from the claim, so it cannot drift from what the analyzer returns.
#let _shell = json(bytes(read("/shared/generated/shell-json.txt")))
#let _fold(v, rule, path: "", depth: 0) = {
  let pad = " " * (depth + 1)
  let mode = rule(path)
  if type(v) == dictionary {
    if mode == "fold" { "{…}" } else if mode == "full" { json.encode(v, pretty: false) } else {
      let items = v
        .pairs()
        .map(((k, x)) => (
          pad + json.encode(k) + ": " + _fold(x, rule, path: path + "." + k, depth: depth + 1)
        ))
      ("{\n" + items.join(",\n") + "\n" + " " * depth + "}")
    }
  } else if type(v) == array {
    if v.len() == 0 { "[]" } else if mode == "fold" { "[…×" + str(v.len()) + "]" } else if (
      mode == "full"
    ) {
      json.encode(v, pretty: false)
    } else {
      let items = v.map(x => pad + _fold(x, rule, path: path + ".#", depth: depth + 1))
      ("[\n" + items.join(",\n") + "\n" + " " * depth + "]")
    }
  } else { json.encode(v, pretty: false) }
}
#let _main = ".p.prog_" + "main"
#let _in-rule(path) = if path in ("", ".p", _main) { "open" } else if path.starts-with(".p.") {
  "fold"
} else { "full" }
// JSON keys that name HOL constants are spelled in two parts, so the reference
// check does not read them as constants written in prose.
#let _checks = ".Analysed.res_" + "checks"
#let _out-rule(path) = if path in ("", ".Analysed", _checks, _checks + ".#") {
  "open"
} else if path.starts-with(_checks + ".#.") { "full" } else { "fold" }

= The Executable Analyzer <ch:executable>

@ch:results proved that every report #isaconst("run_voblint") returns is
sound. A user, however, does not evaluate a HOL function. The user writes
source text and reads a report in a terminal or a browser tab. Between the
two, the proved function has to become a program. Its abstract states are
mathematical functions, which code cannot compute with, so they are first
replaced by finite representations (@sec:represented-function). Isabelle's
code generator then exports #isaconst("run_voblint") to OCaml
(@sec:codegen), and an unverified shell of handwritten OCaml parses the source text and displays
the report (@sec:ocaml-boundary). The change of representation is proved
to preserve the theorem. The code generator and the shell are not proved
correct, so the guarantee for the running tool also rests on them, as
@fig:intro-trust shows.

== Finite representations of abstract states <sec:represented-function>

To export #isaconst("run_voblint") as code, every function it calls must be
computable. Most of the development already is, since its datatypes and
recursive functions translate directly into a functional program, but the
concretizations and the pointwise states do not. The concretization $conc$ maps an abstract value to a possibly infinite set of integers, and in general
no program can compute such a set. The analyzer does not need to, because
$conc$ only states what a value means. This is why the domain interface
separates #isalocale("executable_domain") from the classes and locales
below it in @fig:domain-carrier, which add $conc$ and its laws. Code
generation exports the executable part together with each domain's operation
record, and the rest serves only the proofs.

The pointwise states of @ch:domains are total functions on
infinitely many variable names, so the solver could not even test whether two
of them are equal. Following Concrete Semantics @nipkow14[§13.6], an
_executable state_ (#isatype("default_st")) instead stores a default value and
a finite list of overrides. Voblint keeps two such pairs, one for locals with
default #ltop and one for globals with default $0^sharp$, because VIMP
initializes globals to zero as C does for static storage (#c11("6.7.9p10")).
After `x = 0` in `main`, for example, the local part holds the default #ltop
and the single override $x |-> absval(ivl(0, 0))$, and every other local still
reads #ltop. Since several lists describe the same state, a quotient type
@huffman13 identifies the lists that answer every lookup alike. Order and
equality then depend only on the defaults and the finitely many listed names,
and every operation is computed on exactly these. Each operation therefore
agrees with its counterpart on pointwise states, and the soundness results of
@ch:analysis-interface carry over to the code that runs
(#isathm("exec_local_spec_sound")).

With concretizations left to the proofs and pointwise states replaced, nothing
else stands in the way. The verified TD solver already comes with an executable
version, #isaconst("solve_c", thy: "TD_side_upd_rule"), which Tilscher et al.
refine from its definition @tilscher26, and @sec:certificate shows that every
run of it that returns satisfies the solver's correctness theorem. The values of the numeric domains (@sec:instances-supply) and the
states of the order analysis (@sec:rel-state) are already finite data.

== Exporting the analyzer to OCaml and WebAssembly #thy-badge("Voblint_Codegen", "Voblint_Codegen") <sec:codegen>

With these replacements, every function that #isaconst("run_voblint") uses
has code equations, and Isabelle's
code generator @haftmann10 can export it. One #isacmd("export_code")
declaration emits #isaconst("run_voblint"), #isaconst("render_report"), and the
constructors and selectors a caller needs into one OCaml file,
#link(repo-blob + "codegen/generated/ml/Voblint_Generated.ml")[`Voblint_Generated.ml`].
Both delivered tools call this module through the facade
#link(repo-blob + "cli/voblint.ml")[`cli/voblint.ml`], which re-exports the
generated module unchanged. Every analysis result is therefore computed by generated
code.

The command-line tool links the module with the handwritten OCaml into a native
program. For the playground, #raw("wasm_of_ocaml", lang: "sh") compiles the
same code to WebAssembly, which a web worker in the reader's browser calls
(@fig:build). Both tools thus run the generated code of #isaconst("run_voblint") up to the code generator and the compilers
(@fig:intro-trust).

#figure(
  image("/shared/generated/svg/build.svg", width: 100%),
  placement: none,
  caption: [How the generated #isaconst("run_voblint") reaches the browser. Build:
    #isacmd("export_code") writes #isaconst("run_voblint") into
    `Voblint_Generated.ml`, which `dune` and #raw("wasm_of_ocaml", lang: "sh")
    compile with the handwritten OCaml into a WebAssembly bundle. Run: a web
    worker calls the bundle and returns the answer as JSON. Adapted from the
    project site.],
) <fig:build>

#let _bench = json("/shared/generated/bench-init-publications.json").programs
#let _speedup(prog) = {
  let r = _bench.at(prog)
  str(calc.round(r.before.mean_s / r.after.mean_s, digits: 0))
}

The generated module has #stat("generated_ocaml") lines and follows the proofs rather than the
habits of OCaml programmers, which makes it hard to read. Type classes become records of operations passed
as arguments, finite sets and maps become lists that every lookup scans, and
the solver keeps its valuation as a chain of closures, one per update.

The code that runs is a small part of the development (@tab:sizes). Code
generation keeps only the definitions that #isaconst("run_voblint") depends on and
drops every proof, so the theories and the imported part of the vendored TD solver shrink
to the generated module. The handwritten OCaml around this module is smaller
still. Of the code that runs, it is the only part that has to be checked by
hand, alongside the trusted code generator and OCaml compiler.

#figure(
  {
    set text(size: 9pt)
    table(
      columns: (auto, auto, auto),
      align: (left, right, left),
      stroke: none,
      inset: (x: 5pt, y: 3pt),
      table.hline(),
      [*part*], [*size*], [*status*],
      table.hline(stroke: 0.5pt),
      link(repo-blob + "codegen/generated/ml")[generated OCaml analyzer],
      [#stat("generated_ocaml") lines],
      [generated from the proved #isaconst("run_voblint")],
      link(site("Voblint/index.html"))[Isabelle theories],
      [#stat("isabelle.lines") lines],
      [proved, #stat("isabelle.theories") theories],
      link(site("Unsorted/TD/index.html"))[vendored TD solver, imported part],
      [#stat("solver.used.lines") lines],
      [proved by Tilscher et al. @tilscher26],
      link(repo-blob + "cli")[handwritten OCaml],
      [#stat("handwritten_ocaml") lines],
      [outside the proof (@sec:ocaml-boundary)],
      link(repo-blob + "tests/regression")[regression programs],
      [#stat("corpus.cases") programs],
      [tested, not proved (@sec:eval-corpus)],
      table.hline(),
    )
  },
  placement: auto,
  caption: [The parts of the development by size and status. Line counts
    are measured on the repository at build time.],
) <tab:sizes>

The proofs say nothing about running time, and the generated code can be very
inefficient. Profiling revealed one case. A sampling profile of a program with
256 chained assignments attributed most of the CPU time to a single
function. The generated
code of #isaconst("init_publications") recompiled the whole program at every
equation evaluation, because its definition names the program's entry through the compiler from
VIMP to control-flow graphs (@sec:compile). A proved code equation that names the entry directly fixed this
without changing any theorem (#isathm("init_publications_code")), and on the same machine, the chain of 256 assignments then ran
#_speedup("chain256") times faster and a program of 512 assignments in
procedures of eight statements #_speedup("procs512") times faster, in one
measurement each
(#link(repo-blob + "thesis/shared/generated/bench-init-publications.json")[recorded]).
Finding further inefficiencies and improving the generated code is future work.

== Tracing solver steps without changing the proofs #thy-badge("Voblint_Solver", "Solver_Trace") <sec:tracing>

To explain a run, the command-line tool and the playground can trace the
solver's steps. The solver trace records when each unknown is queried, which update
destabilizes which unknown, and where widening applies. Goblint's tracing of
its top-down solvers reports the same events. Tracing must leave the definitions and proofs of
the vendored TD solver @tilscher26 untouched. Voblint therefore adds tracing only to the equations
that code generation translates. Every traced equation reports each step
through one constant, #isaconst("trace_event"), which is defined as the unit
value $()$ and so does nothing in the logic. Each traced equation is thus
provably equal to the one it replaces (for example,
#isathm("solve_rec_c_traced")). Isabelle's code generator takes the
equations it translates from a set of _code equations_, which a theory may
change. The theory removes the vendored TD solver's equations from this set
(`[code del]`) and declares the traced ones instead (`[code]`), so the
vendored definitions and proofs stay untouched, and one generated analyzer
serves traced and untraced runs alike. A #isacmd("code_printing") declaration then tells the code generator to emit,
in place of #isaconst("trace_event"), a call to the handwritten OCaml function
`Solver_trace_hook.emit`. The hook receives a suspended event and builds it
only when tracing is on, so an untraced run records nothing. The hook joins the trusted base and must return, raise nothing, and leave the
solver's values alone.

The command-line tool prints the events with `--trace`, and the playground
replays them step by step on the solved graph (@fig:replay-still). The replay
shows the order of the solve, which the solved values alone hide, such as when
a call creates a new callee context. The solver trace itself is unverified, but it
never feeds back into a result, so a report computed with tracing on is the
same report as without it.


#pagebreak(weak: true)
== Unverified parsing, rendering, and playground <sec:ocaml-boundary>

The generated #isaconst("run_voblint") works on a syntax tree and returns a
typed answer, whereas a user writes source text and reads a report.
Unverified handwritten OCaml bridges both ends. On the input side, an
`ocamllex` lexer and a Menhir parser turn the source text into an
#isatype("imp_prog") and record each check's source position in its label. On
the output side, the generated #isaconst("render_report") turns the report's
states into text, and handwritten OCaml either prints the command-line report,
placing each check at the position its label carries, or serializes the answer
as JSON, from which the playground draws the graph and marks the verdicts and
diagnostics in the editor. The command-line tool and the playground share the
parser, the generated module, and the code that turns a request into an
analysis configuration. They differ only in their surroundings, since the
command-line tool manages processes and files, and the playground's worker
exchanges JSON with the page. The code generator maps HOL's integers to
arbitrary-precision Zarith integers, as VIMP requires (@sec:vimp-vs-c).

@fig:shell shows, for the program below, the call that #isaconst("run_voblint")
receives and the answer it returns once #isaconst("render_report") has turned
the states into text, serialized as for the playground.

#listing(lang: "c", claim: "shell-json", read("/shared/programs/shell-json.vimp").trim())

#figure(
  {
    set text(size: 6pt)
    show raw: set text(size: 6pt)
    grid(
      columns: (1.3fr, auto, 1.45fr),
      column-gutter: 3pt,
      align: (left + horizon, center + horizon, left + horizon),
      [*call* \ #raw(_fold(_shell.input, _in-rule), block: true, lang: "json")],
      diagram(
        spacing: (3mm, 0mm),
        stage((1, 0), [#isaconst("run_voblint")], kind: "proved", inset: 5pt),
        flow((0, 0), (1, 0)),
        flow((1, 0), (2, 0)),
      ),
      [*answer* \ #raw(_fold(_shell.output, _out-rule), block: true, lang: "json")],
    )
  },
  kind: image,
  placement: none,
  caption: [The input and output of the generated analyzer for the program
    above (claim #claim-ref("shell-json")). The call carries the configuration
    and the syntax tree `p` the parser built, of the kind @fig:vimp-ast shows in
    full; the answer carries the report with its states rendered as text, here
    with its one check in full. Everything before the call, and the rendering
    from the answer on, is unverified. `{…}` and `[…×n]` fold parts of the JSON.],
) <fig:shell>

The #link(site("playground.html"))[playground] runs the analyzer in the
browser. Its toolbar sets the configuration of #isaconst("run_voblint") and
toggles the tracing of @sec:tracing, and the end-to-end soundness theorem covers every
configuration it can select (#isathm("run_voblint_source_sound")).
@fig:pg-overview shows one run.

#subfigures(
  playground-figure(
    "while-loop",
    width: 68%,
    [one run in three views: the check's verdict in the editor, the state
      inspector at the check, and the solved graph. Settings
      #playground-settings("while-loop")],
  ),
  <fig:pg-overview>,
  playground-figure(
    "solve-replay-still",
    width: 66%,
    [one step of the solver replay for the calls of `bump`: the
      graph shows each unknown's value at this step, and the solver trace beside it
      marks the step's line. Settings #playground-settings("solve-replay-still")],
  ),
  <fig:replay-still>,
  columns: (1fr,),
  gutter: 1.2em,
  placement: none,
  caption: [The playground. Both panes run the generated analyzer of
    @fig:build in the reader's browser. The screenshots are illustrative.],
  label: <fig:playground>,
)

== Testing the unverified components <sec:eval-corpus>

The handwritten OCaml around the generated analyzer (@tab:sizes) is tested.
A #link(repo-blob + "tests/regression")[regression corpus] of
#stat("corpus.cases") VIMP fixtures pins the expected verdicts: a definite one
in `precision/`, #verdict("UNKNOWN") in `soundness/`, and a documented loss in
`known-imprecision/`. #link(repo-blob + "tests/solver-trace")[Golden files] pin
solver traces (@sec:tracing), and property tests check that the parser reads
back random syntax trees.
