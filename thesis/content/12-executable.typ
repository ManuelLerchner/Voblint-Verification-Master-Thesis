#import "@preview/fletcher:0.5.8": diagram
#import "../lib/math.typ": *
#import "../lib/figures.typ": *
#import "../lib/code.typ": *
#import "../lib/claims.typ": claim-ref

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

= From Theorem to Tool <ch:executable>

@ch:results proved that every report #isaconst("run_voblint") returns is
sound. A user, however, does not evaluate a HOL function. The user writes
source text and reads a report in a terminal or a browser tab. This chapter
shows how the proved function becomes the analyzer that runs, and where between
the source text and the displayed report the proof stops.

== From theorem to code #thy-badge("Voblint_Codegen", "Voblint_Codegen") <sec:codegen>

@ch:solving replaced the two objects of the argument that cannot run by
executable versions
(@sec:represented-function, @sec:termination). Every function that
#isaconst("run_voblint") uses therefore has code equations, and Isabelle's
code generator @haftmann10 can export it. One #isacmd("export_code")
declaration emits #isaconst("run_voblint"), #isaconst("render_report") and the
constructors a caller needs into one OCaml module,
#link(repo-blob + "codegen/generated/ml/Voblint_Generated.ml")[`Voblint_Generated.ml`].
This module contains the analyzer core that both delivered tools run. The
command-line tool and the playground reach it only through the facade #link(repo-blob + "cli/voblint.ml")[`cli/voblint.ml`], and no handwritten code takes part in computing an analysis result.

The command-line tool links the module with handwritten adapters into a native
program. For the playground, #raw("wasm_of_ocaml", lang: "sh") compiles the
same code to WebAssembly, which a web worker in the reader's browser calls
(@fig:build). Both tools thus run the generated code of #isaconst("run_voblint"), the
function the theorems are about, up to the code generator and the compilers
(@sec:trust-boundary).

#figure(
  image("/shared/generated/svg/build.svg", width: 100%),
  placement: none,
  caption: [How the generated #isaconst("run_voblint") reaches the browser. Build:
    #isacmd("export_code") writes #isaconst("run_voblint") into
    `Voblint_Generated.ml`, which `dune` and #raw("wasm_of_ocaml", lang: "sh")
    compile with the handwritten adapters into a WebAssembly bundle. Run: a web
    worker calls the bundle and returns the answer as JSON. Adapted from the
    project site.],
) <fig:build>

== The unverified shell <sec:ocaml-boundary>

The generated #isaconst("run_voblint") takes a syntax tree and returns a typed
answer, so unverified code has to surround it on both sides. Before it, an
`ocamllex` lexer and a Menhir parser turn the program text a user writes into
an #isatype("imp_prog") and write
each check's source position into its label. After it,
#isaconst("render_report") turns the report's states into text. Handwritten
code then prints the command-line report, each check at the position its label
carries, or serializes the answer as JSON, from which the playground draws the
graph and places the verdicts and arithmetic diagnostics in the editor. Isabelle's code export maps HOL's mathematical integers to
arbitrary-precision Zarith integers, so the generated code computes with
VIMP's integers (@sec:vimp-vs-c). The command-line tool and the playground share the parser,
the generated module and the code that turns a request into an analysis
configuration. They differ in their surroundings: the command-line tool
manages processes and files, and the playground's worker exchanges JSON with
the page.

For the program below, @fig:shell shows what crosses this boundary: the call
#isaconst("run_voblint") receives and its answer after #isaconst("render_report")
has turned the states into text, serialized by the same code the playground
uses.

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
  caption: [What the generated analyzer receives and returns for the program
    above (claim #claim-ref("shell-json")). The call carries the configuration
    and the syntax tree `p` the parser built, of the kind @fig:vimp-ast shows in
    full; the answer carries the report with its states rendered as text, here
    with its one check in full. Everything before the call, and the rendering
    from the answer on, is unverified. `{…}` and `[…×n]` fold parts of the JSON.],
) <fig:shell>

The
#link(
  "https://manuellerchner.github.io/Voblint-Verification-Master-Thesis/playground.html",
)[playground]
is a static page. Its toolbar selects the configuration argument of
#isaconst("run_voblint") and, independently, whether the surrounding tracer is
on. #isathm("run_voblint_source_sound") quantifies over that configuration
whenever #isaconst("run_voblint") returns an #ctor("Analysed") report.
@fig:pg-overview shows one run.



== Tracing the exported solver #thy-badge("Voblint_Solver", "Solver_Trace") <sec:tracing>

To explain a run, the command-line tool and the playground can trace the
solver's steps: which unknown is queried when, which update destabilizes which
unknown, where widening applies (@tab:eq-trace), as Goblint's tracing of its
top-down solvers reports them. Because the vendored solver @tilscher26 stays
unchanged, Voblint supplies traced versions of its equations that report each
step through one constant, #isaconst("trace_event"), which is $()$ in the
logic. Because it is $()$, each traced equation is proved equal to the one it
replaces (#isathm("solve_rec_c_traced"); #isathm("trace_route") and
#isathm("trace_run") do the same for the context policies and the reading of
the result). Code export uses only these equations, so there is a single generated module
containing the trace calls. Enabling tracing only changes the behaviour of the
OCaml hook, not the generated analyzer. In OCaml, #isaconst("trace_event") is mapped
to a hook that records the event when tracing is on. This mapping adds one target
mapping to the trusted base: the hook must return, raise nothing and leave the
solver's values alone. The trace, and the playground's replay of it, are
unverified observations and never feed back into a result. @fig:replay-still
shows one step of the replay.

#subfigures(
  playground-figure(
    "while-loop",
    width: 80%,
    [one run in three views: the check's verdict in the editor, the state
      inspector at the check, and the solved graph. Settings
      #playground-settings("while-loop")],
  ),
  <fig:pg-overview>,
  playground-figure(
    "solve-replay-still",
    width: 78%,
    [one step of the solve replay for the calls of `bump` (@tab:eq-trace): the
      graph shows each unknown's value at this step, and the trace beside it
      marks the step's line. Settings #playground-settings("solve-replay-still")],
  ),
  <fig:replay-still>,
  columns: (1fr,),
  gutter: 1.2em,
  placement: top,
  scope: "parent",
  caption: [The playground. Both panes run the generated analyzer of
    @fig:build in the reader's browser. The screenshots are illustrative.],
  label: <fig:playground>,
)

== The trust boundary <sec:trust-boundary>

Three questions decide what a run of the delivered analyzer establishes.
@fig:intro-trust places each component on the proved, unverified or trusted
side.

*What is proved.* #isathm("run_voblint_source_sound") and the verdict theorems
of @sec:verdict-meaning hold for every report #isaconst("run_voblint")
returns. The proved side reaches from the syntax tree #isaconst("run_voblint")
receives to the semantic report it returns. The proof covers the compiler, the
well-formedness test, the vendored solver with its executable refinement and
the executable state carrier.

*What is trusted.* Two groups lie outside the proof. The first is the code
around the generated analyzer: the lexer and parser and the handwritten
presentation code are unverified, and #isaconst("render_report") is generated
HOL code, but no theorem establishes that its strings describe the semantic
values. The second is the foundation everything runs on: Isabelle's kernel,
its code generator with the target mappings (#isacmd("code_printing")), the
trace hook among them, the OCaml and WebAssembly toolchains, Zarith and the
browser. The handwritten frontend and presentation code are covered only by tests
(@sec:eval-corpus), so bugs and unexpected behaviour remain possible there.

*Whether the definitions are adequate.* A proof establishes consequences of
#isaconst("pstep"). It cannot show that #isaconst("pstep") is the language a
reader has in mind; @sec:vimp-vs-c argues this for the fragment of C that VIMP
models.

*What the soundness theorem does not establish.* A parse error yields no
analyzer answer. An #isaconst("Invalid_Activation"), #isaconst("Malformed_Program") or
#isaconst("No_Answer") answer, a timeout, an aborted code equation and a run
that never returns yield no #ctor("Analysed") report,
so the source-level theorem gives no verdict for these cases. A hang may come from the solve, from the fixpoint reduction of Int,
whose generated code may loop where the HOL function returns
(@sec:reduced-product), or from the toolchain.

Both tools thus run generated code for the #isaconst("run_voblint") that
@ch:results proves sound. The parser, the code generator, the toolchains and
the presentation are trusted, and the source semantics is argued.
