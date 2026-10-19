#import "@preview/fletcher:0.5.8": diagram, edge, node
#import "../lib/math.typ": *
#import "../lib/figures.typ": *
#import "../lib/code.typ": *
#import "../lib/claims.typ": claim-ref
#import "../lib/stats.typ": stat

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
sound. A user, however, writes source text and reads a report in a terminal or a browser tab instead of evaluating a HOL function.

== From theorem to code #thy-badge("Voblint_Codegen", "Voblint_Codegen") <sec:codegen>

@ch:solving replaced the two objects of the argument that cannot run, the
function-valued abstract states and the solver defined through its domain
predicate, with executable versions (@sec:represented-function,
@sec:termination). Every function that
#isaconst("run_voblint") uses therefore has _code equations_, the equations
that determine what code generation emits, and Isabelle's code generator
@haftmann10 exports it, together with the constructors and
selectors a caller needs, into one OCaml module,
#link(repo-blob + "codegen/generated/ml/Voblint_Generated.ml")[`Voblint_Generated.ml`].
The command-line tool and the playground reach this module only through the
facade #link(repo-blob + "cli/voblint.ml")[`cli/voblint.ml`], so no handwritten
code runs between receiving the syntax tree and returning the report.

The command-line tool links the module with handwritten adapters into a native
program, and for the playground #raw("wasm_of_ocaml", lang: "sh") compiles the
same code to WebAssembly, which a web worker in the reader's browser calls
(@fig:build). Both tools thus run the generated code of the function the
theorems are about, up to the code generator and the compilers.

#figure(
  image("/shared/generated/svg/build.svg", width: 100%),
  placement: none,
  caption: [How the generated #isaconst("run_voblint") reaches the browser.
    #isacmd("export_code") writes it into `Voblint_Generated.ml`, which `dune`
    and #raw("wasm_of_ocaml", lang: "sh") compile with the handwritten adapters
    into a WebAssembly bundle that a web worker calls. Adapted from the project
    site.],
) <fig:build>

== The generated code <sec:generated-code>

The exported module has #stat("generated_ocaml") lines and keeps the data
representations of the HOL definitions. Type classes become records of
operations passed as arguments, and finite sets and maps become lists that
membership and lookup scan. The solver keeps its valuation as a function, and
each update wraps the previous valuation in another closure, so a lookup may
traverse a chain as long as the number of earlier updates.

Up to the trusted code generator, this code computes the function the
theorems are about, but no proof says anything about its running time. The
generated code also evaluates every term as written. A definition that named
the program's entry node through the compiled graph would recompile the whole
program at every equation evaluation. The analysis therefore receives the
entry node as a parameter, fixed to the entry of `main`, and a theorem shows
that this node is the entry of every compiled graph
(#isathm("cfg_entry_compile_prog")).

The list representations are hard to replace. Isabelle's library implements
sets by red-black trees only for element types with a linear order, which abstract values, check results,
and entry-state contexts lack. A finite map in place of the solver's
function-valued table would remove the closure chains, but it would change the
state of the vendored solver and require its proof to be redone. This thesis
aims at a sound analyzer, and it reports no measurement of the generated
code's time or memory.

== The unverified shell <sec:ocaml-boundary>

The generated #isaconst("run_voblint") takes a configuration, kind declarations
and a syntax tree and returns a typed answer, so unverified code surrounds it on
both sides. Before it, an `ocamllex` lexer and a Menhir parser turn the program
text into a surface program (#isatype("imp_prog")) and the kinds of its
variables. They also resolve block scopes, turn a declaration without
initializer into a call of `__voblint_nondet_int`, and write each check's
source position into its label. After it, #isaconst("render_report") turns the
report's states into text, and handwritten code prints the command-line report
or serializes the answer as JSON, from which the playground draws the graph and
places verdicts and arithmetic diagnostics in the editor. The generated code
computes VIMP's machine-integer values as arbitrary-precision Zarith integers,
which the semantics keeps within each kind's range by explicit normalization
(@sec:vimp-vs-c). For the program below, @fig:shell shows the call and the
answer that cross this boundary.

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
    and the parsed syntax tree `p` (the surface column of @fig:elab-stages). The
    answer carries the report with its states rendered as text and its one
    check in full. Everything before the call, and the rendering from the
    answer on, is unverified. `{…}` and `[…×n]` fold parts of the JSON. The JSON
    prints the verdict #isai("Decided Check_Proved") of @sec:verdict-meaning under
    the name `Lifted` of the constructor that #isai("Decided") abbreviates.],
) <fig:shell>

The
#link(site("playground.html"))[playground]
is a static page whose toolbar selects the configuration argument of
#isaconst("run_voblint"), over which #isathm("run_voblint_source_sound")
quantifies, and whether the solver's steps are traced (@fig:pg-overview).

== Tracing the exported solver #thy-badge("Voblint_Solver", "Solver_Trace") <sec:tracing>

To explain a run, both tools can trace the solver's steps: which unknown is
queried when, which update destabilizes which unknown (@tab:eq-trace), and
where widening applies. Tracing must leave the definitions and proofs of the
vendored solver @tilscher26 untouched. Voblint therefore supplies traced
versions of its code equations that report each step through one constant,
#isaconst("trace_event"), which is $()$ in the logic, so each traced equation
is proved equal to the one it replaces (for example
#isathm("solve_rec_c_traced")). Code export uses the traced equations, and in
OCaml #isaconst("trace_event") maps to a hook that records the event when
tracing is on. This target mapping joins the trusted base, since the hook must
return, raise nothing, and leave the solver's values alone. The trace and its
replay in the playground (@fig:replay-still) are unverified observations and
never feed back into a result.

#subfigures(
  playground-figure(
    "while-loop",
    width: 60%,
    [one run in three views: the check's verdict in the editor, the state
      inspector at the check, and the solved graph. Settings
      #playground-settings("while-loop")],
  ),
  <fig:pg-overview>,
  playground-figure(
    "solve-replay-still",
    width: 66%,
    [one step of the solver replay for the calls of `bump` (@tab:eq-trace): the
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

@fig:intro-trust places the main components of the delivered analyzer relative to the proof.

*What is proved.* #isathm("run_voblint_source_sound") and the verdict theorems
of @sec:verdict-meaning hold for every report #isaconst("run_voblint")
returns, from the syntax tree it receives to the semantic report. The proof
covers the elaboration, the compiler, the well-formedness test, the vendored
solver with its executable refinement and the executable state carrier. The
vendored solver is a copy of the verified solver of Tilscher et al.
@tilscher26 with three of the four changes proposed upstream for this thesis
and its own build fix, and its proofs are checked with the rest of the
development (@sec:upstream-td). Its repository is
private, so the development cannot yet be built from public sources alone.

*What is trusted.* Two groups lie outside the proof. The first is the
handwritten code around the generated analyzer: the lexer, the parser with its
block-scope resolution and its rewriting of declarations without initializer,
the translation of a request into a configuration, and the presentation,
including the placement of arithmetic diagnostics. #isaconst("render_report")
is generated and passes verdicts and diagnostics through unchanged
(#isathm("render_report_columns")), but no theorem relates its state strings to
the semantic values. The second is the foundation: Isabelle's kernel, its code
generator with the target mappings (#isacmd("code_printing")), the trace hook
among them, the OCaml and WebAssembly toolchains, Zarith or, in the browser, a
JavaScript replacement of it, and the browser. Only regression and property
tests cover the handwritten code.

*Whether the definitions are adequate.* A proof establishes consequences of
#isaconst("pstep") and cannot show that #isaconst("pstep") is the language a
reader has in mind. @sec:vimp-vs-c argues this for the fragment of C that VIMP
models.

*What the soundness theorem does not establish.* A parse error, an
#isaconst("Invalid_Activation"), #isaconst("Malformed_Program"), or
#isaconst("No_Answer") answer, a timeout, and a run that never returns yield
no #ctor("Analysed") report, and neither does an aborted code equation, one
that raises an exception in OCaml where the logic returns a fallback value,
for instance when query recursion exceeds its depth bound. The handwritten
adapter reports this abort as #isaconst("No_Answer"), so the
#isaconst("No_Answer") a user sees comes from this adapter. In all these cases
the theorem gives no verdict. A hang may come from the solve, from the
fixpoint reduction of Int, whose code equation iterates where the HOL function
gives up and returns its input (@sec:reduced-product), or from the toolchain.
