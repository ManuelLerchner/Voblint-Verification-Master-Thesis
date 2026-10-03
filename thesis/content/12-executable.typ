#import "@preview/fletcher:0.5.8": diagram, edge, node
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
syntax tree and a configuration to an analysis answer. A user has source text
and wants a report. Code generation, a compiler, a parser, and a renderer lie
between the two, and the theorem covers none of them. The delivered tools run
the constant the theorem is about, which gives the executable half of the
end-to-end result. @sec:trust-boundary states where the proof ends and which
trusted components remain.

== Code generation and the public interface <sec:codegen>

The source-level theorem is stated about one HOL function, and the delivered
tools call that function:

#thy("run_voblint")

The first argument is the configuration, an #isatype("analysis_config"): the
active analyses (a list of #isatype("analysis_domain")), the global update rule
(#isatype("globals_rule")), the context policy (#isatype("context_mode"): no
contexts, entry states, or call strings of a given depth), and the placement of
program globals (#isatype("program_globals"), @sec:mixed-flow). The second is the
syntax tree, of type #isatype("imp_prog"). The active analyses are solved as one
combined state whose concretization is the intersection of theirs, and they
answer one another's queries (@ch:cooperation). The command-line flag
`--analysis interval,order` names such a list, and the playground offers the
same choice. #isaconst("run_voblint") returns #isaconst("Invalid_Activation")
unless the list is non-empty and has no duplicates (#isaconst("valid_config")).
It then checks the structural conditions compilation requires
(#isaconst("wf_program_compile_input_exec")) and returns
#isaconst("Malformed_Program") on failure. Otherwise it solves with the
executable solver of @sec:termination. #isaconst("No_Answer") is the logical
case in which that solver returns nothing; where the solve diverges, the
generated code simply does not return. #isaconst("Analysed") carries an
#isatype("analysis_report"): the configuration, the CFG, the contexts, one
state per solved point and context with its verdicts and arithmetic
diagnostics, the call routes, the check rows, the solved global unknowns, and
the program's arithmetic diagnostics, which #isathm("run_voblint_arithmetic_safe")
reads. One function, #isaconst("analysis_report_of"), reads the context
policy; every other part of the pipeline is the same for all three.

The report holds semantic values. Each state is a value of the combined state
the solver computed, not a string, so the theorems of @ch:results speak about
what the analysis computed. Text comes later. #isaconst("render_report") maps
each state through its analysis's own display function and
#isaconst("string_of_abstract_value") into the displayed
#isatype("run_result"), a projection no theorem reads. Rendering a value is the
analysis's business: a Congruence value is a residue class behind a type
definition, which OCaml could not look inside, and a new analysis changes no
OCaml. No theorem constrains the strings.

Export requires executable code equations for the whole dependency closure. Two
objects of the soundness argument have none, and @ch:solving replaces both. The
semantic state, a function on an infinite set of variables, becomes the finite
carrier #isatype("default_st"). The solver specification, a recursion whose
termination is not known in general, gets the vendored solver's executable
version as its code equation, which the vendored library proves from their
agreement wherever the specification is defined @tilscher26. Outside that
domain the generated solve does not return. Both replacements are proved, and
neither proves termination (@sec:termination). One #isacmd("export_code")
declaration then emits #isaconst("run_voblint"), #isaconst("render_report") and
the constructors a caller needs as the OCaml module `Generated` of the file
`Voblint_Generated.ml`. It also exports a few program-inspection functions
(#isaconst("prog_table"), #isaconst("declared_global_vars"),
#isaconst("cfg_intra_list")) that the renderer calls outside
#isaconst("run_voblint"). The report's own fields are not exported:
#isaconst("render_report") is their only reader, so no OCaml code depends on
the report's representation. Handwritten OCaml names the export through a thin
facade, the module `Voblint`, which re-exports its signature unchanged; the
export's root list still decides what can be named, and a change of packaging
touches the facade alone.

Because the export is the theorem's own constant, no handwritten entry point
needs an agreement argument. One exported entry point per domain and context
policy would need a lemma relating each of them to the theorem's constant. The single
dispatcher answers every combination of its four configuration arguments, so
the command-line tool never decides which combination is legal.

== Interfaces that separate execution from proof <sec:engineering>

Two requirements of code generation shape the interfaces between execution and
proof. First, a type-class constraint becomes a dictionary of operations passed
at run time. A class holding both the operations of a domain and its
concretization would put the concretization into every dictionary, and a
function into sets of integers, such as the residue class of a congruence, has
no executable code equation in general. The domain classes therefore split
(@fig:domain-carrier): #isalocale("executable_domain") holds the runtime
operations and #isalocale("numeric_domain") adds the concretization and its
laws. The executable analysis mentions only the former. The solver asks for
less: #isalocale("bounded_semilattice_sup_bot") and #isalocale("warrowing"),
both of which #isalocale("executable_domain") extends. A type has at most one
instance of each class, while transfer functions, routing policy and solver
vary over one carrier. They are therefore locale parameters.

Second, code generation needs unconditional equations, and theorems about the
result need semantic premises. #isalocale("dg_pipeline") fixes the
executable ingredients and assumes nothing, so its definitions become code
equations directly. The ingredients are a component, which is one analysis's
local specification or a combination of several, its emptiness test and
the result map, the initial state, the placement of program globals, the
global unknowns, the routing policy with its initial context, the solver and
the check classifier. The placement is a lifter around the component, the
recombination of a local value with an environment of global values, and the
initial value of each global, which the program entry publishes. The global
unknowns are a node's buffer, a key map from analysis-global names to
unknowns, and the entry seeds. Even the bottom state is a parameter, because a least element
taken from a type class would have to be executable at a function type.
#isalocale("dg_analysis") imports it and adds the contracts, among them
soundness of the component (#isaconst("sound_local_spec")) and of the initial
state, an emptiness test on the solver's states that agrees with a sound
emptiness test on the published values, a single entry pair, seeds distinct from the
buffer and from every analysis global, the three solver contracts of @sec:cert-param, and
correctness of the check classifier. @sec:instances-supply shows how a numeric
domain discharges them.

The analyzer interprets #isalocale("dg_analysis") once per context family and
placement for
the combination #isaconst("mcp_comp") of any activation list (@fig:assembly),
and every run inherits the argument of @ch:results from these interpretations.
The order analysis has no registration: it supplies its local specification
#isaconst("order_spec") directly, with #isathm("order_spec_sound"). For a new
analysis, the analysis manifest generates its registration and its field of
the combined state. Everything the analyzer runs of one analysis is one record
(#isatype("analysis_registration")), built by #isaconst("registration_of"), the
one function that dispatches on the analysis at runtime. A few tables are still
edited by hand (@sec:pipeline).

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
      loc((1, 0), isalocale("dg_pipeline"), [a component and the other \
        executable ingredients; no assumptions]),
      loc(
        (1, 1),
        isalocale("dg_analysis"),
        [adds the contracts, among them \
          #isaconst("sound_local_spec")],
        color: vb.proved,
      ),
      loc(
        (2.4, 1),
        isalocale("dg_analysis_exec"),
        [derives the component contracts \
          of a numeric domain],
        color: vb.proved,
      ),
      inst((0.4, 2), [#isaconst("mcp_comp") of any activation list \ three context families]),
      inst((2.4, 2), [one registration per numeric \ domain, at the unit context]),
      loc(
        (2.4, 3),
        isalocale("sound_nonrelational_ops"),
        [a domain's primitives, \ proved sound],
        color: vb.proved,
      ),
      loc((0.4, 3), isaconst("order_spec"), [the order analysis's \ local specification]),
      import-edge((1, 0), (1, 1), label: lab[extends], label-side: left),
      sublocale-edge((2.4, 1), (1, 1), label: lab[sublocale]),
      interp-edge((1, 1), (0.4, 2)),
      interp-edge((2.4, 1), (2.4, 2)),
      edge((2.4, 2), (0.4, 2), "->", stroke: 0.6pt + vb.muted, label: lab[field soundness]),
      edge(
        (2.4, 3),
        (2.4, 2),
        "->",
        stroke: 0.6pt + vb.muted,
        label: lab[soundness discharges contracts],
        label-side: right,
      ),
      edge(
        (0.4, 3),
        (0.4, 2),
        "->",
        stroke: 0.6pt + vb.muted,
        label: lab[field, proved directly],
        label-side: left,
      ),
    )
  },
  kind: image,
  caption: [The analysis assembly. Solid arrows are locale extension, the dashed
    arrow a sublocale proof, dotted arrows global interpretations, and thin grey
    arrows name what one object supplies to another. The interpretations of
    the combined component take the activation list, the global update rule
    and, for call strings, the depth $k$ as parameters.],
) <fig:assembly>

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
and frontend (@sec:pipeline), and they check a request the same way: one
function turns analysis, update-rule and context names into a configuration,
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
run lies within the configurations covered by
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

== What remains outside the proof <sec:trust-boundary>

Three questions determine what a run of the delivered analyzer establishes, and
@fig:intro-trust places each component under one of them.

*What is proved.* Every store a finite source run reaches is described by the
report at a simulating graph node, in some context
(#isai("s \<in> \<lbrakk>res\<rbrakk>\<^bsub>v\<^esub>")), and there every
`PROVED` condition holds and every `REFUTED` condition fails
(#isai("s \<in> \<V>\<^bsub>res\<^esub> v")). This is
#isathm("run_voblint_source_sound") (@sec:headline). It assumes an initial
store from #isaconst("cinit_stores") and an #isaconst("Analysed") answer of
#isaconst("run_voblint"), and nothing about termination: an answer exists only
where the solve returned. #isathm("run_voblint_dead_check_unreached") and
#isathm("run_voblint_arithmetic_safe") give `DEAD` and the absence of an
arithmetic diagnostic their meaning. The proved side includes the compiler,
the well-formedness test, the vendored solver with its executable refinement,
and the finite carrier. The vendored solver's changes (@sec:upstream-td) are
checked by Isabelle like every other theory. The proved side ends at two
points: the syntax tree #isaconst("run_voblint") receives, and the semantic
report it returns, before #isaconst("render_report") turns its states into text
(@sec:codegen). Termination is not proved for every program
(@sec:termination); that is a gap in what the analyzer can answer, not a
premise of what an answer means. No theorem constrains `UNKNOWN` verdicts or
warnings.

*What is trusted.* The delivered guarantee also relies on the following
components, which the theorem does not mention.

- The lexer and parser. A fault builds a syntax tree other than the one the
  text denotes, and the verdicts then describe another program.
- Isabelle's kernel, and its code generator with the library's target
  mappings, which send HOL integers to Zarith and HOL strings to OCaml strings.
  The code equations of the development are theorems. The translation to OCaml
  and these mappings are not. Witness theorems proved by `eval`, such as the
  non-vacuity instances of @sec:nonvacuity, trust the same generator inside
  Isabelle
  (@tab:oracles-audit).
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
fixpoint reduction of the Int product (@ch:instances), or from the toolchain
and the browser. An abort branch of a code equation, such as the query
recursion exceeding #isaconst("query_depth") (@sec:coop-channel), raises an
exception and yields no answer.

The delivered tools run the constant the source-level theorem is about, through
code equations that are theorems. The trust boundary consists of the frontend,
the code generator's translation and target mappings, the compilers and
runtimes, and the rendering, together with the argued adequacy of
#isaconst("pstep").
