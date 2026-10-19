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

= From Theorem to Tool <ch:executable>

@ch:results proved that every report #isaconst("run_voblint") returns is
sound. A user, however, does not evaluate a HOL function. The user writes
source text and reads a report in a terminal or a browser tab. This chapter
shows how the proved function becomes the analyzer that runs, and where the proof stops between the source text and the displayed report.

== Making abstract states executable #thy-badge("Voblint_Exec", "Default_St_Base") <sec:represented-function>

The function states of @ch:domains are total functions on infinitely many
variable names, which the solver cannot compare after every evaluation. This
section gives a finite representation. Nipkow and Klein address the same
problem in the abstract interpreter of Concrete Semantics by refining total
function states to a finite representation with a default @nipkow14[§13.6]:
a state is a finite list of variables with their values, every unlisted name
reads as #ltop, and two states are compared on the listed names. Such a
representation works like a default dictionary, a finite dictionary that
answers every missing key with a default. Voblint follows the same idea but
needs two defaults. It
represents a total function exactly and therefore loses no precision. We call such a representation an _executable state_.

VIMP initializes globals to zero, as
C does for objects with static storage (#c11("6.7.9p10")), and leaves the
locals of `main` arbitrary (@sec:vimp-vs-c). The initial state must give every local
the value #ltop and every global the value $0^sharp$, the abstract value of the
constant $0$, without listing the declared globals. Voblint's executable state
therefore keeps two default dictionaries, one for the names the program
treats as local and one for the globals, each a default paired with a finite
list of overrides. We write the state with local dictionary $(d_l, "ls")$ and
global dictionary $(d_g, "gs")$ as $⟪(d_l, "ls"), (d_g, "gs")⟫$. The initial
state is $⟪(ltop, []), (0^sharp, [])⟫$, and the least element is
$⟪(lbot, []), (lbot, [])⟫$.

Different representations can describe the same state: overrides of distinct
names may appear in any order, and an override equal to its default changes
nothing. A _quotient type_ @huffman13 identifies the representations that
answer every lookup alike, and its operations are lifted with
#isacmd("lift_definition"):

#thy("default_st")

Two executable states are therefore equal exactly when every lookup agrees
(#isathm("default_st_eq_iff")). Comparing the two defaults and the finitely
many listed names decides the order (#isathm("le_default_st_rep_code_iff")),
and equality tests it in both directions.

The program's global-variable classifier $cal(G)$ (@sec:pstep) assigns each
name $x$ its _location_ $ell(x)$, local or global. A lookup reads the
dictionary of the variable's location: the override if there is one, the
default otherwise. We write
$d⟨l⟩$ for the lookup at location $l$ and $d⟨l := a⟩$ for the update. Looking
up every variable at its location gives the total function $rho_(cal(G))(d)$
that an executable state represents (#isaconst("default_st_to_fun")). An executable
state means what its function means under the concretization
#isaconst("gamma_state") of @sec:nonrel-state, so its own concretization
(#isaconst("default_st_gamma")) is
$ conc(d) = conc(rho_(cal(G))(d)) = setcomp(s, forall x. s(x) in conc(d⟨ell(x)⟩)). $
The solver never computes $conc(d)$. It uses only the executable lattice operations. Function states get order, join, and bottom pointwise from HOL, but
no widening or narrowing. The executable state instantiates all of these classes on
#isatype("default_st") whenever the values do, so the generic solver runs on
it unchanged.

Distinct executable states can still denote the same stores: every state whose
local default is #lbot denotes $emptyset$, yet the quotient keeps such states
apart because they represent distinct functions.

Each lattice operation is computed with the value domain's operation on the
two defaults and on each listed name, so under lookup it agrees with the
pointwise operation on functions. For the join,
#isathm("default_st_get_sup") states
$(d union.sq e)⟨l⟩ = d⟨l⟩ union.sq e⟨l⟩$, and analogous lemmas cover
bottom, order, widening, and narrowing. The transfer functions must commute
with the represented function in the same way,
$ rho_(cal(G))("op"_"exec" (d)) = "op"_"abs" (rho_(cal(G))(d)), $
and since $conc(d) = conc(rho_(cal(G))(d))$, the soundness facts of
@ch:analysis-interface then transport from the abstract to the executable
operation. The locale #isalocale("dg_analysis_exec") states this commutation
for the transfer on nonempty states and for procedure entry. For primitives
proved sound it holds without a per-domain proof, because the abstract and
executable steps are derived from the same operations
(#isathm("sound_nonrelational_ops.tf_st_for_commute"), @sec:instances-supply).
Its consequence for the exported code is
#isathm("exec_local_spec_sound").

Emptiness, on which #verdict("DEAD") rests (@ch:domains), is the one operation the
listed overrides do not decide: an unlisted variable can make the state empty
through its default. The test inspects the local default, the
overrides that the represented function reads, and each declared global. The globals are listed explicitly because a program has finitely many of them, so
the global default may describe no variable at all.
#isathm("default_st_is_bot_for_gamma_iff") proves the test exact,
$ #isaconst("default_st_is_bot_for") space "globals" space d <==> conc(d) = emptyset, $
provided the list enumerates exactly the globals of $cal(G)$. Because the test
is exact, collapsing the states it finds empty to #lbot commutes with the
represented function, as the specification's collapse requires, and a state
it keeps is nonempty, which is where the numeric transfer commutes
(#isaconst("live_default_st")).

== Code generation #thy-badge("Voblint_Codegen", "Voblint_Codegen") <sec:codegen>

The previous section replaced function states with carriers, and
@sec:certificate replaced the solver's domain predicate with the executable
#isaconst("solve_c", thy: "TD_side_upd_rule"). Every function that
#isaconst("run_voblint") uses therefore has code equations, and Isabelle's
code generator @haftmann10 can export it. One #isacmd("export_code")
declaration emits #isaconst("run_voblint"), #isaconst("render_report"), and the
constructors and selectors a caller needs into one OCaml file,
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

#let _bench = json("/shared/generated/bench-init-publications.json").programs
#let _speedup(prog) = {
  let r = _bench.at(prog)
  str(calc.round(r.before.mean_s / r.after.mean_s, digits: 0))
}

== The generated code <sec:generated-code>

The exported module,
#link(repo-blob + "codegen/generated/ml/Voblint_Generated.ml")[`Voblint_Generated.ml`],
runs, but it follows the proofs rather than the habits of OCaml programmers. It has #stat("generated_ocaml") lines. Type classes
become records of operations passed as arguments, so polymorphic operations
such as equality go through an indirect call. Finite sets are unsorted lists,
and the finite maps the code uses are association lists, so membership, insertion, and lookup scan them. The solver keeps
its valuation as a function. Each update wraps the previous valuation in
another closure, so a lookup may traverse a chain as long as the number of
earlier updates, and superseded closures stay reachable.

The proofs guarantee that this code computes the proved function, but they say
nothing about its running time. One cost was a defect. On every equation
evaluation, #isaconst("init_publications") tests whether the unknown is the
program's entry, and its definition names the entry as
#isai("cfg_entry (prog_cfg p)"). The generated code evaluated this term as
written and compiled the whole program at every evaluation. A sampling
profile of a program of 256 chained assignments, taken on one machine,
attributed most of the CPU time to this compilation. Isabelle lets a theory replace the
equation that code generation uses for a constant with any proved equation for
it. #isathm("init_publications_code") writes the entry node out as
#isai("FunctionEntry prog_main_name") and follows from
#isathm("cfg_entry_compile_prog"), so the definition and every theorem about it
stay unchanged and no trust is added. On the same machine, the
#link(repo-blob + "scripts/gen_bench_program.py")[generated] chain of 256
assignments then ran #_speedup("chain256") times faster, and a program of 512
assignments in procedures of eight statements #_speedup("procs512") times
faster (#link(repo-blob + "thesis/shared/generated/bench-init-publications.json")[recorded
  measurement]). These are single measurements on one machine, not a
performance evaluation.

The remaining cost is spread over report construction, printing, and
dictionary calls. Further proved code equations could remove more of it
without changing a theorem. Replacing the solver's function-valued table with a
finite map would remove the closure chains, but it would change the state of
the vendored solver and require its proof to be redone.

== The unverified shell <sec:ocaml-boundary>

The generated #isaconst("run_voblint") takes a configuration and a syntax tree
and returns a typed answer, so unverified code has to surround it on both sides. Before it, an
`ocamllex` lexer and a Menhir parser turn the program text a user writes into
an #isatype("imp_prog") and write
each check's source position into its label. After it,
#isaconst("render_report") turns the report's states into text. Handwritten
code then prints the command-line report, each check at the position its label
carries, or serializes the answer as JSON, from which the playground draws the
graph and places the verdicts and arithmetic diagnostics in the editor. Isabelle's code export maps HOL's mathematical integers to
arbitrary-precision Zarith integers, so the generated code computes with
VIMP's integers (@sec:vimp-vs-c). The command-line tool and the playground share the parser,
the generated module, and the code that turns a request into an analysis
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
unknown, where widening applies, as Goblint's tracing of its
top-down solvers reports them. Tracing must leave the definitions and proofs of
the vendored solver @tilscher26 untouched. Voblint therefore supplies traced
versions of its code equations that report each
step through one constant, #isaconst("trace_event"), which is $()$ in the
logic. Because it is $()$, each traced equation is proved equal to the one it
replaces (for example #isathm("solve_rec_c_traced")\; #isathm("cs_route_traced"),
#isathm("trace_route"), and #isathm("trace_run") do the same for routing and the
reading of the result). Code export replaces the original equations with these,
so one generated analyzer serves traced and untraced runs alike. In OCaml, #isaconst("trace_event") is mapped
to a hook that records the event when tracing is on. This mapping adds one target
mapping to the trusted base: the hook must return, raise nothing, and leave the
solver's values alone. The trace, and the playground's replay of it, are
unverified observations and never feed back into a result. @fig:replay-still
shows one step of the replay.

#subfigures(
  playground-figure(
    "while-loop",
    width: 74%,
    [one run in three views: the check's verdict in the editor, the state
      inspector at the check, and the solved graph. Settings
      #playground-settings("while-loop")],
  ),
  <fig:pg-overview>,
  playground-figure(
    "solve-replay-still",
    width: 72%,
    [one step of the solver replay for the calls of `bump`: the
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

== The repository and its checks <sec:voblint-repo>

The generated analyzer is only as current as the theories it was exported from,
and the claims of this thesis are only as current as the statements and outputs
they quote. Keeping these consistent as the development changes is
engineering, not proof. A formalization of this size needs work around the
proof assistant as well as inside it. Its theories must be formatted and checked for unfinished proofs,
its names must stay consistent with the prose that cites them, and a new
contributor must be able to install everything the build needs. For Isabelle,
comparatively little project-level tooling is available outside the distribution itself.
Isabelle users have noted the resulting gap as well, for instance in a
comment on a recent blog post by Paulson @paulson26lean, which observes that
Isabelle's own development uses almost no standard tooling @halbgefressen26.

The need for such tooling grows with AI assistance. Many proofs and a large share of the
surrounding code of this development were written by agents (see #link(<ai-use>)[the statement on the use of generative AI]). An agent can
produce a plausible change quickly, but it cannot be trusted to keep the
cross-references of a large development consistent, and a reviewer cannot read every line
it writes. Deterministic tooling around the agent made its work usable at this scale. An agent's change counts as done only when these checks pass, so
the checks, not the agent, decide whether the repository is consistent.

Everything this thesis describes is published in one repository: the Isabelle
theories, a submodule reference to the vendored solver, the exported analyzer with its command-line tool and playground, the
regression corpus, and the sources of this thesis. Each release is archived on
Zenodo with a citable DOI @voblint. The project site hosts the
playground, the explainer, and the rendered theories that every Isabelle name in
this thesis links to.

The vendored copy of the solver of Tilscher et al. @tilscher26 carries four
changes made for this thesis. Each was proposed upstream, and none changes the
algorithm. The first restores the build under Isabelle2025-2 @td15. The second
removes the well-foundedness assumptions from the solver's
#isalocale("widening") and #isalocale("narrowing") classes @td13. They say that
widening and narrowing stabilize, which only termination proofs use, so a
domain need not provide a stabilizing widening (@sec:domain-carrier-laws). The
third renames short record fields and constructors, such as `c`, `W` and `N`,
that took these names away from downstream theories, and adds one interface
theory per solver family @td14. The fourth adds facts about the solver's own
definitions that Voblint had proved on its side @td16, among them
#isathm("solve_dom_of_solve_c") and #isathm("finite_stabl_solve"), which
#isathm("td_certified_solver") uses (@sec:certificate). At the time of writing,
all four pull requests await review. The solver's repository is private and
accessible only by invitation, so the development cannot yet be built from
public sources alone. There are plans to publish the solver in the Archive of
Formal Proofs.

A development of this size drifts when one fact is written down twice. The
repository therefore keeps a few sources and derives everything else from them
(@fig:pipeline). One grammar file yields the Isabelle syntax of VIMP, the
analyzer's parser and its printer. The parser lies outside the proof and hands
the proved analyzer its syntax tree (@sec:trust-boundary), but it and the
Isabelle syntax are generated from the same language description. An
analysis manifest names each analysis, its value type and the theories that
prove it sound. From it, a generator writes the registration of each numeric domain (@sec:instances-supply) and the combined state of @ch:cooperation, and
Isabelle checks every generated proof. The generator exists because the
repetition lies outside what a theory can express: each domain is registered
once per context policy it supports, for every update rule, and the combined
state has one field per analysis, of differing types. With dependent types, a heterogeneous list indexed
by these types could express it inside the logic @chlipala13cpdt[ch. 9]; HOL's
simple types cannot. #isaconst("run_voblint") itself reaches OCaml through
#isacmd("export_code") (@sec:codegen). Because the derived files are checked
against their sources, a stale name, statement, or quoted output fails the build
instead of reaching the reader (@fig:pipeline).

#figure(
  {
    set text(size: 7.5pt)
    set par(first-line-indent: 0pt, justify: false)
    let src(pos, body, name) = node(
      pos,
      body,
      name: name,
      stroke: 0.6pt + vb.accent,
      fill: vb.accent.lighten(92%),
      corner-radius: 2pt,
      inset: 4pt,
      width: 30mm,
    )
    let out(pos, body, name) = node(
      pos,
      body,
      name: name,
      stroke: 0.6pt + vb.neutral,
      fill: white,
      corner-radius: 2pt,
      inset: 4pt,
      width: 50mm,
    )
    let gen(a, b, lab: none) = edge(
      a,
      b,
      "-|>",
      stroke: 0.6pt + vb.neutral,
      label: if lab != none { text(size: 6.5pt, fill: vb.muted, lab) },
      label-side: center,
    )
    diagram(
      spacing: (14mm, 2.5mm),
      src(
        (0, 1),
        link(repo-blob + "manifests/vimp-grammar.yaml")[grammar \ `vimp-grammar.yaml`],
        <g>,
      ),
      out(
        (1, 0),
        link(
          repo-blob + "src/Program_Model/VIMP/VIMP_Grammar_Generated.thy",
        )[Isabelle syntax of VIMP],
        <g1>,
      ),
      out(
        (1, 1),
        link(repo-blob + "cli/frontend/vimp_parser.mly")[parser and lexer (Menhir)],
        <g2>,
      ),
      out((1, 2), link(repo-blob + "cli/frontend/vimp_printer.ml")[source printer (OCaml)], <g3>),
      gen(<g>, <g1>),
      gen(<g>, <g2>),
      gen(<g>, <g3>),
      src(
        (0, 4),
        link(repo-blob + "manifests/analyses.yaml")[analysis manifest \ `analyses.yaml`],
        <m>,
      ),
      out(
        (1, 3.5),
        link(
          repo-blob + "src/Analyses/Sign/generated/Sign_Analyses.thy",
        )[per-domain registration theories],
        <m1>,
      ),
      out(
        (1, 4.5),
        link(
          repo-blob + "src/Executable_Surface/CLI/generated/MCP_Carrier.thy",
        )[combined state of all analyses],
        <m2>,
      ),
      gen(<m>, <m1>),
      gen(<m>, <m2>),
      src((0, 7), link(repo-blob + "src")[theories, built session \ and analyzer], <t>),
      out(
        (1, 6),
        link(repo-blob + "codegen/generated/ml/Voblint_Generated.ml")[generated OCaml analyzer],
        <t1>,
      ),
      out(
        (1, 7),
        link(repo-blob + "thesis/shared/generated")[theorem statements, snippets, links],
        <t2>,
      ),
      out(
        (1, 8),
        link(repo-blob + "thesis/shared/generated")[quoted analyzer output, figures],
        <t3>,
      ),
      gen(<t>, <t1>),
      gen(<t>, <t2>),
      gen(<t>, <t3>),
    )
  },
  kind: image,
  placement: auto,
  caption: [The sources of the repository (blue) and the files derived from
    them; each box links to its file. Each derived file is generated during the build or committed with a
    check that regenerates it; the link map is also checked against the
    published site.],
) <fig:pipeline>

This thesis is held to the same discipline. Each Isabelle name in its Typst
sources goes through a helper that a check resolves against the theories and
links to the rendered theories. Theorem statements are lifted from the theories
and compared with what the built session proves, quoted analyzer results are rerun against the analyzer, each VIMP listing's playground link is decoded
from the PDF and compared with the listing, and repository figures come from a
measurement script. A rename, a changed statement, or a changed result
therefore fails the build, and another check warns when the text shows a
statement before the entities it uses.

The checks run in layers ordered by cost (@fig:gates), from hooks triggered by
the staged files to continuous integration, which reruns the checks on a fresh
runner, reusing cached results for unchanged inputs, together with the tests of
@sec:eval-corpus. Only the main branch is deployed, and only after the rendered
theories, the formalization PDF, and this thesis build. All layers invoke the same-named Pixi tasks, and a further check keeps the local `verify` task and
continuous integration from diverging.

#figure(
  {
    set text(size: 7pt)
    set par(first-line-indent: 0pt, justify: false)
    let gate(pos, title, items, name) = node(
      pos,
      [*#title* \ #items.join(linebreak())],
      name: name,
      stroke: 0.6pt + vb.neutral,
      fill: white,
      corner-radius: 2pt,
      inset: 4pt,
      width: 25mm,
    )
    let end(pos, body, name) = node(
      pos,
      body,
      name: name,
      stroke: 0.6pt + vb.accent,
      fill: vb.accent.lighten(92%),
      corner-radius: 2pt,
      inset: 4pt,
    )
    let step(a, b) = edge(a, b, "-|>", stroke: 0.6pt + vb.neutral)
    diagram(
      spacing: (3.5mm, 0mm),
      end((0, 0), [change], <c>),
      gate(
        (1, 0),
        link(repo-blob + ".lefthook.yaml")[pre-commit],
        ([drift of derived files], [formatters], [`isar` checks, thesis references]),
        <a>,
      ),
      gate(
        (2, 0),
        link(repo-blob + ".lefthook.yaml")[pre-push],
        ([exported OCaml current], [claims and facts], [thesis build]),
        <b>,
      ),
      gate(
        (3, 0),
        link(repo-blob + ".github/workflows/ci.yml")[CI],
        ([session build], [regression and property tests], [thesis PDF]),
        <d>,
      ),
      gate(
        (4, 0),
        link(repo-blob + ".github/workflows/ci.yml")[deploy (main)],
        ([site with playground], [Pages deploy], [published links]),
        <e>,
      ),
      end(
        (5, 0),
        link("https://manuellerchner.github.io/Voblint-Verification-Master-Thesis/")[website],
        <w>,
      ),
      step(<c>, <a>),
      step(<a>, <b>),
      step(<b>, <d>),
      step(<d>, <e>),
      step(<e>, <w>),
    )
  },
  kind: image,
  placement: none,
  caption: [The layers of checks between a change and the published site, with
    representative checks; the published links are checked after deployment.
    Each box links to its configuration.],
) <fig:gates>

The source tooling built for these checks, which reads Isabelle theories
without running Isabelle, is described in @sec:isar-tools.

== The trust boundary <sec:trust-boundary>

Three questions decide what a run of the delivered analyzer establishes, and @fig:intro-trust places the main components on each side.

*What is proved.* #isathm("run_voblint_source_sound") and the verdict theorems
of @sec:verdict-meaning hold for every report #isaconst("run_voblint")
returns, from the syntax tree it receives to the semantic report. The proof
covers the compiler, the
well-formedness test, the vendored solver with its executable refinement and
the executable states (@sec:represented-function).

*What is trusted.* Two groups lie outside the proof. The first is the
handwritten code around the generated analyzer: the lexer, the parser, the
translation of a request into a configuration, and the presentation, including
the placement of arithmetic diagnostics. #isaconst("render_report") is
generated and passes verdicts and diagnostics through unchanged
(#isathm("render_report_columns")), but no theorem relates its state strings to
the semantic values. The second is the foundation: Isabelle's kernel, its code
generator with the target mappings (#isacmd("code_printing")), the trace hook
among them, the OCaml and WebAssembly toolchains, Zarith or, in the browser, a
JavaScript replacement of it, and the browser. Only the tests of
@sec:eval-corpus cover the handwritten code.

*Whether the definitions are adequate.* A proof establishes consequences of
#isaconst("pstep"). It cannot show that #isaconst("pstep") is the language a
reader has in mind; @sec:vimp-vs-c argues this for the fragment of C that VIMP
models.

*What the soundness theorem does not establish.* A parse error, an
#isaconst("Invalid_Activation"), #isaconst("Malformed_Program"), or #isaconst("No_Answer") answer, a timeout, an aborted code equation, and a run
that never returns yield no #ctor("Analysed") report, so the theorem gives no
verdict. A hang may come from the solve, from the fixpoint reduction of Int,
whose generated code may loop where the HOL function returns
(@sec:reduced-product), or from the toolchain.

Both tools thus run generated code for the #isaconst("run_voblint") that
@ch:results proves sound.
