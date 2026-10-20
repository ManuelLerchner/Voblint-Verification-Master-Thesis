#import "@preview/fletcher:0.5.8": diagram, edge, node
#import "../lib/code.typ": isa, isacmd, isaconst, isalocale, isathm, repo-blob, site
#import "../lib/theme.typ": vb
#import "../lib/stats.typ": stat

= Repository and Tooling <sec:voblint-repo>

The theories, the exported analyzer, the project site, and this thesis quote
one another. The analyzer is exported from the theories, the thesis cites
their names and statements, and both the site and the thesis quote the
analyzer's output. Every change to the theories can therefore make another
part stale, and keeping them consistent is engineering work outside the proof.
Isabelle offers comparatively little project-level tooling for this beyond its
distribution, a gap that users have noted as well @paulson26lean
@halbgefressen26. The need grew with AI assistance. Agents wrote many proofs
and much of the surrounding code (#link(<ai-use>)[statement on the use of
  generative AI]), and a reviewer cannot read every line they produce. A change
therefore counts as done only when deterministic checks pass, so the checks,
not the agent, decide whether the repository is consistent.

== Repository contents and the vendored solver

One repository holds everything this thesis describes: the Isabelle theories,
a submodule reference to the vendored TD solver, the exported analyzer with its
command-line tool and playground, the regression corpus, and the sources of
this thesis. Each release is archived on Zenodo with a citable DOI @voblint,
and the project site hosts the playground, the explainer, and the rendered
theories that every Isabelle name in this thesis links to.

The vendored TD solver of Tilscher et al. @tilscher26 carries four changes made
for this thesis, each proposed upstream and none changing the algorithm. They
restore the build under Isabelle2025-2
(#link("https://github.com/stilscher/td-verification/pull/15")[PR 15]), remove the stabilization
assumptions from the classes #isalocale("widening") and
#isalocale("narrowing"), which only termination proofs use
(#link("https://github.com/stilscher/td-verification/pull/13")[PR 13], @sec:domain-carrier-laws), rename short field and constructor names that
clashed with downstream theories
(#link("https://github.com/stilscher/td-verification/pull/14")[PR 14]), and add facts about the solver's
definitions, such as #isathm("solve_dom_of_solve_c"), that
#isathm("td_certified_solver") uses
(#link("https://github.com/stilscher/td-verification/pull/16")[PR 16], @sec:certificate). At the time of
writing, all four pull requests await review. The solver's repository is
private, so the development cannot yet be built from public sources alone,
and there are plans to publish the solver in the Archive of Formal Proofs.

== OCaml packages on conda-forge

#let _cf = json("/shared/generated/conda-forge.json").packages
#let _cf-ready = _cf.values().filter(p => p.available).len()
#let _pr(n) = "https://github.com/conda-forge/staged-recipes/pull/" + str(n)

The repository currently relies on several package managers.
#link("https://pixi.sh")[Pixi] installs Python and the conda-forge packages
and runs every task, opam installs the OCaml toolchain for the exported
analyzer and its browser build, and Isabelle is installed separately. The goal
is a single Pixi file from which one `pixi install` sets up everything. For the
OCaml side, this requires every package the analyzer builds with on
conda-forge for all supported platforms. Until recently, however, conda-forge
carried the OCaml compiler and only a handful of tools, such as Dune and
Menhir, and almost none of the libraries below them.

Alongside this thesis, considerable effort went into changing this, together
with other conda-forge contributors. A #link(_pr(34872))[recipe for ten base
  libraries], from `csexp` to `yojson`, has been merged, and Apple Silicon builds
have been enabled for each of them. Two fixes to the Dune package have been
merged, and recipes for `ppxlib` and `sedlex`, as well as an update to Zarith,
are under review. `isar-tools` itself #link(_pr(34960))[installs from conda-forge]. Of
the #_cf.len() packages in the
#link(repo-blob + "manifests/conda-forge-ocaml.toml")[toolchain manifest],
#_cf-ready are now available on conda-forge, and the others, among them
`js_of_ocaml` and `ocamlformat`, still come from opam. As far as the author is
aware, this is the first larger effort to bring OCaml libraries to
conda-forge.

== Derived files and checks

When the same information is maintained by hand in several files, the copies
tend to diverge after a change. The repository therefore keeps a few sources and derives everything else from them (@fig:pipeline). One
grammar file yields the Isabelle syntax of VIMP, the analyzer's parser, and its
printer, so the unverified parser (@fig:intro-trust) and the syntax the proofs
use come from one language description. The analysis registrations, in
contrast, are written by hand. Each numeric domain registers itself in a few
lines per context policy by interpreting a shared locale
(@sec:instances-supply). The product state of
@ch:cooperation is written by hand, with one field per analysis, each of a
different type. A dependently typed logic could express such a heterogeneous
structure once @chlipala13cpdt[ch. 9], but HOL's simple types cannot, so adding
an analysis adds a field and one case to each function over the analyses.

The most important derived file is the analyzer itself. Isabelle's code
generator exports #isaconst("run_voblint") as OCaml, and the repository commits
the exported #link(repo-blob + "codegen/generated/ml/Voblint_Generated.ml")[module]
so that the command-line tool and the playground build without Isabelle. A
committed copy can fall behind the theories, however. The continuous
integration therefore regenerates the export from the built session and fails
if the result differs from the committed file. Local builds record a hash of
the theories the export was generated from and warn when it no longer matches,
so a stale analyzer is noticed before it reaches the continuous integration.

#figure(
  {
    set text(size: 6.5pt)
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
      spacing: (12mm, 1.2mm),
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
      src((0, 4.5), link(repo-blob + "src")[theories, built session \ and analyzer], <t>),
      out(
        (1, 3.5),
        link(repo-blob + "codegen/generated/ml/Voblint_Generated.ml")[generated OCaml analyzer],
        <t1>,
      ),
      out(
        (1, 4.5),
        link(repo-blob + "thesis/shared/generated")[theorem statements, snippets, links],
        <t2>,
      ),
      out(
        (1, 5.5),
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

This thesis is held to the same discipline. Every Isabelle name in its sources
goes through a helper that a check resolves against the theories and links to
the rendered theories. Theorem statements are lifted from the theories and
compared with what the built session proves, quoted analyzer results are rerun,
each VIMP listing's playground link is decoded from the PDF and compared with
the listing, and repository figures come from a measurement script. A rename,
a changed statement, or a changed result therefore fails the build instead of
reaching the reader.

#pagebreak(weak: true)
== Maintaining the formalization: `isar-tools` <sec:isar-tools>

Isabelle checks that every proof goes through, but a successful build says
little about how well a development is maintained. A lemma that no proof
cites, an import that another import already brings in, a constant written out
next to the notation the project gave it, or a locale assumption that no proof
uses all leave the build green. Documentation that quotes formal statements or
links to the rendered theories can also fall out of date without affecting the
build. In a development of #stat("isabelle.theories") theories, such problems
accumulate.

#link("https://github.com/ManuelLerchner/isar-tools")[`isar-tools`],
written for this thesis and published separately, addresses them.
The command-line tool reads theory and `ROOT` files the way Isabelle's build
finds them and never runs Isabelle itself, so it answers in seconds, fits a
pre-commit hook, and also works on theories that do not yet build. Related
tools cover parts of this ground. The
#link("https://github.com/isabelle-prover/isabelle-linter")[Isabelle Linter]
checks proof style inside Isabelle, and
#link("https://github.com/ott2/isabelle-query")[`isabelle-query`] answers
source-level queries about declarations, dependencies, and unfinished proofs.

The tool has three parts. `isar fmt` changes only layout. `isar check` offers
about fifty checks in groups. Checks for unfinished proofs and unreached
theories run by default, and checks for unused or duplicated lemmas, unused
locale assumptions, or terms written out next to their notation run when
named. This repository runs the default groups and several named ones, among
them documentation coverage and the locale check below. `isar project`, the
part that matters most for this thesis, exposes sessions, theories, and
declarations to other tools. `isar project extract` keeps the quoted theorem
statements in sync with their sources, `isar project notation` generates the
notation tables of the thesis and the explainer, and `isar project anchors`
resolves the links into the rendered theories. A change that would leave the
thesis inconsistent with the formalization therefore fails the build.

Some findings concern mistakes that Isabelle accepts. Inside a locale header,
Isabelle reads an unknown identifier as a free variable and generalizes it. An
assumption that cites a renamed or misspelled constant therefore still builds,
but it now quantifies over an arbitrary function and states a different
specification. In the theory below, the assumption cites a misspelling of the
constant defined above it, and `isar check locales` reports the identifier.

#{
  set par(first-line-indent: 0pt, justify: false)
  show raw: set text(size: 7pt)
  isa(read("/shared/code/isar-locale/Demo.thy").split("\n").slice(3, 8).join("\n"))
  block(
    width: 100%,
    inset: 5pt,
    radius: 2pt,
    fill: vb.bg,
    stroke: 0.5pt + vb.frame,
    align(left, text(
      size: 7pt,
      font: "Latin Modern Mono",
      read("/shared/code/isar-locale/expected.txt").trim(),
    )),
  )
}
A test reruns the check on this
#link(repo-blob + "thesis/shared/code/isar-locale")[theory]. The check
approximates Isabelle's inner syntax lexically, so its report is a warning to
inspect and does not prove an error.

A second kind of finding concerns build time. A session inherits the heaps of
its parent sessions, but a library theory outside that ancestry is elaborated
again in every session that imports it. `isar stats build` reads the time each
theory took from a verbose build log and reports such repetitions, and
continuous integration enforces a budget per library session. In this
repository, repeated elaboration once cost 19% of a clean build.

All of these checks work on the sources and complement Isabelle. They point to
suspicious patterns and structural problems, and they may report false
positives or miss problems. Whether a theory is formally correct is still
decided by the Isabelle build alone.
