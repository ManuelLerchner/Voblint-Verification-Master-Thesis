#import "../lib/code.typ": isaconst, isalocale, isathm
#import "@preview/fletcher:0.5.8": diagram, edge, node
#import "../lib/theme.typ": vb

= Tooling and Open-Source Work <ch:tooling>

A formalization of this size needs work around the proof assistant as well as
inside it. Its theories must be formatted and checked for unfinished proofs,
its names must stay consistent with the prose that cites them, and a new
contributor must be able to install everything the build needs. For Isabelle,
little of this exists outside the distribution, which ships its own build tool
and editor. The limited tooling around Isabelle comes up in discussions among its
users, for instance in the discussion following a recent blog post by Paulson
@paulson26lean @halbgefressen26.

The need grows with AI assistance. Most proofs and much of the surrounding
code of this development were written by agents (see #link(<ai-use>)[the statement on the use of generative AI]). An agent can
produce a plausible change quickly, but it cannot be trusted to keep the
cross-references of a large development consistent, and a reviewer cannot read every line
it writes. What made the agent work usable at this scale was deterministic
tooling around it: the batch build for the proofs, and the checks of
@sec:pipeline for everything the build does not see. An agent's change counts as done only when these checks pass, so
the checks, not the agent, decide whether the repository is consistent. The
extension of @ch:cooperation followed this pattern.

This chapter describes the tools and upstream changes made for this thesis
and published separately. They are engineering contributions: nothing in them
is proved. The source tooling and the solver changes are in use: the
repository's continuous integration runs them. The packaging work is evidenced
by its pull requests, since the recipes still await review.

== Source tooling for Isabelle <sec:isar-tools>

`isar-tools` @isartools is a command-line tool for Isabelle/Isar projects. It
reads `.thy` and `ROOT` files as text and never runs Isabelle, so its checks
finish before the batch build has loaded its first session. It replaces
Python scripts this repository used before, and it is published under the MIT
license on PyPI, with a conda-forge recipe under review.

The formatter changes only layout: it indents proofs, removes trailing
whitespace and optionally wraps long lines, but it never changes a token, a
string, a cartouche or embedded ML. The checks report problems a batch build
either misses or reports late. This repository runs the groups for projects,
proofs and syntax, which report unfinished, abandoned and unclosed proofs,
theories no session reaches, malformed `ROOT` files and lexical errors, and the
locale check described below. The project commands read sessions, the theory
import graph, the class and locale hierarchy and every named declaration the way
`isabelle build -D` finds them. The statistics report sizes and proof counts,
and from a verbose build log they report which theories were elaborated more
than once, which this repository bounds per session in CI.

One check addresses a silent failure mode of Isabelle. Inside the header of a
`locale`, an identifier Isabelle does not know is read as a free variable and
generalized. An assumption that cites a renamed or deleted constant therefore
still builds, but now quantifies over an arbitrary function. The renames that
aligned the Isabelle names with this thesis, such as
#isalocale("analysis_contract") and #isalocale("numeric_domain"), are the kind
of change that would hide such a mistake. `isar check locales` reports every
identifier in a locale header that is neither a parameter nor bound nor used
elsewhere in the project. The check approximates Isabelle's inner syntax
lexically and is therefore a heuristic.

== One installation for every component <sec:packaging>

The repository needs Isabelle, the vendored solver, Python for its checks and
generators, and an OCaml toolchain for the exported analyzer and its browser
build. Pixi @pixi installs the Python side from conda-forge and PyPI and runs
every task, but the OCaml toolchain still comes from opam and Isabelle is
installed by hand. The goal is a single
`pixi install`. For the OCaml side this means that every package the analyzer
builds with must exist on conda-forge for the three platforms the repository
supports.

@fig:conda-forge shows what that takes. The native analyzer needs only the
compiler, Dune, Menhir and Zarith. The browser build adds `js_of_ocaml` and // thesis-refs: ignore
`wasm_of_ocaml` with a chain of libraries below them, and the formatter
`ocamlformat` needs a few more. Most of these libraries were not on
conda-forge, and two of the existing packages were outdated or missing on
Apple Silicon. We submitted the missing libraries `csexp`, `re`, `cmdliner`,
`yojson`, `seq`, `gen`, `sexplib0`, `stdlib-shims`, `ppx-derivers` and
`compiler-libs` as one recipe @cfstaged34872 and `isar-tools` as another @cfstaged34960; both
await review.

#let _cf = json("/shared/generated/conda-forge.json")
#figure(
  layout(size => context {
    set text(size: 6pt)
    set par(first-line-indent: 0pt, justify: false)
    let pkgs = _cf.packages
    let short(n) = if n.starts-with("ocaml-") and n != "ocaml-dune" { n.slice(6) } else { n }
    let body(n) = {
      let p = pkgs.at(n)
      let c = if p.available { vb.proved } else { vb.muted }
      box(
        stroke: 0.6pt + c,
        fill: if p.available { vb.proved.lighten(90%) } else { white },
        radius: 2pt,
        inset: 2.5pt,
        [#text(fill: c, if p.available { sym.ballot.check } else { sym.ballot }) #raw(short(n))],
      )
    }
    // Rows follow the tiers; a tier wider than the page wraps. Each row is
    // centred, and x and y are physical, so no two boxes overlap.
    let (gap, at, y) = (5pt, (:), 0pt)
    for t in pkgs.values().map(p => p.tier).dedup().sorted() {
      let names = pkgs.keys().filter(n => pkgs.at(n).tier == t)
      let rows = ((),)
      let width = 0pt
      for n in names {
        let w = measure(body(n)).width
        if width + w > size.width and rows.last() != () {
          rows.push(())
          width = 0pt
        }
        rows.last().push(n)
        width += w + gap
      }
      for r in rows {
        let total = r.map(n => measure(body(n)).width).sum() + gap * (r.len() - 1)
        let x = (size.width - total) / 2
        for n in r {
          let w = measure(body(n)).width
          at.insert(n, (x + w / 2, -y))
          x += w + gap
        }
        y += 22pt
      }
    }
    diagram(
      node-inset: 0pt,
      ..pkgs.keys().map(n => node(at.at(n), body(n), name: label("cf-" + n))),
      ..pkgs
        .keys()
        .map(n => pkgs
          .at(n)
          .deps
          .map(d => edge(
            label("cf-" + n),
            label("cf-" + d),
            "-|>",
            stroke: 0.4pt + vb.neutral,
          )))
        .flatten(),
    )
  }),
  kind: image,
  placement: auto,
  caption: [The OCaml packages the analyzer needs, as conda-forge packages
    (`ocaml-` prefixes dropped), each above the packages it needs. A checked,
    green box is published on conda-forge for every supported platform at the
    required version; an empty box is not. Status on #_cf.date.],
) <fig:conda-forge>

Packaging a real OCaml stack exposed problems in conda-forge's OCaml baseline
itself. A first test recipe failed on Linux because the `ocaml-dune` package
required a newer C library than it declared; we restored its C standard
library pin @cfdune17, and in testing that fix found and repaired a stale
module list in its cross-compilation bootstrap @cfdune18. The base libraries then failed for two
further reasons that we reported with a diagnosis. `OCAMLPATH` exposed only
the build environment, so Dune did not find OCaml libraries installed in the
host environment @cfdune19. And `ocamlcommon.cmxa` kept a path to its installation
prefix, which conda's relocation padded with NUL bytes, so that `ocamlopt`
later passed an invalid argument to the linker @cfocaml132. The maintainer fixed both
within a day. The one package still blocked holds the JavaScript stubs of Zarith: the
analyzer's WebAssembly build needs an unreleased upstream commit, and
conda-forge builds from releases, so we asked upstream for a release
@zarithstubs16.

== Changes to the verified solver <sec:upstream-td>

Voblint vendors the top-down solver formalization of
#cite(<tilscher26>, form: "prose") as a submodule, and two changes made for
this thesis were proposed upstream. The first restores the build under
Isabelle2025-2 @td12. The second removes the well-foundedness assumptions from the
solver's #isalocale("widening") and #isalocale("narrowing") classes @td13 and keeps them only in the
locales that prove termination. Those assumptions say that widening and
narrowing stabilize, which only termination proofs use. Partial correctness
needs the four order laws alone, and this is why a domain need not provide a
stabilizing widening (@sec:domain-contract).
Without the change, every domain instance would have to prove a
stabilization property that no soundness theorem of this thesis uses
(@sec:termination). The vendored submodule carries both changes, and both
upstream pull requests await review.

== From sources to the site and the thesis <sec:pipeline>

The repository keeps many artifacts that are derived from others: parsers
from a grammar, Isabelle registrations from a list of analyses, OCaml from the
theories, statistics from the sources, and a website and this thesis from all
of them. @fig:pipeline shows how they depend on one another.

#figure(
  {
    set text(size: 7.5pt)
    set par(first-line-indent: 0pt, justify: false)
    let src(pos, body, name) = node(
      pos,
      body,
      name: name,
      stroke: 0.7pt + vb.neutral,
      fill: vb.neutral.lighten(90%),
      corner-radius: 2pt,
      inset: 4pt,
    )
    let gen(pos, body, name) = node(
      pos,
      body,
      name: name,
      stroke: 0.7pt + vb.accent,
      fill: vb.accent.lighten(92%),
      corner-radius: 2pt,
      inset: 4pt,
    )
    let out(pos, body, name) = node(
      pos,
      body,
      name: name,
      stroke: 0.9pt + vb.proved,
      fill: vb.proved.lighten(92%),
      corner-radius: 2pt,
      inset: 4pt,
    )
    let e(a, b, ..args) = edge(a, b, "-|>", stroke: 0.6pt + vb.muted, ..args)
    diagram(
      spacing: (7mm, 7mm),
      src((0, 0), [VIMP grammar \ (YAML)], <g>),
      src((0, 1), [analysis manifest \ (YAML)], <m>),
      src((0, 2), [theories \ (`.thy`)], <t>),
      src((4, 2.2), [regression corpus], <r>),
      gen((1, 0), [Isabelle syntax, \ parser, printer], <gg>),
      gen((1, 1), [registrations, \ combined state], <mg>),
      gen((2, 2), [batch build], <b>),
      gen((3, 1), [OCaml export], <o>),
      gen((4, 1), [CLI and \ WebAssembly], <c>),
      src((5, 1), [explainer page \ (HTML)], <p>),
      gen((3, 3), [theory HTML, link map, \ theorem statements], <h>),
      gen((1, 3), [statistics, \ snippets], <s>),
      out((5, 0), [website and \ playground], <w>),
      out((5, 2), [thesis], <th>),
      e(<g>, <gg>),
      e(<m>, <mg>),
      e(<gg>, <b>),
      e(<mg>, <b>),
      e(<t>, <b>),
      e(<t>, <s>),
      e(<r>, <s>, bend: -15deg),
      e(<b>, <o>),
      e(<o>, <c>),
      e(<b>, <h>),
      e(<c>, <w>),
      e(<c>, <th>, label: [claims], label-side: right),
      e(<r>, <c>, label: [tests], label-side: left),
      e(<p>, <w>),
      e(<p>, <th>),
      e(<h>, <w>),
      e(<h>, <th>),
      e(<s>, <w>, bend: -35deg),
      e(<s>, <th>, bend: -10deg),
      e(<gg>, <c>, bend: 25deg),
    )
  },
  kind: image,
  placement: auto,
  caption: [How the repository derives its artifacts. Grey nodes are
    handwritten sources, blue nodes derived artifacts, green nodes what readers
    see. Theorem statements are read from the built session, snippets and
    statistics from the source files. Schematic: the tasks that implement each arrow are
    listed in `pixi.toml`.],
) <fig:pipeline>

Three manifests carry facts that would otherwise be repeated by hand. The
conda-forge manifest lists the OCaml packages of @fig:conda-forge. The VIMP
grammar is one file from which the Isabelle syntax, the analyzer's parser and
its source printer are generated, so the parser the proof trusts
(@sec:trust-boundary) and the syntax the theories use describe one language. The
analysis manifest names each analysis, the type of its abstract values, the
prefix its constants and facts share, and the theories that prove it sound. From
an entry the generator writes the registrations of a numeric domain
(@sec:engineering). Each proof applies the certificate of the domain's operation
bundle (#isathm("sound_nonrelational_ops.dg_analysis_execI")) and discharges the
remaining obligations for routing, the seeds, the solver and the initial
state by citing the domain's facts under names the prefix determines. The
generator also writes the combined state of @ch:cooperation with its dispatch
equations. It only places names, and Isabelle checks every generated proof. Some
parts are still written by hand: the key that orders an analysis's values for
display, the export list of code generation, the command-line and browser tables
that map an analysis name to its constructor, and the test that lists the
analyses independently of the manifest. A new analysis therefore needs its own
theories, a manifest entry and these edits.

The command-line tool and the browser adapter link the same exported module
and frontend. The command-line tool runs the analysis in a child process with a
wall-clock budget and reports a run that exceeds it as unfinished, with no
verdicts. For the browser, #raw("wasm_of_ocaml", lang: "sh") compiles the
adapter into a WebAssembly module that runs in a Web Worker the user can
cancel.

Everything a reader sees is derived in the same way. The website and this
document take their repository figures from the sources, their Isabelle names,
definitions and theorem statements from the theories and a built session, and
their analyzer output from the exported analyzer. The thesis also takes figures
and the Goblint comparison from the explainer page. Each such artifact is either
produced during the build or committed together with a check that regenerates it
and fails on a difference. Every check runs in continuous integration next to
the batch build, and the links into the rendered theories are checked again
against the published pages after each deployment. A stale name, statement,
figure or quoted output therefore fails the build instead of reaching the
reader. Prose that describes the repository in words is not checked. The checks
caught stale names, statements and figures while this thesis was written, and
typesetting it turned up a layout bug in Typst that we reported upstream
@typst8890. The pattern of a manifest, its generators and a
regenerate-and-compare check is not specific to Voblint; it applies to any
Isabelle development that shares facts with code, a website or a document.
