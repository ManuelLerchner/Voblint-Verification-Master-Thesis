#import "../lib/code.typ": isaconst, isalocale, isathm, isatype
#import "../lib/figures.typ": playground-figure, playground-settings
#import "../lib/math.typ": lbot
#import "@preview/fletcher:0.5.8": diagram, edge, node
#import "../lib/theme.typ": vb

#let _todo(body) = text(fill: vb.unproved)[TODO: #body]

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
@sec:voblint-repo for everything the build does not see. An agent's change counts as done only when these checks pass, so
the checks, not the agent, decide whether the repository is consistent. The
extension of @ch:cooperation followed this pattern.

This chapter describes the published repository, and the tools and upstream
changes made for this thesis and published separately. They are engineering contributions: nothing in them
is proved. The source tooling and the solver changes are in use: the
repository's continuous integration runs them.

== The Voblint repository <sec:voblint-repo>

Everything this thesis describes is published in one repository under the
BSD-3-Clause license (@fig:repos, right): the Isabelle theories, the vendored
solver under its own license, the exported OCaml analyzer with its
command-line tool, the browser playground and the explainer site, the
regression corpus, and the sources of this thesis. A `CITATION.cff` file states
how to cite it. The project site hosts the playground, the explainer, and the
rendered theories that every Isabelle name in this thesis links to.

Continuous integration runs on every pull request and every push to the main
branch. It builds every session, regenerates the exported analyzer and fails
if the result differs from the checked-in code, runs the regression corpus
with the native and the browser build, and runs the checks described next, including the warning-strict build of this
document.

Much of the repository is derived from a few sources, and each derived artifact
is either produced during the build or committed together with a check that
regenerates it and fails on a difference. One grammar file yields the Isabelle
syntax, the analyzer's parser and its printer, so the parser the proof trusts
(@sec:trust-boundary) and the syntax of the theories describe one language. An
analysis manifest names each analysis, its value type, the prefix of its facts
and the theories that prove it sound; a generator writes from it the
registration of a numeric domain (@sec:instances-supply) and the combined state
of @ch:cooperation, and Isabelle checks every generated proof. This document
takes its Isabelle names, theorem statements, analyzer output and repository
figures from the theories, a built session and the analyzer in the same way,
so a stale name, statement or quoted output fails the build instead of
reaching the reader. Prose that describes the repository in words is not
checked.

#figure(
  {
    // Each preview links to its repository.
    let card(url, img) = link(url, box(
      stroke: 0.5pt + vb.frame,
      radius: 3pt,
      clip: true,
      image("/assets/" + img, width: 100%),
    ))
    grid(
      columns: (1fr, 1fr),
      column-gutter: 8pt,
      card("https://github.com/ManuelLerchner/isar-tools", "isar-tools-repo-social-preview.jpg"),
      card(
        "https://github.com/ManuelLerchner/Voblint-Verification-Master-Thesis",
        "voblint-repo-social-preview.jpg",
      ),
    )
  },
  kind: image,
  placement: auto,
  caption: [The repositories of `isar-tools` (left) and of this formalization
    (right) on GitHub. Each preview links to its repository.],
) <fig:repos>

== Source tooling for Isabelle <sec:isar-tools>

Formatting and simple source checks should not wait for a batch build that
loads every session first. `isar-tools` @isartools is a command-line tool for
Isabelle/Isar projects (@fig:repos, left) that reads `.thy` and `ROOT` files as text and never
runs Isabelle, so its checks finish before the build has loaded its first
session. It replaces
Python scripts this repository used before, and it is published under the MIT
license on PyPI and conda-forge.


The formatter changes only layout: it indents proofs, removes trailing
whitespace and optionally wraps long lines, but it never changes a token, a
string, a cartouche or embedded ML. The checks report problems a batch build
either misses or reports late. This repository runs the groups for projects,
proofs and syntax, which report unfinished, abandoned and unclosed proofs,
theories no session reaches, malformed `ROOT` files and lexical errors, and the
locale check described below. The project commands read sessions, the theory
import graph, the class and locale hierarchy and every named declaration the way
`isabelle build -D` finds them. Three more read what a document needs from the
theories: the source of a declaration, the symbol a declaration introduces
through its mixfix, and the anchors of the rendered theories. The generators of
this thesis use them. Its theorem statements come from `isar project extract`,
the notation table of the README and the explainer from `isar project notation`,
and its links into the rendered theories are resolved against `isar project
anchors`. The statistics report sizes and proof counts,
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

== Changes to the verified solver <sec:upstream-td>

Voblint vendors the top-down solver formalization of
#cite(<tilscher26>, form: "prose") as a submodule. Using it as a library
exposed several things that every downstream user would have to work around,
and four changes made for this thesis were proposed upstream.

- The first restores the build under Isabelle2025-2 @td15.
- The second removes the well-foundedness assumptions from the solver's
  #isalocale("widening") and #isalocale("narrowing") classes and keeps them
  only in the locales that prove termination @td13. Those assumptions say that
  widening and narrowing stabilize, which only termination proofs use. Partial
  correctness needs the four order laws alone, so a domain need not provide a
  stabilizing widening (@sec:domain-carrier-laws), and no domain instance has
  to prove a property that no soundness theorem uses (@sec:termination).
- The third renames short record fields and constructors, such as `c`, `W`
  and `N`, that took these names away from downstream theories, and adds one
  interface theory per solver family that hides the generic field names
  @td14.
- The fourth adds solver facts that Voblint had proved on its side although
  they speak only about the solver's own definitions @td16, among them that a
  returned run of the executable solver lies in the solver's domain
  (#isathm("solve_dom_of_solve_c")) and that a terminating solve returns a
  finite set of unknowns (#isathm("finite_stabl_solve")), both used in
  @sec:cert-param.

All four pull requests await review, and the vendored submodule carries them.
It also carries local changes not proposed upstream: the operator classes moved
out of the update-rule theory, a build on the HOL-Library heap, and further
facts about the solver's states.
