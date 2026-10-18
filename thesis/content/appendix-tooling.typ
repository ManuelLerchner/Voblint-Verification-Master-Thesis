#import "../lib/code.typ": isa, repo-blob
#import "../lib/theme.typ": vb

= `isar-tools`: Source Tooling for Isabelle <sec:isar-tools>


Isabelle checks what a theory means, but not how a project is maintained: whether
every theory is reached by a session, whether a proof was left unfinished,
whether two lemmas state the same fact, or whether a locale still says what it
said before a rename.
#link("https://github.com/ManuelLerchner/isar-tools")[`isar-tools`] @isartools
answers such questions from the sources alone. Written for this thesis and
published separately, it reads sources, build logs, and rendered HTML as text
and never runs Isabelle, so it also reads theories that do not yet check and
runs all its checks in a pre-commit hook.

Its formatter is designed to change only layout. Its checks, grouped by topic,
report unfinished and unclosed proofs, theories no session reaches, malformed `ROOT` files, and, when named, unused or duplicated lemmas, unused imports, leftover proof-search commands, and broken links. This repository runs all of them. Project views list the sessions, the import graph, the class and locale hierarchy, and every named declaration, and statistics report sizes and
proof counts. An extraction layer was built for the remaining tooling of this
repository, in particular to keep the website and this thesis in sync with the
theories: the theorem statements of this thesis come from
`isar project extract`, the notation tables of the thesis and the explainer
from `isar project notation`, and the links into the rendered theories from
`isar project anchors`. Among related tools, the Isabelle Linter
@isabellelinter runs inside Isabelle and lints proof style, and
`isabelle-query` @isabellequery parses the sources without Isabelle and
answers queries about entries, call graphs, and `sorry`s.

== A silent failure in locale headers

One check addresses a mistake the batch build cannot see. Inside the header of
a `locale`, an identifier Isabelle does not know is read as a free variable and
generalized. An assumption that cites a renamed or misspelled constant
therefore still builds, but now quantifies over an arbitrary function. In
@fig:locale-check, the assumption cites a misspelling of the constant defined
above it, and `isar check locales` reports the identifier.



The check flags identifiers in a locale header that appear to be neither
parameters nor locally bound and have no matching declaration. It approximates
Isabelle's inner syntax lexically and is therefore a heuristic.

#figure(
  {
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
  },
  kind: image,
  placement: none,
  caption: [A locale assumption citing a misspelled constant, which Isabelle
    accepts, and the report of `isar check locales` on this
    #link(repo-blob + "thesis/shared/code/isar-locale")[theory], which a test reruns.],
) <fig:locale-check>

== A hidden cost: re-elaborated theories

A second problem also leaves the build green. A session inherits only the
heaps of its parent chain, so a library theory that is not an ancestor is elaborated again in every session that imports it. In this repository, this once cost 19% of a clean build. `isar stats build` finds it in a build log, and
continuous integration enforces a budget per library session.
