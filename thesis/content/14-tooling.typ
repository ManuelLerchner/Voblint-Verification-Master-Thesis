#import "../lib/code.typ": isa, isacmd, isaconst, isai, isalocale, isathm, repo-blob
#import "@preview/fletcher:0.5.8": diagram, edge, node
#import "../lib/theme.typ": vb
#import "../lib/claims.typ": claim-ref

= Engineering and Tooling <ch:tooling>

Every theorem statement, Isabelle name, and analyzer result quoted in this
thesis is derived from the sources and rechecked on every change
(@sec:voblint-repo). This chapter describes the repository and the tools that
make this hold, and the changes made to the vendored solver. Isabelle's batch
build checks every proof, but it does not check that the prose cites existing
names, that every theory belongs to a session, or that a locale assumption
still mentions the constants its author meant.

The need grows with AI assistance. Agents wrote many proofs and a large share
of the surrounding code of this development (see #link(<ai-use>)[the statement
  on the use of generative AI]). An agent produces a plausible change quickly but
cannot be trusted to keep the cross-references of a large development
consistent, and a reviewer cannot read every line it writes. An agent's change
therefore counts as done only when deterministic checks pass, so the
consistency of the repository does not depend on the agent's judgment. The
repository, the tools, and the upstream changes made for this thesis are
engineering contributions, and nothing in them is proved.

== The Voblint repository <sec:voblint-repo>

One repository holds the Isabelle theories, a submodule reference to the
vendored solver, whose fork is private, the exported analyzer with its
command-line tool and playground, the regression corpus, and the sources of
this thesis. Each release is archived on Zenodo with a citable DOI @voblint.
The archive, like the repository, refers to the solver as a submodule and does
not contain its theories (@sec:upstream-td).
The project site hosts the playground, the explainer, and the rendered theories
that every Isabelle name in this thesis links to.

A fact written down in two places drifts as the development changes, so the
repository keeps a few sources and derives everything else from them
(@fig:pipeline). One grammar file yields the Isabelle syntax of VIMP, the
analyzer's parser, and its printer, so the unverified parser
(@sec:trust-boundary) and the Isabelle syntax come from one language
description. #isaconst("run_voblint") reaches OCaml through
#isacmd("export_code") (@sec:codegen). Because the derived files are checked
against their sources, a stale name, statement, or quoted output fails the
build instead of reaching the reader.

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
      src((0, 5), link(repo-blob + "src")[theories, built session \ and analyzer], <t>),
      out(
        (1, 4),
        link(repo-blob + "codegen/generated/ml/Voblint_Generated.ml")[generated OCaml analyzer],
        <t1>,
      ),
      out(
        (1, 5),
        link(repo-blob + "thesis/shared/generated")[theorem statements, snippets, links],
        <t2>,
      ),
      out(
        (1, 6),
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
    them, each generated during the build or committed with a check that
    regenerates it. Each box links to its file.],
) <fig:pipeline>

For the thesis, each Isabelle name goes through a helper that a check resolves
against the theories and links to the rendered theories. Theorem statements are
lifted from the theories and compared with what the built session proves. Each
analyzer result the text quotes is registered as a named run of the analyzer,
which the build repeats and compares with the quoted output. A tag such as
(claim #claim-ref("intro-answers")) in a caption or sentence names such a run and links to
it in the playground. These tags are unrelated to the claims
#isai("cover v c") of @ch:traces. A fixture is a program of the regression
corpus (@sec:eval-corpus). Each VIMP listing's playground link is decoded from
the PDF and compared with the listing, and repository figures come from a
measurement script.

The checks run in layers ordered by cost (@fig:gates), from hooks on the staged
files to continuous integration, which reruns them on a fresh runner together
with the tests of @sec:eval-corpus. Only the main branch is deployed, and only
after the rendered theories, the formalization PDF, and this thesis build.

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
    representative checks. The published links are checked after deployment.
    Each box links to its configuration.],
) <fig:gates>

== `isar-tools`: source tooling for Isabelle <sec:isar-tools>

Isabelle's build does not check project properties such as whether every
theory is reached by a session, whether a proof was left unfinished, whether
two lemmas state the same fact, or whether a locale still says what it said
before a rename. #link("https://github.com/ManuelLerchner/isar-tools")[`isar-tools`]
@isartools, written for this thesis and published separately, answers such
questions from the sources alone. It reads sources, build logs, and rendered
HTML as text and never runs Isabelle, so it also reads theories that do not yet
check and runs in a pre-commit hook.

Besides a formatter that changes only layout, it reports unfinished and
unclosed proofs, theories no session reaches, malformed `ROOT` files, and, on
request, unused or duplicated lemmas, unused imports, leftover proof-search
commands, and broken links. Its extraction layer lifts the theorem
statements, the notation tables, and the anchors into the rendered theories
that this thesis and the website use. Among related tools, the Isabelle Linter
@isabellelinter runs inside Isabelle and lints proof style, and
`isabelle-query` @isabellequery also parses the sources without Isabelle and
answers queries about entries, call graphs, and `sorry`s. What `isar-tools`
adds is the checks that guard a project against silent failures, such as the
locale check below, and the extraction that feeds this thesis.

=== A silent failure in locale headers

Inside the header of a `locale`, an identifier Isabelle does not know is read
as a free variable and generalized. An assumption that cites a renamed or
misspelled constant therefore still builds, and the batch build reports
nothing. The assumption must then hold for every function in place of the
intended constant, which is far stronger than intended. In @fig:locale-check,
choosing the function that maps every argument to the set of all integers
forces `step` to be constant. An interpretation for an intended instance then
fails late, and theorems proved inside the locale may hold only vacuously, the
risk that the non-vacuity instances of @sec:nonvacuity rule out for the main
theorem. `isar check locales` flags identifiers in a locale header that appear
to be neither parameters nor locally bound and have no matching declaration
(@fig:locale-check). It approximates
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
  caption: [A locale assumption citing a misspelled constant,
    which Isabelle accepts, and the report of `isar check locales` on this
    #link(repo-blob + "thesis/shared/code/isar-locale")[theory], which a test
    reruns. The listing is an excerpt, lines 4 to 8 of the theory, and the
    report counts lines in the whole file.],
) <fig:locale-check>

=== A hidden cost: rechecked theories

A session reuses only the prebuilt images of its parent chain, so a library
theory outside that chain is checked again in every session that imports it.
The build stays green, but in this repository this once cost 19% of a clean build.
`isar stats build` finds such theories in a build log, and continuous
integration enforces a budget per library session.

== Changes to the verified solver <sec:upstream-td>

Voblint vendors the top-down solver formalization of Tilscher et al.
@tilscher26 as a submodule. Four changes made for this thesis were proposed
upstream.

- The first restores the build under Isabelle2025-2 @td15.
- The second moves the well-foundedness assumptions, which say that widening
  and narrowing stabilize, out of the solver's #isalocale("widening") and
  #isalocale("narrowing") classes into the locales of the termination proofs
  @td13. Partial correctness needs only the four order laws, so a domain need
  not provide a stabilizing widening (@sec:domain-carrier-laws,
  @sec:termination).
- The third renames short record fields and constructors, such as `c`, `W`
  and `N`, that took these names away from downstream theories, and adds one
  interface theory per solver family @td14.
- The fourth adds facts about the solver's own definitions that Voblint had
  proved on its side @td16, among them that a returned run of the executable
  solver lies in the solver's domain (#isathm("solve_dom_of_solve_c")) and that
  a terminating solve returns a finite set of stable unknowns
  (#isathm("finite_stabl_solve")), both used by
  #isathm("td_certified_solver") (@sec:cert-param).

The vendored copy applies the second to fourth change, together with its own
build fix for Isabelle2025-2, to the upstream revision `af78761` of March 2026.
The pull requests port the changes to the current upstream revision, whose
build the first restores. At the time of writing, all four await review. The
partial-correctness theorem Voblint uses is therefore that of this modified
copy, which every build checks but whose changes upstream has not yet
reviewed. The fork that holds the vendored copy is private and accessible only
by invitation, so the development cannot yet be built from public sources
alone. Publishing the solver in the Archive of Formal Proofs, as
planned, would make the whole development buildable by anyone.
