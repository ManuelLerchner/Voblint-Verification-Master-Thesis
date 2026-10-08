#import "../lib/code.typ": isa, isacmd, isaconst, isalocale, isathm, repo-blob
#import "@preview/fletcher:0.5.8": diagram, edge, node
#import "../lib/theme.typ": vb

= Engineering and Tooling <ch:tooling>

A formalization of this size needs work around the proof assistant as well as
inside it. Its theories must be formatted and checked for unfinished proofs,
its names must stay consistent with the prose that cites them, and a new
contributor must be able to install everything the build needs. For Isabelle,
comparatively little project-level tooling is available outside the distribution itself.
The resulting gap has been noted by Isabelle users as well, for instance in a
comment on a recent blog post by Paulson @paulson26lean, which observes that
Isabelle's own development uses almost no standard tooling @halbgefressen26.

The need of such tooling grows with AI assistance. Many proofs and a large share of the
surrounding code of this development were written by agents (see #link(<ai-use>)[the statement on the use of generative AI]). An agent can
produce a plausible change quickly, but it cannot be trusted to keep the
cross-references of a large development consistent, and a reviewer cannot read every line
it writes. What made the agent work usable at this scale was deterministic
tooling around it. An agent's change counts as done only when these checks pass, so
the checks, not the agent, decide whether the repository is consistent.

This chapter describes the published repository, and the tools and upstream
changes made for this thesis and published separately. They are engineering contributions: nothing in them
is proved.

== The Voblint repository <sec:voblint-repo>

Everything this thesis describes is published in one repository: the Isabelle
theories, a submodule reference to the vendored solver, whose repository is
private (@sec:upstream-td), the exported analyzer with its command-line tool and playground, the
regression corpus, and the sources of this thesis. The project site hosts the
playground, the explainer and the rendered theories that every Isabelle name in
this thesis links to.

A development of this size drifts when one fact is written down twice. The
repository therefore keeps a few sources and derives everything else from them
(@fig:pipeline). One grammar file yields the Isabelle syntax of VIMP, the
analyzer's parser and its printer. The parser lies outside the proof and hands
the proved analyzer its syntax tree (@sec:trust-boundary), but it and the
Isabelle syntax are generated from the same language description. An
analysis manifest names each analysis, its value type and the theories that
prove it sound. A generator writes from it the registration of each numeric
domain (@sec:instances-supply) and the combined state of @ch:cooperation, and
Isabelle checks every generated proof. The generator exists because the
repetition lies outside what a theory can express: each domain is registered
once per context policy it supports, for every update rule, and the combined
state has one field per analysis, of differing types. With dependent types, a heterogeneous list indexed
by these types could express it inside the logic @chlipala13cpdt[ch. 9]; HOL's
simple types cannot. #isaconst("run_voblint") itself reaches OCaml through
#isacmd("export_code") (@sec:codegen). Because the derived files are checked
against their sources, a stale name, statement or quoted output fails the build
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
and compared with what the built session proves, quoted analyzer results are
re-run against the analyzer, each VIMP listing's playground link is decoded
from the PDF and compared with the listing, and repository figures come from a
measurement script. A rename, a changed statement or a changed result
therefore fails the build, and another check warns when the text shows a
statement before the entities it uses.

The checks run in layers ordered by cost (@fig:gates), from hooks triggered by
the staged files to continuous integration, which reruns the checks on a fresh
runner, reusing cached results for unchanged inputs, together with the tests of
@sec:eval-corpus. Only the main branch is deployed, and only after the rendered
theories, the formalization PDF and this thesis build. All layers invoke the
same named Pixi tasks, and a further check keeps the local `verify` task and
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

== `isar-tools`: source tooling for Isabelle <sec:isar-tools>

Isabelle checks what a theory means, but not how a project is kept: whether
every theory is reached by a session, whether a proof was left unfinished,
whether two lemmas state the same fact, or whether a locale still says what it
said before a rename.
#link("https://github.com/ManuelLerchner/isar-tools")[`isar-tools`] @isartools
answers such questions from the sources alone. Written for this thesis and
published separately, it reads sources, build logs and rendered HTML as text
and never runs Isabelle, so it also reads theories that do not yet check and
runs all its checks in a pre-commit hook.

Its formatter is designed to change only layout. Its checks, grouped by topic,
report unfinished and unclosed proofs, theories no session reaches and
malformed `ROOT` files and, when named, unused or duplicated lemmas, unused
imports, leftover proof-search commands and broken links; this repository runs
all of them. Project views list the sessions, the import graph, the class and
locale hierarchy and every named declaration, and statistics report sizes and
proof counts. An extraction layer was built for the remaining tooling of this
repository, in particular to keep the website and this thesis in sync with the
theories: the theorem statements of this thesis come from
`isar project extract`, the notation tables of the thesis and the explainer
from `isar project notation`, and the links into the rendered theories from
`isar project anchors`. Among related tools, the Isabelle Linter
@isabellelinter runs inside Isabelle and lints proof style, and
`isabelle-query` @isabellequery parses the sources without Isabelle and
answers queries about entries, call graphs and `sorry`s.

=== A silent failure in locale headers

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

=== A hidden cost: re-elaborated theories

A second problem also leaves the build green. A session inherits only the
heaps of its parent chain, so a library theory that is no ancestor is
elaborated again in every session that imports it; in this repository that
once cost 19% of a clean build. `isar stats build` finds it in a build log, and
continuous integration enforces a budget per library session.

== Changes to the verified solver <sec:upstream-td>

Voblint vendors the top-down solver formalization of Tilscher et al.
@tilscher26 as a submodule. Four changes made for this thesis, each of use to
any downstream user, were proposed upstream.

- The first restores the build under Isabelle2025-2 @td15.
- The second removes the well-foundedness assumptions from the solver's
  #isalocale("widening") and #isalocale("narrowing") classes; termination is
  proved in locales that state their own well-foundedness assumptions @td13. Those assumptions say that
  widening and narrowing stabilize, which only termination proofs use. Partial
  correctness needs the four order laws alone, so a domain need not provide a
  stabilizing widening (@sec:domain-carrier-laws), and no domain instance has
  to prove a property that no soundness theorem uses (@sec:termination).
- The third renames short record fields and constructors, such as `c`, `W`
  and `N`, that took these names away from downstream theories, and adds one
  interface theory per solver family @td14.
- The fourth adds solver facts that Voblint had proved on its side although
  they speak only about the solver's own definitions @td16, among them that a
  returned run of the executable solver lies in the solver's domain
  (#isathm("solve_dom_of_solve_c")) and that a terminating solve returns a
  finite set of stable unknowns (#isathm("finite_stabl_solve")), both used by
  #isathm("td_certified_solver") (@sec:cert-param).

At the time of writing, all four pull requests await review. The vendored copy
carries the second to fourth on an older upstream revision; the first repairs a
later upstream change. The solver's
repository is private and accessible only by invitation, so the development
cannot yet be built from public sources alone. There are plans to publish the
solver in the Archive of Formal Proofs, which would make the whole development
buildable by anyone.
