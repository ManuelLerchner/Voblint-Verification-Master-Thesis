#import "../lib/math.typ": *
#import "../lib/theme.typ": vb
#import "../lib/code.typ": (
  fixture, isaconst, isalocale, isathm, isatype, oblig, site, site-url, thy-badge,
)
#import "../lib/figures.typ": verdict
#import "../lib/claims.typ": claim-ref

= Reading This Thesis <reading-guide>

The thesis can be read on paper, but it is designed to be read on screen. It closely
follows a machine-checked Isabelle/HOL development, and most of its definitions and
theorems link to the #link(site("Voblint/index.html"))[HTML rendering of the theories].
A single #link(site("formalization.pdf"))[PDF export of the whole formalization] is available as
well. The project site at #link(site-url)[#site-url.trim("https://", at: start)] also
hosts an #link(site("index.html"))[explainer] that animates several of the constructions,
a #link(site("profiling.html"))[profiling page] with the full benchmark data and CPU
profiles, the #link(site("playground.html"))[playground], which runs the analyzer in
the browser on any VIMP program, and a #link(site("paper.pdf"))[preprint] that summarizes
the soundness argument @lerchner26paper.

Each kind of object the text refers to has its own marker, and most markers are also links.
An Isabelle name opens its definition, a program opens the playground, and a fixture opens
its file in the repository.

@sec:isabelle explains how to read the Isabelle listings, and @app:notation lists the
mathematical notation shared by the theories and the text.

#{
  set text(size: 9.5pt)
  set par(justify: false, first-line-indent: 0pt)
  table(
    columns: (auto, 1fr),
    align: (left + horizon, left + horizon),
    stroke: none,
    inset: (x: 4pt, y: 4.5pt),
    table.hline(),
    [*marker*], [*meaning*],
    table.hline(stroke: 0.5pt),
    [#isaconst("run_voblint") \ #isathm("run_voblint_source_sound") \ #isatype(
        "analysis_config",
      ) \ #isalocale("activation_coverage")],
    [Monospace text marks an Isabelle name, blue for a constant, green for a
      theorem, purple for a type, and teal for a locale. Every such name links
      to its definition in the rendered theories, and the thesis build fails
      if a link has no target.],
    [#oblig("INIT"), #oblig("TOTAL")],
    [Teal small capitals mark an obligation of the coverage contract
      (@sec:contract), linked to the locale assumption that states it.],
    [#ctor("FunctionEntry"), #keyw("while")],
    [Purple sans-serif text marks a datatype constructor in notation, and
      bold maroon text a keyword of the source language VIMP.],
    [Section title #thy-badge("Voblint_CLI", "Analysis_Run")],
    [A small blue #raw("thy") box beside a heading marks a section that
      presents one theory, and opens that theory's page.],
    [`(* src/… *)` #h(0.3em) #box(
        stroke: 0.5pt + vb.accent,
        inset: (x: 0.4em, y: 0.12em),
        text(size: 0.78em, fill: vb.accent.darken(20%))[Isabelle],
      )],
    [A framed code block with a blue Isabelle tag is an Isabelle listing.
      Definitions and theorem statements are lifted verbatim from the theories, and every build checks them against their
      source. The first line names the source file, and the listing links to
      the declaration.],
    [#box(
      stroke: 0.5pt + vb.keyword,
      inset: (x: 0.4em, y: 0.12em),
      text(size: 0.78em, fill: vb.keyword.darken(20%))[VIMP #sym.arrow.tr],
    )],
    [A framed code block with a maroon VIMP tag is a source program. The tag
      opens the program in the browser playground,
      with the analysis settings the text uses, so every analyzer run can be
      repeated and varied.],
    [#verdict("PROVED") #verdict("REFUTED") \ #verdict("UNKNOWN") #verdict("DEAD")],
    [A coloured monospace word on a tinted background is a verdict as the
      analyzer reports it (@sec:verdict-meaning).],
    [#claim-ref("intro-answers")],
    [An underlined blue name marks a _claim_, a registered analyzer run. Every
      verdict and state of Voblint quoted in the text is read from a claim,
      which the build repeats, and the name opens the run in the playground.],
    [#fixture(
      "21-context-sensitivity/01-unbounded_context_chain_diverges.vimp",
      label: "01-unbounded_…",
    )],
    [A blue monospace file name marks a fixture of the regression corpus,
      linked to its file in the repository.],
    [#signval("+"), $absval(ivl(1, 9))$, #absval(raw("1+2ℤ"))],
    [A light purple background marks an abstract value, as opposed to a
      concrete integer or set of stores.],
    table.hline(),
  )
}
