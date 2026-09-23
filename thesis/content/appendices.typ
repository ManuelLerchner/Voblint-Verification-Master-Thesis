#import "../lib/math.typ": *
#import "../lib/code.typ": isaconst, isai, isalocale, isasession, isathm, isatype
#import "../lib/sources.typ": proved
#import "../lib/stats.typ": stat, stat-keys
#import "../lib/alignment.typ": alignment, alignment-mark, alignment-table
#import "../lib/notation.typ": notation-table
#import "../lib/theme.typ": vb

= Session Structure <app:theory-map>

@fig:appendix-sessions layers every session of the development by what it
rests on: its parent, the sessions its `ROOT` entry lists, and the sessions its
theories import. The main parent chain runs from #isasession("Voblint_VIMP")
through #isasession("Voblint_CFG"), #isasession("Voblint_Framework"),
#isasession("Voblint_Exec"), #isasession("Voblint_Routing") and
#isasession("Voblint_Result") to #isasession("Voblint_Nonrelational"), which the
five numeric analysis sessions inherit. Their combination reaches
#isasession("Voblint_CLI"), and #isasession("Voblint_Codegen") exports it. The
relational witness in #isasession("Voblint_Analysis_Relational") has parent
#isasession("Voblint_Exec") and does not rest on the pointwise reuse chain. All
sessions build on Isabelle/HOL @nipkow02 and its HOL-Library session.
HOL-Computational\_Algebra enters with the numeric analyses, and
#isasession("Voblint_VIMP") takes the reflexive-transitive closure of its
step relations from HOL-IMP @nipkow14. Two entries of the Archive of Formal Proofs
enter the build: _Deriving Class Instances for Datatypes_ @sternagel15deriving
derives the linear orders on VIMP's syntax, and _Root-Balanced Tree_
@nipkow17rbt is a dependency of the vendored solver development @tilscher26.

// The explainer's cross-section, redrawn at text width from the geometry of
// its extracted SVG: layer names, session labels, widths and thicknesses are
// read from the file, so the drawing follows the page.
#let _strata = {
  let svg = read("/shared/generated/svg/strata.svg")
  let fills = (:)
  for m in svg.matches(regex("\\.stratum-(\\w+) rect \\{ fill: (#[0-9A-Fa-f]{6}); \\}")) {
    fills.insert(m.captures.at(0), rgb(m.captures.at(1)))
  }
  svg
    .matches(regex("(?s)<g class=\"stratum stratum-(\\w+)\"[^>]*>(.*?)</g>"))
    .map(g => {
      let body = g.captures.at(1)
      (
        layer: g.captures.at(0),
        name: body.match(regex("class=\"stratum-name\"[^>]*>([^<]*)<")).captures.at(0),
        parts: body
          .matches(
            regex(
              "<rect x=\"[\\d.]+\" y=\"[\\d.]+\" width=\"([\\d.]+)\" height=\"([\\d.]+)\"[^>]*>(?:</rect>)?<text[^>]*>([^<]*)<",
            ),
          )
          .map(m => (
            width: float(m.captures.at(0)),
            height: float(m.captures.at(1)),
            label: m.captures.at(2),
          )),
      )
    })
    .map(l => l + (fill: fills.at(l.layer, default: rgb("#D9C8A2"))))
}

#figure(
  {
    set text(size: 7.5pt)
    set par(first-line-indent: 0pt, justify: false)
    let bar = 300pt
    let unit = bar / 720
    grid(
      columns: (1fr, bar),
      column-gutter: 8pt,
      ..(
        _strata
          .map(l => {
            let h = calc.max(l.parts.first().height * 0.5pt, 13pt)
            (
              align(right + horizon, text(fill: vb.neutral, l.name)),
              stack(dir: ltr, ..l.parts.map(p => box(
                width: p.width * unit,
                height: h,
                fill: l.fill.lighten(55%),
                stroke: if l.layer == "bedrock" {
                  (paint: vb.neutral, thickness: 0.5pt, dash: "dashed")
                } else { 0.5pt + vb.neutral.lighten(40%) },
                align(center + horizon, text(
                  font: "DejaVu Sans Mono",
                  weight: "bold",
                  fill: vb.neutral,
                  p.label,
                )),
              ))),
            )
          })
          .flatten()
      ),
    )
  },
  kind: image,
  caption: [The sessions in cross-section, after the project explainer. Each session
    lies one layer above the highest session it rests on. A layer's thickness
    grows with its lines, sessions sharing a layer split its width by their
    lines, the examples are drawn as one layer, and the bedrock is not to scale.
    Layers show order, not every dependency.],
) <fig:appendix-sessions>

// The theory of an anchor is the page its verified link points into.
#let _links = json("/shared/generated/links.json")
#let anchor-item(kind, name) = (
  const: isaconst,
  thm: isathm,
  type: isatype,
  locale: isalocale,
).at(kind)(name)
#let anchor-theory(kind, name) = {
  let key = kind + ":" + name
  assert(key in _links.links, message: "Missing Isabelle HTML link for " + key)
  let page = _links.links.at(key).split("#").first()
  let theory = page.split("/").last().trim(".html", at: end).split(".").last()
  link(_links.base + page, text(font: "DejaVu Sans Mono", size: 7pt, fill: vb.neutral, theory))
}

= Formalization Anchor Index <app:anchors>

@tab:anchors lists, for each concept the chapters explain, the Isabelle item
that defines or proves it, linked to its declaration, and the theory that
contains it, read from the verified link map.

#[
  #show figure: set block(breakable: true)
  #figure(
    {
      set text(size: 8pt)
      set par(first-line-indent: 0pt, justify: false)
      let rows = toml("/shared/anchors.toml").anchor
      table(
        columns: (1fr, auto, auto, auto),
        align: (left + top, right + top, left + top, left + top),
        stroke: none,
        inset: (x: 4pt, y: 2.4pt),
        table.header(
          table.hline(stroke: 0.5pt),
          [*Concept*], [*Ch.*], [*Isabelle theory*], [*Item*],
          table.hline(stroke: 0.4pt),
        ),
        ..rows
          .map(r => (
            r.concept,
            context {
              let h = query(label(r.chapter)).first()
              link(h.location(), str(counter(heading).at(h.location()).first()))
            },
            anchor-theory(r.kind, r.name),
            anchor-item(r.kind, r.name),
          ))
          .flatten(),
        table.hline(stroke: 0.5pt),
      )
    },
    kind: table,
    caption: [Concepts and the Isabelle items that define or prove them, with
      the chapter that explains each. Blue items are definitions, green
      theorems, purple types and teal locales.],
  ) <tab:anchors>
]

@tab:notation lists the notation the theories declare, generated from the
declarations, in three groups: operators and relations of the semantics and the
abstraction; the semantic sets, each with a global form listing every parameter
and a short form inside the coverage locale, which fixes them; and proof-local
locale abbreviations, which exported theorems never contain.

#[
  #show figure: set block(breakable: true)
  #figure(
    notation-table(),
    kind: table,
    caption: [The notation the theories declare. A symbol's argument names are
      placeholders; the linked declaration fixes their types. For
      #isai("\<G>"), the declaration is the classifier a program supplies; in
      the theorems it is a parameter.],
  ) <tab:notation>
]

Beyond the table, $lle$, $lbot$, $ltop$ and $ljoin$ denote order, bottom, top
and join of the carrier in use. The outer #ctor("Bot") of #isatype("lifted") is
a constructor separate from a payload's bottom (@sec:lift).

= Comparison with Goblint <app:goblint-alignment>

@tab:goblint-alignment records architectural correspondence with Goblint; it
does not assert that the two analyzers compute the same result. Its rows are
generated from the project's explainer page, which condenses the repository's
alignment register, and link to Goblint's source at revision
#link("https://github.com/goblint/analyzer/tree/" + alignment.revision)[#raw(
  alignment.revision.slice(0, 8),
)]
and to Voblint's declarations.

#[
  #show figure: set block(breakable: true)
  #figure(
    alignment-table(),
    kind: table,
    caption: [Goblint constructs and their Voblint counterparts:
      #alignment-mark("modeled") modeled, #alignment-mark("simplified")
      simplified (weaker or differently encoded), #alignment-mark("absent") not
      modeled. The status is architectural, not proof status.],
  ) <tab:goblint-alignment>
]

= Main Statements and Regression Corpus <app:statements>

This appendix lists the headline theorems in the order of the proof chain,
each lifted from its theory without the proof. The thesis build checks that the
built session proves it there. A source run is matched by a graph run whose
configuration ends a valid trace:

#proved("csim_star", note: [Simulation of source runs (@sec:csim).])

#proved("source_run_has_ltr", note: [Source runs have valid traces
  (@sec:source-bridge).])

The context-indexed collecting semantics is bounded by any cover meeting the
five local obligations, and a solved D/G table meets them:

#proved("activation_collect_sound", note: [Coverage from the local obligations
  (@sec:consequences).])

#proved("activation_collect_dg_sound", note: [Coverage from a solved D/G table
  (@sec:eq-discharge). The statement is inside the routed context locale, whose
  assumptions it inherits.])

The endpoints concern #isaconst("run_voblint") for every configuration it
accepts and take solver termination as a premise. Source-level soundness,
#isathm("run_voblint_certified_source_sound"), is displayed in @sec:headline.
The per-check and dead-code endpoints read:

#proved("run_voblint_check_sound", note: [Check verdicts at the point a run
  reaches (@sec:verdicts).])

#proved("run_voblint_dead_check_unreached", note: [A `DEAD` check is
  unreachable (@sec:verdicts).])

The framework instantiated with a mixed flow-sensitive Sign analysis bounds the
collecting semantics of one program at every node:

#proved("mf_ltr_collect_sound", note: [A mixed flow-sensitive analysis, sound
  end to end for one program (@sec:mixed-flow).])

#heading(level: 2, outlined: false)[Regression corpus] <app:regressions>

The corpus below `tests/regression/` holds #stat("corpus.cases") `.vimp` files
in #stat("corpus.groups") top-level groups, counted by `scripts/pages_stats.py`
at the revision this document is built from. It is an inventory of inputs, not
of passing runs or proved properties: a fixture can exercise several
configurations, and some test rejected syntax or known imprecision.

#{
  let groups = stat-keys("corpus.by_group.")
  let half = calc.ceil(groups.len() / 2)
  let cell(i) = if i < groups.len() {
    (raw(groups.at(i)), [#stat("corpus.by_group." + groups.at(i))])
  } else { ([], []) }
  table(
    columns: (1fr, auto, 1fr, auto),
    [*Directory*], [*Files*], [*Directory*], [*Files*],
    ..range(half).map(i => cell(i) + cell(i + half)).flatten(),
  )
}

Of these, #stat("corpus.kinds.precision") lie under `precision/`,
#stat("corpus.kinds.known-imprecision") under `known-imprecision/`,
#stat("corpus.kinds.soundness") under `soundness/`, and
#stat("corpus.kinds.other") elsewhere, including parser and presentation
fixtures.
