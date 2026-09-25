#import "../lib/math.typ": *
#import "../lib/code.typ": isaconst, isai, isalocale, isasession, isathm, isatype
#import "../lib/alignment.typ": alignment, alignment-mark, alignment-table
#import "../lib/theme.typ": vb

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
      modeled. The status describes architecture and says nothing about proofs.],
  ) <tab:goblint-alignment>
]
