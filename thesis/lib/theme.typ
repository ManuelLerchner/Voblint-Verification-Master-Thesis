// One palette for the whole document. Figures reference these names only.

#let vb = (
  proved: rgb("#2E7D32"), // machine-checked
  trusted: rgb("#B26A00"), // assumed, not proved
  unproved: rgb("#B3261E"), // outside the trust boundary
  neutral: rgb("#37474F"),
  accent: rgb("#1565C0"),
  muted: rgb("#78909C"),

  // solver state
  stable: rgb("#2E7D32"),
  unstable: rgb("#EF6C00"),
  fresh: rgb("#FFFFFF"),
  called: rgb("#5E35B1"),

  // notation and identifiers: what a reader can click is coloured by kind;
  // a name with no resolved link is set in `plain`.
  const: rgb("#1565C0"), // a constant or function of the formalization
  thm: rgb("#2E7D32"), // a proved fact
  type: rgb("#6A1B9A"), // a type, and the constructors of a datatype
  locale: rgb("#00695C"), // a locale, and the obligations it names
  plain: rgb("#37474F"),

  // listings
  keyword: rgb("#7F0055"),
  ident: rgb("#0000C0"),
  string: rgb("#2A00FF"),
  comment: rgb("#3F7F5F"),
  frame: rgb("#CFD8DC"),
  bg: rgb("#FAFAFA"),

  // where a declaration comes from
  hol: rgb("#8D8D8D"), // Isabelle's HOL library
  solver: rgb("#EF6C00"), // the vendored TD solver
  voblint: rgb("#1E88E5"), // this formalization

  // domains
  sign: rgb("#00695C"),
  ivl: rgb("#1565C0"),
  par: rgb("#6A1B9A"),
  cong: rgb("#AD1457"),
)

#let tint(c, amount) = c.lighten(amount)
