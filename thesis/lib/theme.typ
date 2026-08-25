// One palette for the whole document. Figures reference these names only.

#let vb = (
  proved:   rgb("#2E7D32"),   // machine-checked
  trusted:  rgb("#B26A00"),   // assumed, not proved
  unproved: rgb("#B3261E"),   // outside the trust boundary
  neutral:  rgb("#37474F"),
  accent:   rgb("#1565C0"),
  muted:    rgb("#78909C"),

  // solver state
  stable:   rgb("#2E7D32"),
  unstable: rgb("#EF6C00"),
  fresh:    rgb("#FFFFFF"),
  called:   rgb("#5E35B1"),

  // listings
  keyword:  rgb("#7F0055"),
  ident:    rgb("#0000C0"),
  string:   rgb("#2A00FF"),
  comment:  rgb("#3F7F5F"),
  frame:    rgb("#CFD8DC"),
  bg:       rgb("#FAFAFA"),

  // domains
  sign:     rgb("#00695C"),
  ivl:      rgb("#1565C0"),
  par:      rgb("#6A1B9A"),
  cong:     rgb("#AD1457"),
)

#let tint(c, amount) = c.lighten(amount)
