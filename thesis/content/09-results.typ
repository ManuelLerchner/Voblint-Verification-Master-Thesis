#import "../lib/theme.typ": vb
#import "../lib/code.typ": isaconst

= Results, Checks, and the Source-Level Theorem <ch:results>

#block(
  fill: vb.bg,
  stroke: (paint: vb.muted, thickness: 0.7pt, dash: "dashed"),
  radius: 4pt,
  inset: 9pt,
  width: 100%,
)[
  _Chapter draft pending._ The plan for this chapter is in
  `docs/THESIS_BLUEPRINT.md`, section 7. This stub exists so that chapter
  numbering is stable and forward references from written chapters resolve
  against a label rather than a hard-coded number.
]

#block(
  fill: vb.bg,
  stroke: (paint: vb.trusted, thickness: 0.7pt, dash: "dashed"),
  radius: 4pt,
  inset: 9pt,
  width: 100%,
)[
  *Must carry a closing section, "What the theorem depends on."* Not the trust
  boundary, which is @ch:executable's: this is definitional adequacy — whether
  the definitions are the ones intended. `docs/THESIS_BLUEPRINT.md` §15.3 holds
  the reviewer-facing list, ordered by what a mistake would cost, beginning
  with #isaconst("pstep") being the anchor (@ch:program-model) and
  #isaconst("valid_ltr") against #isaconst("cstep") (@ch:traces). It must also
  say plainly what a `PROVED` verdict does and does not mean, and that
  `REFUTED` is not a verified counterexample.
]
