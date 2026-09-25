#import "theme.typ": vb
// Notation library. Only mathematical notation lives here, and each symbol is
// the one the theories print: gamma for the class parameter of sound_domain,
// the semantic brackets for gamma_state, HOL's order, lattice and function-
// update syntax, and the solver's widening and narrowing. Every other formal
// object is written under its Isabelle name (isaconst, isai), not a macro.

// ============================================================== brackets ====
#let sem(x) = $lr(⟦ #x ⟧)$
#let asem(x) = $lr(⟦ #x ⟧)^sharp$
#let sh(x) = $#x^sharp$
#let setof(x) = $lr({ #x })$
#let setcomp(x, y) = $lr({ #x mid(bar.v) #y })$

// ============================================================== lattices ====
// HOL's order classes: the theories write <= for every carrier's order.
#let lle = $lt.eq$
#let llt = $lt$
#let ljoin = $union.sq$
#let lmeet = $inter.sq$
#let lJoin = $union.sq.big$
#let lMeet = $inter.sq.big$
#let lbot = $bot$
#let ltop = $top$
#let widen = $nabla$
#let narrow = $Delta$
#let lfp = $op("lfp")$
#let lat(x) = $bb(#x)$

#let abstr = $alpha$
#let conc = $gamma$

// ========================================================= source syntax ====
// VIMP keywords and datatype constructors are coloured like the identifiers
// of code.typ: keywords in the listing keyword colour, constructors in the
// colour of the type they build.
// Both are text, not math alphabets: the math font's sans and bold ranges
// are not what a reader expects a keyword or a constructor to look like.
// The font is named because math sets text in Latin Modern Math, which has
// no bold face.
//
// Syntax displays follow one rule: a token a VIMP program contains is set in
// the keyword colour (keyw for words, vop for operator symbols), a constructor
// with no source token (Restore, Entry, Root) is set with ctor, and
// metavariables and the notation around them (:=, ";", brackets) stay math.
#let keyw(x) = text(font: "Latin Modern Roman", weight: "bold", fill: vb.keyword, x)
#let ctor(x) = text(font: "Latin Modern Sans", fill: vb.type, x)
// Math only: the class restores the operator spacing that text drops.
#let vop(x, unary: false) = math.class(
  if unary { "unary" } else { "binary" },
  text(font: "Latin Modern Roman", fill: vb.keyword, x),
)
#let skipC = keyw("skip")
#let assign(x, e) = $#x := #e$

// ======================================================= trace constructors ====
#let Root(p) = $ctor("Root") thick #p$
#let CallT(t, p) = $ctor("Call") thick #t med #p$
#let ResumeT(t, u, p) = $ctor("Resume") thick #t med #u med #p$

// ========================================== equation system and solver ======
#let Unk = $cal(X)$
#let rhs(x) = $italic("rhs")_#x$
#let sol = $sigma$

// ================================================ D/G specification fields ===
// The mixfix syntax of the dg_spec record fields and of routed_context's route.
#let enterh = $italic("enter")^\#$
#let combineenvh = $italic("combine_env")^\#$
#let combineassignh = $italic("combine_assign")^\#$
#let ctxh = $italic("context")^\#$

// =============================================================== domains ====
// Sign values are constructors printed as +, ≥0, ...; the chip keeps them
// apart from the operators and relations they share glyphs with.
#let signval(x) = box(
  fill: vb.type.lighten(90%),
  radius: 1.5pt,
  inset: (x: 1.5pt),
  outset: (y: 1.5pt),
  ctor(x),
)
#let ivl(a, b) = $[#a, #b]$

// =============================================================== helpers ====
// HOL's function update.
#let upd(f, x, v) = $#f (#x := #v)$
#let restrict(f, s) = $#f harpoon.tr_#s$
