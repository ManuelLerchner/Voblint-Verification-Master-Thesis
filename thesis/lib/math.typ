// Notation library. Same rule as on the LaTeX side: never write a semantic
// bracket, a sharp, or a lattice symbol directly in the text -- go through a
// binding here, so a notational decision is one edit.

// ============================================================== brackets ====
#let sem(x)   = $lr(⟦ #x ⟧)$
#let asem(x)  = $lr(⟦ #x ⟧)^sharp$
#let sh(x)    = $#x^sharp$
#let shn(x)   = $#x^natural$
#let setof(x) = $lr({ #x })$
#let tup(x)   = $lr(⟨ #x ⟩)$
#let card(x)  = $lr(bar.v #x bar.v)$
#let setcomp(x, y) = $lr({ #x mid(bar.v) #y })$

// ============================================================== lattices ====
#let lle    = $subset.sq.eq$
#let llt    = $subset.sq$
#let lge    = $supset.sq.eq$
#let ljoin  = $union.sq$
#let lmeet  = $inter.sq$
#let lJoin  = $union.sq.big$
#let lMeet  = $inter.sq.big$
#let lbot   = $bot$
#let ltop   = $top$
#let widen  = $nabla$
#let narrow = $triangle.t.small$
#let lfp    = $op("lfp")$
#let gfp    = $op("gfp")$
#let lat(x) = $bb(#x)$

#let abstr = $alpha$
#let conc  = $gamma$
// C <alpha,gamma> A
#let galois(c, a) = $#c attach(arrows.rl, t: alpha, b: gamma) #a$

// ========================================================= source syntax ====
#let Var    = $italic("Var")$
#let Val    = $italic("Val")$
#let Store  = $Sigma$
#let keyw(x) = $bold(#x)$
#let skipC  = keyw("skip")
#let assign(x, e) = $#x := #e$
#let pstep  = $arrow.r_p$
#let psteps = $arrow.r_p^*$
#let pcompletes = $arrow.b.double_p$
#let frstack = $kappa$
#let config(c, s, k) = $lr(⟨ #c, #s, #k ⟩)$

// =================================================================== CFG ====
#let FunEntry(p)  = $sans("Entry") #p$
#let FunResult(p) = $sans("Result") #p$
#let Stmt(n)      = $sans("Stmt") #n$
#let cfgedge(u, a, v) = $#u attach(arrow.r.long, t: #a) #v$
#let cfgcall(u, a, p, v) = $#u attach(arrow.r.dashed, t: #[#a, #p]) #v$
#let cfg  = $cal(G)$
#let prog = $P$

// ============================================== activation-local traces =====
#let Ltr        = $italic("Ltr")$
#let validltr   = $italic("valid")$
#let ltrcollect = $cal(C)$
#let actcollect = $cal(C)_"act"$
#let keyfun     = $beta$
#let sinkstore  = $italic("sink")$
#let callerof   = $italic("caller")$

// ========================================== equation system and solver ======
#let Unk      = $cal(X)$
#let rhs(x)   = $italic("rhs")_#x$
#let sol      = $sigma$
#let stable   = $italic("stable")$
#let called   = $italic("called")$
#let infl     = $italic("infl")$
#let partpost = $italic("part_post")$
#let sidefx   = $arrow.squiggly$
#let TDside   = $"TD"_"side"$

// ========================================================== D/G framework ===
#let Dfact = $sans("D")$
#let Gfact = $sans("G")$
#let Ctxt  = $sans("C")$
#let GVar  = $sans("V")$
#let dgstate(l, g) = $lr(⟨ #l mid(bar.v) #g ⟩)$

#let tf(a)          = $sh(delta) lr([#a])$
#let enterh         = $italic("enter")^sharp$
#let combineh       = $italic("combine")^sharp$
#let combineenvh    = $italic("combine_env")^sharp$
#let combineassignh = $italic("combine_assign")^sharp$
#let ctxh           = $italic("context")^sharp$

// =============================================================== domains ====
#let DSign = $cal(S)$
#let DIvl  = $cal(I)$
#let DPar  = $cal(P)$
#let DCong = $cal(K)$
#let DInt  = $cal(N)$
#let signval(x) = $mono(#x)$
#let ivl(a, b) = $[#a, #b]$

// =============================================================== helpers ====
#let defeq  = $:=$
#let soundby = $in gamma$
#let upd(f, x, v) = $#f [#x |-> #v]$
#let restrict(f, s) = $#f harpoon.tr_#s$
