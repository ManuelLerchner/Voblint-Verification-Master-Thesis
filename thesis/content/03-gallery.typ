#import "@preview/fletcher:0.5.8" as fletcher: diagram, node, edge
#import "@preview/curryst:0.6.0": rule, prooftree
#import "@preview/lilaq:0.6.0" as lq
#import "@preview/lovelace:0.3.1": pseudocode-list
#import "@preview/cetz:0.5.2"
#import "@preview/diagraph:0.3.7": raw-render
#import "@preview/syntree:0.3.1": syntree
#import "@preview/subpar:0.2.2"
#import "../lib/math.typ": *
#import "../lib/theme.typ": vb
#import "../lib/figures.typ": *
#import "../lib/code.typ": *
#import "../lib/theorems.typ": theorem, definition
#import "../lib/sources.typ": thy, stmt, proved
#import "../lib/figures.typ": iteration-plot, simulation, annotation-grid

= Figure Gallery <ch:gallery>

This chapter is not thesis content. It is a working reference: one instance of
every figure kind the thesis needs, built from the vocabulary in
#isafile("lib/"). Copy a figure, change the payload, keep the styles.

== The pipeline and its trust boundary

@fig:pipeline is the thesis in one picture. Every stage carries its status,
and every arrow carries the fact that discharges it: an unlabelled arrow
between two proved stages is a gap, visible at a glance.

#figure(
  diagram(
    spacing: (13mm, 13mm),
    node-stroke: none,

    stage((0, 0), [VIMP source \ text], kind: "unproved"),
    stage((1.6, 0), [lexer + parser \ #text(0.8em)[from `vimp.yaml`]], kind: "unproved"),

    stage((0, 1.2), isatype("imp_prog")),
    stage((1.6, 1.2), [procedure-aware \ CFG]),
    stage((3.2, 1.2), [equation \ system]),
    stage((4.8, 1.2), [#TDside \ #text(0.8em)[vendored]]),

    stage((0, 2.4), [#partpost \ certificate]),
    stage((1.6, 2.4), [sound abstract \ result]),
    stage((3.2, 2.4), [source-level \ result]),

    stage((0, 3.6), isacmd("export_code"), kind: "trusted"),
    stage((1.6, 3.6), [OCaml harness \ #text(0.8em)[#isafile("cli/")]], kind: "unproved"),

    flow((0, 0), (1.6, 0)),
    flow((1.6, 0), (0, 1.2), bend: -20deg),
    flow((0, 1.2), (1.6, 1.2), label: "compile_prog"),
    flow((1.6, 1.2), (3.2, 1.2), label: "dg_gen_of"),
    flow((3.2, 1.2), (4.8, 1.2), label: "TD_side"),
    flow((4.8, 1.2), (0, 2.4), label: "solver_correct", bend: -12deg),
    flow((0, 2.4), (1.6, 2.4), label: "sound_dg_spec"),
    flow((1.6, 2.4), (3.2, 2.4), label: "ltr_collect"),
    flow((3.2, 2.4), (0, 3.6), bend: -12deg),
    flow((0, 3.6), (1.6, 3.6)),

    node(enclose: ((0, 1.2), (4.8, 1.2), (0, 2.4), (3.2, 2.4)),
         stroke: (paint: vb.unproved, thickness: 0.7pt, dash: "dashed"),
         corner-radius: 4pt, inset: 8pt,
         name: <bnd>),
  ),
  caption: [The verified pipeline. Arrow labels name the fact that justifies
    the step; stage colour states whether the stage is proved, trusted, or
    unverified. The parser and the OCaml harness sit outside the boundary by
    construction; the code generator sits on it.
    #v(0.4em)
    #text(0.85em)[#proved-badge machine-checked #h(1em)
      #trusted-badge assumed, not proved #h(1em)
      #unproved-badge outside the boundary]],
) <fig:pipeline>

== Program, CFG, and equation system

#subfigures(
  figure(
    listing(lang: "c", ```
proc fac(n) {
  if (n <= 1) {
    return 1;
  } else {
    r = fac(n - 1);
    return n * r;
  }
}
```),
    caption: [VIMP source],
  ), <fig:cfg-source>,
  figure(
    diagram(
      spacing: (10mm, 9mm),
      entry-node((0, 0), $#FunEntry($italic("fac")$)$),
      ppoint((0, 1), $u_1$),
      ppoint((-0.7, 2), $u_2$),
      ppoint((0.7, 2), $u_3$),
      ppoint((0, 3), $u_4$),
      result-node((0, 4), $#FunResult($italic("fac")$)$),
      intra-edge((0, 0), (0, 1)),
      intra-edge((0, 1), (-0.7, 2), label: "n<=1"),
      intra-edge((0, 1), (0.7, 2), label: "!(n<=1)"),
      intra-edge((-0.7, 2), (0, 3)),
      call-edge((0.7, 2), (0, 3), label: "call fac"),
      intra-edge((0, 3), (0, 4)),
    ),
    caption: [compiled CFG; dashed edges are #isaconst("calls")],
  ), <fig:cfg-graph>,
  columns: (0.42fr, 0.58fr),
  align: bottom,
  caption: [A recursive VIMP procedure and its procedure-aware CFG. Local
    #isaconst("intra") edges carry an #isatype("edge_action"), and call sites are a
    separate relation with their own edge style.],
  label: <fig:cfg>,
)

@fig:cfg-dot shows the alternative route, and the one place where Typst does
something LaTeX cannot: the Graphviz source is laid out and drawn inside the
document, with no build step and no intermediate file.

#figure(
  raw-render(raw(read("/shared/dot/cfg_fac.dot")), height: 70mm),
  caption: [The same CFG, produced by #isaconst("state_report_export_auto") and laid out
    from #isafile("shared/dot/cfg_fac.dot") at compile time.],
) <fig:cfg-dot>

Between the two sits the abstract syntax the compiler actually consumes.
@fig:ast is the same procedure again, as an #isatype("imp_prog") term.

#figure(
  syntree(
    child-spacing: 1.4em, layer-spacing: 2.1em,
    nonterminal: (fill: vb.accent),
    terminal: (fill: black, font: "DejaVu Sans Mono", size: 0.85em),
    [[Proc [fac] [n]
       [If [Leq [n] [1]]
           [Return [1]]
           [Seq [Call [r] [fac] [Minus [n] [1]]]
                [Return [Times [n] [r]]]]]]],
  ),
  kind: image,
  caption: [The procedure as an abstract syntax tree. Non-terminals are the
    constructors of #isatype("com"), and the leaves are identifiers and literals.
    This is what #isaconst("compile") recurses over, so the CFG in
    @fig:cfg is a traversal of exactly this shape.],
) <fig:ast>

== Transfer functions

#figure(
  rhsbox[
    $
      tf(assign(x, e)) d      &= upd(d, x, asem(e) d) \
      tf(keyw("assume") b) d  &= cases(
        d & "if" mono("true") in asem(b) d,
        lbot & "otherwise") \
      tf(skipC) d             &= d \
      enterh p d              &= setcomp(upd(d_0, arrow(x)_p, asem(arrow(e)) d),
                                          d_0 = restrict(d, italic("globals"))) \
      combineh d_c d_r        &= combineassignh (combineenvh d_c d_r)
    $
  ],
  kind: image,
  caption: [Right-hand sides of the abstract transfer for local edges. All
    functions are strict in $lbot$; only the non-$lbot$ cases are shown.],
) <fig:rhs>

== Inference rules

#figure(
  grid(columns: 2, column-gutter: 2.5em, row-gutter: 1.6em,
    prooftree(rule(name: [Root], $validltr ("Root" u_0 s_0)$)),
    prooftree(rule(name: [Step],
      $validltr t$,
      $cfgedge(italic("last") t, a, v)$,
      $s' in sem(a) (sinkstore t)$,
      $validltr (t dot (v, s'))$)),
    prooftree(rule(name: [Call],
      $validltr t$,
      $cfgcall(u, a, p, v)$,
      $s' = enterh p (sinkstore t)$,
      $validltr ("Called" t p s')$)),
    prooftree(rule(name: [Resume],
      $validltr t_c$,
      $callerof t_c = t$,
      $validltr ("Resumed" t t_c)$)),
  ),
  kind: image,
  caption: [The activation-local trace semantics #isaconst("valid_ltr"). Every
    rule matches one constructor of #isatype("ltr"), so the induction
    principle in the proofs has exactly these four cases.],
) <fig:validltr>

== Lattices and abstraction

#subfigures(
  figure(
    hasse(
      ((( 0, 0), $ltop$),
       ((-1, 1), signval("leq0")), (( 1, 1), signval("geq0")),
       ((-1, 2), signval("neg")), (( 0, 2), signval("zero")), (( 1, 2), signval("pos")),
       (( 0, 3), $lbot$)),
      (((-1, 1), (0, 0)), ((1, 1), (0, 0)),
       ((-1, 2), (-1, 1)), ((0, 2), (-1, 1)), ((0, 2), (1, 1)), ((1, 2), (1, 1)),
       ((0, 3), (-1, 2)), ((0, 3), (0, 2)), ((0, 3), (1, 2))),
    ),
    caption: [#DSign],
  ), <fig:lat-sign>,
  figure(
    hasse(
      ((( 0, 0), $ltop$),
       ((-1, 1), signval("even")), (( 1, 1), signval("odd")),
       (( 0, 2), $lbot$)),
      (((-1, 1), (0, 0)), ((1, 1), (0, 0)),
       ((0, 2), (-1, 1)), ((0, 2), (1, 1))),
    ),
    caption: [#DPar],
  ), <fig:lat-par>,
  figure(
    diagram(
      spacing: (18mm, 8mm),
      node((0, 0), $cal(P)(Val)$, stroke: 0.8pt + vb.accent,
           fill: vb.accent.lighten(90%), width: 24mm, height: 20mm,
           corner-radius: 3pt),
      node((1, 0), DSign, stroke: 0.8pt + vb.sign,
           fill: vb.sign.lighten(90%), width: 20mm, height: 20mm,
           corner-radius: 3pt),
      edge((0, 0), (1, 0), "->", label: $alpha$, bend: 25deg,
           stroke: 0.8pt + vb.accent),
      edge((1, 0), (0, 0), "->", label: $gamma$, bend: 25deg,
           stroke: 0.8pt + vb.proved),
    ),
    caption: [the induced abstraction],
  ), <fig:galois>,
  columns: (1fr, 1fr, 1.15fr),
  align: bottom,
  caption: [Hasse diagrams of two component domains and the abstraction they
    induce. The formalization fixes only $conc$; $abstr$ is drawn for
    intuition and is not required by #isalocale("sound_domain").],
  label: <fig:lattices>,
)

#figure(
  lq.diagram(
    width: 11cm, height: 4.2cm,
    xlabel: [iteration $i$], ylabel: [interval at the loop head],
    xlim: (0, 7), ylim: (-1, 12),
    legend: (position: left + top),
    lq.plot((0, 1, 2, 3, 4, 5, 6, 7), (0, 1, 2, 11, 11, 11, 11, 11),
            color: vb.ivl, label: [upper bound, with $widen$ at $i = 3$]),
    lq.plot((0, 1, 2, 3, 4, 5, 6, 7), (0, 1, 2, 3, 4, 5, 6, 7),
            color: vb.unstable, stroke: (dash: "dashed"),
            label: [without widening]),
    lq.plot((3, 4, 5, 6, 7), (11, 10, 10, 10, 10),
            color: vb.proved, stroke: (dash: "dotted"), label: [after $narrow$]),
  ),
  caption: [Chain iteration at a single loop head. Widening jumps to a coarse
    bound at iteration 3; narrowing recovers the exact one. Plots like this
    come from the analyzer's own trace output, not from hand-placed
    coordinates.],
) <fig:widening>

== The solver

#subfigures(
  figure(
    cetz.canvas({
      import cetz.draw: *
      rect((-2.5, -1.6), (2.5, 1.6), fill: vb.called.lighten(90%),
           stroke: none, radius: 0.2)
      content((0, 1.3), text(0.75em, fill: vb.called)[#called])
      rect((-2.1, -1.25), (1.0, 1.0), fill: vb.stable.lighten(82%),
           stroke: none, radius: 0.2)
      content((-0.55, 0.7), text(0.75em, fill: vb.stable)[#stable])
      rect((-1.8, -0.95), (-0.2, 0.3), fill: vb.proved.lighten(65%),
           stroke: none, radius: 0.2)
      content((-1.0, -0.35), text(0.7em)[truly \ stable])
      rect((0.3, -1.25), (2.2, 0.35), fill: vb.unstable.lighten(65%),
           stroke: none, radius: 0.2)
      content((1.25, -0.45), text(0.7em)[affected by \ side effects])
    }),
    caption: [invariant regions of a solver state],
  ), <fig:euler>,
  figure(
    diagram(
      spacing: (12mm, 10mm),
      unk((0, 0), $u_1$, state: "stable"),
      unk((1, 0), $u_2$, state: "unstable"),
      unk((1, 1), $u_3$, state: "fresh"),
      unk((0, 1), $u_4$, state: "called"),
      global-unk((1, 2), $g$),
      dep-edge((0, 0), (1, 0)),
      dep-edge((1, 0), (1, 1)),
      dep-edge((0, 1), (1, 1)),
      side-edge((1, 0), (1, 2)),
      withdrawn-edge((0, 1), (1, 2)),
    ),
    caption: [one frame of a #TDside run],
  ), <fig:solverstate>,
  columns: (1fr, 1fr),
  align: bottom,
  caption: [Left: the subsets a correctness argument reasons about; #called
    unknowns need not be stable once side effects are in play. Right: the same
    state as a graph. Green is stable, orange destabilised, white fresh, purple
    outline #called; double-tipped arrows are side effects and dashed ones are
    withdrawn contributions.],
  label: <fig:solver>,
)

#figure(
  table(
    columns: 6,
    align: (left, left, center, center, center, left),
    stroke: none,
    table.hline(),
    [step], [action], [$sol u_1$], [$sol u_2$], [$sol g$], [note],
    table.hline(stroke: 0.5pt),
    [1], [$italic("solve") u_1$], [$lbot$], [$lbot$], [$lbot$], [],
    [2], [$italic("eval") u_2$], [$lbot$], [$lbot$], [$lbot$], [dependency recorded],
    [3], [$italic("eval") u_1$], [$lbot$], [$lbot$], [$lbot$],
        [#text(fill: vb.unstable)[cycle detected]],
    [4], [update $u_2$], [$lbot$], [$ivl(0, 0)$], [$lbot$], [],
    [5], [side effect to $g$], [$lbot$], [$ivl(0, 0)$], [$ivl(0, 0)$],
        [$u_2 sidefx g$],
    [6], [destabilise], [$lbot$], [$ivl(0, 0)$], [$ivl(0, 0)$],
        [$u_1$ leaves #stable],
    [7], [update $u_1$ with $widen$], [$ivl(0, infinity)$], [$ivl(0, 0)$],
        [$ivl(0, 0)$], [widening point],
    table.hline(),
  ),
  caption: [After @grass25 @tilscher26. Computation trace of one $italic("solve")$ call, one row per solver
    step. Auxiliary rows separate the effect of an edge from the effect of the
    widening operator, so a reader can attribute each value change to exactly
    one cause.],
) <tab:trace>

#algorithm(
  caption: [The $TDside$ core, in the shape the formalization proves correct.
    Widening is applied at the update, and destabilisation is what makes the
    surrounding `repeat` terminate rather than spin.],
  label-name: "alg:tdside",
  pseudocode-list(booktabs: true, hooks: 0.5em)[
    + *function* $italic("solve")(x)$
      + *if* $x in.not called union stable$
        + $called <- called union {x}$
        + *repeat*
          + $stable <- stable union {x}$
          + $d <- rhs(x) italic("eval") italic("side")$
          + *if* $d subset.sq.eq.not sol x$
            + $sol x <- sol x widen d$
            + $italic("destabilize")(x)$
        + *until* $x in stable$
        + $called <- called without {x}$#h(1fr)
  ],
)

== Software architecture of the formalization

The layout follows the module maps of comparable systems @apinis14 @jourdan15;
the trust boundary follows @leroy09.

#figure(
  diagram(
    spacing: (16mm, 10mm),
    locale-node((0, 0), "ord"),
    locale-node((0, 1), "bounded_lattice"),
    locale-node((0, 2), "sound_domain"),
    locale-node((-1, 3), "domain_transfer"),
    locale-node((1, 3), "dg_ctx_activation_base"),
    locale-node((0, 4), "dg_spec"),
    locale-node((0, 5), "sound_dg_spec"),
    instance-node((-1.6, 6), "Sign_Analysis"),
    instance-node((-1.6, 7), "Interval_Analysis"),
    instance-node((1.6, 6), "Int_Analysis"),
    instance-node((1.6, 7), "Parity_Analysis"),

    import-edge((0, 0), (0, 1)),
    import-edge((0, 1), (0, 2)),
    import-edge((0, 2), (-1, 3)),
    import-edge((0, 2), (1, 3)),
    import-edge((-1, 3), (0, 4)),
    sublocale-edge((1, 3), (0, 4)),
    import-edge((0, 4), (0, 5)),
    interp-edge((0, 5), (-1.6, 6)),
    interp-edge((0, 5), (1.6, 6)),
    interp-edge((-1.6, 6), (-1.6, 7)),
    interp-edge((1.6, 6), (1.6, 7)),
  ),
  caption: [Locale hierarchy of the domain framework. The three edge kinds are
    genuinely different: `import` is declared, `sublocale` is proved after the
    fact, and `interpretation` lands an abstract theory on a concrete
    instance. This figure is generated from #isacmd("locale_deps"), not
    drawn by hand.
    #v(0.3em)
    #text(0.85em)[
      #box(line(length: 8mm, stroke: 0.9pt + vb.neutral)) `import` #h(1em)
      #box(line(length: 8mm, stroke: (paint: vb.accent, thickness: 0.9pt, dash: "dashed"))) `sublocale` #h(1em)
      #box(line(length: 8mm, stroke: (paint: vb.proved, thickness: 0.9pt, dash: "dotted"))) `interpretation`]],
) <fig:locales>

#let yes = text(fill: vb.proved)[#sym.checkmark]
#let no = text(fill: vb.unproved)[#sym.times]

#figure(
  table(
    columns: 6,
    align: (left, center, center, center, center, center),
    stroke: none,
    table.hline(),
    [locale / class], [Sign], [Interval], [Parity], [Congruence], [Int product],
    table.hline(stroke: 0.5pt),
    [#isalocale("sound_domain")], yes, yes, yes, yes, yes,
    [#isatype("domain_transfer")], yes, yes, yes, yes, yes,
    [#isalocale("dg_ctx_activation_base")], yes, yes, yes, no, yes,
    [#isatype("dg_spec")], yes, yes, yes, no, yes,
    [#isalocale("sound_dg_spec")], yes, yes, yes, no, yes,
    table.hline(),
  ),
  caption: [Which abstract theory is landed on which concrete domain. A row
    with no #yes is a false abstraction; a #no is a deliberate scope decision,
    here that Congruence is not selectable on its own but only as a component
    of the Int product.],
) <tab:instantiation>

#figure(
  diagram(
    spacing: (20mm, 9mm),
    node((0, 0), `Abstract_Domain`, stroke: 0.7pt + vb.muted, inset: 5pt),
    node((0, 1), `Constraint_System`, stroke: 0.7pt + vb.muted, inset: 5pt),
    node((0, 2), `DG_Framework`, stroke: 0.7pt + vb.muted, inset: 5pt),
    node((1, 0), `Sign_Exec`, stroke: 0.7pt + vb.muted, inset: 5pt),
    node((1, 1), `Ivl_Exec`, stroke: 0.7pt + vb.muted, inset: 5pt),
    node((1, 2), `Int_Exec`, stroke: 0.7pt + vb.muted, inset: 5pt),
    node((2, 0), `Analyse_Dispatch`, stroke: 0.7pt + vb.muted, inset: 5pt),
    node((2, 1), `Analysis_Config`, stroke: 0.7pt + vb.muted, inset: 5pt),
    node((2, 2), `State_Report_GraphViz`, stroke: 0.7pt + vb.muted, inset: 5pt),

    edge((0, 0), (0, 1), "->"), edge((0, 1), (0, 2), "->"),
    edge((1, 0), (1, 1), "->"), edge((1, 1), (1, 2), "->"),
    edge((0, 2), (1, 0), "->", bend: -30deg),
    edge((1, 2), (2, 0), "->", bend: -30deg),
    edge((2, 0), (2, 1), "-->"), edge((2, 1), (2, 2), "-->"),

    node(enclose: ((0, 0), (0, 2)), stroke: 0.8pt + vb.neutral,
         corner-radius: 4pt, inset: 7pt),
    node(enclose: ((1, 0), (1, 2)), stroke: 0.8pt + vb.neutral,
         corner-radius: 4pt, inset: 7pt),
    node(enclose: ((2, 0), (2, 2)), stroke: 0.8pt + vb.neutral,
         corner-radius: 4pt, inset: 7pt),
  ),
  caption: [Theories grouped by session, and the module boundary the code
    generator produces. Solid arrows are theory imports; dashed arrows mark
    theories the #isacmd("code_identifier") block remaps. Adding a theory
    that an export root reaches without adding it here is the single most
    common cause of a module-dependency cycle at export time.],
) <fig:modules>

== Isabelle in the text #thy-badge("Voblint_Core", "Abstract_Domain")

Snippets are written in ASCII source form, exactly as the repository stores
them, and decoded at render time with Isabelle's own symbol table.

#figure(
  thy("sound_domain"),
  kind: image,
  caption: [The domain interface as the sources state it, lifted by name from
    the theory rather than retyped. Presenting it verbatim is what lets a
    reader check the obligations a domain must discharge.],
) <fig:isasnippet>

#proved("valid_ltr_eq_lfp", note: [
  The activation-local semantics is a least fixpoint, which is what makes
  induction over it available. The statement below is not a paraphrase: it is
  exported from the built session, so it cannot drift from what was proved.
])

#proved("ltr_collect_semantic_postfix", note: [
  The bridge from a semantic post-fixpoint to the compiled program's collecting
  semantics.
])

#[Everything above is generated. What follows is not, and says so.]

#figure(
  table(
    columns: 4,
    align: (left, left, center, center),
    stroke: none,
    table.hline(),
    [endpoint], [session], [oracles], [`sorry`],
    table.hline(stroke: 0.5pt),
    [#isathm("run_source_sound")], [#isasession("Voblint_Core")], [none], yes,
    [#isathm("ltr_collect_semantic_postfix")], [#isasession("Voblint_CFG")], [none], yes,
    [#isathm("source_completes_ltr_collect_exit")], [#isasession("Voblint_CFG")], [none], yes,
    [#isathm("source_activation_sound")], [#isasession("Voblint_Soundness")], [none], yes,
    table.hline(),
  ),
  caption: [Output of #isacmd("thm_oracles") for the endpoint theorems,
    transcribed into a table. This is machine-checked evidence that the results
    rest on no oracle and no admitted subgoal --- a claim that is otherwise
    only asserted in prose.],
) <tab:oracles>

== Drawing the mathematics

Four figures adapted from _Concrete Semantics_, which solves the same
presentation problem this thesis has: how to show a reader what a formal
development means without asking them to read it.

@fig:iteration is its treatment of widening. Plotting the iteration against
$f x$ rather than against time shows *why* the sequence terminates --- the jump
leaves the region where $f$ can keep climbing --- instead of only showing that
a bound moved.

#figure(
  iteration-plot(),
  kind: image,
  caption: [Fixpoint iteration at one loop head. The staircase is plain
    iteration climbing toward the fixpoint; the heavy jump is widening
    overshooting it; the dotted descent is narrowing recovering precision. The
    dashed diagonal is $f x = x$.],
) <fig:iteration>

A lemma about two levels of a pipeline is easier to draw than to read. The
squares below are @fig:simulation --- the claim is that they commute.

#subfigures(
  figure(
    simulation(
      top-left: $(c, s)$, top-right: $t$,
      bottom-left: $italic("compile") c$, bottom-right: $t'$,
      top-label: text(0.8em)[$arrow.r.double$],
      bottom-label: text(0.8em)[$arrow.r.double^*$],
      left-label: text(0.8em)[$approx$], right-label: text(0.8em)[$approx$],
    ),
    caption: [every source execution is matched],
  ), <fig:sim-forward>,
  figure(
    simulation(
      top-left: $italic("compile") c$, top-right: $t'$,
      bottom-left: $(c, s)$, bottom-right: $t$,
      top-label: text(0.8em)[$arrow.r.double^*$],
      bottom-label: text(0.8em)[$arrow.r.double$],
      left-label: text(0.8em)[$approx$], right-label: text(0.8em)[$approx$],
      dashed-bottom: true,
    ),
    caption: [every compiled execution comes from one],
  ), <fig:sim-backward>,
  columns: (1fr, 1fr),
  align: bottom,
  caption: [Compiler correctness as two simulations. Neither direction alone is
    correctness, and drawing both is what makes the asymmetry visible.],
  label: <fig:simulation>,
)

#figure(
  annotation-grid(
    ($u_1$, $u_2$, $u_3$),
    ("i", "n", "sum"),
    ((ivl(0, 0), $top$, ivl(0, 0)),
     (ivl(0, 9), $top$, ivl(0, 45)),
     (ivl(10, 10), $top$, ivl(45, 45))),
  ),
  kind: image,
  caption: [The abstract state as a grid: one value per variable per program
    point. A termination argument sums a measure over the cells, so seeing the
    state as a finite tuple is the point of the picture.],
) <fig:annotations>

Finally, the convention this repository enforces everywhere: theory sources are
ASCII-only, and every symbol is written in its escaped form. @tab:symbols is
not maintained by hand --- it lists exactly the symbols that appear in the
material this chapter quotes, so it grows when a new snippet does.

#figure(
  symbol-table((
    read("/shared/generated/snippets/sound_domain.thy"),
    read("/shared/generated/snippets/sound_dg_spec.thy"),
    read("/shared/generated/snippets/combine_env_abs.thy"),
    json("/shared/generated/facts.json").facts.values()
      .map(f => f.statement).join(" "),
  )),
  caption: [Isabelle symbols and the ASCII forms the sources are written in.],
) <tab:symbols>

== Stacks and activations

#subfigures(
  figure(
    stack(dir: ttb, spacing: 0pt,
      rect(width: 34mm, inset: 5pt, stroke: 0.7pt + vb.muted)[`fac`, $n = 1$],
      rect(width: 34mm, inset: 5pt, stroke: 0.7pt + vb.muted)[`fac`, $n = 2$],
      rect(width: 34mm, inset: 5pt, stroke: 0.7pt + vb.muted)[`fac`, $n = 3$],
      rect(width: 34mm, inset: 5pt, stroke: 0.7pt + vb.muted,
           fill: vb.muted.lighten(85%))[`main`],
    ),
    caption: [standard semantics: the whole stack],
  ), <fig:stack-std>,
  figure(
    stack(dir: ttb, spacing: 0pt,
      rect(width: 34mm, inset: 5pt, stroke: 1pt + vb.accent,
           fill: vb.accent.lighten(90%))[`fac`, $n = 1$],
      rect(width: 34mm, inset: 5pt, stroke: 0.7pt + vb.muted.lighten(50%))[
        #text(fill: vb.muted)[`fac`, $n = 2$]],
      rect(width: 34mm, inset: 5pt, stroke: 0.7pt + vb.muted.lighten(50%))[
        #text(fill: vb.muted)[`fac`, $n = 3$]],
      rect(width: 34mm, inset: 5pt, stroke: 0.7pt + vb.muted.lighten(50%))[
        #text(fill: vb.muted)[`main`]],
    ),
    caption: [activation-local: one activation plus a caller link],
  ), <fig:stack-local>,
  columns: (1fr, 1fr),
  align: top,
  caption: [The same runtime stack under two semantics.
    #isaconst("valid_ltr") keeps only the active frame and a pointer to its
    caller, which is what makes the collecting semantics finite per activation
    and what #isaconst("combine_env") has to restore on return.],
  label: <fig:stack>,
)

== Correspondence with Goblint

#figure(
  grid(columns: 2, column-gutter: 1em, align: top,
    [
      #align(center, text(0.95em, weight: "bold")[Goblint (OCaml)])
      #listing(lang: "ocaml", ```ocaml
module type Spec =
sig
  module D : Lattice.S
  module G : Lattice.S
  module C : Printable.S
  module V : SpecSysVar
  val assign : (D.t,G.t,C.t,V.t) ctx
            -> lval -> exp -> D.t
end
```)
    ],
    [
      #align(center, text(0.95em, weight: "bold")[Voblint (Isabelle)])
      #isa(```
locale dg_spec =
  fixes tf   :: "edge_action
              \<Rightarrow> ('d,'g) dg_state
              \<Rightarrow> ('d,'g) dg_state"
    and route :: "store \<Rightarrow> 'c"
    and read  :: "'k \<Rightarrow> 'g"
    and publish :: "'k \<Rightarrow> 'g \<Rightarrow> unit"
```)
    ],
  ),
  kind: image,
  caption: [Interface correspondence, side by side. `D` and `G` map onto the
    two fields of #isatype("dg_state"); `C` and `V` onto the locale parameters
    `'c` and `'k`. Where the correspondence is inexact --- here, that both
    payloads are currently the same flat type --- the divergence is recorded
    rather than glossed over.],
) <fig:correspondence>

== Analyzer output as a figure

#figure(
  table(
    columns: (1fr, 0.8fr),
    align: (left, left),
    stroke: none,
    table.hline(),
    text(0.9em)[source], text(0.9em)[abstract state after the line],
    table.hline(stroke: 0.5pt),
    raw("i = 0;", lang: "c"), $setof(i |-> ivl(0, 0))$,
    raw("while (i < 10) {", lang: "c"), $setof(i |-> ivl(0, 9))$,
    raw("  i = i + 2;", lang: "c"), $setof(i |-> ivl(2, 11))$,
    raw("}", lang: "c"), $setof(i |-> ivl(10, 11))$,
    raw("assert(i >= 10);", lang: "c"), text(fill: vb.proved)[PROVED],
    table.hline(),
  ),
  caption: [The analyzer's result rendered against the program that produced
    it. Generated by the CLI, so it cannot drift from what the analyzer
    actually computes.],
) <fig:annotated>

@fig:claim is the same idea applied to prose: the listing is not typed into
this file, it is the output of a recorded command, regenerated and diffed by
#isafile("thesis/tools/claims.py"). If the analyzer's answer changes, the build
fails and names the claim rather than leaving the figure describing behaviour
that is gone.

#figure(
  listing(read("/shared/generated/sign-cannot-bound-magnitude.txt")),
  kind: image,
  caption: [Output of `voblint --analysis sign` on the known-imprecision case.
    Sign tracks #signval("Positive") exactly, but the lattice has no magnitude,
    so `total < 100` is genuinely undecidable here --- `UNKNOWN` is the correct
    answer, not a regression.],
) <fig:claim>

== Evaluation

#figure(
  lq.diagram(
    width: 11cm, height: 4.5cm,
    ylabel: [assertions proved],
    xaxis: (ticks: (0, 1, 2, 3, 4).zip(
      ([Sign], [Parity], [Congruence], [Interval], [Int product])).map(
      ((i, l)) => (i, l))),
    lq.bar((-0.15, 0.85, 1.85, 2.85, 3.85), (31, 24, 29, 68, 84),
           width: 0.3, fill: vb.accent.lighten(40%), label: [precision suite]),
    lq.bar((0.15, 1.15, 2.15, 3.15, 4.15), (12, 9, 11, 26, 33),
           width: 0.3, fill: vb.muted.lighten(40%),
           label: [known-imprecision suite]),
  ),
  caption: [Assertions discharged per selectable analysis. Bars are read off
    the regression runner, so the figure and the test suite cannot disagree.],
) <fig:eval>

#figure(
  table(
    columns: 4,
    align: (left, right, right, right),
    stroke: none,
    table.hline(),
    [session], [theories], [lines], [lemmas],
    table.hline(stroke: 0.5pt),
    [#isasession("Voblint_VIMP")], [14], [6 200], [210],
    [#isasession("Voblint_CFG")], [23], [12 800], [480],
    [#isasession("Voblint_Core")], [31], [18 400], [690],
    [#isasession("Voblint_Analysis")], [28], [15 100], [520],
    [#isasession("Voblint_Soundness")], [9], [4 300], [130],
    table.hline(stroke: 0.5pt),
    [total], [105], [56 800], [2 030],
    table.hline(),
  ),
  caption: [Size of the formalization by session. Numbers are placeholders
    until the counting script runs in the build.],
) <tab:size>
