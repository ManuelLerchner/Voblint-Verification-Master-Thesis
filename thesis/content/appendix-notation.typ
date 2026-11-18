#import "../lib/notation.typ": notation-table
#import "../lib/math.typ": *

= Mathematical and Isabelle Notation <app:notation>

The thesis uses two kinds of notation. The first table lists the symbols that
the theories declare and that appear in both the formal statements and the
prose. Each entry names the Isabelle declaration that introduces it and links
to that declaration in the rendered theories. The table is generated from the
theories, so it cannot drift from them.

#notation-table()

The second table lists the notation that the thesis introduces in its prose
for the mathematical presentation, with the section that introduces it. These
symbols have no declaration of their own in the theories, or the theories write
them differently.

#figure(
  {
    set text(size: 8pt)
    set par(first-line-indent: 0pt, justify: false)
    table(
      columns: (auto, 1fr, auto),
      align: (left + top, left + top, left + top),
      stroke: none,
      inset: (x: 4pt, y: 3pt),
      table.hline(stroke: 0.5pt),
      [*Notation*], [*Meaning*], [*Introduced in*],
      table.hline(stroke: 0.4pt),
      $a lle b$,
      [$a$ is at least as precise as $b$, with strict $llt$ and converse $lge$],
      [@sec:lattices],
      $a ljoin b$,
      [join, the least upper bound, and $lJoin$ its form over a set or list],
      [@sec:lattices],
      $a lmeet b$, [meet, the greatest lower bound], [@sec:lattices],
      [$lbot$ and $ltop$],
      [least and greatest element, describing no state and every state],
      [@sec:lattices],
      $lfp f$, [least fixpoint of a monotone $f$], [@sec:lattices],
      $absval(ivl(0, 5))$,
      [a shaded value is a finite description, as opposed to the concrete set it stands for],
      [@sec:lattices],
      $sh(f)$,
      [the abstract counterpart of an operation $f$, such as $sh(+)$, #enterh, #combineenvh],
      [@sec:abs-int],
      $Unk$, [the set of unknowns of an equation system], [@sec:constraints],
      $sol$, [a valuation of the unknowns, typically a post-solution], [@sec:constraints],
      $rhs(x)$, [the right-hand side of unknown $x$], [@sec:constraints],
      $F_(v,c)(tau)$,
      [the local part of the right-hand side of the unknown $(v,c)$],
      [@sec:eq-call],
      [$Pi$, $S$, $Sigma$],
      [procedure table, initial stores, and the set of all stores],
      [@sec:vimp, @ch:traces, @sec:verdicts],
      $conc_(D G)(d, eta)$,
      [stores described by a local state $d$ under the environment $eta$ of analysis globals],
      [@sec:analysis-globals],
      $conc_M$, [concretization of the product state of the selected analyses], [@sec:coop-mcp],
      $conc_("res")$, [concretization of the configured analyses in a report], [@sec:report],
      [$u dot c$, $"take"_k$],
      [a call string extended by site $u$, and its first $k$ entries],
      [@sec:eq-routing],
      $e|_"formals"$,
      [the entry-state context, the abstract values of the callee's formals in $e$],
      [@sec:eq-routing],
      table.hline(stroke: 0.5pt),
    )
  },
  kind: table,
  placement: none,
  caption: [Notation introduced in the prose of the thesis.],
) <tab:thesis-notation>
