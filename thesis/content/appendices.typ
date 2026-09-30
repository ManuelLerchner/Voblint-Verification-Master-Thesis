#import "../lib/math.typ": *
#import "../lib/code.typ": isaconst, isai, isalocale, isasession, isathm, isatype, listing
#import "../lib/figures.typ": (
  dep-edge, global-unk, intra-edge, ppoint, side-edge, snapshot-var, subfigures, unk,
)
#import "../lib/sources.typ": proved
#import "@preview/fletcher:0.5.8": diagram, edge, node
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

= Program globals as flow-insensitive unknowns <sec:mixed-flow>

// A value at `pp7`, after both calls, from the flow-sensitive Sign run.
#let _mf(var) = snapshot-var("mixed-flow-sign", "main_pp7_ctx0", var)

The shipped analyses keep program globals in the flow-sensitive local value of
every unknown, next to the locals. Goblint's base analysis makes the same
choice for single-threaded programs: it reads globals from its local state and
publishes nothing (#link("https://github.com/goblint/analyzer/blob/5320a6b741e50dc049f7a1b85e1709e9565cc54a/src/analyses/base.ml")[`base.ml`]). Seidl et
al. note that global store widening improves scalability and also helps
incremental analysis @seidl26[§1]. The following program
compares the two placements:

#listing(lang: "c", claim: "mixed-flow-sign", ```
global Gx;
fun set() { Gx = 1; }
fun get() { return Gx; }
fun main() { x = 1; set(); y = get(); }
```)

Flow-sensitively, the value of `Gx` travels with the state. It enters `set`
with the caller's state, comes back through the return combination and enters
`get` from `main`'s continuation, so every procedure's unknowns carry every
global. An analysis may instead keep one fact per global that holds throughout
the run: a flow-insensitive unknown written by side effects (@ch:background),
which the certificate (@sec:certificate) makes bound everything published to
it. The write in `set` then reaches the read in `get` through that fact. This
loses precision, because the fact must cover the initial `Gx = 0` as well as
the written 1. Sign can only claim #signval("≥0") for `Gx` and for `y` after
`y = get()`, although every run ends with `y = 1`. A flow-sensitive analysis
carries #signval("+") from `set`'s exit into `get`'s entry and derives
#signval(_mf("y")) for `y` (claim `mixed-flow-sign`).

The lifter #isaconst("ownership_split_lift") adds one global unknown
$kappa = #isaconst("Analysis_Global") thin ()$ whose value is an abstract
store for all VIMP globals together. Every lifted transfer reads the globals
from $kappa$ and publishes the global half of its result there. A solved store
is read back by merging the local half with $sol(kappa)$
(#isaconst("gamma_ownership_split")), and soundness makes $sol(kappa)$ cover
the globals of every store reached anywhere.

For @ch:equations to apply, the lifted specification must meet the analysis
soundness contract. #isathm("ownership_split_lift_contract") shows this for
every transfer bundle that satisfies
#isalocale("sound_nonrelational_transfer"). The solved example above runs the
executable Sign instance of the split specification
(#isaconst("ownership_split_dg_spec_st_for")), whose contract is proved
separately (#isathm("analysis_contract_mf")), and the generator instance fixes
$kappa$. Its routed obligations of @sec:eq-routing are discharged only for this
program, under the unit context and the join update rule, from facts evaluated
on its solved table with the code-generator oracle (@ch:executable). They bound the stores at
`pp7`, the node after both calls:

#proved("mf_after_calls")

The bound on `y` is what the flow-insensitive `Gx` leaves. The analysis is not
selectable in #isaconst("run_voblint"), and no theorem discharges its routed
obligations for every program.

All program globals share $kappa$ because #isalocale("analysis_contract")
fixes the type of analysis-global names to `unit` (@sec:sound-core). Several
names would need a concretization over an environment that maps each name to
its value. The values of different globals stay apart inside $kappa$, since
joins and widening act on each entry of the store, but the solver sees one
unknown (@fig:shared-deps). A write to `g` therefore re-evaluates a node that
reads only `h`. The update rule also decides between widening and narrowing
for the whole store (@sec:update-rules): while `g` still grows, $kappa$ is
widened, and `h` cannot be narrowed until `g` has stabilized. Apinis et al.,
Seidl et al. and Goblint keep one unknown per global @apinis12[§5]
@seidl26[§3]. The manager is already generic in the name type.

// A straight-line procedure over two flow-insensitive globals g and h: which
// right-hand sides read (grey) and publish to (double tip) the global unknowns,
// and which nodes the solver re-evaluates when g = g + 1 publishes (orange).
// (a) Voblint keeps all analysis globals in one global unknown; (b) one global
// unknown per global, as Goblint does.
#let _deps(split) = {
  set text(size: 8pt)
  let hot = if split { (2,) } else { (2, 3) }
  let pt(i) = if i in hot {
    unk((0, i), $u_#i$, state: "unstable", name: label("u" + str(i)))
  } else { ppoint((0, i), $u_#i$, name: label("u" + str(i))) }
  let edges = (
    intra-edge(<u0>, <u1>, label: "x = x + 1", label-side: right),
    intra-edge(<u1>, <u2>, label: "g = g + 1", label-side: right),
    intra-edge(<u2>, <u3>, label: "y = h", label-side: right),
  )
  if split {
    diagram(
      spacing: (10mm, 9mm),
      ..range(4).map(pt),
      global-unk((1.5, 1.6), $kappa_g$, name: <kg>),
      global-unk((1.5, 3), $kappa_h$, name: <kh>),
      ..edges,
      dep-edge(<kg>, <u2>, bend: 18deg),
      side-edge(<u2>, <kg>, bend: 18deg),
      dep-edge(<kh>, <u3>, bend: 18deg),
    )
  } else {
    diagram(
      spacing: (10mm, 9mm),
      ..range(4).map(pt),
      global-unk((1.5, 2), $kappa$, name: <k>),
      ..range(4).map(i => node((-0.75, i), text(fill: vb.muted, $(d_#i, bot)$))),
      node((2.1, 2), text(fill: vb.muted, $(bot, v)$)),
      ..edges,
      dep-edge(<k>, <u2>, bend: 18deg),
      side-edge(<u2>, <k>, bend: 18deg),
      dep-edge(<k>, <u3>, bend: 18deg),
    )
  }
}

#subfigures(
  figure(_deps(false), caption: [one global unknown $kappa$ for `g` and `h`]),
  <fig:shared-deps-one>,
  figure(_deps(true), caption: [one global unknown per global]),
  <fig:shared-deps-per>,
  columns: (1.2fr, 1fr),
  placement: auto,
  caption: [The right-hand sides that depend on the global unknowns of two
    flow-insensitive globals `g` and `h` (schematic). Grey arrows are reads
    (#ctor("QueryG")), purple double-tipped arrows publications (#ctor("Side")),
    and orange nodes are re-evaluated when `g = g + 1` enlarges the value of
    `g`; $u_1$, after `x = x + 1`, depends on no global. Voblint keeps all
    analysis globals in one global unknown (a), so the write to `g` also
    re-evaluates $u_3$, which reads only `h`. With one global unknown per global
    (b), as in Goblint, it does not. In (a) each unknown holds a
    #isatype("dg_state") (grey).],
  label: <fig:shared-deps>,
)

The shipped analyzer publishes only to the activation seeds
(@sec:eq-seed-global). @ch:related compares the instance with
earlier mechanizations of mixed flow sensitivity.
