#import "../lib/math.typ": *
#import "../lib/code.typ": isaconst, isai, isalocale, isasession, isathm, isatype, listing
#import "../lib/figures.typ": (
  dep-edge, global-unk, intra-edge, ppoint, side-edge, snapshot-var, subfigures, unk,
)
#import "../lib/sources.typ": proved
#import "@preview/fletcher:0.5.8": diagram, edge, node
#import "../lib/theme.typ": vb
#import "../lib/claims.typ": claim-ref

= Program globals as flow-insensitive unknowns <sec:mixed-flow>

// A value at `pp7`, after both calls, from the flow-sensitive Sign run.
#let _mf(var) = snapshot-var("mixed-flow-sign", "main_pp7_ctx0", var)
// The same value from the run with program globals on the shared channel.
#let _mfs(var) = snapshot-var("mixed-flow-sign-shared", "main_pp7_ctx0", var)

By default the shipped analyses keep program globals in the flow-sensitive
local value of every unknown, next to the locals. Goblint's base analysis makes the same
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
#signval(_mf("y")) for `y` (claim #claim-ref("mixed-flow-sign")).

The simplest lifter, #isaconst("ownership_split_lift"), adds one global unknown
$kappa$ whose value is an abstract store for all VIMP globals together. Every
lifted transfer reads the globals from $kappa$ and publishes the global half of
its result there. A solved store is read back by merging the local half with
$sol(kappa)$ (#isaconst("gamma_ownership_split")), and
#isathm("ownership_split_lift_contract") shows that the lifted specification
meets the analysis soundness contract for every transfer bundle that satisfies
#isalocale("sound_nonrelational_transfer"). The values of different globals
stay apart inside $kappa$, since joins and widening act on each entry of the
store, but the solver sees one unknown (@fig:shared-deps-one). A write to `g`
therefore re-evaluates a node that reads only `h`, and the update rule decides
between widening and narrowing for the whole store (@sec:update-rules): while
`g` still grows, $kappa$ is widened, and `h` cannot be narrowed until `g` has
stabilized. Apinis et al., Seidl et al. and Goblint keep one unknown per global
@apinis12[§5] @seidl26[§3].

The analyzer does the same. Its lifter #isaconst("keyed_split_spec") keeps each
program global $x$ at its own unknown $ctor("Analysis_Global") thin x$
(@fig:shared-deps-per), so the analysis-global names are the program's
variable names. A transfer reads only
the globals its edge mentions (#isaconst("edge_global_reads")) and publishes
only the globals its edge may assign (#isaconst("edge_global_writes")), each
cut to the part of the result that describes that global. In place of every
global it does not read, the wrapped transfer receives a value that claims
nothing about it. A call reads the globals its arguments mention. The initial
value of each global is published by the program entry like any other write,
so the solved value of a global already includes its initialization. For two globals `g` and `h`,
#isathm("read_g_depends_on_g_only") and #isathm("write_h_publishes_h_only")
check this shape on one reading and one writing edge.

Skipping the unwritten globals is sound because a concrete step leaves them
unchanged (#isathm("edge_step_frame")). #isathm("keyed_split_contract")
turns this into the analysis soundness contract over environments
(@sec:sound-core) for every sound local specification, given monotone
operations to recombine a local half with a global environment and to cut out
one global, and one frame law on the carrier: a store that the result
describes, and that agrees on every unwritten global with a store the read
environment describes, is described by the result's local half recombined
with the published globals and the read environment elsewhere. The combined
state of @ch:cooperation provides these operations field by field
(#isathm("mcp_keyed_dg_analysis")): a pointwise field splits each name by
where it is stored, and the order analysis's relation stays wholly local. The
routed obligations of @sec:eq-routing are discharged for this placement as for
the default one, for every program and under all three context policies. The
placement is therefore a configuration choice of #isaconst("run_voblint")
(#ctor("Program_Globals_Flow_Insensitive"), @sec:headline), and
#isathm("run_voblint_source_sound") covers it. The command-line interface and
the playground default to bounded narrowing under this placement.

On the program above the flow-insensitive placement leaves `y` at
#signval(_mfs("y")) after both calls (claim #claim-ref("mixed-flow-sign-shared")).
This bound is what the flow-insensitive `Gx` leaves.

// A straight-line procedure over two flow-insensitive globals g and h: which
// right-hand sides read (grey) and publish to (double tip) the global unknowns,
// and which nodes the solver re-evaluates when g = g + 1 publishes (orange).
// (a) one global unknown for all globals (ownership_split_lift); (b) one global
// unknown per global, as in Voblint's flow-insensitive placement and Goblint.
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
    `g`; $u_1$, after `x = x + 1`, depends on no global. With one global
    unknown for all globals (a), the write to `g` also re-evaluates $u_3$,
    which reads only `h`. With one global unknown per global (b), as in
    Voblint's flow-insensitive placement and in Goblint, it does not. In (a)
    each unknown holds a #isatype("dg_state") (grey).],
  label: <fig:shared-deps>,
)

The update rule is chosen once per run, for the seeds and every global
together (@sec:update-rules). @ch:related compares the instance with earlier mechanizations of
mixed flow sensitivity.
