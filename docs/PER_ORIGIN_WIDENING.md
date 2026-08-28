# Per-origin widening

An update rule that stores one abstract value **per write origin** and widens
those cells independently, reading their join. FM 2026 Sect. 5.3 proposes it as
the first improvement over widening a global's accumulated value, and states it
is "sufficient to recover a precise result in Example 1".

Voblint uses the vendored `TD` solver's own `update_global_warrowing_per_origin`
rule. It is one of four update rules the solver menu offers, reachable from the
CLI as `--solver warrow-per-origin` and from `Analysis_Config`'s
`Solver_WarrowPerOrigin`. There is no domain lift and no separate solver.

## Where it helps, and why that is narrow

Per-origin widening only pays where a **flow-insensitively** analyzed unknown
receives contributions from **several distinct origins**. The place where that
is observable in Voblint is a procedure's `FunctionEntry` seed, side-effected
once per call site.

Declared globals are not such a place **under the placement the CLI runs**. There
a `global` lives in the same reachability-lifted local unknown as every other
variable and is analyzed flow-sensitively through calls, so its writes never
accumulate into a shared slot to begin with. Measured: the paper's Fig. 1
answers `g == 42` and `h == 1` identically under all four update rules.

That is not a missing feature, and it is not a divergence from Goblint. The
paper introduces flow-insensitive globals as a choice -- "In principle, the
values of g and h could be analyzed flow-sensitively. For efficiency, we may
choose to analyze the values of one or both of them flow-insensitively" --
and Goblint's own single-threaded path makes the same choice Voblint's CLI
does: `base.ml` reads globals from local state without publication at all
(`GOBLINT_ALIGNMENT_REGISTER.md`, D/G reconstruction and publication timing,
source-checked 2026-08-10).

The other choice is already formalized. `unit_dg_spec_placed` takes a
per-variable `keep_local`/`publish_side` placement and is proved sound via
`gamma_join`, and `Example_Interval_Placement.thy` runs a program with one
global on each side: `balance`, kept local, reads `[3,3]`; `request_count`,
published to the side, reads `[0,+inf]` in the globals slot -- the paper's
Example 3 result for `h`, by `eval`, for the paper's reason. What is missing
is only a way to select a placement from VIMP source or a CLI flag; the CLI
hardwires the exclusive local routing. That flag, not any solver or domain
work, is what a source-level reproduction of Examples 2 and 3 needs.

That single site is enough to reproduce the paper's own chain. With the paper's
three contributions to `g` arriving in the paper's order:

```text
[1,1]                                the first contribution
[1,1]     \/ [-17,1]   -> [-inf,1]   lower bound grew downwards, widening drops it
[-inf,1]  \/ [-inf,42] -> [-inf,+inf]  upper bound grew, widening drops that too
```

Apinis warrowing reaches `[-inf,+inf]`, the paper's Example 2 result. Per origin
each cell holds one constant, nothing widens, and the join is `[-17,42]` --
the paper's Sect. 5.3 figure. Both are machine-checked at the CLI by
`tests/regression/19-paper-examples/`, whose 02/03 pair pins both bounds, and the
four update rules are compared one slot at a time by the `15-solver-choice/`
group, whose join, per-origin and two warrowing cases read the same two-producer
global.

Voblint answers the paper's Fig. 1 itself exactly -- `g == 42`, `h == 1` --
because it never widens a global. That beats both the paper's Example 2 result
and its recovered `[-17,42]`, and it is a difference in what is analyzed
flow-insensitively, not a better widening operator.

## Where it does not help: recursive globals

An earlier experiment tested whether per-origin widening recovers precision on a
recursive interval program, `void p(){ if (G<3){ G:=G+1; p() } else { G:=G } }`,
with origin = program point. It does not, and the origin split is not the
deciding factor. The mechanized breakdown, in order of impact:

- **Lower bound -- fixed by the widening bot-law, unrelated to origins.** Interval
  widening carries the bot-law `widen bot x = x`. Without it `bot` is the empty interval
  `[+inf,-inf]`, so an unguarded widen from `bot` jumps straight to the top
  interval, topping **every** global on its first write: `G := 5` with no loop
  gave `[-inf,+inf]`. That was the dominant loss and had nothing to do with
  per-origin widening. With the bot-law the lower bound is exact for both solves.
- **Upper bound -- lost to the recursion, not to the update rule.** The guard
  `G < 3` refines the read, but the increment's write-back is unguarded, so
  `F([0,+inf]) = [0,+inf]` is a genuine fixpoint. No value-domain machinery
  shrinks it.
- **Per-origin widening is orthogonal here.** It separates the recursion's writes
  into their own cells, but every cell tops the same way, so the join equals the
  monovariant value. Origin-separated *reads* would not help under a
  per-program-point origin either: the increment must read its own origin,
  because the previous recursion depth shares its program point, so no reader
  breaks the self-loop.
- **Narrowing is real and helps locals, not this global.** Interval narrowing
  fills an infinite bound of the widened value from the guard-refined value. It
  recovers locals (`while(x<20){x:=x+1}` reaches `[0,20]` under every update
  rule) via the guard filter. On a self-referential global there is nothing to
  descend to.

The two findings are consistent: per-origin widening fixes the loss that comes
from **joining several origins before widening**, and only that. A single origin
whose own contribution genuinely grows -- a recursive global feeding itself --
widens exactly as before, because separating one origin from itself is a no-op.
