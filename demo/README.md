# voblint_pipeline — an executable model of the analyzer

A faithful, runnable Python reimplementation of the VobLint pipeline, so you can
execute, print, and debug the same computation the Isabelle formalization proves
sound. Each module cites the `file:line` it mirrors. Companion doc:
`../docs/PIPELINE_AST_TO_SOLUTION.md`.

```
com  ──compile──▶  CFG  ──side_cfg_T_eff──▶  strategy trees  ──solve──▶  post-fixpoint  ──side_env──▶  abstract state + γ
```

## Run

```bash
cd demo
python3 -m voblint_pipeline.main            # sign analysis, straight-line program
python3 -m voblint_pipeline.main_interval   # interval widening vs per-origin widening
```

`main` prints the compiled CFG, every Kleene iteration round, and the final abstract
state + concretisation `γ` at each program point.

`main_interval` runs `G := 0; while (G < 3) { G := G + 1 }` — a global that climbs
monotonically, the hard case for the infinite-height interval lattice — under three
disciplines and compares them:

1. **plain join** — does not converge (capped; `G` keeps climbing `[0,k]`);
2. **monovariant widening** (`solve_widening`) — `G = [0, +inf]`;
3. **per-origin widening** (`origin_lift.py`, mirrors `Origin_Lift.thy`) — `G = [0, +inf]`,
   **identical to (2)** — the same phenomenon as the machine-checked
   `rec_per_origin_matches_monovariant`.

The point is the negative: per-origin widening separates the *writes* by origin but the
transfer *reads* `collapse_origins`, re-merging the self-loop, so it buys no precision on
a climbing global (see `../docs/PER_ORIGIN_WIDENING.md`, OPEN_PROBLEMS P11/P12).

**Correspondence with Isabelle** (audited after the fact): the interval domain ops
(`join`/`plus`/`minus`/`leq`/`widen_ivl_core`) and the tree transform
(`lift_tree`/`collapse`/`inject`) are exact. The fixpoint *strategy* is a naive
Kleene-with-widening stand-in for the vendored TD Apinis warrowing (documented, as for the
sign demo), and the program is a loop rather than the recursive procedure — so the numbers
illustrate the mechanism rather than reproduce the `by eval` result bit-for-bit. `times` is
an unverified approximation, not exercised here.

## Modules (each ↔ a formalization file)

| file | mirrors |
| --- | --- |
| `imp_ast.py` | `IMP2_Syntax.thy`, `IMP2_Proc.thy`, `is_global` |
| `cfg.py` | `CFG_Def.thy` + `IMP2_Proc_to_CFG.thy:19` (`compile`) |
| `strategy_tree.py` | `Basics_side.thy` — `traverse_rhs` / `sides_of_rhs` / `dep_aux` |
| `state.py` | `restrict_local`/`restrict_global`/`side_env`/`combine_abs` |
| `trees.py` | `unit_edge_tree`, `local_edge_tree`, `unit_combine_tree`, `side_cfg_T_eff` |
| `sign.py` | `Sign_Domain.thy` — lattice, γ, arithmetic, forward transfer |
| `interval.py` | `Interval_Domain` / `Ivl_Exec` — interval lattice + `widen`/`narrow` (infinite height) |
| `solver.py` | naive Kleene post-fixpoint + `solve_widening` (monovariant warrowing analogue) |
| `origin_lift.py` | `Origin_Lift.thy` — `OriginState`, `lift_tree`, `solve_per_origin` (per-origin widening) |
| `main.py` | sign end-to-end driver |
| `main_interval.py` | interval widening vs per-origin widening driver |

## What is faithful, and what is simplified

**Faithful:** the strategy-tree semantics (`traverse_rhs`/`sides_of_rhs`/`dep_aux`),
the local/global split, `unit_edge_tree`'s query-global / publish-global / answer-
local shape, the `local_edge_tree` optimization (no global dependency for local
edges), the fold generator, `side_env` read-back, the sign lattice and abstract
arithmetic, and the `compile` AST→CFG rules.

**Deliberately simplified (both SOUND, just less precise / less efficient):**

1. **`assume` / `assume_not` are the identity** (`sign.py`). The real analyzer
   refines guards with the backward domain (`afilter`/`bfilter`,
   `Abstract_Domain.thy` + `Sign_Domain.thy`). Effect: at a branch join both arms
   are taken, so e.g. `if (x<0)` doesn't prune even when `x` is `Pos`. Swap a
   `bfilter` into `SignTransfer.assume` to recover precision.
2. **Naive Kleene solving** instead of the verified `TD.TD_side`. Any post-fixpoint
   is sound; `TD_side` just reaches one efficiently by following `dep_aux`.
3. **Intra core only** (`SKIP/Assign/Seq/If/While`). `Scope`/`Call` add `EA_Enter`
   edges + combine triples (`unit_combine_tree` is included and used by the fold;
   wire up `compile` for `Scope`/`Call` to exercise it).
4. **Base single-global system** (`'g = unit`). Context/digest sensitivity is the
   `map_gtree (λ_. key)` / `map_ltree` relabelling layer on top (see the doc §7);
   not modelled here.

## Debugging tips

- `solver.solve(..., verbose=True)` prints each iteration — watch values ascend the
  lattice to the fixpoint.
- To inspect one equation: build `T = side_cfg_T_eff(g, etf, bot0, s0)`, then
  `traverse_rhs(T(v), sigma, dom, vars)` is the RHS at point `v`, and
  `sides_of_rhs(T(v), sigma, dom, vars)` its global writes.
- Flip `UnitEtf(..., mixed=False)` to route every edge through `unit_edge_tree`
  (like the Interval instance) and compare the dependency behaviour.
