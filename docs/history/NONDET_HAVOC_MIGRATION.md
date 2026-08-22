# Nondeterministic Havoc (`random()`) Migration

Status: **PLANNED, re-scoped and partially verified**. Originally authored
2026-06-19, against the pre-#41 collecting-semantics architecture (`edge_step`
in `CFG_Collect_Trace.thy`, `edges_trace`, `lift`, `alpha_last`,
`edges_trace_global_frame`). That architecture no longer exists; this
revision re-scopes the migration against the current `valid_ltr` /
`ltr_collect` architecture and records a proof-engineering-risk experiment
that checked the plan's central assumption before committing to it.

## Goal

Add a nondeterministic integer source to the source language so a single
incoming store can leave a program point as an unbounded set of stores.
Surface syntax `x := random()`; one store entering the havoc edge yields
`{ s(x := v) | v }`. This is the first genuinely nondeterministic construct
in the pipeline -- every existing edge is a deterministic function.

We model `random()`, **not** `input()`: each call is independently arbitrary,
with no ordering or consumption. That removes any oracle/stream state and
keeps `store = vname => int` unchanged across every layer.

## Decisions on record (unchanged from the original plan)

- **`random()` over `input()`.** Stateless havoc, no input stream, so no
  `store`-type surgery. `input()` would tempt an oracle-stream design
  (`store x int stream`) that threads through every layer.
- **Atomic assignment `x := random()`, not a `random()` aexp leaf.** A
  nondeterministic subexpression would break `aval :: aexp => store => int`
  (`src/VIMP/VIMP_Expr.thy`) as a total function, poisoning every
  expression-evaluation proof. The nondeterministic unit is the whole RHS:
  a dedicated statement `Havoc vname` / edge action `EA_Havoc vname`.
  `aval` / `bval` stay total and deterministic.
- **Genuine set-valued semantics, not a pre-chosen oracle.** See the design
  decision below for exactly where this lands.

## Current architecture (post-#41)

```text
VIMP_Syntax.thy (aexp/bexp, total aval/bval)
  -> VIMP_Proc.thy: com, pstep (inductive_set, relational small-step)
  -> VIMP_Proc_to_CFG.thy: compile_prog -> cfg
  -> CFG_Def.thy: cfg_node, edge_action, intra/calls relations,
                  edge_step :: edge_action => store => store option
  -> CFG_Transfer.thy: edge_collect :: edge_action => store set => store set
                        (pointwise lift of edge_step -- already set-valued)
  -> CFG_Local_Trace.thy: valid_ltr (inductive_set: init/intra/call/ret)
     LTR_Collect.thy: ltr_F (monotone transformer), valid_ltr = lfp(ltr_F),
                       ltr_collect / activation_collect (forgetful projections)
  -> Core/Equations/Constraint_System.thy: domain_transfer record
                       (tf_assign/tf_assume/tf_assume_not/tf_enter/tf_combine),
                       apply_tf :: edge_action => abs_state => abs_state
                       (plain function -- no option/set anywhere; abstract
                       interpretation already absorbs nondeterminism through
                       the concretization gamma, not through the type)
  -> Analysis/Instances/{Sign,Interval,Parity,Mixed}: per-domain transfers
  -> Core/Solver/{Context,TD_Side}: D/G framework, TD-side effectful solver
  -> Executable analysis instances / Formalization/Pipeline soundness endpoints
```

`edge_step` did not disappear in the #41 rewrite -- it moved into
`CFG_Def.thy` and became the primitive `valid_ltr`'s `intra` rule reads
directly. `valid_ltr` is not a computed trace (there is no `edges_trace`,
`lift`, or `alpha_last` anymore); it is an `inductive_set` characterized as
the least fixed point of a monotone transformer `ltr_F`
(`valid_ltr_eq_lfp`, `LTR_Collect.thy`). It was already a *set of traces*,
never a single computed run, so it already tolerates one node having many
outgoing witnesses.

There is no `pstep_deterministic` lemma anywhere in the current tree
(confirmed by repository-wide search). `pstep` (`VIMP_Proc.thy`) has always
been a plain `inductive_set` with no determinism lemma proved about it, so
there is nothing to weaken for the new `Havoc` rule.

## Design decision: where does the nondeterminism live?

Before touching any file, three designs were compared for where genuine
fan-out should be introduced.

**Design A -- widen `edge_step` itself.**
`edge_step :: edge_action => store => store option` becomes
`edge_action => store => store set`. Every consumer (`cfg_intra_step`,
`valid_ltr`, `cstep`, `edge_collect`, every "for every successor, closure
holds" soundness premise) sees the same one primitive, generalized.

**Design B -- keep `edge_step` deterministic, add a parallel
`edge_successors :: edge_action => store => store set`.**
Rejected. `EA_Havoc x`'s result cannot be expressed as an `option` (an
option has cardinality <=1), so `edge_step (EA_Havoc x) s` would have to be
either undefined (illegal for a `fun`) or `None` -- and `None` does not mean
"not modeled here," it means *this edge never fires*. Anything still routed
through `edge_step` (`cstep.Intra` in `Located_Exec.thy`, `intra_path`) would
then treat every `Havoc` edge as permanently blocked, breaking
`Control_Simulation.thy`'s existing source-to-compiled correspondence
theorem for any program containing `Havoc`. Making that theorem's
consumers use `edge_successors` instead is the only sound version of this
design -- at which point `edge_step` is a dead alias next to a primitive
that does the real work, which is exactly the parallel-interface-plus-shim
pattern this project's conventions call out as a smell. The one place a
genuinely deterministic view remains useful is `Example_Compile_Baseline.thy`
(see the affected-files table below); that is a legitimate, narrowly-scoped
exception, not a second public primitive.

**Design C -- keep the whole concrete execution deterministic; introduce
Havoc only in collecting semantics.**
Ruled out, not merely disfavored. `Control_Simulation.thy` already proves
that every source `pstep` step has a matching compiled `cstep` transition.
The `pstep` `Havoc` rule (`!v. pstep gs Pi (Havoc x, s, frs) (SKIP,
s(x:=v), frs)`) is genuinely nondeterministic by construction (Slice 1
below). If the compiled side stayed deterministic -- say, always resolving
to `v = 0` -- a source run choosing `v = 5` would have no matching compiled
transition, and the existing correspondence theorem would stop holding for
any `Havoc`-containing program. This is not a stylistic preference; it is
forced by a theorem that already exists in the repository.

**Decision: Design A.** Widen `edge_step` itself. Keep a narrowly-scoped
deterministic helper only where one already exists for unrelated,
non-load-bearing reasons (the diagnostic runner in
`Example_Compile_Baseline.thy`).

## Verification experiment

Design A's soundness case is straightforward; the open question was
proof-engineering risk: does the type change survive the existing proof
scripts unchanged, or does some proof secretly rely on `edge_step`
returning at most one value?

Checked on branch `experiment/havoc-edge-step-typecheck` (two commits,
`e16da809`, `dac10b5e`; not merged into `main`; `EA_Havoc` was
deliberately **not** added, to isolate the signature-generalization risk
from the mechanical exhaustiveness-churn of a new `edge_action` case):

1. `CFG_Def.thy`: retyped `edge_step :: edge_action => store => store set`;
   rewrote its five clauses (`Some s` -> `{s}`, `None` -> `{}`); updated
   `cfg_intra_step`, `cfg_intra_stepI/E`, `intra_path_single`,
   `edge_step_fail_iff` (`= None` -> `= {}`).
2. `CFG_Local_Trace.thy`: `valid_ltr`'s `intra` rule and
   `caller_chain_closure`'s `Intra` premise, `edge_step a s = Some s'` ->
   `s' \| edge_step a s`.
3. `LTR_Collect.thy`: `ltr_F`'s extend clause and five lemma premises,
   including the target theorem `ltr_collect_intra_step`.
4. `CFG_Transfer.thy`: `edge_collect`'s definition (drops the `Some`
   pattern for plain membership); `edge_collect_single` **simplifies** from
   `set_option (edge_step a s)` to exactly `edge_step a s` -- an identity,
   not a wrapper, once `edge_step` already returns a set.
5. `Constraint_System_Sound.thy`: `edge_of_bound`, the theorem that ties a
   concrete `edge_step` transition to abstract-transfer soundness
   (`apply_tf`/`gamma`) -- the most load-bearing premise on this path.

**Result: every touched theory is batch-clean via I/Q (0 errors, 0
warnings, full reprocessing), and every proof script closed with its
original tactics.** The only lines that changed anywhere are the
`edge_step` definition itself and premise restatements
(`edge_step a s = Some s'` -> `s' \| edge_step a s`, `= None` -> `= {}`).
No new helper lemma, no changed proof method, no case-split that wasn't
already there. In particular:

- `CFG_Def.thy` (98 commands), `CFG_Local_Trace.thy` (644 commands,
  including all four `caller_chain_closure` instantiations and
  `callee_entry_invariant`), `LTR_Collect.thy` (317 commands, including
  `valid_ltr_eq_lfp`, `valid_ltr_mono_S`, and the target
  `ltr_collect_intra_step`), `CFG_Transfer.thy` (17 commands), and
  `Constraint_System_Sound.thy` (194 commands) all reprocessed at 0
  errors / 0 warnings.
- `edge_of_bound`'s proof -- `by (simp add: edge_collect_single)`, three
  `by blast`, `by (rule edge_collect_apply_tf_sound)` -- closed completely
  unchanged. This is the theorem that would have exposed a hidden
  uniqueness dependency in abstract-transfer soundness, had one existed.

This confirms the report's central claim directly rather than by static
reading alone: abstract-transfer soundness only ever required "every
successor lands in the invariant," never uniqueness of the successor, and
`valid_ltr`'s trace layer was already relational enough to absorb fan-out
for free.

Not independently checked: the D/G and TD-side `EDGE` premises
(`Activation_Backbone.thy`, `Activation_Local_Sound.thy`,
`DG_Ctx_Activation.thy`, `DG_LTR_Sound.thy`, `LTR_TD_Side_Eff_Sound.thy`,
`LTR_TD_Side_Eff_Exit.thy`, `Source_Activation_Sound.thy`,
`LTR_Analysis_Sound.thy`). These share the identical textual shape as the
ones checked and are expected to generalize the same way, but that is an
expectation, not a verified result.

The experiment branch is retained locally as a reference and is not merged.
A real migration should start from a clean branch and add `Havoc`
coherently across syntax, CFG, compiler, semantics, and abstract transfer
in one coordinated pass, rather than resuming this partial,
signature-only spike.

## Where determinism is (and is not) baked in today

| Site | Classification | Why |
| --- | --- | --- |
| `edge_step :: edge_action => store => store option` (`CFG_Def.thy`) | Implementation detail, generalizes for free | `option` is a degenerate case of `set` (`edge_collect_single` already documented this via `set_option`, and now states it as a plain identity). Verified: see experiment above. |
| `pstep` (`VIMP_Proc.thy`) | Not a determinism assumption | Plain `inductive_set` from the start; no `pstep_deterministic` lemma exists in the current tree to weaken. |
| The `EDGE`-shaped soundness premises across `LTR_Abstract.thy`, `Activation_Backbone.thy`, `Activation_Local_Sound.thy`, `DG_Ctx_Activation.thy`, `DG_LTR_Sound.thy`, `Source_Activation_Sound.thy`, `Constraint_System_Sound.thy`, `LTR_Analysis_Sound.thy`, `LTR_TD_Side_Eff_Sound.thy` / `_Exit.thy` | Proof convenience, generalizes mechanically (verified for one, expected for the rest) | Each is already "for every successor, closure holds," never "for the unique successor." |
| `apply_tf` / `domain_transfer` (`Constraint_System.thy`) | Not a determinism assumption at all | Already a plain function over one abstract lattice point; abstract interpretation's whole point is collapsing many concrete successors into one abstract one. |
| `step_exec` / `enabled_intra` / `run_labels` (`Example_Compile_Baseline.thy`) | Genuine redesign, but scoped to one non-load-bearing file | An executable "run one path" oracle for old-vs-new compiler regression diffing, explicitly documented as "diagnostic code, not a proof device." Cannot type-check once `edge_step` returns a set; needs an explicit Havoc-exclusion or a small deterministic sub-view carved out for this file only. Zero soundness impact. |

## Migration slices (dependency order)

### Slice 1 -- base language (semantic decision + mechanical)

- `VIMP_Proc.thy`: add `com` constructor `Havoc vname`. Add relational
  `pstep` rule `Havoc: pstep gs Pi (Havoc x, s, frs) (SKIP, s(x := v), frs)`
  for all `v` -- the one genuinely new semantic rule in the whole
  migration. Add `inductive_cases HavocSE`.
- `VIMP_Syntax.thy`: mirror `Assign`'s clause in `com_vnames`,
  `source_com`, `wf_source_com`, `may_fallthrough`, `may_return_none`,
  `may_return_value` (mechanical, one clause each).
- No `pstep_deterministic` to repair -- it does not exist.

### Slice 2 -- CFG signature generalization (the one load-bearing edit)

- `CFG_Def.thy`: add `EA_Havoc vname` to `edge_action`; generalize
  `edge_step :: edge_action => store => store set`; add the `EA_Havoc`
  clause `edge_step (EA_Havoc x) s = { s(x := v) | v. True }`; update
  `cfg_intra_step` / `intra_path` premises (verified mechanical for the
  other four clauses; the `EA_Havoc` clause and its interaction with
  `edge_step_fail_iff` still need direct checking once the constructor
  exists).
- `Core/Equations/CFG_Enumeration.thy`: re-derive `linorder edge_action`
  after the new constructor (mechanical `derive`).

### Slice 3 -- downstream premise restatement (mechanical, verified low-risk)

- `CFG_Local_Trace.thy`, `LTR_Collect.thy`, `CFG_Transfer.thy`,
  `Constraint_System_Sound.thy`: verified via the experiment above --
  substitute `edge_step a s = Some s'` -> `s' \| edge_step a s` throughout,
  each proof re-closes with its existing tactic.
- `Located_Exec.thy` (`cstep.Intra` and its five per-constructor
  convenience lemmas), `Activation_Backbone.thy`,
  `Activation_Local_Sound.thy`, `DG_Ctx_Activation.thy`, `DG_LTR_Sound.thy`,
  `LTR_Analysis_Sound.thy`, `LTR_TD_Side_Eff_Sound.thy` / `_Exit.thy`,
  `Source_Activation_Sound.thy`, `LTR_Abstract.thy`: same textual shape as
  the verified files; not independently checked, expected to generalize
  identically.

### Slice 4 -- compiler and pruning (mechanical)

- `VIMP_Proc_to_CFG.thy`: `compile (Havoc x) = (n, EA_Havoc x, n+1)`
  clause, mirrors `Assign`'s compile clause.
- `CFG_Prune.thy`: add a `Havoc` case to the induction over `com`, same
  single-node/single-edge shape as the existing `Assign` case.

### Slice 5 -- abstract transfer + per-domain soundness (mechanical + small proofs)

- `Constraint_System.thy`: `domain_transfer` gets a `tf_havoc` field;
  `apply_tf` gets an `EA_Havoc` clause. Mechanical.
- `Sign_Exec.thy` / `Sign_Exec_Sound.thy`: `sign_tf_st (EA_Havoc x) s =
  update_st s x STop`; soundness case expected near-trivial via
  `gamma_sign STop = UNIV`.
- `Ivl_Exec.thy` / `Interval_Side_Soundness.thy`,
  `Parity_Exec.thy`, `Exec_DG_Bridge.thy`, `Sign_Named_Global_Eff.thy`,
  `Sign_Local_Effects.thy`: same pattern per domain instance.

### Slice 6 -- diagnostic-runner exception (design decision, not proof work)

- `Example_Compile_Baseline.thy`: exclude `Havoc` from
  `enabled_intra`'s filter, or scope the regression to havoc-free example
  programs. No proof-theoretic fix is available for this file; it is
  fundamentally a "pick one deterministic path" tool.

### Slice 7 -- showcase example

Absolute value of a random input, on the 7-element sign lattice
(`SBot SNeg SNonPos SZero SNonNeg SPos STop`):

```text
x := random();        // x : STop          (havoc -> top)
if (x > 0) {
  y := x;             // assume x > 0  =>  x : SPos,  y : SPos
} else {
  y := 0 - x;         // assume x <= 0 =>  0 - x >= 0,  y : SNonNeg
}
// join: y : SPos  join  SNonNeg  =  SNonNeg
// => analyzer certifies  y >= 0  for ALL random inputs
```

The join lands exactly on `SNonNeg`, so the post-fixpoint at the merge
point soundly states `y >= 0` for every draw. The havoc'd `x` stays `STop`;
precision on `y` is recovered purely through the assume edges. A
concrete, trace-by-trace checker cannot establish this (the trace set is
infinite); the analyzer does it in one abstract pass.

Stretch (interprocedural variant, once slices 1-5 land): havoc a global,
pass it through a parameterless procedure that clamps it, and certify the
global is `SNonNeg` after the call.

## Impact estimate

- **Implementation complexity: small.** One new `com` / `edge_action`
  constructor, roughly 20-25 mechanical case additions mirroring the
  existing `Assign` / `EA_Assign` shape.
- **Proof complexity: small-medium.** One new relational `pstep` rule
  (trivial). The `edge_step` signature generalization is verified
  low-risk on its highest-leverage path, including the abstract-soundness
  boundary. Per-domain soundness cases reduce to `gamma(top) = UNIV`. One
  contained, non-mechanical design decision in a single diagnostic-only
  example file.
- **Architectural risk: low.** No redesign of `valid_ltr`, `ltr_collect`,
  `activation_collect`, the D/G framework, or the TD-side solver. Verified,
  not just argued: the type generalization propagated through the
  concrete-collecting layer and into the abstract-soundness boundary
  theorem with zero tactic changes.

**Classification: small.** Smaller than the original issue's own estimate,
which budgeted a dedicated high-risk "trace layer" slice against code that
no longer exists.

## Open items before starting a real migration branch

- Verify the same premise-restatement pattern on the D/G and TD-side
  `EDGE` premises listed above (expected, not yet checked).
- Decide the exact scoping mechanism for `Example_Compile_Baseline.thy`
  once `EA_Havoc` exists (exclude from `enabled_intra`'s filter vs. a
  havoc-free precondition on the regression's example set).
- Confirm no other file does an exhaustive `case a of EA_Nop => ... |
  EA_Assign => ...` match without a wildcard beyond the ~20-25 files
  already identified; the full batch build is the real completeness
  check, per this project's usual workflow.
