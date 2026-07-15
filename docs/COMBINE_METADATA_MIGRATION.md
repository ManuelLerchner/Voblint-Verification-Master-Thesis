# Combine-metadata migration — status and remaining slices

Companion to `IMP2_PARAMETERS_RETURNS_MIGRATION_PLAN.md`, which holds the design.
This document tracks *where the migration currently stands* and how the remaining
work splits into independently checkable pieces.

## 1. Where the cut currently sits

`combine_info` is a 5-tuple in the CFG layer:

```isabelle
type_synonym combine_info = "pp * pp * pp * vname option * aexp option"
```

Migrated to it (green):

- `src/IMP2/` — `Call dst p actuals`, `RestoreInternal`, `bind_formals`
- `src/CFG/` — `EA_Enter formals actuals`, 5-tuple `combines`, collecting semantics
- `src/CFG/Compiler/` — the whole compiler-correctness core

Not migrated (red): the `Voblint_Analysis` session, which still destructures
`combines g` as a 3-tuple `(c, ex, ret)`.

The mismatch is a type error, not a proof gap. Feeding a 5-tuple set into a
lemma written against `(pp * pp * pp) set` infers `ret` as the *tail*
`pp * vname option * aexp option`, which is the symptom seen at
`Constraint_System_Sound.thy:197`.

## 2. Compiler-correctness restructure (done)

`Compiler_Correctness_Prototype.thy` (2930 lines, one file, Analysis-coupled) was
split. The compiler core needs only `Voblint_CFG` + `Voblint_IMP2`, so it moved
into the CFG session:

| Theory | Session | Contents |
| --- | --- | --- |
| `CFG/Compiler/Compile_Invariants` | Voblint_CFG | `wf_compile_input`, endpoints, layouts, `compile_procs_*` |
| `CFG/Compiler/Control_Residual` | Voblint_CFG | `control_at`, residual fragments |
| `CFG/Compiler/Located_Exec` | Voblint_CFG | `frames_match`, `cstep`, `control_finish_simulation` |
| `CFG/Compiler/Control_Simulation` | Voblint_CFG | `control_step_simulation`, `concrete_program_step_match` |
| `CFG/Compiler/Located_Reaches` | Voblint_CFG | `located_sound`, pruning, `cfg_reaches` transport |
| `Formalization/Pipeline/Compiler_Correctness` | Voblint_Formalization | `compiled_source_simulation` locale, side-solver soundness |

Only the last file imports `Voblint_Analysis`, so all Analysis-layer breakage is
confined there.

`control_step_simulation` is ~1000 lines in a single theorem. Splitting it into
per-constructor case lemmas is deliberately deferred; it is now isolated in its
own theory, which is the precondition for doing that safely.

## 3. Remaining work: 24 files in `Voblint_Analysis`

Two kinds, and the distinction matters for effort.

### 3.1 Mechanical — widen the pattern (11 files)

These bind combine metadata only to state coverage or finiteness
(`ret \<in> vars`, `finite (combines g)`). They never inspect the returned value,
so they need `(c, ex, ret)` widened to `(c, ex, ret, dst, rex)` and nothing more.

- `Generic/Solver/Context/Ctx_Collect_Backbone.thy`
- `Generic/Solver/Context/Goblint/DG/DG_Route_Soundness.thy`
- `Generic/Solver/Context/Goblint/Read/Support/TD_Side_Eff_Cmp_Gen.thy`
- `Generic/Solver/Context/Goblint/Read/Support/TD_Side_Eff_Cmp_Pull.thy`
- `Generic/Solver/Context/Goblint/Read/Support/Value_Digest_Reader.thy`
- `Generic/Solver/Context/Goblint/Routing/Support/Activation/Seeded_Activation_Reach.thy`
- `Generic/Solver/Core/TD_Side_Eff_Bounds.thy`
- `Generic/Solver/Core/TD_Side_Eff_Pipeline.thy`
- `Generic/Solver/Core/TD_Side_Eff_Soundness.thy`
- `Instances/Interval/Interval_DG.thy`
- `Instances/Sign/Sign_DG.thy`

### 3.2 Semantic — the abstract combine must model the return assign (13 files)

These reference `combine_states` / `<caller|callee_exit>` / `combine_abs`. The
concrete collecting semantics now evaluates `rex` in the callee exit and assigns
it to `dst` in the restored caller. An abstract `combine` that ignores `dst`/`rex`
no longer over-approximates it, so these are re-proofs, not renames.

- `Generic/Equations/Constraint_System.thy`
- `Generic/Equations/Constraint_System_Sound.thy`
- `Generic/Solver/Core/TD_Side_Tree.thy`
- `Generic/Solver/Core/TD_Side_Eff_Sound.thy`
- `Generic/Solver/Context/Goblint/DG/DG_Context_Soundness.thy`
- `Generic/Solver/Context/Goblint/DG/DG_Soundness.thy`
- `Generic/Solver/Context/Goblint/DG/Local_DG.thy`
- `Generic/Solver/Context/Goblint/Read/Clean_RRead_Sound.thy`
- `Generic/Solver/Context/Goblint/Read/Digest_Global_Read.thy`
- `Generic/Solver/Context/Goblint/Read/Support/TD_Side_Eff_Cmp_Sound.thy`
- `Generic/Solver/Context/Goblint/Routing/Support/Activation/Activation_Witness_From.thy`
- `Generic/Solver/Context/Goblint/Routing/Support/Activation/Seeded_Activation_Sound.thy`
- `Instances/Mixed/Mixed_Sign_Interval.thy`

### 3.3 The transfer interface also moves

`Constraint_System_Sound.thy:147` shows the `EA_Enter` obligation the transfer
record must now discharge:

```text
bind_formals formals (map (\<lambda>e. aval e s) actuals) (enter_state s)
  \<in> \<lbrakk>apply_tf tf (EA_Enter formals actuals) \<sigma>\<rbrakk>
```

`tf_enter` currently abstracts `enter_state` alone and cannot see formals or
actuals. This is the concrete evidence for the `call_info` extension that
`IMP2_PARAMETERS_RETURNS_MIGRATION_PLAN.md` section 11 left open: the abstract
interface needs the metadata, it cannot be closed over by generated trees.

Sign's `combine_sign` is currently the identity on the callee state. Once the
concrete side assigns `dst`, that instance is unsound until it models the assign.

## 4. Suggested slice order

Bottom-up, each slice ending file-clean in I/Q before the next:

1. `Constraint_System` + `Constraint_System_Sound` — fixes the interface every
   later layer quotes.
2. `Solver/Core` — `TD_Side_Tree`, `TD_Side_Eff_Bounds`, `TD_Side_Eff_Sound`,
   `TD_Side_Eff_Pipeline`, `TD_Side_Eff_Soundness`.
3. Instances — `Sign_DG`, `Interval_DG`, `Mixed_Sign_Interval`, plus the transfer
   records and their soundness proofs.
4. Context tower — `Ctx_Collect_Backbone`, `DG/*`, `Read/*`, `Routing/Activation/*`.
5. `Formalization/Pipeline/Compiler_Correctness` — the 44 remaining errors here
   are downstream of the above and should mostly evaporate.

Do the mechanical widenings within a slice first: they shrink the error list and
expose the genuinely semantic obligations.

## 5. Verification note

The relocated compiler core is green in I/Q (1711 commands, 0 errors) but has not
yet passed a batch build. The `Voblint_IMP2`, `IMP2`, `Deriving`, and `TD` heaps
are absent, so the next batch run is a cold bootstrap — use the staged sequence in
`AGENTS.md` with a modest `-j`, not `-j 12`.
