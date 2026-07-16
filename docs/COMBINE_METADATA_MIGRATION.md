# Combine-metadata migration — status and remaining slices

Companion to `IMP2_PARAMETERS_RETURNS_MIGRATION_PLAN.md`, which holds the design.
This document tracks *where the migration currently stands* and how the remaining
work splits into independently checkable pieces.

## 1. Where the cut currently sits

`combine_info` is a 4-tuple in the CFG layer (see section 6 — the result
expression is not carried into combine):

```isabelle
type_synonym combine_info = "pp * pp * pp * vname option"
```

Migrated to it (green):

- `src/IMP2/` — `Call dst p actuals`, nullary `Restore`, `bind_formals`, `ret_var`
- `src/CFG/` — `EA_Enter formals actuals`, 4-tuple `combines`, collecting semantics
- `src/CFG/Compiler/` — the compiler-correctness core (except `Control_Simulation`)

Not migrated (red): the `Voblint_Analysis` session, which still destructures
`combines g` as a 3-tuple `(c, ex, ret)`.

The mismatch is a type error, not a proof gap. Feeding a 5-tuple set into a
lemma written against `(pp * pp * pp) set` infers `ret` as the *tail*
`pp * vname option`, which is the symptom seen at
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

## 3. Remaining work: 36 files in `Voblint_Analysis`

The breakage has **two independent axes**. A file may sit on either or both.

| Axis | Change | Files |
| --- | --- | --- |
| (a) combine arity | `combines g` is a 4-tuple set, still read as `(c, ex, ret)` | 24 |
| (b) `EA_Enter` arity | `EA_Enter` is now `EA_Enter formals actuals`, still used bare | 32 |
| | on both axes | 20 |
| | **union** | **36** |

Axis (b) is what a batch build reports first, because it is a constructor-arity
clash that fails at `fun`/`theorem` elaboration:

```text
Operator:  apply_tf tf :: edge_action => (char list => 'a) => char list => 'a
Operand:   EA_Enter    :: char list list => aexp list => edge_action
```

Bare `EA_Enter` is now a function, not a value. Most axis-(b) sites only need the
pattern given its two arguments (`EA_Enter _ _`) and are mechanical. The exception
is the transfer interface itself (section 3.3), where the arguments carry meaning.

Files on axis (b) only (no combine destructuring):

- `Generic/Solver/Context/Goblint/DG/DG_Framework.thy`
- `Generic/Solver/Context/Goblint/DG/Retain_Analysis.thy`
- `Generic/Solver/Context/Goblint/Routing/Support/Seeded_Clean_Ctx_Collect.thy`
- `Generic/Solver/Core/TD_Side_CFG.thy`
- `Generic/Solver/Exec/Exec_Bridge.thy`
- `Instances/Interval/Ivl_Exec.thy`
- `Instances/Mixed/Exec_DG_Bridge.thy`
- `Instances/NamedGlobalSign/Sign_Named_Global_Eff.thy`
- `Instances/Sign/Sign_Exec.thy`
- `Instances/Sign/Sign_Local_Effects.thy`
- `Instances/Sign/Sign_Side_Soundness.thy`
- `Instances/Tooling/Analysis_GraphViz.thy`

The rest of this section classifies the axis-(a) files.

### 3.1 Mechanical — widen the pattern (11 files)

These bind combine metadata only to state coverage or finiteness
(`ret \<in> vars`, `finite (combines g)`). They never inspect the returned value,
so they need `(c, ex, ret)` widened to `(c, ex, ret, dst)` and nothing more.

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
concrete collecting semantics now reads the callee's `ret_var` and assigns it to
`dst` in the restored caller. An abstract `combine` that ignores `dst` no longer
over-approximates it, so these are re-proofs, not renames. They need no abstract
expression evaluation, however: reading a variable and assigning it is already
`tf_assign`-shaped.

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

## 5. Verification status

`Voblint_IMP2` and `Voblint_CFG` build green in batch, so the compiler-correctness
restructure of section 2 is verified, not merely I/Q-clean.

`Voblint_Analysis` is the first failing session. `Voblint_Formalization` is only
cancelled behind it; the 44 errors in `Compiler_Correctness.thy` are downstream and
should not be worked on directly.

Two bugs cleared on the way to that point, both predating this work:

- `IMP2_Proc.thy` — `by (meson star.cases)` had no `pstep` inversion available and
  looped forever in batch. Fixed by supplying `ScopeSE`.
- `IMP2_VCG_Example.thy` — passed `source_pi`/`source_com` to `backward_sim`, which
  requires the stricter `bridge_pi`/`bridge_com`. Fixed by adding
  `bridge_count_prog` and switching both use sites.

The second is worth remembering as a pattern: `source_*` is the broad source
language (parameters allowed) used by the CFG compiler; `bridge_*` is the
AFP-translatable nullary subset. They are not synonyms.

## 6. Goblint-faithful call/return: implemented

Verified against Goblint `src/analyses/base.ml` (not assumed):

| Goblint | Here |
| --- | --- |
| `make_entry`: eval args in caller, keep globals, bind `sformals` | `EA_Enter formals actuals` / `bind_formals xs (map (aval . s) es) (enter_state s)` |
| `return`: eval result in callee, `set_var … (return_varinfo ()) rv` | `with_result body result` appends `Assign ret_var e` |
| `combine_env`: caller locals + callee globals, strips return var | `combine_states` (`<s|t>`); `ret_var` is local so it never escapes |
| `combine_assign`: read return var from callee exit, `Option.map_default … lval` | `combine_assign dst (t ret_var)` |

Consequences, all simplifying:

- `combine_info` is `(call, exit, ret, dst)` — the result expression is **not**
  carried into combine; the callee publishes it into `ret_var`.
- `RestoreInternal` is gone; `Restore` is nullary again. The reason for it
  (section 16.2) evaporates once a return variable exists.
- `combine_assign` is total (`store`, not `store option`); the malformed
  `(Some x) None` case cannot arise.
- `combine_collect` is a function, not a set-valued partial map.
- `cstep` has one `Return` rule, not `ReturnNone`/`ReturnSome`.
- `IMP2_Proc_to_CFG` needs **no** new compile clause: `with_result` reuses
  `Seq`/`Assign`, so the callee's CFG ends in a plain `EA_Assign ret_var e` edge
  and the abstract side inherits it through `tf_assign`.

`ret_var` is local and written last, so a program using that name is unaffected:
the callee's copy is dropped by `<fr|s>` and the caller's own copy is restored
from the frame.

### Status of this refactor

Green in I/Q: `IMP2_Proc` (319/319), `IMP2_Bridge` (285/285),
`IMP2_VCG_Example` (48/48), `CFG_Def` (192/192), `IMP2_Proc_to_CFG` (164/164),
`CFG_Collect` (348/348), `CFG_Collect_Trace` (439/439),
`Compile_Invariants` (539/539), `Control_Residual` (157/157),
`Located_Exec` (59/59).

Batch-confirmed earlier in the run: `CFG_Prune`, `CFG_Collect_Activation`.

Remaining: `Control_Simulation` — the ~1000-line `control_step_simulation`. Its
`ReturnNone`/`ReturnSome` case split must collapse to the single `Restore` rule,
so the theorem should shrink. Then `CFG_Collect_Runs`, `CFG_GraphViz`,
`Located_Reaches`, and the Analysis session (`tf_enter` gains formals/actuals).

### Workflow note

`open_file` does **not** re-read a file jEdit already has open. Edit on disk
*before* the first `open_file`, or edit through I/Q `write_file`. Restarting via
`./scripts/start-iq.sh` clears every stale buffer. A stale buffer once resaved a
deleted theory back onto disk.

## 7. Analysis-session migration: status

`Voblint_IMP2` and `Voblint_CFG` are **batch-green**. `Voblint_Analysis` has 25
theories green; the remaining error roots are listed below.

### Done (batch-verified)

* `combine_info` accessors: added `combine_dst`; `combine_predecessors` now
  returns `(pp * pp * vname option) set`, with `combine_predecessors_eq` as the
  bridging lemma to the `{(c, ex, dst) | ... (c, ex, v, dst) : combines g}` shape
  that `rhs` uses.
* `tf_enter :: vname list => aexp list => 'a abs_state => 'a abs_state`;
  `tf_sound_enter` mirrors `edge_collect (EA_Enter xs es)` exactly.
* `bind_formals_abs` + `bind_formals_abs_sound` + `bind_formals_abs_mono`
  (generic, in `Constraint_System`) — the abstract mirror of Goblint's
  `make_entry` argument binding.
* `combine_assign_abs` / `combine_collect_abs` + `combine_collect_sound`: the
  abstract mirror of `combine_env` then `combine_assign`.  **Pure `sound_domain`
  fact** — no domain-specific return machinery; Sign and Interval inherit it.
* Sign / Interval: `enter_frame_{sign,ivl}` (the old locals-reset) plus
  `enter_{sign,ivl} xs es` = frame reset then `bind_formals_abs`.  Parameters are
  now passed *precisely*, not havocked.
* `etf_enter` gained `xs es`; `etf_combine` gained `dst`; `unit_combine_tree`
  computes `combine_collect_abs` and splits it into Side/Answer, so a **global**
  destination is routed to the global slot automatically.

### Import fix worth remembering

`Constraint_System` referenced `bind_formals` without importing
`Voblint_IMP2.IMP2_Proc`, so it silently elaborated as a **free variable** —
the locale assumption would have been vacuous in the wrong direction.  The
imports now name `IMP2_Proc` and `CFG_Collect` explicitly.  Autoformalization
audit item 1: a missing import does not fail, it fabricates a variable.

### Open error roots

* `TD_Side_CFG` 217, `TD_Side_Tree` 451, `Analysis_GraphViz` 156,
  `TD_Side_Eff_Cmp_Sound` 130 — mechanical `(cc, ex)` -> `(cc, ex, dst)` fallout.
* `Ctx_Collect_Backbone` 60 — **not mechanical.**  `DG_CALLEE` assumes
  `hd rho = enter_state (last tau)`, but the callee entry store is now
  `bind_formals xs (map (\e. aval e s) es) (enter_state s)`.  The caller/callee
  trace linkage has to come through the `EA_Enter xs es` edge rather than a bare
  `enter_state`.  Decide the contract shape before editing: this is the one place
  where native parameters change what the context digest can assume.
