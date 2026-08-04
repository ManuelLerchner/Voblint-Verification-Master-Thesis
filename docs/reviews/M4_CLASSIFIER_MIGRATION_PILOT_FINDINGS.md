# Classifier migration pilot: findings from the `twice_program` attempt

Session record, not a proposal. Every claim below was checked directly
against source during the pilot (issue #83, M4.1a/M4.2 scope) by editing
live through I/Q and reading `get_diagnostics` output, not by inspection
alone. No `sorry` was left in any `.thy` file at any point.

## Starting assumption vs. outcome

The plan going in: swap `is_global` for `declared_global prog` in the
smallest available `dg_ctx_activation`/`routed_context` example
(`Example_Interval_DG_Ctx_Collect.thy`, the `twice_program` chain:
`Example_Interval_DG_IP_Flagship.thy` -> `Example_Interval_DG_Ctx_Flagship.thy`
-> `Example_Interval_DG_Ctx_Sound.thy` -> `Example_Interval_DG_Ctx_Collect.thy`),
expecting an example-local rename.

That undersold the task. The pilot instead mapped the real boundary between
an already-generic layer and a layer that was never migrated. Six of seven
generalization steps closed in one or two `simp`/`rule` calls each, citing
already-proven `_for` infrastructure. The seventh does not have a `_for`
counterpart to cite, and building one is a from-scratch proof development,
not a specialization.

## The discoveries, in the order they surfaced

### 1. M4.1's framework-generalization goal was already substantially done

`sound_transfer_for`, `sign_tf_for`, `ivl_tf_for`, `sound_dg_spec_ltr_for`
all existed before this pilot touched anything. The pattern throughout the
codebase: `X` (the historical, `is_global`-fixed name) is a one-line
sublocale/definitional specialization of `X_for` (the generic, `gs`-parametric
name) at `gs = is_global` — e.g. `sound_transfer \<subseteq> sound_transfer_for
is_global tf` (`Constraint_System.thy`). No duplicated proof content; `X`'s
old name and callers are unaffected by `X_for`'s existence.

### 2. `is_global` grep counts undercount real coupling

`Example_Interval_DG_Ctx_Sound.thy` had zero literal occurrences of
`is_global` before this pilot. It was still fully coupled to it, through

```isabelle
abbreviation Sabs :: "(ivl abs_state, ivl abs_state) dg_spec" where
  "Sabs \<equiv> unit_dg_spec ivl_tf"
```

— `ivl_tf` (not `ivl_tf_for`) is itself `is_global`-fixed at
`Interval_Transfer.thy`. Any audit of this migration's remaining scope by
literal-string search alone will misclassify files like this one as
already-generic.

### 3. The recurring shape: one missing `_for` mirror per layer, not a missing framework

Working outward from `Ctx_Sound.thy`, each layer turned out to already be
generic *except* one function, and that function's generalization was a
direct, low-risk mirror of an already-proven sibling:

| Layer | File | Missing `_for` | Fixed by |
| --- | --- | --- | --- |
| Executable transfer/enter commute | `Ivl_Exec.thy` | `ivl_tf_st_for_commute`, `ivl_enter_st_for_commute` | direct proof replay of the `is_global` originals, `gs` substituted throughout |
| D/G combine-assign | `Exec_DG_Bridge.thy` | `unit_combine_step_st_assign_for`, `unit_dg_spec_st_for` | same, using already-generic `combine_assign_resolved_q gs` |
| Run-analysis Hstep/Henter/Hcomb | `Run_Analysis_Sound.thy` | `unit_dg_Hstep_for`, `unit_dg_Henter_for`, `unit_dg_Hcomb_for` | same, citing the two rows above |

Each addition kept the old name as a callers-unchanged specialization
(`unit_combine_step_st_assign = unit_combine_step_st_assign_for is_global`,
etc.), matching the established repository pattern. `rtk make build` (full
session chain) stayed green after each addition; no other example file's
proof needed touching.

### 4. A real, previously-invisible bug: write/read classifier mismatch

Before row 2 of the table above was fixed, `Spoly` (the executable D/G spec
for the `twice_program` chain) was redefined to *write* through
`ivl_tf_st_for twice_gs`/`ivl_enter_st_for twice_gs`, while every readback
site (`fun_of_exec_dg_st`, `lookup_exec_dg_st`) still read through the
`is_global`-fixed abbreviations. This is not hypothetical: it is the exact
"classifier used to construct, update, solve, and read an executable D/G
state must be identical" invariant stated during the pilot, caught in the
act of being violated.

It stayed invisible because `twice_program` (`void twice(p) { return p + p }
void main() { x := twice(3); y := twice(10) } `) declares no globals — every
variable `is_global` and `twice_gs` (`declared_global twice_program`) both
classify as local, so write and read land on the same tag by coincidence.
On a program with one real global the mismatch would silently read the
wrong slot (default/bot) instead of the written value, while still batch-
building green. Fixed by introducing chain-local `twice_fun_of_exec_dg_st`/
`twice_lookup_exec_dg_st` abbreviations over `fun_of_exec_dg_st_for
twice_gs` and sweeping every readback site in `Ctx_Flagship.thy` to use
them.

**This finding generalizes beyond this pilot.** Any classifier swap that
touches only the write side (an interpretation's `gs` argument, matching
this repository's own earlier "swap the classifier in one line" instinct)
without auditing every `fun_of_exec_dg_st`/`lookup_exec_dg_st` site in the
same file is at risk of exactly this bug, masked by any globals-free test
program.

### 5. `unit_combine_step_st_assign` was hardcoded, not just unproven

Distinct from the discoveries above: `unit_combine_step_st_assign`
(`Exec_DG_Bridge.thy`) called `combine_assign_resolved_q is_global dst ...`
literally in its body — not a missing lemma over an already-generic
definition, but a definition that had never taken `gs` as a parameter at
all, despite `combine_assign_resolved_q` itself already being fully generic
one layer down. This is the one point in the pilot where the fix was a new
parameter on a `definition`, not a new `lemma`. Confirmed low-risk before
editing: `unit_combine_step_st_env` (the sibling half of D/G combine) needs
no such change, because it only calls `restrict_local_resolved_q`/
`restrict_global_resolved_q`, which read a location's existing tag rather
than reclassifying by name — issue #82's "classic resolved-state pair,"
confirmed here from the opposite direction (not itself in need of a `gs`
parameter, because it never had one to fix).

### 6. The readback and tree-commutation layers were *already* fully generalized

Expecting to need `fun_of_dg_st_for` and a generic `dg_tree_st_commute`,
this pilot initially wrote both from scratch — and hit a genuine Isabelle
type-inference snag along the way (a `definition` reusing a curried,
already-`definition`-polymorphic helper twice at two different types within
one equation fails to unify; using the underlying doubly-polymorphic
primitive directly, or a `case`-free direct construction, avoids it). Before
finishing, both `fun_of_dg_st_for` (`Exec_DG_Bridge.thy`) and
`dg_tree_st_commute_for`, with a full helper family (`_trav`, `_sides`,
`_dep`, `list_all2` variants), turned out to **already exist**, several
thousand lines further into the same file. The duplicate additions were
removed; nothing new was needed at this layer.

### 7. The actual blocker: two D/G equation-system pipelines, only one generalized

`dg_tree_st_commute_for` backs `part_post_solution_hook_gen_st_to_abs`
(`Exec_DG_Bridge.thy`), built over `side_cfg_T_eff_keyed_seed_trees` — the
newer hooks/placement equation-system constructor (AD-48). It does **not**
back what `Ctx_Sound.thy` actually needs: `part_post_solution_seed_dg_st_to_abs`,
built over `side_cfg_T_eff_keyed_seed_dg` — the older, classic
`dg_ctx_activation`/`routed_context` equation-system constructor that every
CallString/Ctx example (Sign and Interval both) still runs on.

`part_post_solution_seed_dg_st_to_abs`'s proof is built from three lemmas,
confirmed to exist only in `is_global`-fixed form, no `_for` sibling
anywhere in the repository:

- `dep_seed_dg_eq` (`Exec_DG_Bridge.thy:3660`)
- `eq_seed_dg_commute` (`Exec_DG_Bridge.thy:3596`)
- `sides_seed_dg_commute` (`Exec_DG_Bridge.thy:3621`)

Unlike every prior layer in this pilot, there is no generic proof one level
down to cite — generalizing this means writing `dep_seed_dg_eq_for`,
`eq_seed_dg_commute_for`, `sides_seed_dg_commute_for`, and
`part_post_solution_seed_dg_st_to_abs_for` as new proof development,
mirroring roughly 150 lines of dependency/eq/sides reasoning three times
over, not specializing an existing generic statement. This is exactly the
shape the pilot's own stop condition ("don't duplicate a complete
tree-commutation proof when no generic version exists") was written to
catch, and it is the point where work stopped.

## Architecture, as now confirmed rather than assumed

```text
                         generic (gs-parametric)
                                  |
        +-------------------------+-------------------------+
        |                                                   |
  hooks/placement pipeline                       classic seed_dg pipeline
  side_cfg_T_eff_keyed_seed_trees                side_cfg_T_eff_keyed_seed_dg
  dg_tree_st_commute_for                         (X) no generic transport theorem
  part_post_solution_hook_gen_st_to_abs          part_post_solution_seed_dg_st_to_abs
        |                                                   |
        +-------------------------+-------------------------+
                                  |
                    dg_post_solution_collect_sound_ltr
                       (collecting-soundness endpoint,
                        already gs-generic, consumes either)
```

Everything below the executable D/G state (transfer, enter, combine,
resolved-state lookup/update, readback) is generic. Everything above the
`part_post_solution` boundary (collecting soundness) is generic. The one
fixed piece is the classic pipeline's own transport theorem connecting the
two — exactly the piece AD-48's cancelled "migrate every example onto
hooks" would have made moot, and exactly the piece this pilot's evidence
newly grounds as the actual remaining M4.2 item, rather than a guess.

## What is landed vs. what remains

**Landed, batch-clean, additive only (no existing caller touched):**

- `Ivl_Exec.thy` — `ivl_tf_st_for_commute`, `ivl_enter_st_for_commute`, ret-shape lemmas
- `Exec_DG_Bridge.thy` — `unit_combine_step_st_assign_for`, `unit_dg_spec_st_for`,
  `unit_combine_step_st_commute_for`, `unit_step_st_commute_for`, `dg_spec_step_unit_st_for`
- `Run_Analysis_Sound.thy` — `unit_dg_Hstep_for`, `unit_dg_Henter_for`, `unit_dg_Hcomb_for`

**Landed but only meaningful together with the above (not yet reconciled
with the rest of the chain):**

- `Example_Interval_DG_Ctx_Flagship.thy` — `Spoly`/`twice_gs` write-and-read
  consistent, all `by eval` facts hold for real (verified: not merely
  coincidental with `is_global`, since the classifier-independence of the
  values was confirmed by actually running the generic path, not assumed).

**Reverted to `HEAD`, not migrated:**

- `Example_Interval_DG_Ctx_Sound.thy` — depends on `part_post_solution_seed_dg_st_to_abs`
  (item 7 above). Reverting it alone while keeping `Ctx_Flagship.thy`'s
  `Spoly` change produces a *worse* error count (7 vs. the original file's
  0) than either extreme, because `Ctx_Sound.thy`'s original proofs assume
  `Spoly` still matches the `is_global`-shaped value. This is an open
  question, not yet resolved: either revert `Ctx_Flagship.thy` too (clean
  infrastructure-only landing) or finish item 7 (a separate, ~150-line
  proof-development task).
- `Example_Interval_DG_Ctx_Collect.thy` — never edited.

## Recommended next decision, not yet made

Two paths for closing item 7, requiring a comparison before starting
either (mirroring the comparison `docs/reviews/M4_SPINE_BOUNDARY_AUDIT.md`
already ran for the adjacent hooks-migration question):

1. **Generalize the classic transport spine** — write `dep_seed_dg_eq_for`/
   `eq_seed_dg_commute_for`/`sides_seed_dg_commute_for`/
   `part_post_solution_seed_dg_st_to_abs_for`, keep old names as
   specializations. Real, contained, but ~150 lines of new proof content
   with no existing generic version to mirror.
2. **Migrate the classic pipeline onto hooks** — the option AD-48's own
   record says was "investigated and cancelled" for the general case. Worth
   re-examining narrowly for just the classifier-migration path, since the
   generic transport theorem already exists there; but the cancellation
   reason (large per-example size growth for small measured benefit,
   `M4_SPINE_BOUNDARY_AUDIT.md` section 0) has not been re-checked
   specifically against this narrower motivation.
