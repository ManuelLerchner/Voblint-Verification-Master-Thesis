# Equation systems

Turn a CFG plus abstract domain into a constraint system (`rhs :: pp => (pp => abs_state) => abs_state`)
and prove that any post-fixpoint soundly over-approximates collecting semantics `cfg_collect`.

**Theories**

| File | Role |
| --- | --- |
| `Constraint_System.thy` | `domain_transfer`, `apply_tf`, `rhs`, `is_post_fixpoint`, `rhs_mono`; `cinit_stores` C-faithful seed |
| `Constraint_System_Sound.thy` | `apply_tf_le_rhs`, `s0_le_rhs_entry`, `edge_collect_apply_tf_sound`; `post_fixpoint_sound_at` |
| `Analysis_Sound.thy` | `unified_post_fixpoint_sound` — single soundness engine via `cfg_collect_post_fixpoint_sound` |

**Key concepts**

One equation per program point: join over predecessor edges + combine triples.
`is_post_fixpoint g tf join bot s0 env` means `∀v. rhs g tf join bot s0 env v ≤ env v`.
`unified_post_fixpoint_sound` constructs the `cfg_collect_F` witness and applies the fixpoint lemma.

**Imports:** `Constraint_System` → `Generic/Domain/Abstract_Domain`, CFG layer.
`Analysis_Sound` → `Constraint_System_Sound`.

**Downstream:** `Generic/Solver/TD_Side_Eff_Soundness.thy` bridges `part_post_solution`
to `is_post_fixpoint` via the reach cone.

## Scope

Models a **single-domain, interprocedural, side-effecting** equation system matching the
AFP `TD_side` solver. Structural extensions (per-unknown domains, digests, context refinement,
`demand`/`Queries`, multi-analysis product) are out of scope — see `docs/NON_GOALS.md`.
