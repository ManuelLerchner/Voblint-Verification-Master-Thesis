# Equation systems

**Main contribution:** Turn a CFG plus abstract domain into a constraint system
(`rhs :: pp => (pp => abs_state) => abs_state`, `rhs` for IP, `domain_transfer`
record), and prove that any post-fixpoint soundly over-approximates collecting
semantics `cfg_collect` / `cfg_collect`.

**Theories**

| File | Role |
| --- | --- |
| `Constraint_System.thy` | `domain_transfer`, `apply_tf`, `rhs`, `rhs`, `is_post_fixpoint`, `is_post_fixpoint`, `rhs_mono` |
| `Constraint_System_Sound.thy` | shared head lemmas: `apply_tf_le_rhs`, `s0_le_rhs_entry`, `edge_collect_apply_tf_sound` |
| `Constraint_System_Sound.thy` | `post_fixpoint_sound_at`, IP soundness via `rhs` and `cfg_collect` |
| `Analysis_Sound.thy` | concrete `cfg_collect` post-fixpoint engine; `unified_post_fixpoint_sound` |

**Key concepts:** One equation per program point (join over predecessor edges + combine triples).
`is_post_fixpoint g tf join bot s0 env` means `∀v. rhs g tf join bot s0 env v ≤ env v`.
`unified_post_fixpoint_sound` is the single soundness engine: constructs the
`cfg_collect_F` post-fixpoint witness and applies `cfg_collect_post_fixpoint_sound`.

**Imports:** `Constraint_System` → `CFG_Def`, `Abstract_Domain`.
`Analysis_Sound` → `Constraint_System_Sound`.

**Downstream:** `Analysis/Solver/TD_Side_Eff_Soundness.thy` — bridges `part_post_solution`
to `is_post_fixpoint` via reach cone.

## Scope vs. Voblint's actual framework

The constraint system models a **single-domain, interprocedural, side-effecting**
equation system over a CFG — matching the AFP `TD_side` solver it sits on. The
framework Voblint actually uses is **mixed flow-sensitive** (Seidl, Vojdani, Erhard,
Schwarz, FM 2026 tutorial) — a tuple `(L, G, D^X, C)` of locals, globals, per-unknown
domains, and side-effecting constraints. **None of the following structural extensions
is currently modelled here**: per-unknown distinct domains, context refinement, digests,
update rules, `demand`, `Queries`, `sync` events, multi-analysis sum/product, or
context-set tracking on globals.

This is intentional. The thesis is on the **pipeline / domain-instance axis**, not
the solver axis. The directly adjacent verified-solver work is Tilscher et al., FM 2026.
