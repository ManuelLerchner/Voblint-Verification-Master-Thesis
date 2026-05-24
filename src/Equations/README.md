# Equation systems

**Main contribution:** Turn a CFG plus abstract domain into a constraint system
(`rhs :: pp => (pp => abs_state) => abs_state`, `domain_transfer` record), and prove
that any post-fixpoint soundly over-approximates collecting semantics `cfg_collect`.

**Theories**

| File | Role |
| --- | --- |
| `Constraint_System.thy` | `domain_transfer`, `apply_tf`, `rhs`, `is_post_fixpoint`, `rhs_mono` |
| `Constraint_System_Sound.thy` | `collect_pp_abstract_sound`, `post_fixpoint_sound`, `exit_sound` |

**Key concepts:** One equation per program point (join over predecessor edges).
`is_post_fixpoint g tf join bot s0 env` means `∀v. rhs g tf join bot s0 env v ≤ env v`
(env is a post-fixpoint of the one-step operator). `post_fixpoint_sound` is per-pp
inclusion in `gamma_state`; `exit_sound` is the exit-projected corollary.

**Imports:** `Constraint_System` → `CFG_Def`, `Abstract_Domain`.
`Constraint_System_Sound` → `Constraint_System`, `CFG_Runs_To_Bridge` (not a separate
`CFG_Collecting` theory).

**Downstream:** `Solver/TD_Interface.thy` — `make_rhs_tree`, `td_analyse`,
`td_analyse_post_fixpoint` (TD session `TD_plain`).
