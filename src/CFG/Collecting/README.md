# CFG collecting semantics

**Main contribution:** The operational collecting specification of programs on the
compiled CFG: least fixpoint `cfg_collect` at every program point, path-based
characterisation `cfg_collect_paths`, and exit projection `runs_to` with small-step
equivalence.

**Import:** `CFG_Runs_To_Bridge` pulls in the full chain below (also imported by
`Goblint_Formalization`, `Constraint_System_Sound`, `TD_CFG_Core`,
`Example_CFG_Collecting_Equiv`).

**Theories (dependency order)**

| File                      | Role                                                                                    |
| ------------------------- | --------------------------------------------------------------------------------------- |
| `CFG_Edges_Collect.thy`   | `edge_collect`, `edges_collect`, `cfg_collect` (lfp); imports `IMP2_to_CFG`, `CFG_Path` |
| `CFG_Collecting_Core.thy` | `cfg_collect_paths`; `cfg_collect` ⊑ path side (`cfg_collect_le_paths`)                 |
| `CFG_Collect_IP.thy`      | `cfg_collect_ip` — interprocedural collecting (`combines` + `combine_states`)           |
| `CFG_Compound_Paths.thy`  | Seq / If / While path structure and offsets                                             |
| `CFG_Path_Bridge.thy`     | `cfg_collect_eq_cfg_collect_paths`, `compile_path_small_step`                           |
| `CFG_Runs_To_Bridge.thy`  | `runs_to`, `runs_to_iff_small_step` (biconditional small-step bridge; public entry)     |

**Specification spine**

- **Canonical:** `cfg_collect (to_cfg c) S v` — soundness is stated at every `v`.
- **Paths:** `cfg_path` + `edges_collect`; equivalence in `CFG_Path_Bridge.thy`
  (`cfg_collect_eq_cfg_collect_paths`).
- **Exit sugar:** `runs_to c s t` — definitional abbreviation, not a second semantics;
  `runs_to_iff_small_step` links to `(c, s) →* (SKIP, t)`.

**Downstream:** `Equations/Constraint_System_Sound.thy` — `post_fixpoint_sound`,
`exit_sound` vs `cfg_collect`.
