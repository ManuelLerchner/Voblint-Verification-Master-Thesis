# CFG collecting semantics

**Main contribution:** The operational collecting specification of programs on the
compiled CFG: interprocedural lfp `cfg_collect`, trace-valued
`cfg_collect_trace`, and the unified `collecting` locale.

**Theories (dependency order)**

| File | Role |
| --- | --- |
| `CFG_Collect.thy` | `edge_collect`, `edges_collect`, `collect_pp`, `collect_combine_pp`, `cfg_collect_F`, `cfg_collect`, and the witness/path-to-lfp bridge |
| `CFG_Collect_Runs.thy` | `cfg_runs_to` (exit projection); run-to-collecting witness (`inc_pi` example) |
| `CFG_Collect_Unified.thy` | `collecting` locale parameterised by `combine_at`; `ip.collect = cfg_collect` |
| `CFG_Collect_Trace.thy` | `cfg_collect_trace` — IP trace collecting; `alpha_last`; projection `alpha_last (cfg_collect_trace …) ⊆ cfg_collect …` |

**Specification spine**

- **IP state:** `cfg_collect g S v` — lfp of `cfg_collect_F`; used by `unified_post_fixpoint_sound`.
- **IP trace:** `cfg_collect_trace g S v` — trace-valued IP collecting; `alpha_last` projects to last stores.
- **Exit sugar:** `cfg_runs_to pi ps c s t` — definitional abbreviation for membership in `cfg_collect … (cfg_exit …)`.

**Downstream:** `Analysis/Equations/Constraint_System_Sound.thy` — `post_fixpoint_sound_at`;
`Analysis/Equations/Analysis_Sound.thy` — `unified_post_fixpoint_sound`.
