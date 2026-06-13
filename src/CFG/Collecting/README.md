# CFG collecting semantics

**Main contribution:** The operational collecting specification of programs on the
compiled CFG: intra lfp `cfg_collect`, interprocedural lfp `cfg_collect_ip`,
trace-valued `cfg_collect_trace_ip`, and the unified `collecting` locale.

**Theories (dependency order)**

| File | Role |
| --- | --- |
| `CFG_Edges_Collect.thy` | `edge_collect`, `collect_pp`, `cfg_collect` (intra lfp); imports `IMP2_Proc_to_CFG`, `CFG_Path` |
| `CFG_Collecting_Core.thy` | `cfg_collect_F`, intra one-step functional; monotonicity |
| `CFG_Collect_IP.thy` | `cfg_collect_ip_F`, `cfg_collect_ip` (IP lfp); `collect_combine_pp`; `combine_states` triples |
| `CFG_Collect_IP_Adeq.thy` | `pruns_to_ip` (exit projection); operational adequacy witness (`inc_pi` example) |
| `CFG_Collect_Unified.thy` | `collecting` locale parameterised by `combine_at`; `intra.collect = cfg_collect`; `ip.collect = cfg_collect_ip` |
| `CFG_Trace_Collect.thy` | `cfg_collect_trace` — intra trace-valued collecting |
| `CFG_Trace_Collect_IP.thy` | `cfg_collect_trace_ip` — IP trace collecting; `alpha_last`; projection `alpha_last (cfg_collect_trace_ip …) ⊆ cfg_collect_ip …` |

**Specification spine**

- **Intra:** `cfg_collect g S v` — least fixpoint of intra F; used by `Analysis_Sound.unified_post_fixpoint_sound`.
- **IP state:** `cfg_collect_ip g S v` — lfp extending intra with combine triples; used by `unified_post_fixpoint_sound_ip`.
- **IP trace:** `cfg_collect_trace_ip g S v` — trace-valued IP collecting; `alpha_last` projects to last stores.
- **Exit sugar:** `pruns_to_ip pi ps c s t` — definitional abbreviation for membership in `cfg_collect_ip … (cfg_exit …)`.

**Downstream:** `Analysis/Equations/Constraint_System_Sound.thy` — `post_fixpoint_sound_at`;
`Analysis/Equations/Constraint_System_IP_Sound.thy` — `post_fixpoint_sound_at_ip`;
`Analysis/Equations/Analysis_Sound.thy` — `unified_post_fixpoint_sound_ip`.
