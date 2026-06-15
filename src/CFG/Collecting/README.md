# CFG collecting semantics

**Main contribution:** The operational collecting specification of programs on the
compiled CFG: interprocedural lfp `cfg_collect_ip`, trace-valued
`cfg_collect_trace_ip`, and the unified `collecting` locale.

**Theories (dependency order)**

| File | Role |
| --- | --- |
| `CFG_Collect_Edges.thy` | `edge_collect`, `collect_pp`, `cfg_collect_F` (per-point transformer); imports `IMP2_Proc_to_CFG`, `CFG_Path` |
| `CFG_Collect_Core.thy` | `cfg_collect_paths` — path-based collecting; adequacy lemmas for the IP spine |
| `CFG_Collect_IP.thy` | `cfg_collect_ip_F`, `cfg_collect_ip` (IP lfp); `collect_combine_pp`; `combine_states` triples |
| `CFG_Collect_IP_Adeq.thy` | `pruns_to_ip` (exit projection); operational adequacy witness (`inc_pi` example) |
| `CFG_Collect_Unified.thy` | `collecting` locale parameterised by `combine_at`; `ip.collect = cfg_collect_ip` |
| `CFG_Collect_Trace.thy` | `cfg_collect_trace` — intra trace-valued collecting |
| `CFG_Collect_Trace_IP.thy` | `cfg_collect_trace_ip` — IP trace collecting; `alpha_last`; projection `alpha_last (cfg_collect_trace_ip …) ⊆ cfg_collect_ip …` |

**Specification spine**

- **IP state:** `cfg_collect_ip g S v` — lfp of `cfg_collect_ip_F`; used by `unified_post_fixpoint_sound_ip`.
- **IP trace:** `cfg_collect_trace_ip g S v` — trace-valued IP collecting; `alpha_last` projects to last stores.
- **Exit sugar:** `pruns_to_ip pi ps c s t` — definitional abbreviation for membership in `cfg_collect_ip … (cfg_exit …)`.

**Downstream:** `Analysis/Equations/Constraint_System_IP_Sound.thy` — `post_fixpoint_sound_at_ip`;
`Analysis/Equations/Analysis_Sound.thy` — `unified_post_fixpoint_sound_ip`.
