# CFG collecting semantics

**Main contribution:** The operational collecting specification of programs on the
compiled CFG: interprocedural lfp `cfg_collect`, and the call-structured local
trace `valid_ltr` with its activation collector `cfg_collect_ctx_act`.

**Theories (dependency order)**

| File | Role |
| --- | --- |
| `CFG_Collect.thy` | `edge_collect`, `edge_step`, `call_enter_store`, `edges_collect`, `collect_pp`, `collect_combine_pp`, `cfg_collect_F`, `cfg_collect`, and the witness/path-to-lfp bridge |
| `CFG_Collect_Runs.thy` | `cfg_runs_to` (exit projection) and generic collecting introduction lemmas for edges and combines |
| `CFG_Local_Trace.thy` | call-structured local trace `valid_ltr` and the activation collector `activation_collect` (sink stores of `valid_ltr` traces reaching a node, keyed by `key`) |

`CFG_Local_Trace` currently extends `CFG_Collect`. A separate activation-local
session remains a possible future boundary, but is intentionally deferred.

**Specification spine**

- **IP state:** `cfg_collect g S v` — lfp of `cfg_collect_F`; the plain collecting endpoint.
- **Activation:** `activation_collect enterc seedc g S v c` — sink stores of `valid_ltr` traces reaching `v`, keyed by `key enterc seedc`.
- **Exit sugar:** `cfg_runs_to pi ps c s t` — definitional abbreviation for membership in `cfg_collect … (cfg_exit …)`.

**Downstream:** `src/Analysis/Generic/Equations/Constraint_System_Sound.thy` — per-step collecting soundness;
`src/Analysis/Generic/Equations/Analysis_Sound.thy` — post-fixpoint soundness bridges.
