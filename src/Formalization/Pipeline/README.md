# End-to-end pipeline

**Main contribution:** Composes the trace-IP projection (`alpha_last`) with the unified
IP post-fixpoint soundness to obtain trace-level soundness theorems. Also provides
global-read soundness and digest-read soundness as corollaries.

**Theory:** `Trace_Analysis_Sound.thy`

**Main theorems**

| Theorem | Meaning |
| --- | --- |
| `trace_analysis_sound` | `alpha_last (cfg_collect_trace g S v) ⊆ γ(env v)` — analyzer sound w.r.t. IP trace semantics |
| `reaching_global_read_sound` | For every reaching trace `tr` at `v`: `(last tr) x ∈ γ(env v x)` |
| `reaching_global_read_sound_d` | Digest-indexed variant: soundness for the `reaching_compat dgx rel d` refinement |
| `digest_read_sound` | Digest-level corollary: `d ∈ dgx '' reaching_compat …` |
| `flat_env_is_digest_sound` | Per-pp flat abstract env is a valid digest (specialises the digest family to the sign domain) |

**Context:** `sound_transfer` locale — parameterised over an abstract domain with
proved transfer soundness.

**Proof structure:** Composes two steps:

1. `alpha_last_cfg_collect_trace_le` — `alpha_last (…cfg_collect_trace…) ⊆ cfg_collect`.
2. `unified_post_fixpoint_sound` — `cfg_collect … ⊆ γ(env v)`.
Then applies `subset_trans`.

**Imports:** `Voblint_Analysis.Analysis_Sound`, `Voblint_CFG.CFG_Collect_Trace`.

**Downstream:** `Analysis/Domains/Sign_Side_Soundness.thy` imports `TD_Side_Eff_Soundness`
(not this file directly); `Example_Side_Proc_Global.thy` uses `side_sign_analysis_sound`.
