# End-to-end pipeline

**Main contribution:** Composes the trace-IP projection (`alpha_last`) with
post-fixpoint and TD_side soundness to obtain trace-level analyzer theorems.
Also provides global-read, digest-read, mixed flow-sensitive soundness, and
mixed-flow optimality statements.

**Theories:** `Trace_Analysis_Sound.thy`, `Mixed_Flow_Sound.thy`

**Main theorems**

| Theorem | Meaning |
| --- | --- |
| `trace_analysis_sound` | `alpha_last (cfg_collect_trace g S v) ⊆ γ(env v)` — analyzer sound w.r.t. IP trace semantics |
| `reaching_global_read_sound` | For every reaching trace `tr` at `v`: `(last tr) x ∈ γ(env v x)` |
| `reaching_global_read_sound_d` | Digest-indexed variant: soundness for the `reaching_compat dgx rel d` refinement |
| `digest_read_sound` | Digest-level corollary: `d ∈ dgx '' reaching_compat …` |
| `flat_env_is_digest_sound` | Per-pp flat abstract env is a valid digest (specialises the digest family to the sign domain) |
| `mixed_flow_analysis_sound_tf` | Trace-level soundness for analyses built from a pure transfer `tf` via `etf_from_tf` |
| `mixed_flow_analysis_optimal_tf` | Soundness plus least-partial-post-solution optimality for the generated TD_side equation system |

**Context:** `Trace_Analysis_Sound.thy` works inside the `sound_transfer` locale.
`Mixed_Flow_Sound.thy` is stated directly over `sound_effectful_transfer`,
`threefold_mono`, and the TD_side post-solution interface; the `_tf` corollaries
discharge the structural obligations for pure transfers.

**Proof structure:** Composes two steps:

1. `alpha_last_cfg_collect_trace_le` — `alpha_last (…cfg_collect_trace…) ⊆ cfg_collect`.
2. `cfg_collect_post_fixpoint_sound`, `post_fixpoint_sound`, or `side_collect_sound_exit_pruned_eff_cone` — `cfg_collect … ⊆ γ(env v)`.
Then applies `subset_trans`.

**Imports:** `Voblint_Analysis.Analysis_Sound`,
`Voblint_Analysis.TD_Side_Eff_Soundness`, `Voblint_CFG.CFG_Collect_Trace`.

**Downstream:** Examples import these theories directly when they need trace-level
or mixed-flow statements.
