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
| `mixed_flow_analysis_sound` | Plain `cfg_collect g S (cfg_exit g) ⊆ γ(side_env σ)` soundness for any effectful transfer record, given a partial post-solution |
| `mixed_flow_analysis_optimal` | Soundness plus least-partial-post-solution optimality for TD_side on an effectful equation system |

**Context:** `Trace_Analysis_Sound.thy` works inside the `sound_transfer` locale.
`Mixed_Flow_Sound.thy` is stated directly over `sound_effectful_transfer`,
`threefold_mono`, and the TD_side post-solution interface. Domain theories should
provide native `effectful_domain_transfer` records (`sign_etf`, `ivl_etf`) and
discharge their structural contracts from the record shape.

**Proof structure:** Composes two steps:

1. `alpha_last_cfg_collect_trace_le` — `alpha_last (…cfg_collect_trace…) ⊆ cfg_collect`.
2. `cfg_collect_post_fixpoint_sound`, `post_fixpoint_sound`, or `side_collect_sound_exit_pruned_eff_cone` — `cfg_collect … ⊆ γ(env v)`.
Then applies `subset_trans`.

**Imports:** `Voblint_Analysis.Analysis_Sound`,
`Voblint_Analysis.TD_Side_Eff_Soundness`, `Voblint_CFG.CFG_Collect_Trace`.

**Downstream:** Examples import these theories directly when they need trace-level
or mixed-flow statements.
