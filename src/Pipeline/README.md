# End-to-end pipeline

**Main contribution:** Parameterised soundness of the full analyzer pipeline —
IMP2 → `to_cfg` → `rhs` / `td_analyse` → concretization — stated against
**`cfg_collect` at every program point** (not only at exit).

**Theory:** `Pipeline.thy` — also `domain_transfer_sound`, `sign_analysis_config`,
`ivl_analysis_config`, `run_analysis`.

**Main theorems**

| Theorem | Meaning |
| --- | --- |
| `pipeline_invariant_sound` | Every `v`: `cfg_collect (to_cfg c) {s} v ⊆ γ(run_analysis cfg c v)` |
| `sign_pipeline_invariant_sound` | Sign-domain instance of the invariant |
| `pipeline_sound_path` | Along any `cfg_path`, stores in `edges_collect` are covered |
| `pipeline_sound_runs_to` | Exit corollary from `t ∈ cfg_collect … (cfg_exit …)` |
| `pipeline_sound_runs_to_runs` | Same, with `runs_to c s t` as premise |
| `sign_pipeline_sound` / `ivl_pipeline_sound` | Sign and interval exit corollaries (from `runs_to`) |

**Imports:** `TD_Soundness`, `Sign_Domain`, `Interval_Domain`.

**Top-level corollary:** `goblint_sign_sound` in `Goblint_Formalization.thy`.
