# End-to-end pipeline

**Main contribution:** Mixed flow-sensitive soundness and optimality for the
TD_side solver, stated directly over the plain collecting semantics
(`cfg_collect`).

**Theories:** `Mixed_Flow_Sound.thy`, `Source_Activation_Sound.thy`,
`Compiler_Correctness.thy`

**Main theorems**

| Theorem | Meaning |
| --- | --- |
| `mixed_flow_analysis_sound` | Plain `cfg_collect g S (cfg_exit g) ⊆ γ(side_env σ)` soundness for any effectful transfer record, given a partial post-solution |
| `mixed_flow_analysis_optimal` | Soundness plus least-partial-post-solution optimality for TD_side on an effectful equation system |

**Context:** `Mixed_Flow_Sound.thy` is stated directly over
`sound_effectful_transfer`, `threefold_mono`, and the TD_side post-solution
interface. Domain theories provide native `effectful_domain_transfer` records
(`sign_etf`, `ivl_etf`) and discharge their structural contracts from the record
shape.

**Proof structure:** the `cfg_collect ⊆ γ(env)` bound comes from
`side_collect_sound_exit_pruned_eff_cone` /
`side_analyse_eff_collect_sound_exit_pruned` (TD_side collecting soundness); the
optimality half comes from the solver's least-post-solution guarantee.

**Downstream:** Examples import these theories directly when they need mixed-flow
statements.
