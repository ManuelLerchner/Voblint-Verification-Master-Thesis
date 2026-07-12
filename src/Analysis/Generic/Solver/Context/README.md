# Solver context reads — context-indexed and digest-refined global reads

The global-read layer the core spine (`../Core/`) consumes. `digest_global_read`
(`obs_digest`) is the kernel; the context-only reads are the degenerate base it
collapses to; the `cmp` files carry the EDGE/ENTRY discharge the kernel reaches
the digest read from. See `../README.md` for the Core/Context/Exec split.

| File | Role |
| --- | --- |
| `Global_Cmp_Read.thy` | `glob_env_cmp` — context-filtered global read + `_singleton`/`_upper` lemmas |
| `Context_Domain.thy` | context-indexed store domain; the backward-compatible context-only base |
| `Digest_Global_Read.thy` | kernel locale `digest_global_read` (`obs_digest`); `obs_digest_collapse_shape`, `obs_digest_recovers_cmp_collect`, the `reaching_def_collect_sound_*` capability theorems |
| `TD_Side_Eff_Cmp_Sound.thy` | `cmp` combine layer + `post_fixpoint_sound_at_ctx_semantic_cmp*` |
| `TD_Side_Eff_Cmp_Pull.thy` | `cmp_edge_sound` / `cmp_entry_sound` — the EDGE/ENTRY discharge |
| `TD_Side_Eff_Cmp_Gen.thy` | generator-level cmp soundness |
| `TD_Side_Eff_Ctx_Sound.thy` | context-indexed pullback soundness |
| `Clean_RRead_Sound.thy` | clean read-side soundness for D/G/C-style seeded runs |
| `Seeded_Clean_Ctx_Collect.thy` | context collecting facts used by seeded-clean examples |
| `Seed_EnterMono_Lift.thy` | enter-monotonicity lifting helpers for seeded contexts |
| `Seeded_Activation_Reach.thy` | activation reachability infrastructure |
| `Seeded_Activation_Sound.thy` | seeded activation collecting soundness |
| `Activation_Witness_From.thy` | `twf` / `twfr` witness layer for recursive examples |
| `Value_Digest_Reader.thy` | generic value-projected reader locale (`value_digest_reader`, `vd_obs`); the sign mode reader (`Instances/Sign/Value_Digest_Read`) instantiates it |
| `Digest_Keyed_Writer.thy` | value-derived (mode) keyed global writer |
| `Digest_Keyed_Writer_Sound.thy` | its soundness + `part_post_solution_digest_st_to_abs_eff` transport |
| `Call_Spec.thy` | Goblint-inspired semantic call/routing contract (`call_spec`, `global_routing_spec`, `trace_context_compatibility`, `goblint_analysis_spec`; `context_collecting_sound`) |
| `Call_Spec_Generator.thy` | wiring: `spec_generator` = seeded CMP generator with `frame_seed := entry_seed`; `spec_cmb_realizes_combine` |
| `Call_Spec_Sound.thy` | Stage-0.5 endpoint: `spec_post_fixpoint_collecting_sound` — collecting soundness from a `spec_generator` post-fixpoint, no six-premise restatement |
