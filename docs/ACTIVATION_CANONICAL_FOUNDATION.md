# The activation witness as the canonical foundation for seeded soundness

Design note (Stage 3). Records what the activation-aware development delivers, why it
is the right foundation for seeded context-sensitive soundness, which digest machinery
it retires, and the one remaining slice for full end-to-end retirement of the old path.

## 1. What is delivered (batch-green)

* `CFG_Collect_Activation.thy` (Stage 1): the call-only activation witness
  `trace_witness_act` — context constant on ordinary edges, routed at `EA_Enter`,
  resumed at combine — with the forgetful collapse to `trace_witness` and
  `cfg_collect_ctx_act_le_collect`.
* `Seeded_Activation_Sound.thy` (Stages 2-3):
  * `activation_trace_sound` / `activation_collect_sound` — the domain-independent
    backbone, `cfg_collect_ctx_act \<subseteq> \<gamma>` from five semantic obligations.
  * `seeded_activation_edge` / `seeded_activation_seed` / `seeded_activation_comb` —
    per-rule discharge from the closed reductions.
  * `cover_seed` + `enter_state_in_cover_seed` — the locals-covering seed that makes
    `SEED_G` satisfiable (Stage-3 fix, see §4).
  * `seeded_activation_collecting_sound_cover` — the packaged theorem: with the
    covering seed, `SEED_G` reduces to seed-\<gamma> on globals plus `0 \<in> gamma pz`.
* `Activation_Domain_Instances.thy` (Stage 3): the Sign and Interval instances
  `sign_activation_collecting_sound_cover` / `ivl_activation_collecting_sound_cover`,
  and the zero-point facts `sign_zero_point` (`0 \<in> gamma SZero`) /
  `ivl_zero_point` (`0 \<in> gamma (Ivl (Fin 0) (Fin 0))`).

## 2. Why the activation witness is canonical

Goblint's context is **call-only**: `Spec.context : man -> fundec -> D.t -> C.t` is
selected once at a call and never updated on ordinary edges; unknowns are
`(node, C)`. The concrete collecting semantics `trace_witness` inlines a call (the
enter transition extends the caller trace), which is correct concrete semantics but
carries no context. The activation witness is the exact bridge: it threads the
call-only context as an **index** over the unchanged concrete trace — one rule per
Goblint protocol step (`enter` -> `context`, `combine` -> `combine_env`/`combine_assign`),
with the concrete run delegated to the forgetful map into `trace_witness`. This is the
same concrete-vs-index separation Goblint itself is built on
(`ACTIVATION_SEMANTICS_MODEL_DECISION.md`), so soundness stated against
`cfg_collect_ctx_act` is soundness against Goblint's own `(node, C)` semantics.

## 3. Digest machinery retired (task 5)

The old context soundness path threads a **whole-trace digest** and needs its
propagation laws:

| Old (`Clean_RRead_Sound.clean_ctx_trace_rread`, `post_fixpoint_sound_at_ctx_semantic`) | New (`activation_trace_sound`) |
|---|---|
| `dg :: store list => 'c` (whole-trace digest) | — (context is structural) |
| `cmp :: 'c => 'c => bool` (compat filter) | — |
| `entdg :: store => 'c` | — |
| `DG_INTRA` (digest stable across an edge) | — |
| `DG_RETURN` (digest stable across a return) | — |
| `DG_CALLEE` (callee digest = entdg) | — |
| `ENTER_MONO` (routing from the digest) | folded into `SEED_G` |

`activation_trace_sound` has **none** of `dg`, `cmp`, `entdg`, `DG_INTRA`,
`DG_RETURN`, `DG_CALLEE` — verifiable by reading its signature. The context is carried
by the witness structurally, so the three digest-propagation obligations and the
digest/compare parameters simply do not arise. This is the concrete payoff of the
structural context: the enter step is discharged by a **seed** obligation
(`SEED_G`), not by a digest law plus a transfer bound.

The digest infrastructure (`trace_witness_d`, `reaching_compat`, `cfg_collect_ctx`,
`context_transfer`, the `DG_*`-based kernels) is **not removed**: it remains part of
the current DG/keyed/digest/clean stack and the seeded activation path. The deleted
entry-store context experiment no longer depends on it.

## 4. The Stage-3 fix: the locals-covering seed

The shipped globals-only seed `restrict_global` sets callee-entry **locals** to `\<bottom>`.
Since `gamma_state` is total over all variables and `gamma \<bottom> = {}`
(`gamma_ivl bot = {}`, `gamma_sign SBot = {}`), the callee-entry slot concretises to
the **empty set**, so `SEED_G` (`enter_state s \<in> \<lbrakk>slot\<rbrakk>`, with `enter_state` zeroing
locals to `0`) is unsatisfiable. The activation witness *exposed* this — the old
`head_digest` path gave callee entries the caller context, leaving
`cfg_collect_ctx` empty there and the bound vacuously true
(`ACTIVATION_SEED_LOCALS_OBSTRUCTION.md`).

`cover_seed pz fs = (\<lambda>x. if is_global x then fs x else pz)` fixes it: keep the context
globals (R_read precision, unchanged) and pin every callee-entry local to a zero
point `pz` with `0 \<in> gamma pz`. `enter_state_in_cover_seed` then discharges the local
half, and `seeded_activation_collecting_sound_cover` reduces `SEED_G` to the *existing*
seed-\<gamma>-on-globals obligation plus the trivial `0 \<in> gamma pz` (`SZero` / `Ivl 0 0`).
This is Goblint's `Spec.enter` initialising the callee frame's locals — the piece the
globals-only witness omitted.

## 5. Remaining slice — end-to-end for the shipped runs

`seeded_activation_collecting_sound_cover` is fully proved and instantiated per domain,
conditional on a post-solution **over the covering seed** plus the run-level premises
(`cov_frame`, `SEED_glob`, `COMB_BOUND`). Feeding it a concrete run
(`rdiv_rehyd_*`, `kgen_seed_clean_*`) requires two pieces not yet built:

1. **Re-solve with the covering seed.** The shipped runs use `restrict_global`;
   instantiating needs an executable `cover_seed_st` run, a `by eval` termination
   witness, and the `st`->`abs` commutation of `cover_seed` with
   `part_post_solution_cmp_seed_st_to_abs_eff`.
2. **Generator-routing correspondence.** `cov_frame` / `SEED_glob` / `COMB_BOUND`
   must be discharged against the *actual* solver contexts, i.e. `enterc` / `combc`
   must be shown to match how the seeded generator (`gkey` / `cmb`) routes and resumes
   contexts, and `enterc kc s` must lie in the solved `vars`. This is a
   reachable-context correspondence between the abstract routing and the concrete run.

Both are genuinely new development (a new seed run + a routing-correspondence theorem),
not a re-application of an existing lemma — which is why the shipped-run end-to-end and
the retirement of the old `clean_ctx_collect_rread_head_bound` path are deferred rather
than forced. The old theorem is retained as the current soundness route for the
existing return-node results until the correspondence lands.

## 6. Bottom line

The activation witness is the canonical foundation because it states seeded
context-sensitive soundness against Goblint's own call-only `(node, C)` semantics,
carries the context structurally (retiring all digest-propagation machinery on the
seeded path), and reduces the enter step to a seed obligation that the locals-covering
seed makes satisfiable. The generic theorem and both domain instances are proved and
green; only the covering-seed re-solve and the generator-routing correspondence remain
to turn the shipped executable runs into end-to-end `cfg_collect_ctx_act \<subseteq> \<gamma>`
instances and retire the old path.
