# Local-only DG adapter: single-framework feasibility probe

> **Status:** probe DELIVERED, batch-green (`Voblint_Analysis` +
> `Voblint_Soundness`, no `sorry`). **Recommendation: GO** — the single-domain
> clean analysis becomes a genuine DG instance with no client-facing global plumbing.

## Question

Can the homogeneous single-domain clean analysis (`clean_ctx_collect_rread`, the
R_read endpoint ~15 examples ride) become a **derived DG instance** rather than an
independent proof foundation — without exposing fake global machinery to clients?

Target architecture: `Ctx_Collect_Backbone -> DG_Core -> Local_DG adapter`, with the
clean analysis as `D = local state`, `G = unit`, `gammaDG d () = gammaD d`.

## What was built

`src/Analysis/Generic/Solver/Context/Goblint/DG/Local_DG.thy` (210 lines total; ~85 of
reusable adapter core):

| Name | Role |
| --- | --- |
| `local_dg_spec tf` | DG spec with trivial Side: every edge advances the local `D` by `tf`, `G` slot is `()`; combine is `combine_abs` on locals |
| `local_gamma d () = [[d]]` | the joint concretization ignores `G` entirely |
| `sound_dg_spec_core_local` | `sound_transfer tf ==> sound_dg_spec_core (local_dg_spec tf) local_gamma` — the two unused `G` obligations discharge by `simp` |
| `sound_transfer.local_dg` (sublocale) | the adapter instance, one per sound transfer |
| `local_sigma loc` | lift a clean local solution `loc :: pp x 'c => 'a abs_state` to a DG solution (Side slot `()`) |
| `local_sigma_D`, `local_sigma_gamma` | read-back: `dg_D_c (local_sigma loc) ctx v = loc (v,ctx)`, `dg_gamma_c ... = [[loc (v,ctx)]]` |
| `clean_ctx_collect_rread_via_dg` | **the clean context theorem, proved through `local_dg.dg_collect_ctx_sound`** |
| `clean_ctx_collect_rread_is_dg_corollary` | witnesses the redirection: `using assms by (rule clean_ctx_collect_rread_via_dg)` |

## Decision criteria — all met

| Criterion | Verdict | Evidence |
| --- | --- | --- |
| Client proofs carry **no** unused `G` plumbing | **PASS** | `clean_ctx_collect_rread_via_dg`'s statement is byte-identical to `clean_ctx_collect_rread`: premises `ENTRY/PROC_ENTRY/EDGE_BOUND/COMB/DG_INTRA/DG_RETURN/DG_CALLEE/ENTER_MONO` over `[[sg (Inl (v,ctx))]]`, conclusion `cfg_collect_ctx ... <= [[sg (Inl (v,ctx))]]`. No `unit`/`G`/`dg_state` in the client-facing signature. |
| Adapter is small, reusable boilerplate | **PASS** | ~85 lines, parametric in `sound_transfer tf` — one sublocale serves Sign, Interval, every domain. |
| No assumptions strengthened | **PASS** | Premises identical to the original; `local_gamma d () = [[d]]` imposes nothing on `G`. |
| Old clean theorem becomes a direct DG corollary | **PASS** | `clean_ctx_collect_rread_is_dg_corollary` closes by `using assms by (rule clean_ctx_collect_rread_via_dg)`; the original's ~30-line `context_analysis_soundness` interpretation reduces to this one line. |
| Removes a proof foundation rather than wrapping | **PASS (with one follow-up)** | The `context_analysis_soundness` interpretation inside `clean_ctx_collect_rread` becomes eliminable. One residual import: the adapter uses `clean_edge_ctx_of_bound` (from `Clean_RRead_Sound`) in the EDGE case — a domain-level `edge_collect`+mono fact, not clean-specific. Hoisting it to a domain theory severs the last dependency, making `Local_DG` a true foundation. |

## The `G`-honesty question (the original objection, resolved)

My earlier objection was that forcing the clean read onto the two-gamma carrier is false
abstraction (unused `G`). The probe shows the adapter is **not** false abstraction: `G =
unit` with `gammaDG d () = [[d]]` is an *honest* "no global fact" instance (the trivial
one-element domain), and — crucially — the trivial `G` is **invisible at the client
boundary**. The unused-obligation discharge (`edge`/`combine` global bounds) happens
*once*, inside `sound_dg_spec_core_local`, by `simp` on `local_gamma`'s definition. Clients
never see it. This is the difference between "unused parameter exposed to every client"
(the false-abstraction failure mode) and "trivial instance proved once, hidden behind a
same-shaped corollary" (this adapter).

## Overhead

* One-time: ~85-line reusable adapter (`local_dg_spec` + `local_gamma` +
  `sound_dg_spec_core_local` + `local_sigma` + 2 read lemmas).
* Per-theorem migration: the `clean_ctx_collect_rread` *body* (~30 lines of
  `context_analysis_soundness` interpretation with 8 goal cases) is replaced by the
  adapter's `dg_collect_ctx_sound` application (~45 lines, mostly mechanical
  `dg_gamma_c -> [[local slot]]` rewrites). Net: the trace-level reasoning moves into the
  shared backbone; the per-analysis code shrinks.

## Recommendation: GO

The single-framework end state is reachable **honestly**: one canonical
`Ctx_Collect_Backbone`, `sound_dg_spec_core` as the analysis interface, and the clean
single-domain analysis as a `local_dg` instance whose trivial `G` never surfaces to
clients. This supersedes the earlier "backbone-unified, keep readers separate"
compromise: the readers need not stay a *separate foundation* — they become DG
corollaries.

**Full migration plan (follow-up, not this probe):**

1. Hoist `clean_edge_ctx_of_bound` to a domain-level theory (sever `Local_DG` ->
   `Clean_RRead_Sound`).
2. Redirect `clean_ctx_collect_rread` (+ `_bound`/`_head`/`_head_bound`) to
   `clean_ctx_collect_rread_via_dg` (one-line proofs).
3. The five `clean_rread_*` transfer step lemmas are *not* collecting theorems — they
   stay (they define the clean transfer; the adapter's `local_dg_spec` re-expresses the
   same steps, so they become derivable too, but that is domain-transfer scope, separate
   from the context spine).
4. Once every `clean_ctx_collect_rread*` consumer routes through the adapter and the
   `context_analysis_soundness` locale has no remaining interpretations, retire it and
   the `side_env_cmp`/`route_read_cmp` support that only fed it.

**Constraint honored:** the homogeneous clean stack was **not** deleted in this probe;
`Local_DG` sits beside it and derives the same theorem.
