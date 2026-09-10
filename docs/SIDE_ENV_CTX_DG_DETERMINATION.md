# `side_env_ctx` unit-context spine: DG-derivation determination

> **Status:** historical. The effectful unit-context endpoint was deleted; its
> reusable helpers now live in `TD_Side_Eff_Ctx_Shared`.
>
> **Framing correction (see `GOBLINT_DG_INTERFACE_VALIDATION.md`):** the
> "local-only routing" this doc calls an *obstruction* is, per Goblint source
> (`base.ml` computes context from local state and drops globals), the *faithful*
> model. DG's `rt` over `dg_D_c` is correct as-is; the effectful spine's
> `side_env_ctx` (local ⊔ unit-global) routing is the outlier. The conclusion —
> keep the effectful spine on the generic backbone — stands, for that reason.

## Question

Can the remaining `TD_Side_Eff_Ctx_Sound` unit-context soundness endpoint
(`post_fixpoint_sound_at_ctx_semantic` / `semantic_entry_store_ctx_analysis_sound`)
become a derived `Local_DG` (or genuine multi-domain `sound_dg_spec_core`) instance,
removing another independent proof foundation?

## Verdict

| Target | Verdict |
| --- | --- |
| Shares the canonical backbone induction | **YES — done.** |
| Genuine multi-domain `sound_dg_spec_core` instance | **NO.** Routing incompatibility (below). |
| Trivial `Local_DG` (`G = unit`) instance via the existing adapter | **NO.** `sound_transfer` coupling + non-vacuous DG axioms. |
| Every context-sensitive endpoint derives from `sound_dg_spec_core` | **Already true up to naming** — see the inertness finding. |

## What was done

`post_fixpoint_sound_at_ctx_semantic` carried its own `trace_witness.induct`
(~47 lines) — a byte-near copy of the backbone `trace_ctx_sound_meaning`. It is now
a direct instance of the backbone:

```
M  (p,c) = [[side_env_ctx sigma (p,c)]]      -- the effectful reading sigma(Inl) ⊔ sigma(Inr())
rd (p,c) = side_env_ctx sigma (p,c)          -- routing read: the SAME full reading
rt cl ctx r = ec ctx r                       -- value-derived callee context
```

The 8 premises (`ENTRY/PROC_ENTRY/EDGE/COMB_BOUND/DG_INTRA/DG_RETURN/DG_CALLEE/
ENTER_MONO`) are unchanged; only the combine case is spine-specific, discharged by
`combine_case_ctx_sound`. Two helper lemmas the old induction inlined
(`prefix_compat_return`, `callee_entry_compat`) became dead and were deleted.
Net: `TD_Side_Eff_Ctx_Sound.thy` 1181 → 1150 lines; the file's only duplicated
trace induction is gone.

`semantic_entry_store_ctx_analysis_sound` (the concrete entry-store endpoint,
consumed by `Example_Entry_Store_Context_Precision` and `Seeded_Clean_Ctx_Collect`)
is unchanged in statement and strength — it rides the redirected theorem.

## Why not a genuine multi-domain DG instance — the routing incompatibility

The DG context endpoint `dg_collect_ctx_sound` routes the callee context through

```
last rho ∈ dg_gamma_c sigma (rt cl ctx (dg_D_c sigma ctx cl)) ex
```

i.e. the context selector reads **only the local slot** `dg_D_c = locals(sigma(Inl …))`.
The effectful spine's selector reads the **full** value:

```
ec ctx (side_env_ctx sigma (cl,ctx))  =  ec ctx (sigma(Inl(cl,ctx)) ⊔ sigma(Inr()))
```

A genuine two-domain split — local part in `D`, effectful global `sigma(Inr())` in
`G` — makes `dg_D_c` expose the local part alone, so `rt` can no longer reconstruct
`side_env_ctx`. The routing premise `ENTER_MONO`/`COMB` would then be unprovable
(the caller value the callee context depends on is missing its global join). The
effectful global is **genuinely used**, so it cannot be dropped.

## Why not a `Local_DG` instance via the existing adapter

The one shape that aligns the routing is folding the *whole* reading into `D`:
`loc(v,ctx) = side_env_ctx sigma (v,ctx)`, `G = unit`, `local_gamma d () = [[d]]` —
the `Local_DG` shape. At the reading level this matches exactly. Two blockers stop
the existing adapter:

1. **`sound_transfer` coupling.** `local_dg` is a sublocale of `sound_transfer`
   (pure `tf`). `local_dg.dg_collect_ctx_sound` therefore demands a `sound_transfer
   tf` witness. The effectful endpoint has only `sound_effectful_transfer etf`; no
   pure `tf` is in scope, and manufacturing one is spurious coupling.
2. **DG axioms are not vacuously inhabited.** `sound_dg_spec_core` requires `step_sound`
   / `combine_sound` for a real over-approximating step. `bounded_semilattice_sup_bot`
   has no top, so no trivial witness spec exists — the interpretation genuinely needs
   a sound transfer.

## The load-bearing finding: `sound_dg_spec_core` is inert for context routing

`dg_collect_ctx_sound`'s proof uses **none** of the `sound_dg_spec_core` axioms
(`gammaDG_mono`, `step_sound`, `combine_sound`). It is `collect_ctx_sound_meaning`
plus definitional unfolding of `dg_gamma_c` / `dg_D_c`. The locale is a *naming
layer* — supplying `dg_gamma_c` as the meaning — not a proof foundation for the
value-dependent endpoint. The axioms are load-bearing only in the single-context
`dg_postfix_c_collect_sound` (plain `cfg_collect`, same-context combine).

Consequence: for **every** context-sensitive (value-dependent-routing) endpoint,
"derives from `sound_dg_spec_core`" is equivalent to "derives from
`Ctx_Collect_Backbone` with `dg_gamma_c` as the meaning." The canonical foundation
is the backbone. The effectful spine now rides it directly — the *same* foundation
the DG endpoint rides.

## Minimal interface extension (if uniform DG naming is still wanted)

Split `sound_dg_spec_core` into two locales:

```
dg_meaning       fixes gammaDG only; hosts dg_gamma_c / dg_D_c / dg_collect_ctx_sound
sound_dg_spec_core    extends dg_meaning with the 3 axioms; hosts dg_postfix_c_collect_sound
```

Then both the clean and effectful spines interpret `dg_meaning` with
`gammaDG d _ = [[d]]` at **zero** axiom cost (no `sound_transfer`, no `step_sound`),
and ride `dg_collect_ctx_sound`. This is presentational: it renames the backbone
call as a DG call. It removes no further foundation, because the backbone already is
the foundation. Recommended only if a single uniform endpoint name is valued over
minimal locale surface. Not performed here.

## Dependency graph

Before:

```
TD_Side_Eff_Ctx_Sound
  post_fixpoint_sound_at_ctx_semantic  -- own trace_witness.induct  (independent foundation)
    combine_case_ctx_sound, callee_entry_compat, prefix_compat_return
```

After:

```
Ctx_Collect_Backbone.trace_ctx_sound_meaning   (the one induction)
        ↑  rd = side_env_ctx sigma,  rt = ec
TD_Side_Eff_Ctx_Sound
  post_fixpoint_sound_at_ctx_semantic  -- backbone instance
    combine_case_ctx_sound             (combine discharger, spine-specific)
```

`callee_entry_compat`, `prefix_compat_return` — deleted (dead).

## Retirement of `TD_Side_Eff_Ctx_Sound`?

**Yes — the file was deleted.** The shared helpers that used to live there now
reside in `TD_Side_Eff_Ctx_Shared`; the current consumers are DG / keyed / digest /
clean analyses.

## End-state summary

Every soundness endpoint's context-sliced induction now flows through the single
`Ctx_Collect_Backbone`:

- DG two-gamma endpoint → `dg_collect_ctx_sound` → backbone
- clean single-domain → `clean_ctx_collect_rread_via_dg` → `local_dg` → backbone
- keyed cmp → `side_cfg_T_eff_cmp_collect_ctx_sound_semantic` → backbone
- digest → `obs_digest_collect_ctx_sound(_bot)` → backbone
- **effectful unit-context → `post_fixpoint_sound_at_ctx_semantic` → backbone (historical)**

The backbone is the canonical foundation; `sound_dg_spec_core` sits above it as the
two-domain naming layer, load-bearing only for the homogeneous single-context combine.

## Consumer matrix

| Consumer | Global affects routing? | Local-only result | Existing replacement | Decision |
| --- | --- | --- | --- | --- |
| `side_collect_sound_exit_pruned_ctx` | n/a | n/a | none | **Deleted**; dead cone, no live consumers |
| `post_fixpoint_sound_at_ctx_semantic` | historical | historical | `Ctx_Collect_Backbone` plus current DG / keyed / digest / clean stack | **Deleted** |
| `semantic_entry_store_ctx_analysis_sound` | historical | historical | none | **Deleted** |
| `Example_Entry_Store_Context_Precision` | historical | historical | none | **Deleted** |
| `side_env_ctx`, `pull_ctx`, `unit_combine_tree_ctx`, `etf_full_ctx_unit`, `inr_slot_locals_bot_ctx` | shared helpers extracted | current users are DG / keyed / digest / clean | `TD_Side_Eff_Ctx_Shared` | **Retired as a spine; keep only extracted helpers** |

## Remaining blockers

- No proof blocker remains for the canonical DG/local-only path.
- No blocker remains. The effectful entry-store path was deleted, and the shared helpers were extracted.

## Final recommendation

The `side_env_ctx` path is retired.
Keep the shared helpers in `TD_Side_Eff_Ctx_Shared` only.
