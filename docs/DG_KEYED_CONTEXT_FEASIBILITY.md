# Keyed / context-sensitive soundness on the DG spine — feasibility report

> **Status:** feasibility slice DELIVERED (2026-07-14), batch-green
> (`Voblint_Analysis` + `Voblint_Formalization`, no `sorry`). Recommendation:
> **conditional GO** — see §5.
>
> Scope: decide whether the homogeneous keyed/context soundness kernel
> (`TD_Side_Eff_Ctx_Sound` + `TD_Side_Eff_Cmp_Sound` + `Clean_RRead_Sound`, ~2100
> lines) can be rebuilt over the two-gamma DG carrier before committing to the full
> migration. No existing theory deleted; no downstream example migrated.

## 0. Starting point

`DG_Soundness` proves collecting soundness for `sound_dg_spec` but fixes the context
to `unit`: `dg_gen`/`dg_D`/`dg_G`/`dg_postfix` read the single slots `Inl (v, ())` /
`Inr ()`, and `dg_gen` is literally `side_cfg_T_eff_cmp_seed_dg` frozen at
`(λ_. ())` (`DG_Soundness.thy:175`). The keyed DG generator
`side_cfg_T_eff_cmp_seed_dg gkey cmb frame_seed …` (`DG_Framework.thy:311`) is fully
context/key-general but has **no** soundness theorem. Keyed/context soundness lives
only on the homogeneous `abs_state` kernel.

## 1. What the maintained keyed examples actually need

Read tier, from source (`Example_Finite_Sign_Context_Analysis`,
`Exec_Sign_Cmp_Keyed_Run`): they pick **`gcmp = (=)`**. With equality routing,
`side_env_cmp (=) sig (p, ctx) = kw_loc p ⊔ kw_slot ctx` — each context reads *only
its own* global slot `Inr ctx` (the **diagonal / own-slot** read), never a multi-slot
join. Context *selection* at call/return (`route_read_cmp`, `kw_ec`) is exercised
(cross-context), but the global **read** is single-slot.

So the port factors into two orthogonal generalisations:

* **carrier**: `⟦·⟧` (single homogeneous gamma) → `gammaDG` (two concretizations);
* **read**: single `unit` slot → keyed slot `Inr ctx`, and — only if a future
  non-diagonal analysis needs it — a `gcmp` join.

## 2. Implemented slice

`src/Analysis/Generic/Solver/Context/Goblint/DG/DG_Context_Soundness.thy`
(inside `context sound_dg_spec`):

| Name | Statement | Role |
| --- | --- | --- |
| `collect_sound_reader` | `dg_postfix_collect_sound` with the accessors abstracted to explicit readers `dD :: pp ⇒ 'D`, `dG :: 'G` | the reusable, **context-agnostic** core |
| `dg_D_c` / `dg_G_c` / `dg_gamma_c` | keyed accessors reading `Inl (v, ctx)` / `Inr ctx` | own-slot (`gcmp = (=)`) diagonal read |
| `dg_postfix_c` | within-context post-fixpoint at `ctx` | keyed post-fixpoint |
| `dg_postfix_c_collect_sound` | `dg_postfix_c g ctx … ⟹ S0 ⊆ gammaDG s0d s0g ⟹ cfg_collect g S0 v ⊆ dg_gamma_c sigma ctx v` | **per-context soundness**, one theorem per reachable context |
| `dg_D_c_unit` / `dg_G_c_unit` / `dg_postfix_c_unit` | keyed accessors at `()` = the original unit accessors | the `unit` theorem is the `ctx = ()` instance |

`src/Analysis/Instances/Sign/Sign_DG.thy`:

| Name | Statement |
| --- | --- |
| `sign_dg_two_context_sound` | one solution over `pp × bool + bool` unknowns soundly serves **both** contexts `True`/`False`, each reading its own slots, independently seeded |

Proposed generalized theorem shape (**answers §2 of the goal**): keep the three
`sound_dg_spec` assumptions (`gammaDG_mono`, `step_sound`, `combine_sound`) unchanged;
the endpoint is `cfg_collect g S0 v ⊆ gammaDG (dD v) dG` where `dD`/`dG` read
context-keyed slots. **No new locale assumption is required for the diagonal read.**

## 3. Theorem-port classification

Against the implemented slice, classifying the homogeneous kernel:

### Direct port / already generalised (within-context)
The whole edge + within-context-combine argument. The homogeneous
`step_local_le_ctx`, `side_post_solution_le_global_ctx`, `etf_combined_le_ctx`,
`post_fixpoint_sound_at_ctx_pull/conservative/semantic` collapse to
`collect_sound_reader` + `step_sound`/`combine_sound`. **This tier is done** — the
slice proves it once, context-agnostically, in ~50 lines.

### Carrier-agnostic (port needs no `gammaDG` work)
The digest laws over `store list`: `head_digest_DG_INTRA/RETURN/CALLEE`,
`prefix_compat_return`, `callee_entry_compat`, `entry_store_dg_*`,
`trace_context_compatibility`. These constrain the context function `dg`/`entdg`/`cmp`
on concrete traces; they do not mention `⟦·⟧` and transfer verbatim.

### Requires two-gamma reformulation (the real remaining work)
Context **selection** at call/return: `route_read_cmp`, `combine_read_cmp`,
`combine_read_cmp_le`, `combine_case_cmp_sound`, `collect_ctx_sound_route`,
`side_cfg_T_eff_cmp_collect_ctx_sound_semantic`. Here the combine reads the **caller**
context's `D`/`G` and the **callee** context's `D`/`G` and must relate them — the one
place a cross-context step appears. Restating over `gammaDG` is mechanical *provided*
the D-slot and G-slot of two contexts are read independently (they are, under
own-slot). Estimated ~300–400 lines.

### Requires a `gcmp` join generalisation (only if a non-diagonal analysis appears)
`glob_env_cmp` / `side_env_cmp` with nontrivial `gcmp`, `own_slot_le_read`. **Not
needed** for any maintained example (all use `gcmp = (=)`). Defer until a consumer
exists; classifying it as *beyond current need*, not a blocker.

### Obsolete under DG
`pull_ctx` / `pull_ctx_Inl` / `pull_ctx_Inr` / `side_env_ctx_pull` — the homogeneous
solution-projection plumbing. Under DG the keyed accessors `dg_D_c`/`dg_G_c` read
slots directly; no projection layer is needed.

## 4. Answers to the feasibility questions

* **Mostly a mechanical `⟦·⟧ → gammaDG` port?** For the within-context body, *yes* —
  and it is already done, with `finE`/`finC` dropped as unused. For context selection
  at call/return, mechanical *but not trivial* (~300–400 lines). The digest laws are
  carrier-agnostic.
* **Where does the proof need `D`–`G` relations rather than separate concretizations?**
  Nowhere in the slice. `gammaDG` is used only through `gammaDG_mono` + the two
  step/combine soundness assumptions, which already package any D/G interaction inside
  the analysis. The intersection `gamma_dg` and the `gamma_unit` merge are the only two
  instantiations and neither needs a cross-carrier invariant. **The combine/return does
  not require a new cross-carrier invariant** for own-slot reads.
* **Does `ENTER_MONO` stay expressible without strengthening the DG interface?** The
  within-context part needs nothing (no `EA_Enter` that switches context). The
  cross-context `EA_Enter` reintroduces `ENTER_MONO` exactly as on the homogeneous
  spine — a candidate-solution premise, not a locale assumption (unchanged status).
* **Can keyed `side_env_cmp` reads be proved with current `gammaDG` assumptions?** For
  `gcmp = (=)` (own-slot), yes — that is `dg_G_c`, proved. General `gcmp` join is
  deferred (no consumer).
* **New locale assumptions required?** **None** for the diagonal read. The generalized
  theorem reuses `sound_dg_spec` verbatim.
* **Realistic remaining size after this slice?** The full keyed DG spine (context
  selection + digest glue + one migrated keyed Sign example with `eval`) is **~500–700
  lines**, down from the ~2100-line homogeneous kernel, because (a) the within-context
  tier is already done once and reused, and (b) `pull_ctx` projection is obsolete.

## 5. Go/No-go

**Conditional GO.** The load-bearing risk — that DG's separated concretizations
would need a cross-carrier D/G invariant the homogeneous proof hid inside `⟦·⟧` — did
**not** materialise: `collect_sound_reader` discharges the whole within-context
argument from the existing three locale assumptions, and the maintained examples read
own-slot only. The remaining work is the context-selection tier (~300–400 lines,
mechanical two-gamma restatement of `route`/`combine_read_cmp`) plus digest glue
(carrier-agnostic) and one migrated example.

**Condition:** proceed only when the goal is *retiring the homogeneous kernel* (the
24-vs-5 file imbalance), not merely adding DG context sensitivity — the payoff is the
deletion, and that requires migrating every keyed example, not just proving the DG
theorem. If the near-term aim is only a DG context-sensitive endpoint for one new
analysis, the slice already suffices via `dg_postfix_c_collect_sound`.

**Not recommended now:** the general-`gcmp` join tier — no consumer, pure speculation.
