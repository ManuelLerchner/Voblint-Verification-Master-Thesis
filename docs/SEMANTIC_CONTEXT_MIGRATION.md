# Semantic-context migration plan (Path B, soundness-only)

Historical note: the `TD_Side_Eff_Ctx_Sound` / `side_env_ctx` spine discussed in this plan has been deleted. Shared helpers now live in `TD_Side_Eff_Ctx_Shared`.

> **Agent entry point:** `TRACE_CONTEXT_ANALYSIS_MIGRATION.md` (umbrella, Track B).
> This file holds warrowing + entry-state slice detail (S0–S4).

> **STATUS (batch-sealed, `Voblint_Formalization` build exit 0, no `sorry` in `src/`):**
> The headline contribution is **DONE** — sound semantic entry-state context-sensitivity
> with a machine-checked strict-precision witness.
> - **S0** — sign warrowing back-end soundness end-to-end (`sign_exec_sound_collecting`
>   / `_trace`, `Sign_Exec_Sound.thy`), mono-free via `partial_post_solution` + RG
>   `inr_slot_locals_bot`. *Interval-apinis (real-widening) soundness is the lone S0
>   follow-on — independent transport, sign already witnesses the back-end.*
> - **S1** — context-indexed equation system + context-parametric soundness chain
>   (`TD_Side_Tree.thy` `side_cfg_T_eff_ctx`; `TD_Side_Eff_Ctx_Sound.thy`
>   `post_fixpoint_sound_at_ctx_semantic`, `side_collect_sound_exit_pruned_ctx`).
> - **S2** — entry-store instance `semantic_entry_store_ctx_analysis_sound`
>   (`TD_Side_Eff_Ctx_Sound.thy`); the value-dependent combine `unit_combine_tree_ctx
>   entry_store_ec`. *`flag_etf`-through-warrowing bonus is unstarted — same transport
>   class as interval-apinis.*
> - **S3** — `entry_store_context_precision_witness`
>   (`Example_Entry_Store_Context_Precision.thy`): strict precision over any
>   monovariant cover, machine-checked.
> - **S4** — future / out of scope (`solve_dom` assumed, as the whole pipeline does).

Plan to give Voblint **Goblint-style semantic (entry-state) context-sensitivity** —
procedure entries as side-effect sinks keyed by `c = enter#(abstract state)`, with
conditional routing allowed — by running the **warrowing side back-end**, accepting
**loss of the optimality (leastness) guarantee**. Grounded in
[[research/td-side-monotonicity-audit]]; this is "Path B / future-direction 1" of
[[research/trace-precision-direction]], reframed from *blocked* to *feasible*.

## The enabling architecture: shared eqsystem, two solver back-ends

The migration rests on a fact verified in the audit: `TD_side` and
`TD_side_upd_rule` consume the **same** `('x,'g,'d) eqsT`; they differ only in the
update rule (precise vs. warrowing) and a `warrowing` type-class constraint on `'d`.
The γ-soundness layer (`edge_collect_etf_sound`, `sound_effectful_transfer`) is
solver-agnostic.

```
        side_cfg_T_eff g etf bot s0 gseed         ← one equation system T
                       │
        sound_effectful_transfer  (γ-soundness, solver-independent)
              ┌────────┴───────────────────────────────┐
   warrowing back-end                          mono back-end
   TD_side_upd_rule.partial_post_solution      TD_side_mono.least_partial_post_solution
   SOUND always; terminates via widening;      OPTIMAL; needs threefold_mono T;
   no leastness (even under mono)              terminates only w/o widening (finite-height)
```

`threefold_mono T` is the conditional switch to the optimality back-end. Semantic
contexts break `mono_sides` (the entry side-effect target becomes value-dependent),
so they use the **warrowing back-end only**. Syntactic contexts (Path A, AD-33) keep
`threefold_mono` and may use *either* back-end. **The two paths share `T` and the
transfer-soundness layer** — this plan adds the warrowing back-end and the context
dimension without disturbing the existing mono/optimality result.

## Stages

### S0 — Warrowing back-end interface (domain-axis; no contexts yet)

New `TD_Side_Eff_Warrow_Interface.thy` paralleling `TD_Side_Eff_Interface.thy` (which
currently does `interpretation side: TD_side_mono`):

- interpret `TD_side_upd_rule` over the existing `side_cfg_T_eff g etf bot0 s0 gseed`;
- supply a concrete `update_rule` instance — a **global widening** `update_global` —
  discharging its four obligations (`init_rho_leq_bot`, `update_global_untouched`,
  `update_global_recorded_in_rho`, `update_global_preserves_rho_invariant`) and the
  `warrowing` type class on `'d`;
- lift `partial_post_solution` → `part_post_solution` at `cfg_exit` → feed the
  existing `edge_collect_etf_sound` / `post_fixpoint_sound_at_ip_eff` chain →
  `cfg_collect` soundness.

**Acceptance:** `side_analyse_warrow_sound` for sign + interval (interval now widened
properly); the mono interface and its `least_partial_post_solution` are untouched.
**Risk:** discharging the four `update_rule` obligations for a real widening; confirm
the interval domain instantiates `warrowing` (widening/narrowing already exist in the
domain layer). `solve_dom` stays an assumption.

### S1 — Context-indexed equation system (entries-as-sinks, abstract context)

Generalize the unknown to carry a context `'c` (analogous to the `'g`-generalization
already done in [[research/architecture-decisions]] AD-31/AD-32):

- unknown `(pp + 'g) × 'c`; `side_cfg_T_eff` / `make_side_rhs_tree_eff` thread `'c`;
- a **call edge** computes the callee context via a parameter
  `enter_ctx :: 'c ⇒ edge ⇒ 'c` and side-effects the callee entry `[start_g, c']`
  (encoding 1 in [[concepts/interprocedural-encodings]]); **combine** reads
  `[ret, c']`;
- keep `'c` and `enter_ctx` **abstract**; re-establish `sound_effectful_transfer` for
  the context-indexed `etf`, parametric in `'c`.

**Acceptance:** context-parametric `cfg_collect`-level soundness; `'c = unit` recovers
the current monovariant result (sanity check). **This is the proof bulk** — but it
reuses the decoupling architecture (AD-31) that already made the spine `'g`-polymorphic.
**Risk:** per-context **entry seeding** interacts with the `gseed` machinery (AD-32);
likely needs per-`c` seeding (the piece AD-32 left at `unit`).

> **Update (2026-07-01, AD-35): the entry-seeding risk is resolved.** The keyed
> context generator `side_cfg_T_eff_cmp` (`TD_Side_Eff_Cmp_Gen.thy`) filters
> `EA_Enter` out of the intra predecessor fold (`non_enter_predecessor_list`) and
> seeds a context-independent **fresh local frame** at frame-entry nodes; callee-entry
> globals come only from the `combine` edge. Soundness is re-established through a new
> transfer contract `sound_effectful_transfer_framed` (the enter *upper* bound
> `etf_full (etf_enter etf u) σ ≤ fresh_frame ⊔ glob_env σ`), with
> `side_cfg_T_eff_cmp_collect_sound` case-splitting enter/non-enter. This realises the
> S1 context-indexed system on the **monotone** back-end for the finite-context special
> case (Path A). The Path-B warrowing route stays the target for value-dependent
> `enter#`. See `docs/KEYED_CONTEXT_ENTER_FRAMED_MIGRATION.md` and
> `docs/GLOBAL_CONTEXT_REDESIGN.md`.

### S2 — Semantic (entry-state) context instance

- instantiate `'c =` abstract entry state (or a projection); `enter_ctx =` the `enter#`;
- prove `sound_effectful_transfer` for this instance (mono-free → goes through);
- **do not** prove `threefold_mono` (false here — `flag_etf`); route via the **S0
  warrowing back-end** only;
- compose S0 + S1 + S2 → `semantic_ctx_analysis_sound` (sign), `solve_dom` assumed.

**Bonus:** the previously-`oops` `flag_etf` conditional routing becomes a *real*
through-(warrowing-)solver result — capture it as a witness that semantic routing is
now expressible.

### S3 — Precision payoff witness

Mirror `digest_beats_flat`: a program with calls where the entry-state-context
analysis is **strictly more precise** than the context-insensitive read.
**Acceptance:** `semantic_ctx_strictly_more_precise`, machine-checked. Without this
the contribution is "sound context-sensitivity" with no demonstrated benefit.

> **Partial witness already on `main` (2026-07-01, AD-35).** For a *finite* context
> type, `Example_Finite_Sign_Context_Analysis.thy` proves by `eval` that the keyed
> context analysis separates two activations of `f() { GH := G }` — `GZero`-context
> slot `GH = SZero`, `GPos`-context slot `GH = SPos`, join-all `SNonNeg` — where the
> context-insensitive read collapses to `SNonNeg`. This is the finite-context (Path A)
> analogue of the S3 payoff; the semantic entry-state (Path B)
> `semantic_ctx_strictly_more_precise` is still the target.

### S4 — Termination / runnability (scoped)

> **Detail doc:** `EXECUTABLE_CONTEXT_MIGRATION.md` — the generator-driven
> executable path (E0–E4). Viability already proven (`Exec_Sign_Ctx_Run`,
> `Exec_Ivl_Ctx_Run`); the headline is E2, a generator-driven precision witness
> over a compiled CFG.

The soundness claim assumes `solve_dom` (as the whole pipeline does today). For a
*runnable* (`value`/code-gen) result the context set must be finite — full
entry-state contexts can be infinite, so this needs a context bound (Context Gas),
which drifts toward Path A. **Decision:** thesis claim = soundness with `solve_dom`
assumed; runnable + a real `solve_dom` proof for the warrowing side solver = future
work on the [[people/grass|Graß]]/Tilscher solver axis.

## Dependencies & effort

```
S0 ──▶ S1 ──▶ S2 ──▶ S3
                └────▶ S4 (future)
```

| Stage | Axis | Size | Note |
| --- | --- | --- | --- |
| S0 warrowing interface | domain | moderate | locale instantiation + 4 obligations |
| S1 context dimension | domain | **large** | the bulk; analogous to AD-31 `'g`-generalization |
| S2 semantic instance | domain | moderate | instance + compose; `flag_etf` bonus |
| S3 precision witness | domain | small | one program, mirror `digest_beats_flat` |
| S4 termination/runnable | **solver** | open | `solve_dom`; Graß/Tilscher; future |

## What is given up, and what is kept

- **Given up:** optimality (leastness) for the semantic-context instances —
  `least_partial_post_solution` provably needs `mono_sides`.
- **Kept:** soundness (via the warrowing back-end); the existing mono/optimality
  result for syntactic-context and finite-height systems (S0 leaves it untouched);
  the entire transfer-soundness layer and equation-system construction.
- **Unchanged risk:** `solve_dom` (termination) stays assumed — the same standing
  hypothesis as today, not a new blocker.

## Open questions / coordinate with supervisor

- Confirm the `update_rule` obligations are dischargeable for the chosen global
  widening (S0).
- Per-context entry seeding off the `gseed = unit` default (S1; AD-32 Level B).
- `solve_dom` for the warrowing side solver — is a terminating result on the
  Graß/Tilscher roadmap, or genuinely future? (See the Slack draft,
  `output/reports/slack-alexandra-td-side-mono.md`.)

## See Also

- `docs/TRACE_CONTEXT_BRIDGE_MIGRATION.md` — semantic middle layer (`alpha_ctx`,
  `cfg_collect_ctx`, optional `lfp(trace)`); target `context_analysis_sound`
- [[research/td-side-monotonicity-audit]] — the vendor/locale evidence this plan rests on
- [[research/trace-precision-direction]] — Path A vs B; the `mono_sides` wall
- [[concepts/interprocedural-encodings]] — the encoding-1 (entries-as-sinks) target
- [[research/architecture-decisions]] — AD-33 (scope), AD-31/AD-32 (the `'g` decoupling reused in S1)
- [[concepts/digests]] — `digest_beats_flat`, the precision-witness template for S3
