# Handoff — Unified Analysis Migration (post–Seidl pivot)

Pick-up doc for **consolidating parallel analysis stacks** built during the
[[Seidl trace migration](SEIDL_TRACE_MIGRATION_HANDOFF.md)] on branch `trace-spike`.
Read this before starting **M4** (digests / trace-combine) or merging to `main`.

KB companion:

- `~/git/voblint-formalization-kb/wiki/research/unified-analysis-migration-plan.md`
- `~/git/voblint-formalization-kb/wiki/research/seidl-pivot-migration-plan.md` — parent pivot (M0–M4)
- `docs/SEIDL_TRACE_MIGRATION_HANDOFF.md` — Seidl execution status (M1 done 2026-06-07)

> **Status (2026-06-07):** planned, **not started**. Seidl pivot slices M0–M3 + M1
> are green on `trace-spike`; this migration is the recommended **next structural
> step** before M4 or a large merge.

> **Status update (2026-06-09) — U1–U4 done, green.** Executed on `trace-spike`,
> full `isabelle build` sorry-free:
>
> - **U1** — `src/CFG/Collecting/CFG_Collect_Unified.thy`: `collecting` locale
>   parameterised by a `combine_at` hook; `F`/`collect` lfp skeleton (mono,
>   unfold, post, entry, `collect_lowerbound`, per-edge step) proved once.
>   `intra` (`combine_at = {}`) and `ip` (`collect_combine_pp`) interpretations
>   recover `cfg_collect` / `cfg_collect_ip` via `intra_collect_eq` /
>   `ip_collect_eq`.
> - **U2** — `src/Equations/Analysis_Sound.thy`: `collect_post_fixpoint_sound`
>   (the lfp→gamma engine, in the locale) + `unified_post_fixpoint_sound[_ip]`
>   (in `sound_domain`) re-derive intra/IP soundness through the single engine.
>   A new `combine_at` (M4 digests) gets soundness the same way.
> - **U3** — `Sign_Domain.thy` `sign_tf_sound_{assign,assume,assume_not,enter}`
>   bundle; `Example_Proc_Global` cites it instead of re-proving `h1`–`h4`.
> - **U4** — `src/Pipeline/Trace_IP_Analysis_Sound.thy` `trace_ip_analysis_sound`:
>   `alpha_last (cfg_collect_trace_ip g S v) \<le> gamma_state (env v)`, composing
>   M3.5's projection with U2's IP soundness. `alpha_last` is the
>   soundness-preserving morphism — the M4 extension point.
>
> U0 (audit) folded into U1/U2 design (the duplication was the shared `lfp(F)`
> skeleton + the `gamma`-post-fixpoint finish, both now factored). M4 (digests)
> is the remaining open frontier; its locale extension point is proved (U4).

---

## 1. Problem in one paragraph

The Seidl pivot was executed **additively** (new theory per slice, spine stays
green). That delivered capabilities quickly but left **parallel vertical stacks**:
intra vs interprocedural vs side-effecting vs trace soundness each re-prove
reach bridging, post-fixpoint soundness, and domain corollaries. M4 on the same
pattern would add a fifth stack. This migration **parameterizes one chain** and
makes examples thin `[interpretation]` corollaries — without deleting the vendored
solver proofs or domain instances.

---

## 2. Duplication inventory (current `trace-spike`)

| Layer | Intra | IP (M1) | Side (M3) | Trace (M0/M2) |
| --- | --- | --- | --- | --- |
| Collecting | `cfg_collect` | `cfg_collect_ip` | (uses intra) | `cfg_collect_trace` |
| Post-fixpoint | `is_post_fixpoint` | `is_post_fixpoint_ip` | side variant | via `alpha_last` |
| RHS / tree | `make_rhs_tree` | `make_rhs_tree_ip` | `side_cfg_T` | projection lemmas |
| Soundness | `TD_Soundness` | `TD_IP_Soundness` | `TD_Side_Soundness` | `Trace_Soundness` |
| Examples | `Example_Sign_*` | `Example_Proc_Global` | `Example_Side_Global` | `Example_Trace_*` |

**Not duplicated (keep as shared core):**

- `Domains/` — one `domain_transfer`, sign/interval instances
- Vendored `TD` / `TD_side` — algorithm correctness stays external
- `edge_collect`, `cfg_path`, `combine_states`, `compile` / `compile_prog`
- `lift` / `alpha_last` — trace is an overlay on paths, not a third semantics

**Genuinely different shapes (two backends, not five):**

1. **Plain TD** (`TD_plain`) — unary edge RHS; IP combine is a **tree encoding** on
   top of this, not a third solver.
2. **Side TD** (`TD_side`) — `'l + 'g` unknowns + `Side` nodes for flow-insensitive
   globals (M3 axis).

Consolidation target: **one soundness locale**, two solver interpretations, collecting
and tree hooks as locale parameters.

---

## 3. Target architecture

### 3.1 Collecting locale

```isabelle
locale collecting =
  fixes g :: cfg
  fixes step :: "store set => edge_action => store set"   (* or path step *)
  fixes combine_at :: "pp => store set => store set"     (* identity for intra *)
  defines collect :: "store set => pp => store set"
  ...
```

Interpretations:

| Name | `step` | `combine_at` | Recovers |
| --- | --- | --- | --- |
| `collecting_intra` | `edge_collect` | `{}` / skip | `cfg_collect` |
| `collecting_ip` | enter + edge | `combine_states` at triples | `cfg_collect_ip` |
| `collecting_trace` | `edges_trace` / trace set | (later: digest hook) | `cfg_collect_trace` |

Prove **once**: lfp characterisation, path lower bound, adequacy scheme
(`runs_to` / `pruns_to_ip` => membership).

### 3.2 Constraint + soundness locale

```isabelle
locale analysis_sound =
  fixes collect :: "store set => pp => store set"
  fixes make_tree :: "pp => strategy_tree"
  fixes reach_lemma :: ...
  assumes post_fp: "is_post_fixpoint ..."
  ...
  shows "cfg_collect ... v <= gamma (env v)"   (* schematic *)
```

Thin corollaries:

- `TD_Soundness` = `[interpretation collecting_intra + plain_td]`
- `TD_IP_Soundness` = same + IP tree / `is_post_fixpoint_ip` as instance
- `TD_Side_Soundness` = `[interpretation collecting_intra + side_td]`
- `Trace_Soundness` = collecting_trace + `alpha_last` + pipeline locale

### 3.3 Examples

One schema `domain_analysis_sound` with locale parameters; each `Example_*` discharges
only: program AST, `compile_*` facts, reach/discharge lemmas, `td_solve_dom`.

**Anti-pattern:** copying `h1`–`h4` assign/assume/enter proofs per example.

---

## 4. Migration slices

### Slice U0 — audit (no proof changes)

- Map every `post_fixpoint_sound*` / `*_collect_sound*` / `make_rhs_tree*` lemma to
  the generic statement it should become.
- Mark which lemmas differ only by `unfolding` vs genuinely new math (IP combine,
  `Side` global slot).
- Output: table in this doc or KB; drives slice order.

**Exit:** inventory signed off; no duplicate work listed twice.

### Slice U1 — collecting parameterization

- Introduce `CFG_Collect_Unified.thy` (or extend `CFG_Collecting_Core`) with locale
  above.
- Prove `collecting_intra` and `collecting_ip` interpretations recover existing defs
  (`cfg_collect`, `cfg_collect_ip`) by reflexivity lemmas — **do not delete** old
  names until recovery lemmas green.
- Adequacy: generalize `pruns_to_ipD`-shaped lemmas from IP instance.

**Exit:** one adequacy theorem family; `CFG_Collect_IP_Adeq` shrinks to instance.

### Slice U2 — soundness parameterization

- Introduce `Analysis_Sound.thy` (or locale block in `Constraint_System_Sound.thy`)
  with parameterized `post_fixpoint_sound_at`.
- Refactor `TD_Soundness`, `TD_IP_Soundness`, `TD_Side_Soundness` to
  `[interpretation]` + one-line corollaries.
- Keep `TD_CFG_Core`, `TD_CFG_IP_Core`, `TD_Side_CFG` as **tree builders** only.

**Exit:** batch green; old theorem names exported as aliases for pipeline/examples.

### Slice U3 — example consolidation

- Extract shared `sign_transfer_sound_lemmas` (the repeated `h1`–`h4` blocks).
- Rewrite `Example_Proc_Global`, `Example_Side_Global`, `Example_Sign_Analysis` as
  thin wrappers.

**Exit:** no example theory duplicates transfer-function soundness proofs.

### Slice U4 — trace overlay (prep for M4)

- State `collecting_trace` interpretation + `alpha_last` as locale morphism
  ("projection preserves soundness").
- Document extension point for digest-indexed `combine_at` — **do not implement M4
  here**.

**Exit:** M4 handoff can extend locales instead of forking new `.thy` stacks.

---

## 5. Milestone checklist

| Milestone | Status | Notes |
| --- | --- | --- |
| **U0** — duplication audit | **Done** | folded into U1/U2 design |
| **U1** — collecting locale | **Done** | `CFG_Collect_Unified.thy`; intra + IP |
| **U2** — soundness locale | **Done** | `Analysis_Sound.thy`; intra/IP via one engine |
| **U3** — thin examples | **Done** | `sign_tf_sound_*` bundle; `Example_Proc_Global` thinned |
| **U4** — trace overlay | **Done** | `Trace_IP_Analysis_Sound.thy`; `trace_ip_analysis_sound` |

**Gate before M4 met:** U1–U4 green (collecting + soundness unified, trace overlay
morphism proved). M4 (digests) extends `combine_at` on the unified locale.

---

## 6. Sequencing relative to Seidl pivot

```
Seidl M0–M3 + M1 (done on trace-spike)
        |
        v
  THIS MIGRATION (U0–U4)  <-- you are here
        |
        +--> merge trace-spike -> main (can overlap U1–U2)
        |
        v
Seidl M4 (digests / trace-combine) on unified locales
```

Do **not** start M4 feature proofs until U1/U2 at least are planned — otherwise
M4 will cement a fifth parallel stack.

---

## 7. Constraints — what NOT to do

| Don't | Why |
| --- | --- |
| Merge Seidl + unification in one PR | Review and rollback become impossible |
| Delete old theorem names immediately | Pipeline and examples break silently |
| Re-prove vendored TD / TD_side | AD-13; bridge only |
| Unify plain TD and TD_side into one solver | Different `'x` unknown shapes; two backends stay |
| Start M4 digests before U2 | Duplication becomes permanent |
| Destructive spine rewrite of `cfg_collect` | Use interpretation + recovery lemmas |

---

## 8. Build gate

Same as Seidl handoff §5:

```bash
isabelle build -v -d ~/afp/thys -d vendor/td-verification -D . Voblint_Formalization
```

Each slice exits sorry-free with **no regression** in existing example theorems
(even if proofs move behind locale interpretations).

---

## 9. Likely file touch list

```
src/CFG/Collecting/CFG_Collect_Unified.thy   -- new (locale + interpretations)
src/Equations/Analysis_Sound.thy              -- new (parameterized soundness)
src/Equations/Constraint_System_Sound.thy     -- shrink / re-export
src/Solver/TD_Soundness.thy                   -- corollaries only
src/Solver/TD_IP_Soundness.thy                -- corollaries only
src/Solver/TD_Side_Soundness.thy              -- corollaries only
src/Pipeline/Pipeline.thy                     -- use generic locale
src/Examples/Example_*.thy                    -- thin wrappers (U3)
docs/SEIDL_TRACE_MIGRATION_HANDOFF.md         -- cross-link (done)
```

---

## 10. First action

Run **Slice U0**: grep-driven inventory of `post_fixpoint`, `make_rhs_tree`,
`cfg_collect`, `*_sound_at` theorem statements; paste into KB page
`unified-analysis-migration-plan.md` §inventory. Then pick U1 vs merge-to-main
based on whether `trace-spike` lands on `main` first.
