# Track Plan — 2026-05-27

Two parallel tracks. Track A = internal polish, in-budget. Track B = Seidl
scope expansion, gated on meeting 4 (placeholder 2026-06-01).

Source analysis:

- `docs/NEXT_STEPS.md`, `docs/ROADMAP.md`, `docs/OPEN_PROBLEMS.md`.
- KB: `wiki/research/seidl-scope-feedback.md`,
  `wiki/research/procedures-extension-feasibility.md`,
  `wiki/meetings/2026-06-01-meeting4-prep.md`.

---

## Track A — Internal polish (drop TD assumptions, write thesis)

Goal: ≤1 explicit TD hypothesis on top-level theorems; thesis chapters from
walkthrough.

| # | Task | Where | Effort | Issue | Status |
| --- | --- | --- | --- | --- | --- |
| A1 | Discharge **P3** `comp_fun_idem (ac_join cfg)` from `sound_domain` join laws | `Domains/Abstract_Domain.thy` — new lemma `join_state_comp_fun_idem`; drop `cfi` / `join_cfi` in `Pipeline.thy`, `Goblint_Formalization.thy` | 1–2 sessions | #7 | ✅ done 2026-05-27 (commit `1c119d3`) |
| A2 | Discharge **P2** `td_cfg_in_reach` | Fix B (per-pp `td_analyse`, `td_analyse_collect_sound_at`) | done 2026-06-01 | #8 | ✅ closed |
| A3 | Thesis prose — sign + interval chapters | `docs/walkthrough/` → thesis PDF | parallel | #17 | ongoing |
| A4 | Executability — full `run_analysis` map | `Examples/`, `code_datatype`/`code_unfold` pragmas | optional | #16 | defer |
| A5 | Session split core vs stretch | `ROOT`, import refactor (`TD_Soundness` / `Pipeline`) | optional | #13 | defer |

Defer indefinitely:

- **#14** (total correctness, P1 finite `pp`). Partial correctness with
  explicit `solve_dom` is defensible.
- Octagon track (#25, #15, #19). Scope B only.

Exit criterion: `goblint_sign_sound` / `goblint_interval_sound` carry only
`solve_dom` as TD hypothesis; thesis chapters drafted.

---

## Track B — Seidl scope expansion (procedures / side-effects)

Triggered by Seidl email 2026-05-26: *"warum keine Prozeduren? warum keine
Seiten-Effekte? Ohne das kommt mir dieses Thema ein wenig sehr main-stream
vor"*.

Layered. Each layer independently shippable. Sits on top of Track A
soundness chain.

| # | Layer | Change | Effort | Risk | Gate |
| --- | --- | --- | --- | --- | --- |
| B1 | **L1** structural unknown split | `Constraint_System.thy` unknowns `pp` → `'l + 'g`; default `'g = unit` for sign/interval; touches `Constraint_System_Sound.thy`, `TD_CFG_Core.thy`, `Pipeline.thy` (types only) | 1–2 sessions | none — soundness shape unchanged | — adopt unconditionally |
| B2 | **Approach A** procedures (no params, unified store) | Add `Call pname` to `com`; `type pname = string`; parameterise small-step by `π :: pname ⇒ com option`; `compile_program` two-pass with Nop call/return edges; thread `π` through `Pipeline.thy` | ~2 weeks | low — `Constraint_System` untouched; boring without recursion | meeting 4 verdict |
| B3 | **L3a** side-effecting eqsys (vendored TD) | Bridge target is `TD_side` (or `TD_side_unopt` fixing `destab`) in `vendor/td-verification/TD_side.thy` (246KB). Import `Basics_side` strategy_tree (`Answer` / `QueryL` / `QueryG` / `Side`). σ is bipartite `'x + 'g ⇒ 'd`. Domains need `'d :: bounded_semilattice_sup_bot` (stronger than current `bot + equal`). New `rhs_tree_fold_side`. Bridge `post_fixpoint_sound_side` from `TD_side` correctness to collecting inclusion. | ~6–8 weeks | medium — locale richer than `TD_plain`; not a parameter-rename refactor | meeting 4 Q1, Q3 |
| B4 | **Approach C** procs + globals + enter/combine | Combine B2+B3 with store split `(local, global)`; `enter` strips locals; `combine` propagates globals; procedure entries become globals (Seidl-Apinis-Vojdani 2014 encoding) | ~10–12 weeks | high — likely overruns thesis | reject default |

Reject:

- **L3b** (re-prove side-effecting TD). Duplicates Graß/Tilscher coauthored
  NASA FM 2026 work.
- **L4** (digests, demand, sync, multi-analysis Var2, threads, heap). Cite
  only.

### B3 gating questions (meeting 4)

1. Is Tilscher–Graß–Schwarz–Seidl NASA FM 2026 Isabelle artifact public /
   vendorable?
2. Which gap rows does it cover (Paper §2 minimum vs full
   `DemandGlobConstrSys`)?
3. Same `strategy_tree` shape as AFP `Top_Down_Solver` (extended with
   `Side`), or divergent?

### B0 finding (2026-05-27) — corrects KB

`TD_plain_s.thy` is **not** the side-effecting solver. The `_s` suffix means
"simple stable" (variant of stability tracking); it imports `Basics` (plain
`('x, 'd) strategy_tree`, no `Side`). The KB note in
`wiki/research/procedures-extension-feasibility.md` claiming
"`TD_plain_s.thy` is the simpler side-effecting variant" is **wrong**.

| Solver | Imports | tree | Locale fixes | Side? |
| --- | --- | --- | --- | --- |
| `TD_plain` | `Basics` | `('x, 'd)` Answer/Query | `T` | no |
| `TD_plain_s` | `Basics` | `('x, 'd)` Answer/Query | `T` | **no** |
| `TD_side` (246KB) | `Basics_side` + `Destabilization_side` | `('x, 'g, 'd)` Answer/QueryL/QueryG/Side | `destab`, `abort`, `T`; σ bipartite; `'d :: bounded_semilattice_sup_bot`; `destab_removes` | yes |
| `TD_side_unopt` | — | — | `TD_side` instantiated with `λx i s c. destab x i s` | yes |

Consequence: B3 has **no minimal swap point** in `TD_Interface.thy`. Real
work = new bridge locale matching `TD_side`'s signature, stronger class on
`'d`, new `make_rhs_tree_side`. Effort estimate ~6–8 weeks still plausible;
the "drop-in swap" framing is gone.

Post-meeting 4: patch `wiki/research/procedures-extension-feasibility.md`
§"Key discovery" and §"Concrete next step".

---

## Order of operations

1. **A1** (P3 packaging) — ✅ done 2026-05-27 (commit `1c119d3`).
2. **A2** (P2 reachability) — ⚠️ structural finding 2026-05-27.
   `td_cfg_in_reach` unconditionally false for forward-equation CFGs.
   See `OPEN_PROBLEMS.md` §"P2 finding". Surfaced for meeting 4. No
   code change pending until supervisor verdict.
3. **B3 pre-check** (vendor `TD_plain_s` interface grep) — gates B3
   feasibility, zero cost.
4. **B1** (structural unknown split) — cheap, unconditional adopt before
   meeting 4 so the "shape matches `GlobConstrSys`" framing is concrete.
5. Meeting 4 verdict → A3 (write up), A2 repair direction (Fix A/B),
   and Track B scope decided together. P2 fix and B3 may merge.

---

## See also

- `docs/NEXT_STEPS.md` — week plan (now superseded for week 1 by this file)
- `docs/OPEN_PROBLEMS.md` — P1–P10 catalogue
- `wiki/research/seidl-scope-feedback.md` — full L0–L4 ladder
- `wiki/research/procedures-extension-feasibility.md` — change sets, effort
- `wiki/meetings/2026-06-01-meeting4-prep.md` §6 — supervisor agenda
