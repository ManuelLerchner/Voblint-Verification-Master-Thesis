# Collecting-Semantics Unification Plan (migration decision)

Status: decision document, no code changed. Verified against `src/` at branch
`local-trace-semantic`. A large proof migration is assumed acceptable; the
objective is **minimum final conceptual and proof complexity**, not minimum diff.

Companion: `docs/COLLECTING_SEMANTICS_ARCHITECTURE.md` (the review that
established the current structure). This document is the actionable plan.

---

## Decision (read this first)

**Adopt `valid_ltr` as the single canonical execution witness. Generalize the
context reader to `ctx_of :: ltr ⇒ 'c`. Collapse every collector to one generic
projection and every soundness spine to one backbone. Keep `cfg_collect` as the
*derived plain projection*, not as a second foundation.**

Retire: `trace_witness`, `cfg_collect_trace`, `trace_witness_ctx`,
`cfg_collect_ctx` (flat), and the `Ctx_Collect_Backbone` induction.
Keep and re-root: `cfg_collect` (as the no-context projection),
`cfg_collect_ctx_act` (as the activation instance), `valid_ltr`, the source
bridge, the interval flagship.

This meets the simplification threshold in §8: two trace inductives → one, two
context backbones → one, three context collectors → one generic projection with
thin corollaries. Recommended.

---

## 1. Required semantic information (the essence)

What the current proofs genuinely consume, separated from representation
accidents:

| Needed by some proof | Where it shows up | Carried by |
|---|---|---|
| CFG node reached | every collector's `node_of` | `sink_node` |
| store reached | every collector's `store_of` | `sink_store` |
| intra edge transfer | `EDGE`/`intra` obligations | `extend` step |
| call entry | `SEED`/`call` obligations | `Call` / `EA_Enter` |
| return / combine | `COMB`/`ret` obligations | `Resume` / `combines` |
| caller/callee structure | activation identity, source stack | `Call`/`Resume` subtrees |
| activation identity | `key`, source `stack_repr` | `caller_of` chain |
| complete execution order | digest `dg`, precision examples | the `path` + subtrees (linearizable) |
| history for `dg` | digest DG read soundness | flattening of the witness |
| source-stack correspondence | `Located_LTR` bridge | `stack_repr`, `concrete_program_match` |
| executable DG soundness | `twice_ctx_collect_ctx_act_sound` | collector cap, domain-side |

**Verdict:** every item is present in, or a projection of, `valid_ltr`. The flat
`trace_witness` carries a *strict subset* (loses caller/callee structure and
activation identity). `cfg_witness` carries a further subset (store reaching
only). Nothing needs information that `valid_ltr` lacks.

Representation accidents to drop: the flat store-list encoding of calls
(`tau @ tl rho @ [r]` splice in `trace_witness.combine`), and the separate
store-only `cfg_witness` inductive.

---

## 2. Canonical witness

Keep the existing `valid_ltr` / `ltr` unchanged — it is already the canonical
witness. No new datatype (a new type would be the rejected "fourth layer").

```text
datatype ltr = Root path | Call ltr path | Resume ltr ltr path     -- CFG_Local_Trace.thy:46
inductive_set valid_ltr :: "cfg ⇒ store set ⇒ ltr set"             -- :73
  start:  Root [(cfg_entry g, s)]                 for s ∈ S
  intra:  extend t (v, s')                        for an ordinary edge
  call:   Call caller [(fe, se)]                  for an EA_Enter + matching combine
  ret:    Resume caller callee (path caller @ [(v, r)])   for combine_collect
```

Two projections must be **added** (both are new, small, and independently
useful):

```text
flatten :: ltr ⇒ trace        -- linearize to the flat store list
  flatten (Root p)          = map snd p
  flatten (Call c p)        = flatten c @ map snd p        -- (exact splice TBD to match trace_witness.combine)
  flatten (Resume c d p)    = flatten c @ tl (flatten d) @ [last store]   -- mirrors the combine rule

adequacy:  t ∈ valid_ltr g S ⟹ trace_witness g S (sink_node t) (flatten t)
```

`flatten` is the bridge that lets any flat digest `dg :: trace ⇒ 'c` run on the
canonical witness as `dg ∘ flatten`, with **no loss of digest generality**.

---

## 3. Generic collector API

One scheme replaces all four public collectors:

```text
definition collect_by ::
  "'w set ⇒ ('w ⇒ pp) ⇒ ('w ⇒ store) ⇒ ('w ⇒ 'c) ⇒ pp ⇒ 'c ⇒ store set"
where
  "collect_by W node_of store_of ctx_of v c =
     {store_of w | w. w ∈ W ∧ node_of w = v ∧ ctx_of w = c}"
```

`cfg_collect_ctx_act` is *already exactly this shape* (`CFG_Local_Trace.thy:627`)
— it is `collect_by (valid_ltr g S) sink_node sink_store (key enterc seedc)`.

Context policy becomes a **parameter** (`ctx_of`), instantiated three ways:

| View | `ctx_of` | Result |
|---|---|---|
| plain collecting | `(λ_. ())` (trivial context) | `= cfg_collect` (after the reverse-inclusion lemma, §4) |
| digest-keyed | `λt. dg (flatten t)`, filtered by `cmp` | replaces `cfg_collect_ctx` with full `dg` generality |
| activation-keyed | `key enterc seedc` | `= cfg_collect_ctx_act` (unchanged) |

Digest `cmp`-compatibility (currently `alpha_ctx dg cmp`, `CFG_Collect_Trace.thy:499`)
is expressed as a set-comprehension side condition on `ctx_of`, or by taking
`ctx_of` into a quotient — either way it stays parametric.

**Constants that change status:**

- `cfg_collect_ctx_act` → abbreviation over `collect_by`.
- `cfg_collect_ctx` → abbreviation over `collect_by` with `ctx_of = dg ∘ flatten`.
- `cfg_collect_trace`, `trace_witness`, `trace_witness_ctx`, `alpha_ctx`,
  `cfg_witness`, `cfg_collect_paths` → **retired**.
- `cfg_collect` → kept, re-characterized as `collect_by … (λ_. ())` union over
  nodes (see §4).

---

## 4. `cfg_collect`: canonical, derived, or retired?

New evidence corrects the earlier "only inclusions" reading:

- `cfg_collect = cfg_collect_paths` is an **equality**, proved by antisymmetry
  (`cfg_collect_eq_paths`, `CFG_Collect.thy:392/394`).
- `cfg_collect_paths g S v = {s. cfg_witness g S v s}` (`:277`) — a store-level
  reaching witness.

So `cfg_collect` is *already* a witness collection, just over the weakest witness
(`cfg_witness`, store-only). Its lfp form is an equivalent presentation, not an
irreducible primitive.

**Missing direction for full unification:** we have
`valid_ltr_sink_in_cfg_collect` (`:507`), i.e.
`sink_store '' valid_ltr ⊆ cfg_collect` (per node). The reverse —
*every* `cfg_collect` store is the sink of some `valid_ltr` — is unproved. It is
the `valid_ltr`-completeness statement, and it is almost certainly **true**
(mirrors the existing `cfg_witness`/`trace_witness` completeness arguments) but
requires an induction lifting a store-reaching witness to a full activation tree.

**Decision:** do **not** put this on the critical path.

- Keep `cfg_collect` with its current definition and the existing `⊆` bridge.
- Add the reverse-inclusion lemma `cfg_collect_subset_ltr_sink` as an *optional*
  follow-up; once proved, `cfg_collect = collect_by (valid_ltr) … (λ_. ())`
  (unioned over contexts) and `cfg_collect` becomes a formal abbreviation.
- Rationale: `cfg_collect` is consumed by 46 files across the domain/eqsys layer
  that never touch traces. Forcing its retirement couples an easy trace refactor
  to a hard denotational-completeness proof for zero client benefit. Keep it as
  the stable plain-projection endpoint; make it *provably derived* only as a
  clean-up epilogue.

---

## 5. Unified proof backbone

Today there are **two parallel inductions proving the same theorem**:

| Current backbone | Trace type | Statement |
|---|---|---|
| `ctx_collect_backbone` (`Ctx_Collect_Backbone.thy:123`) | flat `trace_witness` | `cfg_collect_ctx dg cmp g S v c ⊆ M (v,c)` |
| `valid_ltr_ctx_sound` (`Activation_Local_Sound.thy:151`) → `activation_collect_sound` (`Activation_Backbone.thy:40`) | `valid_ltr` | `cfg_collect_ctx_act enterc seedc g S v c ⊆ ⟦sg (Inl (v,c))⟧` |

Both are 4-case inductions (entry/edge/enter/combine ≈ start/intra/call/ret) with
the same ENTRY/EDGE/SEED/COMB transfer obligations. **One replaces both.**

Target backbone (schematic in the context reader):

```text
theorem collect_by_sound:
  fixes ctx_of :: "ltr ⇒ 'c" and M :: "pp × 'c ⇒ 'a::sound_domain abs_state"
  assumes step_ctx: <how ctx_of evolves along start/intra/call/ret>   -- context-policy law
    and ENTRY: <seed covers start at ctx_of Root>
    and EDGE:  <intra edge preserves cover>
    and SEED:  <call lands entering store at ctx_of Call>
    and COMB:  <combine reassembles into ctx_of Resume>
  shows "collect_by (valid_ltr g S) sink_node sink_store ctx_of v c ⊆ ⟦M (v,c)⟧"
```

Then the three current headline results are **corollaries by instantiation**:

- activation: `ctx_of = key enterc seedc`, `step_ctx` = the `key` recursion →
  reproduces `activation_collect_sound` verbatim.
- digest DG: `ctx_of = dg ∘ flatten` (with `cmp`), `step_ctx` = the digest's
  incremental law → reproduces `ctx_collect_backbone`; the DG read lemmas
  (`Clean_RRead_Sound`, `Digest_Global_Read`, `Value_Digest_Reader`,
  `TD_Side_Eff_Cmp_*`) are **already schematic in `dg`/`cmp`** and transfer
  unchanged.
- plain: `ctx_of = (λ_. ())` → `⊆ cfg_collect` soundness.

The one nontrivial hypothesis is `step_ctx` — the "context evolves lawfully along
the four `valid_ltr` constructors" law. For `key` it is the definitional
recursion (`:110`); for `dg ∘ flatten` it is the flat digest's existing
incremental step re-expressed along `flatten`. **This is the load-bearing proof
obligation of the whole migration** (see risks, §7).

---

## 6. End-to-end path (must survive)

The source chain is unchanged in shape; only the middle constant is generalized:

```text
IMP2 pstep run
  → source_run_has_ltr / stack_repr        (Located_LTR.thy, UNCHANGED)
  → t ∈ valid_ltr                          (UNCHANGED)
  → collect_by (…) (key enterc seedc)      (was cfg_collect_ctx_act, now its abbreviation)
  → collecting cap (twice_ctx_collect_ctx_act_sound)   (UNCHANGED)
  → abstract source-store bound            (source_sound_from_collecting_cap, UNCHANGED)
```

- `source_store_in_cfg_collect_ctx_act` / `source_toplevel_in_cfg_collect_ctx_act`
  (`Located_LTR.thy:235/283`) keep their statements — `cfg_collect_ctx_act`
  survives as an abbreviation, so the public source theorems and the `twice`
  flagship (`Example_Interval_Source_Ctx.thy`) need **no restatement**.
- Source-stack simulation is defined against `valid_ltr` already; it is untouched
  by retiring the flat trace world.
- The recursive `twice` example migrates for free: its cap
  (`twice_ctx_collect_ctx_act_sound`) is stated over `cfg_collect_ctx_act`, now an
  abbreviation of `collect_by`.
- The final source theorem still exposes only `(v, s, stk)` and an abstract
  bound — no `ltr` internals leak.

---

## 7. Two target designs compared

### Design A — `valid_ltr` canonical (recommended)

`valid_ltr` stays the witness; add `flatten`; generalize `ctx_of` to `ltr ⇒ 'c`;
one `collect_by`; one `collect_by_sound`; `cfg_collect` kept as derived plain
projection.

| Metric | Outcome |
|---|---|
| Final semantic concepts | **2 witnesses → 1** (`valid_ltr`); plus `cfg_collect` as a projection endpoint |
| Collectors | 3 → **1 generic** + 3 abbreviations |
| Backbones | 2 → **1** |
| Definitions removed | `trace_witness`, `cfg_collect_trace`, `trace_witness_ctx`, `alpha_ctx`, `cfg_witness`, `cfg_collect_paths` |
| Theories retired/gutted | `CFG_Collect_Trace.thy` (most of it), `Ctx_Collect_Backbone.thy` (folded) |
| Theorems unified | `ctx_collect_backbone` ≡ `activation_collect_sound` ← `collect_by_sound` |
| Hard obligation | `step_ctx` for `dg ∘ flatten`; `flatten` adequacy |
| Executable impact | none — solver/domain side untouched |
| Source-simulation impact | none — already on `valid_ltr` |
| Risk of *adding* complexity | **low** — no new type, richer object already exists |

### Design B — new canonical event trace

Introduce a fresh event sequence (call/return events + stores) and derive both
`trace_witness` and `valid_ltr` from it.

| Metric | Outcome |
|---|---|
| Final semantic concepts | **3** during migration (old two + new), target 1 |
| Definitions removed | eventually the old two, but only after two adequacy proofs |
| Hard obligation | **two** encodings (event→flat, event→ltr) + two adequacy proofs, plus re-proving `key` and `dg` over events |
| Risk of adding complexity | **high** — this is precisely the "fourth layer" the threshold forbids until the old ones are gone; the linearization/relinking proofs are new and large |
| Upside over A | only if a future feature needs an execution order that `ltr` cannot linearize — no current proof does |

**Design B is rejected.** `valid_ltr` already subsumes the flat trace by
`flatten`; a new event type buys nothing today and adds a migration hop.

---

## 8. Simplification threshold check

Design A achieves, of the required targets:

- [x] retire one old trace inductive (`trace_witness`) — **yes**
- [x] remove one major proof backbone (`Ctx_Collect_Backbone`) — **yes**
- [x] all context collectors through one generic projection (`collect_by`) — **yes**
- [x] eliminate repeated entry/edge/combine inductions — **yes** (one `collect_by_sound`)
- [~] `cfg_collect` clearly canonical or derived — **derived**, with the equality
      lemma as an optional epilogue (not gated)
- [x] architecture explanation substantially shorter — **yes** (§ "final architecture")

Six of six (one partial by deliberate scoping). Above threshold → **recommend the
rewrite.**

---

## 9. Theorem / definition correspondence

| Current | Target |
|---|---|
| `cfg_collect_ctx_act enterc seedc` | `collect_by (valid_ltr) sink_node sink_store (key enterc seedc)` (abbrev, name kept) |
| `cfg_collect_ctx dg cmp` | `collect_by (valid_ltr) sink_node sink_store (dg ∘ flatten)` + `cmp` filter |
| `cfg_collect_trace` | retired (use `valid_ltr` + `flatten`) |
| `trace_witness`, `trace_witness_ctx` | retired |
| `cfg_witness`, `cfg_collect_paths` | retired (folded into plain `collect_by`) |
| `cfg_collect` | kept; optionally `= collect_by … (λ_.())` after reverse inclusion |
| `activation_collect_sound` | corollary of `collect_by_sound` (`ctx_of = key`) |
| `ctx_collect_backbone` | corollary of `collect_by_sound` (`ctx_of = dg ∘ flatten`) |
| `valid_ltr_ctx_sound` | subsumed by `collect_by_sound` |
| `alpha_last_cfg_collect_trace_le`, `cfg_collect_ctx_act_le_collect` | replaced by one `collect_by_le_cfg_collect` |
| source theorems, `twice_*` flagship | **unchanged** (ride the kept abbreviation) |

---

## 10. Staged migration plan (green-build checkpoints)

Each stage ends with `isabelle build … Voblint_Formalization` green before the
next begins.

1. **Add `collect_by` + `flatten` + adequacy.** Prove
   `cfg_collect_ctx_act = collect_by … (key …)` (definitional). No consumer
   changes. **Checkpoint 1.**
2. **Prove `collect_by_sound`** with a parametric `step_ctx`. Re-derive
   `activation_collect_sound` as its instance; keep the old name as a corollary.
   **Checkpoint 2** (activation spine now rides the generic backbone).
3. **Re-base the digest world:** define `cfg_collect_ctx` as `collect_by` with
   `ctx_of = dg ∘ flatten`; discharge `step_ctx` for `dg ∘ flatten`; re-derive
   `ctx_collect_backbone` as an instance. DG read lemmas unchanged (schematic in
   `dg`). **Checkpoint 3** — *this is the risk gate.*
4. **Migrate `Trace_Analysis_Sound`, `Mixed_Flow_Sound`, `Sign_Exec_Sound`, and
   trace examples** off `cfg_collect_trace`/`trace_witness`. **Checkpoint 4.**
5. **Delete** `trace_witness`, `cfg_collect_trace`, `trace_witness_ctx`,
   `alpha_ctx`, `cfg_witness`, `cfg_collect_paths`; fold `Ctx_Collect_Backbone`.
   **Checkpoint 5.**
6. **(Optional epilogue)** prove `cfg_collect_subset_ltr_sink`, make
   `cfg_collect` a formal `collect_by` abbreviation. **Checkpoint 6.**

---

## 11. Risks and fallback points

| Risk | Stage | Fallback |
|---|---|---|
| `step_ctx` for `dg ∘ flatten` does not close (flat incremental step genuinely needs the flat splice) | 3 | **Stop at Checkpoint 2.** Activation spine is unified; keep the flat digest world as-is and document the split as intentional (the review's Option A). Still a net win: one backbone covers activation + plain. |
| `flatten` adequacy is fiddly (combine splice mismatch) | 1 | Weaken to the one direction actually needed (`valid_ltr ⟹ trace_witness`); the reverse is never used. |
| Reverse `cfg_collect` inclusion is hard/false | 6 | Skip — `cfg_collect` stays primitive-presented with the existing `⊆` bridge; no client cares. |
| DG lemmas silently depend on flat structure, not just `dg` | 3 | grep shows them schematic in `dg`/`cmp` (`Clean_RRead_Sound:261`, `Digest_Global_Read:147`, `Value_Digest_Reader:74`); if a hidden flat dependency surfaces, isolate it as an extra `step_ctx` premise rather than abandoning the merge. |
| Migration drags on, half-migrated tree | any | Every stage is independently green and shippable; a stall leaves a *strictly better* intermediate, never a broken one. |

---

## Final architecture (≤10 lines)

```text
valid_ltr                         -- the one execution witness (call-structured)
  ├ sink_node / sink_store        -- what a witness reaches
  ├ flatten :: ltr ⇒ trace        -- history projection for digests
  └ collect_by W node store ctx_of v c = {store w | w∈W, node w = v, ctx_of w = c}
        ctx_of = (λ_.())          → plain collecting     (⊇ cfg_collect endpoint)
        ctx_of = dg ∘ flatten     → digest/DG collecting  (full dg generality)
        ctx_of = key enterc seedc → activation collecting (cfg_collect_ctx_act)
collect_by_sound (one backbone)   → all three soundness corollaries
source: pstep ⇒ valid_ltr ⇒ collect_by(key) ⇒ cap ⇒ abstract store bound
```

One witness, one projection, one backbone, three thin corollaries, one unchanged
source theorem. `cfg_collect` remains the stable plain endpoint, provably derived
as an optional epilogue.

**Recommendation: execute Design A, stages 1–5, with Checkpoint 3 as the
go/no-go gate.**
