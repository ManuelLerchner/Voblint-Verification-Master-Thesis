# Collecting-Semantics Architecture Review

Status: **SUPERSEDED (2026-07-18) — historical review.** This review recommended
*Option B* (make `valid_ltr` canonical and reconstruct the digest world on top of
it via `flatten`). The project instead **deleted** the relational digest spine
(see docs/history/DIGEST_SPINE_REMOVAL_PLAN.md, AD-44) — the witness-merging half of the
recommendation was not adopted. What was adopted: the generic `collect_by`
combinator and `valid_ltr` as the single trace foundation (both live). Retained
as the design analysis that led to the removal decision.

Status (original): design review, no code changed. Verified against `src/` at branch
`local-trace-semantic`. All `file:line` refs are live at time of writing.

The goal is to decide whether the collecting-semantics layers can be reduced to
**fewer semantic concepts, fewer proof spines, and one end-to-end story** —
knowing the maintainer will accept a large migration *iff* the result is
genuinely simpler.

> Follow-up: the actionable migration decision is
> `docs/history/COLLECTING_SEMANTICS_UNIFICATION_PLAN.md`. It also corrects §3 below:
> `cfg_collect` is **not** irreducibly primitive — `cfg_collect_eq_paths`
> (`CFG_Collect.thy:392`) proves `cfg_collect = cfg_collect_paths`, a store-level
> `cfg_witness` collection. It is a *derived* witness collection over the weakest
> witness, kept as the plain-projection endpoint rather than a second foundation.

---

## 0. Executive summary

- There is **not** one trace foundation today. There are **two disjoint trace
  inductives** plus **one lfp over-approximation target**:
  - flat `trace_witness :: … store list …` (context via a digest `dg :: trace ⇒ 'c` + `cmp`),
  - call-structured `valid_ltr :: … ltr set` (context via `key enterc seedc`),
  - `cfg_collect = lfp (cfg_collect_F g S)`.
- The two trace worlds are **not bridged** (no `ltr_of_trace` / `trace_of_ltr`;
  grep empty). They are related to `cfg_collect` only by **one-directional
  soundness inclusions**, never equalities.
- `valid_ltr` **strictly dominates** `trace_witness` in information: an `ltr`
  carries the call tree (`Root`/`Call`/`Resume`); a flat trace is its
  `path`-flattening. The reverse encoding is impossible — a flat trace has lost
  call nesting.
- The digest context model is **genuinely general**: every DG read-soundness
  lemma is proved schematically in `dg`/`cmp`. The activation `key` is *not* an
  instance of a flat-trace digest (it needs call structure), so the two context
  mechanisms are **typing-incomparable today**.
- **A real unification exists** and it is the recommended target: make
  `valid_ltr` the single trace foundation and generalize the context reader from
  `dg :: trace ⇒ 'c` to `dg :: ltr ⇒ 'c`. That single reader **subsumes both**
  the flat digest (`dg ∘ flatten`) and the activation key (`key enterc seedc`).
  Net effect: **one trace inductive, one context-collecting definition, two
  instantiations**, and `activation_collect_sound` becomes a corollary of the
  general context backbone instead of a parallel induction.
- This is **Option C** below. It is a multi-file re-proof of the context
  backbone over the `ltr` induction, not a lemma — but the DG lemmas are already
  schematic in `dg`, so they transfer by construction, and it deletes an entire
  trace inductive and a duplicated soundness spine.

Recommendation: **Option C**, staged. Confidence that it reduces concepts:
high. Confidence in effort estimate: medium (backbone re-induction is the risk).

---

## 1. Current dependency diagram (verified)

```text
   flat trace_witness                         call-structured valid_ltr
   (store list)                               (ltr = Root|Call|Resume)
   CFG_Collect_Trace.thy:86                   LTR_Def.thy:73
        │                                              │
        │ cfg_collect_trace {tr. trace_witness…}       │ sink_store / key
        │ CFG_Collect_Trace.thy:102                    │
        ▼                                              ▼
   cfg_collect_trace                            cfg_collect_ctx_act
        │                                       LTR_Def.thy:627
        │ alpha_ctx dg cmp  (digest context)           │
        ▼                                              │
   cfg_collect_ctx  (dg :: trace ⇒ 'c, cmp)            │
   CFG_Collect_Trace.thy:502                           │
        │                                              │
        │ alpha_last_cfg_collect_trace_le (:345)       │ cfg_collect_ctx_act_le_collect (:634)
        │  ⊆                                           │  ⊆
        └───────────────►  cfg_collect (lfp)  ◄────────┘
                           CFG_Collect.thy:169
                                 │  (sound over-approximation TARGET)
                                 ▼
        DG read soundness  ────────────────►  activation source soundness
        Ctx_Collect_Backbone / Clean_RRead     Activation_Backbone / Source_Activation_Sound
        (rides cfg_collect_ctx)                (rides cfg_collect_ctx_act)
```

Two independent inductions land in the same target. No horizontal edge between
the trace worlds.

---

## 2. Semantic comparison: `trace_witness` vs `valid_ltr`

| Aspect | `trace_witness` (`CFG_Collect_Trace.thy:86`) | `valid_ltr` (`LTR_Def.thy:73`) |
| --- | --- | --- |
| Carrier | `trace = store list` (flat) | `ltr = Root p \| Call caller p \| Resume caller callee p` |
| Constructors | `entry`, `proc_entry`, `edge`, `combine` | `start` (Root), `intra` (extend), `call` (Call), `ret` (Resume) |
| Call/return info | **flattened**: combine splices `tau @ tl rho @ [r]` into one store list; caller/callee identities lost | **explicit**: `Call` keeps the caller subtree; `Resume` keeps both caller and callee subtrees |
| Recursion | implicit (just a longer list) | explicit (nested `Call`/`Resume` tree) |
| Activation identity | **not recoverable** | recoverable via `caller_of` chain (`LTR_Def.thy:84`) |
| Context computation | external digest `dg :: trace ⇒ 'c` + compatibility `cmp` (`alpha_ctx`, `:499`) | fixed fold `key enterc seedc` over the call tree (`:110`); `Resume` keeps caller's context |
| Retained store path | full store list | full local `path` per activation, plus retained subtrees |
| Generality of context | **high** — any `dg`/`cmp` | **fixed shape** — one two-op activation fold |
| Trace expressiveness | **low** — flat | **high** — call tree |

**Encoding direction (verified by construction, not yet formalized):**

- `valid_ltr` → `trace_witness`: a flat store trace is `path`/flatten of an
  `ltr`. An `ltr` determines its flat trace. **Encodable.**
- `trace_witness` → `valid_ltr`: a flat trace cannot reconstruct call nesting.
  **Not encodable.**

So `valid_ltr` is the more expressive object. `trace_witness` is (morally) its
flat projection — but this projection is **not currently formalized**; there is
no `flatten :: ltr ⇒ trace` and no lemma relating the two inductives.

**Context mechanisms are incomparable *as typed today*:**

- `key enterc seedc` reads the `ltr` (needs call structure) — **cannot** be
  written as a `dg :: trace ⇒ 'c` on the flat trace.
- `dg :: trace ⇒ 'c` reads only the flat trace — strictly less input than an
  `ltr`.

The asymmetry is the whole reason both exist. It also points straight at the
fix: lift the digest's input type to `ltr`.

---

## 3. Role of `cfg_collect` (the lfp)

- Definition: `cfg_collect g S = lfp (cfg_collect_F g S)` (`CFG_Collect.thy:169`).
- Why only inclusions are proved: it is the **soundness target**, an
  over-approximation both trace worlds must land inside. `cfg_collect_ctx_act ⊆
  cfg_collect` (`:634`) and `alpha_last (cfg_collect_trace) ⊆ cfg_collect`
  (`:345`) are exactly the "traces refine the fixpoint" facts.
- Should equality hold? For the flat trace world, `cfg_collect` and
  `alpha_last (cfg_collect_trace)` are plausibly equal (standard collecting =
  path-collecting), and the `⊆` half is proved; the reverse is unproved and not
  needed. For `valid_ltr`, only `⊆` is meaningful — the activation collecting is
  a *filtered* subset (the `key` filter only removes traces, per the doc comment
  at `:620`).
- Is the mismatch essential? **Yes and no.** `cfg_collect` earns its keep as a
  small, context-free, fixpoint-shaped target that domain soundness and the
  eqsys layer consume directly (46 files). Keep it. Its lfp form is a genuine
  API advantage — do **not** try to redefine it as a trace projection; that
  would drag the whole eqsys/domain layer through trace reasoning for no gain.

**Verdict:** `cfg_collect` is not part of the redundancy. It is the shared sink.
Unification is about the two *trace* worlds above it.

---

## 4. Dependency inventory

Counts are files under `src/` mentioning the name (grep `-l | wc -l`).

| Object | Def site | Files | Principal consumers / spine |
| --- | --- | ---: | --- |
| `cfg_collect` | `CFG_Collect.thy:169` | 46 | domain soundness, eqsys, both trace bridges, examples — the universal target |
| `cfg_collect_ctx` | `CFG_Collect_Trace.thy:502` | 11 | DG read spine: `Ctx_Collect_Backbone`, `Clean_RRead_Sound`, `Digest_Global_Read`, `Value_Digest_Reader`, `TD_Side_Eff_Cmp_*`, `DG_Route_Soundness`, `Trace_Analysis_Sound` |
| `cfg_collect_trace` | `CFG_Collect_Trace.thy:102` | 14 | `Trace_Analysis_Sound`, `Mixed_Flow_Sound`, `Sign_Exec_Sound`, many trace/digest examples |
| `cfg_collect_ctx_act` | `LTR_Def.thy:627` | 8 | activation spine: `Activation_Backbone`, `Source_Activation_Sound`, interval flagship, `Located_LTR` source bridge |
| `trace_witness` | `CFG_Collect_Trace.thy:86` | 5 | flat-trace backbone (`Ctx_Collect_Backbone`), its own lemmas |
| `valid_ltr` | `LTR_Def.thy:73` | (LTR_Def + Activation spine) | `activation_collect_sound`, `valid_ltr_ctx_sound`, `Located_LTR` |

**Duplicated inductions (the review's smoking gun, question 3):**

- `valid_ltr_ctx_sound` (`Activation_Local_Sound.thy:151`) — 4-case induction
  (start/intra/call/ret) proving `sink_store ∈ ⟦sg⟧` under ENTRY/EDGE/SEED/COMB.
- `ctx_collect_backbone` (`Ctx_Collect_Backbone.thy:123`) — 4-case induction
  (entry/edge/enter/combine) proving `cfg_collect_ctx dg cmp ⊆ M` under the same
  shape of obligations.

These are **the same theorem over two trace types.** They are the primary
duplication a unification removes.

**Convenience vs semantic dependency:** `cfg_collect_trace` in the `Example_*`
files is largely *witness/precision demonstration* (convenience). The
semantically load-bearing consumers of the flat world are `Ctx_Collect_Backbone`
- `Trace_Analysis_Sound` + `Mixed_Flow_Sound`. Migrating those three is the real
cost; the examples follow mechanically.

---

## 5. Common-foundation possibility

Minimal shared witness: **`valid_ltr` already is it.** No fourth layer is
needed. The only missing pieces are two *projections* that are currently absent:

```text
                         valid_ltr  (single trace foundation)
                             │
        ┌────────────────────┼─────────────────────────┐
        │ flatten :: ltr⇒trace      │ key enterc seedc         │ sink_store
        ▼                           ▼                          ▼
   flat-store trace            activation context          plain collecting
   (recovers trace_witness)    (cfg_collect_ctx_act)       (⊆ cfg_collect)
        │
        │ dg' := dg ∘ flatten     ← general digest, now reading ltr
        ▼
   digest context  (cfg_collect_ctx, generalized to dg :: ltr ⇒ 'c)
```

The single generalization that unlocks everything: **change the context reader's
input type** from `dg :: trace ⇒ 'c` to `dg :: ltr ⇒ 'c`. Then:

- flat digests survive unchanged as `dg (flatten t)` — **no loss of generality**;
- the activation key is the instance `dg = key enterc seedc`, `cmp = (=)`;
- `cfg_collect_ctx` and `cfg_collect_ctx_act` become the **same definition** at
  different `dg`.

This genuinely *reduces* concepts (deletes `trace_witness`, `cfg_collect_trace`,
`trace_witness_ctx`, and one backbone induction). It does **not** add a fourth
layer — it collapses the two trace worlds into the richer existing one.

Caveat to verify before committing: the flat backbone's incremental-context
lemmas (`step_ctx`/`comb_ctx`, `context_step_refines_dg` at
`CFG_Collect_Trace.thy:~590`) assume `dg` updates *incrementally along a flat
edge*. Under `dg :: ltr ⇒ 'c` the update happens along `extend`/`Call`/`Resume`.
The generic backbone must be re-stated with an `ltr`-shaped incremental
compatibility. This is the load-bearing proof obligation of the migration.

---

## 6. Refactoring options

### Option A — Keep three layers, document + dedupe bridges only

- Conceptual complexity: unchanged (still two trace worlds).
- Files touched: ~5 (docs, rename, delete dead bridge lemmas).
- Theorem migration: none.
- Proof risk: minimal.
- Duplicate-code reduction: low — the two backbone inductions remain.
- Maintainability: documents the split but institutionalizes it.

### Option B — Make `valid_ltr` canonical, recreate the digest world on top *(recommended core)*

- Add `flatten :: ltr ⇒ trace` + `valid_ltr_flatten_trace_witness` adequacy
  (one direction suffices: `t ∈ valid_ltr ⟹ trace_witness (flatten t)`).
- Generalize the context reader to `dg :: ltr ⇒ 'c`; redefine `cfg_collect_ctx`
  over `valid_ltr`.
- Re-prove `ctx_collect_backbone` over the `ltr` induction; derive
  `activation_collect_sound` as the `dg = key` instance.
- Retire `trace_witness`, `cfg_collect_trace` (flat), `trace_witness_ctx`.
- Conceptual complexity: **down** — one trace inductive, one context collecting.
- Files touched: ~15–20 (DG spine 11 + `Trace_Analysis_Sound`, `Mixed_Flow_Sound`,
  trace examples).
- Theorem migration: the DG lemmas are **already schematic in `dg`/`cmp`**, so
  they transfer once the backbone is re-proved; examples follow mechanically.
- Proof risk: **medium** — concentrated entirely in the re-inducted backbone and
  the `flatten` adequacy lemma. Everything downstream is parametric.
- Duplicate-code reduction: **high** — deletes one inductive + one backbone.
- Maintainability: **best** — single "there exists an `ltr` whose projection
  satisfies …" story for every collecting semantics.

### Option C — New richer trace foundation, derive both

- Rejected as written. Evidence shows the "richer foundation" **already exists**
  (`valid_ltr`); inventing a fourth object would *add* a layer. Option C
  collapses into Option B. Do not build a new trace type.

---

## 7. Low-risk cleanup (worthwhile regardless of unification)

Concrete, independently actionable:

1. **Delete dead directional bridges** once their consumer is gone — audit
   `cfg_collect_ctx_flat`, `cfg_collect_trace_d` lemmas for live use.
2. **Name the two backbones consistently.** `valid_ltr_ctx_sound` vs
   `ctx_collect_backbone` obscure that they are the same theorem — rename to
   `*_collect_backbone` pair until unified.
3. **Add the missing `flatten` projection lemma** even under Option A — it
   documents that `trace_witness` is `valid_ltr`'s flat shadow and de-risks a
   later Option B.
4. **README drift.** `src/CFG/Collecting/README.md` and
   `src/Soundness/README.md` describe the trace layers as peers;
   state the dominance relation explicitly.
5. **Public-API annotation.** Mark `trace_witness` / `cfg_collect_trace` as
   *internal to the flat digest world* and `cfg_collect_ctx_act` /
   `cfg_collect` as the public client entry points (see §8).

---

## 8. Public API intent

| Interface | Audience | Level | Public? | Fate under Option B |
| --- | --- | --- | --- | --- |
| `cfg_collect` | domain/eqsys authors | over-approx target | **public** | unchanged |
| `cfg_collect_ctx_act` | context-sensitive clients, source bridge | activation collecting | **public** | becomes `dg = key` instance, kept as abbreviation |
| `cfg_collect_ctx` (`dg`/`cmp`) | DG read-soundness authors | general digest collecting | **public** | generalized to `dg :: ltr ⇒ 'c`, kept |
| `cfg_collect_trace`, `trace_witness` | internal | flat trace mechanism | **implementation detail** | retired |
| `valid_ltr` | semantics/foundation only | canonical trace | semi-public | the single foundation |

---

## Final recommendation

Do **Option B**, staged:

1. Land `flatten` + one-direction adequacy (low risk, valuable even alone).
2. Generalize the context reader to `dg :: ltr ⇒ 'c`; re-prove
   `ctx_collect_backbone` over `valid_ltr`. **Gate: green build before step 3.**
3. Instantiate `activation_collect_sound` from the general backbone; delete the
   duplicate `valid_ltr_ctx_sound` induction.
4. Migrate `Trace_Analysis_Sound`, `Mixed_Flow_Sound`, then examples; retire
   `trace_witness` / `cfg_collect_trace`.

Outcome: one trace inductive (`valid_ltr`), one context-collecting definition
(two instantiations), one soundness backbone, `cfg_collect` unchanged as the
target. That is a **strict reduction** in concepts and proof spines with no loss
of digest generality — the bar the maintainer set.

Stop-and-reassess trigger: if step 2's `ltr`-shaped incremental compatibility
does not close cleanly, the digest world's flat incremental step may be
genuinely load-bearing — in which case fall back to Option A + cleanup §7 and
document the split as intentional.
