# Migration plan — value-carried digests: reader precision from solved `D`

> **Status: design only.** No theory changed, nothing implemented, nothing committed.
> Reaching definitions are out of scope here (see `DIGEST_INDEXED_READER_MIGRATION.md`
> for the RD line). This plan targets Goblint-style **value-carried** digests — mode /
> thread-id / lockset / privatization partition — where the reader digest is a
> **projection of the solved local state `D`**, not an external map.
>
> Claims tagged **[verified]** (read from the Isabelle sources this session, with
> `file:line`), **[verified-source]** (read from `goblint/analyzer` OCaml this session),
> or **[conjectured]** (design inference, not machine-checked). Goblint claims are
> source-checked where marked; the paper framing (Seidl FM 2026) is theory-level.

---

## 0. Target architecture (restated)

```
local unknown   Inl (pp, ctx)        ↦ D                 -- carries the digest component
global unknown  Inr partition_key    ↦ G                 -- partitioned by digest key
reader digest   reader_digest pp ctx := π (σ (Inl (pp,ctx)))
read            obs_digest σ (pp,ctx) = σ(Inl(pp,ctx)) ⊔ ⨆{ σ(Inr k) | compatible (π …) k }
```

The write key and the read filter both derive from `D`; `reader_digest` is no longer
supplied by hand.

---

## 1. Where `reader_digest` is fixed, passed, consumed  [verified]

- **Fixed**: locale `digest_global_read` (`src/Analysis/Generic/Solver/Digest_Global_Read.thy:69`)

  ```isabelle
  locale digest_global_read =
    fixes reader_digest :: "pp ⇒ 'c ⇒ 'd"
      and compatible    :: "'d ⇒ 'g::finite ⇒ bool"
  begin
  ```

  **The locale has no `assumes`** — `reader_digest` is entirely unconstrained. [verified,
  `:69-72`]
- **Consumed**: only inside `obs_digest` (`:83`):

  ```isabelle
  obs_digest σ p = σ (Inl p)
                 ⊔ glob_env_cmp (λ_ g. compatible (reader_digest (fst p) (snd p)) g) (snd p) σ
  ```

  Every downstream theorem (`combine_read_obs`, `post_fixpoint_sound_obs_digest`,
  `obs_digest_collect_ctx_sound`, and the RD wrappers in `Reaching_Defs.thy`) sees
  `reader_digest` **only** through `obs_digest`. [verified, grep of all `reader_digest`/
  `obs_digest` sites]
- **Passed**: at rule application via `[where reader_digest = …]`, jointly with `[where
  sigma = …]` — e.g. `reaching_def_collect_sound` does
  `apply (rule digest_global_read.obs_digest_collect_ctx_sound
             [where reader_digest = reach and compatible = rd_compatible and …])`
  (`Digest_Global_Read.thy:660`). [verified]

**Consequence.** `reader_digest` is a free parameter instantiated at use, alongside `σ`,
with zero locale assumptions. Nothing in the kernel refers to it except the read.

---

## 2. Does the kernel permit `reader_digest := π(σ)` without changes?

**[verified] that it is well-formed and kernel-free; [conjectured] that the resulting
obligations discharge cheaply.**

- `obs_digest` takes `σ` as an argument and uses the fixed `reader_digest`. Instantiating
  the locale/theorem parameters with `reader_digest := λ v ctx. π (σ0 (Inl (v,ctx)))` and
  `sigma := σ0` for a **solved constant `σ0`** is type-correct: `σ0` is an ordinary
  defined environment (`rd_solution`, `kgen_solution` are exactly such constants), and
  `π (σ0 (Inl (v,ctx)))` has type `'d`. No recursion — `σ0` is solved first, the reader is
  defined from it, the read is computed. [verified: term-level well-formedness; the
  theorems already expose both as `[where]` params]
- The degenerate collapse lemma already covers a *projection-of-`ctx`* reader
  (`obs_digest_collapse_shape`, `:104`; `reader_digest v ctx = ctx` recovers
  `side_env_cmp`). A projection-of-`D` reader is the same move with a different
  projection. [verified: the collapse mechanism exists]
- **Open**: the collecting theorem's premises — `ENTER_MONO`, `CALLEE_INCL` /
  `READER_INCL`, `CMP_SOUND` — become statements about `π(σ0)` and must be discharged from
  `σ0`'s post-fixpoint invariants. That is real per-instance proof, not kernel work.
  [conjectured dischargeable]

**Verification gate (do this before Stage 2).** In I/Q, instantiate
`digest_global_read.obs_digest_collect_ctx_sound` on the existing `kgen_solution` with
`reader_digest := λ v ctx. π (snd kgen_solution (Inl (v,ctx)))`, `compatible := …`,
`sigma := snd kgen_solution`; confirm it typechecks and reduces the premises to
projection facts. Green here promotes §2 from [conjectured] to [verified].

---

## 3. Minimal extension to `D`  [verified facts + conjectured design]

`D = 'a abs_state = vname ⇒ 'a` (`Abstract_Domain.thy:23`), `'a::sound_domain`
(`:46`). Two structural invariants matter:

- **Inl slots are `bot` on globals** (`inl_slot_globals_bot`, `Constraint_System.thy:667`).
- **Inr slots are `bot` on locals** (`inr_slot_locals_bot`, `:653`).

So the projection `π(σ(Inl(v,ctx)))` can only read a **local** coordinate of `D` — a
global coordinate is `bot` there. This drives the extension choice:

| Design | What carries the digest | Domain change | First-example fit |
| --- | --- | --- | --- |
| **P — ghost local var** | a designated **local** name (e.g. `"mode"`) whose `'a`-value encodes the digest | **none** (rides existing `'a`) | mode ∈ {0,1} encodes as `SZero`/`SPos` in `sign` |
| **Q — product value** | enrich `'a` to `'a × 'dig` (or unknown codomain to `'a abs_state × 'dig`) | domain typeclass + transfer + bridge + gamma | locksets, richer digests |

**Recommendation: start with Design P.** For a 2-valued mode, no domain extension is
needed at all — the mode is a local ghost variable tracked by the *existing* sign
analysis, and `reader_digest v ctx = decode (σ (Inl (v,ctx)) ''mode'')`. This is the
literal Goblint move (`context = projection of D`) with the smallest surface.
[conjectured that the sign lattice suffices for a 2-valued mode and the projection
obligations hold; verified that P needs no domain-type change]

Design Q is deferred to a later stage for genuinely set-valued digests (locksets), where
`'a` cannot encode the digest. Q touches: `sound_domain`/`abstract_domain` instances,
`effectful_domain_transfer`, `Exec_St` code-gen, and `gamma_state`. Sizable; not on the
first path.

---

## 4. Write key from `D` — already supported  [verified]

The digest must also key the **global partitions** (`Inr partition_key`). The writer
must deposit its contribution into the partition of *its own* digest — i.e. a
**state-dependent** write key. This machinery already exists:

- `switching_combine` computes `Side` keys from the **queried caller state**:
  `kgen_combine_st cc ex ctx = QueryL (cc,ctx) (λsc. QueryG ctx (λg. … Side callee …))`
  where `callee = kgen_ec ctx (sc ⊔ g)` (`Exec_Sign_Cmp_Keyed_Gen_Run.thy:57-65`). A
  mode-switching combine keys `Side (partition-of (decode (sc ''mode'')))` the same way.
  [verified: state-dependent Side keys are what "switching" means]
- Its soundness obligation is named: `switching_combine_sound`
  (`TD_Side_Eff_Cmp_Gen.thy:961`), discharged for the context-preserving instance by
  `fixed_combine_satisfies_switching_combine_sound` (`:982`). A mode-switching combine
  needs its own discharge. [verified: obligation + one discharge exist; mode discharge
  is new]

**Consequence.** The *write* side needs a new switching-combine instance + its
`switching_combine_sound` proof, but no new kernel mechanism.

---

## 5. First example — recommendation  [conjectured ranking]

Rank by proof surface, ascending:

1. **Mode-sensitive globals (2-valued), Design P — RECOMMENDED FIRST.**
   A config-mode / `{ST,MT}` flag as a ghost **local**, encoded in `sign` (`SZero`/`SPos`).
   Reader digest = decode of the local slot; global partitions keyed by mode. No domain
   change; reuses the existing sign solver and switching combine. Directly reworks the
   *narrative* of `Example_Config_Mode_Digest_Precision.thy` — which today fakes the mode
   via RD def-sites (`:11-13`, `rd_reach` hand-supplied `:136`) — into a genuine
   projection reader. This is the smallest end-to-end proof of the target architecture.
2. **Thread-id-like digest.** Same shape as mode but the digest lattice is a small finite
   set of thread ids; still Design P if ids encode in a finite `'a`, else Design Q-lite.
3. **Lockset-like digest.** Set-valued → needs Design Q (product domain). Highest surface;
   do last, once P is proven and the projection obligations are understood.

**Verdict: build the 2-valued mode example first.** It exercises projection reader +
state-dependent write key + compatibility, with zero domain-type work.

---

## 6. Mapping to Goblint  [verified-source where marked]

| Goblint (`goblint/analyzer`) | This plan | Status |
| --- | --- | --- |
| `context : man → fundec → D.t → C.t` (projection of `D` at calls) | `reader_digest v ctx := π(σ(Inl(v,ctx)))` (projection of `D`) | analogy [verified-source: `analyses.ml` Spec] |
| `sideg : 'v → 'g → unit` | `Side k d` with `k` from the queried state (switching combine) | [verified `sideg`; verified switching machinery `:961`] |
| global var `V.t` (`SpecSysVar`), thread-id / lockset partitioned in `basePriv` | `Inr partition_key`, `'g::finite` | [verified-source: `V : SpecSysVar`; partition wiring in `basePriv` noted, not line-quoted] |
| privatization read consults the `D`-relevant partition | `compatible (π(σ(Inl…))) g` filter | [verified read shape `:83`; compatibility-correctness is the new obligation] |
| no reaching-definitions analysis | (RD kept as legacy/example only — §9) | [verified-source: absent] |

The projection reader is the faithful transcription of `context : D.t → C.t`: both read
the abstract local state to decide flow-insensitive behaviour.

---

## 7. Staged migration plan

Each stage: **goal → changes → obligations → exit criterion**. Stages are additive; the
existing `side_env_cmp` and RD spines stay batch-green throughout.

### Stage 0 — projection-reader feasibility gate (no new theory)

- **Goal.** Promote §2 from [conjectured] to [verified].
- **Changes.** None committed. I/Q-only: apply `obs_digest_collect_ctx_sound` on
  `kgen_solution` with a projection reader; inspect the residual premises.
- **Obligations.** None proved yet — this reads the goal shapes.
- **Exit.** Instantiation typechecks; the premises `ENTER_MONO` / `CALLEE_INCL` /
  `CMP_SOUND` are expressed over `π(σ0)` and look dischargeable. **If it does not
  typecheck, the whole plan needs a kernel touch — stop and reassess.**

### Stage 1 — the digest interface for a value projection (additive)

- **Goal.** A named `compatible` + `reader_digest` for the mode digest, plus the collapse
  witness (as for the ctx and RD readers).
- **Changes.** New theory `Value_Digest_Read.thy` (sibling of the RD scaffold in
  `Digest_Global_Read.thy`): a `mode` type (finite), `mode_compatible`, and
  `mode_obs σ ≡ digest_global_read.obs_digest (λ v ctx. decode (σ (Inl (v,ctx)))) mode_compatible`.
  Prove the degenerate/collapse and `glob_env_cmp` reuse — mirror `rd_obs`.
- **Obligations.** `mode_obs` shape lemmas (mechanical, mirror `rd_read_at`,
  `rd_glob_read_singleton`). [conjectured mechanical]
- **Exit.** `Value_Digest_Read` I/Q-clean; `mode_obs` collapses correctly.

### Stage 2 — projection-reader collecting soundness (the core)

- **Goal.** The value analogue of `reaching_def_collect_sound_*`: collecting soundness
  with `reader_digest = π(σ)`.
- **Changes.** In `Value_Digest_Read.thy`, a theorem
  `mode_collect_sound : cfg_collect_ctx dg cmp g S v ctx ≤ ⟦mode_obs σ (v,ctx)⟧`
  routed through `obs_digest_collect_ctx_sound` (or its `_bot` variant if the mode local
  case needs the bot-on-locals route). `rt` instantiated by `context_domain.route`.
- **Obligations** (the four the user names):
  - **Projection soundness** — `decode (σ(Inl(v,ctx)))` over-approximates the concrete
    digest at `(v,ctx)`. Follows from `gamma_state` soundness of the ghost local +
    `decode` monotone. [conjectured]
  - **Compatibility correctness** — every concrete global write affecting the concrete
    state at `(v,ctx)` lands in a partition `compatible` with `π(σ(Inl(v,ctx)))`. The
    genuine content (Goblint's "reader in ST ignores MT writes"). [conjectured — the load-
    bearing new proof]
  - **`CALLEE_INCL` / `READER_INCL`** — reader inclusion across a combine, or the
    bot-on-locals route (`obs_digest_collect_ctx_sound_bot`, already proven, `:417`) to
    sidestep it. [verified route exists; discharge conjectured]
  - **`ENTER_MONO`** — the routed callee digest is compatible with the caller's; here it
    is provable *because* the reader is exact-per-point (the very gap
    `DIGEST_INDEXED_READER_MIGRATION.md:63` documents for `side_env_cmp`). [conjectured]
- **Exit.** `mode_collect_sound` batch-green.

### Stage 3 — state-dependent write key (switching combine instance)

- **Goal.** An executable generator that side-effects each global write to its mode
  partition, keyed from the writing state.
- **Changes.** A `mode_switching_combine_st` (sibling of `kgen_combine_st`,
  `Exec_Sign_Cmp_Keyed_Gen_Run.thy:54`) whose `Side` key is `partition-of (decode (sc
  ''mode''))`; wire through `side_cfg_T_eff_cmp_st`.
- **Obligations.** `switching_combine_sound` (`TD_Side_Eff_Cmp_Gen.thy:961`) for this
  combine. Plus the `Exec_Cmp_Bridge` zip-relation transport for the mode key (mirror
  `part_post_solution_cmp_st_to_abs_eff`). [verified obligation exists; discharge new,
  bridge is the "sizable mechanical" risk per the build-timeout policy]
- **Exit.** The generator code-generates and `TD_side_always_join_Interp_solve` runs on
  a mode program (`by eval`, mirror `kgen_runs`).

### Stage 4 — executable, sound end-to-end example

- **Goal.** Replace the faked mode in `Example_Config_Mode_Digest_Precision.thy` with the
  real projection reader on the solved environment.
- **Changes.** New `Example_Mode_Projection_Digest.thy`: solve the mode program (Stage 3),
  read back partitions, and `value (mode_obs (proj-reader) σ (v,ctx))` per node —
  point-sensitive precision by projection, `by eval`. Connect to `mode_collect_sound`
  (Stage 2) so the executed reads are the certified reads (mirror
  `exec_read_agrees_with_sound_witness`, `Exec_Sign_RD_Keyed_Solve.thy:119`).
- **Obligations.** `eval` equalities + the agreement lemma. [conjectured mechanical]
- **Exit.** Two-panel showcase (baseline merges; projection separates), fully machine-
  checked, with **no hand-supplied reader**.

### Stage 5 (later) — Design Q for set-valued digests

- **Goal.** Locksets / richer digests that `'a` cannot encode.
- **Changes.** Product unknown codomain `'a abs_state × 'dig`: new `sound_domain` product
  instance, product transfer (`effectful_domain_transfer`), `Exec_St` code-gen, product
  `gamma_state`. Reader projects `π₂`.
- **Obligations.** All of Stage 2 re-proved at the product level + product-domain
  soundness. [conjectured; largest surface]
- **Exit.** A lockset-like example end-to-end. **Optional / research-grade.**

---

## 8. Proof-obligation catalog (per the user's four)

| Obligation | Where it lands | Status |
| --- | --- | --- |
| **Monotonicity** | `decode`/`π` monotone; product `sup` (Stage 5) | mechanical for P [conjectured]; real for Q |
| **Post-fixpoint soundness** | reused verbatim — `post_fixpoint_sound_obs_digest` swallows any `renv`; the reader change is invisible to the backbone (`Digest_Global_Read.thy:196`, one-line instantiation) | [verified reusable] |
| **Compatibility correctness** | Stage 2, the load-bearing new proof — writes affecting `(v,ctx)` land in compatible partitions | [conjectured] |
| **Projection soundness** | Stage 2 — `decode (σ(Inl…))` over-approximates concrete digest, from `gamma_state` | [conjectured] |

The kernel backbone (COMB split, trace theorem, collecting wrapper) is **reused
unchanged** — [verified], since it is read-agnostic (`renv`/`rread` are parameters,
`:218-221`).

---

## 9. Disposition of the RD `rd_reach` path  [recommendation]

Keep it as **legacy / example-only**. Rationale:

- It is batch-green and self-contained (`Reaching_Defs.thy`, `Exec_Sign_RD_Keyed_*`), and
  proves a genuinely different (syntactic, σ-independent) digest that has **no Goblint
  analog** (§6, verified-source: no RD analysis). Deleting it loses coverage of the
  σ-independent branch of the generic kernel.
- It shares the kernel (`digest_global_read`, `obs_digest`) with the projection reader, so
  both are instances of one interface — the RD path is evidence the interface spans both
  σ-independent and σ-projected readers.
- **Action:** freeze `rd_reach` as the def-site/legacy instance; do not extend it. The
  value-carried line (Stages 1-4) becomes the primary, Goblint-faithful path. Re-narrate
  `Example_Config_Mode_Digest_Precision.thy` (or supersede it with the Stage-4 example) so
  "mode" no longer means "def-site" — its current framing is misleading (it calls a
  reaching-definition mechanism a "mode", `:11-13`).

---

## 10. Risks and open conjectures

- **Stage 0 gate is load-bearing.** If a collecting-theorem premise implicitly needs
  `reader_digest` independent of `σ` (not evident, but unproven), the kernel-free claim
  fails. Mitigation: Stage 0 before anything else. [conjectured kernel-free]
- **Compatibility correctness** (Stage 2) is the real new theorem, analogous to RD's
  `must_write`/`REAL` but value-based. Unproven; cost unknown. [conjectured]
- **Bridge transport** (Stage 3) is flagged repeatedly as the metis/simp blow-up surface
  (build-timeout policy). Per-instance, sizable.
- **Ghost-local encoding fidelity.** Modeling a mode/thread-state as an IMP2 local
  assignment is a modeling choice; whether it faithfully mirrors Goblint's event-driven
  mode transitions is a semantic question, not just a proof one. [conjectured adequate for
  a first example]
- **`'a` expressiveness.** Design P only works while the digest embeds in the value
  lattice. The moment it does not (locksets), Stage 5 (product domain) is unavoidable.
  [verified constraint from `abs_state = vname ⇒ 'a`]

---

## Bottom line

The kernel **already permits** a projection reader (`digest_global_read` has no
assumptions; `reader_digest` and `σ` are jointly instantiable) — [verified] at the
term/interface level, [conjectured] at the discharge level, with Stage 0 as the gate that
settles it. The **write** side is already state-dependent (switching combine,
[verified]). The **smallest faithful first step** is a 2-valued mode as a ghost local
(Design P, no domain change), turning the currently-faked
`Example_Config_Mode_Digest_Precision` into a real projection-reader instance. Set-valued
digests (locksets) need a product domain (Stage 5) and are research-grade. The RD path
stays as legacy evidence of the interface's σ-independent branch — Goblint has no RD, so
nothing to port there.
