# Value-carried digest migration — status, roadmap, judgement

> Companion to `VALUE_CARRIED_DIGEST_MIGRATION.md` (the design). This file records
> what is **built and machine-checked**. Stages 0–2, the read-integration keystone,
> and an executable end-to-end example are complete and **batch-green** (`isabelle
> build Voblint_Analysis` + downstream `Voblint_Formalization`, no `sorry`). Claims
> tagged **[verified]** were checked against the Isabelle sources (`file:line`);
> **[batch-green]** = passes the full `isabelle build`, not only the I/Q checker.

---

## 1. Bottom line

**Done. The Goblint-style value-carried digest is implemented, batch-green, and
demonstrated end-to-end — read side *and* write side — with the generic digest kernel
unchanged.** The read side (`mode_obs`) is the digest-filtered `getg`; the new write
side (`side_cfg_T_eff_digest_st`) is Goblint's `sideg (G, Digest.compute d)` — each
intra global write keyed by a **projection of the write-point state**. On a compiled
program the two writes `G:=0`/`G:=1` separate into partitions `Inr MZero`/`Inr MOne`
(`SZero`/`SPos`) where the context/site generators merge them to `SNonNeg`.

Three things came together:

- the one architectural constraint that disqualified `kgen_solution` (globals keyed by
  non-`finite` `sign st`) is dissolved by keying on a **finite `mode`**;
- the read side (`mode_obs`) and the certified context read are fused by one algebraic
  identity (`mode_obs_eq_side_env_cmp`);
- the **digest-keyed writer** `side_cfg_T_eff_digest_st` (+ `switching_combine_digest_st`)
  supplies the write-key shape the existing generators lacked, giving genuine value
  separation on a real compiled CFG (`digest_separates_the_modes`, `by eval`).

Kernel `Digest_Global_Read.thy` never edited. The digest writer is now transported to
its abstract image and the solver invariants discharged (§5.1); the read side and kernel
were already proven. What remains is not an obligation but a **finding**: the kernel's
`MODE_AGREE` premise is machine-checked *false* at callee interiors — the value-derived
read is precise in the frame that sets the mode and rides the context elsewhere
(frame-locality; `DIGEST_TWO_FAMILIES.md` §5).

---

## 2. What is built and checked

All in `src/Analysis/Instances/Sign/Value_Digest_Read.thy` (kernel
`Digest_Global_Read.thy` untouched). File [I/Q-clean], 116/116 commands, 0 errors.

| Item | Statement | Status |
| --- | --- | --- |
| `mode`, `instance mode :: finite` | 2-point finite partition key | [I/Q-clean] |
| `mode_decode`, `mode_compatible`, `mode_reader`, `mode_obs` | projection reader + digest read, instantiating `digest_global_read.obs_digest` | [I/Q-clean] |
| `mode_obs_reduce` | `mode_obs σ (v,ctx) = σ(Inl(v,ctx)) ⊔ σ(Inr(mode_decode(σ(Inl(v,ctx)) ''mode'')))` | [I/Q-clean] |
| `mode_collect_ctx_sound_bot` | digest-read collecting soundness via `obs_digest_collect_ctx_sound_bot` | [I/Q-clean] |
| `mode_glob_bot_ctx`, `mode_obs_global`, `mode_cmp_sound` | discharge GLOB_BOT / CMP_SOUND from slot invariants + mode agreement | [I/Q-clean] |
| `mode_collect_ctx_sound_bot_reduced` | soundness from `inr_slot_locals_bot_ctx` + `inl_slot_globals_bot_ctx` + `MODE_AGREE` | [I/Q-clean] |
| **`mode_obs_eq_side_env_cmp`** (keystone) | under alignment `mode_decode(σ(Inl(v,ctx)) ''mode'') = ctx`, **`mode_obs σ (v,ctx) = side_env_cmp (=) σ (v,ctx)`** | [I/Q-clean] |

The keystone identifies the digest kernel's projection read with the executable
generator's certified context read.

Executable demonstration in `src/Analysis/Instances/Sign/Exec_Sign_Mode_Value_Run.thy`
(batch-green, no `sorry`; mirrors the RD solve template):

| Item | Statement | Status |
| --- | --- | --- |
| `mode :: enum` | enum instance so `glob_env_cmp`/`mode_obs` code-generate | [batch-green] |
| `mode_eqs`, `mode_solution` | mode-keyed side-effecting eqs, run through the vendored `TD_side_always_join_Interp_solve` | [batch-green] |
| `slot_MZero` / `slot_MOne` | `by eval`: partition `Inr MZero` holds `G=SZero`, `Inr MOne` holds `G=SPos` | [batch-green] |
| `read_mode_zero` / `read_mode_one` | `by eval`: **projection reader** `mode_obs` recovers `SZero` / `SPos` per mode | [batch-green] |
| `read_join_all`, `mode_reads_point_sensitive` | context-blind join-all merges to `SNonNeg`; the precision the keying recovers | [batch-green] |
| `mode_align_zero` / `_one` | `by eval`: the alignment `mode_decode(σ(Inl(v,ctx)) ''mode'') = ctx` holds on the solved env | [batch-green] |
| `exec_read_is_certified_read` | via the keystone: `mode_obs mode_env (v,ctx) = side_env_cmp (=) mode_env (v,ctx)` — the executed read is the certified read | [batch-green] |

---

## 3. The two soundness spines and where they meet  [verified]

```
Stage 2 (digest kernel)                 Generator (executable write side)
------------------------                ---------------------------------
mode_collect_ctx_sound_bot_reduced      side_cfg_T_eff_cmp_collect_sound_gen
  proves ≤ ⟦ mode_obs σ (v,ctx) ⟧         proves ≤ ⟦ side_env_cmp (=) σ (v,ctx) ⟧
  reads Inr( mode_decode(σ(Inl(v,ctx)) ''mode'') )   reads Inr( ctx )    (gkey=id)
                     \                        /
                      \                      /
           mode_obs_eq_side_env_cmp  (this session)
           equal  ⟺  ctx = mode_decode(σ(Inl(v,ctx)) ''mode'')      (CTX_IS_MODE)
```

`side_cfg_T_eff_cmp_collect_sound_gen` (`TD_Side_Eff_Cmp_Gen.thy:1032`) proves
soundness against `side_env_cmp gcmp σ (v0,ctx)` where `single: {k. gcmp ctx k} =
{gkey ctx}` collapses the read to the single slot `gkey ctx`. [verified `:1037,1047`]

With context type `= mode` (finite) and `gkey = id`, that slot is `ctx`, and the
generator read is `side_env_cmp (=) σ (v,ctx)`. The keystone then equals it to
`mode_obs`. So a single executable generator run discharges the digest-kernel
soundness — no second solve.

---

## 4. Stage 3 (write side) = reuse, confirmed  [verified]

The migration doc conjectured Stage 3 reuses existing machinery. **Confirmed at the
source:**

- **Executable switching combine already exists:** `switching_combine_st`
  (`Exec_Cmp_Bridge.thy:~185`) with `fun_of_st` bridge lemmas
  `traverse_switching_combine_st_fun_of_st` / `sides_..._st_fun_of_st` /
  `dep_..._st_fun_of_st` (`:220,230,249`). It code-generates and maps to the abstract
  `abs_switching_combine` (`:193`). [verified]
- **Its soundness is already discharged generically:**
  `abs_switching_combine_satisfies_switching_combine_sound` (`:446`) proves
  `switching_combine_sound` under three conditions — (a) `etf_combine etf = unit_combine_tree`,
  (b) `prep` preserves locals, (c) **`gkey ctx = ctx`**. [verified]
- **All three conditions are met by the mode instance:** (a)
  `sign_etf_unit_combine_tree` exists (`Exec_Sign_Ctx_Gen_Run.thy:113`); (b) the
  sign argument-fixing `prep` preserves locals (reuse); (c) `gkey = id` on the mode
  context gives `gkey ctx = ctx` trivially. [verified (a),(c); (b) reuse]

**Consequence: Stage 3 needs no new switching combine and no new
`switching_combine_sound` proof.** The value-dependence lives in `ec` — the
enter-context function computes the callee mode from the queried caller state
(`ec cc ctx caller`, `abs_switching_combine_def:201`), which is exactly Goblint's
`context : man → fundec → D.t → C.t`. The switched callee slot is invisible to the
caller's contract read, which is why the generic discharge holds regardless of `ec`.

---

## 5. The compiled example and the digest-keyed writer

`src/Analysis/Instances/Sign/Exec_Sign_Mode_Compiled_Run.thy` compiles a real IMP
program (`mode` local ghost, `G` global; `main` sets the mode + `G`, calls `f`, reads
`G` back) and runs it two ways — a before/after, both `by eval`, batch-green.

**The merge (context-keyed).** `side_cfg_T_eff_cmp_st` with a `mode` context, `ec`
projecting the caller's local `''mode''`, `switching_combine_st`. Automatic context
generation works — `ctxs_at_0 = {MZero, MOne}`, so `f` is analyzed under both mode
activations — but the two writes `G:=0`/`G:=1` live in `main` under one context, and
that generator keys **every intra write by the fixed context**, so both land in one
slot and flow-insensitively join: `slot_MZero = slot_MOne = SNonNeg`. The mode split is
real but spurious for the value. This exposed the architectural gap concretely:

> Every executable generator relabels a global write by a **constant** key — e.g. the
> fixed context `gkey c` (`side_cfg_T_eff_cmp_st`). None keys by a **projection of the
> write-point state**, which is what a value-carried digest needs.

**The fix (digest-keyed).** New generic, kernel-free generator in
`src/Analysis/Generic/Solver/Digest_Keyed_Writer.thy`:

| Item | What | Status |
| --- | --- | --- |
| `side_cfg_T_eff_digest_st` | generator: each intra edge does `QueryL (u,c) (λs. map_gtree (λ_. dg s) …)` — write key `dg s` is a projection of the write-point state (Goblint's `sideg (G, Digest.compute d)`) | [batch-green] |
| `side_rg_side_cfg_T_eff_digest_st_unit` | right-goingness (solver accepts it) | [batch-green] |
| `switching_combine_digest_st` | digest-consistent combine: reads/republishes the caller global through `QueryG (dg sc)`, callee context `dg caller` | [batch-green] |
| `side_rg_switching_combine_digest_st` | right-goingness | [batch-green] |

Instantiated for `mode` (`mode_dg s = mode_decode (lookup_st s ''mode'')`) on the same
compiled program:

| Item | `by eval` result | Status |
| --- | --- | --- |
| `digest_slot_MZero` | `Inr MZero` holds `G = SZero` | [batch-green] |
| `digest_slot_MOne` | `Inr MOne` holds `G = SPos` | [batch-green] |
| `digest_slot_join` | join-all merges to `SNonNeg` | [batch-green] |
| `digest_separates_the_modes` | `SZero`, `SPos`, strictly below the merge — **genuine value separation via the compiled pipeline** | [batch-green] |

Two supporting points, both discharged: the entry seed pollutes whichever partition
`dg(cinit)` selects, so `mode_decode`'s default is set to `MZero` (unset/`STop → MZero`,
the initial mode), keeping `SZero → MZero`, `SPos → MOne`; and the combine must read the
caller global through the **same** digest as the writer (else it republishes the
context-slot value to the callee slot and re-merges) — hence `switching_combine_digest_st`.

**Frame-locality caveat.** `f`'s reads of `G` are *not* served by re-projecting `f`'s
local `''mode''` — `enter_state` resets locals, so inside `f` the ghost is unset. A
callee's per-context read is context-channel work (`side_env_cmp` keyed by `f`'s
context), documented in `Exec_Sign_Ctx_Seeded_Run` ("caller locals are the wrong context
channel"). The digest writer separates writes in the **frame that sets the mode**; the
callee reads via its context. This matches Goblint: the digest rides the context across
calls, not a reset local.

### 5.1 Digest-writer soundness — proven; the read boundary is the finding

**Closed (`Digest_Keyed_Writer_Sound.thy`, batch-green).** The executable digest
generator abstracts to the abstract digest generator:
`part_post_solution_digest_st_to_abs_eff` (+ the unit-transfer variant bundling the
sign edge/combine trees), mirroring `part_post_solution_cmp_st_to_abs_eff`. On the
compiled run the solver invariants are discharged on the real output — `mode_INR_BOT`
(partition slots bot on locals, `restrict_global_st`-shaped) and `mode_LOCAL_POST`
(caller locals flow to the return). So the write side is transported and the two
solver-invariant premises of the collecting theorem are met.

**The finding: the read boundary is real.** The one collecting premise that does *not*
discharge is the kernel's `MODE_AGREE` — the ghost `''mode''` read at a callee exit
under the routed context must equal the read at the return. It is **machine-checked
false**: the callee exit `(1, MOne)` decodes `MZero` (reset on entry) while the return
decodes `MOne` (`mode_agree_probe_callee` / `mode_agree_probe_return`, `by eval`). So
`mode_collect_sound_witness` is the honest **conditional** theorem — `cfg_collect_ctx
<= mode_obs` given `INL_BOT` / `MODE_AGREE` / the generic collecting premises — at the
same premise-carrying standard as the RD witness, but with a premise false at
callee-interior points. This is not a proof gap: a value-derived digest is precise in
the frame that sets the mode and rides the context elsewhere (frame-locality). See
`DIGEST_TWO_FAMILIES.md` §5.

---

## 6. Risk assessment

| Risk | Severity | Mitigation |
| --- | --- | --- |
| ~~Solver/code-gen must accept a `mode`-typed context.~~ | **resolved** | Confirmed `by eval`: `mode_runs`, `ctxs_at_0`, all `digest_slot_*`. The `_st` solver runs with a finite `mode` context. |
| ~~Digest-writer soundness (§5.1) is unproven.~~ | **resolved** | `part_post_solution_digest_st_to_abs_eff` transports the write side; `mode_INR_BOT`/`mode_LOCAL_POST` discharge the solver invariants (`Digest_Keyed_Writer_Sound.thy`, batch-green). |
| **`MODE_AGREE` false at callee interiors** — the value-derived read is unsound where the reset ghost disagrees with the routed context. | **by design, not a blocker** | Machine-checked (`mode_agree_probe_*`, `by eval`). Precise in the mode-setting frame; the callee frame rides the context (frame-locality). `mode_collect_sound_witness` carries it as an honest premise. |
| `CTX_IS_MODE` structural proof (vs per-run `eval`) needs a write-once-`''mode''` syntactic condition. | low–medium | Ship the `eval` version first (sufficient for the example); generalise later. |
| `prep` seeding the ghost while preserving locals — the two must not conflict. | low | Seed `''mode''` is itself a local; encode context in it at entry, leave other locals fixed. |
| Batch vs I/Q divergence (already seen: `[OF …]` HO multiple-unifiers). | low | Pin instances with `[where …]`; keystone already fixed this way. |
| Design collapses to "context-sensitivity with a mode context" (projection redundant with context). | conceptual, not a blocker | Value-dependence is real at the **call** (`ec` projects caller `D` → callee mode); the read identity is the point, matching Goblint. Set-valued digests that `sign` cannot encode need Design Q (product domain, Stage 5, research-grade) — out of scope. |

---

## 7. Final judgement

**Implemented, batch-green, kernel unchanged.** The generic digest kernel
(`Digest_Global_Read.thy`) is used purely by instantiation and was never edited. Both
halves of the digest run on the real solver: the read side (`mode_obs`, keystone) and
the new write side (`side_cfg_T_eff_digest_st` + `switching_combine_digest_st`). On a
compiled IMP program the two writes separate into distinct finite-mode partitions
(`digest_separates_the_modes`, `by eval`) where the context/site generators merge. All
in `isabelle build Voblint_Analysis` + `Voblint_Formalization`, no `sorry`. The write
side is now transported to its abstract image and the solver invariants discharged
(`part_post_solution_digest_st_to_abs_eff`, `mode_INR_BOT`, `mode_LOCAL_POST`, §5.1);
the read side and kernel were already proven. The remaining premise, `MODE_AGREE`, is
**machine-checked false** at callee interiors — a frame-locality read boundary, not a
gap (`DIGEST_TWO_FAMILIES.md` §5).

**Fidelity to Goblint.** Read side: `reader_digest v ctx := decode(σ(Inl(v,ctx))
''mode'')` transcribes `getg` filtered by the digest; the finite key `mode` mirrors
`C.t`; the slots `Inr MZero`/`Inr MOne` mirror `sideg`-written globals. Write side:
`side_cfg_T_eff_digest_st` keys each `sideg` by `Digest.compute` of the write-point
state — Goblint's actual privatization mechanism. Context generation (`ec`/`mode_dg`
projecting the caller's local) is `context : man → fundec → D.t → C.t`. The one place
we diverge is deliberate and matches Goblint: a **callee's** read uses its context, not
a re-projection of its (reset) local — the digest rides the context across calls.

Set-valued digests (locksets) remain the one genuinely-open modeling extension: they
need a product domain (`'a abs_state × 'dig`) because `sign` cannot encode them. That is
Design Q / Stage 5 and is deliberately out of this migration's scope.
