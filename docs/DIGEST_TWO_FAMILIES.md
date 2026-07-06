# Digest-Indexed Context-Sensitive Analysis

This work develops a generic framework for digest-indexed context-sensitive analyses on top of a
verified top-down solver. Rather than committing to a single notion of context, the framework
abstracts over *how* contexts (or digests) are computed and *how* global information is
partitioned and recovered.

The framework supports two complementary families of digest analyses:

- **Value-derived digests**, where the digest is projected directly from the abstract value state
  computed by the existing analysis. These require no additional fixpoint computation and closely
  mirror Goblint's context projection mechanism.
- **Externally-computed digests**, where the digest is obtained from an independent analysis, such
  as reaching definitions. These allow richer context distinctions while remaining within the same
  generic framework.

Both families instantiate the same kernel without modification, demonstrating that the framework
is independent of the particular digest construction.

The framework is implemented on top of the verified top-down solver formalization (the vendored
`td-verification` / `TD_side` of Tilscher, Graß, Schwarz, and Seidl, NASA FM 2026) and provides a
machine-checked connection from executable solver output to the abstract collecting semantics.

A central technical result of this work is identifying that the main precision limitation does
**not** arise from context sensitivity itself, but from the publish-and-erase treatment of
globals. This boundary is characterized formally and motivates future work on automatic digest
generation and selective publication strategies.

The current development proves the soundness of the generic digest framework and its executable
writer-side implementation. For value-derived digests, it additionally characterizes the precise
frame-locality boundary where the projection-based reader ceases to be sufficient. Generic
generator-to-collecting ENTRY/EDGE discharge remains future work shared by all digest instances.

> **Status & companions.** One kernel, two instances, differing only in *where the digest comes
> from*. Both build in `Voblint_Analysis` and are demonstrated in `Voblint_Formalization` under
> the full `isabelle build` (no `sorry`); the value-derived compiled run
> `Exec_Sign_Mode_Compiled_Run` (`digest_separates_the_modes`) is wired into the session ROOT
> alongside the RD run, and `Example_Digest_Pipeline_Showcase.thy` carries one program through the
> whole executable chain. Claims tagged **[verified]** were checked at `file:line`; **[batch-green]**
> passes the full build. Companions: `DIGEST_INDEXED_READER_MIGRATION.md` (RD spine),
> `VALUE_CARRIED_DIGEST_MIGRATION.md` + `VALUE_CARRIED_DIGEST_STATUS.md` (mode),
> `DGC_ALIGNMENT_ANALYSIS.md` (the publish-and-erase alignment gap).

---

## 1. The shared kernel

Both families instantiate one locale, `digest_global_read`
(`src/Analysis/Generic/Domain/Digest_Global_Read.thy`), never edited by either
instance. It fixes two parameters and derives one read:

```isabelle
locale digest_global_read =
  fixes reader_digest :: "pp => 'c => 'd"            -- reader's digest at a program point
    and compatible    :: "'d => 'g::finite => bool"  -- reader accepts this writer key?

obs_digest sigma (v, ctx)
   = sigma (Inl (v, ctx))  join  Sup { sigma (Inr g) | compatible (reader_digest v ctx) g }
```

`Inl` is the flow-sensitive local slot at `(pp, ctx)`; `Inr g` are the global
partition slots keyed by a writer key `g`. The read joins the local slot with every
global slot the reader's digest admits. With `reader_digest v ctx = ctx` and
`compatible = gcmp` this collapses to the context-only read `side_env_cmp`
[verified `obs_digest_collapse_shape`] — so both digest families strictly generalize
context-sensitivity.

The generator side supplies a matching **writer key** `writer_key :: pp => vname => 'g`
per instance (not a kernel parameter — no read theorem mentions it). Distinct writes
land in distinct `Inr g` slots, joined only when a reader's `compatible` accepts
several.

The whole difference between the two families is the choice of `'g`, `'d`,
`reader_digest`, `compatible`, and `writer_key`.

---

## 2. Side by side

| | **RD — reaching definitions** | **mode — value-carried** |
|---|---|---|
| where the digest is computed | a **separate** dataflow (interprocedural gen/kill), external to the value solution | a **projection of the same value solution** — no second computation |
| Goblint analogue | def-site / mod-count digest on `getg`/`sideg` | `context : D.t -> C.t`, `sideg (G, Digest.compute d)` |
| key type `'g` | `def_site` (finite datatype) | `mode` (finite datatype) |
| reader digest `'d` | `def_site set` | `mode` |
| `reader_digest v ctx` | static RD set: all def-sites that may reach `(v,ctx)` | `mode_decode (sigma (Inl (v,ctx)) ''mode'')` — decode of the solved ghost local |
| `compatible d g` | `g : d` (set membership) | `d = g` (equality; single slot) |
| writer key | def-site of the assignment (`site v`, the target `pp`) | `mode_dg s` — projection of the **write-point state** |
| reader monotone? | **no** — a must-write kills an earlier def | trivially (single equality slot) |
| soundness of the read | `rd_obs_cmp_sound_from_incl`: bot-on-`Inl`-globals + reaching-set inclusion | `mode_collect_ctx_sound_bot_reduced`: slot invariants + `MODE_AGREE` |
| the interprocedural bit | `must_write_to` (decidable CFG summary) + `combine_backward_realizable` (per-digest contract) | `MODE_AGREE` — and it is **false** at callee interiors |
| status | read spine complete modulo two named per-instance facts; concrete example sound **and** executable | executable end-to-end; write-transport proven; read boundary machine-checked |

---

## 3. Family A — reaching definitions (externally computed)

The digest is a classic dataflow, run alongside the value analysis. Along a CFG path
the last writer of `x` wins; `path_def x d0 es` folds the reaching def, `path_rd` is
the `pp`-set reader (`src/Analysis/Instances/Sign/Reaching_Defs.thy`). Interprocedurally
a call `f()` kills the caller's incoming defs when `f` `must_write`s the global and
gens `f`'s exit defs; a `may_write` gens without kill.

- **Writer** keys each global write by its def-site, so `G:=0 (DS1)` and `G:=1 (DS3)`
  occupy `Inr DS1` / `Inr DS3` — never joined at write time.
- **Reader** at a point carries the reaching set; `compatible g d = g : d` selects
  exactly the live defs. Node 4 reads `{DS1} -> SZero`, node 7 reads `{DS3} -> SPos`
  (the kill dropped `DS1`), where a context-blind join gives `SNonNeg`
  [batch-green `Exec_Sign_RD_Keyed_Run`, `Exec_Sign_RD_Keyed_Solve`].
- **Soundness** collapses to two structural facts, no solved solution mentioned:
  `Inl` slots are bot on globals, and the callee-exit read sits below the return read
  by the reaching-set inclusion (`rd_obs_cmp_sound_from_incl`, `reaching_def_collect_sound_bot_incl`).
  The interprocedural residue splits into a decidable CFG summary (`must_write_to`)
  and a per-digest realizability contract (`combine_backward_realizable`, named,
  proven consistent) — neither a read-soundness nor kernel obligation
  [batch-green, `DIGEST_INDEXED_READER_MIGRATION.md` B2.7–B2.9].

The reader is **non-monotone**: kill drops a def, so the caller-side inclusion
`reach cl ⊆ reach v` fails under a killing callee. The proof routes such combines
through the bot-on-locals path instead of a monotone reader.

---

## 4. Family B — mode (value-derived)

The digest is not a separate computation — it is read back **from the value solution
itself**. The program carries a *ghost local* `''mode''`; the reader decodes it:

```isabelle
mode_reader sigma v ctx = mode_decode (sigma (Inl (v, ctx)) ''mode'')   -- Value_Digest_Read.thy:69
mode_compatible d g     = (d = g)                                        -- :58
```

- **Writer** `side_cfg_T_eff_digest_st` keys each global write by `mode_dg s`, a
  projection of the write-point state (`Digest_Keyed_Writer.thy`). `G:=0` taken at
  mode 0 publishes to `Inr MZero`, `G:=1` at mode 1 to `Inr MOne`
  [batch-green `digest_separates_the_modes`, `by eval`].
- **Reader** decodes the flow-sensitive ghost and selects that one slot. On the
  compiled run `mode_obs` reads `SZero` at `pp7` (mode 0) and `SPos` at `pp14`
  (mode 1) where the context-blind join gives `SNonNeg`
  [batch-green `Example_Mode_Value_Digest_Showcase`].
- **Transport** the executable digest generator abstracts to the abstract digest
  generator (`part_post_solution_digest_st_to_abs_eff`, unit-transfer variant), and
  the solver invariants are discharged on the real output (`mode_INR_BOT`,
  `mode_LOCAL_POST`) [batch-green, `Digest_Keyed_Writer_Sound.thy`].
- **Read boundary** the kernel's `MODE_AGREE` premise — the ghost read at a callee
  exit under the routed context equals the read at the return — is **machine-checked
  false** here: the callee exit `(1, MOne)` decodes `MZero` (reset on entry) while the
  return decodes `MOne` (`mode_agree_probe_callee` / `mode_agree_probe_return`,
  `by eval`). So `mode_collect_sound_witness` is the honest *conditional* theorem
  (`cfg_collect_ctx <= mode_obs` given `INL_BOT`, `MODE_AGREE`, and the generic
  collecting premises) — at the RD witness's premise-carrying standard, but with a
  premise that is false at callee-interior points [verified `Exec_Sign_Mode_Compiled_Run.thy:328,368`].

---

## 5. The distinguishing axis: frame-locality

Both families share one root fact and diverge on how they answer it.

**The root.** On a call, `enter_state` resets the callee's locals to `0`. A
value-derived digest read *inside* the callee cannot re-project its own ghost — it has
been wiped. The digest must ride the **context channel** across the call, not a reset
local. This is Goblint's frame-locality of the digest.

**RD's answer** is external and interprocedural: the callee's writes reach the caller
through `exit_defs` and the `must_write`/`may_write` summary. The read at a callee
interior is served by the *routed context*, and the interprocedural correctness is
the `combine_backward_realizable` contract — a genuine but dischargeable summary
obligation. Because RD is computed outside the value solution, the reset local is
simply not where it looks.

**mode's answer** exposes the boundary as a value fact. The digest *is* the ghost, so
at a callee interior the reset ghost decodes `MZero` while the caller's real mode was
`MOne` — `MODE_AGREE` fails, and the projection read is unsound there. This is not a
proof difficulty; it is the correct statement that a value-derived digest is precise
exactly in **the frame that sets the mode**, and rides the context elsewhere. The
showcase turns this into the value: at the aligned point `pp7` the projection read
equals the certified context read (`mode_obs_eq_side_env_cmp`); at the misaligned
`pp14` it is strictly more precise than the fixed context.

So the two families are not competitors — they are two points on one design. RD pays
for precision with a separate dataflow and an interprocedural summary; mode reads its
digest for free from the solution but inherits a sharp frame-locality boundary that RD
launders through its external computation.

---

## 6. What each is good for

- **RD** — precision *without* refining the context, faithful to the paper's
  call-only model. Distinct def-sites at distinct program points separate under one
  context. Costs a second dataflow and the must-write/realizability summary. Sound
  **and** executable on the flat callee-writes example.
- **mode** — no second computation; the digest is a projection of the value the solver
  already computed, matching Goblint's `context : D.t -> C.t` literally. Precise in the
  mode-setting frame; the callee frame rides the context. Executable end-to-end with a
  machine-checked read boundary.

Both leave the same genuinely-open item, shared with every instance and not
digest-specific: the generic `ENTRY`/`EDGE` generator-to-collecting bounds (see
`OPEN_PROBLEMS.md`). Set-valued digests `sign` cannot encode (locksets) need a product
domain and are out of scope (Design Q / Stage 5).

---

## 7. Pointers

| | RD | mode |
|---|---|---|
| kernel | `Digest_Global_Read.thy` | `Digest_Global_Read.thy` |
| reader/instance | `Reaching_Defs.thy`, `Digest_Global_Read.thy` (RD section) | `Value_Digest_Read.thy` |
| writer | reader-only in-tree — the RD run's equation system is hand-built (`Exec_Sign_RD_Keyed_Run.thy`); no generic solver-emitted writer | `Digest_Keyed_Writer.thy` + `Digest_Keyed_Writer_Sound.thy` |
| executable run | `Exec_Sign_RD_Keyed_Run/_Solve.thy` | `Exec_Sign_Mode_Value_Run.thy`, `Exec_Sign_Mode_Compiled_Run.thy` |
| showcase | — | `Example_Mode_Value_Digest_Showcase.thy` |
| design/status | `DIGEST_INDEXED_READER_MIGRATION.md` | `VALUE_CARRIED_DIGEST_{MIGRATION,STATUS}.md` |
