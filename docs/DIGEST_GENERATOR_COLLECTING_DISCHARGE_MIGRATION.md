# Discharging the generic ENTRY/EDGE generator-to-collecting bounds for the digest read

> **Status: IN PROGRESS — superset-reader class closed (batch-green).** Scopes the one
> item `DIGEST_TWO_FAMILIES.md` §6 and `OPEN_PROBLEMS.md` leave open for *every* digest
> instance: the generic `ENTRY` / `EDGE` generator-to-collecting bounds on the
> `obs_digest` read. Claims tagged **[verified]** were read against the sources at
> `file:line`; **[batch-green]** passes the full `isabelle build`.
>
> Companions: `DIGEST_TWO_FAMILIES.md` (the two families and their shared residual),
> `DIGEST_INDEXED_READER_MIGRATION.md` (RD spine; COMB split + `CMP_SOUND` closed),
> `VALUE_CARRIED_DIGEST_{MIGRATION,STATUS}.md` (mode family), `OPEN_PROBLEMS.md` P11.

---

## 0. Session findings (2026-07-05) — the plan sharpened by reading the seam

Two facts from reading the sources changed the plan and are load-bearing below:

1. **The gamma-level EDGE/ENTRY discharge already exists for the `side_env_cmp` read.**
   `cmp_edge_sound` and `cmp_entry_sound` (`TD_Side_Eff_Cmp_Pull.thy:163,205`
   [verified]) prove exactly the trace backbone's `EDGE` / `ENTRY` for `side_env_cmp`
   from a generator post-fixpoint, via the masking pullback `pull_cmp`. So the residual
   is **not** "discharge EDGE/ENTRY from scratch" — it is "reach the `obs_digest` read
   from these."

2. **The true family boundary is point-*dependence* of the reader, not monotonicity.**
   My first draft called `ENTRY` "easy monotone"; that is wrong for tight readers.
   `obs_digest ≥ side_env_cmp` holds **iff** the reader admits a *superset* of the
   context keys (`side_env_cmp_le_obs_digest`, below). The mode/RD readers admit a
   *different, tighter* set — so the monotone bridge does not apply, and their `EDGE`
   needs the per-point argument. What actually decides tractability:

   | reader | `reader_digest` | admits vs `{k. gcmp ctx k}` | discharge |
   | --- | --- | --- | --- |
   | ctx-collapse | `λv ctx. ctx` (point-indep.) | equal | bridge → cmp read **[batch-green]** |
   | superset | any, `⊇ gcmp` | superset | bridge → cmp read **[batch-green]** |
   | mode | `mode_decode (σ(Inl(v,ctx)) ''mode'')` (point-dep.) | tighter, not ⊇ | frontier |
   | RD | reaching set (point-dep., non-monotone) | tighter, kill | frontier |

**Landed this session (batch-green, `Voblint_Analysis` + `Voblint_Formalization`):**

- `side_env_cmp_le_obs_digest` (`Digest_Global_Read.thy`) — the superset-reader
  monotone bridge `side_env_cmp gcmp σ (v,ctx) ≤ obs_digest σ (v,ctx)` from
  `glob_env_cmp_filter_mono`.
- `obs_digest_collect_ctx_sound_of_cmp` (`Digest_Global_Read.thy`) — the payoff:
  `cfg_collect_ctx ≤ [[side_env_cmp]] ⟹ cfg_collect_ctx ≤ [[obs_digest]]` for a
  superset reader, by `gamma_state_mono`. So a superset-reader digest read inherits the
  `side_env_cmp` collecting bound with **no** `ENTRY`/`EDGE` restated at `obs_digest`.
- `side_cfg_T_eff_cmp_collect_ctx_sound` (`TD_Side_Eff_Cmp_Gen.thy`) — **the premise-free
  ctx-collecting theorem.** From a `side_cfg_T_eff_cmp` post-fixpoint (fixed combine) it
  proves `cfg_collect_ctx dg cmp g S v0 ctx ≤ [[side_env_cmp gcmp σ (v0,ctx)]]` carrying
  **no** `ENTRY`/`EDGE`/`PROC_ENTRY`/`LOCAL_POST`/`CMP_SOUND`/`DG_*`/`ENTER_MONO`
  premise. The short route: `cfg_collect_ctx ⊆ cfg_collect` (`cfg_collect_ctx_le`) chained
  with the already-premise-free state bound `side_cfg_T_eff_cmp_collect_sound` — the
  digest-filtered slice inherits the plain generator soundness, which discharges every
  one of those obligations structurally.

This closes the superset-reader class (ctx-collapse included), sidesteps the seam
(§0.1), and delivers the premise-free ctx theorem the whole item was about — for the
`side_env_cmp` read. Remaining: (a) point the context-reader **witnesses** at
`side_cfg_T_eff_cmp_collect_ctx_sound` (drop their per-edge `by eval` `EDGE`/`ENTRY`),
S8; (b) the point-dependent readers mode/RD at the **tight** `obs_digest` read (the
frontier, §4) — `cfg_collect_ctx ⊆ cfg_collect` does **not** help there, because a
tight `obs_digest` need not over-approximate `cfg_collect`.

### 0.1 The seam that turned out not to matter: `pull_gk` vs `pull_cmp`

The gamma-EDGE discharge for `side_env_cmp` exists as `cmp_edge_sound`
(`TD_Side_Eff_Cmp_Pull.thy:163`), but its abstract-bound premise is stated at
`pull_cmp` (masks the `'g`-keyed slots, type `pp + 'g`), whereas the executable
generator `side_cfg_T_eff_cmp` is **unit-global** and its edge bound
`side_cfg_T_eff_cmp_edge_le` (`TD_Side_Eff_Cmp_Gen.thy:300`) is at `pull_gk` (single
`Inr (gkey ctx)` slot, type `pp + unit`). The first draft treated reconciling these as
the load-bearing next step.

It is not needed. `side_cfg_T_eff_cmp_collect_ctx_sound` proves the ctx bound through
the **state**-collecting route (`cfg_collect_ctx_le` + `side_cfg_T_eff_cmp_collect_sound`),
which never touches the trace backbone's gamma-EDGE and so never crosses the seam. A
`pull_gk` sibling of `cmp_edge_sound` was prototyped and verified during this work, then
**removed** as dead code once the state route landed — it discharged the same fact by a
longer path with no consumer. The seam remains real for anyone who *wants* the
trace-level per-edge discharge, but the premise-free ctx theorem does not.

---

## 1. What "ENTRY/EDGE discharge" means

Every digest read-soundness theorem concludes that the collecting semantics at a
program point is over-approximated by the digest read `obs_digest`:

```isabelle
theorem obs_digest_collect_ctx_sound:            -- Digest_Global_Read.thy:287 [verified]
  assumes ENTRY:      "\<And>ctx s. s \<in> S \<Longrightarrow> cmp (dg [s]) ctx
                          \<Longrightarrow> s \<in> \<lbrakk>obs_digest \<sigma> (cfg_entry g, ctx)\<rbrakk>"
    and   PROC_ENTRY: "\<And>ctx v s. (cfg_entry g, EA_Enter, v) \<in> edges g \<Longrightarrow> s \<in> enter_state ` S \<Longrightarrow> \<dots>"
    and   EDGE:       "\<And>ctx u a v tr s'. (u, a, v) \<in> edges g \<Longrightarrow> edge_step a (last tr) = Some s'
                          \<Longrightarrow> last tr \<in> \<lbrakk>obs_digest \<sigma> (u, ctx)\<rbrakk>
                          \<Longrightarrow> s' \<in> \<lbrakk>obs_digest \<sigma> (v, ctx)\<rbrakk>"
    and   \<dots>  -- DG_INTRA / DG_RETURN / DG_CALLEE / ENTER_MONO / COMB_SEM / wit / compat
  shows "cfg_collect_ctx dg cmp g S v ctx \<le> \<lbrakk>obs_digest \<sigma> (v, ctx)\<rbrakk>"
```

`ENTRY` / `PROC_ENTRY` / `EDGE` are **local soundness of the abstract transfer against
the concrete small-step, read through `obs_digest`**:

- `ENTRY` — every start store the digest admits at entry lands in the entry read.
- `PROC_ENTRY` — the same across an `EA_Enter` (callee-seeding) edge.
- `EDGE` — for every CFG edge, the concrete `edge_step` maps the source read into the
  target read.

Today these three are **carried as premises** at every instance and discharged only
per-example (`by eval`) or threaded all the way to the top:

| Carrier | File | How `EDGE`/`ENTRY` are met today |
| --- | --- | --- |
| `obs_digest_collect_ctx_sound` (+ `_bot`) | `Digest_Global_Read.thy:287,417` | premises |
| `post_fixpoint_sound_at_ctx_semantic_generic` | `TD_Side_Eff_Cmp_Sound.thy:23` | premises (the read-agnostic backbone) |
| RD reader theorem | `Reaching_Defs.thy` | premises |
| mode reader theorem | `Value_Digest_Read.thy` | premises |
| `Exec_Sign_RD_Keyed_Run`, `Exec_Sign_Mode_Compiled_Run` | Sign instances | discharged **per compiled program** `by eval` |

The goal: discharge `ENTRY` / `PROC_ENTRY` / `EDGE` **once**, from the abstract domain
transfer soundness and the keyed generator's own algebraic bounds — so no digest
instance restates them, exactly as the plain read already does.

---

## 2. The template already exists for the plain read

The plain (non-digest) keyed read `side_env_cmp` already has a *premise-free*
generator-to-collecting theorem — read directly, this is the pattern to lift:

```isabelle
theorem side_cfg_T_eff_cmp_collect_sound_gen:      -- TD_Side_Eff_Cmp_Gen.thy:1142 [verified]
  assumes stf:  "sound_effectful_transfer_framed etf fresh_frame"
    and comb_sound: "switching_combine_sound gkey cmb g etf fresh_frame bot0 s0"
    and single: "{k. gcmp ctx k} = {gkey ctx}"
    and inr:    "inr_slot_locals_bot_ctx \<sigma>"
    and inl:    "inl_slot_globals_bot_ctx \<sigma>"
    and S_sound:"S \<le> \<lbrakk>s0\<rbrakk>"
    and pp:     "part_post_solution (side_cfg_T_eff_cmp gkey cmb g etf fresh_frame bot0 s0) x \<sigma> vars"
    and \<dots>  -- finiteness + coverage
  shows "cfg_collect g S v0 \<le> \<lbrakk>side_env_cmp gcmp \<sigma> (v0, ctx)\<rbrakk>"
```

Its proof (`TD_Side_Eff_Cmp_Gen.thy:1158-1192` [verified]) does **not** assume
`EDGE`/`ENTRY`. It calls the base per-pp collecting theorem

```isabelle
sound_effectful_transfer.post_fixpoint_sound_at_eff   -- base spine, B4
```

and discharges its per-edge / per-combine / entry obligations from three algebraic
generator bounds proven earlier in the same file:

| Base obligation | Discharged by | `file:line` [verified] |
| --- | --- | --- |
| intra edge  `apply_etf ≤ side_env … w`     | `side_cfg_T_eff_cmp_edge_le`    | `:300` (used `:1177`) |
| `EA_Enter`  edge                            | `side_cfg_T_eff_cmp_enter_le`   | `:782` (used `:1172`) |
| entry seed  `s0 ≤ side_env … entry`         | `s0_le_side_env_cmp_entry`      | `:1003` (used `:1187`) |
| combine edge                                | `switching_combine_sound`       | `:1071` |

**So `ENTRY`/`EDGE` for `side_env_cmp` are already theorems**, not premises. The plain
thesis theorems `trace_analysis_sound` / `reaching_global_read_sound`
(`Trace_Analysis_Sound.thy:28,63` [verified]) inherit this: they take only
`is_post_fixpoint`, `S ≤ [[s0]]`, finiteness — no `ENTRY`/`EDGE`.

The residual is precisely: **the same theorem, but read through `obs_digest` instead
of `side_env_cmp`.**

---

## 3. Why `obs_digest` is not free from §2 — *(frontier only)*

> **Scope.** §3–§5 describe the per-edge construction for **point-dependent (tight)
> readers** — the mode/RD frontier. For the **context / superset** readers this is
> obsolete: `side_cfg_T_eff_cmp_collect_ctx_sound` (§0) reaches `obs_digest` through the
> state-collecting route without any `obs_digest_edge_le`. Read §3–§5 as the plan for
> the frontier, not for the context read.

`obs_digest` is `side_env_cmp` plus the extra admitted global slots:

```isabelle
obs_digest \<sigma> (v, ctx)
   = \<sigma> (Inl (v, ctx)) \<squnion> Sup { \<sigma> (Inr g) | compatible (reader_digest v ctx) g }   -- Digest_Global_Read.thy [verified]
```

and `obs_digest \<sigma> (v,ctx) \<ge> side_env_cmp gcmp \<sigma> (v,ctx)` pointwise via
`glob_env_cmp_filter_mono` (`Digest_Global_Read.thy:88` [verified]). Direction of the
inequality decides which of `ENTRY`/`EDGE` is easy:

- **`ENTRY` / `PROC_ENTRY` — easy (monotone).** The obligation is
  `s0 ≤ obs_digest … entry`. Chain `s0 ≤ side_env_cmp … entry` (§2's
  `s0_le_side_env_cmp_entry`) with `side_env_cmp ≤ obs_digest`
  (`glob_env_cmp_filter_mono`). One `order_trans`.

- **`EDGE` — the real content.** `EDGE` reads the **source** through the *larger*
  `obs_digest`, so its hypothesis `last tr ∈ [[obs_digest σ (u,ctx)]]` is a *weaker*
  assumption than the `side_env_cmp` one — §2's edge bound does not apply verbatim.
  What is needed is a per-edge bound *at the digest read*:

  ```isabelle
  etf_full (apply_etf etf a u) (pull-of obs_digest at (u,ctx)) \<le> obs_digest \<sigma> (v, ctx)   (obs_digest_edge_le)
  ```

  Structurally the intra transfer of an edge `(u,a,v)` writes only the **single**
  writer-key slot `Inr (writer_key v)` (`side_cfg_T_eff_cmp_site`,
  `TD_Side_Eff_Cmp_Gen.thy:96` [verified]); every other admitted `Inr g` slot is a
  flow-insensitive global, **equal at `u` and `v`**. So `obs_digest_edge_le` splits:

  1. the `Inl` local part — the site generator's own edge bound
     `side_cfg_T_eff_cmp_site_edge_le` (`:411` [verified]);
  2. the writer-key `Inr` part — `side_post_solution_le_global_site` (`:399` [verified]);
  3. the **inert admitted slots** — a frame lemma: slots the *reader* admits at both
     `u` and `v` are untouched by the edge, hence carry through;
  4. the **reader shift** `reader_digest u ctx` vs `reader_digest v ctx` — the one
     genuinely family-specific step (next section).

---

## 4. The family split: `READER_EDGE`

Step 4 above is where the two families diverge, and why the discharge is a **generic
skeleton + one per-family obligation**, not a single lemma. Isolate it as

```isabelle
READER_EDGE:  "(u, a, v) \<in> edges g \<Longrightarrow>
                 { Inr g | compatible (reader_digest u ctx) g }
                   \<subseteq> { Inr g | compatible (reader_digest v ctx) g } \<union> (slots the edge writes)"
```

i.e. *every global slot the reader admits at the source is either admitted again at
the target or is the slot this edge (re)writes.*

| family | `reader_digest` behaviour on an edge | `READER_EDGE` discharge |
| --- | --- | --- |
| **ctx-collapse** (`reader_digest = ctx`, `compatible = gcmp`) | identical at `u`, `v` | `obs_digest_collapse_shape` (`Digest_Global_Read.thy:104` [verified]) rewrites `obs_digest = side_env_cmp`; **reuse §2 unchanged** |
| **mode** (single equality slot) | one admitted slot `Inr (mode …)`; edge either preserves the ghost or is the write | trivial subset (singleton); the write case is the writer-key slot |
| **RD** (reaching-def set) | **non-monotone**: a must-write *kills* a def, so `reach u ⊄ reach v` | fails at kill edges — route through the **bot-on-locals** path `combine_read_obs_le_bot` (`:338` [verified]); already the RD spine's chosen route |

The RD row is the reason the framing is a per-edge *transport* obligation, not a
monotonicity requirement (matching `DIGEST_INDEXED_READER_MIGRATION.md`: "`READER_INCL`
is **not** a monotonicity requirement"). For RD the kill edge does not satisfy the
naive subset; the honest discharge is that at a kill the source local slot is `⊥` on
the killed global, so the dropped admitted slot contributes nothing — the
`combine_read_obs_le_bot` route already in the tree.

---

## 5. Proposed construction

### 5.1 Generic skeleton (analysis- and family-independent)

New in `TD_Side_Eff_Cmp_Gen.thy` (beside `side_cfg_T_eff_cmp_collect_sound_gen`):

```isabelle
theorem obs_digest_collect_sound_gen:
  assumes stf:      "sound_effectful_transfer_framed etf fresh_frame"
    and comb_sound: "switching_combine_sound (writer_key) cmb g etf fresh_frame bot0 s0"
    and inr:        "inr_slot_locals_bot_ctx \<sigma>"       -- solution invariant, §5.3
    and inl:        "inl_slot_globals_bot_ctx \<sigma>"       -- solution invariant, §5.3
    and S_sound:    "S \<le> \<lbrakk>s0\<rbrakk>"
    and pp:         "part_post_solution (side_cfg_T_eff_cmp_site writer_key cmb g etf fresh_frame bot0 s0) x \<sigma> vars"
    and reader_edge:"\<And>u a v. (u,a,v) \<in> edges g \<Longrightarrow> READER_EDGE u a v"   -- §4, per family
    and \<dots>          -- finiteness + coverage (as §2)
  shows "cfg_collect_ctx dg cmp g S v0 ctx \<le> \<lbrakk>obs_digest \<sigma> (v0, ctx)\<rbrakk>"
```

Proof shape mirrors `side_cfg_T_eff_cmp_collect_sound_gen` line-for-line:
`post_fixpoint_sound_at_eff` at the digest read, discharging its per-edge obligation by
`obs_digest_edge_le` (§3, new), entry by the `order_trans` of §3, combine by
`comb_sound`. `reader_edge` is the only new hypothesis versus §2.

### 5.2 The load-bearing new lemma `obs_digest_edge_le` (§3)

Prove the four-way split of §3. Steps 1–2 are `[OF]` of existing site bounds; step 3 is
a `Sup`-frame lemma (global slots constant across an intra edge — provable from
`side_post_solution_le_global_site` plus the fact that `apply_etf … a u` writes only
`Inr (writer_key v)`); step 4 consumes `READER_EDGE`.

### 5.3 Solution invariants as generic post-fixpoint facts

`inr_slot_locals_bot_ctx` / `inl_slot_globals_bot_ctx` (the publish-side shape) already
have per-instance witnesses on the real solver output — `mode_INR_BOT` /
`mode_LOCAL_POST` (`Digest_Keyed_Writer_Sound.thy` [verified]), `GLOB_BOT_inst` /
`INL_GLOB_BOT` (`Reaching_Defs.thy` [verified]). Promote to one lemma over
`side_cfg_T_eff_cmp_site` so instances stop re-proving them. (For a *retain* spine use
`side_cfg_T_eff_cmp_collect_sound_gen_le` / `inl_glob_le_keyed_ctx`,
`TD_Side_Eff_Cmp_Gen.thy:1203` [verified].)

### 5.4 Per-instance closure

Each instance discharges **only** `READER_EDGE` (§4) and supplies its
`sound_effectful_transfer_framed` interpretation (Sign already has it —
`Sign_Side_Soundness.thy` [verified]):

- **ctx-collapse / mode** → `READER_EDGE` by rewrite / singleton; then
  `obs_digest_collect_sound_gen` gives the reader theorem with **no** `ENTRY`/`EDGE`
  premise.
- **RD** → `READER_EDGE` via `combine_read_obs_le_bot` at kills; the interprocedural
  residue stays `must_write_to` + `combine_backward_realizable` (already isolated,
  `DIGEST_INDEXED_READER_MIGRATION.md` B2.7–B2.9 [verified]) — untouched by this work.

---

## 6. Migration sequence

| Step | Deliverable | Depends on | Risk |
| --- | --- | --- | --- |
| S1 | `ENTRY`/`PROC_ENTRY` for `obs_digest` from `glob_env_cmp_filter_mono` + `s0_le_side_env_cmp_entry` (§3) | — | low — two `order_trans` |
| S2 | `Sup`-frame lemma: admitted `Inr` slots constant across an intra edge (§5.2 step 3) | site global bound | medium |
| S3 | `obs_digest_edge_le` combining S2 + `side_cfg_T_eff_cmp_site_edge_le` + `READER_EDGE` (§5.2) | S2 | medium |
| S4 | `obs_digest_collect_sound_gen` skeleton (§5.1), mirroring `side_cfg_T_eff_cmp_collect_sound_gen` | S1, S3 | low — copy of §2 |
| S5 | Promote solution invariants (§5.3) to generic post-fixpoint lemmas | — | low |
| S6a | **[DONE — batch-green]** superset-reader class: `side_env_cmp_le_obs_digest` + `obs_digest_collect_ctx_sound_of_cmp` reduce the `obs_digest` bound to the cmp read | — | done |
| S6b-ii | **[DONE — batch-green]** `side_cfg_T_eff_cmp_collect_ctx_sound`: premise-free ctx-collecting bound from a post-fixpoint (via `cfg_collect_ctx_le` + `side_cfg_T_eff_cmp_collect_sound`) | — | done |
| S7-mode | mode instance: point-dependent reader; `READER_EDGE` fails at reset frames (`MODE_AGREE`) — **frontier** | S3 | high — point-dependent |
| S7-RD | RD instance: `READER_EDGE` via bot-on-locals; non-monotone kill — **frontier** | S3 | high — non-monotone |
| S8 | Re-thread `Exec_Sign_*_Keyed_Run` witnesses: delete the `by eval` `EDGE`/`ENTRY` discharges, cite S6/S7 | S6b, S7 | low |

Order that survived contact with the sources: **S6a + S6b-ii (done) → S8 → S7**. S6a
closes the superset-reader class (ctx-collapse included) by reduction; S6b-ii makes the
`side_env_cmp` collecting theorem premise-free via the state-collecting route
(`cfg_collect_ctx_le`), giving that reduction a premise-free target. The point-dependent readers
(**mode, RD**) are the genuine frontier: their readers admit a tighter, non-superset key
set, so neither the monotone bridge nor `cmp_edge_sound` applies — mode additionally
hits the machine-checked-false `MODE_AGREE` at reset frames. Honest end-state if the
frontier resists: *generic ENTRY/EDGE discharge complete for point-independent
(superset) readers; point-dependent readers (mode value-projection, RD reaching sets)
carry a per-point reader-transport obligation that is a real soundness layer, not a
proof convenience.*

---

## 7. What this does and does not close

**Closes.** The `ENTRY` / `PROC_ENTRY` / `EDGE` premises on the `obs_digest` read —
today restated at `obs_digest_collect_ctx_sound`, the ctx-semantic backbone, and every
witness — become theorems of any `side_cfg_T_eff_cmp_site` post-fixpoint under
`sound_effectful_transfer_framed`. Mode and ctx families lose all three premises. The
`Exec_Sign_*` witnesses stop discharging them `by eval`.

**Does not touch** (out of scope, tracked elsewhere):

- **P1** — solver termination `side_cfg_solve_dom_eff` (`OPEN_PROBLEMS.md` P1). Orthogonal.
- **RD interprocedural summary** — `must_write_to` + `combine_backward_realizable`
  (`DIGEST_INDEXED_READER_MIGRATION.md` B2.7–B2.9). A CFG-summary obligation, not an
  `EDGE`/`ENTRY` one.
- **mode `MODE_AGREE`** — machine-checked false at callee interiors; the frame-locality
  boundary is the *scientific finding*, not a gap (`DIGEST_TWO_FAMILIES.md` §5). This
  work does not make the projection reader sound where it is honestly unsound.

---

## 8. Verification gate

Per `AGENTS.md`: I/Q inner loop (`get_diagnostics` clean on every touched theory), then
one batch build as the gate — do **not** claim done on the interactive checker.

```bash
isabelle build -v -N -d ~/afp/thys -d vendor/td-verification -D . Voblint_Formalization
```

Touched sessions: `Voblint_Analysis` (`TD_Side_Eff_Cmp_Gen`, `Digest_Global_Read`,
`Reaching_Defs`, `Value_Digest_Read`, Sign instances) and `Voblint_Formalization`
(witnesses). After green, update `DIGEST_TWO_FAMILIES.md` §6 and `OPEN_PROBLEMS.md`.

---

## 9. Pointers

| | `file:line` |
| --- | --- |
| Target premises | `Digest_Global_Read.thy:287,417` (`obs_digest_collect_ctx_sound[_bot]`) |
| Read-agnostic backbone | `TD_Side_Eff_Cmp_Sound.thy:23` (`post_fixpoint_sound_at_ctx_semantic_generic`) |
| **Template (plain read, premise-free)** | `TD_Side_Eff_Cmp_Gen.thy:1142` (`side_cfg_T_eff_cmp_collect_sound_gen`) |
| Generator edge/enter/entry bounds | `TD_Side_Eff_Cmp_Gen.thy:300,411,782,1003` |
| `obs_digest ≥ side_env_cmp` | `Digest_Global_Read.thy:88` (`glob_env_cmp_filter_mono`) |
| ctx collapse | `Digest_Global_Read.thy:104` (`obs_digest_collapse_shape`) |
| bot-on-locals route (RD kills) | `Digest_Global_Read.thy:338` (`combine_read_obs_le_bot`) |
| solution invariants (per-instance today) | `Digest_Keyed_Writer_Sound.thy`, `Reaching_Defs.thy` |
| Sign framed-transfer interpretation | `Sign_Side_Soundness.thy` |
| plain thesis theorems (no ENTRY/EDGE) | `Trace_Analysis_Sound.thy:28,63` |
