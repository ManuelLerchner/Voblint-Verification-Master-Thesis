# Activation-separated collecting semantics — design study

Historical note: the `TD_Side_Eff_Ctx_Sound` / `side_env_ctx` spine discussed in this study has been deleted. Shared helpers now live in `TD_Side_Eff_Ctx_Shared`.

> Superseded design study. Its activation-indexed collecting alternative is not the endpoint.
> See [`ACTIVATION_LOCAL_TRACE_CONVERGENCE.md`](ACTIVATION_LOCAL_TRACE_CONVERGENCE.md) for the
> single canonical activation-local semantics.

Status: **design only, not implemented.** Source-backed analysis of the least
invasive way to unblock

```
seeded activation-aware collecting semantics  ⊆  γ(seeded solver solution)
```

for the seeded-clean context spine, whose per-obligation reductions
(`seeded_clean_edge_bound`, `seeded_clean_seed_bound`, `seeded_clean_comb_bound`,
`combine_abs_bound_sound`, `point_digest.enter_mono_kernel`) are already closed
generically but cannot be assembled against the current trace semantics.

---

## 1. The current semantics and its theorem dependencies

### 1.1 Trace witness — `EA_Enter` is folded into the generic edge rule

`src/CFG/Collecting/CFG_Collect_Trace.thy:83`

```
inductive trace_witness g S where
  entry:      v = cfg_entry g ==> s ∈ S ==> trace_witness g S v [s]
| proc_entry: (cfg_entry g, EA_Enter, v) ∈ edges g ==> s ∈ enter_state ` S
                 ==> trace_witness g S v [s]
| edge:       (u, a, v) ∈ edges g ==> trace_witness g S u tr
                 ==> edge_step a (last tr) = Some s' ==> trace_witness g S v (tr @ [s'])
| combine:    (c, ex, v) ∈ combines g ==> trace_witness g S c tau ==> trace_witness g S ex ρ
                 ==> hd ρ = enter_state (last tau)
                 ==> trace_witness g S v (tau @ tl ρ @ [<last tau|last ρ>])
```

The load-bearing fact for this study: **there is no dedicated enter rule.** A
callee entry `v` reached through a call is produced by the `edge` rule with
`a = EA_Enter`, because `edge_step EA_Enter s = Some (enter_state s)`
(`CFG_Collect_Trace.thy:41`). The enter transition is therefore indistinguishable,
at the level of the witness, from an intra assignment/assume.

`cfg_collect_trace` (`:96`), `alpha_last` (`:51`), and the interprocedural
projection `alpha_last_cfg_collect_trace_le : alpha_last (cfg_collect_trace ...) ⊆
cfg_collect ...` (`:336`) all build on this witness.

### 1.2 Context-indexed collecting

`CFG_Collect_Trace.thy:474`–`504`:

```
alpha_ctx dg cmp T c        = {last tr | tr. tr ∈ T ∧ cmp (dg tr) c}
cfg_collect_ctx dg cmp g S v c = alpha_ctx dg cmp (cfg_collect_trace g S v) c
cfg_collect_ctx_le : cfg_collect_ctx dg cmp g S v c ⊆ cfg_collect g S v   (:501)
```

The context dimension is a **whole-trace digest** filter `cmp (dg tr) c`. It never
inspects trace structure; it only classifies each complete trace.

### 1.3 The incremental-context locale — already switches context, but not the proof

`context_transfer` (`CFG_Collect_Trace.thy:522`) already threads an incremental
context through a witness:

```
trace_witness_ctx g S v c tr        (:537)
  edge: ... ==> trace_witness_ctx g S v (step_ctx c a (last tr)) (tr @ [s'])   (:543)
```

Because `step_ctx c a (last tr)` fires on **every** edge, it *may* return a fresh
callee context at `a = EA_Enter`. So a context switch at enter is already
expressible. What it buys:

* `trace_witness_ctx_imp` (`:553`): forgets to plain `trace_witness`.
* `context_step_refines_dg` (`:558`): the threaded context is `dg`-compatible,
  hence `trace_witness_ctx_last_in_cfg_collect_ctx` (`:577`) lands the last store
  in `cfg_collect_ctx`.

What it does **not** buy: a soundness proof. `trace_witness_ctx` still has a single
`edge` rule for all `a`, and the refinement obligations (`step_ok`, `comb_ok`) are
stated against the whole-trace `dg`. The analyzer-soundness induction lives
elsewhere and inducts on plain `trace_witness` (next).

### 1.4 The generic soundness theorem — uniform `DG_INTRA` over all edges

`src/Analysis/Generic/Solver/Context/TD_Side_Eff_Ctx_Sound.thy:971`,
`post_fixpoint_sound_at_ctx_semantic`, inducts on plain `trace_witness`. Its `edge`
case (`:1004`) is the crux:

```
case (edge u a v tr s')
  have ctr: cmp (dg tr) ctx  by (rule DG_INTRA[OF tr_ne edge.prems])   -- (:1007)
  have lt : last tr ∈ ⟦side_env_ctx σ (u, ctx)⟧  ...
  have     s' ∈ ⟦side_env_ctx σ (v, ctx)⟧  using EDGE ...              -- (:1009)
```

with

```
DG_INTRA: tr ≠ [] ==> cmp (dg (tr @ [s'])) ctx ==> cmp (dg tr) ctx       (:983)
EDGE:     (u,a,v) ∈ edges g ==> edge_step a (last tr) = Some s'
             ==> last tr ∈ ⟦σ(u,ctx)⟧ ==> s' ∈ ⟦σ(v,ctx)⟧               (:979)
```

Both `DG_INTRA` and `EDGE` are quantified over **all** `a`, `EA_Enter` included.
The callee point reached by an enter edge is therefore proved at the **caller's**
context `ctx` (digest stable across the edge), and its store is covered by running
the **transfer** `EDGE` at `EA_Enter`.

### 1.5 The retain instance — why it closes `cfg_collect_ctx`

`TD_Side_Eff_Ctx_Sound.thy:1041`–`1179`:

```
entry_store_dg tr    = {hd tr}                                          (:1041)
entry_store_ec ctx a = edge_collect EA_Enter ⟦a⟧                        (:1044)
entry_store_entdg s  = {enter_state s}                                  (:1047)
```

`entry_store_dg` is `{hd tr}`, **stable across every edge** including `EA_Enter`
(`entry_store_dg_intra`, `:1050`). The enter edge is discharged by `EDGE` via the
transfer, instantiated at `entry_store_edge_sound_ctx` (`:1072`), which runs
`apply_etf etf EA_Enter u` and covers `enter_state (last tr)` with `edge_collect
EA_Enter`. Result: `semantic_entry_store_ctx_analysis_sound` (`:1111`),
`cfg_collect_ctx entry_store_dg (⊆) g S v ctx ≤ ⟦side_env_ctx σ (v, ctx)⟧`.

The retain spine works because it **uses the transfer at enter**. The callee body
is indexed by the caller's entry store, and the enter transfer flows the caller
store into the callee slot.

### 1.6 The seeded generator — replaces the enter transfer with a seed

`src/Analysis/Generic/Solver/Exec/Exec_Cmp_Bridge.thy:83`:

```
side_cfg_T_eff_cmp_seed gkey cmb frame_seed g etf bot0 s0 = (λ(v, c).
   let acc0  = (if v = cfg_entry g then bot0 ⊔ restrict_local s0 else bot0)
               ⊔ (if is_frame_entry g v then frame_seed c else ⊥);
       intra = map (...) (non_enter_predecessor_list g v);   -- EA_Enter DROPPED
       comb  = map (...) (combine_predecessor_list g v)
   in ...)
```

with `is_frame_entry g v = (enter_predecessor_list g v ≠ [])` and
`non_enter_predecessor_list = filter (λ(u,a). a ≠ EA_Enter) ...`
(`src/CFG/CFG_Def.thy:216`–`223`). At a frame entry:

* the seed `frame_seed c` supplies the callee's entry abstraction at the **callee**
  context `c` (for the clean spine, `restrict_global` of the caller slot);
* the enter edge is **filtered out** of `intra`, so there is **no enter-edge
  constraint** in the equation system.

This is the R_read precision move: a clean transfer reads only the local slot, and
the seed puts the caller's globals into that slot at the callee context.

### 1.7 The exact mismatch

Assembling the closed reductions needs a digest `dg` giving a callee-entry-reaching
trace the **callee** context. But §1.1: that trace is `tau @ [enter_state (last
tau)]`, produced by the generic `edge` rule; every head/whole-trace digest
(`head_digest`, `entry_store_dg`) yields the **caller** context. The seed sits at
the callee context, so `sg (Inl (v, caller_ctx)) = ⊥`, and §1.4's uniform
`EDGE`/`DG_INTRA` at the enter edge demands `apply_tf tf EA_Enter (caller slot) ≤ ⊥`
— false. The obligation the seeded generator *can* discharge at that point is the
**seed bound** `seeded_clean_seed_bound`, not `EDGE`. The proof cannot select it
because the witness does not mark the step as an enter.

**Conclusion.** The blocker is structural in the *witness*, not the digest: the
enter transition must be a separate constructor so the soundness induction can use
a different obligation there.

---

## 2. Design options

### Option A — extend `trace_witness` with an enter/activation rule

Split the canonical `edge` rule so `EA_Enter` gets its own rule that opens a child
activation; adjust `combine` to link activations.

* Impact: touches the canonical semantics. Every consumer re-proves —
  `trace_witness_mono_initial`, `trace_witness_ext_edges`,
  `trace_witness_last_in_cfg_collect`, `alpha_last_cfg_collect_trace_le`, the
  digest refinement `trace_witness_d`, `context_transfer`, and the **retain**
  soundness `post_fixpoint_sound_at_ctx_semantic` (which relies on the uniform
  `edge` case). Also `CFG_Collect_Runs`, `Trace_Analysis_Sound`, `Mixed_Flow_Sound`,
  every `Example_*` that inducts on `trace_witness`.
* Verdict: **rejected.** Largest blast radius; contradicts "keep current
  `trace_witness` and existing theorems unchanged."

### Option B — parallel activation-aware witness + collapse *(recommended)*

Add a new inductive `trace_witness_act` beside `trace_witness`, with a **dedicated
enter rule** that switches context, an **intra rule restricted to `a ≠ EA_Enter`**,
and entry/proc_entry/combine as before. Prove a forgetful collapse
`trace_witness_act ... ==> trace_witness` (soundness anchor) and a new generic
soundness theorem by induction on `trace_witness_act`.

* Impact: purely additive. `trace_witness` and every existing theorem untouched.
  New theory + one forgetful lemma + one soundness theorem + two instances.
* Verdict: **recommended.** Matches the stated strong preference exactly.

### Option C — enrich trace elements with activation/context metadata

Change the `trace = store list` datatype to carry per-step activation/context tags.

* Impact: changes the trace *type*. `edge_step`, `alpha_last`, `edge_collect_single`,
  every digest, every projection theorem, executable code that manipulates traces —
  all re-typed. Strictly worse than A.
* Verdict: **rejected.**

### Option D — digest-only, no witness change

Keep `trace_witness`; find a stateful/context-switching `dg`/`cmp` that resets to
the callee context at enter and still satisfies the §1.4 obligations.

**Formal rejection.** `post_fixpoint_sound_at_ctx_semantic` uses one `DG_INTRA`
(`:983`) for every edge. A context-switching digest resets at enter:

```
dg (tau @ [enter_state (last tau)]) = callee_ctx ≠ dg tau = caller_ctx.
```

`DG_INTRA` at that enter edge instantiates to

```
cmp callee_ctx ctx  ==>  cmp caller_ctx ctx.
```

Take `ctx = callee_ctx` with `caller_ctx ≠ callee_ctx` and `cmp` reflexive but not
constant (any real context comparison, e.g. `(=)` or `(⊆)` on the entry-store
digest): the premise `cmp callee_ctx callee_ctx` holds, the conclusion `cmp
caller_ctx callee_ctx` fails. `DG_INTRA` is therefore unprovable for any
context-switching digest **as long as the enter step is a `DG_INTRA` step** — i.e.
as long as the witness folds enter into the generic edge rule. Reparametrizing the
digest cannot rescue it; the enter step must leave the `DG_INTRA` obligation, which
is a witness change. **Rejected, with the counterexample above.**

---

## 3. Recommended design (Option B) in detail

### 3.1 Placement

Two theories, to keep the CFG session free of solver dependencies (mirrors how the
pure `context_transfer` locale lives in `CFG_Collect_Trace`):

* `src/CFG/Collecting/CFG_Collect_Activation.thy` — the **pure** activation witness,
  parametric in an abstract context carrier; forgetful + collapse theorems. No
  solver, no domain.
* `src/Analysis/Generic/Solver/Context/Seeded_Activation_Sound.thy` — the seeded
  instantiation and the generic `⊆ γ` theorem, importing `Seeded_Clean_Ctx_Collect`
  (reductions) + `CFG_Collect_Activation`.

Alternative: add both as new locales inside `CFG_Collect_Trace.thy` beside
`context_transfer`. Same additivity; a separate file keeps the diff isolated for
review. Recommend the separate file.

### 3.2 New semantic objects (pure layer)

Parametric in a context carrier `'c`, an enter-context map, an intra-context step,
and a combine-context map — the same shape as `context_transfer`, minus the enter
fold:

```
inductive trace_witness_act ::
    "(edge_action ⇒ 'c ⇒ store ⇒ 'c)   -- stepc  (intra, a ≠ EA_Enter)
     ⇒ ('c ⇒ store ⇒ 'c)               -- enterc (callee context of an entering store)
     ⇒ ('c ⇒ 'c ⇒ 'c)                  -- combc  (return to caller context)
     ⇒ 'c                              -- seedc  (initial / proc-entry context)
     ⇒ cfg ⇒ store set ⇒ pp ⇒ 'c ⇒ trace ⇒ bool"
  for stepc enterc combc seedc g S where
  entry:      v = cfg_entry g ⟹ s ∈ S
                 ⟹ trace_witness_act ... g S v seedc [s]
| proc_entry: (cfg_entry g, EA_Enter, v) ∈ edges g ⟹ s ∈ enter_state ` S
                 ⟹ trace_witness_act ... g S v seedc [s]
| intra:      (u, a, v) ∈ edges g ⟹ a ≠ EA_Enter ⟹ trace_witness_act ... g S u c tr
                 ⟹ edge_step a (last tr) = Some s'
                 ⟹ trace_witness_act ... g S v (stepc a c (last tr)) (tr @ [s'])
| enter:      (u, EA_Enter, v) ∈ edges g ⟹ trace_witness_act ... g S u c tau
                 ⟹ trace_witness_act ... g S v (enterc c (last tau))
                       (tau @ [enter_state (last tau)])
| combine:    (cl, ex, v) ∈ combines g
                 ⟹ trace_witness_act ... g S cl c1 tau ⟹ trace_witness_act ... g S ex c2 ρ
                 ⟹ hd ρ = enter_state (last tau)
                 ⟹ trace_witness_act ... g S v (combc c1 c2)
                       (tau @ tl ρ @ [<last tau|last ρ>])
```

Derived:

```
cfg_collect_trace_act ... g S v      = {tr. ∃c. trace_witness_act ... g S v c tr}
cfg_collect_ctx_act ... g S v ctx    = {last tr | tr c. trace_witness_act ... g S v c tr ∧ c = ctx}
```

The **enter** rule is the only structural novelty: it is the `edge` rule
specialized to `EA_Enter`, but it applies `enterc c (last tau)` (a context
**switch**) instead of `stepc EA_Enter c ...`, and the soundness induction gets to
treat it separately.

### 3.3 Collapse / forgetful theorem (soundness anchor)

```
lemma trace_witness_act_imp:
  "trace_witness_act stepc enterc combc seedc g S v c tr ⟹ trace_witness g S v tr"
```

by induction: `intra`/`enter` both map to `trace_witness.edge` (enter via
`edge_step EA_Enter (last tau) = Some (enter_state (last tau))`), `combine` maps to
`trace_witness.combine`, `entry`/`proc_entry` verbatim. One-line cases. Hence

```
lemma cfg_collect_ctx_act_le_collect:
  "cfg_collect_ctx_act ... g S v ctx ⊆ cfg_collect g S v"
```

via `trace_witness_act_imp` + `trace_witness_last_in_cfg_collect`
(`CFG_Collect_Trace.thy:292`). This makes the activation collecting a genuine subset
of the real reachable set — **no fabricated semantics**.

### 3.4 The generic `⊆ γ` theorem (the unblocking theorem)

`src/Analysis/Generic/Solver/Context/Seeded_Activation_Sound.thy`:

```
theorem seeded_activation_collecting_sound:
  fixes sg :: "pp × 'c + 'g ⇒ 'a::sound_domain abs_state"
  assumes STF:   "-- transfer soundness of tf (clean_etf_of_transfer tf) --"
    and SEED_G:  "⋀c s. s ∈ ⟦sg (Inl (u, c))⟧ ⟹ (u, EA_Enter, v) ∈ edges g
                     ⟹ enter_state s ∈ ⟦frame_seed (enterc c s)⟧"      -- seed γ-soundness
    and ROUTE:   "⋀c s. s ∈ ⟦sg (Inl (u, c))⟧ ⟹ enterc c s = -- key from sg(Inl(u,c)) --"  -- point routing
    and POST:    "part_post_solution
                    (side_cfg_T_eff_cmp_seed gkey cmb frame_seed g (clean_etf_of_transfer tf) bot0 s0)
                    x sg vars"
    and COVER:   "-- (entry/edge/comb/frame-entry) ∈ vars --"
    and FIN:     "finite (edges g)" "finite (combines g)"
  shows "cfg_collect_ctx_act stepc enterc combc seedc g S v ctx ⊆ ⟦sg (Inl (v, ctx))⟧"
```

Proof by induction on `trace_witness_act`, one obligation per rule:

| rule       | discharged by |
|------------|---------------|
| `entry`/`proc_entry` | `seeded_clean_seed_bound` (order) + `S_sound`/seed γ (coverage) + `gamma_state_mono` |
| `intra` (`a ≠ EA_Enter`) | `seeded_clean_edge_bound` + `STF` edge soundness + `gamma_state_mono` |
| `enter`    | `SEED_G` (`enter_state s` covered by `frame_seed (enterc c s)`) + `seeded_clean_seed_bound` at `(v, enterc c s)` + `ROUTE`/`enter_mono_kernel` (the switched context is the seeded key) + `gamma_state_mono` |
| `combine`  | `seeded_clean_comb_bound` + `combine_abs_bound_sound` (the rehydrating combine meets the abstract bound) |

Every entry in the right column is already a closed generic theorem. The `enter`
row is where the previously-false `EDGE` obligation is replaced by `SEED_G` +
`seed_bound` — the whole point of the restructuring.

### 3.5 How the closed reductions plug in

* **EDGE** → `seeded_clean_edge_bound` (`Seeded_Clean_Ctx_Collect.thy:54`), used in
  the `intra` case, now correctly *only* for `a ≠ EA_Enter`.
* **SEED** → `seeded_clean_seed_bound` (`:89`), used in `entry`/`proc_entry`/`enter`.
* **ENTER_MONO** → `point_digest.enter_mono_kernel` (`:145`) / `enter_mono_point`
  (`Seed_EnterMono_Lift.thy:46`), supplying `ROUTE`: the switched context
  `enterc c s` equals the seeded callee key `enc (sg (Inl (u, c)) proj_var)`.
* **COMB** → `seeded_clean_comb_bound` (`Exec_Cmp_Bridge.thy:120`) +
  `combine_abs_bound_sound` (`Clean_RRead_Sound.thy`), used in `combine`.

The **one genuinely new premise** is `SEED_G` — *seed γ-soundness*: the entering
store's globals are covered by the seed at the callee context. Today only the order
half (`seeded_clean_seed_bound`) exists; `SEED_G` is the semantic-coverage half, and
it is domain-specific but small (from `restrict_global` faithfulness + point
exactness). This is exactly the "seed γ-soundness for concrete
initial/procedure-entry stores" premise the goal names.

### 3.6 Two reusable premises (goal task 1)

The `enter` case reduces to precisely two reusable premises, as required:

1. **seed γ-soundness** `SEED_G`: `enter_state s ∈ ⟦frame_seed (enterc c s)⟧`.
2. **point routing** `ROUTE`: `enterc c s` = the seeded callee key derived from
   `sg (Inl (u, c)) proj_var` (discharged by `enter_mono_kernel`).

`ENTRY`/`PROC_ENTRY`/`ENTER_MONO` are no longer raw semantic premises: they are
`seeded_clean_seed_bound` + `SEED_G` + `ROUTE`.

---

## 4. Instantiation (goal task 5)

* **Sign** — `src/Formalization/Examples/Executable/Sign/SeededClean/`. Interpret
  `point_digest` with the sign point map (already done for `enter_mono_kernel`);
  discharge `SEED_G` from the sign `restrict_global` coverage
  (`Exec_Sign_Seed_EnterMono.thy`). Produce
  `sign_seeded_cfg_collect_ctx_act ⊆ γ`.
* **Interval (recursive rehydrate)** —
  `src/Formalization/Examples/Digest/Example_Interval_Recursion_Rehydrate.thy` +
  `.../Interval/SeededClean/`. Reuse `point_ivl_gamma_exact` and
  `Exec_Ivl_Seed_EnterMono`; discharge `SEED_G` from interval `restrict_global`
  coverage. Produce the `rdiv` `⊆ γ`, replacing the current `rdiv_rehyd_rhs_dominated`
  stop with a genuine `cfg_collect_ctx_act ⊆ γ` at the return node.

Both reuse the existing post-solution witnesses (`rdiv_rehyd_solve_dom`, the sign
seeded run) unchanged — no new solver runs.

---

## 5. Impact summary

| Component | Impact |
|-----------|--------|
| `trace_witness`, `cfg_collect_trace`, `cfg_collect_ctx`, `context_transfer` | **none** (additive) |
| `CFG_Collect_Runs`, `alpha_last_*`, `trace_witness_d` | **none** |
| retain spine (`post_fixpoint_sound_at_ctx_semantic`, `semantic_entry_store_ctx_analysis_sound`) | **none** |
| compiler-correctness proofs | **none** (CFG structure untouched) |
| executable solver code (`side_cfg_T_eff_cmp_seed(_st)`) | **none** (interface untouched) |
| Sign / interval instances | **new corollaries only** |
| new code | 1 pure theory (witness + collapse), 1 soundness theory, 2 instance corollaries |

No CFG structure change, no solver-interface change, existing theorems untouched:
the additive design reuses the entire generic soundness stack. The guardrail
("stop if the additive design cannot reuse the current stack without changing solver
or CFG interfaces") is satisfied — it can.

---

## 6. Staged implementation plan (buildable commits)

1. `feat(dgc): pure activation-separated collecting witness` — new
   `CFG_Collect_Activation.thy`: `trace_witness_act`, `cfg_collect_trace_act`,
   `cfg_collect_ctx_act`, `trace_witness_act_imp`, `cfg_collect_ctx_act_le_collect`.
   Add to `src/CFG/ROOT`. Build `Voblint_CFG`. *(No soundness — pure semantics +
   collapse. Low risk.)*
2. `feat(dgc): generic seeded activation-collecting soundness` — new
   `Seeded_Activation_Sound.thy`: `seeded_activation_collecting_sound`, wiring the
   four closed reductions + `SEED_G`/`ROUTE`. Add to `src/Analysis/ROOT`. Build
   `Voblint_Analysis`. *(Medium risk — the induction assembly.)*
3. `feat(dgc): sign seeded activation-collecting soundness` — Sign `SEED_G` witness
   + `⊆ γ` corollary. Build `Voblint_Formalization`.
4. `feat(dgc): interval recursion activation-collecting soundness` — interval
   `SEED_G` witness + `rdiv` return-node `⊆ γ`, retiring `rdiv_rehyd_rhs_dominated`
   as the stopping point.
5. `docs(dgc): record activation-separated closure` — update this study to
   "implemented", update `Seeded_Clean_Ctx_Collect.thy` §Status to point at the
   closed theorem, update `OPEN_PROBLEMS.md` / `M2_DGC_RREAD_BOUNDARY_MIGRATION.md`.

Each commit is an independently green build.

---

## 7. Proof-risk assessment

* **Low — collapse `trace_witness_act_imp`.** `intra`/`enter` both reduce to
  `trace_witness.edge`; mechanical.
* **Low — `intra`/`combine` cases.** Verbatim reuse of `seeded_clean_edge_bound` /
  `seeded_clean_comb_bound` / `combine_abs_bound_sound`, already batch-green.
* **Medium — `enter` case, `SEED_G`.** The genuinely new obligation: the entering
  store's globals are covered by `frame_seed (enterc c s)`. Provable per domain from
  `restrict_global`/`restrict_local` faithfulness + point exactness, but must be
  verified against the *actual* seed shape (`restrict_global_st` of the caller slot),
  not assumed. This is where a false-abstraction slip would hide.
* **Medium — `ROUTE` / context matching.** The switched context `enterc c s` must
  equal the seeded callee key `gkey`-side. `enter_mono_kernel` gives the value
  equation on a *point* slot; the residual is showing the generator's `gkey ctx`
  routing agrees with `enterc`. Depends on the concrete `gkey`/`cmb` of each
  instance — check per domain.
* **Deferred (not needed for soundness) — completeness/faithfulness.** The reverse
  `trace_witness g S v tr ⟹ ∃c. trace_witness_act ... g S v c tr` (every reachable
  store has an activation witness at *some* context) is **not** required for the
  `⊆ γ` soundness theorem, since `enterc`/`stepc`/`combc` are total and the witness
  can always be threaded. It *is* required to claim the activation collecting equals
  the real reachable set (no precision loss). Recommend proving it as a follow-up
  (threading the canonical context along any `trace_witness` derivation —
  essentially the `context_transfer.trace_witness_ctx` construction with the enter
  split); flag as separate, higher-effort, and orthogonal to unblocking.

---

## 8. Recommendation

Adopt **Option B**: a parallel `trace_witness_act` with a dedicated context-switching
`enter` rule, a forgetful collapse to `trace_witness`, and a generic
`seeded_activation_collecting_sound` inducting on it. It is fully additive, reuses
every closed reduction, changes no CFG or solver interface, and reduces the enter
step to the two reusable premises the goal names (`SEED_G` + `ROUTE`). Options A and
C modify canonical semantics or the trace type and are rejected; Option D is
rejected with the `DG_INTRA` counterexample of §2.

The guardrail holds: the additive design reuses the current generic soundness stack
without touching the solver or CFG interfaces. Proceed to stage 1 on approval.
