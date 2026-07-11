# The semantic model for context-sensitive calls — decision study

Status: **decision study, no theory changes.** Companion to and supersedes the
recommendation of `ACTIVATION_SEPARATED_COLLECTING_DESIGN_STUDY.md`, which argued
"parallel because smallest patch." This study answers the sharper question the patch
framing skipped: **what is the correct semantic model**, judged by fidelity to
Goblint and by clean layering, independent of patch size.

## Verdict up front

Keep the concrete collecting semantics `trace_witness` **unchanged**, and add a
**parallel, call-only, activation-indexed refinement** that forgets back to it. This
is not the smallest patch talking — it is the correct *layering*:

* `trace_witness` is the **concrete** collecting semantics. Concrete execution of a
  call *inlines* the callee onto the caller's store sequence — there is no activation
  object in concrete semantics, only an implicit call stack in the store history.
  The current enter-as-edge rule is *exactly right* for the concrete layer.
* Goblint's activation/context structure — `(node, C)` unknowns, `C = context(D)`
  computed **only at calls** — is an **abstraction-indexing** notion, not concrete
  semantics. It belongs in a refinement layer *over* the concrete semantics, keyed
  by a per-activation context that resets at each call.

Modifying `trace_witness` to be activation-separated would push an abstraction
concern into the concrete layer, corrupting the one semantics every soundness
theorem is anchored to, and would be *less* faithful to Goblint, not more — because
Goblint, too, keeps concrete transfer (`enter`/`combine` on `D`) separate from the
context abstraction (`C = context(D)`).

---

## 1. How Goblint models procedure activations (source-backed)

From the repository's upstream audits (`DGC_ALIGNMENT_ANALYSIS.md §1`,
`ROUTE_A7_GOBLINT_CONTEXT_DESIGN_STUDY.md §1`, citing `src/framework/analyses.ml`
and `src/analyses/base.ml` by line):

* **Unknowns are `(node, context)`.** `type lv = MyCFG.node * S.C.t`
  (`constraints.ml`, `FromSpec`). The callee is solved over *its own* context's
  unknowns, a family disjoint from the caller's.
* **Context is call-only.** `Spec.context : man -> fundec -> D.t -> C.t`
  (`analyses.ml:1435`). "Goblint does **not** update contexts on ordinary CFG
  edges" (ROUTE_A7 §1). The context is selected once, at the call, from the callee
  entry state `D.t`.
* **Call entry.** `Spec.enter : ... -> (D.t * D.t) list` (`analyses.ml:1491`) returns
  `(caller_after_enter_D, callee_entry_D)`. The framework then computes
  `context man f callee_entry_D` and solves/reads the callee at
  `(return_node, callee_C)`.
* **Return.** `combine_env` / `combine_assign` (`analyses.ml:1500`) receive the
  callee context and returned `D.t` and reassemble the caller's local scope + the
  callee's effects. This is the *only* link between the two unknown families.
* **No explicit activation object.** There is no call-stack value in the constraint
  system. The context `C` *is* the activation-identity abstraction: two calls with
  the same `context(callee_entry_D)` share the callee unknowns; distinct contexts
  separate them. Recursion is handled by the fixpoint over the finite `(node, C)`
  domain, not by an activation stack.

Call-flow shape (`DGC_ALIGNMENT_ANALYSIS.md §1`):

```
caller D at call node
  -> enter          : (caller_after_enter_D, callee_entry_D)
  -> context f callee_entry_D                 : callee_C            (call-only)
  -> solve/read callee return at (ret_node, callee_C)
  -> combine_env / combine_assign(callee_C, return_D)
```

**The essential shape:** concrete transfer at the boundary is `enter` / `combine` on
`D`; the context `C` is a *derived index* computed once at the call by
`context(callee_entry_D)`, and it partitions the callee's unknowns. Activation
separation lives entirely in the *index*, computed by a call-only reset.

---

## 2. What the current Isabelle layers already model

### 2.1 Concrete collecting — `trace_witness` (inlined, correct)

`src/CFG/Collecting/CFG_Collect_Trace.thy:83`. A call is the `edge` rule at
`EA_Enter`, extending the caller trace by `enter_state (last tr)`
(`edge_step EA_Enter s = Some (enter_state s)`, `:41`). This is the **concrete**
semantics: it collects exactly the reachable store sequences, and
`alpha_last_cfg_collect_trace_le` (`:336`) certifies `alpha_last ⊆ cfg_collect`. It
has no context and needs none — it is the ground truth soundness is stated against.

### 2.2 Abstraction index — two existing mechanisms

The framework already carries the activation/context notion in refinement layers
*over* `trace_witness`, exactly where it belongs:

* **Whole-trace digest** `trace_witness_d` / `reaching_compat` / `cfg_collect_ctx`
  (`CFG_Collect_Trace.thy:351`–`504`): filters concrete traces by a digest
  `cmp (dg tr) c`. The context dimension is a *filter over concrete traces*, not a
  change to them.
* **Incremental context** `context_transfer` locale (`:522`): threads a context
  `seed_ctx`/`step_ctx`/`comb_ctx` along a witness, forgets to `trace_witness`
  (`trace_witness_ctx_imp`, `:553`), and lands in `cfg_collect_ctx`
  (`:577`). This is the closest existing analogue of Goblint's index — but its
  `step_ctx` fires on **every** edge (`:543`), which is *not* Goblint's call-only
  model.

### 2.3 The routed soundness backbone — already Goblint-faithful at COMBINE

`src/Analysis/Generic/Solver/Context/TD_Side_Eff_Cmp_Sound.thy`,
`post_fixpoint_sound_at_ctx_semantic_generic` (parametric in read `renv`/`rread` and
router `rt`), inducts on `trace_witness` and, in its **combine** case, reads the
callee exit at the **routed callee context**:

```
CMP_SOUND: ... last rho ∈ ⟦renv σ (ex, rt cl ctx (rread σ (cl, ctx)))⟧
ENTER_MONO: s ∈ ⟦renv σ (cl, ctx)⟧ ==> cmp (entdg s) (rt cl ctx (rread σ (cl, ctx)))
```

`rt cl ctx (rread σ (cl,ctx))` is documented (`:52`) as "exactly Goblint's `context`
after `enter`." `collect_ctx_sound_route` (`:443`) fixes `rt = route =
ctx_sel ∘ prep`. So the backbone **already resets the context at the call in the
combine case**, via the independent callee witness `rho` whose head is the callee
entry — for `entry_store_dg`, `dg rho = {hd rho} = {enter_state (last tau)}` is the
callee context, and `ENTER_MONO`/`DG_CALLEE` route the IH to it. This is faithful.

### 2.4 The one unfaithful spot — the ENTER edge

The **enter edge** is *not* in the combine case. It is the `edge` rule at `EA_Enter`,
handled by the uniform `EDGE` + `DG_INTRA` obligations (`:15`, `DG_INTRA` on all
edges). Two consequences:

* The trace `tau @ [enter_state (last tau)]` reaching the callee entry inline has
  **whole-trace-head** digest `{hd tau}` = **caller** context. So a callee body point
  reached by falling through the enter edge is indexed at the *caller* context.
* The **retain** instance (`entry_store_dg = {hd tr}`, stable across all edges) makes
  this sound by running the **transfer** at enter (`entry_store_ec = edge_collect
  EA_Enter`, `TD_Side_Eff_Ctx_Sound.thy:1044`). It over-approximates: the callee is
  indexed by the caller entry store, a **coarser** context than Goblint's call-only
  reset.

### 2.5 The seeded generator — Goblint-faithful, hence the mismatch

`side_cfg_T_eff_cmp_seed` (`Exec_Cmp_Bridge.thy:83`) seeds the frame entry at the
**callee** context (`frame_seed c`, `is_frame_entry`) and **drops** the enter edge
from the intra fold (`non_enter_predecessor_list`). This is the faithful Goblint
model: context resets at the call, callee indexed by `callee_C`, `enter` replaced by
the seed (`restrict_global` = Goblint's `sidel (FunctionEntry f, fc)`,
`Example_Seed_Clean_Context.thy:13`). Its precision **strictly exceeds** the retain
baseline on a global-derived split (`Example_Seed_Clean_Context.thy:74`).

**The mismatch, exactly.** The seeded index is *call-only-reset* (callee point →
callee context). The only collecting model that assigns a callee point the callee
context is one whose digest resets at enter. But a reset digest breaks the uniform
`DG_INTRA` at the enter edge:

```
dg (tau @ [enter_state (last tau)]) = callee_ctx ≠ dg tau = caller_ctx
DG_INTRA at enter:  cmp callee_ctx ctx ==> cmp caller_ctx ctx     -- FALSE (ctx := callee_ctx)
```

The retain spine dodges this by *not* resetting (whole-trace head) and using the
transfer at enter; the seeded spine cannot, because its whole point is the reset.
The reset cannot live in the `edge` rule. **The enter transition must be a dedicated
witness rule** so the induction discharges it by the seed, not by `EDGE`/`DG_INTRA`.

---

## 3. Task 1 — can `trace_witness` be made activation-aware in place?

**No, and it should not be.** Two independent reasons:

1. **Conceptual.** Activation separation is an abstraction index, not concrete
   semantics. Concrete execution inlines a call; the reachable store at a callee
   point genuinely *is* `enter_state (last tau)` extended along the caller history.
   `trace_witness` is correct as the concrete layer. Injecting a context reset into
   it would make the *concrete* semantics depend on the *abstract* context notion —
   a layering inversion. Goblint keeps them separate (`enter`/`combine` on `D` vs
   `C = context(D)`); we should too.
2. **Mechanical.** The only in-place change that helps is splitting `EA_Enter` out of
   the `edge` rule. That is a change to the canonical inductive, so every induction
   over `trace_witness` re-proves: `trace_witness_last_in_cfg_collect`,
   `alpha_last_cfg_collect_trace_le`, `trace_witness_d`, `context_transfer`, the
   routed backbone `post_fixpoint_sound_at_ctx_semantic_generic`, the retain
   `semantic_entry_store_ctx_analysis_sound`, and every `Example_*` digest witness
   (`Example_Trace_Digest_*`, `Example_Entry_Store_Context_Precision`). High cost for
   a layer that should not change.

Activation-awareness must therefore be a **parallel refinement** that forgets to the
unchanged `trace_witness`.

---

## 4. Options compared

Axes: **correctness**, **generic-solver compatibility**, **existing-proof
compatibility**, **migration cost**, **long-term maintainability**.

### Option 1 — modify `trace_witness` (split enter, add activation)

* Correctness: makes the *concrete* semantics carry an abstraction index — a layering
  inversion; the inlined concrete meaning is the correct one and would be obscured.
* Solver compat: neutral (solver already keyed by `(pp, C)`).
* Proof compat: **breaks** every induction in §3.2. All re-prove.
* Migration: high — the canonical semantics and its whole transitive theorem cone.
* Maintainability: **poor.** Two concerns (concrete run vs abstract index) fused into
  one datatype; future digests/domains inherit the fusion.
* **Rejected.**

### Option 2 — parallel call-only activation witness, forgetting to `trace_witness` (recommended)

* Correctness: concrete layer untouched and provably over-approximated
  (forgetful collapse `⊆ cfg_collect`); the new layer adds only the Goblint index.
* Solver compat: **exact** — the index is `(pp, C)` with `C` reset at the call,
  matching `side_cfg_T_eff_cmp_seed`'s `(v, c)` keys.
* Proof compat: **fully additive** — `trace_witness` and all its theorems untouched;
  reuses the four closed reductions (`seeded_clean_edge_bound`,
  `seeded_clean_seed_bound`, `seeded_clean_comb_bound` + `combine_abs_bound_sound`,
  `enter_mono_kernel`).
* Migration: one new pure theory + one soundness theory + two instances.
* Maintainability: **best.** Concrete vs index cleanly separated, mirroring Goblint's
  own `D` vs `C` split; new domains reuse the generic theorem.
* **Recommended.**

### Option 3 — redesign the digest interface (no witness change)

Make `dg`/`cmp` a call-only-reset (stateful) digest over the current `trace_witness`.

* Correctness: **impossible** against the current backbone — the reset breaks
  `DG_INTRA` at the enter edge (§2.5 counterexample). Provable only if the enter step
  leaves the `DG_INTRA` obligation, i.e. a witness change. Rejecting the witness
  change *and* the digest is contradictory.
* **Rejected**, with the §2.5 counterexample.

### Option 4 — reuse/extend `context_transfer` (framework-suggested)

`context_transfer` (`CFG_Collect_Trace.thy:522`) already threads a context and
forgets to `trace_witness`. But its `step_ctx` fires on **every** edge — not
Goblint's call-only model (ROUTE_A7 §3 explicitly rejects intra-edge context updates
as "not the Goblint model"). Reusing it as-is re-imports the non-Goblint intra-step
and still lacks the enter split.

* This is Option 2 done right: define the recommended witness as a **call-only
  sibling** of `context_transfer` — context constant on intra edges, switched only at
  the dedicated `enter` rule and restored at `combine`. Reuse its forgetful/`cfg_collect_ctx`
  bridge lemmas by analogy.
* **Folded into the recommendation** (§5) as the concrete realization.

---

## 5. Recommended design

A parallel, **call-only** activation-indexed collecting semantics that forgets to
the unchanged `trace_witness`. Context is **piecewise-constant per activation**:
untouched on intra edges (Goblint call-only), switched at the dedicated `enter` rule
to `context(callee_entry)`, restored at `combine` to the caller context — the direct
image of `enter` → `context` → `combine_env`/`combine_assign`.

### 5.1 New objects (pure layer, `src/CFG/Collecting/CFG_Collect_Activation.thy`)

```
inductive trace_witness_act ::
    "('c ⇒ store ⇒ 'c)     -- enterc  : callee context of the entering store (= context∘enter)
     ⇒ ('c ⇒ 'c ⇒ 'c)      -- combc   : caller context restored at return (= combine)
     ⇒ 'c                   -- seedc   : start context (= start_context)
     ⇒ cfg ⇒ store set ⇒ pp ⇒ 'c ⇒ trace ⇒ bool"
  for enterc combc seedc g S where
  entry:      v = cfg_entry g ⟹ s ∈ S ⟹ trace_witness_act ... g S v seedc [s]
| proc_entry: (cfg_entry g, EA_Enter, v) ∈ edges g ⟹ s ∈ enter_state ` S
                 ⟹ trace_witness_act ... g S v seedc [s]
| intra:      (u, a, v) ∈ edges g ⟹ a ≠ EA_Enter ⟹ trace_witness_act ... g S u c tr
                 ⟹ edge_step a (last tr) = Some s'
                 ⟹ trace_witness_act ... g S v c (tr @ [s'])          -- context CONSTANT
| enter:      (u, EA_Enter, v) ∈ edges g ⟹ trace_witness_act ... g S u c tau
                 ⟹ trace_witness_act ... g S v (enterc c (last tau))  -- context SWITCH (call-only)
                       (tau @ [enter_state (last tau)])
| combine:    (cl, ex, v) ∈ combines g ⟹ trace_witness_act ... g S cl c1 tau
                 ⟹ trace_witness_act ... g S ex c2 ρ ⟹ hd ρ = enter_state (last tau)
                 ⟹ trace_witness_act ... g S v (combc c1 c2)          -- context RESTORE
                       (tau @ tl ρ @ [<last tau|last ρ>])

cfg_collect_ctx_act enterc combc seedc g S v ctx = {last tr | tr. trace_witness_act ... g S v ctx tr}
```

The `intra` rule keeps `c` (call-only, faithful); the only context change is `enter`.

### 5.2 Forgetful collapse — the soundness anchor

```
trace_witness_act_imp: trace_witness_act enterc combc seedc g S v c tr ⟹ trace_witness g S v tr
cfg_collect_ctx_act_le_collect: cfg_collect_ctx_act ... g S v ctx ⊆ cfg_collect g S v
```

`intra`/`enter` both map to `trace_witness.edge`, `combine` verbatim. This certifies
the activation collecting is a genuine subset of reachable states — no fabricated
semantics; the concrete layer remains the ground truth.

### 5.3 Generic soundness (`src/Analysis/.../Seeded_Activation_Sound.thy`)

```
theorem seeded_activation_collecting_sound:
  assumes STF, POST (side_cfg_T_eff_cmp_seed ... post-solution), COVER, FIN
    and SEED_G:  s ∈ ⟦sg (Inl (u, c))⟧ ⟹ (u, EA_Enter, v) ∈ edges g
                    ⟹ enter_state s ∈ ⟦frame_seed (enterc c s)⟧          -- seed γ-soundness
    and ROUTE:   s ∈ ⟦sg (Inl (u, c))⟧ ⟹ enterc c s = <callee key from sg (Inl (u,c))>  -- point routing
  shows "cfg_collect_ctx_act enterc combc seedc g S v ctx ⊆ ⟦sg (Inl (v, ctx))⟧"
```

Induction on `trace_witness_act`, one obligation per rule:

| rule | discharged by |
|---|---|
| entry/proc_entry | `seeded_clean_seed_bound` + start coverage + `gamma_state_mono` |
| intra (`a ≠ EA_Enter`) | `seeded_clean_edge_bound` + `STF` + `gamma_state_mono` |
| **enter** | `SEED_G` (entering store covered by `frame_seed (enterc c s)`) + `seeded_clean_seed_bound` at `(v, enterc c s)` + `ROUTE`/`enter_mono_kernel` |
| combine | `seeded_clean_comb_bound` + `combine_abs_bound_sound` |

Every right-column entry is already batch-green except `SEED_G` — the one genuinely
new, domain-small premise (`restrict_global` faithfulness + point exactness). The
`enter` row is where the previously-false `EDGE` obligation is *replaced* by the seed
bound — the entire purpose of splitting the rule.

### 5.4 Faithfulness to Goblint, made precise

| Goblint | `trace_witness_act` |
|---|---|
| `enter : D → (caller_D, callee_entry_D)` | the `enter` rule; `enter_state (last tau)` is `callee_entry_D` |
| `context f callee_entry_D` (call-only) | `enterc c (last tau)`; context unchanged on `intra` |
| solve callee at `(node, callee_C)` | callee sub-derivation under `enterc c (last tau)` |
| `combine_env`/`combine_assign(callee_C, return_D)` | the `combine` rule; `combc c1 c2` restores caller context |
| `(node, context)` unknowns | `cfg_collect_ctx_act ... v ctx` ↔ solver slot `sg (Inl (v, ctx))` |
| no explicit activation object | none here either — context is the index; recursion via the finite `'c` fixpoint |

The witness is the concrete-trace image of Goblint's call protocol, one rule per
protocol step, with the concrete run delegated to the forgetful map into
`trace_witness`.

---

## 6. Rejected alternatives (summary)

* **Modify `trace_witness`** — layering inversion (abstraction index into concrete
  semantics) + breaks the whole `trace_witness` theorem cone. §4 Option 1.
* **Digest-only redesign** — impossible: a call-only-reset digest breaks `DG_INTRA`
  at the enter edge (§2.5 counterexample). §4 Option 3.
* **Reuse `context_transfer` unchanged** — its every-edge `step_ctx` is explicitly
  non-Goblint (ROUTE_A7 §3) and lacks the enter split; the recommendation is its
  call-only, enter-split sibling. §4 Option 4.
* **Enrich the `trace` datatype with metadata** — changes `trace = store list`
  itself; re-types `edge_step`, `alpha_last`, every digest and projection. Strictly
  worse than modifying the witness.

---

## 7. Exact implementation plan (if adopted)

Buildable, independently green commits:

1. `feat(dgc): call-only activation-indexed collecting witness` — new
   `src/CFG/Collecting/CFG_Collect_Activation.thy`: `trace_witness_act`,
   `cfg_collect_ctx_act`, `trace_witness_act_imp`, `cfg_collect_ctx_act_le_collect`.
   Add to `src/CFG/ROOT`. Build `Voblint_CFG`. *(Pure semantics + collapse; low
   risk.)*
2. `feat(dgc): generic seeded activation-collecting soundness` — new
   `src/Analysis/Generic/Solver/Context/Seeded_Activation_Sound.thy`:
   `seeded_activation_collecting_sound`, wiring the four closed reductions +
   `SEED_G`/`ROUTE`. Add to `src/Analysis/ROOT`. Build `Voblint_Analysis`. *(Medium
   risk — the induction assembly.)*
3. `feat(dgc): sign seeded activation-collecting soundness` — Sign `SEED_G` witness
   (from `Exec_Sign_Seed_EnterMono`) + `point_digest` interpretation; corollary
   `sign_seeded_cfg_collect_ctx_act ⊆ γ`. Build `Voblint_Formalization`.
4. `feat(dgc): interval recursion activation-collecting soundness` — interval
   `SEED_G` witness (from `Exec_Ivl_Seed_EnterMono` / `point_ivl_gamma_exact`) +
   `rdiv` return-node `cfg_collect_ctx_act ⊆ γ`, retiring `rdiv_rehyd_rhs_dominated`
   as the stopping point.
5. `docs(dgc): record activation-semantics closure` — update this study and
   `ACTIVATION_SEPARATED_COLLECTING_DESIGN_STUDY.md` to "implemented", replace the
   `Seeded_Clean_Ctx_Collect.thy §Status` blocker with a pointer to the closed
   theorem, update `OPEN_PROBLEMS.md` / `M2_DGC_RREAD_BOUNDARY_MIGRATION.md`.

Optional follow-up (not needed for soundness, higher effort): the completeness
direction `trace_witness g S v tr ⟹ ∃ctx. trace_witness_act ... g S v ctx tr` (every
reachable store carries a canonical activation context), giving
`cfg_collect_ctx_act = cfg_collect_ctx dg cmp` for the induced call-only digest —
the exact bridge between the new layer and the `cfg_collect_ctx` contract. Defer.

### Proof-risk

* Low: forgetful collapse; intra/combine cases (verbatim reuse of batch-green
  reductions).
* Medium: `SEED_G` per domain — must be verified against the real
  `restrict_global_st` seed shape, not assumed (false-abstraction guard). `ROUTE` /
  `enterc`–`gkey` agreement is per-instance; `enter_mono_kernel` supplies the value
  equation on a point slot, leaving only the routing-key identity.
* Deferred: completeness (§7 optional) — the reverse direction; orthogonal to
  soundness.

## 8. Bottom line

The correct model is a **parallel, call-only, activation-indexed refinement** over an
**unchanged** `trace_witness`. It is architecturally preferable *not* because it is
the smaller patch but because it respects the same concrete-vs-context separation
Goblint itself is built on: concrete transfer (`enter`/`combine` on `D`, = the
inlined `trace_witness`) is one layer; the call-only context index (`C =
context(D)`, = `trace_witness_act`) is another. The existing routed backbone already
proves this separation is right — it resets context at the call in the combine case
and is faithful there; the only gap is the enter edge, which the dedicated `enter`
rule closes. Changing the concrete semantics would fuse two layers Goblint keeps
apart; the parallel refinement keeps them apart, which is why it is the cleaner
long-term design.
