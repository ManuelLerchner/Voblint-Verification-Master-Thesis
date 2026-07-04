# Design study — computing the reader digest inside the solve

> **Scope.** Research/design only. No theory changed, nothing implemented, nothing
> committed. Every claim tagged **[proven]** (batch-green in tree per the migration
> log), **[validated]** (eval/REPL this session or read directly from source), or
> **[conjectured]** (design inference, not machine-checked). Goblint-source-level
> claims are grounded in the repo's own `SEIDL_2026_GOBLINT_ALIGNMENT_MIGRATION.md`
> (which renders Seidl/Vojdani/Erhard/Schwarz, *Mixed Flow-Sensitive Static Analysis*,
> FM 2026) and are **not** verified against Goblint OCaml source — that source is not
> vendored here.

---

## 1. Current architecture

### 1.1 What actually runs

The pipeline splits cleanly into a **value solve** and a **read**:

```
IMP prog
  │  compile_prog
  ▼
CFG
  │  side_cfg_T_eff_cmp_st  (equation generator)      -- [proven]
  ▼
side-effecting equation system  (strategy_tree)
  │  TD_side_always_join_Interp_solve  (vendored TD)  -- [proven]
  ▼
solution σ : (pp × 'c) + 'g ⇒ abs_state
  │  obs_digest reader_digest compatible σ            -- [proven] read
  ▼
annotated value at (pp, ctx)
```

Unknowns carry two shapes (`src/Analysis/Generic/Solver/Digest_Global_Read.thy:80`):

- `Inl (pp, ctx)` — flow-sensitive local unknown (Goblint's `D`).
- `Inr g` — flow-insensitive global slot keyed by `'g` (Goblint's `G`).

The digest read (`obs_digest`, `Digest_Global_Read.thy:83`) is:

```
obs_digest σ (v,ctx) = σ (Inl (v,ctx))
                     ⊔ glob_env_cmp (λ_ g. compatible (reader_digest v ctx) g) ctx σ
```

i.e. the local slot joined with exactly the global slots whose key is `compatible`
with the reader's digest at that point.

### 1.2 What is already computed by the fixpoint

For the RD instance (`Exec_Sign_RD_Keyed_Solve.thy`), the equation system already
side-effects each global write to its **own def-site slot**:

```isabelle
rd_eqs RMain = Side DS1 (G↦0) (QueryL RF (Answer (G↦0)))   -- writes → Inr DS1
rd_eqs RF    = Side DS3 (G↦1) (Answer (G↦1))               -- writes → Inr DS3
```

and `TD_side_always_join_Interp_solve` computes `Inr DS1 ↦ SZero`, `Inr DS3 ↦ SPos`,
strictly separated (`slot_DS1`, `slot_DS3`, `rd_slots_strictly_separate`, all
`by eval`) **[proven]**. So the **writer-key half of the digest already lives in the
solved σ.**

### 1.3 The one thing supplied by hand

`reader_digest` = `rd_reach` (`Exec_Sign_RD_Keyed_Run.thy:58`):

```isabelle
definition rd_reach :: "pp ⇒ unit ⇒ def_site set" where
  "rd_reach p ctx = (if p = 4 then {DS1} else {DS3})"
```

A per-program constant, hand-written for the 6-node example. **This is the UX weak
point named in the task** — the "manual `reader_digest` witness."

### 1.4 What is proven around it

The kernel over `obs_digest` is analysis-independent and **[proven]** batch-green:
COMB split (`combine_case_obs_sound`), the `CMP_SOUND`/`READER_INCL` reduction
(`combine_read_obs_le`), the trace backbone (`post_fixpoint_sound_obs_digest`), the
collecting wrapper (`obs_digest_collect_ctx_sound`), and the degenerate-ctx
subsumption (`obs_digest_recovers_cmp_collect` = the existing `side_env_cmp` spine).

For the **RD instance specifically**, read soundness is **[proven] modulo exactly two
named facts** (`reaching_def_collect_sound_paths_mustwrite`):

- `must_write_to g S ex x` — a **decidable CFG-path predicate** (every path to the
  callee exit writes `x`); σ-independent, context-independent.
- `combine_backward_realizable …` (`REAL`) — a **per-digest** contract: every
  compatible callee run reaching `ex` came from a compatible caller reaching `cl`.

Critically: **the RD reader digest is a pure function of the CFG + interprocedural
must/may-write summaries. It does not read the sign values at all** (`reach_paths_sem`,
`path_rd_key`, `must_write_to` never mention `abs_state`) **[proven, by inspection]**.

---

## 2. Goblint / Seidl comparison

Now grounded in the actual `goblint/analyzer` OCaml source (`src/framework/analyses.ml`,
`src/analyses/`) **[validated: read of GitHub `master` this session]**, plus the theory
papers (Seidl FM 2026; Schwarz et al. SAS 2021, *Improving Thread-Modular*; arXiv
2511.11055, *Data Race Detection by Digest-Driven Abstract Interpretation*, Nov 2025).

### Verified against the source

- **`context : man → fundec → D.t → C.t`** (`analyses.ml`, `Spec` module type). The
  context is a projection **of the local abstract state `D.t`**, keyed to a function
  (`fundec`) — i.e. computed at calls. **This directly confirms: the Goblint context is
  a projection of `D`, not a separate analysis.** **[verified from source]**
- **`sideg : 'v → 'g → unit`** in the manager record. Transfer functions side-effect
  values of type `G.t` to global constraint variables of type `V.t` (a `SpecSysVar`).
  This is exactly our `Side k d` / `Inr g`. Globals are keyed by `V.t`, and that key is
  the partitioning knob. **[verified from source]**
- **No reaching-definitions analysis exists.** The `src/analyses/` tree has ~no
  `reachingDefs.ml` / `rd.ml` / `defUse.ml` — nothing computing classical RD.
  Concurrency-precision files are thread-id (`threadId.ml`), locksets
  (`mayLocks.ml`, `mutexAnalysis.ml`), access (`accessAnalysis.ml`), and privatization
  (`basePriv.ml`). **This confirms the user's original insight and the doc's premise:
  Goblint does not run a reaching-definitions pass to feed the value analysis.**
  **[verified from source, by absence]**

### Paper concept, not a literal code construct

- **"Digest" is a term of the theory papers, not the released analyzer** — a code search
  for `digest` in `goblint/analyzer` returns **0 matches** **[verified from source]**.
  In released code the concurrency-sensitivity the papers call a "digest" is realized
  concretely: the global constraint variable `V.t` is **partitioned by thread-id /
  lockset** inside privatization (`basePriv`), and a read consults the partition relevant
  to the reader's current `D` (its lockset / thread state). So the "compatibility
  relation on digests" is, in code, "which `V.t` partition does my current `D` let me
  read." **[verified concept location; exact partition wiring inferred, not line-quoted]**
- The paper's **reduced cardinal power** `[x]^A = A → D[x]` (reader's digest = the index
  of its own unknown, solved with everything else) is the *formal* framing the FM 2026
  paper — which this whole repo targets — uses. It is **paper-level**, not a released-code
  module. **[paper-grounded]**

### Mapping to this framework

| Goblint (source) | This framework | Status |
|---|---|---|
| `context : D.t → C.t` at calls | `context_domain.route`, `ctx_sel ∘ prep` | [proven] present |
| `sideg v g` | `Side k d` strategy-tree node | [proven] present |
| global var `V.t` (`SpecSysVar`), partitioned | `Inr g`, `'g::finite` key | [proven] present |
| read consults `D`-relevant partition | `compatible (reader_digest v ctx) g` filter | [proven] read; **reader map hand-supplied** |
| (no RD analysis) | (target: generate `reach` as a summary, not an analysis) | open — §3 |

**Takeaway (now source-backed).** The user is right. Goblint keeps the information in
`D` + context and partitioned globals, solved once; it has **no reaching-definitions
pass**. This framework already mirrors the domain-indexing half — `ctx` in `Inl`, key
`g` in `Inr`, both solved by `TD_side`. What it externalizes is the **reader-filter map**
`reader_digest`. Goblint never externalizes that: the reader's partition follows from its
own `D` at the read point. The honest gap is therefore exactly §1.3's hand-written
`rd_reach`, and the Goblint-faithful fix is to derive it (from `D`, or from a CFG
summary), not to add an analysis.

---

## 3. Candidate architectures

Notation: `σ` = solved value environment; `reach : pp × 'c → 'g set` = the reader
digest (for RD).

### Option A — status quo (`reader_digest` supplied by hand)

`rd_reach` written per program; obligations discharged by `simp` on the concrete
definition.

- **Pros.** Zero new machinery. Kernel + executable solve + soundness all
  **[proven]** today for the witness.
- **Cons.** `reach` is unchecked against the CFG — the human asserts it. Does not scale
  past toy examples; the target UX ("`value` the annotated CFG, then a soundness
  theorem") is not met because `reach` is neither generated nor connected to the program
  by anything but a hand proof.

### Option B — separate static RD summary pass (σ-independent)

Compute `reach` by a standalone dataflow/summary over the CFG, feed it as
`reader_digest`. **This is the flavor the existing theory is built for.**

- `reach_paths_sem` / `path_rd_key` already define the concrete σ-independent reader
  **[proven]**; `reaching_def_collect_sound_paths_mustwrite` discharges read soundness
  from `must_write_to` (decidable) + `REAL` **[proven]**.
- New work: (i) an **executable** RD/must-write summary producing `reach`, proven to
  realize `reach_paths_sem` (or directly to satisfy `must_write_to`); (ii) discharge
  `REAL` for the chosen context encoding.
- **Pros.** Kernel untouched. Best-supported by proven theory. `reach` becomes a checked
  CFG fact, not a hand assertion. Decidable summary → `by eval` friendly, matching the
  existing executable style.
- **Cons.** A second pass, not "one fixpoint" → **least Goblint-shaped**. Two solvers to
  maintain. `REAL` is genuinely per-instance new proof.

### Option C — co-computed product domain (reach rides the value solve)

Enrich the local unknown's domain from `abs_state` to `abs_state × 'g set`; the
`'g set` component runs the RD transfer on intra edges inside the **same** `TD_side`
fixpoint. Then instantiate `reader_digest v ctx := π₂ (σ (Inl (v,ctx)))`.

- **Kernel change?** **None** **[conjectured — see §4]**. The locale fixes
  `reader_digest :: pp ⇒ 'c ⇒ 'd` as a *free parameter*. Nothing forbids instantiating
  it, post-solve, with a projection of the (now constant) solved `σ`. The soundness
  theorems quantify `reach` and `σ` and only demand the listed obligations
  (`CALLEE_INCL`/`ENTER_MONO`/…); they never require `reach` independent of `σ`.
- **Honest caveat on coupling.** For **RD**, reach is *syntactic* — it does **not**
  depend on the sign values, so the product's two components don't interact except at
  the read. It is "one fixpoint" only cosmetically: the reach coordinate is a passenger
  lattice, not coupled to the value iteration. You still prove the same RD dataflow
  facts, now as product-solution invariants.
- **Where C is genuinely right:** the **value-carried** digests (thread mode, lockset,
  mod-count). There the reader digest *is* a projection of `D`, so co-computation is not
  cosmetic — it is the only faithful design, and it is exactly Goblint.
- **Pros.** Goblint-shaped ("everything in `D`, one solve"). Eliminates the hand
  `rd_reach`. Kernel-free (if §4 holds).
- **Cons.** Product-domain plumbing (transfer, join, code-gen for `abs_state × 'g set`).
  Reproves the RD obligations at the product level. For RD specifically, buys the "one
  fixpoint" aesthetic without real coupling.

### Option D — fold reach into the context `'c` (reduced cardinal power)

Make `'c = base_ctx × reach_coord`, so `reader_digest v ctx = snd ctx` is a projection
handled by the **existing** `obs_digest_collapse_shape` **[proven]**, and the existing
context-keyed generator solves it.

- **Verdict: rejected for the motivating problem.** Contexts are **call-only**
  (`Context_Domain.thy`, and §3 of the migration note, **[proven from the paper
  rendering]**): a non-call edge keeps the same context. But reach is **flow-sensitive**
  — nodes 4 and 7 in the flat example share one context yet need different reaches.
  Putting reach in `'c` forces `'c` to change on intra edges = the `cstep` move the note
  already demoted as **non-faithful** (it contradicts call-only). So D cannot separate
  two program points under one call context. Flow-sensitive digest info must live in the
  flow-sensitive place: the local unknown's **value** (Option C), not its **index**.

### Option D′ (cleaner discovery) — lightweight summary passenger, not a full RD analysis

The synthesis of B and C, and the honest recommendation core. Two observations collapse
the problem:

1. The **writer** half is already solved (§1.2) — def-site slots are separated in σ by
   the existing fixpoint. Nothing to add there.
2. The **reader** half reduces — **[proven]** — to `must_write_to` (a decidable CFG
   summary) + `REAL` (a per-context realizability contract). It is **not** a full value
   analysis and **not** classical iterative RD; it is a bounded CFG summary.

So the missing object is small: a decidable per-`(callee, var)` must-write bit plus the
reach-set projection. Compute it as either a tiny static pass (B-style, `by eval`) or a
passenger coordinate on the local unknown (C-style, one solve). Either way the kernel is
untouched and the hand `rd_reach` disappears.

---

## 4. Theory impact (per option)

`Δ` = change required; `—` = none. "Kernel" = `digest_global_read` + the collecting
theorems. "Bridge" = `Exec_Cmp_Bridge` executable transport.

| Concern | A | B | C | D | D′ |
|---|---|---|---|---|---|
| Generic kernel (`digest_global_read`) | — | — | — [conj.] | — | — [conj.] |
| Collecting soundness theorems | — | — | — | — | — |
| `digest_global_read` locale signature | — | — | — [conj.] | — | — |
| Executable value solver | — | — | Δ product domain | — | opt. Δ (passenger) |
| Executable transport (`Exec_Cmp_Bridge`) | — | — | Δ | — | opt. Δ |
| New executable component | — | Δ RD/must-write summary | Δ product transfer | (n/a) | Δ small summary |
| New per-instance proof | hand `reach` | `must_write_to`+`REAL` realized | product invariants ⇒ obligations | (n/a) | `must_write_to`+`REAL` |
| `reach` becomes σ-dependent | no | no | yes (projection) | no | no (RD) / yes (thread) |

**The load-bearing conjecture (all of C, D′-passenger).** *Instantiating
`reader_digest` with a projection of the already-solved constant `σ` needs no kernel
edit.* Rationale: `digest_global_read` fixes `reader_digest` at interpretation time; the
collecting theorems fix `σ` at application time; to use a projection you interpret the
locale with `reader_digest := λ p c. π (σ₀ …)` for the specific solved `σ₀`, then apply
the theorem with `sigma := σ₀`. Type-compatible, and no theorem premise asserts the two
are independent. **[conjectured]** — not yet exercised in I/Q. **First validation step
before committing to C:** in I/Q, interpret `digest_global_read` with a σ-projection
reader on the existing `rd_solution` and re-run `obs_digest_collect_ctx_sound`'s
obligations; confirm they typecheck and reduce to product-solution facts.

`compatible`, `context_domain`, and the `'g::finite` constraint are unaffected in every
option (the digest is orthogonal to context; `'g` stays abstract-finite) **[proven]**.

---

## 5. UX impact

Target workflow:

```
define IMP program
value  generated equation system
value  solved system
value  annotated CFG
theorem: executable result overapproximates collecting semantics
```

- **A.** Fails at "annotated CFG": the annotation depends on hand-written `rd_reach`, and
  the final theorem carries `reach` as an assumed constant, not a generated value.
- **B / D′.** Supports it. `value (generate_reach cfg)` yields `reach` by `eval`;
  `value (obs_digest (generate_reach cfg) σ (v,ctx))` yields the annotated value; the
  theorem instantiates `reader_digest := generate_reach cfg`, and `must_write_to` is
  `eval`-decidable. `REAL` remains a proof obligation but is context-shaped, discharged
  once per context encoding, not per program.
- **C.** Supports it most directly: `value (σ (Inl (v,ctx)))` already carries both value
  and reach; the annotated CFG is one projection, no separate `generate_reach`. The
  soundness theorem still needs the product-solution invariants proven, but there is a
  single `value`-able artifact.
- **D.** N/A (rejected).

All executable options preserve the current `by eval` discipline for the concrete
reads (`Exec_Sign_RD_Keyed_Solve` already does this) **[proven]**.

---

## 6. Risks

- **Kernel-free claim for C is unverified.** §4's conjecture is the linchpin; if a
  collecting theorem implicitly needs `reach` σ-independent (e.g. an obligation stated
  before σ is fixed), C leaks into the kernel. **Mitigation:** the I/Q validation in §4
  before any product-domain work.
- **`REAL` discharge (B/D′).** `combine_backward_realizable` is proven *consistent*
  (`combine_backward_realizable_vacuous`) but never discharged non-vacuously on a real
  CFG **[proven that it's consistent; conjectured that it's dischargeable at reasonable
  cost]**. This is the genuine open per-instance proof, independent of option.
- **Product-domain build cost (C).** `Exec_Cmp_Bridge` reshape is flagged repeatedly as
  the largest mechanical surface with metis/simp blow-up risk (migration note §12,
  build-timeout policy). Product state doubles the code-gen surface.
- **Wrong-flavor coupling.** Treating RD's syntactic digest as if it were value-carried
  (forcing C's coupling) buys nothing over B for RD, and adds domain complexity. Match
  the option to the digest: **B/D′ for syntactic (RD), C for value-carried (thread/
  lockset).**
- **Recursion.** RD over finitely many def-sites is a finite powerset lattice → no
  widening; unverified end-to-end for mutual recursion **[conjectured, migration §12]**.

---

## 7. Migration effort

Rough, relative; assumes the kernel and executable value solve stay as-is (**[proven]**
today).

| Option | Effort | Shape |
|---|---|---|
| A | 0 | keep hand `rd_reach` |
| B / D′ | **S–M** | executable must-write/reach summary (`eval`-decidable) + prove it feeds `reaching_def_collect_sound_paths_mustwrite`; discharge `REAL` once per context encoding |
| C | **M–L** | product domain `abs_state × 'g set` + transfer + `Exec_Cmp_Bridge` reshape + reprove obligations as product invariants; validate the kernel-free conjecture first |
| D | — | rejected |

The framework has already paid down most of B/D′: the reader, its soundness spine, the
executable def-site solve, and the two-layer `RUN` decomposition are all **[proven]**.
What remains for B/D′ is an executable summary + `REAL`, not a new analysis.

---

## Bottom line — is automatic RD generation necessary?

**No full reaching-definitions analysis is necessary, and no separately-designed joint
fixpoint is necessary.**

1. The **writer** side of the digest is *already* computed inside the existing solve —
   def-site slots are separated in σ by `TD_side` **[proven]**.
2. The **reader** side reduces — **[proven]** — to a *decidable CFG summary*
   (`must_write_to`) plus a *per-context realizability contract* (`REAL`). That is a
   bounded static fact, not a value analysis and not classical iterative RD.
3. The generic kernel takes `reader_digest` as a **free parameter**, so the summary can
   be delivered **either** as a small static pass (Option B/D′, kernel-free, best proof
   support, `eval`-friendly) **or** folded as a passenger coordinate into the local
   unknown's domain so it is projected out of the one solved σ (Option C, Goblint-shaped,
   kernel-free **[conjectured]**).

**Recommendation.** For the RD instance, take **Option D′**: generate the reach digest
as a small decidable CFG summary (not a full RD analysis), feed it through the already-
proven `reaching_def_collect_sound_paths_mustwrite`, and discharge `REAL` once for the
call-only context encoding. This meets the target UX with the least new proof and no
kernel change. Reserve **Option C** for the *value-carried* digests (thread mode,
locksets), where the reader digest genuinely is a projection of `D` and co-computation
is the faithful, Goblint-matching design — the same generic kernel absorbs both without
modification. Before any Option-C product-domain work, **validate the §4 kernel-free
conjecture in I/Q** on the existing `rd_solution`.

The "separate RD preprocessing analysis" the task worried about is a strawman: what the
framework needs is a bounded summary, and the generic digest kernel is already indifferent
to whether that summary arrives from a pre-pass or from the value fixpoint.
