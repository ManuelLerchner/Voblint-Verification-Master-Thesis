# D/G/C/V native layer — audit and migration plan

> **Status:** design + migration plan, grounded in a source audit (2026-07-13). No
> theory changes yet. This is the concrete plan behind the one-line "next
> boundary" in `docs/ROADMAP.md` ("generalize native soundness beyond
> abstract-state-shaped `D`/`G`, then port the context/digest tower").
>
> Companions: `SPLIT_STATE_MIGRATION.md` (the completed D/G migration and its
> limitation tables), `GOBLINT_SPEC_LOCAL_GLOBAL_SEPARATION_AUDIT.md` (the Stage-0
> `call_spec` contract over the homogeneous state), `DGC_ALIGNMENT_ANALYSIS.md`
> (the M2 routing-read obstruction), `GOBLINT_SPEC_FULL_ALIGNMENT_PLAN.md`
> (gap inventory).

**Question answered here:** should the repo grow a generic D/G/C/V locale layer —
Goblint's `module D / G / C / V` `Spec` boundary — above the current
`abs_state`-typed bridge, and is there a coherent migration path? **Yes on both.**
The audit shows the four axes already exist separately; what is missing is one
locale that joins them and one soundness theorem family stated over it. No
generator redesign is needed.

---

## 1. Audit: where each axis lives today

Goblint's `Spec` boundary (`src/framework/analyses.ml`):

```text
D = flow-sensitive local analysis state      (arbitrary, analysis-chosen)
G = flow-insensitive global side-effect value
C = context (keys local unknowns)
V = global constraint-variable key
```

### 1.1 D and G — native, but restricted

`dg_spec` (`src/Analysis/Generic/Solver/Context/Goblint/DG/DG_Framework.thy:221`)
is the analysis interface: per-edge-action `step :: D => G => G x D` plus the
return combine `D => D => G => G x D`. The framework never inspects `D` or `G`
(`dg_edge_tree_answer_pure_D` / `dg_edge_tree_side_pure_G`,
`DG_Framework.thy:184,188`).

The heterogeneous generator `side_cfg_T_eff_cmp_seed_dg`
(`DG_Framework.thy:311`) is **already fully C/V-polymorphic**: it takes
`gkey :: 'c => 'k`, a context-indexed combine builder
`cmb :: 'c => pp => pp => tree`, and a context-keyed frame seed
`frame_seed :: 'c => 'd`, and emits equations over unknowns `(pp x 'c) + 'k`.

The native soundness locale `sound_dg_spec`
(`Goblint/DG/DG_Soundness.thy:141`) is canonical (no homogeneous transport), but
it is narrower than the generator on four axes:

| # | Restriction | Where |
| --- | --- | --- |
| R1 | carriers fixed to `D = 'd abs_state`, `G = 'g abs_state` | `DG_Soundness.thy:142-144` |
| R2 | context erased: `dg_gen` instantiates `'c = unit` | `DG_Soundness.thy:169-176` |
| R3 | global key erased: `gkey = (%_. ())`, one `G` slot | `DG_Soundness.thy:175` |
| R4 | no procedure-entry seeding: `frame_seed = (%_. bot)`, theorem assumes no `EA_Enter` edge | `DG_Soundness.thy:176,302` |

Its endpoint is the **flat** `cfg_collect` (`dg_post_solution_collect_sound`,
`DG_Soundness.thy:572`), not the context-indexed `cfg_collect_ctx`.

The locale body uses only `<=`, `sup`, `bot` on the carriers plus the
analysis-supplied `gammaDG`; nothing in the proofs of
`dg_post_solution_postfix` / `dg_postfix_collect_sound` unfolds the
`abs_state` structure of `D` or `G`. R1 is a declaration-level restriction, not
a mathematical one.

### 1.2 C — exists, but typed over the homogeneous state

`context_domain` (`Goblint/Read/Context_Domain.thy:32`) packages
`start_context`, `prep`, `ctx_sel`, `entdg`, `cmp` — the Goblint `Spec.context`
shape. Its routing input is the homogeneous state:

```isabelle
ctx_sel :: "pp => 'c => 'a abs_state => 'c"
```

Goblint's `context : man -> fundec -> D.t -> C.t` consumes the analysis's own
`D`. Baking `abs_state` into the selector input is the clearest remaining place
where the simplified single-state model survives, and it is also what blocks the
M2 pre-loss routing read (`DGC_ALIGNMENT_ANALYSIS.md`): with an opaque `D`, an
analysis keeps routing-relevant information in `D` until `ctx_sel` reads it — no
`publish`-then-lose step forced by the framework.

### 1.3 V — exists, homogeneous

`global_routing_spec` (`Goblint/Routing/Call_Spec.thy:50`) fixes
`gkey :: 'c => 'g::finite` and `gcmp :: 'c => 'g => bool` with the law
`reads_own_slot`. The key type is already separate from the value type — but
every consumer (the `side_env_cmp` read, `pull_gk`, the CMP kernel) reads
`'a abs_state`-valued slots.

### 1.4 The two proof towers

| Tower | Files | D/G | C/V | Endpoint |
| --- | --- | --- | --- | --- |
| Native DG | `Goblint/DG/DG_Soundness.thy` | independent | `unit`/`unit` | flat `cfg_collect` |
| Homogeneous context/digest | `Goblint/Read/TD_Side_Eff_Ctx_Sound.thy`, `Read/Support/TD_Side_Eff_Cmp_Sound.thy`, `Read/Support/TD_Side_Eff_Cmp_Gen.thy`, `Goblint/Routing/Call_Spec*.thy` | one `'a abs_state` | full (`'c`, `'g::finite`, digests, `ENTER_MONO`) | `cfg_collect_ctx` |

Every context-sensitive result (Sign/Interval endpoints, keyed globals, digest
precision, seeded-clean/activation spine) lives in the second tower. The mixed
Sign/Interval analysis lives in the first. No analysis can currently be both
mixed-domain and context-sensitive.

### 1.5 Retain — the carrier casualty

`retain_dg_spec` (`Goblint/DG/Retain_Analysis.thy:447`) chooses
`D = ('a abs_state, 'a abs_state) dg_state` (locals x flow-sensitive snapshot).
That carrier is not `abs_state`-shaped, so R1 blocks it from interpreting
`sound_dg_spec`; its soundness still routes through the homogeneous retain
theorems. This is exactly the "arbitrary flow-sensitive analysis state" point of
the upstream model: `D` may be a product, and the framework must not care.

---

## 2. Verdict

A D/G/C/V layer is **not a new bridge above the `abs_state` machinery** — the
repo already committed to the opaque-D/G endpoint (`dg_spec` is the framework
boundary; `SPLIT_STATE_MIGRATION.md` records the homogeneous APIs as a legacy
family). The layer is the *completion* of that endpoint: lift the four
restrictions R1–R4 and re-type `context_domain`'s selector input from
`'a abs_state` to `D`. The generator needs no change; the work concentrates in
one locale declaration and one soundness theorem family (the heterogeneous
mirror of the CMP kernel).

Coherence check, per axis:

- **D/G:** done (Stages 1D + 2). Lifting R1 is a declaration change.
- **C:** `context_domain` already has the right field shapes; only the state
  type parameter moves from `'a abs_state` to an opaque `'D`.
- **V:** `global_routing_spec` is value-type-agnostic already; only its
  consumers (keyed read, kernel) need `G`-typed versions.
- **Soundness:** the homogeneous kernel
  (`side_cfg_T_eff_cmp_collect_ctx_sound_semantic` and the
  `collect_ctx_sound_route` re-export) is stated over ten premises that already
  separate concerns (`GOBLINT_SPEC_LOCAL_GLOBAL_SEPARATION_AUDIT.md` §6.1). Each
  premise has an evident two-gamma restatement; the digest obligations
  (`DG_INTRA/RETURN/CALLEE`) are store-trace-level and carry over verbatim.

---

## 3. Target interface

One locale joining the axes (names indicative):

```isabelle
locale dg_analysis_spec =
  fixes S          :: "('D::bounded_semilattice_sup_bot,
                        'G::bounded_semilattice_sup_bot) dg_spec"
    and gammaDG    :: "'D => 'G => store set"
    (* C: context selection over the analysis's own D *)
    and start_context :: "'c"
    and ctx_sel    :: "pp => 'c => 'D => 'c"
    and entry_seed :: "'c => 'D"
    (* V: global routing, G-valued slots *)
    and gkey       :: "'c => 'v::finite"
    and gcmp       :: "'c => 'v => bool"
  assumes gammaDG_mono: ...
    and step_sound:    "edge_collect a (gammaDG d g) <= ... dg_spec_step ..."
    and combine_sound: ...
    and reads_own_slot: "gcmp ctx (gkey ctx)"
```

Differences from today's pieces:

- `sound_dg_spec`'s three semantic assumptions survive unchanged, over
  generalized carriers.
- `ctx_sel` consumes `'D` (Goblint `context`), not `'a abs_state`. The current
  `context_domain` instances are recovered by `'D = 'a abs_state`.
- `entry_seed :: 'c => 'D` is the generator's existing `frame_seed` parameter
  (`Call_Spec`'s `entry_seed`, re-typed).
- `prep` folds into `ctx_sel` (or stays as a separate field; decide at
  implementation — Goblint's `enter` split suggests keeping it once `enter`
  grows beyond a seed).
- The digest side (`trace_context_compatibility`: `dg`, `cmp`, `entdg`) is
  already typed over `store list` / `'c` only — it composes unchanged.

The solver boundary keeps `dg_state` packing: unknowns
`(pp x 'c) + 'v`, values `('D, 'G) dg_state`. That is R2/R3 lifted with the
machinery `side_cfg_T_eff_cmp_seed_dg` already provides.

---

## 4. Migration stages

Each stage is independently green-buildable.

### Stage N1 — lift R1: generalize `sound_dg_spec` carriers — **DELIVERED (2026-07-13)**

Replaced `'d abs_state` / `'g abs_state` by
`'D::bounded_semilattice_sup_bot` / `'G::bounded_semilattice_sup_bot`
throughout `DG_Soundness.thy` (locale header + `dg_cmb`, `dg_gen`, `dg_D`,
`dg_G`, `dg_gamma`, `dg_trees`, `dg_acc`, `dg_postfix`; both theorems and all
interpretations unchanged). The proofs use only lattice operations and the
locale assumptions — the port was mechanical, no proof body changed.

**Audit result (goal item 6).** `sound_dg_spec`'s body depends on the carriers
*only* through `<=` / `\<squnion>` / `bot` (via the `dg_state` lattice instances) and the
analysis-supplied `gammaDG`. It contains no `is_global`, no `gamma_state` /
`\<lbrakk>_\<rbrakk>`, no `restrict_local`/`restrict_global`, and no reliance on the carrier
being a `vname \<Rightarrow> _` function (the `sigma` applications are solver-valuation
applications, unrelated to the carrier). `sound_domain` is not used inside the
locale; `bounded_semilattice_sup_bot` suffices. These constants appear only in
the *instances* (`gamma_unit`, `indep_dg_spec`, `gamma_retain`/`merge_dg`),
which is correct — they are analysis-side, not framework-side.

**Blocker report for N2:** none. The carrier-opacity is genuine, so N2's
context/key generalization (`ctx_sel :: ... \<Rightarrow> D \<Rightarrow> C`, keyed `V \<Rightarrow> G`) is
independent of `sound_dg_spec` and can proceed without reopening it.

**Verification.** `DG_Soundness` and `Retain_Analysis` file-clean in I/Q (0
errors); focused `Voblint_Analysis` and full `Voblint_Formalization` batch
builds both green; zero new `sorry`.

Deliverables:

- `sound_dg_spec` over opaque carriers; `gamma_dg` / `gamma_unit` / `indep` /
  the Mixed `mixed_si_*` endpoints unchanged (they fix the carriers back to
  `abs_state`s). *Delivered — all recompile against the generalized locale.*
- **Retain natively sound:** `sound_dg_spec_retain` interprets the generalized
  locale directly at `D = ('a abs_state, 'a abs_state) dg_state`,
  `G = 'a abs_state`, with joint concretization
  `gamma_retain d g = [[merge_dg d ⊔ g]]` (retain merges its two local slots
  before applying the transfer, `retain_hetero_step f d g = ... f (merge_dg d ⊔ g)`,
  so the merge-then-single-gamma form matches the analysis; monotonicity from
  `merge_state_mono`). `retain_post_solution_collect_sound` exposes the CFG
  collecting endpoint. This removes analysis-limitation #2 and
  framework-limitation #1 of `SPLIT_STATE_MIGRATION.md`. *Delivered — no
  homogeneous transport; the old `abs_state`-only locale could not accept this
  product `D`, which is the proof the generalization is real.*

Effort: low. Risk: low. No new mathematics. **Status: delivered.**

### Stage N2 — lift R2–R4: native heterogeneous context soundness

Introduce `dg_analysis_spec` (§3) and prove the heterogeneous mirror of the CMP
kernel: a `cfg_collect_ctx` bound for post-solutions of
`side_cfg_T_eff_cmp_seed_dg gkey cmb entry_seed ...` with nontrivial `'c`/`'v`,
`EA_Enter` edges seeded by `entry_seed`, and the keyed `G`-read
(`side_env_cmp`'s `G`-typed analogue).

Structure mirrors the homogeneous tower one-to-one:

| Homogeneous | Heterogeneous mirror |
| --- | --- |
| `glob_env_cmp` / `side_env_cmp` (`Read/Global_Cmp_Read.thy`) | `G`-valued keyed read over `Inr 'v` slots |
| `pull_gk` routing (`Core/TD_Side_Tree.thy`) | same, `dg_state`-valued (map lemmas exist) |
| `post_fixpoint_sound_at_ctx_semantic` (`Read/TD_Side_Eff_Ctx_Sound.thy`) | two-gamma restatement: `ENTRY`/`PROC_ENTRY`/`EDGE` over `gammaDG` |
| `CMP_SOUND` / `LOCAL_POST` (`Read/Support/TD_Side_Eff_Cmp_Sound.thy`) | combine premises over `dgs_combine` (already the `sound_dg_spec.combine_sound` shape) |
| `ENTER_MONO` + `dg_*` digest laws | unchanged store-level statements; `ctx_sel` now reads `dg_D sigma` |
| `collect_ctx_sound_route` | `dg_analysis_spec` corollary |

The `ENTER_MONO` caveat carries over: it stays a candidate-solution-level
premise (or a flat-collapse-free endpoint per the Stage-0.5 pattern in
`GOBLINT_SPEC_LOCAL_GLOBAL_SEPARATION_AUDIT.md` §8), not a locale assumption.

Effort: high — this is the load-bearing stage, comparable to the original
Ctx/Cmp kernel. Risk: moderate; the proof plan is a port of an existing proof,
not new soundness content. The one genuinely new design point is the routing
read for `ctx_sel` (joined `G`-read vs pre-loss `D`) — resolve it the M2 way:
`ctx_sel` reads `D` only, which the analysis populates, so no separate
`R_read`/`Obs` split is needed at the framework level.

### Stage N3 — migrate instances

- **Sign, Interval:** diagonal interpretations (`unit_dg_spec` /
  `indep_dg_spec` pattern, `DG_Soundness.thy:607`) with their existing keyed
  `gkey`/`gcmp` and `entry_seed`. Existing endpoints
  (`sign_spec_post_fixpoint_sound`, `side_*_analysis_sound`) become one-line
  corollaries of the N2 theorem; keep old names as aliases until consumers move.
- **Retain:** N1 interpretation + N2 for its keyed/context runs.
- **Clean / seeded-clean / activation:** Clean is an ordinary `D`/`G` analysis
  (Retain-style product `D` holding the cleaned snapshot); the
  context-dependent `entry_seed` is native in N2's generator, so the
  activation-witness plumbing shrinks to discharging `ENTER_MONO` (or the
  `point_digest` checkable condition).
- **Mixed flagship:** one analysis exercising *both* axes — mixed lattices
  (`D` = Sign locals, `G` = Interval or a may-write set) *and*
  context-sensitive routing with a precision witness the homogeneous design
  cannot state. This is the thesis-level validation.

### Stage N4 — retire the homogeneous tower

Only after N3: delete `effectful_domain_transfer`, `edge_tf_tree`,
`combine_tf_tree`, the homogeneous generator + Ctx/Cmp kernels, and the
homogeneous halves of `Call_Spec*`, keeping at most a thin
`D = G = 'a abs_state` adapter (the `unit_dg_spec` route) if it saves instance
boilerplate. Same dead-code-audit discipline as the Stage-2 cleanup
(consumer counts, then batch build).

---

## 5. What the layer buys

| Payoff | Mechanism |
| --- | --- |
| Retain (and Clean) natively sound | N1 carrier generalization |
| Mixed-domain **and** context-sensitive analyses | N2 joins the two towers |
| `ctx_sel` over `D` — Goblint's actual `context` signature | N2 re-typing; removes the last `abs_state` baked into a contract |
| A home for M2 (pre-loss routing) | opaque `D` carries routing info until `ctx_sel` reads it; no framework-forced publication loss |
| One proof tower instead of two API families | N4 |
| Honest Goblint mapping for the thesis | `D/G/C/V` named and typed as upstream |

---

## 6. Goblint `Spec` coverage after the migration

Classification per `Spec` feature. Two reference points: the **tutorial's
`SimplifiedSpec`** (Fig. 5, the fidelity target — see §8) and the richer
`analyses.ml`. Rows marked *beyond-tutorial* are extensions past the paper's
simplified interface, not gaps in paper fidelity.

| Goblint feature | Status after N1–N4 | Class |
| --- | --- | --- |
| `module D / G : Lattice`, arbitrary carriers | native | **required — delivered** |
| `module C`, `context : ... -> D.t -> C.t` | native (`ctx_sel :: pp => 'c => 'D => 'c`) | **required — delivered** |
| `module V`, `global`/`sideg` channel | `'v` key, `Side 'v G` / keyed `G`-read | **required** — single-key `step` now; keyed `V → G` reads + finite keyed writes is Phase 4 (§8.2 pt. 1) |
| `enter` (tutorial: single, caller-`D`-dependent) | `entry_seed :: 'c => 'D` (context-keyed constant) | **restricted** — Phase 2 replaces with caller-`D`-dependent `enter` (§8.3) |
| `combine` (tutorial: single, `D → D → D`) | `dgs_combine :: D => D => G => G x D` | **delivered** (paper-faithful; our G-emit is a benign superset) |
| `enter` returning `(D × D) list` (multi-path) | single result | *beyond-tutorial* — not required for paper fidelity |
| split `combine_env` / `combine_assign` | single `combine` | *beyond-tutorial* — not required for paper fidelity |
| return destinations / return value (`lval option`) | absent | **unsupported by the language** (IMP2 has no first-class return) |
| `man` / `Queries.ask`, inter-analysis queries | absent | **out of scope** (§8.4) |
| product locals `∏_A` / sum globals `∑_A` | absent | **out of scope** (single analysis) |
| `sync` events, `threadenter`, interferences | absent | **unsupported** (no concurrency model) |

---

## 7. Recommended order and immediate next step

1. **N1 now.** Cheap, mechanical, unlocks Retain, and N2 is only worth proving
   once, over the generalized carriers.
2. **N2** as the next research-scale slice (go/no-go on the two-gamma
   `PROC_ENTRY`/`CMP_SOUND` restatements early, on a minimal fragment).
3. **N3, N4** as consolidation.
4. Then the paper-alignment sequence of §8.5: caller-`D`-dependent `enter`
   (Phase 2), paper-order call-constraint generation (Phase 3), keyed `V → G`
   reads / finite keyed writes (Phase 4). These generalize the call interface
   past the restricted `entry_seed`; they are downstream of the D/G/C/V cleanup.

---

## 8. Paper alignment — Seidl, Vojdani, Erhard, Schwarz (FM 2026)

> Reference: H. Seidl, V. Vojdani, J. Erhard, M. Schwarz, *Mixed Flow-Sensitive
> Static Analysis: Engineering Modularity*, tutorial, in A. Sampaio, M. Stoelinga
> (Eds.), FM 2026, LNCS **16557**, pp. 446–470, 2026.
> DOI 10.1007/978-3-032-26220-2_22.

This is the canonical write-up of Goblint's side-effecting-constraint-system
framework and its `Spec` interface. It is the design authority for the D/G/C/V
direction of this document. **Fidelity target: the paper's formal model
(§2–§4)** — the side-effecting constraint system — *not* its OCaml engineering
surface (§6, Figs. 4–5). The paper presents both; a proof should mirror the
formal one. The `man` record (`global : 'v → 'g`, imperative `sideg : 'v → 'g →
unit`, `ask`, `context`) is sugar over the functional §2 constraint
`f : E → (E × D_[u])`, and its imperative side-effect has no faithful pure
analogue except "return a finite `'v ⇒ 'g` contribution map," which *is* the
paper's `η′`.

### 8.1 What the migration realizes (validated)

- **The D/G split is the paper's core model.** §2: flow-sensitive local unknowns
  `L`, flow-insensitive global unknowns `G`, per-unknown domains, constraints
  producing one local result plus finitely many global side effects. That is
  exactly `Answer : D` / `Side : G` over opaque, analysis-defined carriers.
- **N1 is validated verbatim.** Fig. 5 types `module D : Lattice`,
  `module G : Lattice`, assembled "from existing building blocks — products,
  lifters, map domains" (p. 460). Retain's `D = locals × snapshot` is the named
  "product" case: a retained snapshot belongs *inside* the analysis-defined local
  domain `D`, not in framework-specific retain semantics. N1 is the correct first
  step under any paper-faithful version.
- **Unified `enter`/`combine` are paper-faithful.** Against *this tutorial's*
  `SimplifiedSpec` (Fig. 5) — not the richer `analyses.ml` — there is one `enter`
  and one `combine`. Multi-result `enter` and split `combine_env`/`combine_assign`
  are **beyond** the paper's simplified interface, not missing requirements for
  paper fidelity. Our single `dgs_enter` / `dgs_combine` match Fig. 5.
- **Digest routing follows the same refinement principle.** §4 refines both local
  and global information by digests and lets global reads select compatible digest
  components. Our `gkey` / `gcmp` compatibility read is a concrete representation
  of that principle.

### 8.2 Precision caveats (do not overstate)

1. **`step :: D ⇒ G ⇒ G × D` is a restricted form, not the architectural
   ceiling.** The paper's transfer inspects a valuation over many unknowns and
   emits finitely many contributions, potentially to *multiple differently typed*
   globals. The long-term paper-aligned shape is
   ```text
   reads  : V → G          (read any global key)
   writes : finite map V G (finitely many keyed contributions)
   result : D
   ```
   i.e. the strategy-tree form `QueryG V` / `Side V G` / `Answer D`. The single-`G`
   `step` is the degenerate one-key case, sufficient for the current framework
   instance. Phase 4 below generalizes it if the DG interface cannot already
   express keyed reads and finite keyed side effects.
2. **Callee-start modeling is a difference, not a proven equivalence.** §3
   treats callee start points as *side-effected* unknowns, motivated by dynamic
   calls. We use CFG-local unknowns `(start_f, context)` with explicit
   `enter`/`combine` structure. This is a modeling difference **expected to be
   equivalent under the formalization's statically resolved call graph** — a
   correspondence argument, not yet an unconditional equivalence. Documented as a
   deliberate deviation (Phase 5), justified by static call resolution.
3. **Digest correspondence is conceptual, not formal.** §4 presents digest
   refinement as a reduced-cardinal-power-style domain `A → D_[x]`. Our
   implementation uses context-indexed locals and keyed globals with compatibility
   reads. These **implement the same refinement principle**; the formal relation
   to `A → D_[x]` has not been proved and must not be stated as "is exactly the
   reduced cardinal power construction."

### 8.3 The call-interface correction (most important roadmap change)

The paper's call model is caller-state-dependent:

```text
enter   : D_caller           → D_callee-entry     (eq. 3; arg-dependent)
combine : D_caller → D_callee-return → D_successor
context : D_caller → C → C                         (eq. 6)
```

For a context-sensitive call the context is computed from the caller local state
and current context; the callee-entry state is contributed to the callee-start
unknown; the return unknown is queried before `combine`. Therefore

```text
entry_seed : C → D
```

is only a **restricted current implementation** (a context-keyed constant frame),
**not** the final paper-aligned interface. Replacing it with caller-`D`-dependent
`enter` is the key roadmap correction. Our framework already supports the stronger
form: the `EA_Enter` edge's `dgs_enter` sees the predecessor (caller) `D`.

### 8.4 Explicitly out of thesis scope

Formal-model fidelity (§2–§4) deliberately excludes the §6 OCaml surface where the
language cannot support it or where it is a separate large effort:

- multi-analysis product locals `∏_A D_{L,A}` / sum globals `∑_A D_{G,A}`;
- inter-analysis `man.ask` / `query`;
- threads (`threadenter`, interferences) — no concurrency model in IMP2;
- return-value handling (`combine_assign`, `lval option`) — IMP2 has no
  first-class return;
- quasi-join partial orders (§2) — we require `bounded_semilattice_sup_bot`, which
  the vendored TD solver assumes; relaxing is upstream solver work.

### 8.5 Revised roadmap (supersedes §4's stage sketch downstream of N1)

1. Finish opaque-carrier / native heterogeneous soundness (**N1**, this document).
2. Replace context-only `entry_seed` with caller-`D`-dependent `enter`.
3. Generate call constraints in the paper's order:
   ```text
   caller D → enter → compute context → contribute callee-entry D
            → query callee-return D → combine → successor D
   ```
4. Generalize global access to keyed reads `V → G` and finite keyed side effects
   if the current DG interface cannot already express that.
5. Document static call resolution as the reason callee entry stays a local
   context-indexed unknown rather than the paper's dynamic-dispatch side-effected
   formulation.
6. Keep multi-analysis products/sums, queries, threads, and quasi-lattices
   explicitly out of scope.

### 8.6 Thesis claim

> The migration realizes the paper's central mixed-flow-sensitive constraint
> architecture — opaque flow-sensitive domain `D`, opaque flow-insensitive domain
> `G`, and side-effecting constraints — while its current procedure-call interface
> remains a restricted form that must be generalized from context-seeded entry to
> caller-state-dependent `enter`.
