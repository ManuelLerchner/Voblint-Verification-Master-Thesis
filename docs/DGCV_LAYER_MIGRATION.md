# D/G/C/V native layer — audit and migration record

> **Status:** the context-sensitive DG migration is delivered and closed, the
> legacy `side_env_ctx` / `TD_Side_Eff_Ctx_Sound` spine is deleted, and the
> remaining notes here track the separate post-migration D/G/C/V consolidation
> that sits on top of the current DG/keyed/digest/clean architecture. This is
> the concrete record behind the one-line "next boundary" in `docs/ROADMAP.md`
> ("generalize native soundness beyond abstract-state-shaped `D`/`G`, then port
> the context/digest tower").
>
> Companions: `SPLIT_STATE_MIGRATION.md` (the completed D/G migration and its
> limitation tables), `GOBLINT_SPEC_LOCAL_GLOBAL_SEPARATION_AUDIT.md` (the Stage-0
> `call_spec` contract over the homogeneous state), `DGC_ALIGNMENT_ANALYSIS.md`
> (the M2 routing-read obstruction), `GOBLINT_SPEC_FULL_ALIGNMENT_PLAN.md`
> (gap inventory).

**Question answered here:** should the repo grow a generic D/G/C/V locale layer —
Goblint's `module D / G / C / V` `Spec` boundary — above the current
`abs_state`-typed bridge, and is there a coherent migration path? **Yes on both.**
The audit showed the four axes already existed separately; N1 and N2 then
collapsed the carrier restriction and the DG-signature gap. What remains is the
separate paper-alignment / consolidation work described below, not the retired
`side_env_ctx` spine.

---

## 0. Architectural correction (N2 pivot, 2026-07-13)

A source audit for N2 ("caller-state-dependent `enter`") found the target is
**already met at the framework level** — and on a different spine than expected.
Two parallel spines exist:

| | Spine | Carrier | `enter` shape | Instances |
| --- | --- | --- | --- | --- |
| **Legacy** | `Call_Spec` / `context_collecting_soundness` | homogeneous `abs_state` | `entry_seed :: C => D` (context-seeded) | **Sign only** |
| **Survivor** | `sound_dg_spec` (DG spine) | opaque `D`/`G` | `dgs_enter :: D => G => G x D` (**reads caller `D`**) | **Mixed** (`mixed_si`), **Retain** (`unit_dg_spec` diagonal) |

`dgs_enter` already consumes the caller's `D`, so it **already matches the FM 2026
caller-state-dependent `enter`** (eqs. 2–4). N2 is therefore not a redesign of
`enter`; it is **convergence**: move the maintained analyses onto `sound_dg_spec`
and retire the homogeneous `Call_Spec`/`entry_seed` tower.

**Dependency-cone facts driving the plan:**

* `Sign_Call_Spec` is a **dead leaf** — imported by nothing, endpoints
  (`Sign_spec.*`, `sign_spec_post_fixpoint_sound`) consumed by nothing. It is a
  demonstration that Sign fits the Goblint contract, not a maintained endpoint;
  Sign's examples ride `sign_etf` / the generic CMP path directly.
* `Call_Spec_Sound` is imported only by `Sign_Call_Spec`.
* `DG_Framework` used to import `Call_Spec_Generator` while referencing **none**
  of its names — the import only transitively pulled in the
  `Exec_Cmp_Bridge` / `TD_Side_Eff_Cmp_*` substrate. Re-pointing that import to
  the substrate directly severed the coupling and isolated the whole
  `Call_Spec` tower.
* The CMP kernel (`Exec_Cmp_Bridge`, `TD_Side_Eff_Cmp_*`) was shared substrate
  for **both** spines and stayed separate from the `Call_Spec` spec wrapper
  until the bridge retirement finished.

**Sequence:** (1) sever `DG_Framework`'s `Call_Spec_Generator` import; (2) give
Sign a native `sound_dg_spec` endpoint via the `unit_dg_spec sign_tf` diagonal,
mirroring `mixed_si`; (3) prove the Sign DG endpoint sound with unchanged
collecting-soundness statement; (4) audit Interval (DG interpretation only if it
is a maintained endpoint, not straight-line scaffolding); (5) delete the
`Call_Spec` tower (`Call_Spec`, `Call_Spec_Generator`, `Call_Spec_Sound`,
`Sign_Call_Spec`) once its cone is empty. N3 below is the delivered migration;
N4 below is the separate post-migration consolidation work.

### N2 outcome — DELIVERED (2026-07-13)

* **DG import severed.** `DG_Framework` was re-pointed away from
  `Call_Spec_Generator` and toward the CMP substrate directly (the import only
  carried the substrate). The `Call_Spec` tower became an isolated island, and
  the keyed executable bridge was later retired.
* **Sign migrated.** `src/Analysis/Instances/Sign/Sign_DG.thy`:
  `interpretation sign_dg: sound_dg_spec "unit_dg_spec sign_tf" gamma_unit`
  (discharged by `sound_dg_spec_unit[OF sign_is_sound_transfer]`), with the native
  endpoint `sign_dg_post_solution_collect_sound`
  (`cfg_collect g S0 v ⊆ sign_dg_gamma sigma v` from a generator post-solution) —
  the same collecting-soundness shape `mixed_si` proves. Sign now rides the survivor
  spine with the same caller-`D` `dgs_enter` as Mixed/Retain.
* **Executables untouched.** Sign's examples ride `sign_etf` / the generic CMP path,
  not the deleted wrapper — no executable result changed. `Sign_Call_Spec` was a dead
  leaf (imported by nothing, endpoints consumed by nothing).
* **Interval: no DG interpretation** (task 4 audit). Interval never had a `Call_Spec`
  wrapper; its straight-line endpoint is `side_ivl_analysis_sound` and its
  context-sensitive behavior is exercised through the executable CMP-seed digest
  family (seeded-clean / keyed-retain, shared substrate — kept). A native DG endpoint
  is available generically via `sound_dg_spec_unit`/`sound_dg_spec_retain` at `ivl_tf`
  if a consumer ever needs one; adding a bare `Interval_DG` mirror now would be
  consumerless scaffolding.
* **Tower deleted.** `Call_Spec.thy`, `Call_Spec_Generator.thy`,
  `Call_Spec_Sound.thy`, `Sign_Call_Spec.thy` removed; `Routing/` top level now holds
  only the `Support/` context-routing proof infrastructure (task 8 substrate,
  preserved). READMEs and `ROOT` updated.
* **Cone now empty:** no `.thy` references the deleted names; `Voblint_Analysis` +
  `Voblint_Formalization` green, no new `sorry`.

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
| Shared context backbone + DG/keyed/digest/clean | `Goblint/Read/Support/TD_Side_Eff_Ctx_Shared.thy`, `Read/Support/TD_Side_Eff_Cmp_Sound.thy`, `Read/Support/Digest_Global_Read.thy`, `Read/Support/Value_Digest_Reader.thy`, `Read/Support/TD_Side_Eff_Cmp_Gen.thy`, `Goblint/Routing/Call_Spec*.thy` | one `'a abs_state` | full (`'c`, `'g::finite`, digests, `ENTER_MONO`) | `cfg_collect_ctx` |

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

* **D/G:** done (Stages 1D + 2). Lifting R1 is a declaration change.
* **C:** `context_domain` already has the right field shapes; only the state
  type parameter moves from `'a abs_state` to an opaque `'D`.
* **V:** `global_routing_spec` is value-type-agnostic already; only its
  consumers (keyed read, kernel) need `G`-typed versions.
* **Soundness:** the homogeneous kernel
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

* `sound_dg_spec`'s three semantic assumptions survive unchanged, over
  generalized carriers.
* `ctx_sel` consumes `'D` (Goblint `context`), not `'a abs_state`. The current
  `context_domain` instances are recovered by `'D = 'a abs_state`.
* `entry_seed :: 'c => 'D` is the generator's existing `frame_seed` parameter
  (`Call_Spec`'s `entry_seed`, re-typed).
* `prep` folds into `ctx_sel` (or stays as a separate field; decide at
  implementation — Goblint's `enter` split suggests keeping it once `enter`
  grows beyond a seed).
* The digest side (`trace_context_compatibility`: `dg`, `cmp`, `entdg`) is
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

* `sound_dg_spec` over opaque carriers; `gamma_dg` / `gamma_unit` / `indep` /
  the Mixed `mixed_si_*` endpoints unchanged (they fix the carriers back to
  `abs_state`s). *Delivered — all recompile against the generalized locale.*
* **Retain natively sound:** `sound_dg_spec_retain` interprets the generalized
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
| shared context helpers (`TD_Side_Eff_Ctx_Shared.thy`) | pullback/slot invariants reused by DG, keyed, digest, clean |
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

* **Sign, Interval:** diagonal interpretations (`unit_dg_spec` /
  `indep_dg_spec` pattern, `DG_Soundness.thy:607`) with their existing keyed
  `gkey`/`gcmp` and `entry_seed`. Existing endpoints
  (`sign_spec_post_fixpoint_sound`, `side_*_analysis_sound`) become one-line
  corollaries of the N2 theorem; keep old names as aliases until consumers move.
* **Retain:** N1 interpretation + N2 for its keyed/context runs.
* **Clean / seeded-clean / activation:** Clean is an ordinary `D`/`G` analysis
  (Retain-style product `D` holding the cleaned snapshot); the
  context-dependent `entry_seed` is native in N2's generator, so the
  activation-witness plumbing shrinks to discharging `ENTER_MONO` (or the
  `point_digest` checkable condition).
* **Mixed flagship:** one analysis exercising *both* axes — mixed lattices
  (`D` = Sign locals, `G` = Interval or a may-write set) *and*
  context-sensitive routing with a precision witness the homogeneous design
  cannot state. This is the thesis-level validation.

### Stage N4 — post-migration consolidation

This is a separate cleanup project, not a blocker for the delivered migration.
Treat it as a current-source inventory plus dead-code removal pass:

1. find surviving homogeneous helpers and wrappers;
2. classify each as dead, thin adapter, real independent functionality, or
   duplicate of DG functionality;
3. delete zero-consumer leftovers;
4. thin surviving adapters to DG corollaries where possible;
5. update terminology and docs for retained adapters only.

Keep feature work separate. Caller-`D`-dependent `enter`, paper-order
call-constraint generation, keyed `V -> G` reads, and broader D/G/C/V
generalization stay in the roadmap as future feature work, not N4 cleanup.

**Current residual:** the DG-native executable examples remain; the retired
`_st` bridge and deleted legacy examples stay deleted. If a surviving
homogeneous helper still has live consumers, it belongs in the inventory below
and is handled case by case. The dead `Exec_Ctx_Bridge` executable context
mirror was deleted as part of the N4 cleanup pass.

---

## 5. What the layer buys

| Payoff | Mechanism |
| --- | --- |
| Retain (and Clean) natively sound | N1 carrier generalization |
| Mixed-domain **and** context-sensitive analyses | N2 joins the two towers |
| `ctx_sel` over `D` — Goblint's actual `context` signature | N2 re-typing; removes the last `abs_state` baked into a contract |
| A home for M2 (pre-loss routing) | opaque `D` carries routing info until `ctx_sel` reads it; no framework-forced publication loss |
| One proof tower instead of two API families | N4 consolidation only |
| Honest Goblint mapping for the thesis | `D/G/C/V` named and typed as upstream |

---

## 6. Goblint `Spec` coverage after the migration

Classification per `Spec` feature. Two reference points: the **tutorial's
`SimplifiedSpec`** (Fig. 5, the fidelity target — see §8) and the richer
`analyses.ml`. Rows marked *beyond-tutorial* are extensions past the paper's
simplified interface, not gaps in paper fidelity.

| Goblint feature | Status after the DG migration | Class |
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

## 7. Final status and post-migration note

1. **N3 is delivered**: Sign and Interval have native DG interpretations, Retain
   is natively sound on the generalized carriers, Clean / seeded-clean /
   activation derive through the DG stack, and the mixed Sign+Interval flagship
   exists; Sign and Interval both have native DG context probes, and the
   interval executable keyed regression now uses the DG-native witness
   `Exec_Ivl_Cmp_Keyed_DG_Run`.
2. **N4 is delivered**: the remaining dead executable bridge was deleted, the
   docs now describe the historical cleanup correctly, and no live `_st`-bridge
   consumer remains.
3. **Next work is consolidation, not new semantics**: caller-`D`-dependent
   `enter` is already realized by the DG witnesses, and keyed global access is
   already shown by the current read/write examples. Any further work here
   should unify those witnesses where that reduces duplication; it does not need
   a new architecture story.

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

* **The D/G split is the paper's core model.** §2: flow-sensitive local unknowns
  `L`, flow-insensitive global unknowns `G`, per-unknown domains, constraints
  producing one local result plus finitely many global side effects. That is
  exactly `Answer : D` / `Side : G` over opaque, analysis-defined carriers.
* **N1 is validated verbatim.** Fig. 5 types `module D : Lattice`,
  `module G : Lattice`, assembled "from existing building blocks — products,
  lifters, map domains" (p. 460). Retain's `D = locals × snapshot` is the named
  "product" case: a retained snapshot belongs *inside* the analysis-defined local
  domain `D`, not in framework-specific retain semantics. N1 is the correct first
  step under any paper-faithful version.
* **Unified `enter`/`combine` are paper-faithful.** Against *this tutorial's*
  `SimplifiedSpec` (Fig. 5) — not the richer `analyses.ml` — there is one `enter`
  and one `combine`. Multi-result `enter` and split `combine_env`/`combine_assign`
  are **beyond** the paper's simplified interface, not missing requirements for
  paper fidelity. Our single `dgs_enter` / `dgs_combine` match Fig. 5.
* **Digest routing follows the same refinement principle.** §4 refines both local
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

* multi-analysis product locals `∏_A D_{L,A}` / sum globals `∑_A D_{G,A}`;
* inter-analysis `man.ask` / `query`;
* threads (`threadenter`, interferences) — no concurrency model in IMP2;
* return-value handling (`combine_assign`, `lval option`) — IMP2 has no
  first-class return;
* quasi-join partial orders (§2) — we require `bounded_semilattice_sup_bot`, which
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

## 9. N5 — consolidation plan (on top of the delivered migration)

N5 is a **proof-shape consolidation** pass, not a semantics change. It starts
from the delivered DG/keyed/digest/clean witnesses and removes repeated proof
plumbing where the current tree still says the same thing in several files.

### 9.1 File order

1. `DG_Context_Soundness.thy`
2. `DG_Route_Soundness.thy`
3. `Sign_DG.thy`
4. `Interval_DG.thy`
5. `Retain_Analysis.thy`
6. `Global_Cmp_Read.thy`
7. `Digest_Global_Read.thy`
8. `Value_Digest_Reader.thy`
9. `Sign_Named_Global_Eff.thy`

### 9.2 First shared-lemma targets

Start with the DG collecting spine:

* factor the repeated post-solution-to-collecting soundness pattern around
  `dg_gamma_c` / `dg_gamma` into one reusable helper;
* keep `DG_Context_Soundness.collect_sound_reader` as the base reader lemma and
  make the per-context theorem a thin instantiation of it;
* collapse identical `dg_D_c` / `dg_G_c` / `dg_gamma_c` accessor setup where the
  same diagonal context-keying pattern is repeated.

Then move to the instance files:

* keep `Sign_DG.thy` and `Interval_DG.thy` as one-line interpretation wrappers
  plus their named endpoints;
* keep `Retain_Analysis.thy` as the only place that needs the product-carrier
  retain-specific proof shape;
* leave `Sign_Named_Global_Eff.thy` separate unless its `sideg_tree` witness can
  share a generic named-global reader lemma with `Global_Cmp_Read.thy`.

### 9.3 What not to do

* Do not change the DG semantics.
* Do not turn N5 into a new D/G/C/V interface design.
* Do not pull feature work into the cleanup pass.
* Do not touch the already-delivered `_st` retirement unless a live consumer
  appears.

### 9.4 Exit criteria

* repeated proof skeletons are factored into shared lemmas;
* instance theories are thin wrappers;
* docs and roadmap name N5 as consolidation only;
* `Voblint_Analysis` and `Voblint_Formalization` still build green;
* no new `sorry`.

### 8.6 Thesis claim

> The migration realizes the paper's central mixed-flow-sensitive constraint
> architecture — opaque flow-sensitive domain `D`, opaque flow-insensitive domain
> `G`, and side-effecting constraints — while its current procedure-call interface
> remains a restricted form that must be generalized from context-seeded entry to
> caller-state-dependent `enter`.
