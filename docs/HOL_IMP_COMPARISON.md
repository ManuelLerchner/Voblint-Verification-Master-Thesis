# Comparison with HOL-IMP abstract interpretation

How this repository’s Voblint-shaped pipeline relates to Tobias Nipkow’s abstract
interpretation development in Isabelle’s
[HOL-IMP session](https://isabelle.in.tum.de/library/HOL/HOL-IMP/) (`Collecting`,
`ACom`, `Abs_Int0`–`Abs_Int3`, `Abs_State`, `Abs_Int2_ivl`, …).

Related: `docs/OPEN_PROBLEMS.md`, `docs/PROOF_OVERVIEW.md`.

---

## Same mathematical goal

Both prove **sound abstract interpretation w.r.t. collecting semantics**:

- define concrete **collecting** (sets of stores, or store sets at program points);
- define abstract transformers linked by **γ** (concretization);
- prove **concrete ⊆ γ(abstract)** (possibly at every program point).

The difference is **where** fixpoints live, **how** domains plug in, and **what**
computes the abstract result.

---

## Workflow comparison

| Aspect                         | HOL-IMP `Abs_*`                                                                                     | This repository                                                                                         |
| ------------------------------ | --------------------------------------------------------------------------------------------------- | ------------------------------------------------------------------------------------------------------- |
| **Source language**            | Standard IMP (`Com`)                                                                                | IMP2 (extended `aexp`/`bexp`; hybrid wrap over HOL-IMP)                                                   |
| **Program shape for analysis** | **`acom`** : annotated command tree (`SKIP {S}`, `IF … THEN {P1} C1 …`)                             | Plain **`com`** + compiled **`cfg`** (`cfg_entry`, `cfg_exit`, `cfg_edges`)                             |
| **Collecting semantics**       | `CS c = lfp c (step UNIV)` on **annotated commands**; `step` pushes **store sets** through the tree | **`cfg_collect`** on CFG program points; path form `cfg_edges_collect`; exit sugar **`runs_to`** |
| **Abstract analysis**          | `AI c = pfp (step' ⊤) (bot c)` : Kleene iteration **on the same `acom` shape**                      | `rhs` / `make_rhs_tree` on CFG; **`td_analyse`** (vendored TD solver) → `env :: pp ⇒ abs_state`         |
| **Main soundness theorem**     | `AI_correct`: `AI c = Some C ⟹ CS c ≤ γ_c C`                                                        | **`pipeline_invariant_sound`** / **`pipeline_sound_path`**: `cfg_collect ⊆ γ ∘ env`; exit via **`pipeline_sound_runs_to`** |
| **Solver**                     | Built-in **`pfp`** / `while_option` in Isabelle                                                     | **Separate verified session** (`TD`); we prove `td_analyse_collect_sound_at` (per-pp, Fix B)           |
| **CFG / equation system**      | None : control flow is implicit in recursive `Step` / `step'`                                       | **Central** : matches Voblint compile → eqsys → solve. `cfg` extends AFP `Dijkstra_Shortest_Path.Graph` |
| **Intervals / widening**       | Worked out in-session (`Abs_Int2_ivl`, `Abs_Int3`)                                                  | Started (`Interval_Domain.thy`); stretch goal; code notes possible reuse of `Abs_Int2_ivl`              |
| **“Run analysis”**             | `AI` + `show_acom` inside Isabelle                                                                  | `run_analysis` / `td_analyse`; full `value` on maps still limited (`Example_Sign_Analysis.thy`)         |

---

## Architecture (side by side)

```text
HOL-IMP (Nipkow)                    Voblint formalization
─────────────────                   ─────────────────────

com ──annotate──► acom              com ──to_cfg──► cfg (pp, edges)
       │                                    │
       ▼                                    ▼
CS = lfp(step) on acom              cfg_collect (lfp on pp)
       │                                    │
       ▼                                    ▼
AI = pfp(step') on acom             env = td_analyse(rhs tree)
       │                                    │
       └─ AI_correct: CS ≤ γ_c C    └─ post_fixpoint_sound:
                                         cfg_collect ≤ γ ∘ env
```

**HOL-IMP:** soundness = abstract `step'` on **annotated commands** refines concrete
`step`; computation = **`pfp` in Isabelle**.

**Here:** soundness = TD solver’s **post-fixpoint** on a **CFG equation system**
refines **`cfg_collect`**; computation = **`td_analyse`** (verified externally).

---

## What is proved once vs per domain

### HOL-IMP

| Once (generic)                           | Per domain                                                                                  |
| ---------------------------------------- | ------------------------------------------------------------------------------------------- |
| `AI_correct`, `step_step'`, `pfp` theory | Instantiate `Gamma_semilattice` / `Val_lattice_gamma`: `aval'`, `plus'`, … correct w.r.t. γ |
| Collecting `CS`, `step` on `acom`        | Prove `gamma_Step_subcomm` / monotonicity for `step'`                                       |
|                                          | Run `AI` (executable for many domains)                                                      |

### This repository

| Once (generic)                                                                                  | Per domain                                                                                     |
| ----------------------------------------------------------------------------------------------- | ---------------------------------------------------------------------------------------------- |
| `pipeline_invariant_sound`, `pipeline_sound_path`, `post_fixpoint_sound`, `post_fixpoint_sound_at`, `td_analyse_collect_sound_at` | `interpretation … abstract_domain` (or `sound_domain` axioms) |
| CFG bridge, TD interface                                                                        | **`domain_transfer_sound`** (assign / assume / assume-not on CFG edges)                        |
|                                                                                                 | `analysis_config` + init in γ (`s ∈ γ_state (ac_init cfg)`)                                    |
|                                                                                                 | TD: `⋀v. TD_plain.solve_dom` on `make_rhs_tree (to_cfg c) …` (P1 only; P2 removed)            |

You do **not** re-prove the pipeline chain per domain; you discharge obligations and
apply `pipeline_invariant_sound` / `sign_pipeline_sound` (as in `voblint_sign_sound`).

HOL-IMP does **not** separate edge transfer functions : assignment and guards are
wired into `step'` on `acom`. We match **Voblint edge kinds** (`EA_Assign`,
`EA_Assume`, `EA_AssumeNot`) explicitly.

---

## Domain theory: minimal `sound_domain` vs HOL-IMP’s lattice + `st`

### What HOL-IMP uses

- **Type classes** on abstract values: `order`, `semilattice_sup`, `semilattice_sup_top`, later `bounded_lattice`, `wn` (widen/narrow).
- **Quotient type `st`**: abstract store as list rep modulo equality, lifted `fun`, `update`, order pointwise : avoids “function space” issues and gives executable structure.
- **Full lattice structure** on values: ⊔, ⊓, ⊤, ⊥ with lemmas like `gamma_inf` (γ commutes with meet).
- **Locales** `Gamma_semilattice`, `Val_lattice_gamma`, `Abs_Int`, `Abs_Int_mono` tying γ to `step'` on `acom`.
- **Backward analysis** (`Abs_Int2`): refinement / inverse operators for tighter abstract arithmetic.

### What we use

- **`sound_domain` locale** (`Abstract_Domain.thy`): γ, `join_op`, bot; axioms
  `gamma_bot`, `gamma_mono`, join upper bounds, commutativity, associativity.
- **`abs_state = vname => 'a`** globally; joins lifted pointwise (`join_state`).
- **`abstract_domain`** extends with **widening** (for interval stretch / `TD_Widen_Interface`).
- **`domain_transfer`** record + **`domain_transfer_sound`** : edge transformers
  separate from the locale.
- Soundness theorems need only **semantic** over-approximation (γ-monotone join,
  transfer preserves γ), not full syntactic lattice laws on the generic locale.

### What we gain by staying minimal

| Benefit                                     | Why it matters here                                                                                   |
| ------------------------------------------- | ----------------------------------------------------------------------------------------------------- |
| **Smaller proof obligations for soundness** | `post_fixpoint_sound` / `pipeline_invariant_sound` do not need ⊓, ⊤, or `st` quotient theory.                   |
| **Alignment with TD solver API**            | TD expects `join`, `bot`, optional `widen` on **`abs_state` maps** : same shape as `analysis_config`. |
| **Voblint-shaped edges**                    | Transfer bundle matches CFG `edge_action`; not forced into Nipkow’s `Step` on `acom`.                 |
| **Independent of IMP syntax details**       | No `acom` annotations, no `strip`/`annotate`/`asize` bookkeeping.                                     |
| **Clear thesis story**                      | “User supplies γ + join + transfers” is one table; pipeline proof is separate.                        |

### What we would gain by adopting HOL-IMP-style domain theory

| Potential gain                      | Detail                                                                                                                                                              |
| ----------------------------------- | ------------------------------------------------------------------------------------------------------------------------------------------------------------------- |
| **Reuse of proved interval domain** | `Abs_Int2_ivl` has interval arithmetic, order, and γ lemmas. Adapting `eint` + quotient `ivl` to our `Fin` intervals could shorten `Interval_Domain.thy`.           |
| **Widening/narrowing theory**       | `Abs_Int3` proves widening axioms and iteration termination for `ivl`. Relevant to interval stretch (P6/P7 in `OPEN_PROBLEMS.md`; `widen_ivl_terminates` proved in-tree).        |
| **Meet (⊓) for precision**          | `Val_lattice_gamma` gives γ(`a1 ⊓ a2`) = γ(a1) ∩ γ(a2). Useful for backward refinement; our forward-only pipeline does not require meet for soundness.              |
| **Executable abstract stores**      | Quotient `st` + `fun_rep` is tuned for code generation. Would help with the P9 (executable end-to-end) story.                                                       |
| **Backward / invariant reasoning**  | `Abs_Int2` inverse operators give assume-refinement that we currently encode only via forward `tf_assume` / `tf_assume_not`.                                        |

### What we would pay

| Cost                                     | Detail                                                                                                                                                              |
| ---------------------------------------- | ------------------------------------------------------------------------------------------------------------------------------------------------------------------- |
| **Representation mismatch**              | Nipkow’s `st` and `acom` do not match `cfg` + `pp => 'a abs_state` without a substantial adapter layer.                                                             |
| **Stronger axioms than soundness needs** | Proving full lattice laws for every new domain is more work than `sound_domain` + transfers.                                                                        |
| **Two parallel proof styles**            | Mixing `step'` on `acom` with `rhs` on CFG risks duplicate maintenance unless one is derived from the other.                                                        |
| **Session / import weight**              | Pulling `HOL-IMP.Abs_Int2_ivl` into `Voblint_Formalization` adds dependencies and notation clashes (`top`, `bot`, `dom` are hidden in `Abs_Int_init` for a reason). |

### Pragmatic recommendation

- **Keep `sound_domain` + `domain_transfer_sound`** for the main thesis chain
  (CFG → eqsys → TD → `pipeline_invariant_sound`).
- **Cherry-pick from HOL-IMP** where it saves proof effort:
  - interval value operations and γ-lemmas from `Abs_Int2_ivl` (with a thin
    mapping layer), rather than re-proving interval arithmetic from scratch;
  - widening laws from `Abs_Int3` when finishing interval widening integration
    (`TD_Widen_Interface` / P6–P7).
- **Do not** replace the CFG pipeline with `acom` + `AI` unless the thesis
  explicitly claims equivalence to the textbook presentation : that would be a
  different formalization goal (annotation-centric vs Voblint-centric).

---

## Collecting semantics shape

|                       | HOL-IMP                                                                     | Here                                                                        |
| --------------------- | --------------------------------------------------------------------------- | --------------------------------------------------------------------------- |
| **Granularity**       | One annotated command: information at **every annotation index** on the AST | **Program points** on the CFG (`pp = nat`)                                  |
| **Exit vs point-map** | Soundness compares whole `CS c` to `γ_c C` on the tree                      | **`pipeline_invariant_sound`**: every reachable `v`; exit is `v = cfg_exit` |
| **While loops**       | Fixpoint inside `step` on `acom`                                            | `cfg_collect` fixpoint on the compiled CFG                                  |

---

## When the two approaches feel the same

- Instantiating a locale **does not** automatically export a top-level theorem :
  you still write a corollary (`voblint_sign_sound` / `AI_correct` application).
- **Transfer / step correctness** is always domain-specific (HOL-IMP: `aval'_correct`;
  us: `assign_*_sound`, `assume_*_sound`).
- Both separate **“framework sound once”** from **“this lattice + these ops are correct”**.

---

## References in this repo

| Topic                   | Location                                                         |
| ----------------------- | ---------------------------------------------------------------- |
| Expression evaluation   | `src/IMP2/IMP2_Expr.thy` (`aval`/`bval`, leaf cases via HOL-IMP)  |
| Small-step semantics    | `src/IMP2/IMP2_Proc.thy` (`pstep`, frame-stack; procedural)      |
| CFG collecting + bridge | `src/CFG/Collecting/` (`CFG_Runs_To_Bridge.thy` entry)           |
| Minimal domain locale   | `Domains/Abstract_Domain.thy`                                    |
| Sign instantiation      | `Domains/Sign_Domain.thy`                                        |
| Interval + HOL-IMP note | `Domains/Interval_Domain.thy` (comment on `Abs_Int2_ivl`)        |
| Generic pipeline        | `Pipeline/Pipeline.thy`                                          |
| Sign end-to-end         | `Voblint_Formalization.thy` (`voblint_sign_sound`)               |
