# Migration — local edge trees and generic effectful soundness

Status: **CORE COMPLETE** (2026-06-30). `local_edge_tree`,
`etf_collecting_full`, `inr_slot_locals_bot`, generic effectful-transfer
factories, RHS-generator locales, Sign/Interval instances, named-global
soundness, and unit executable transport build green through
`Voblint_Formalization`. Step 9 remains a deferred refinement for executable
local trees, not a blocker for the current migration.

Related: `docs/EFFECTFUL_TF_MIGRATION.md` (effectful transfer record),
`docs/TD_SIDE_ONLY_MIGRATION.md` (side solver spine).

---

## 1. Problem

### 1.1 What we optimized

For edges that neither read nor write globals, `unit_edge_tree` always performs
`QueryL` **and** `QueryG`. That is unnecessary solver work. `local_edge_tree`
queries only the source local unknown; global information is restored via
`etf_collecting_full t σ = etf_full t σ ⊔ glob_env σ`.

Syntactic gate:

```isabelle
local_edge_action (EA_Assign x e)  ⟺  ¬is_global x ∧ ¬aexp_mentions_global e
local_edge_action (EA_Assume b)    ⟺  ¬bexp_mentions_global b
(* nop local; enter not local *)
```

Post-fixpoint invariant (needed because local trees do not propagate locals
through `Inr` side slots):

```isabelle
inr_slot_locals_bot σ  ⟺  ∀g x. ¬is_global x ⟶ σ (Inr g) x = bot
```

### 1.2 What went wrong in the first pass

Sign and Interval each proved `sound_effectful_transfer` with parallel case
splits on `local_edge_action` vs `unit_edge_tree`. That duplicates the same
theorem: one proof is a specialization of the other. The abstraction was at the
wrong level.

Exec soundness (`Sign_Exec_Sound`) tried to bridge mixed abstract trees to
unit executable trees via `part_post_solution_st_to_abs_eff_unit_transfer` with
incompatible assumptions.

---

## 2. Target design

One semantic transfer; trees are implementations of how the solver obtains inputs.

```text
domain semantic transfer          sound_transfer tf
        │
        ▼
tree implementation               unit_edge_tree / local_edge_tree implement tf
        │
        ▼
effectful record                  unit_etf_of_transfer tf
                                  mixed_etf_of_transfer tf
        │
        ▼
effectful soundness (once)        sound_effectful_transfer_unit_of_transfer tf
                                  sound_effectful_transfer_mixed_of_transfer tf
```

### 2.1 Domain obligations (thin)

Each domain proves **semantics once**:

```isabelle
interpretation sign_sound_tf: sound_transfer sign_tf
```

For the mixed factory only, additionally:

```isabelle
local_edge_action a  ⟹  local_edge_invariant (apply_tf sign_tf a)
```

No per-domain `sound_effectful_transfer` case split.

### 2.2 `local_edge_action` vs `local_edge_invariant`

| Concept | Role |
| --- | --- |
| `local_edge_action` | **Syntactic dispatch** — which tree shape to build |
| `local_edge_invariant` | **Semantic hook** — `apply_tf` preserves globals and reads only locals |

Bridge (per domain, case split on `edge_action`):

```isabelle
local_edge_action a  ⟹  local_edge_invariant (apply_tf tf a)
```

There is **no** separate soundness theorem for “local edges”.

### 2.3 Layer separation

| Layer | Theories | Must not contain |
| --- | --- | --- |
| Semantics | `TD_Side_CFG`, `Constraint_System` | `fun_of_st`, `dep_aux`, `part_post_solution` |
| Solver preconditions | `TD_Side_Eff_Bounds`, `TD_Side_Eff_Soundness` | domain names |
| Execution | `Exec_Bridge`, `*_Exec` | duplicated soundness proofs |

Collecting soundness consumes **γ / store membership** (`s ∈ ⟦…⟧`).
`part_post_solution_st_to_abs_eff` consumes **exact** `traverse` / `sides` /
`dep_aux` commutation through `fun_of_st` — a separate concern (exec transport).

---

## 3. Implementation plan

Build after **every** step (`isabelle build -d … Voblint_Analysis`).

Locales are **not** first-class values. Do **not** write
`etf_of_generator :: edge_tree_generator ⇒ …`. Use concrete record factories
first; introduce an `edge_tree_generator` locale later only if the factories
still duplicate too much.

### Step 1 — Generic implementation lemmas

**Where:** `TD_Side_CFG.thy` (and/or `Constraint_System_Sound.thy` if imports
require it).

Inside `context sound_transfer` prove one lemma per edge action, for each tree
shape. Proofs use locale facts (`tf_sound_assign`, etc.) without passing
`sound_transfer tf` manually.

**Unit** (always):

```isabelle
context sound_transfer
begin

lemma in_gamma_unit_edge_tree_nop: …
lemma in_gamma_unit_edge_tree_assign: …
lemma in_gamma_unit_edge_tree_assume: …
lemma in_gamma_unit_edge_tree_assume_not: …
lemma in_gamma_unit_edge_tree_enter: …

end
```

**Local** (requires `local_edge_invariant f`):

```isabelle
lemma in_gamma_local_edge_tree_assign:
  assumes "local_edge_invariant (tf_assign tf x e)"
  assumes "inr_slot_locals_bot σ"
  assumes "s ∈ ⟦σ (Inl u) ⊔ glob_env σ⟧"
  shows "s(x := aval e s) ∈ ⟦etf_collecting_full (local_edge_tree (tf_assign tf x e) u) σ⟧"
```

Analogous lemmas for nop / assume / assume_not / enter.

**Forbidden in Step 1:** `fun_of_st`, `traverse_rhs`, `dep_aux`, `stable_at`,
`part_post_solution`, `side_cfg_T_eff*`.

**Do not** prove lattice `≤` or equality between local and unit trees here unless
a later step genuinely needs it. Prefer direct γ statements:
`s ∈ ⟦etf_collecting_full (local …)⟧ ⟹ s ∈ ⟦etf_collecting_full (unit …)⟧`
only in the optional analysis lemma (Step 6).

**Exit:** Step 1 theories green in I/Q; batch build for touched session.

---

### Step 2 — Concrete ETF factories

**Where:** `TD_Side_CFG.thy` or `Constraint_System.thy`.

```isabelle
definition unit_etf_of_transfer ::
  "'a::sound_domain domain_transfer ⇒ (unit, 'a) effectful_domain_transfer"
  (* every field: unit_edge_tree (apply_tf tf …) *)

definition mixed_etf_of_transfer ::
  "'a::sound_domain domain_transfer ⇒ (unit, 'a) effectful_domain_transfer"
  (* dispatch: if local_edge_action a then local_edge_tree else unit_edge_tree *)
```

**Exit:** definitions compile; no soundness yet.

---

### Step 3 — Generic effectful soundness theorems

**Where:** `Constraint_System.thy` or new `Effectful_Sound.thy` importing
`TD_Side_CFG` + `Constraint_System_Sound`.

```isabelle
lemma sound_effectful_transfer_unit_of_transfer:
  fixes tf :: "'a::sound_domain domain_transfer"
  assumes "sound_transfer tf"
  shows "sound_effectful_transfer (unit_etf_of_transfer tf)"

lemma sound_effectful_transfer_mixed_of_transfer:
  fixes tf :: "'a::sound_domain domain_transfer"
  assumes "sound_transfer tf"
  assumes "⋀a. local_edge_action a ⟹ local_edge_invariant (apply_tf tf a)"
  shows "sound_effectful_transfer (mixed_etf_of_transfer tf)"
```

Combine case stays `unit_combine_tree` in both factories. Prove each
`sound_effectful_transfer` locale obligation once from Step 1 lemmas + factory
unfolding.

**Exit:** generic theorems green; no domain names in proofs.

---

### Step 4 — Sign

**Where:** `Sign_Domain.thy`, `Sign_Side_Soundness.thy`.

1. Close sorries:
   `assume_sign_le_etf_collecting_full_local`,
   `assume_not_sign_le_etf_collecting_full_local`
   (or fold into a single `sign_tf_local_edge_invariant` bundle).

2. Prove:

   ```isabelle
   lemma sign_tf_local_edge_invariant:
     "local_edge_action a ⟹ local_edge_invariant (apply_tf sign_tf a)"
   ```

3. Make `sign_etf` a definitional alias:

   ```isabelle
   definition sign_etf :: … where
     "sign_etf = mixed_etf_of_transfer sign_tf"
   ```

4. Replace the large `sign_sound_etf` proof with:

   ```isabelle
   lemma sign_sound_etf: "sound_effectful_transfer sign_etf"
     by (rule sound_effectful_transfer_mixed_of_transfer
           [OF sign_sound_tf sign_tf_local_edge_invariant])
   ```

5. Delete redundant lemmas such as
   `assign_sign_in_gamma_etf_collecting_full_local` once subsumed by Step 1.

**Exit:** `Sign_Side_Soundness` green; `Sign_Domain` sorry-free.

---

### Step 5 — Interval (unit-only)

**Where:** `Interval_Side_Soundness.thy`.

```isabelle
definition ivl_etf :: … where
  "ivl_etf = unit_etf_of_transfer ivl_tf"

lemma ivl_sound_etf: "sound_effectful_transfer ivl_etf"
  by (rule sound_effectful_transfer_unit_of_transfer [OF ivl_sound_tf])
```

No `local_edge_invariant` work. No local tree migration.

**Exit:** `Interval_Side_Soundness` green.

---

### Step 6 — Named-global Sign

**Where:** `Sign_Named_Global_Eff.thy`.

`named_etf` uses **`route_tree`** (queries `Gpos` + `Gneg`), not
`mixed_etf_of_transfer`. Update for the strengthened `sound_effectful_transfer`
locale (`inr_slot_locals_bot`, `etf_collecting_full`). Prove
`named_edge_inr` / `named_comb_inr` or `cone_compatible_etf named_etf` for the
pruned exit theorem.

Do **not** reuse `sound_effectful_transfer_mixed_of_transfer` directly; route
trees need their own implementation lemmas (same *pattern*, different tree
shape).

**Exit:** `named_analysis_sound` green.

**Gate:** `isabelle build Voblint_Analysis` green — mathematics layer done.

---

### Step 7 — Analysis: local refines unit (optional)

**Where:** `TD_Side_CFG.thy`.

Conservative-unit story for exec/analysis comparison only — **not** required for
`sound_effectful_transfer`:

```isabelle
lemma in_gamma_local_refines_unit:
  assumes "local_edge_invariant f"
  assumes "inr_slot_locals_bot σ"
  assumes "s ∈ ⟦etf_collecting_full (local_edge_tree f u) σ⟧"
  shows "s ∈ ⟦etf_collecting_full (unit_edge_tree f u) σ⟧"
```

**Exit:** lemma green; no solver vocabulary.

---

### Step 8 — Exec transport

**Where:** `Exec_Bridge.thy`, `Sign_Exec_Sound.thy`.

Shortest path while execution stays unit-only:

```text
sign_etf_st  =  unit_etf_of_transfer_st sign_tf   (already unit-shaped)
sign_exec    →  part_post_solution_st_to_abs_eff_unit_transfer
              →  sound_effectful_transfer (unit_etf_of_transfer sign_tf)
```

Mixed `sign_etf` is for `side_analyse_eff` (analysis path). Exec soundness does
not require mixed transport until Step 9.

Prove solver-layer `dep_aux` compatibility separately if a mixed exec bridge is
needed later.

**Exit:** `sign_exec_sound_collecting` green.

**Gate:** `isabelle build Voblint_Formalization` green.

---

### Step 9 — Executable local trees (deferred refinement)

**Where:** `Exec_Bridge.thy`, `Sign_Exec.thy`.

```isabelle
local_edge_tree_st …
mixed_etf_of_transfer_st tf
```

Replace unit-only exec with mixed/mixed transport when `dep_aux` compatibility
is proved. Delete Step 7 dependency if redundant.

---

### Step 10 — RHS-generator locale refactor

Implemented for the unit and mixed unit-global tree shapes. The locales collect
the dependency, cone-compatibility, and threefold monotonicity obligations that
used to be duplicated in `TD_Side_Eff_Soundness`.

```isabelle
locale sound_rhs_generator = …   (* cone / mono / deps — no exec *)

locale sound_rhs_generator_exec = sound_rhs_generator + …
  (* fun_of_st bridge only here *)
```

Interpretations replace `*_unit_transfer` / `*_local_unit_transfer` bodies.

---

## 4. Files touched (expected)

| File | Steps |
| --- | --- |
| `TD_Side_CFG.thy` | 1, 2, 7 |
| `Constraint_System.thy` | 2, 3 |
| `Constraint_System_Sound.thy` | 1, 3 |
| `Sign_Domain.thy` | 4 |
| `Sign_Side_Soundness.thy` | 4 (shrink) |
| `Interval_Side_Soundness.thy` | 5 |
| `Sign_Named_Global_Eff.thy` | 6 |
| `Exec_Bridge.thy` | 8, 9 |
| `Sign_Exec.thy`, `Sign_Exec_Sound.thy` | 8, 9 |
| `TD_Side_Eff_Soundness.thy` | 10 only |

---

## 5. Exit criteria

- [x] 0 sorries in `src/`
- [x] `sound_effectful_transfer_*_of_transfer` proved once generically
- [x] `sign_sound_etf` / `ivl_sound_etf` are one-line corollaries
- [x] No duplicated case split on `local_edge_action` in domain soundness theories
- [x] `Sign_Exec_Sound` green via unit exec transport (Step 8)
- [x] `named_analysis_sound` green (Step 6)
- [x] Solver-level cone/mono obligations factored through `TD_Side_RHS_Generator`
- [x] `sound_rhs_generator` locales introduced for unit and mixed unit-global RHS shapes
- [x] `Voblint_Formalization` batch build green
- [ ] (Deferred) `local_edge_tree_st` + mixed exec (Step 9)

---

## 6. Non-goals (this migration)

- Interval local trees (stay on `unit_etf_of_transfer` until a separate effort)
- Proving equality `etf_collecting_full local = etf_collecting_full unit`
- `edge_tree_generator` locale before concrete factories work (Step 10 only)
- Reintroducing `side_cfg_T_st` / plain `tf_st` fold
- Routing `named_etf` through `mixed_etf_of_transfer`

---

## 7. Current staged work — disposition

| Staged artifact | Action |
| --- | --- |
| `local_edge_tree`, `etf_collecting_full`, `inr_slot_locals_bot` | **Keep** — core semantics |
| `sign_edge_tree` + large `sign_sound_etf` | **Replace** — Step 4 alias + generic theorem |
| `Sign_Domain` local invariant lemmas | **Keep** — feed `sign_tf_local_edge_invariant` |
| `Sign_Domain` assume sorries | **Close** — Step 4 |
| `*_local_unit_transfer` duplicate families | **Deleted / replaced** — RHS-generator locales discharge cone and mono contracts |
| `Sign_Exec_Sound` broken `unit_transfer` OF | **Fixed** — Step 8 via unit factory |
| Legacy `side_cfg_T` removal in `TD_Side_Tree` | **Keep** — side-effecting-only spine |

---

## 8. Order summary

```text
 1  generic in_gamma lemmas (context sound_transfer)
 2  unit_etf_of_transfer / mixed_etf_of_transfer
 3  sound_effectful_transfer_*_of_transfer
 4  Sign  (local_edge_invariant + alias + one-line sound)
 5  Interval (unit alias + one-line sound)
 6  Named-global
    ── build Voblint_Analysis ──
 7  in_gamma_local_refines_unit (optional)
 8  Exec transport + Sign_Exec_Sound
    ── build Voblint_Formalization ──
 9  local_edge_tree_st (deferred)
10  sound_rhs_generator locale (done for current RHS shapes)
```

**Rule:** keep executable local trees as a separate refinement. The current build
uses mixed abstract Sign analysis and unit-shaped executable transport.
