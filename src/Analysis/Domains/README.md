# Abstract domains

**Main contribution:** Shared abstract-domain interface (`sound_domain` /
`abstract_domain` locales, `'a abs_state`, `gamma_state`) and concrete domains
(sign, interval stretch) with per-edge transfer soundness lemmas.

**Theories**

| File                         | Role                                                                                              |
| ---------------------------- | ------------------------------------------------------------------------------------------------- |
| `Abstract_Domain.thy`        | `sound_domain`, `abstract_domain` (+ `widen`), `gamma_state`, join/fold lemmas                   |
| `Exec_St.thy`                | `'a st` quotient type (two-region rep), `lookup_st`, `update_st`, order/sup/widening instances   |
| `Sign_Domain.thy`            | 7-element sign lattice (`SBot SNeg SNonPos SZero SNonNeg SPos STop`), `gamma_sign`, `sign_tf`, type class + locale interpretations |
| `Sign_Exec.thy`              | Executable mirror `sign_tf_st`, commutation proof, `cinit_sign_st` seed                          |
| `Sign_Side_IP_Soundness.thy` | `side_ip_sign_analysis_sound` — sign domain end-to-end via `side_analyse_ip_eff`                     |
| `Sign_Exec_Sound.thy`        | `sign_exec_eqs`, `sign_exec`, `sign_exec_sound_collecting` / `_trace` — program-parametric sound theorems |
| `Exec_Sign_Run.thy`          | Code-generation entry point for the sign analysis executable                                     |
| `Interval_Domain.thy`        | Interval domain (`ivl`), `gamma_ivl`, `ivl_tf`, `ivl_domain` / `ivl_sound_tf` interpretations   |
| `Interval_Side_IP_Soundness.thy` | Interval domain end-to-end soundness                                                         |

**C-faithful initial stores** (`cinit_stores`) is defined in
`Analysis/Equations/Constraint_System.thy` (the first layer that imports both `store`
and `is_global`) so every domain can use it without pulling in sign-specific code.

---

## Instantiation chain

Adding a domain means threading through four layers:

### 1. Type class layer

```isabelle
instantiation sign :: ord   -- sign_le as ≤
instantiation sign :: bot   -- SBot as ⊥
instantiation sign :: sup   -- join_sign as ⊔
instantiation sign :: order / order_bot / bounded_semilattice_sup_bot
```

HOL's `fun` instances then lift these automatically to `sign abs_state`
(`= vname ⇒ sign`) — pointwise ⊥, ⊔, ≤. No extra definitions needed.

### 2. Locale interpretation layer

Two interpretations discharge all proof obligations once:

```isabelle
-- Abstract_Domain.thy: sound_domain ⊆ abstract_domain
interpretation sign_domain: abstract_domain gamma_sign widen_sign
```
Provides `sign_domain.gamma_state_mono`, `gamma_state_sup_ub1/2`, etc.

```isabelle
-- Constraint_System.thy: sound_transfer = sound_domain + tf soundness
interpretation sign_sound_tf: sound_transfer gamma_sign sign_tf
```
Provides `sign_sound_tf` from which `sign_sound_etf : sound_effectful_transfer
gamma_sign sign_etf` is derived; the latter exposes
`side_collect_sound_ip_exit_pruned_eff` — the big soundness engine used by the
end-to-end proof.

### 3. Executable bridge layer  (`Sign_Exec.thy`)

The proofs run on the abstract `sign_tf :: sign domain_transfer`.
Code generation needs the `sign st` association-list representation.
The bridge is a single commutation theorem:

```isabelle
sign_tf_st_commute:
  fun_of_st (sign_tf_st a s) = apply_tf sign_tf a (fun_of_st s)
```

`part_post_solution_st_to_abs_eff` (in `Exec_Bridge.thy`) converts a TD
post-fixpoint in `sign st` space into one for the effectful equation system
`side_cfg_T_ip_eff (etf_from_tf sign_tf)` in `sign abs_state` space, where the
effectful soundness locale theorems apply.

**C-faithful seed:** `cinit_sign_st :: sign st` represents
`λx. if is_global x then SZero else STop` — globals seeded at zero
(matching ISO C §6.7.9p10), locals at top (uninitialised). Its
concretisation is `cinit_stores` (defined in `Constraint_System.thy`).

### 4. End-to-end solver connection (`Sign_Exec_Sound.thy`)

```isabelle
sign_exec_eqs Π ps main =
  side_cfg_T_ip_st (compile_prog Π ps main) sign_tf_st ⊥ cinit_sign_st
```

Packages CFG + executable transfer function + seed into the solver's
`eqsT` format.  `predecessor_list` / `combine_predecessor_list` over a
compiled CFG code-generate directly (`edge_action` carries a structural
executable linear order), so the equation system runs without a separate
list-built mirror.  The vendored `TD_side_always_join_Interp` runs on it
and returns a stable assignment.  The soundness proof:

1. Unwrap solver output: `TD_side_always_join_Interp.partial_post_solution`
2. Lift to the effectful system: `part_post_solution_st_to_abs_eff` (uses commutation)
4. Cover entry: `cinit_stores ⊆ γ(cinit_sign_st)` (provable by `auto`)
5. Apply soundness engine: `sign_sound_etf.side_collect_sound_ip_exit_pruned_eff`

**Result:** `cfg_collect_ip g cinit_stores exit ≤ γ(sign_exec ...)`

---

## Precision: 7-element sign lattice

The sign lattice has 7 elements arranged as a diamond:

```
         STop
        /    \
    SNonPos  SNonNeg
    /    \  /    \
 SNeg   SZero   SPos
    \    /
      SBot
```

Key joins that weren't precise in the old 5-element lattice:

| Expression        | Old (5-element) | New (7-element) |
| ----------------- | --------------- | --------------- |
| `SZero ⊔ SPos`   | `STop`          | `SNonNeg`       |
| `SNeg  ⊔ SZero`  | `STop`          | `SNonPos`       |
| `SNeg  ⊔ SNonNeg`| `STop`          | `STop` (same)   |

Combined with C-faithful seeding (`SZero` for globals), the analysis
computes `Gresult = SNonNeg` for the branch-call example instead of
`STop`.  The remaining gap to `SPos` (needed to certify division safety)
requires flow-sensitivity on globals.

---

## Layering

```
Sign_Domain ──imports──▶ Abstract_Domain, Constraint_System, IMP2_Expr, IMP2_Globals
Sign_Exec   ──imports──▶ Exec_Bridge, Sign_Domain
Sign_Side_IP_Soundness ──imports──▶ Sign_Domain, TD_Side_IP_Eff_Soundness
Sign_Exec_Sound ──imports──▶ Sign_Exec, Sign_Side_IP_Soundness
```

**Downstream:** `Formalization/Pipeline/Trace_IP_Analysis_Sound.thy` —
`trace_ip_analysis_sound`.  `Formalization/Examples/` — concrete verified
programs using `sign_exec_prog`.

**Stretch goal:** Interval domain reintroduction (fits `sound_transfer` locale
without architectural changes); Octagon domain (see `docs/ROADMAP.md`).
