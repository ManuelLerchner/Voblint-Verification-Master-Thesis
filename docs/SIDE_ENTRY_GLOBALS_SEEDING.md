# Migration — seed initial globals at the entry (drop `restrict_global s0 = bot`)

Status: **complete (E1–E4).** The side-effecting analysis is sound from an
*arbitrary* initial state `s0`; the `restrict_global s0 = bot` hypothesis is
gone from both the interprocedural and the intra side stacks. Full
`Voblint_Soundness` session builds sorry-free (`isabelle build`, ~44s warm).

Goal: make the side-effecting analysis sound from an *arbitrary* initial state
`s0`, not only one whose globals are `bot`.

## 0. The gap

The side encoding seeds only the **local** part of the initial state at the
entry. In `make_side_rhs_tree` / `make_side_rhs_tree_ip`:

```
acc0 = (if v = cfg_entry g then join bot0 (restrict_local s0) else bot0)
```

`restrict_local s0` flows into the local fold (→ `sigma (Inl entry)`), but the
**global** part `restrict_global s0` is contributed nowhere. The global unknown
`sigma (Inr ())` starts at `bot` and only accumulates edge/combine globals.

Consequence: the entry-coverage lemma `s0_le_side_env_entry_ip`
(`TD_Side_IP_Bounds`) carries the hypothesis `restrict_global s0 = bot`, and the
example `Example_Side_Proc_Global` is forced to use `s0 = bot` (for Sign,
`gamma_state bot` is small, so the example only witnesses composition, not real
precision). The intra side stack (`TD_Side_CFG`, `side_collect_sound_at`,
`Example_Side_Global`) has the identical limitation.

This is not faithful: in Voblint globals start at their initial values, not `⊥`.

## 1. The fix

At the entry node, additionally contribute `restrict_global s0` to the single
global unknown via a `Side ()`. Concretely, wrap the entry tree:

```
make_side_rhs_tree_ip g tf join bot0 s0 v =
  (let acc0 = (if v = cfg_entry g then join bot0 (restrict_local s0) else bot0);
       t    = side_rhs_fold_ip tf join acc0 (predecessor_list g v)
                                            (combine_predecessor_list g v)
   in if v = cfg_entry g then Side () (restrict_global s0) t else t)
```

(and symmetrically in `make_side_rhs_tree` for the intra stack).

### Why this is the whole change

`Side () d t` is invisible to `traverse_rhs` (= `eq`) and to `dep_aux`, and it
adds `d` only to the global slot of `sides_of_rhs`:

- `traverse_rhs (Side () d t) sigma = traverse_rhs t sigma` ⇒ the **local fold
  denotation `side_acc_ip` is unchanged** ⇒ `eq_side_cfg_T_ip`, `is_mono_eq`,
  all local bounds carry over verbatim.
- `dep_aux sigma (Side () d t) = dep_aux sigma t` ⇒ **dependencies unchanged** ⇒
  `mono_deps`, the `dep_side_rhs_tree_ip_*` membership lemmas, and the
  reachability cone (`ip_reaches_imp_trans_dep_or_eq_side`, `side_ip_cone_in_vars`)
  carry over verbatim.
- `sides_of_rhs (Side () d t) sigma (Inr ()) = sides_of_rhs t sigma (Inr ()) ⊔ d`
  ⇒ the **global contribution at the entry gains `⊔ restrict_global s0`**.

So only the global side of the post-solution bound moves.

### What changes, precisely

1. `sides_side_rhs_fold_ip_Inr` is used through `make_side_rhs_tree_ip`; the
   entry now reads `side_glob_ip … ⊔ restrict_global s0`. Add a
   `side_glob_at g … v = side_glob_ip … ⊔ (if v = cfg_entry g then restrict_global s0 else bot)`
   shape (or inline the entry case).
2. `side_post_solution_le_global_ip` splits: for **any** `v ∈ vars`,
   `side_glob_ip … ≤ sigma (Inr ())` still holds (it is `≤` the entry's larger
   contribution), so `apply_tf_combined_le_ip` and `combine_combined_le_ip` are
   **unchanged** — they only need `side_glob_ip … ≤ sigma (Inr ())`.
3. New: `restrict_global s0 ≤ sigma (Inr ())` at the entry (from the entry's
   `Side`), giving the unconditional
   `s0_le_side_env_entry_ip` (drop the `restrict_global s0 = bot` premise).
4. `mono_sides`: the entry's `sides_of_rhs` gains a *constant* (`restrict_global
   s0`, independent of `sigma`) ⇒ still monotone; extend the proof's `Inr` case.

## 2. Slices

| Slice | Change | Exit | Status |
| --- | --- | --- | --- |
| E1 | Redefine `make_side_rhs_tree_ip` (entry `Side`); add `sides_make_side_rhs_tree_ip_{Inr,Inl}` + `dep_aux_make_side_rhs_tree_ip` helpers; repair `mono_sides` (structured) / `mono_deps` / `dep_side_rhs_tree_ip_{edge,combine}` in `TD_Side_IP_Bounds` (`eq`/`is_mono_eq` carried verbatim) | theory builds, preconditions green | ✅ done |
| E2 | Split `side_post_solution_le_global_ip` (now bounds `side_glob_ip ≤ sides_of_rhs … (Inr ())`); add `restrict_global_s0_le_global_ip`; prove unconditional `s0_le_side_env_entry_ip` | bounds green | ✅ done |
| E3 | Drop `restrict_global s0 = bot` from `side_analyse_ip_collect_sound_exit_pruned` and `side_ip_sign_analysis_sound`; `Example_Side_Proc_Global` now uses `side_proc_global_s0 = (λ_. STop)` | examples green from arbitrary `s0` | ✅ done |
| E4 | Mirror in the intra stack: `make_side_rhs_tree` + helpers in `TD_Side_CFG`, new `restrict_global_s0_le_global` / `s0_le_side_env_entry`; rewrite the inline entry-coverage in the three `TD_Side_Soundness` theorems; drop the hypothesis from `side_sign_analysis_sound`; `Example_Side_Global` now uses `(λ_. STop)` | intra green from arbitrary `s0` | ✅ done |

Single key idea, applied in both stacks: wrap the entry node's strategy tree in
`Side () (restrict_global s0) t`. It is invisible to `traverse_rhs` (= `eq`) and
to `dep_aux`, so every local-fold and dependency lemma carries verbatim; it adds
only `⊔ restrict_global s0` to the global slot `sides_of_rhs … (Inr ())`, which
is exactly what discharges `s0 ≤ side_env σ (cfg_entry g)` without the
globals-free hypothesis.

## 3. Risks

- **Foundational definition change.** `make_side_rhs_tree[_ip]` is the root of
  the side equation system; every downstream lemma re-checks. Most carry
  verbatim (see §1), but the sides/`mono_sides`/global-bound trio needs care.
  Keep each slice build-gated.
- **`Side` placement.** Putting the `Side` *outside* the fold (wrapping `t`)
  keeps the fold lemmas untouched; putting it inside would re-thread every
  `side_glob_ip` proof. Prefer the outer wrap.
- **Sort/typing.** `restrict_global s0` reuses the existing `restrict_*`; no new
  polymorphism. Watch the `combine_abs` / bare-`c` inference clash already noted
  in `docs/ISABELLE_AGENT_NOTES.md`-adjacent experience — pin `pp` types where
  needed.

## 4. Build gate

```bash
isabelle build -v -d ~/afp/thys -d vendor/td-verification -D . Voblint_Soundness
```

I/Q for development; each slice exits sorry-free.

## 5. Out of scope (separate tracks)

- Discharging `side_cfg_ip_solve_dom` for a concrete program (turn the example
  from conditional-on-termination into an unconditional theorem).
- Interval / Octagon domain stretch (precision, orthogonal to the entry fix).
