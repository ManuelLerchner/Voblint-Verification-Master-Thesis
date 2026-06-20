# Handoff — generalize the effectful IP solver to named globals (`'g::finite`)

> **Uncommitted working note** (intentionally not in git). Task spec for a fresh
> proof-engineering agent. Read this, then `docs/EFFECTFUL_TF_MIGRATION.md §9` and
> `docs/SIDE_ENTRY_GLOBALS_SEEDING.md`, then start. Follow `CLAUDE.md` for the I/Q
> MCP workflow and the build-green discipline — **never edit `.thy` via host
> Read/Edit/Write; go through I/Q `write_file`.**

## 0. TL;DR

This session (2026-06-20) generalised the *abstract* effectful layer to `'g::finite`
and proved a named-global soundness **witness** (`Sign_Named_Global_Eff.thy`,
`flag_etf_sound`). What stayed at `'g = unit` is the **executable solver
construction** (`side_cfg_T_ip_eff` and its interface), because its entry seeding
emits `Side ()`. This task lifts that construction to `'g::finite` so a *named-global
analysis runs through the real solver interface* and gets an end-to-end soundness
theorem (the `side_ip_*_analysis_sound` analogue for `flag_etf`).

**Achievable core (do this):** generalise the solver-construction chain + re-prove the
standalone gen theorem at `'g::finite`; instantiate at `flag_etf` for a named-global
headline soundness theorem. **Stretch (mark, don't attempt unless asked):** full
code-gen `value`-runnable demo — that needs the `'a st` executable layer
(`Exec_St`/`Exec_Bridge`) at `'g`, which is a separate, heavier effort (see §6).

## 1. The one design decision to lock first

The entry currently seeds the initial globals into the single pot:

```isabelle
(* TD_Side_IP_Tree.make_side_rhs_tree_ip_eff, line ~167 *)
in if v = cfg_entry g then Side () (restrict_global s0) t else t
```

`Side ()` forces `'g = unit`. For `'g::finite` the initial global state
`restrict_global s0 :: 'a abs_state` must be seeded into *some* named slot. Seeding
into **one designated slot suffices for soundness**, because the entry-coverage
obligation is `restrict_global s0 ≤ glob_env σ`, and `glob_env σ = ⨆_g σ(Inr g)`
already dominates any single slot (`glob_env_upper`).

**LOCKED DESIGN: add a designated seed-slot parameter `gseed :: 'g`** to
`make_side_rhs_tree_ip_eff` / `side_cfg_T_ip_eff` / the solver interface /
`side_analyse_ip_eff`, and seed `Side gseed (restrict_global s0)`.

- Unit instantiation: `gseed = ()` — every existing unit caller passes `()` and is
  unchanged in behaviour.
- Entry-coverage lemma generalises to:
  `restrict_global s0 ≤ σ(Inr gseed)` (from the `Side gseed` contribution, exactly as
  `restrict_global_s0_le_global_ip_eff` does for `Inr ()` today) `≤ glob_env σ`
  (`glob_env_upper`), hence `s0 ≤ side_env σ (cfg_entry g)` (`side_env` is already
  `σ(Inl v) ⊔ glob_env σ` after this session).

Rejected alternatives: a seed *function* `'g ⇒ 'a abs_state` or seed *list* — more
general but more plumbing; the single-slot version is the minimum that unblocks the
named-global headline. Revisit only if an analysis genuinely needs per-name initial
values.

## 2. Why this is now tractable (what this session already did)

- `Constraint_System`: `sound_effectful_transfer` locale + `etf_full` + `glob_env`
  (+ `glob_env_upper`/`_unit`/`_mono`, `all_sides`, `all_sides_le_glob_env_sides`) are
  **already `'g::finite`-generic**.
- `TD_Side_CFG.side_env σ v = σ(Inl v) ⊔ glob_env σ` is **already generic**
  (`= σ(Inl v) ⊔ σ(Inr ())` at unit via `glob_env_unit`).
- `edge_collect_etf_sound`, `ip_witness_gamma_eff`, `post_fixpoint_sound_at_ip_eff`
  (in the `sound_effectful_transfer` context) are **already generic in `'g`** — the
  abstract collecting soundness needs no change.
- The witness `flag_etf :: (gname, sign)` + `flag_etf_sound` already exist
  (`Sign_Named_Global_Eff.thy`). You instantiate the generalised gen theorem at it.

So the work is confined to the **executable-solver-construction** files, which are
still `(unit, 'a)`-typed.

## 3. Exact change list (file by file)

Generalise `(unit, 'a) effectful_domain_transfer` → `('g::finite, 'a) ...` and thread
`gseed :: 'g`. Current `(unit,_)` / `Inr ()` counts in parentheses.

| File | Change | Notes |
|---|---|---|
| `TD_Side_IP_Tree.thy` (4 `Inr ()`; defs at L145/159/170/179) | `make_side_rhs_tree_ip_eff` + `side_cfg_T_ip_eff` take `gseed`; entry `Side gseed (restrict_global s0)`. `side_rhs_fold_ip_eff` is already structurally `'g`-agnostic (it folds `apply_etf`/`etf_combine`) — only the type signature widens. | The denotation lemmas (`traverse_side_rhs_fold_ip_eff`, `sides_…`, `dep_aux_…`) should carry; `Side gseed d` behaves like `Side () d` for `traverse_rhs`/`dep_aux` and adds to slot `Inr gseed` in `sides_of_rhs`. |
| `TD_Side_IP_Eff_Bounds.thy` (25 `Inr ()`; ~24 etf fixes) | Widen all `etf` fixes to `'g`. The per-edge/combine closure bounds (`etf_combined_le_ip_eff`, `etf_combine_combined_le_ip_eff`) currently bound via `σ(Inr ())`; restate via the per-name bound `sides_of_rhs (T x) σ (Inr g) ≤ σ(Inr g)` for every `g`, then `all_sides ≤ glob_env σ` (`all_sides_le_glob_env_sides` + `glob_env_mono`) gives the global half of `etf_full ≤ side_env`. | This is the mechanically largest file but the math is the split already used at unit; the `glob_env` bridge lemma exists. |
| `TD_Side_IP_Eff_Interface.thy` (0 `Inr ()`; 3 pins) | Widen `side_cfg_ip_solve_dom_eff`, the `td_cfg_side_ip_solver_eff` locale, `nu_at`, `side_analyse_ip_eff` to `'g`; thread `gseed`. `nu_at :: pp ⇒ pp + 'g ⇒ …`. | The vendored `TD_side_mono` interpretation is `'g`-generic already (Basics_side is `'x,'g,'d`). Mostly type-signature widening. |
| `TD_Side_IP_Eff_Soundness.thy` (8 `Inr ()`) | (a) cone lemmas `ip_reaches_imp_trans_dep_or_eq_side_eff` / `side_ip_cone_in_vars_eff` track `Inl` deps only — should carry with type widening. (b) entry-seeding `restrict_global_s0_le_global_ip_eff` / `s0_le_side_env_entry_ip_eff`: `Inr ()` → `Inr gseed`, finish via `glob_env_upper`. (c) the standalone executable theorems (`side_collect_sound_ip_exit_pruned_eff`, `side_analyse_ip_eff_collect_sound_exit_pruned_gen`) widen `etf :: ('g, 'a)`, keep the explicit `sound_effectful_transfer γ etf` hypothesis. | These were pulled out of the generic locale this session precisely so they could be re-typed at `'g` here. |
| `Sign_Named_Global_Eff.thy` (the example) | Add `gseed` choice for `gname` (e.g. a dedicated `Ginit` constructor, or reuse `Gpos`); state `flag_ip_analysis_sound` by instantiating the generalised gen theorem at `flag_etf_sound` — the named-global headline. Discharge the three TD_side preconditions for `flag_etf` from the monad mono/static lemmas (`seqcomp_mono`, `static_deps_seqcomp`) — NOT from the `etf_from_tf` shim (flag_etf is non-shim). | This is the payoff. The mono/static discharge for a genuinely effectful etf is the one genuinely new proof obligation (shim versions exist; you need the non-shim analogue). |
| **`Exec_Bridge.thy` (39 `Inr ()`) — DO NOT TOUCH for the core.** | It transports the `'a st` *executable* Sign path (`sign_exec`) to the abstract post-solution; it is **not** on the `side_analyse_ip_eff` path used by `flag_etf`. Leave it at `'g = unit`. Only the stretch (code-gen runnable) needs it. | Confirm by `rg` that nothing in the core change list calls into `Exec_Bridge`. |

Downstream unaffected (already generic or off-path): `Sign_Side_IP_Soundness`,
`Interval_Side_IP_Soundness`, `Sign_Exec_Sound` — they pass `'g = unit` (sign/ivl
`etf_from_tf`) and continue to work via the `gseed = ()` instantiation. Re-check they
still build (the `side_analyse_ip_eff` signature gains a `gseed` arg — update those
call sites to pass `()`).

## 4. The one genuinely new proof: non-shim TD_side preconditions

Every existing `side_analyse_ip_eff` user discharges `is_mono_eq`/`mono_sides`/
`mono_deps` via `side_cfg_T_ip_eff_is_mono_eq` etc., which are stated for
`etf_from_tf tf` (the pure shim). `flag_etf` is **not** a shim. You must discharge the
three preconditions for `flag_etf` from the generic `_gen` lemmas in
`TD_Side_IP_Eff_Bounds` (`side_cfg_T_ip_eff_is_mono_eq_gen` / `_mono_sides_gen` /
`_mono_deps_gen`), feeding them per-tree monotonicity + static-deps of `flag_etf`'s
trees. The building blocks exist: `seqcomp_mono`, `static_deps_seqcomp`,
`sides_of_rhs_seqcomp`. The `route_tree`/`route_combine` of `flag_etf` have a fixed
query skeleton (`QueryL`, `QueryG Gpos`, `QueryG Gneg`), so `static_deps` holds; values
at `Side`/`Answer` are monotone in σ, so `seqcomp_mono` applies. Budget real time here —
this is the part with no shim shortcut.

## 5. Precedent to copy: `docs/SIDE_ENTRY_GLOBALS_SEEDING.md`

That migration did the *identical shape* at `unit`: it introduced the entry
`Side () (restrict_global s0) t` wrap and proved `s0_le_side_env_entry_ip` without the
`restrict_global s0 = bot` hypothesis (slices E1–E4). Re-read §1 "Why this is the whole
change": `Side y d t` is invisible to `traverse_rhs` and `dep_aux`, and adds `d` only to
slot `Inr y` of `sides_of_rhs`. The `gseed` generalisation is that same argument with
`y = gseed` instead of `y = ()`. Most local-fold / dependency / cone lemmas carry
verbatim; only the global-side bound and entry-seeding move.

## 6. Scope honesty — "runnable" has two levels

- **Level A (this task):** the abstract solver `side_analyse_ip_eff` at `'g = gname` as
  a *mathematical* object, with `flag_etf` sound end-to-end through it. This proves "a
  named-global analysis is sound through the real solver interface." Precision stays
  demonstrated at the per-tree level (`flag_assign_routes_pos`/`_neg`, already proved).
- **Level B (stretch, separate handoff):** code-gen `value`-evaluation. `'a abs_state =
  vname ⇒ 'a` is not executable; the executable path uses `'a st` (`Exec_St`) bridged by
  `Exec_Bridge` (`part_post_solution_st_to_abs_eff`). Making *that* run at `'g = gname`
  means generalising `Exec_St`'s side fold + `Exec_Bridge` (the 39 `Inr ()`) to `'g` —
  the heavy piece deliberately excluded here. Only then can you `value`-observe `Gpos`
  and `Gneg` holding distinct values. Do **not** start this unless explicitly asked.

State Level A as the deliverable; record Level B as the remaining open item in
`docs/EFFECTFUL_TF_MIGRATION.md §9`.

## 7. Workflow & build discipline (from `CLAUDE.md`)

- I/Q MCP for all `.thy` edits (`write_file` str_replace, small diffs); `get_diagnostics`
  per file; `explore`/`get_context_info` before non-trivial proofs. **No host
  Read/Edit/Write on `.thy`.**
- After every `write_file`: `python3 scripts/normalize_isabelle_ascii.py <file>` then
  re-`open_file` (I/Q serialises ASCII tokens back to unicode).
- **Build is the gate, not I/Q.** Batch-build only at a closed slice:
  `isabelle build -v -N -d ~/afp/thys -d vendor/td-verification -D . Voblint_Formalization`.
  Heap caveat: after generalising a locale/def, downstream I/Q diagnostics run against
  the *stale heap* until you rebuild — trust batch over I/Q for cross-file type changes
  (this bit hard this session).
- ASCII-only `.thy` (`\<Longrightarrow>` etc.); pre-commit hook blocks unicode.
- Commit only when the user asks; on `main` branch first.

## 8. Suggested build-gated slices

1. **Tree + seed-slot.** Add `gseed` to `make_side_rhs_tree_ip_eff` / `side_cfg_T_ip_eff`,
   widen to `'g`. Fix all unit callers to pass `()`. Batch-green `Voblint_Analysis`.
2. **Interface.** Widen the locale + `side_analyse_ip_eff` + `gseed`; update unit call
   sites. Green.
3. **Bounds.** Widen etf fixes; restate the global-half bounds via `glob_env`. Green.
4. **Soundness.** Widen cone + entry-seeding (`Inr gseed`) + the two standalone
   executable theorems to `'g`. Re-prove `side_ip_sign_analysis_sound` /
   `side_ip_ivl_analysis_sound` (now at `gseed = ()`). Green.
5. **Example.** Discharge `flag_etf` TD_side preconditions (§4); state + prove
   `flag_ip_analysis_sound`. Green, no sorry. Update migration doc §9 + KB.

Each slice: I/Q until file-clean, then one batch build. Expect 4–5 (sign/ivl callers)
to surface most of the breakage.

## 9. Risks / where it can stall

- **Bounds restatement (slice 3)** is the largest mechanical surface (25 `Inr ()`). The
  risk is a bound that genuinely needed the *single* pot; cross-check each against the
  `glob_env`/`all_sides` bridge — if a bound can't be re-expressed per-name, that's a
  real finding, surface it.
- **Non-shim preconditions (§4)** — no shortcut; if `seqcomp_mono`/`static_deps_seqcomp`
  don't compose cleanly for `route_tree`/`route_combine`, you may need a small per-tree
  lemma. Don't widen `auto`/`simp` to force it (batch-hang risk per `CLAUDE.md`).
- **Heap staleness** — re-typing a def turns downstream I/Q red until rebuild; gate on
  batch, not I/Q diagnostics, for the type-change slices.
- **Scope creep into Exec_Bridge** — if you find yourself touching `Exec_Bridge`, stop:
  you've drifted into Level B. The core deliverable does not need it.

## 10. Done = 

`Voblint_Formalization` batch-green, no `sorry`, with a `flag_ip_analysis_sound`-style
theorem: the named-global `flag_etf` analysis over-approximates `cfg_collect_ip` at the
exit, proved through `side_analyse_ip_eff` at `'g = gname` (not the unit shim). Update
`docs/EFFECTFUL_TF_MIGRATION.md §9` (Level A done; Level B = code-gen runnable, open)
and the KB (`status.md`, AD-31 impact, thesis-structure §9.4) to match.
