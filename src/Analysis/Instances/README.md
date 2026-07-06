# Concrete domain instances

Each sub-folder threads one abstract domain through four layers:

1. **Type class** — `instantiation` blocks for `ord`, `bot`, `sup`, `order_bot`, etc.;
   `fun` instances lift these pointwise to `'d abs_state` automatically.
2. **Locale interpretation** — one `interpretation` of `abstract_domain` + one of `sound_transfer`
   discharge all proof obligations; downstream lemmas (`gamma_state_mono`, `gamma_state_sup_ub*`)
   are derived automatically.
3. **Executable bridge** — a commutation theorem `tf_st_commute` linking the abstract transfer
   function to its `'d st` association-list mirror; consumed by `Exec_Bridge.thy`.
4. **End-to-end soundness** — packages the domain as an `effectful_domain_transfer` record and
   proves `sound_effectful_transfer`; the soundness engine in `Generic/Solver/` delivers
   `cfg_collect g cinit ≤ γ(analyse …)`.

The four layers above are the **domain definition** and live directly in the domain folder.
Executable **witnesses and runs** (the `Exec_<domain>_*_Run` / `_Solve` demonstrations that
evaluate the real solver via the code generator) live in the folder's `Runs/` subfolder —
they demonstrate the domain, they are not part of it.

## Sub-folders

| Folder | Domain | Status |
| --- | --- | --- |
| `Sign/` | 7-element sign lattice | full soundness + executable + end-to-end |
| `Interval/` | Interval domain (`ivl`) | full soundness + executable + end-to-end (`side_ivl_analysis_sound`) |
| `NamedGlobalSign/` | Named-global sign (mixed-flow, side-effecting) | executable + constant-route soundness through the solver; the conditional-flag route is a **documented boundary** (`flag_etf_mono_sides_unprovable`, `oops`) — provably not `mono_sides`, hence not solver-drivable |
| `Tooling/` | GraphViz CFG/analysis output | utility, no soundness obligation |

## Adding a domain

1. **Type-class instances.** Instantiate `ord`, `order`, `bot`/`order_bot`,
   `sup`/`semilattice_sup`, `inf`/`lattice`, and `warrowing`, then `sound_domain`
   (fixes `gamma`) and `abstract_domain` (adds `widen`). HOL lifts them pointwise to
   `'d abs_state = vname => 'd` automatically. Add `show_val` for visualisation.
2. **Forward transfer.** Define `aval_<d>` / `assign_<d>` / `assume_<d>`, bundle a
   `domain_transfer` record, and `interpret sound_transfer` — this discharges the
   collecting obligations. `gamma_state_mono` / `gamma_state_sup_ub*` follow.
3. **Backward transfer (guards).** Provide `meet`, `aval_abs`, and the four `inv_*`
   operators; `interpret backward_domain` for `afilter`/`bfilter` + soundness, then
   `interpret backward_domain_mono` (only the six operator-mono goals; the parent is
   already interpreted) for `afilter_mono`/`bfilter_mono` — both proved generically
   in `Generic/Domain/Abstract_Domain`. See `Sign_Domain` / `Interval_Domain` for the
   interpretation shape.
4. **Executable mirror.** Define the `'d st` mirror and prove `tf_st_commute`; the
   generic `part_post_solution_st_to_abs_transport` in `Generic/Solver/Exec/Exec_Bridge`
   lifts any executable post-solution to the abstract one.
5. **End-to-end soundness.** Package an `effectful_domain_transfer` record; prove
   `sound_effectful_transfer`. The engine in `Generic/Solver/` delivers
   `cfg_collect g cinit <= gamma(analyse ...)`.
6. **Context-sensitivity / digests — free.** No per-domain work: `glob_env_cmp`,
   `side_env_cmp`, `digest_global_read` (`obs_digest`), the cmp/ctx/digest generators,
   and their soundness are all generic over `'d::bounded_semilattice_sup_bot`. A new
   domain plugs into them unchanged; only *witnesses* (`Runs/`) are written per domain.
7. Register the `.thy` files in `src/Analysis/ROOT` (`directories` + `theories`,
   order: domain before soundness before exec/runs).

No changes to `Generic/` are needed unless the new domain requires a new tree shape.
The Sign and Interval folders are the two worked examples; the `Generic/` layer is
domain-agnostic — it contains no domain-specific code (comments name `sign`/`ivl`
only as illustrations).
