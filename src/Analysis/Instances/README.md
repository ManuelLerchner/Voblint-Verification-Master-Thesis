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

## Sub-folders

| Folder | Domain | Status |
| --- | --- | --- |
| `Sign/` | 7-element sign lattice | full soundness + executable + end-to-end |
| `Interval/` | Interval domain (`ivl`) | full soundness + executable + end-to-end (`side_ivl_analysis_sound`) |
| `NamedGlobalSign/` | Named-global sign (mixed-flow, side-effecting) | executable; soundness in progress |
| `Tooling/` | GraphViz CFG/analysis output | utility, no soundness obligation |

## Adding a domain

1. Add type class instantiations; HOL lifts them pointwise automatically.
2. Interpret `abstract_domain` and `sound_transfer` in `Generic/Domain/Abstract_Domain`.
3. Define the `'d st` executable mirror and prove `tf_st_commute`.
4. Define the `effectful_domain_transfer` record; prove `sound_effectful_transfer`.
5. Add the new `.thy` files to `src/Analysis/ROOT` `theories` (order: domain before soundness before exec).

No changes to `Generic/` are needed unless the new domain requires a new tree shape.
