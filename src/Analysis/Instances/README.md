# Concrete domain instances

Each sub-folder threads one abstract domain through four layers:

1. **Type class** — `instantiation` blocks for `ord`, `bot`, `sup`, `order_bot`, etc.;
   `fun` instances lift these pointwise to `'d abs_state` automatically.
2. **Locale interpretation** — one `interpretation` of `abstract_domain` + one of `sound_transfer`
   discharge all proof obligations; downstream lemmas (`gamma_state_mono`, `gamma_state_sup_ub*`)
   are derived automatically.
3. **Executable witnesses** — native DG and per-domain executable runs live in the
   example theories under `src/Formalization/Examples/Executable/`; they exercise the
   generated equation systems directly and no longer rely on a bridge theory.
4. **End-to-end soundness** — packages the domain as an `effectful_domain_transfer` record and
   proves `sound_effectful_transfer`; the soundness engine in `Generic/Solver/` delivers
   `cfg_collect g cinit ≤ γ(analyse …)`.

The four layers above are the **domain definition** and live directly in the domain folder.
Executable **witnesses and runs** (the `Exec_<domain>_*_Run` / `_Solve` demonstrations that
evaluate the real solver via the code generator) live under
`src/Formalization/Examples/Executable/`. They demonstrate the domain, they are not
part of the reusable analysis instance.

## Sub-folders

| Folder | Domain | Status |
| --- | --- | --- |
| `Sign/` | 7-element sign lattice | full soundness + executable + end-to-end |
| `Interval/` | Interval domain (`ivl`) | full soundness + executable + end-to-end (`side_ivl_analysis_sound`) |
| `NamedGlobalSign/` | Named-global sign (mixed-flow, side-effecting) | executable + constant-route soundness through the solver; the conditional-flag route is a **documented boundary** (`flag_etf_mono_sides_unprovable`, `oops`) — provably not `mono_sides`, hence not solver-drivable |
| `Mixed/` | Sign answers (`D`) + one flow-insensitive Interval side invariant (`G`) on the heterogeneous `dg_spec` interface | collecting soundness (`mixed_si_post_solution_collect_sound`) + executable solver run; first analysis with two genuinely different domains (see `docs/SPLIT_STATE_MIGRATION.md` §6.6) |
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
5. **Context-sensitivity / digests — free.** No per-domain work: `glob_env_cmp`,
   `side_env_cmp`, `digest_global_read` (`obs_digest`), the cmp/ctx/digest generators,
   and their soundness are all generic over `'d::bounded_semilattice_sup_bot`. A new
   domain plugs into them unchanged; only executable witnesses are written per domain,
   in `src/Formalization/Examples/Executable/`.
6. Register the `.thy` files in `src/Analysis/ROOT` (`directories` + `theories`,
   order: domain before soundness before executable witnesses).

No changes to `Generic/` are needed unless the new domain requires a new tree shape.
The Sign and Interval folders are the two worked examples; the `Generic/` layer is
domain-agnostic — it contains no domain-specific code (comments name `sign`/`ivl`
only as illustrations).
