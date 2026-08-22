# M4 executable-store handoff

Status: executable-store groundwork is I/Q-checked and uncommitted. The old
`st` quotient remains in place. The new resolved-location carrier is a
scaffold; executable solver integration is the next task.

Date: 2026-08-01

## Scope

This handoff continues the M4.1a/M4.2 migration from name-based storage
classification to declaration-driven, classifier-aware operations. It covers
the executable store boundary in `src/Core/Domain/Exec_St.thy`.

The broader classifier-aware framework is also present in:

- `src/Core/Equations/Constraint_System.thy`
- `src/Core/Equations/Constraint_System_Sound.thy`
- `src/Core/Solver/Context/DG/DG_Framework.thy`
- `src/Core/Solver/Context/DG/DG_Soundness.thy`
- `src/Core/Solver/Context/DG/DG_LTR_Sound.thy`
- `src/Core/Solver/TD_Side/TD_Side_CFG.thy`

Do not delete `is_global`, rename example variables, or begin M4.3/M4.5/M4.6
work from this handoff.

## Completed

`Exec_St.thy` now contains:

- `remove_st_key`, which removes previous entries for a variable before an
  `update_st` prepend;
- `fun_rep_st_update` and `fun_rep_st_update_cong`;
- the original `lookup_update_same` and `lookup_update_diff` laws, still
  proved after canonical updates;
- `location = Local_Location vname | Global_Location vname`;
- `resolved_st`, an explicit-location triple with local/global defaults and a
  location-keyed override list;
- canonical `update_resolved_st` and `lookup_resolved_st` laws;
- `location_of gs`, resolving a source variable to an explicit location only at
  the conversion boundary;
- `fun_of_resolved_st_for`, converting a resolved store to a
  classifier-indexed variable function;
- `restrict_local_resolved` and `restrict_global_resolved`, with lookup and
  classifier-conversion lemmas.

The old `st` representation is unchanged semantically. Its updates no longer
retain stale shadowed entries. The resolved carrier is not yet used by the
verified solver.

## Design constraints

The old `st` is a quotient over
`fun_rep_st (dl, dg, overrides)`. Missing entries use `is_global` to choose
between `dl` and `dg`. An arbitrary `gs` cannot be added to `lookup_st` or
`restrict_*_st`: quotient-equivalent raw triples under `is_global` need not
remain equivalent when defaults are interpreted using `gs`.

The canonical counterexample uses a redundant override:

```text
r1 = (dlocal, dglobal, [(x, dlocal)])
r2 = (dlocal, dglobal, [])
```

When `x` is local under `is_global`, these have the same semantic function.
If `gs x` is true, the override in `r1` and the global default in `r2` can
differ. This is why the classifier-aware path uses explicit locations rather
than parameterizing the existing quotient.

`resolved_st` currently uses a list, so updates are canonical but lookup is
still linear. A balanced executable map is a later performance option; do not
introduce it while the semantic carrier API is unsettled.

Do not add a raw list-based `sup_resolved_st` as a shortcut. A correct join
needs an explicit policy for absent locations, duplicate keys, and the
carrier's executable order structure before it can support a unit-step
refinement.

Keep storage class and analysis placement separate. `Local_Location` and
`Global_Location` are resolved D/G locations for this scaffold, not the final
M4.3 placement interface.

## Next steps

1. Add a resolved-store unit-step operation and prove its conversion theorem
   against `unit_step_for gs`.
2. Add resolved combine and entry operations, reusing the existing
   classifier-aware abstract operations.
3. Establish an executable refinement locale for the resolved carrier before
   changing `Run_Analysis_Sound.thy` or domain executors.
4. Revisit the carrier choice if solver use requires order, join, widening, or
   code-generation instances; prefer an explicit finite-map implementation at
   that point.
5. Only after the bridge is stable, migrate executable solver consumers from
   `st` and update their soundness statements.

## Verification

`Exec_St.thy` is fully processed in I/Q with zero errors. The latest local
checks pass:

```text
rtk python3 scripts/normalize_isabelle_ascii.py src/Core/Domain/Exec_St.thy
rtk git diff --check
rtk python3 scripts/check_isabelle_ascii.py
```

No full batch build was run for this slice. Run the project batch gate only
after the executable bridge and its downstream consumers are complete.
