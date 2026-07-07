# Solver exec bridges — the `'a st` executable mirror

Association-list (`'a st`) mirrors of the solver fold plus the `fun_of_st`
transport that carries a concrete post-solution back to the abstract
`part_post_solution`. The generic transport
(`part_post_solution_st_to_abs_transport`) lives here; each generator variant is
a thin corollary. See `../README.md` for the Core/Context/Exec split.

| File | Role |
| --- | --- |
| `Exec_Bridge.thy` | `'a st` fold mirror, `fun_of_st` simulation, generic `part_post_solution_st_to_abs_transport` + node-level `_eff` corollary |
| `Exec_Ctx_Bridge.thy` | context / context-seeded generator transport (`part_post_solution_ctx{,_seeded}_st_to_abs_eff`) |
| `Exec_Cmp_Bridge.thy` | cmp generator transport (`part_post_solution_cmp_st_to_abs_eff`) |
| `Solver_Side_RG.thy` | reach-global lemmas shared by the bridges |
