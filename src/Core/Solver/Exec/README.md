# Solver exec bridge support — the `'a st` executable mirror

Association-list (`'a st`) mirrors of the solver fold plus the `fun_of_st`
transport that carries a concrete post-solution back to the abstract
`part_post_solution`. The generic transport
(`part_post_solution_st_to_abs_transport`) lives here; each remaining generator
variant is a thin corollary. See `../README.md` for the Core/Context/Exec split.

| File | Role |
| --- | --- |
| `Exec_Bridge.thy` | `'a st` fold mirror, `fun_of_st` simulation, generic `part_post_solution_st_to_abs_transport` + node-level `_eff` corollary |
| `Solver_Side_RG.thy` | reach-global lemmas shared by the executable bridge |
| `Solver_Menu.thy` | executable menu over join, per-origin, and warrowing solver update rules |
