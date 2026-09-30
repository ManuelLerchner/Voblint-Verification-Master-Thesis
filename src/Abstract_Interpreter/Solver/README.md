# Solver

The equation language of the vendored side-effecting top-down solver
(`vendor/td-verification`, session `TD`), and nothing else: no CFG, no
domain, no analysis. The counterpart of Goblint's `goblint.constraint` and
`goblint.solver` libraries.

A right-hand side is a `strategy_tree` over the solver's four instructions:
`QueryL` reads a local unknown, `QueryG` reads a global one, `Side`
publishes a value under a global key, `Answer` yields the result. This
session gives that language a typed continuation-passing frontend whose
intermediate values need not be the solver carrier, a way to fold a
right-hand side from contribution programs, and the per-key buffering that keeps
repeated `Side` writes from destabilising an update rule.

| File | Role |
| --- | --- |
| `Strategy_Program_Fold.thy` | `fold_rhs_program_projected` and its identity instance `fold_rhs_program`: a right-hand side as a join-fold over contribution programs |
| `Strategy_Tree_Program.thy` | `strategy_program`, a typed continuation-passing frontend with do-notation: `sp_bind`'s intermediate type need not be the solver carrier `'d`, only the final answer `sp_compile`/`sp_compile_with` encodes does. `sp_lift_tree` embeds an already-built vendor tree by recursing over its constructors directly |
| `Strategy_Tree_Side_Buffering.thy` | `buffer_sides`: one flush per key per evaluation |
| `TD_Solver_Bridge.thy` | `certified_solver`, the solver contract the pipeline assumes |

Algorithm correctness lives upstream: `TD.TD_side` proves `partial_correctness`
and `TD_side_mono`; `part_post_solution` (`TD.Basics_side`) is the certificate
every soundness endpoint in `Voblint_Framework` consumes. `DG_Indexed_Generator`
(`Voblint_Framework`) discharges `TD_side_mono`'s three preconditions for the
keyed generator from per-hook properties; they are the hypotheses of the
least-solution theorem for the solver without widening, which the shipped
analyses do not use. TD also provides the facts about its own definitions that
the rest of Voblint uses: `solve_dom_of_solve_c`, `part_post_solution_of_solve_c`
and `finite_stabl_solve` in `TD_side_upd_rule`, and `tree_covered_at`,
`part_post_solution_cong`, `mono_tree_deps` and the named conjuncts of
`part_post_solution` in `Basics_side`. The locale
`certified_solver` names the solver contract the analysis pipeline assumes
(post-solution, finite key set, `solve_c` success implies `solve_dom`), and
`td_certified_solver` (`Globals_Rule`) discharges it for every `globals_rule`;
the generated `<Domain>_Analyses.thy` registrations cite that one fact.
