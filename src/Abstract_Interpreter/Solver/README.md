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
| `Strategy_Tree_Properties.thy` | `env_indep_deps`/`mono_tree_deps`: query-set dependency predicates on a tree *value*, independent of how the tree was built |
| `Strategy_Program_Fold.thy` | `fold_rhs_program_projected` and its identity instance `fold_rhs_program`: a right-hand side as a join-fold over contribution programs |
| `Strategy_Tree_Post_Solution.thy` | `tree_covered_at`: what one unknown owes a `part_post_solution` |
| `Strategy_Tree_Program.thy` | `strategy_program`, a typed continuation-passing frontend with do-notation: `sp_bind`'s intermediate type need not be the solver carrier `'d`, only the final answer `sp_compile`/`sp_compile_with` encodes does. `sp_lift_tree` embeds an already-built vendor tree by recursing over its constructors directly |
| `Strategy_Tree_Side_Buffering.thy` | `buffer_sides`: one flush per key per evaluation |
| `TD_Solver_Bridge.thy` | The semantic boundary to the vendored TD solver: an executable termination check to `solve_dom` to `part_post_solution`, proved once inside the vendored `TD_side_upd_rule` locale, for any update rule |

Algorithm correctness lives upstream: `TD.TD_side` proves `partial_correctness`
and `TD_side_mono`; `part_post_solution` (`TD.Basics_side`) is the certificate
every soundness endpoint in `Voblint_Framework` consumes. `DG_Keyed_Generator`
(`Voblint_Framework`) discharges `TD_side_mono`'s three preconditions for the
keyed generator from per-hook properties; they are the hypotheses of the
least-solution theorem for the solver without widening, which the shipped
analyses do not use. `TD_Solver_Bridge` packages TD's proof vocabulary
(`term_equivalence`, `solve_c_dom_def`, `partial_post_solution`) as
`part_post_solution_of_solve_c`, used by the Sign examples. The generated
`<Domain>_Analyses.thy` registrations cite TD's facts directly:
`TD_side_rule_Interp.partial_post_solution` for the certificate and
`TD_side_rule_Interp.solve_dom_of_solve_c` for the termination premise.
