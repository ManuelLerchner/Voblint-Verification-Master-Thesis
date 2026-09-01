# Solver

The equation language of the vendored side-effecting top-down solver
(`vendor/td-verification`, session `TD`), and nothing else: no CFG, no
domain, no analysis. The counterpart of Goblint's `goblint.constraint` and
`goblint.solver` libraries.

A right-hand side is a `strategy_tree` over the solver's four instructions:
`QueryL` reads a local unknown, `QueryG` reads a global one, `Side`
publishes a value under a global key, `Answer` yields the result. This
session gives that language sequential composition and do-notation over its
own homogeneous carrier, a genuinely polymorphic typed frontend for
intermediate values that aren't that carrier, named combinators, a way to
fold a right-hand side from contribution trees, and the per-key buffering
that keeps repeated `Side` writes from destabilising an update rule.

| File | Role |
| --- | --- |
| `Strategy_Tree_Properties.thy` | `env_indep_deps`/`mono_tree_deps`: query-set dependency predicates on a tree *value*, independent of how the tree was built |
| `Strategy_Tree_Sequencing.thy` | `seqcomp_tree`, bind and `do`-notation for already-built strategy trees at their own homogeneous carrier, and how bind preserves `Strategy_Tree_Properties`'s predicates |
| `Strategy_Tree_Fold.thy` | `fold_rhs_trees`: a right-hand side as a join-fold over contribution trees |
| `Strategy_Tree_Post_Solution.thy` | `se_constraint_holds`: what one unknown owes a `part_post_solution` |
| `Strategy_Tree_Combinators.thy` | `read_local`, `read_global`, `side_effect`, `answer`: named readings of the four constructors |
| `Strategy_Tree_Program.thy` | `strategy_program`, a typed continuation-passing frontend, a sibling of `Strategy_Tree_Sequencing` rather than built on it: `sp_bind`'s intermediate type need not be the solver carrier `'d`, only `sp_run`/`sp_run_with`'s final answer does. `sp_lift_tree` embeds an already-built vendor tree by recursing over its constructors directly, the same way `seqcomp_tree` does -- raw and typed sequencing are two specializations of the same idea, neither built on the other |
| `Strategy_Tree_Side_Buffering.thy` | `buffer_sides`: one flush per key per evaluation |
| `TD_Solver_Bridge.thy` | The semantic boundary to the vendored TD solver: an executable termination check to `solve_dom` to `part_post_solution`, proved once inside the vendored `TD_side_upd_rule` locale, for any update rule |
| `TD_Solver_Menu.thy` | The named menu of concrete update-rule solvers (`join`, `per_origin`, `warrow`, `warrow_per_origin`) built on `TD_Solver_Bridge`; the sole point where this session names TD's concrete update-rule interpretations |

Algorithm correctness lives upstream: `TD.TD_side` proves `partial_correctness`
and `TD_side_mono`; `part_post_solution` (`TD.Basics_side`) is the certificate
every soundness endpoint in `Voblint_Core` consumes. `DG_Keyed_Generator`
(`Voblint_Core`) is what discharges `TD_side_mono`'s three preconditions for
the keyed generator, once, for an arbitrary generator instance. `TD_Solver_Bridge`
is this session's sole point of contact with TD's own proof vocabulary
(`term_equivalence`, `solve_c_dom_def`, `partial_post_solution`): every
domain/context instance reaches `solve_c`/`solve_dom`/`part_post_solution`
through it rather than re-deriving the same three-step bridge per instance.
