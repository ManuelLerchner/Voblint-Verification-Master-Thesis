# Solver

The equation language of the vendored side-effecting top-down solver
(`vendor/td-verification`, session `TD`), and nothing else: no CFG, no
domain, no analysis. The counterpart of Goblint's `goblint.constraint` and
`goblint.solver` libraries.

A right-hand side is a `strategy_tree` over the solver's four instructions:
`QueryL` reads a local unknown, `QueryG` reads a global one, `Side`
publishes a value under a global key, `Answer` yields the result. This
session gives that language a monad, do-notation, named combinators, a way
to fold a right-hand side from contribution trees, a relabelling of unknowns
for context-sensitivity, and the per-key buffering that keeps repeated
`Side` writes from destabilising an update rule.

| File | Role |
| --- | --- |
| `Strategy_Tree_Monad.thy` | `seqcomp_tree`, bind and `do`-notation for strategy trees, and its environment-independent/monotone dependency facts |
| `Strategy_Tree_Rhs.thy` | `fold_rhs_trees`: a right-hand side as a join-fold over contribution trees |
| `Post_Solution.thy` | `se_constraint_holds`: what one unknown owes a `part_post_solution` |
| `Strategy_Tree_Relabel.thy` | `relabel_ltree`/`relabel_gtree`: reading a tree against a re-indexed unknown space |
| `Strategy_Tree_Combinators.thy` | `read_local`, `read_global`, `side_effect`, `answer`: named readings of the four constructors |
| `Side_Buffering.thy` | `buffer_sides`: one flush per key per evaluation |
| `Context_Refinement.thy` | A seeded valuation for a coarser system is a post-solution exactly when three per-unknown facts hold |

Algorithm correctness lives upstream: `TD.TD_side` proves `partial_correctness`
and `TD_side_mono`; `part_post_solution` (`TD.Basics_side`) is the certificate
every soundness endpoint in `Voblint_Core` consumes. `DG_Keyed_Generator`
(`Voblint_Core`) is what discharges `TD_side_mono`'s three preconditions for
the keyed generator, once, for an arbitrary generator instance.
