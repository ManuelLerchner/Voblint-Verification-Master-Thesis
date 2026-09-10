# Authoring a D/G analysis

How to add a new abstract domain to the D/G solver pipeline without
constructing `strategy_tree` by hand. Term definitions are in
`docs/GLOSSARY.md`; the combinator design is in
`docs/history/DG_COMBINATOR_MIGRATION.md`.

## The steps

1. **Define the abstract domain.** Instantiate `sound_domain`
   (`src/Analysis/Generic/Domain/Abstract_Domain.thy`): carrier, order, and
   concretization.

2. **Prove transfer soundness.** Pure per-edge transfers as a
   `domain_transfer`, or side-effecting ones as an `effectful_domain_transfer`
   (`src/Analysis/Generic/Equations/Constraint_System.thy`).

3. **Package enter/combine as a `dg_spec`.** `dgs_enter`,
   `dgs_combine_env`/`dgs_combine_assign` (`DG_Constraint_Trees.thy`), proved to
   satisfy `sound_dg_spec_core`.

4. **Context-sensitive with one shared global and one routing policy:**
   interpret the `routed_context` locale
   (`src/Analysis/Generic/Solver/Context/DG/Routed_Context.thy`) instead of
   hand-writing `cmb`/`extra`. Fix `route`, `seed_key`, and the semantic
   context function `enterc`; discharge `route_enterc_agree`, `call_fwd`,
   `comb_fwd`, and `call_enter_store_agree`. CALL and COMB soundness
   (`routed_context_call`, `routed_context_comb`) follow as locale theorems —
   no per-instance strategy-tree proof. The equation system is then built from
   `routed_cmb`/`routed_extra` directly:

   ```isabelle
   definition my_eqs where
     "my_eqs = routed_node_rhs intra_predecessor_list (\<lambda>_. Global)
         my_route (routed_cmb S Global) (routed_extra g S Seed Global)
         g S bot0 s0d s0g"
   ```

   Worked examples: `src/Examples/Interval/Example_Interval_DG_Ctx_Flagship.thy`
   (partial-tabulation context) and `Example_Interval_DG_CallString.thy`
   (call-string context).

5. **Not context-sensitive** (e.g. plain named-global sharing, no routing):
   write the equation directly with the generic combinators instead of raw
   constructors:

   ```isabelle
   definition my_tree where
     "my_tree u = read_local u (\<lambda>d. read_global Gk (\<lambda>g.
        depend_on Gk (transfer_result d g) (answer (local_result d g))))"
   ```

   Worked example: `src/Analysis/Instances/NamedGlobalSign/Sign_Named_Global_Eff.thy`.

## What you should never need to write

- Raw `QueryL`/`QueryG`/`Side`/`Answer`. Reserved for
  `Strategy_Tree_Combinators.thy`, `Strategy_Tree_Monad.thy`,
  `DG_Transfer_Combinators.thy`, and core solver proof machinery that reasons
  about arbitrary trees generically.
- Manual `DG bot x` / `DG x bot` wrapping, or `fst`/`snd` on `dgs_enter`/
  `dgs_combine` — use `enter_global`/`enter_local`, `combine_global`/
  `combine_local`, `publish_global`/`publish_seed`, `return_local` (see the
  combinator table in `docs/GLOSSARY.md`).
- A hand-copied CALL/COMB soundness proof for a routed analysis — that is
  exactly what `routed_context` derives generically once, in step 4.

## If a combinator doesn't fit

Every equation still bottoms out in `answer`/`return_local`, so the existing
combinator set covers the full solver instruction set. If a new analysis
genuinely needs a shape none of them express, extend
`Strategy_Tree_Combinators.thy` (generic) or `DG_Transfer_Combinators.thy`
(DG-specific) with a new `abbreviation` rather than falling back to raw
constructors in the analysis file — see the design note in
`docs/history/DG_COMBINATOR_MIGRATION.md` on why `abbreviation`, not `definition`, is
the default shape.
