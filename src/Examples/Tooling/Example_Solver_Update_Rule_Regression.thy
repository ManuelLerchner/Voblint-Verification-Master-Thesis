theory Example_Solver_Update_Rule_Regression
  imports
    "Voblint_Core.Solver_Side_RG"
    "Voblint_Analysis.Ivl_Exec"
begin

section \<open>Minimal update-rule regression: multiple Side writes per RHS evaluation (issue #121)\<close>

text \<open>
  Isolates the Voblint issue #121 regression at the vendored solver's own
  interface, independent of Interval program construction, CFG compilation, or
  \<open>is_bot_pred\<close> normalization: a single unknown \<open>()\<close> whose right-hand side
  reads global \<open>()\<close>, then issues \<^emph>\<open>two\<close> \<^const>\<open>depend_on\<close> (\<open>Side\<close>) writes to
  that same global before answering -- exactly the shape
  \<^const>\<open>unit_edge_tree_st\<close> produces per predecessor edge of a CFG merge node,
  collapsed to its essential two-write pattern.

  The first write is structurally \<^const>\<open>Bot\<close>; the second is an ordinary
  \<^const>\<open>Lifted\<close> value. \<^const>\<open>update_global_warrowing_apinis\<close>'s per-origin
  gate (\<open>rho_lookup (\<rho> state) g orig = d'\<close>, \<open>Update_rules.thy\<close>) compares each
  write against the previously \<^emph>\<open>stored\<close> per-origin contribution rather than
  the visible aggregate: since \<^const>\<open>Bot\<close> and \<open>Lifted _\<close> are never
  equal, every write in every pass reports a change, destabilizing this
  equation's own \<open>QueryG ()\<close> dependency and forcing an unbounded re-evaluation
  loop. This is not itself an executable fact and must not be encoded as one
  (a batch build evaluating a genuinely non-terminating term would hang); the
  hang was confirmed interactively (not batch-checked) during the issue #121
  investigation.

  The landed fix operates one layer up, at the RHS \<^emph>\<open>generator\<close> rather than the
  update rule: \<open>minimal_side_multiwrite_buffered_eqs\<close> below issues the \<^emph>\<open>same\<close>
  two contributions but folds them Side-free and publishes exactly one \<open>Side\<close>
  write per RHS evaluation, so the unmodified vendored
  \<^const>\<open>update_global_warrowing_apinis\<close> never sees more than one write to
  \<open>()\<close> in the first place.
\<close>

text \<open>
  Built from the exact production combinators (@{const unit_edge_tree_st},
  @{const fold_rhs_trees}), not a hand-rolled approximation -- \<open>v = True\<close> is a
  merge node fed by two edges from the same stable predecessor \<open>v = False\<close>,
  matching @{const side_rhs_fold_eff_st}'s own fold shape over
  @{const intra_predecessor_list}. The first edge's \<open>is_bot_pred\<close> is
  \<open>\<lambda>_. True\<close> (always normalizes to \<^const>\<open>Bot\<close>); the second's is \<open>\<lambda>_. False\<close>
  (never does), forcing the same \<^const>\<open>Bot\<close>/\<^const>\<open>Lifted\<close> split the real
  infeasible/feasible edge pair produces, without depending on interval
  filtering to manufacture it.
\<close>

definition minimal_side_multiwrite_eqs ::
  "(pp, unit, ivl resolved_st_q lifted) eqsT" where
  "minimal_side_multiwrite_eqs v =
     (if v = Statement 1 then
        fold_rhs_trees Bot
          [unit_edge_tree_st (\<lambda>_. True) id (Statement 0),
           unit_edge_tree_st (\<lambda>_. False) id (Statement 0)]
      else
        answer (Lifted cinit_ivl_st))"

text \<open>
  Aggregate gating alone is not the fix: with only one origin contributing to
  \<open>()\<close>, the visible aggregate genuinely passes through \<open>Lifted G \<rightarrow> Bot \<rightarrow>
  Lifted G\<close> mid-evaluation, so \<^emph>\<open>any\<close> gate comparing aggregates after each
  individual \<open>Side\<close> call -- not just a per-origin one -- destabilizes this
  node on its own still-in-progress evaluation and never converges
  (confirmed interactively during the issue #121 investigation; not encoded
  as an executable fact here, since a genuinely non-terminating \<open>by eval\<close>
  would hang the batch build). This is exactly why the landed fix operates
  at the \<^emph>\<open>generator\<close> layer instead: \<open>minimal_side_multiwrite_eqs\<close> above
  hangs because it issues \<^emph>\<open>two\<close> \<^const>\<open>Side\<close> writes to \<open>()\<close> within one RHS
  evaluation; the buffered generator never constructs more than one.
\<close>

text \<open>
  Buffered counterpart of \<^const>\<open>minimal_side_multiwrite_eqs\<close>: the same two
  predecessor contributions (\<open>is_bot_pred = \<lambda>_. True\<close> vs. \<open>\<lambda>_. False\<close>, so one
  contribution is structurally \<^const>\<open>Bot\<close> and the other \<^const>\<open>Lifted\<close>),
  built Side-free via \<^const>\<open>unit_edge_contribution_st\<close> and folded through
  the same untouched \<^const>\<open>fold_rhs_trees\<close>, then split into local
  \<^const>\<open>Answer\<close> and global \<^const>\<open>Side\<close> \<^emph>\<open>once\<close>, mirroring
  \<^const>\<open>make_side_rhs_tree_eff_st_buffered\<close>'s own shape without depending on
  a real \<^typ>\<open>cfg\<close>. Terminates under the completely unmodified vendored
  \<^const>\<open>TD_side_warrowing_apinis_Interp_solve_c\<close> -- no update-rule change
  needed once the generator publishes at most one \<open>Side\<close> write per RHS
  evaluation.
\<close>

definition minimal_side_multiwrite_buffered_eqs ::
  "(pp, unit, ivl resolved_st_q lifted) eqsT" where
  "minimal_side_multiwrite_buffered_eqs v =
     (if v = Statement 1 then
        seqcomp_tree
          (fold_rhs_trees Bot
            [unit_edge_contribution_st (\<lambda>_. True) id (Statement 0),
             unit_edge_contribution_st (\<lambda>_. False) id (Statement 0)])
          (\<lambda>res. depend_on () (map_lift restrict_global_resolved_q res)
                   (answer (map_lift restrict_local_resolved_q res)))
      else
        answer (Lifted cinit_ivl_st))"

lemma minimal_side_multiwrite_buffered_terminates:
  "TD_side_warrowing_apinis_Interp_solve_c minimal_side_multiwrite_buffered_eqs (Statement 1) \<noteq> None"
  by eval

section \<open>Order-sensitivity experiment: does predecessor evaluation order affect the result?\<close>

text \<open>
  \<^const>\<open>traverse_rhs\<close>/\<^const>\<open>sides_of_rhs\<close> (\<open>Basics_side.thy\<close>) -- the declarative
  reading of what an RHS \<^emph>\<open>means\<close>, underlying every fixpoint/soundness
  statement in this codebase -- read every \<^const>\<open>QueryL\<close>/\<^const>\<open>QueryG\<close> from
  the \<^emph>\<open>same fixed\<close> \<open>sigma\<close>, and fold \<^const>\<open>Side\<close> contributions into a result
  map without ever feeding a written value back into a later read in the same
  traversal. Declaratively, sibling predecessor contributions are already an
  order-independent join over a fixed incoming state -- generator buffering
  would only make the \<^emph>\<open>executable\<close> solver's per-evaluation behavior match
  this existing declarative reading more closely, not change it.

  This section checks whether the \<^emph>\<open>operational\<close> solver (which does thread
  \<open>\<sigma>\<close> imperatively through a single RHS evaluation, per
  \<open>TD_side_upd_rule.thy\<close>'s \<open>Side\<close> case) is actually sensitive to predecessor
  order for a global two predecessors both touch. Uses
  @{const TD_side_always_join_Interp_solve_c} (not warrowing/\<open>_agg\<close>): plain
  join has no widen/narrow-driven flip-flop risk, so it is safe to run to
  completion on this finite example regardless of the outcome.
\<close>

definition ord_gx :: vname where "ord_gx = STR ''g''"
definition ord_zy :: vname where "ord_zy = STR ''z''"

abbreviation ord_gs :: "vname \<Rightarrow> bool" where
  "ord_gs \<equiv> (\<lambda>x. x = ord_gx \<or> x = ord_zy)"

text \<open>\<open>fA\<close> always publishes \<open>g := [0,0]\<close>. \<open>fB\<close> reads the \<^emph>\<open>currently visible\<close>
  global \<open>g\<close> (via \<open>assemble_local_global\<close>'s reconstruction inside
  \<^const>\<open>unit_edge_tree_st\<close>) and sets local \<open>z\<close> to \<open>[1,1]\<close> if \<open>g\<close> still looks
  untouched (bottom) or \<open>[2,2]\<close> if it already reflects \<open>fA\<close>'s contribution --
  a direct probe for same-pass sibling visibility.\<close>

definition ord_fA :: "ivl resolved_st_q \<Rightarrow> ivl resolved_st_q" where
  "ord_fA s = update_resolved_st_q s (Global_Location ord_gx) (Ivl (Fin 0) (Fin 0))"

definition ord_fB :: "ivl resolved_st_q \<Rightarrow> ivl resolved_st_q" where
  "ord_fB s = update_resolved_st_q s (Global_Location ord_zy)
     (if lookup_resolved_st_q s (Global_Location ord_gx) = bot
      then Ivl (Fin 1) (Fin 1) else Ivl (Fin 2) (Fin 2))"

definition order_ab_eqs :: "(pp, unit, ivl resolved_st_q lifted) eqsT" where
  "order_ab_eqs v =
     (if v = Statement 2 then
        fold_rhs_trees Bot
          [unit_edge_tree_st (\<lambda>_. False) ord_fA (Statement 0),
           unit_edge_tree_st (\<lambda>_. False) ord_fB (Statement 1)]
      else answer (Lifted cinit_ivl_st))"

definition order_ba_eqs :: "(pp, unit, ivl resolved_st_q lifted) eqsT" where
  "order_ba_eqs v =
     (if v = Statement 2 then
        fold_rhs_trees Bot
          [unit_edge_tree_st (\<lambda>_. False) ord_fB (Statement 1),
           unit_edge_tree_st (\<lambda>_. False) ord_fA (Statement 0)]
      else answer (Lifted cinit_ivl_st))"

value "map_option (\<lambda>sol. fun_of_resolved_st_q_for ord_gs (case_lifted bot id (snd sol (Inr ()))) ord_gx)
         (TD_side_always_join_Interp_solve_c order_ab_eqs (Statement 2))"
value "map_option (\<lambda>sol. fun_of_resolved_st_q_for ord_gs (case_lifted bot id (snd sol (Inr ()))) ord_gx)
         (TD_side_always_join_Interp_solve_c order_ba_eqs (Statement 2))"
value "map_option (\<lambda>sol. fun_of_resolved_st_q_for ord_gs (case_lifted bot id (snd sol (Inr ()))) ord_zy)
         (TD_side_always_join_Interp_solve_c order_ab_eqs (Statement 2))"
value "map_option (\<lambda>sol. fun_of_resolved_st_q_for ord_gs (case_lifted bot id (snd sol (Inr ()))) ord_zy)
         (TD_side_always_join_Interp_solve_c order_ba_eqs (Statement 2))"

value "(bot :: ivl)"
value "(Ivl (Fin 1) (Fin 1)) \<squnion> (Ivl (Fin 2) (Fin 2))"

end
