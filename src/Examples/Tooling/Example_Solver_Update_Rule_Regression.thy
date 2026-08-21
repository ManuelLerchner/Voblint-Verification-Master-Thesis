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
end

