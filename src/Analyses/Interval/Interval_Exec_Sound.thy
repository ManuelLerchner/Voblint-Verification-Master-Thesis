theory Interval_Exec_Sound
  imports Interval_Exec
          "Voblint_Result.DG_Result_Construction"
          "Voblint_Solver.TD_Solver_Bridge"
          "TD.TD_side_upd_rule"
          "Voblint_CFG.CFG_Prune"
          "Voblint_VIMP.VIMP_Program"
          "Voblint_Compile.Compile_Invariants"
          "Voblint_Exec.DG_Local_State_Exec_Refinement"
begin

section \<open>Native D/G runtime API: an arbitrary VIMP program\<close>

text \<open>
  A whole-state D/G route for Interval: the local unknown is the whole
  reachability-lifted abstract state (\<open>D\<close>), so a VIMP global lives exactly where
  a local does, with no separate flow-insensitive solver-global summary to route
  it through.

  Interval's local lattice has infinite height (an unbounded integer bound), so
  unlike a finite-height domain this route needs widening for termination: a
  loop-carried local bound still needs
  \<^const>\<open>TD_side_warrowing_apinis_Interp_solve\<close>, not the always-join rule ---
  \<open>Example_Interval_DG_Flagship\<close> demonstrates that solver terminating on a
  genuinely unbounded loop.

  Only raw computation lives here. \<open>Interval_Entry\<close> later composes this runtime
  interface with the reusable source-soundness endpoint; the CLI merely dispatches
  to that public analysis entry point.

  \<open>G\<close> stays diagonal at \<open>ivl exec_dg_st lifted\<close>, matching what \<open>unit_routed_eqs\<close>
  needs; its content is never read, since every field of
  \<^const>\<open>local_state_dg_spec_st_for_lifted\<close> threads its incoming \<open>g\<close> through unchanged.

  The equation system is \<^const>\<open>unit_routed_eqs\<close> at the unit context: the same
  routed generator every registration locale and every other flagship uses, so a
  VIMP call site publishes its callee's entry through an activation seed rather
  than through a second, unrouted call protocol. Since \<open>p\<close> is an arbitrary
  \<^typ>\<open>imp_prog\<close>, a call may genuinely occur, and the solver below --
  \<^const>\<open>TD_side_seed_join_warrowing_Interp_solve\<close> -- keeps that seed join-only
  while still warrowing the analysis global and every loop-carried local: an
  activation seed is the join of what its callers publish, and widening it would
  age the callee's entry before the callee has iterated at all.
\<close>

definition analyse_interval_dg_eqs_for ::
  "(ivl exec_dg_st \<Rightarrow> bool) \<Rightarrow> (vname \<Rightarrow> bool) \<Rightarrow> imp_prog \<Rightarrow>
     pp \<times> unit \<Rightarrow> (pp \<times> unit, (unit, unit) routed_gk,
       (ivl exec_dg_st lifted, ivl exec_dg_st lifted) dg_state) strategy_tree" where
  "analyse_interval_dg_eqs_for empty_pred gs p =
     unit_routed_eqs
       (local_state_dg_spec_st_for_lifted gs empty_pred
          (ivl_tf_st_for gs) (ivl_enter_st_for gs))
       (prog_cfg p) bot (Lifted cinit_ivl_st) (Lifted cinit_ivl_st)"

definition analyse_interval_dg_for ::
    "(ivl exec_dg_st \<Rightarrow> bool) \<Rightarrow> (vname \<Rightarrow> bool) \<Rightarrow> imp_prog \<Rightarrow>
     (pp \<times> unit) set
       \<times> (pp \<times> unit + (unit, unit) routed_gk
            \<Rightarrow> (ivl exec_dg_st lifted, ivl exec_dg_st lifted) dg_state)" where
  "analyse_interval_dg_for empty_pred gs p =
     TD_side_seed_join_warrowing_Interp_solve is_activation_seed
       (analyse_interval_dg_eqs_for empty_pred gs p)
       (cfg_exit (prog_cfg p), ())"

text \<open>
  The shared whole-state reader projects the solved local unknown at \<open>Inl (v, ())\<close>.
  Passing the solved map to \<^const>\<open>dg_env_for\<close> preserves the single-solve generated
  code shape: the call-by-value target evaluates that argument before returning the
  per-node reader.
\<close>

definition analyse_interval_dg_env_for ::
    "(ivl exec_dg_st \<Rightarrow> bool) \<Rightarrow> (vname \<Rightarrow> bool) \<Rightarrow> imp_prog \<Rightarrow> pp \<Rightarrow> ivl abs_state" where
  "analyse_interval_dg_env_for empty_pred gs p =
     dg_env_for gs (snd (analyse_interval_dg_for empty_pred gs p))"


text \<open>
  Convenience instances at \<^const>\<open>declared_global\<close> \<open>p\<close>, the classifier every
  caller with only an \<^typ>\<open>imp_prog\<close> in hand recomputes anyway.
  \<open>empty_pred\<close> is fixed here to
  \<^const>\<open>resolved_st_q_is_bot_for\<close> at \<open>p\<close>'s own \<^const>\<open>declared_global_vars\<close>, exact for
  \<^const>\<open>is_empty_state\<close> by @{thm resolved_st_q_is_bot_for_iff} (@{thm declared_global_iff}).
\<close>

definition analyse_interval_dg_eqs :: "imp_prog \<Rightarrow>
    pp \<times> unit \<Rightarrow> (pp \<times> unit, (unit, unit) routed_gk,
      (ivl exec_dg_st lifted, ivl exec_dg_st lifted) dg_state) strategy_tree" where
  "analyse_interval_dg_eqs p =
     analyse_interval_dg_eqs_for
       (resolved_st_q_is_bot_for (declared_global_vars p)) (declared_global p) p"

definition analyse_interval_dg ::
    "imp_prog \<Rightarrow>
     (pp \<times> unit) set
       \<times> (pp \<times> unit + (unit, unit) routed_gk
            \<Rightarrow> (ivl exec_dg_st lifted, ivl exec_dg_st lifted) dg_state)" where
  "analyse_interval_dg p =
     analyse_interval_dg_for
       (resolved_st_q_is_bot_for (declared_global_vars p)) (declared_global p) p"

definition analyse_interval_dg_env :: "imp_prog \<Rightarrow> pp \<Rightarrow> ivl abs_state" where
  "analyse_interval_dg_env p =
     analyse_interval_dg_env_for
       (resolved_st_q_is_bot_for (declared_global_vars p)) (declared_global p) p"

subsection \<open>Join and per-origin update rules, on the same equation system\<close>

text \<open>
  \<open>analyse_interval_dg_join_for\<close>/\<open>analyse_interval_dg_per_origin_for\<close> are
  \<^const>\<open>analyse_interval_dg_for\<close>'s siblings under the always-join and per-origin update rules
  (\<^const>\<open>TD_side_always_join_Interp_solve\<close>, \<^const>\<open>TD_side_per_origin_Interp_solve\<close>) instead of
  Apinis warrowing --- solving the exact same \<^const>\<open>analyse_interval_dg_eqs_for\<close> equation
  system, so a VIMP global still lives only in the reachability-lifted local unknown, with no
  separate flow-insensitive summary reintroduced for either update rule. Both get
  the same \<open>_env_for\<close> reading layer \<^const>\<open>analyse_interval_dg_env_for\<close> already
  has, so their soundness proofs (in the Examples session, downstream) reuse the
  identical \<open>local_state_dg_exec_analysis\<close> proof shape the warrowing route uses, not a
  bespoke argument per update rule.
\<close>

definition analyse_interval_dg_join_for ::
    "(ivl exec_dg_st \<Rightarrow> bool) \<Rightarrow> (vname \<Rightarrow> bool) \<Rightarrow> imp_prog \<Rightarrow>
     (pp \<times> unit) set
       \<times> (pp \<times> unit + (unit, unit) routed_gk
            \<Rightarrow> (ivl exec_dg_st lifted, ivl exec_dg_st lifted) dg_state)" where
  "analyse_interval_dg_join_for empty_pred gs p =
     TD_side_always_join_Interp_solve (analyse_interval_dg_eqs_for empty_pred gs p)
       (cfg_exit (prog_cfg p), ())"

definition analyse_interval_dg_per_origin_for ::
    "(ivl exec_dg_st \<Rightarrow> bool) \<Rightarrow> (vname \<Rightarrow> bool) \<Rightarrow> imp_prog \<Rightarrow>
     (pp \<times> unit) set
       \<times> (pp \<times> unit + (unit, unit) routed_gk
            \<Rightarrow> (ivl exec_dg_st lifted, ivl exec_dg_st lifted) dg_state)" where
  "analyse_interval_dg_per_origin_for empty_pred gs p =
     TD_side_per_origin_Interp_solve (analyse_interval_dg_eqs_for empty_pred gs p)
       (cfg_exit (prog_cfg p), ())"

end
