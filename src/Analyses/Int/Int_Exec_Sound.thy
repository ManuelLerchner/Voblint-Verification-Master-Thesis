theory Int_Exec_Sound
  imports
    "Voblint_Framework.DG_Local_State_Spec"
    "Voblint_Result.DG_Result_Construction"
    "Voblint_Exec.DG_Local_State_Exec_Refinement"
    Int_Exec
    Int_Warrowing
    "Voblint_Compile.Compile_Invariants"
    "Voblint_CFG.CFG_Prune"
    "Voblint_VIMP.VIMP_Program"
    "TD.TD_side_upd_rule"
    "Voblint_Solver.TD_Solver_Bridge"
begin

section \<open>Native D/G runtime API: the composite integer domain\<close>

text \<open>
  The whole-state route for \<open>int_dom\<close> mirrors Interval's: the local unknown carries
  the reachability-lifted \<open>int_dom exec_dg_st\<close>, so a VIMP global lives exactly where a
  local does, with no separate flow-insensitive summary.

  The explicit \<^typ>\<open>refine_mode\<close> parameter keeps domain refinement orthogonal to
  equation generation and solver choice. Public production reporting later selects
  \<^const>\<open>Refine_Fixpoint\<close>; this lower runtime interface also supports
  \<^const>\<open>Refine_Never\<close> and \<^const>\<open>Refine_Once\<close>.

  Solved via \<^const>\<open>TD_side_warrowing_apinis_Interp_solve\<close>, not plain join: \<open>int_dom\<close>'s
  \<open>int_ivl\<close> component has the same unbounded integer bound Interval's own carrier does, so a
  loop-carried local value still needs Apinis warrowing for termination, exactly the reason
  Interval's own production route (\<open>analyse_interval_dg_for\<close>) already made this choice.
  \<^theory>\<open>Voblint_Analysis_Int.Int_Warrowing\<close>'s \<open>bounded_warrowing\<close> instance for \<open>int_dom\<close> is what
  makes the local unknown's type admit this solver at all.

  \<open>G\<close> stays diagonal at \<open>int_dom exec_dg_st lifted\<close>, matching what \<^const>\<open>unit_routed_eqs\<close>
  needs; its content is never read, since every field of \<^const>\<open>local_state_dg_spec_st_for_lifted\<close>
  threads its incoming \<open>g\<close> through unchanged.

  The equation system is \<^const>\<open>unit_routed_eqs\<close> at the unit context, the same routed
  generator every registration locale and every other flagship uses, so a VIMP call site
  publishes its callee's entry through an activation seed. \<open>p\<close> is an arbitrary
  \<^typ>\<open>imp_prog\<close>, so a call may genuinely occur; \<^const>\<open>TD_side_seed_join_warrowing_Interp_solve\<close>
  keeps that seed join-only while still warrowing the analysis global and every
  loop-carried local, mirroring Interval's own production route.
\<close>

text \<open>
  \<open>int_tf_st_for\<close>/\<open>int_dom_enter_st_for\<close> are production-selection
  dispatchers only: each mode case is a bare reference to its own
  \<open>Int_Exec\<close> definition, so none of the three modes' distinct capabilities
  collapse into them. In particular they do not imply a uniform monotonicity
  fact across modes -- \<open>Refine_Fixpoint\<close> still has none
  (\<^theory>\<open>Voblint_Analysis_Int.Int_Transfer\<close>'s own header explains why), and
  nothing below requires one; the production soundness route (the
  \<open>local_state_dg_exec_analysis\<close> locale, one session downstream) never cites
  transfer monotonicity.
\<close>



fun int_tf_st_for :: "refine_mode \<Rightarrow> (vname \<Rightarrow> bool) \<Rightarrow> edge_action \<Rightarrow>
    int_dom resolved_st_q \<Rightarrow> int_dom resolved_st_q" where
  "int_tf_st_for Refine_Never gs = int_tf_st_never_for gs"
| "int_tf_st_for Refine_Once gs = int_tf_st_once_for gs"
| "int_tf_st_for Refine_Fixpoint gs = int_tf_st_fixpoint_for gs"

fun int_dom_enter_st_for ::
    "refine_mode \<Rightarrow> (vname \<Rightarrow> bool) \<Rightarrow> call_info \<Rightarrow>
      int_dom resolved_st_q \<Rightarrow> int_dom resolved_st_q" where
  "int_dom_enter_st_for Refine_Never gs = int_dom_enter_never_st_for gs"
| "int_dom_enter_st_for Refine_Once gs = int_dom_enter_once_st_for gs"
| "int_dom_enter_st_for Refine_Fixpoint gs = int_dom_enter_fixpoint_st_for gs"

definition analyse_int_dg_eqs_for ::
  "refine_mode \<Rightarrow> (int_dom exec_dg_st \<Rightarrow> bool) \<Rightarrow> (vname \<Rightarrow> bool) \<Rightarrow> imp_prog \<Rightarrow>
     pp \<times> unit \<Rightarrow> (pp \<times> unit, (unit, unit) routed_gk,
       (int_dom exec_dg_st lifted, int_dom exec_dg_st lifted) dg_state) strategy_tree" where
  "analyse_int_dg_eqs_for mode empty_pred gs p =
     unit_routed_eqs
       (local_state_dg_spec_st_for_lifted gs empty_pred (int_tf_st_for mode gs) (int_dom_enter_st_for mode gs))
       (prog_cfg p) bot (Lifted cinit_int_dom_st) (Lifted cinit_int_dom_st)"

definition analyse_int_dg_for :: "refine_mode \<Rightarrow> (int_dom exec_dg_st \<Rightarrow> bool) \<Rightarrow> (vname \<Rightarrow> bool) \<Rightarrow> imp_prog \<Rightarrow>
    (pp \<times> unit) set
     \<times> (pp \<times> unit + (unit, unit) routed_gk \<Rightarrow> (int_dom exec_dg_st lifted, int_dom exec_dg_st lifted) dg_state)" where
  "analyse_int_dg_for mode empty_pred gs p =
     TD_side_seed_join_warrowing_Interp_solve is_activation_seed
       (analyse_int_dg_eqs_for mode empty_pred gs p)
       (cfg_exit (prog_cfg p), ())"

text \<open>
  The shared whole-state reader projects the solved local unknown at \<open>Inl (v, ())\<close>.
  Passing the solved map to \<^const>\<open>dg_env_for\<close> preserves the single-solve generated
  code shape for every refinement mode.
\<close>

definition analyse_int_dg_env_for ::
    "refine_mode \<Rightarrow> (int_dom exec_dg_st \<Rightarrow> bool) \<Rightarrow> (vname \<Rightarrow> bool) \<Rightarrow> imp_prog
       \<Rightarrow> pp \<Rightarrow> int_dom abs_state" where
  "analyse_int_dg_env_for mode empty_pred gs p =
     dg_env_for gs (snd (analyse_int_dg_for mode empty_pred gs p))"


text \<open>
  Convenience instances at \<^const>\<open>declared_global\<close> \<open>p\<close>, matching \<open>analyse_interval_dg_eqs\<close>/
  \<open>analyse_interval_dg\<close>/\<open>analyse_interval_dg_env\<close>'s shape. \<open>empty_pred\<close> is fixed here
  to \<^const>\<open>resolved_st_q_is_bot_for\<close> at \<open>p\<close>'s own \<^const>\<open>declared_global_vars\<close>, exact for
  \<^const>\<open>is_empty_state\<close> by @{thm resolved_st_q_is_bot_for_iff} (@{thm declared_global_iff}).
\<close>

definition analyse_int_dg_eqs :: "refine_mode \<Rightarrow> imp_prog \<Rightarrow>
    pp \<times> unit \<Rightarrow> (pp \<times> unit, (unit, unit) routed_gk,
      (int_dom exec_dg_st lifted, int_dom exec_dg_st lifted) dg_state) strategy_tree" where
  "analyse_int_dg_eqs mode p =
     analyse_int_dg_eqs_for mode (resolved_st_q_is_bot_for (declared_global_vars p)) (declared_global p) p"

definition analyse_int_dg :: "refine_mode \<Rightarrow> imp_prog \<Rightarrow>
    (pp \<times> unit) set
     \<times> (pp \<times> unit + (unit, unit) routed_gk \<Rightarrow> (int_dom exec_dg_st lifted, int_dom exec_dg_st lifted) dg_state)" where
  "analyse_int_dg mode p =
     analyse_int_dg_for mode (resolved_st_q_is_bot_for (declared_global_vars p)) (declared_global p) p"

definition analyse_int_dg_env :: "refine_mode \<Rightarrow> imp_prog \<Rightarrow> pp \<Rightarrow> int_dom abs_state" where
  "analyse_int_dg_env mode p =
     analyse_int_dg_env_for mode (resolved_st_q_is_bot_for (declared_global_vars p)) (declared_global p) p"

text \<open>
  Solver-choice variants: always-join and per-origin update rules, mirroring
  \<open>Interval_Exec_Sound.analyse_interval_dg_join_for\<close>/\<open>_per_origin_for\<close> exactly ---
  solving the same \<^const>\<open>analyse_int_dg_eqs_for\<close> equation system (\<open>mode\<close> included)
  under \<^const>\<open>TD_side_always_join_Interp_solve\<close>/\<open>TD_side_per_origin_Interp_solve\<close>
  instead of \<^const>\<open>TD_side_warrowing_apinis_Interp_solve\<close>, so the \<open>Analyse_Dispatch\<close>
  runtime dispatcher (in the downstream CLI session) can compare update rules on the
  identical equation system, the same role Interval's own join/per-origin variants
  already play there.
\<close>

definition analyse_int_dg_join_for :: "refine_mode \<Rightarrow> (int_dom exec_dg_st \<Rightarrow> bool) \<Rightarrow> (vname \<Rightarrow> bool) \<Rightarrow> imp_prog \<Rightarrow>
    (pp \<times> unit) set
     \<times> (pp \<times> unit + (unit, unit) routed_gk \<Rightarrow> (int_dom exec_dg_st lifted, int_dom exec_dg_st lifted) dg_state)" where
  "analyse_int_dg_join_for mode empty_pred gs p =
     TD_side_always_join_Interp_solve (analyse_int_dg_eqs_for mode empty_pred gs p)
       (cfg_exit (prog_cfg p), ())"

definition analyse_int_dg_join_env_for ::
    "refine_mode \<Rightarrow> (int_dom exec_dg_st \<Rightarrow> bool) \<Rightarrow> (vname \<Rightarrow> bool) \<Rightarrow> imp_prog
       \<Rightarrow> pp \<Rightarrow> int_dom abs_state" where
  "analyse_int_dg_join_env_for mode empty_pred gs p =
     dg_env_for gs (snd (analyse_int_dg_join_for mode empty_pred gs p))"


definition analyse_int_dg_per_origin_for :: "refine_mode \<Rightarrow> (int_dom exec_dg_st \<Rightarrow> bool) \<Rightarrow> (vname \<Rightarrow> bool) \<Rightarrow> imp_prog \<Rightarrow>
    (pp \<times> unit) set
     \<times> (pp \<times> unit + (unit, unit) routed_gk \<Rightarrow> (int_dom exec_dg_st lifted, int_dom exec_dg_st lifted) dg_state)" where
  "analyse_int_dg_per_origin_for mode empty_pred gs p =
     TD_side_per_origin_Interp_solve (analyse_int_dg_eqs_for mode empty_pred gs p)
       (cfg_exit (prog_cfg p), ())"

definition analyse_int_dg_per_origin_env_for ::
    "refine_mode \<Rightarrow> (int_dom exec_dg_st \<Rightarrow> bool) \<Rightarrow> (vname \<Rightarrow> bool) \<Rightarrow> imp_prog
       \<Rightarrow> pp \<Rightarrow> int_dom abs_state" where
  "analyse_int_dg_per_origin_env_for mode empty_pred gs p =
     dg_env_for gs (snd (analyse_int_dg_per_origin_for mode empty_pred gs p))"


end
