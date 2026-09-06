theory Sign_Exec_Sound
  imports
    Sign_Sound
    Sign_Exec
    "Voblint_Exec.Result_Normalization"
    "Voblint_Exec.DG_Local_State_Exec"
    "Voblint_Exec.Routed_Domain_Exec"
    "Voblint_Framework.Analysis_Result"
    "Voblint_Framework.Routed_Context_Unit"
    "Voblint_Solver.TD_Solver_Bridge"
    "Voblint_Compile.Compile_Invariants"
    "Voblint_CFG.CFG_Prune"
    "Voblint_VIMP.VIMP_Program"
    "TD.TD_side_upd_rule"
begin

section \<open>Native D/G runtime API: an arbitrary VIMP program\<close>

text \<open>
  What a caller runs when it has an \<^typ>\<open>imp_prog\<close> and wants an answer: the equation
  system that program generates at the context-insensitive route, the solver call that
  computes a solution for it, the termination side condition that call carries, and the
  result table the solution reads back into.

  Nothing here is a theorem about Sign.  The specification and its soundness are
  \<^theory>\<open>Voblint_Analysis_Sign.Sign_Sound\<close>'s, and the collecting-soundness half that turns a
  computed solution into a statement about source runs stays downstream, in the
  \<open>local_state_dg_exec_analysis\<close> locale a CLI entry point interprets.  This theory only
  \<^emph>\<open>computes\<close>, which is why it can sit below every context policy: the call-string and
  entry-state routes in \<open>Sign_Analyses\<close> build their own
  equation systems the same way, from the same \<^const>\<open>sctx_spec\<close>.

  Sign's lattice is finite, so the always-join update rule suffices and no widening is
  needed --- the reason \<open>sctx_sol\<close> names
  \<^const>\<open>TD_side_always_join_Interp_solve\<close> where Interval's counterpart must name a
  warrowing solver.  \<open>sctx_sol_prog_per_origin\<close> is the one solver-choice sibling
  kept here, for the comparisons the dispatcher exposes.
\<close>

subsection \<open>The routed equation system and its executable solution\<close>

definition sctx_eqs ::
    "(vname \<Rightarrow> bool) \<Rightarrow> (sign exec_dg_st \<Rightarrow> bool) \<Rightarrow> proc_table \<Rightarrow> pname list \<Rightarrow> (pp \<times> unit, (unit, unit) routed_gk, (sign exec_dg_st lifted, sign exec_dg_st lifted) dg_state) eqsT" where
  "sctx_eqs gs empty_pred Pi ps =
     routed_node_rhs_buffered intra_predecessor_addr_list (\<lambda>_. Analysis_Global ())
       route_unit
       (\<lambda>ctx' src a. dg_spec_edge_tree (sctx_spec gs empty_pred) a src (\<lambda>_. Analysis_Global ()))
       (routed_call_tree (sctx_spec gs empty_pred) (Analysis_Global ()) Activation_Seed
          (static_resolve (compile_prog Pi ps)) (\<lambda>d. d = Bot))
       (routed_entry_seed_tree Activation_Seed)
       (compile_prog Pi ps) Bot (Lifted cinit_sign_st) Bot"

definition sctx_sol ::
    "(vname \<Rightarrow> bool) \<Rightarrow> (sign exec_dg_st \<Rightarrow> bool) \<Rightarrow> proc_table \<Rightarrow> pname list \<Rightarrow> (pp \<times> unit) set \<times> (pp \<times> unit + (unit, unit) routed_gk \<Rightarrow> (sign exec_dg_st lifted, sign exec_dg_st lifted) dg_state)" where
  "sctx_sol gs empty_pred Pi ps =
     TD_side_always_join_Interp_solve (sctx_eqs gs empty_pred Pi ps)
       (cfg_exit (compile_prog Pi ps), ())"

definition sctx_terminates ::
    "(vname \<Rightarrow> bool) \<Rightarrow> (sign exec_dg_st \<Rightarrow> bool) \<Rightarrow> proc_table \<Rightarrow> pname list \<Rightarrow> bool" where
  "sctx_terminates gs empty_pred Pi ps =
     TD_side_always_join_Interp.solve_dom TYPE((unit, unit) routed_gk) TYPE((sign exec_dg_st lifted, sign exec_dg_st lifted) dg_state)
       (sctx_eqs gs empty_pred Pi ps) (cfg_exit (compile_prog Pi ps), ())"

lemma sctx_terminates_via_solve_c:
  assumes "TD_side_always_join_Interp_solve_c (sctx_eqs gs empty_pred Pi ps)
             (cfg_exit (compile_prog Pi ps), ()) \<noteq> None"
  shows "sctx_terminates gs empty_pred Pi ps"
  unfolding sctx_terminates_def
  by (rule TD_side_always_join_Interp.solve_dom_of_solve_c[OF assms])

lemma sctx_vars_finite:
  assumes "sctx_terminates gs empty_pred Pi ps"
  shows "finite (fst (sctx_sol gs empty_pred Pi ps))"
  using TD_side_always_join_Interp.finite_stabl_solve[
      OF assms[unfolded sctx_terminates_def]]
  unfolding sctx_sol_def TD_side_always_join_Interp_solve_def
  by simp

section \<open>Solved-result table\<close>

text \<open>
  Whole-program convenience layer, mirroring Interval's own \<open>entry_state_eqs_prog\<close>/
  \<open>entry_state_sol_prog\<close>/\<open>entry_state_terminates_prog\<close>. The result tables below read
  the raw executable solve through the same \<^const>\<open>canonicalize_lift\<close>/\<^const>\<open>normalize_point\<close>
  boundary Interval's own \<open>analyse_interval_entry_state_result_for\<close> already uses, and are the tables Sign's public
  API (\<open>Sign_Checks\<close>) redirects onto in production. Their soundness is established there
  through a \<open>dg_analysis_adapter\<close> interpretation of this file's own \<open>sctx_routed\<close>
  context, bridged to these executable tables by composing
  \<^const>\<open>canonicalize_lift\<close>'s witness-bottom collapse with
  \<^const>\<open>normalize_point\<close>'s readback.
\<close>

definition sctx_eqs_prog ::
    "(vname \<Rightarrow> bool) \<Rightarrow> imp_prog
       \<Rightarrow> (pp \<times> unit, (unit, unit) routed_gk, (sign exec_dg_st lifted, sign exec_dg_st lifted) dg_state) eqsT" where
  "sctx_eqs_prog gs p =
     sctx_eqs gs (resolved_st_q_is_bot_for (declared_global_vars p))
       (prog_table p) (prog_procs p)"

definition sctx_sol_prog ::
    "(vname \<Rightarrow> bool) \<Rightarrow> imp_prog
       \<Rightarrow> (pp \<times> unit) set \<times> (pp \<times> unit + (unit, unit) routed_gk \<Rightarrow> (sign exec_dg_st lifted, sign exec_dg_st lifted) dg_state)" where
  "sctx_sol_prog gs p =
     TD_side_always_join_Interp_solve (sctx_eqs_prog gs p) (cfg_exit (prog_cfg p), ())"

text \<open>
  Solver-choice sibling of \<^const>\<open>sctx_sol_prog\<close>: the same \<^const>\<open>sctx_eqs_prog\<close> equation
  system, solved under the per-origin update rule instead of the always-join rule production
  uses. \<open>Sign_Checks.analyse_sign_result_per_origin_for\<close> reads this table.
\<close>

definition sctx_sol_prog_per_origin ::
    "(vname \<Rightarrow> bool) \<Rightarrow> imp_prog
       \<Rightarrow> (pp \<times> unit) set \<times> (pp \<times> unit + (unit, unit) routed_gk \<Rightarrow> (sign exec_dg_st lifted, sign exec_dg_st lifted) dg_state)" where
  "sctx_sol_prog_per_origin gs p =
     TD_side_per_origin_Interp_solve (sctx_eqs_prog gs p) (cfg_exit (prog_cfg p), ())"

definition sctx_terminates_prog :: "(vname \<Rightarrow> bool) \<Rightarrow> imp_prog \<Rightarrow> bool" where
  "sctx_terminates_prog gs p =
     sctx_terminates gs (resolved_st_q_is_bot_for (declared_global_vars p))
       (prog_table p) (prog_procs p)"

lemma sctx_terminates_prog_via_solve_c:
  assumes "TD_side_always_join_Interp_solve_c
             (sctx_eqs gs (resolved_st_q_is_bot_for (declared_global_vars p))
                (prog_table p) (prog_procs p))
             (cfg_exit (compile_prog (prog_table p) (prog_procs p)), ()) \<noteq> None"
  shows "sctx_terminates_prog gs p"
  unfolding sctx_terminates_prog_def
  using assms by (rule sctx_terminates_via_solve_c)

definition analyse_sign_ctx_result_for ::
    "(vname \<Rightarrow> bool) \<Rightarrow> imp_prog \<Rightarrow> (unit, sign abs_state) analysis_result" where
  "analyse_sign_ctx_result_for gs p =
     Analysis_Result
       (fst (sctx_sol_prog gs p))
       (\<lambda>v ctx. normalize_point gs
                  (canonicalize_lift (resolved_st_q_is_bot_for (declared_global_vars p))
                    (locals (snd (sctx_sol_prog gs p) (Inl (v, ctx))))))"

text \<open>\<^const>\<open>ctx_solved_for\<close> at this domain's solve, with \<^const>\<open>Analysis_Global\<close> and
  \<^const>\<open>Activation_Seed\<close> handed to \<^const>\<open>seed_global_keys\<close> the way \<^const>\<open>routed_entry_seed_tree\<close>
  already takes them.\<close>

definition analyse_sign_ctx_solved_for ::
    "(vname \<Rightarrow> bool) \<Rightarrow> imp_prog
     \<Rightarrow> (unit, sign abs_state) analysis_result
          \<times> (String.literal \<times> sign abs_state lifted) list" where
  "analyse_sign_ctx_solved_for = ctx_solved_for sctx_sol_prog (unit_seed_global_keys (Analysis_Global ()) Activation_Seed)"

lemma fst_analyse_sign_ctx_solved_for:
  "fst (analyse_sign_ctx_solved_for gs p) = analyse_sign_ctx_result_for gs p"
  by (simp add: analyse_sign_ctx_solved_for_def fst_ctx_solved_for
      analyse_sign_ctx_result_for_def Let_def)

declare analyse_sign_ctx_result_for_def [code del]

lemma analyse_sign_ctx_result_for_code [code]:
  "analyse_sign_ctx_result_for gs p =
     (let sol = sctx_sol_prog gs p; gl = declared_global_vars p
      in Analysis_Result (fst sol)
           (\<lambda>v ctx. normalize_point gs
                      (canonicalize_lift (resolved_st_q_is_bot_for gl)
                        (locals (snd sol (Inl (v, ctx)))))))"
  unfolding analyse_sign_ctx_result_for_def Let_def by (rule refl)

definition analyse_sign_ctx_result :: "imp_prog \<Rightarrow> (unit, sign abs_state) analysis_result" where
  "analyse_sign_ctx_result p =
     analyse_sign_ctx_result_for (declared_global p) p"

text \<open>Per-origin sibling of \<^const>\<open>analyse_sign_ctx_result_for\<close>, reading
  \<^const>\<open>sctx_sol_prog_per_origin\<close> instead of \<^const>\<open>sctx_sol_prog\<close>.\<close>

definition analyse_sign_ctx_result_per_origin_for ::
    "(vname \<Rightarrow> bool) \<Rightarrow> imp_prog \<Rightarrow> (unit, sign abs_state) analysis_result" where
  "analyse_sign_ctx_result_per_origin_for gs p =
     Analysis_Result
       (fst (sctx_sol_prog_per_origin gs p))
       (\<lambda>v ctx. normalize_point gs
                  (canonicalize_lift (resolved_st_q_is_bot_for (declared_global_vars p))
                    (locals (snd (sctx_sol_prog_per_origin gs p) (Inl (v, ctx))))))"

declare analyse_sign_ctx_result_per_origin_for_def [code del]

lemma analyse_sign_ctx_result_per_origin_for_code [code]:
  "analyse_sign_ctx_result_per_origin_for gs p =
     (let sol = sctx_sol_prog_per_origin gs p; gl = declared_global_vars p
      in Analysis_Result (fst sol)
           (\<lambda>v ctx. normalize_point gs
                      (canonicalize_lift (resolved_st_q_is_bot_for gl)
                        (locals (snd sol (Inl (v, ctx)))))))"
  unfolding analyse_sign_ctx_result_per_origin_for_def Let_def by (rule refl)

definition analyse_sign_ctx_result_per_origin :: "imp_prog \<Rightarrow> (unit, sign abs_state) analysis_result" where
  "analyse_sign_ctx_result_per_origin p =
     analyse_sign_ctx_result_per_origin_for (declared_global p) p"

end
