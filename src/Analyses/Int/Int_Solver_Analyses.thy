theory Int_Solver_Analyses
  imports Int_Analyses "Voblint_Result.Unit_DG_Analysis"
begin

chapter \<open>The same Int configurations, at the alternative solver disciplines\<close>

text \<open>
  Solver discipline is independent of context policy.
  \<^theory>\<open>Voblint_Analysis_Int.Int_Analyses\<close> supplies the three context
  configurations and their base always-join instances. This theory interprets
  the Apinis warrowing contract for each of them and publishes their result and
  report tables; the context-insensitive configuration's other three solvers are
  partial applications of one assembly, published downstream by
  \<open>Int_Checks\<close>.

  The \<^typ>\<open>refine_mode\<close> parameter remains an independent domain axis. Each
  block reuses an existing equation system and discharges the selected solver's
  post-solution and finite-key obligations; no product-domain reasoning is
  repeated here. Production reporting selects Apinis warrowing with
  \<^const>\<open>Refine_Fixpoint\<close>.
\<close>

subsection \<open>Solved-result table: Apinis warrowing\<close>

text \<open>
  Apinis warrowing is the discipline the production entry point selects, so its
  solve and its termination predicate carry names of their own here. What this
  table adds beyond the assembly application is the solved pair
  \<^const>\<open>ctx_solved_for\<close> needs, which the contextual configurations reuse.
\<close>

definition int_conf_sol_prog_warrow ::
    "refine_mode \<Rightarrow> (vname \<Rightarrow> bool) \<Rightarrow> imp_prog
       \<Rightarrow> (pp \<times> unit) set \<times> (pp \<times> unit + (unit, unit) routed_gk \<Rightarrow> (int_dom exec_dg_st lifted, int_dom exec_dg_st lifted) dg_state)" where
  "int_conf_sol_prog_warrow mode gs p =
     unit_dg_pipeline.solution (int_tf_st_for mode) (int_dom_enter_st_for mode)
       cinit_int_dom_st TD_side_warrowing_apinis_Interp_solve gs p"

definition int_conf_terminates_prog_warrow :: "refine_mode \<Rightarrow> (vname \<Rightarrow> bool) \<Rightarrow> imp_prog \<Rightarrow> bool" where
  "int_conf_terminates_prog_warrow mode gs p =
     unit_dg_pipeline.terminates (int_tf_st_for mode) (int_dom_enter_st_for mode)
       cinit_int_dom_st
       (TD_side_warrowing_apinis_Interp.solve_dom TYPE((unit, unit) routed_gk)
          TYPE((int_dom exec_dg_st lifted, int_dom exec_dg_st lifted) dg_state))
       gs p"

definition analyse_int_ctx_result_warrow_for ::
    "refine_mode \<Rightarrow> (vname \<Rightarrow> bool) \<Rightarrow> imp_prog \<Rightarrow> (unit, int_dom abs_state) analysis_result" where
  "analyse_int_ctx_result_warrow_for mode gs p =
     dg_result_for gs (declared_global_vars p) (int_conf_sol_prog_warrow mode gs p)"

text \<open>\<^const>\<open>ctx_solved_for\<close> at this domain's warrowing solve, with \<^const>\<open>Analysis_Global\<close>
  and \<^const>\<open>Activation_Seed\<close> handed to \<^const>\<open>seed_global_keys\<close> the way \<^const>\<open>routed_entry_seed_tree\<close>
  already takes them. The refinement mode is applied first, leaving the solve in the
  shape \<^const>\<open>ctx_solved_for\<close> takes.\<close>

definition analyse_int_ctx_solved_warrow_for ::
    "refine_mode \<Rightarrow> (vname \<Rightarrow> bool) \<Rightarrow> imp_prog
     \<Rightarrow> (unit, int_dom abs_state) analysis_result
          \<times> (String.literal \<times> int_dom abs_state lifted) list" where
  "analyse_int_ctx_solved_warrow_for mode =
     ctx_solved_for (int_conf_sol_prog_warrow mode) (unit_seed_global_keys (Analysis_Global ()) Activation_Seed)"

lemma fst_analyse_int_ctx_solved_warrow_for:
  "fst (analyse_int_ctx_solved_warrow_for mode gs p)
     = analyse_int_ctx_result_warrow_for mode gs p"
  by (simp add: analyse_int_ctx_solved_warrow_for_def fst_ctx_solved_for
      analyse_int_ctx_result_warrow_for_def)

subsection \<open>The certified executable post-solution under warrowing: call strings\<close>

context
  fixes mode :: refine_mode and gs :: "vname \<Rightarrow> bool" and empty_pred :: "int_dom exec_dg_st \<Rightarrow> bool"
    and Pi :: proc_table and ps :: "pname list" and k :: nat
  assumes solves: "ics_terminates_warrow k mode gs empty_pred Pi ps"
    and exact: "\<And>s. empty_pred s = is_empty_state (fun_of_resolved_st_q_for gs s)"
begin

lemma ics_solve_dom_warrow:
  "TD_side_warrowing_apinis_Interp.solve_dom TYPE(call_string_gk) TYPE((int_dom exec_dg_st lifted, int_dom exec_dg_st lifted) dg_state)
     (ics_eqs k mode gs empty_pred Pi ps) (cfg_exit (compile_prog Pi ps), [])"
  using solves[unfolded ics_terminates_warrow_def] .

lemma ics_pp_st_warrow:
  "part_post_solution (ics_eqs k mode gs empty_pred Pi ps) (cfg_exit (compile_prog Pi ps), [])
     (snd (ics_sol_warrow k mode gs empty_pred Pi ps)) (fst (ics_sol_warrow k mode gs empty_pred Pi ps))"
  using TD_side_warrowing_apinis_Interp.partial_post_solution
          [OF ics_solve_dom_warrow, of "fst (ics_sol_warrow k mode gs empty_pred Pi ps)"
             "snd (ics_sol_warrow k mode gs empty_pred Pi ps)"]
  unfolding ics_sol_warrow_def by simp

theorem ics_pp_routed_warrow:
  "part_post_solution
     (routed_node_rhs intra_predecessor_addr_list (\<lambda>_. Call_String_Context.Global)
        (cs_route k)
        (\<lambda>ctx' src a. dg_spec_edge_tree (int_dom_spec mode empty_pred gs) a src
           (\<lambda>_. Call_String_Context.Global))
        (routed_call_tree (int_dom_spec mode empty_pred gs) Call_String_Context.Global
           Call_String_Context.Seed (static_resolve (compile_prog Pi ps)) (\<lambda>d. d = Bot))
        (routed_entry_seed_tree Call_String_Context.Seed)
        (compile_prog Pi ps) Bot (Lifted cinit_int_dom_st) Bot)
     (cfg_exit (compile_prog Pi ps), [])
     (snd (ics_sol_warrow k mode gs empty_pred Pi ps))
     (fst (ics_sol_warrow k mode gs empty_pred Pi ps))"
  using ics_pp_st_warrow
  unfolding ics_eqs_def call_string_eqs_for_def compiled_routed_eqs_for_def
    int_dom_spec_def bot_lifted_eq
  by (rule int_cs_pp_st_gen[OF exact])
end

subsection \<open>Result table and report under warrowing: call strings\<close>

definition analyse_int_call_string_result_for_warrow ::
    "nat \<Rightarrow> (vname \<Rightarrow> bool) \<Rightarrow> imp_prog \<Rightarrow> (call_string, int_dom abs_state) analysis_result" where
  "analyse_int_call_string_result_for_warrow k gs p =
     dg_result_for gs (declared_global_vars p) (ics_sol_prog_warrow k gs p)"

definition analyse_int_call_string_result_warrow ::
    "nat \<Rightarrow> imp_prog \<Rightarrow> (call_string, int_dom abs_state) analysis_result" where
  "analyse_int_call_string_result_warrow k p =
     analyse_int_call_string_result_for_warrow k (declared_global p) p"

definition ics_verdict_report_prog_warrow ::
    "nat \<Rightarrow> imp_prog \<Rightarrow> (pp \<times> exp \<times> contextual_verdict) list" where
  "ics_verdict_report_prog_warrow k p =
     classify_checks_verdicts (prog_cfg p)
       (analyse_int_call_string_result_for_warrow k (declared_global p) p)
       int_classify_check"

definition analyse_int_call_string_report_warrow ::
    "nat \<Rightarrow> imp_prog \<Rightarrow> (pp \<times> exp \<times> contextual_verdict) list" where
  "analyse_int_call_string_report_warrow k p = ics_verdict_report_prog_warrow k p"


subsection \<open>The certified executable post-solution under warrowing: entry states\<close>

context
  fixes mode :: refine_mode and gs :: "vname \<Rightarrow> bool" and empty_pred :: "int_dom exec_dg_st \<Rightarrow> bool"
    and Pi :: proc_table and ps :: "pname list"
  assumes solves: "int_conf_entry_terminates_warrow mode gs empty_pred Pi ps"
    and exact: "\<And>s. empty_pred s = is_empty_state (fun_of_resolved_st_q_for gs s)"
begin

lemma int_conf_entry_solve_dom_warrow:
  "TD_side_warrowing_apinis_Interp.solve_dom TYPE((unit, int_dom list) routed_gk) TYPE((int_dom exec_dg_st lifted, int_dom exec_dg_st lifted) dg_state)
     (int_conf_entry_eqs mode gs empty_pred Pi ps) (cfg_exit (compile_prog Pi ps), [])"
  using solves[unfolded int_conf_entry_terminates_warrow_def] .

lemma int_conf_entry_pp_st_warrow:
  "part_post_solution (int_conf_entry_eqs mode gs empty_pred Pi ps) (cfg_exit (compile_prog Pi ps), [])
     (snd (int_conf_entry_sol_warrow mode gs empty_pred Pi ps)) (fst (int_conf_entry_sol_warrow mode gs empty_pred Pi ps))"
  using TD_side_warrowing_apinis_Interp.partial_post_solution
          [OF int_conf_entry_solve_dom_warrow, of "fst (int_conf_entry_sol_warrow mode gs empty_pred Pi ps)"
             "snd (int_conf_entry_sol_warrow mode gs empty_pred Pi ps)"]
  unfolding int_conf_entry_sol_warrow_def by simp

theorem int_conf_entry_pp_routed_warrow:
  "part_post_solution
     (routed_node_rhs intra_predecessor_addr_list (\<lambda>_. Analysis_Global ())
        (int_conf_entry_route_gen mode gs empty_pred)
        (\<lambda>ctx' src a. dg_spec_edge_tree (int_dom_spec mode empty_pred gs) a src (\<lambda>_. Analysis_Global ()))
        (routed_call_tree (int_dom_spec mode empty_pred gs) (Analysis_Global ()) Activation_Seed
           (static_resolve (compile_prog Pi ps)) (\<lambda>d. d = Bot))
        (routed_entry_seed_tree Activation_Seed)
        (compile_prog Pi ps) Bot (Lifted cinit_int_dom_st) Bot)
     (cfg_exit (compile_prog Pi ps), [])
     (snd (int_conf_entry_sol_warrow mode gs empty_pred Pi ps))
     (fst (int_conf_entry_sol_warrow mode gs empty_pred Pi ps))"
  using int_conf_entry_pp_st_warrow
  unfolding int_conf_entry_eqs_def compiled_routed_eqs_for_def int_dom_spec_def bot_lifted_eq
  by (rule int_es_pp_st_gen[OF exact])

end

subsection \<open>Result table and report under warrowing: entry states\<close>

definition analyse_int_entry_state_result_for_warrow ::
    "(vname \<Rightarrow> bool) \<Rightarrow> imp_prog \<Rightarrow> (int_dom list, int_dom abs_state) analysis_result" where
  "analyse_int_entry_state_result_for_warrow gs p =
     dg_result_for gs (declared_global_vars p) (int_conf_entry_sol_prog_warrow gs p)"

definition analyse_int_entry_state_result_warrow ::
    "imp_prog \<Rightarrow> (int_dom list, int_dom abs_state) analysis_result" where
  "analyse_int_entry_state_result_warrow p =
     analyse_int_entry_state_result_for_warrow (declared_global p) p"

definition int_conf_entry_verdict_report_prog_warrow ::
    "imp_prog \<Rightarrow> (pp \<times> exp \<times> contextual_verdict) list" where
  "int_conf_entry_verdict_report_prog_warrow p =
     classify_checks_verdicts (prog_cfg p)
       (analyse_int_entry_state_result_for_warrow (declared_global p) p)
       int_classify_check"

definition analyse_int_entry_state_report_warrow ::
    "imp_prog \<Rightarrow> (pp \<times> exp \<times> contextual_verdict) list" where
  "analyse_int_entry_state_report_warrow p = int_conf_entry_verdict_report_prog_warrow p"

end

