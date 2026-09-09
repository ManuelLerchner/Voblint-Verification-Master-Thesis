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
     routed_dg_pipeline.solution (int_tf_st_for mode) (int_dom_enter_st_for mode)
       cinit_int_dom_st (Analysis_Global ()) Activation_Seed (\<lambda>_. route_unit) ()
       TD_side_warrowing_apinis_Interp_solve gs p"

definition int_conf_terminates_prog_warrow :: "refine_mode \<Rightarrow> (vname \<Rightarrow> bool) \<Rightarrow> imp_prog \<Rightarrow> bool" where
  "int_conf_terminates_prog_warrow mode gs p =
     routed_dg_pipeline.terminates (int_tf_st_for mode) (int_dom_enter_st_for mode)
       cinit_int_dom_st (Analysis_Global ()) Activation_Seed (\<lambda>_. route_unit) ()
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

lemma fst_analyse_int_ctx_solved_warrow_for [simp]:
  "fst (analyse_int_ctx_solved_warrow_for mode gs p)
     = analyse_int_ctx_result_warrow_for mode gs p"
  by (simp add: analyse_int_ctx_solved_warrow_for_def fst_ctx_solved_for
      analyse_int_ctx_result_warrow_for_def)

subsection \<open>Result table and report under warrowing: call strings\<close>

text \<open>
  Only the solve differs from the always-join siblings in
  \<^theory>\<open>Voblint_Analysis_Int.Int_Analyses\<close>: the equation system, the routing
  pair and the classifier are the same arguments to the same assembly, so a
  discipline swap adds no construction of its own.
\<close>

definition analyse_int_call_string_result_for_warrow ::
    "nat \<Rightarrow> (vname \<Rightarrow> bool) \<Rightarrow> imp_prog
       \<Rightarrow> (call_string, int_dom abs_state) analysis_result" where
  "analyse_int_call_string_result_for_warrow k gs p =
     routed_dg_pipeline.result (int_tf_st_for Refine_Fixpoint)
       (int_dom_enter_st_for Refine_Fixpoint) cinit_int_dom_st
       Call_String_Context.Global Call_String_Context.Seed (\<lambda>_. cs_route k) []
       TD_side_warrowing_apinis_Interp_solve gs p"

definition analyse_int_call_string_result_warrow ::
    "nat \<Rightarrow> imp_prog \<Rightarrow> (call_string, int_dom abs_state) analysis_result" where
  "analyse_int_call_string_result_warrow k p =
     analyse_int_call_string_result_for_warrow k (declared_global p) p"

definition analyse_int_call_string_report_warrow ::
    "nat \<Rightarrow> imp_prog \<Rightarrow> (pp \<times> exp \<times> contextual_verdict) list" where
  "analyse_int_call_string_report_warrow k p =
     routed_dg_pipeline.verdict_report (int_tf_st_for Refine_Fixpoint)
       (int_dom_enter_st_for Refine_Fixpoint) cinit_int_dom_st
       Call_String_Context.Global Call_String_Context.Seed (\<lambda>_. cs_route k) []
       TD_side_warrowing_apinis_Interp_solve int_classify_check (declared_global p) p"

subsection \<open>Result table and report under warrowing: entry states\<close>

definition analyse_int_entry_state_result_for_warrow ::
    "(vname \<Rightarrow> bool) \<Rightarrow> imp_prog
       \<Rightarrow> (int_dom list, int_dom abs_state) analysis_result" where
  "analyse_int_entry_state_result_for_warrow gs p =
     routed_dg_pipeline.result (int_tf_st_for Refine_Fixpoint)
       (int_dom_enter_st_for Refine_Fixpoint) cinit_int_dom_st
       (Analysis_Global ()) Activation_Seed exec_formals_route []
       TD_side_warrowing_apinis_Interp_solve gs p"

definition analyse_int_entry_state_result_warrow ::
    "imp_prog \<Rightarrow> (int_dom list, int_dom abs_state) analysis_result" where
  "analyse_int_entry_state_result_warrow p =
     analyse_int_entry_state_result_for_warrow (declared_global p) p"

definition analyse_int_entry_state_report_warrow ::
    "imp_prog \<Rightarrow> (pp \<times> exp \<times> contextual_verdict) list" where
  "analyse_int_entry_state_report_warrow p =
     routed_dg_pipeline.verdict_report (int_tf_st_for Refine_Fixpoint)
       (int_dom_enter_st_for Refine_Fixpoint) cinit_int_dom_st
       (Analysis_Global ()) Activation_Seed exec_formals_route []
       TD_side_warrowing_apinis_Interp_solve int_classify_check (declared_global p) p"

end
