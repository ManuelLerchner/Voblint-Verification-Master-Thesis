theory Analysis_Run_Solver_Sound
  imports Analysis_Run_Ctx_Sound
begin

section \<open>The contextual configurations' tables, at an explicitly named discipline\<close>

text \<open>
  Which solver runs an equation system is independent of which context policy
  generated it, so a configuration naming an explicit discipline --- always-join,
  per-origin, warrowing-per-origin --- solves the system the policy's default
  solves and earns the same endpoint. Each table below is
  \<open>sound_table_of_activation\<close> at one registration's own solved table, coverage
  endpoints and finiteness fact: the endpoint does not know which discipline
  produced the table it reads.

  A registration fixed at interpretation time names its facts through its
  binder. One whose configuration carries a call-string bound \<open>k\<close> cannot, since no
  interpretation fixes a runtime parameter; it spells the pipeline application
  out in abbreviations and cites the registration's \<^verbatim>\<open>lemmas\<close> aliases instead.
\<close>

abbreviation int_es_join_terminates where
  "int_es_join_terminates \<equiv>
     routed_dg_pipeline.terminates (int_tf_st_for Refine_Fixpoint)
       (int_dom_enter_st_for Refine_Fixpoint) cinit_int_dom_st
       (Analysis_Global ()) Activation_Seed exec_formals_route []
       (TD_side_upd_rule.solve_dom init_basic_ug_state update_global_always_join)"

abbreviation int_es_join_ctx_succ where
  "int_es_join_ctx_succ \<equiv>
     routed_dg_pipeline.ctx_succ (int_tf_st_for Refine_Fixpoint)
       (int_dom_enter_st_for Refine_Fixpoint) cinit_int_dom_st
       (Analysis_Global ()) Activation_Seed exec_formals_route []
       TD_side_always_join_Interp_solve"

abbreviation int_es_join_vars where
  "int_es_join_vars \<equiv>
     routed_dg_pipeline.sol_vars (int_tf_st_for Refine_Fixpoint)
       (int_dom_enter_st_for Refine_Fixpoint) cinit_int_dom_st
       (Analysis_Global ()) Activation_Seed exec_formals_route []
       TD_side_always_join_Interp_solve"

abbreviation int_es_join_ctx_rel where
  "int_es_join_ctx_rel \<equiv>
     routed_dg_analysis.admitted_contexts (int_tf_st_for Refine_Fixpoint)
       (int_dom_enter_st_for Refine_Fixpoint) cinit_int_dom_st
       (Analysis_Global ()) Activation_Seed exec_formals_route []
       TD_side_always_join_Interp_solve"

abbreviation interval_cs_join_terminates where
  "interval_cs_join_terminates k \<equiv>
     routed_dg_pipeline.terminates ivl_tf_st_for ivl_enter_st_for cinit_ivl_st
       Call_String_Context.Global Call_String_Context.Seed (\<lambda>_. cs_route k) []
       (TD_side_upd_rule.solve_dom init_basic_ug_state update_global_always_join)"

abbreviation interval_cs_join_ctx_succ where
  "interval_cs_join_ctx_succ k \<equiv>
     routed_dg_pipeline.ctx_succ ivl_tf_st_for ivl_enter_st_for cinit_ivl_st
       Call_String_Context.Global Call_String_Context.Seed (\<lambda>_. cs_route k) []
       TD_side_always_join_Interp_solve"

abbreviation interval_cs_join_vars where
  "interval_cs_join_vars k \<equiv>
     routed_dg_pipeline.sol_vars ivl_tf_st_for ivl_enter_st_for cinit_ivl_st
       Call_String_Context.Global Call_String_Context.Seed (\<lambda>_. cs_route k) []
       TD_side_always_join_Interp_solve"

abbreviation interval_cs_join_result where
  "interval_cs_join_result k \<equiv>
     routed_dg_pipeline.result ivl_tf_st_for ivl_enter_st_for cinit_ivl_st
       Call_String_Context.Global Call_String_Context.Seed (\<lambda>_. cs_route k) []
       TD_side_always_join_Interp_solve"

abbreviation interval_cs_po_terminates where
  "interval_cs_po_terminates k \<equiv>
     routed_dg_pipeline.terminates ivl_tf_st_for ivl_enter_st_for cinit_ivl_st
       Call_String_Context.Global Call_String_Context.Seed (\<lambda>_. cs_route k) []
       (TD_side_upd_rule.solve_dom init_basic_ug_state update_global_per_origin)"

abbreviation interval_cs_po_ctx_succ where
  "interval_cs_po_ctx_succ k \<equiv>
     routed_dg_pipeline.ctx_succ ivl_tf_st_for ivl_enter_st_for cinit_ivl_st
       Call_String_Context.Global Call_String_Context.Seed (\<lambda>_. cs_route k) []
       TD_side_per_origin_Interp_solve"

abbreviation interval_cs_po_vars where
  "interval_cs_po_vars k \<equiv>
     routed_dg_pipeline.sol_vars ivl_tf_st_for ivl_enter_st_for cinit_ivl_st
       Call_String_Context.Global Call_String_Context.Seed (\<lambda>_. cs_route k) []
       TD_side_per_origin_Interp_solve"

abbreviation interval_cs_po_result where
  "interval_cs_po_result k \<equiv>
     routed_dg_pipeline.result ivl_tf_st_for ivl_enter_st_for cinit_ivl_st
       Call_String_Context.Global Call_String_Context.Seed (\<lambda>_. cs_route k) []
       TD_side_per_origin_Interp_solve"

abbreviation interval_cs_wpo_terminates where
  "interval_cs_wpo_terminates k \<equiv>
     routed_dg_pipeline.terminates ivl_tf_st_for ivl_enter_st_for cinit_ivl_st
       Call_String_Context.Global Call_String_Context.Seed (\<lambda>_. cs_route k) []
       (TD_side_upd_rule.solve_dom init_basic_ug_state update_global_warrowing_per_origin)"

abbreviation interval_cs_wpo_ctx_succ where
  "interval_cs_wpo_ctx_succ k \<equiv>
     routed_dg_pipeline.ctx_succ ivl_tf_st_for ivl_enter_st_for cinit_ivl_st
       Call_String_Context.Global Call_String_Context.Seed (\<lambda>_. cs_route k) []
       TD_side_warrowing_per_origin_Interp_solve"

abbreviation interval_cs_wpo_vars where
  "interval_cs_wpo_vars k \<equiv>
     routed_dg_pipeline.sol_vars ivl_tf_st_for ivl_enter_st_for cinit_ivl_st
       Call_String_Context.Global Call_String_Context.Seed (\<lambda>_. cs_route k) []
       TD_side_warrowing_per_origin_Interp_solve"

abbreviation interval_cs_wpo_result where
  "interval_cs_wpo_result k \<equiv>
     routed_dg_pipeline.result ivl_tf_st_for ivl_enter_st_for cinit_ivl_st
       Call_String_Context.Global Call_String_Context.Seed (\<lambda>_. cs_route k) []
       TD_side_warrowing_per_origin_Interp_solve"

abbreviation int_cs_join_terminates where
  "int_cs_join_terminates k \<equiv>
     routed_dg_pipeline.terminates (int_tf_st_for Refine_Fixpoint)
       (int_dom_enter_st_for Refine_Fixpoint) cinit_int_dom_st
       Call_String_Context.Global Call_String_Context.Seed (\<lambda>_. cs_route k) []
       (TD_side_upd_rule.solve_dom init_basic_ug_state update_global_always_join)"

abbreviation int_cs_join_ctx_succ where
  "int_cs_join_ctx_succ k \<equiv>
     routed_dg_pipeline.ctx_succ (int_tf_st_for Refine_Fixpoint)
       (int_dom_enter_st_for Refine_Fixpoint) cinit_int_dom_st
       Call_String_Context.Global Call_String_Context.Seed (\<lambda>_. cs_route k) []
       TD_side_always_join_Interp_solve"

abbreviation int_cs_join_vars where
  "int_cs_join_vars k \<equiv>
     routed_dg_pipeline.sol_vars (int_tf_st_for Refine_Fixpoint)
       (int_dom_enter_st_for Refine_Fixpoint) cinit_int_dom_st
       Call_String_Context.Global Call_String_Context.Seed (\<lambda>_. cs_route k) []
       TD_side_always_join_Interp_solve"

subsection \<open>Entry state\<close>

lemma interval_es_join_table:
  assumes wf: "wf_program_compile_input p"
    and cov: "interval_es_join.terminates (declared_global p) p"
  shows "sound_table p (interval_es_join.result (declared_global p) p) interval_classify_check"
proof (rule sound_table_of_activation
    [where R = "interval_es_join.admitted_contexts (declared_global p) p" and rc = "[]",
     OF _ _ _ interval_classify_check_proved interval_classify_check_refuted], goal_cases)
  case (1 u)
  show ?case
    by (simp add: interval_es_join.entry_state_ltr_collect_eq_Union_of_terminates [OF wf cov])
next
  case (2 u ctx)
  show ?case
    using interval_es_join.entry_state_activation_collect_sound_of_terminates [OF wf cov]
    unfolding interval_es_join.gamma_reader_eq_lookup .
next
  case 3
  show ?case
    using interval_es_join.vars_finite_of_terminates [OF cov]
    by (simp add: finite_analysis_result_def interval_es_join.result_def
        interval_es_join.sol_vars_def)
qed

lemma interval_es_po_table:
  assumes wf: "wf_program_compile_input p"
    and cov: "interval_es_po.terminates (declared_global p) p"
  shows "sound_table p (interval_es_po.result (declared_global p) p) interval_classify_check"
proof (rule sound_table_of_activation
    [where R = "interval_es_po.admitted_contexts (declared_global p) p" and rc = "[]",
     OF _ _ _ interval_classify_check_proved interval_classify_check_refuted], goal_cases)
  case (1 u)
  show ?case
    by (simp add: interval_es_po.entry_state_ltr_collect_eq_Union_of_terminates [OF wf cov])
next
  case (2 u ctx)
  show ?case
    using interval_es_po.entry_state_activation_collect_sound_of_terminates [OF wf cov]
    unfolding interval_es_po.gamma_reader_eq_lookup .
next
  case 3
  show ?case
    using interval_es_po.vars_finite_of_terminates [OF cov]
    by (simp add: finite_analysis_result_def interval_es_po.result_def
        interval_es_po.sol_vars_def)
qed

lemma interval_es_wpo_table:
  assumes wf: "wf_program_compile_input p"
    and cov: "interval_es_wpo.terminates (declared_global p) p"
  shows "sound_table p (interval_es_wpo.result (declared_global p) p) interval_classify_check"
proof (rule sound_table_of_activation
    [where R = "interval_es_wpo.admitted_contexts (declared_global p) p" and rc = "[]",
     OF _ _ _ interval_classify_check_proved interval_classify_check_refuted], goal_cases)
  case (1 u)
  show ?case
    by (simp add: interval_es_wpo.entry_state_ltr_collect_eq_Union_of_terminates [OF wf cov])
next
  case (2 u ctx)
  show ?case
    using interval_es_wpo.entry_state_activation_collect_sound_of_terminates [OF wf cov]
    unfolding interval_es_wpo.gamma_reader_eq_lookup .
next
  case 3
  show ?case
    using interval_es_wpo.vars_finite_of_terminates [OF cov]
    by (simp add: finite_analysis_result_def interval_es_wpo.result_def
        interval_es_wpo.sol_vars_def)
qed

lemma int_es_join_table:
  assumes wf: "wf_program_compile_input p"
    and cov: "int_es_join_terminates (declared_global p) p"
  shows "sound_table p (analyse_int_entry_state_result p) int_classify_check"
proof (rule sound_table_of_activation
    [where R = "int_es_join_ctx_rel (declared_global p) p" and rc = "[]",
     OF _ _ _ int_classify_check_proved int_classify_check_refuted], goal_cases)
  case (1 u)
  show ?case
    by (simp add: analyse_int_entry_state_ltr_collect_eq_Union_of_terminates [OF wf cov])
next
  case (2 u ctx)
  show ?case
    using analyse_int_entry_state_sound_of_terminates [OF wf cov]
    unfolding analyse_int_entry_state_result_def analyse_int_entry_state_result_for_def
      analyse_int_entry_state_gamma_reader_eq_lookup .
next
  case 3
  show ?case
    using analyse_int_entry_state_vars_finite [OF cov]
    by (simp add: finite_analysis_result_def analyse_int_entry_state_result_def
        analyse_int_entry_state_result_for_def
        routed_dg_pipeline.result_def routed_dg_pipeline.sol_vars_def)
qed

subsection \<open>Call string\<close>

lemma interval_cs_join_table:
  assumes wf: "wf_program_compile_input p"
    and cov: "interval_cs_join_terminates k (declared_global p) p"
  shows "sound_table p (interval_cs_join_result k (declared_global p) p) interval_classify_check"
proof (rule sound_table_of_activation
    [where R = "call_context_rel_of_fun (\<lambda>u c t. cs_context k u c t)" and rc = "[]",
     OF _ _ _ interval_classify_check_proved interval_classify_check_refuted], goal_cases)
  case (1 u)
  show ?case
    by (rule equalityD1
          [OF analyse_interval_call_string_ltr_collect_eq_Union_join
              [where ctx_fun = "cs_context k"]])
next
  case (2 u ctx)
  show ?case
    using analyse_interval_call_string_sound_of_terminates_join [OF wf cov,
       where s = "\<lambda>u c t. t"]
    unfolding analyse_interval_call_string_gamma_reader_eq_lookup_join .
next
  case 3
  show ?case
    using analyse_interval_call_string_vars_finite_join [OF cov]
    by (simp add: finite_analysis_result_def routed_dg_pipeline.result_def
        routed_dg_pipeline.sol_vars_def)
qed

lemma interval_cs_po_table:
  assumes wf: "wf_program_compile_input p"
    and cov: "interval_cs_po_terminates k (declared_global p) p"
  shows "sound_table p (interval_cs_po_result k (declared_global p) p) interval_classify_check"
proof (rule sound_table_of_activation
    [where R = "call_context_rel_of_fun (\<lambda>u c t. cs_context k u c t)" and rc = "[]",
     OF _ _ _ interval_classify_check_proved interval_classify_check_refuted], goal_cases)
  case (1 u)
  show ?case
    by (rule equalityD1
          [OF analyse_interval_call_string_ltr_collect_eq_Union_po
              [where ctx_fun = "cs_context k"]])
next
  case (2 u ctx)
  show ?case
    using analyse_interval_call_string_sound_of_terminates_po [OF wf cov,
       where s = "\<lambda>u c t. t"]
    unfolding analyse_interval_call_string_gamma_reader_eq_lookup_po .
next
  case 3
  show ?case
    using analyse_interval_call_string_vars_finite_po [OF cov]
    by (simp add: finite_analysis_result_def routed_dg_pipeline.result_def
        routed_dg_pipeline.sol_vars_def)
qed

lemma interval_cs_wpo_table:
  assumes wf: "wf_program_compile_input p"
    and cov: "interval_cs_wpo_terminates k (declared_global p) p"
  shows "sound_table p (interval_cs_wpo_result k (declared_global p) p) interval_classify_check"
proof (rule sound_table_of_activation
    [where R = "call_context_rel_of_fun (\<lambda>u c t. cs_context k u c t)" and rc = "[]",
     OF _ _ _ interval_classify_check_proved interval_classify_check_refuted], goal_cases)
  case (1 u)
  show ?case
    by (rule equalityD1
          [OF analyse_interval_call_string_ltr_collect_eq_Union_wpo
              [where ctx_fun = "cs_context k"]])
next
  case (2 u ctx)
  show ?case
    using analyse_interval_call_string_sound_of_terminates_wpo [OF wf cov,
       where s = "\<lambda>u c t. t"]
    unfolding analyse_interval_call_string_gamma_reader_eq_lookup_wpo .
next
  case 3
  show ?case
    using analyse_interval_call_string_vars_finite_wpo [OF cov]
    by (simp add: finite_analysis_result_def routed_dg_pipeline.result_def
        routed_dg_pipeline.sol_vars_def)
qed

lemma int_cs_join_table:
  assumes wf: "wf_program_compile_input p"
    and cov: "int_cs_join_terminates k (declared_global p) p"
  shows "sound_table p (analyse_int_call_string_result k p) int_classify_check"
proof (rule sound_table_of_activation
    [where R = "call_context_rel_of_fun (\<lambda>u c t. cs_context k u c t)" and rc = "[]",
     OF _ _ _ int_classify_check_proved int_classify_check_refuted], goal_cases)
  case (1 u)
  show ?case
    by (rule equalityD1
          [OF analyse_int_call_string_ltr_collect_eq_Union [where ctx_fun = "cs_context k"]])
next
  case (2 u ctx)
  show ?case
    using analyse_int_call_string_sound_of_terminates [OF wf cov,
       where s = "\<lambda>u c t. t"]
    unfolding analyse_int_call_string_result_def analyse_int_call_string_result_for_def
      analyse_int_call_string_gamma_reader_eq_lookup .
next
  case 3
  show ?case
    using analyse_int_call_string_vars_finite [OF cov]
    by (simp add: finite_analysis_result_def analyse_int_call_string_result_def
        analyse_int_call_string_result_for_def
        routed_dg_pipeline.result_def routed_dg_pipeline.sol_vars_def)
qed
end

