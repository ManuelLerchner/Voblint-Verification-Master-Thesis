theory Analysis_Run_Ctx_Sound
  imports Analysis_Run_Sound
begin

section \<open>The contextual configurations' tables, at each policy's default discipline\<close>

text \<open>
  A context-sensitive table has one entry per point and context. Each domain
  publishes its soundness in activation form: the activation buckets exhaust a
  point --- outright for a call string, which is a function of the call site and
  the caller's context, and for entry state from the totality of its context
  relation --- and each bucket is bounded by the entry filed under its context.
  \<open>sound_table_of_activation\<close> turns that into a \<open>sound_table\<close>, so each
  configuration below names its route's three published facts and its domain's
  classifier soundness, and nothing else.

  What the premises still ask for is the coverage the solve achieved: a
  termination fact and one \<^const>\<open>ctx_vars_cover\<close> closure fact, which nothing here
  proves for an arbitrary program. The same endpoint at an explicitly named
  discipline lives in \<open>Analysis_Run_Solver_Sound\<close>.

  A call-string route carries a runtime bound \<open>k\<close>, and Int's registrations a
  refinement mode, so neither exports a binder a caller outside can name. Their
  solve's termination, solved keys and successor function are spelled out from
  \<^locale>\<open>routed_dg_pipeline\<close> at the route's own operands instead.
\<close>

abbreviation sign_cs_terminates where
  "sign_cs_terminates k \<equiv>
     routed_dg_pipeline.terminates sign_tf_st_for sign_enter_st_for cinit_sign_st
       Call_String_Context.Global Call_String_Context.Seed (\<lambda>_. cs_route k) []
       (TD_side_upd_rule.solve_dom init_basic_ug_state update_global_always_join)"

abbreviation sign_cs_ctx_succ where
  "sign_cs_ctx_succ k \<equiv>
     routed_dg_pipeline.ctx_succ sign_tf_st_for sign_enter_st_for cinit_sign_st
       Call_String_Context.Global Call_String_Context.Seed (\<lambda>_. cs_route k) []
       TD_side_always_join_Interp_solve"

abbreviation sign_cs_vars where
  "sign_cs_vars k \<equiv>
     routed_dg_pipeline.sol_vars sign_tf_st_for sign_enter_st_for cinit_sign_st
       Call_String_Context.Global Call_String_Context.Seed (\<lambda>_. cs_route k) []
       TD_side_always_join_Interp_solve"

abbreviation parity_cs_terminates where
  "parity_cs_terminates k \<equiv>
     routed_dg_pipeline.terminates parity_tf_st_for parity_enter_st_for cinit_parity_st
       Call_String_Context.Global Call_String_Context.Seed (\<lambda>_. cs_route k) []
       (TD_side_upd_rule.solve_dom init_basic_ug_state update_global_always_join)"

abbreviation parity_cs_ctx_succ where
  "parity_cs_ctx_succ k \<equiv>
     routed_dg_pipeline.ctx_succ parity_tf_st_for parity_enter_st_for cinit_parity_st
       Call_String_Context.Global Call_String_Context.Seed (\<lambda>_. cs_route k) []
       TD_side_always_join_Interp_solve"

abbreviation parity_cs_vars where
  "parity_cs_vars k \<equiv>
     routed_dg_pipeline.sol_vars parity_tf_st_for parity_enter_st_for cinit_parity_st
       Call_String_Context.Global Call_String_Context.Seed (\<lambda>_. cs_route k) []
       TD_side_always_join_Interp_solve"

abbreviation congruence_cs_terminates where
  "congruence_cs_terminates k \<equiv>
     routed_dg_pipeline.terminates congruence_tf_st_for congruence_enter_st_for
       cinit_congruence_st Call_String_Context.Global Call_String_Context.Seed
       (\<lambda>_. cs_route k) []
       (TD_side_upd_rule.solve_dom init_basic_ug_state update_global_always_join)"

abbreviation congruence_cs_ctx_succ where
  "congruence_cs_ctx_succ k \<equiv>
     routed_dg_pipeline.ctx_succ congruence_tf_st_for congruence_enter_st_for
       cinit_congruence_st Call_String_Context.Global Call_String_Context.Seed
       (\<lambda>_. cs_route k) [] TD_side_always_join_Interp_solve"

abbreviation congruence_cs_vars where
  "congruence_cs_vars k \<equiv>
     routed_dg_pipeline.sol_vars congruence_tf_st_for congruence_enter_st_for
       cinit_congruence_st Call_String_Context.Global Call_String_Context.Seed
       (\<lambda>_. cs_route k) [] TD_side_always_join_Interp_solve"

abbreviation interval_cs_terminates where
  "interval_cs_terminates k \<equiv>
     routed_dg_pipeline.terminates ivl_tf_st_for ivl_enter_st_for cinit_ivl_st
       Call_String_Context.Global Call_String_Context.Seed (\<lambda>_. cs_route k) []
       (TD_side_upd_rule.solve_dom init_basic_ug_state update_global_warrowing_apinis)"

abbreviation interval_cs_ctx_succ where
  "interval_cs_ctx_succ k \<equiv>
     routed_dg_pipeline.ctx_succ ivl_tf_st_for ivl_enter_st_for cinit_ivl_st
       Call_String_Context.Global Call_String_Context.Seed (\<lambda>_. cs_route k) []
       TD_side_warrowing_apinis_Interp_solve"

abbreviation interval_cs_vars where
  "interval_cs_vars k \<equiv>
     routed_dg_pipeline.sol_vars ivl_tf_st_for ivl_enter_st_for cinit_ivl_st
       Call_String_Context.Global Call_String_Context.Seed (\<lambda>_. cs_route k) []
       TD_side_warrowing_apinis_Interp_solve"

abbreviation int_cs_terminates where
  "int_cs_terminates k \<equiv>
     routed_dg_pipeline.terminates (int_tf_st_for Refine_Fixpoint)
       (int_dom_enter_st_for Refine_Fixpoint) cinit_int_dom_st
       Call_String_Context.Global Call_String_Context.Seed (\<lambda>_. cs_route k) []
       (TD_side_upd_rule.solve_dom init_basic_ug_state update_global_warrowing_apinis)"

abbreviation int_cs_ctx_succ where
  "int_cs_ctx_succ k \<equiv>
     routed_dg_pipeline.ctx_succ (int_tf_st_for Refine_Fixpoint)
       (int_dom_enter_st_for Refine_Fixpoint) cinit_int_dom_st
       Call_String_Context.Global Call_String_Context.Seed (\<lambda>_. cs_route k) []
       TD_side_warrowing_apinis_Interp_solve"

abbreviation int_cs_vars where
  "int_cs_vars k \<equiv>
     routed_dg_pipeline.sol_vars (int_tf_st_for Refine_Fixpoint)
       (int_dom_enter_st_for Refine_Fixpoint) cinit_int_dom_st
       Call_String_Context.Global Call_String_Context.Seed (\<lambda>_. cs_route k) []
       TD_side_warrowing_apinis_Interp_solve"

abbreviation int_es_ctx_succ where
  "int_es_ctx_succ \<equiv>
     routed_dg_pipeline.ctx_succ
       (int_tf_st_for Refine_Fixpoint) (int_dom_enter_st_for Refine_Fixpoint)
       cinit_int_dom_st (Analysis_Global ()) Activation_Seed exec_formals_route []
       TD_side_warrowing_apinis_Interp_solve"

abbreviation int_es_terminates where
  "int_es_terminates \<equiv>
     routed_dg_pipeline.terminates
       (int_tf_st_for Refine_Fixpoint) (int_dom_enter_st_for Refine_Fixpoint)
       cinit_int_dom_st (Analysis_Global ()) Activation_Seed exec_formals_route []
       (TD_side_upd_rule.solve_dom init_basic_ug_state update_global_warrowing_apinis)"

abbreviation int_es_vars where
  "int_es_vars \<equiv>
     routed_dg_pipeline.sol_vars
       (int_tf_st_for Refine_Fixpoint) (int_dom_enter_st_for Refine_Fixpoint)
       cinit_int_dom_st (Analysis_Global ()) Activation_Seed exec_formals_route []
       TD_side_warrowing_apinis_Interp_solve"

abbreviation int_es_ctx_rel where
  "int_es_ctx_rel \<equiv>
     routed_dg_analysis.admitted_contexts
       (int_tf_st_for Refine_Fixpoint) (int_dom_enter_st_for Refine_Fixpoint)
       cinit_int_dom_st (Analysis_Global ()) Activation_Seed exec_formals_route []
       TD_side_warrowing_apinis_Interp_solve"

subsection \<open>Entry state\<close>

lemma sign_es_table:
  assumes cov: "sign_entry_state_terminates_for (declared_global p) p"
      "ctx_vars_cover (prog_cfg p) (sign_es.ctx_succ (declared_global p) p) []
         (sign_entry_state_vars (declared_global p) p)"
  shows "sound_table p (analyse_sign_entry_state_result p) sign_classify_check"
proof (rule sound_table_of_activation
    [where R = "sign_entry_state_context_rel (declared_global p) p" and rc = "[]",
     OF _ _ _ sign_classify_check_proved sign_classify_check_refuted], goal_cases)
  case (1 u)
  show ?case by (simp add: analyse_sign_entry_state_ltr_collect_eq_Union_of_cover [OF cov])
next
  case (2 u ctx)
  show ?case
    using analyse_sign_entry_state_sound_of_cover [OF cov]
    unfolding analyse_sign_entry_state_result_def
      analyse_sign_entry_state_gamma_reader_eq_lookup .
next
  case 3
  show ?case
    using sign_es.vars_finite_of_terminates [OF cov(1)]
    by (simp add: finite_analysis_result_def analyse_sign_entry_state_result_def
        sign_es.result_def sign_es.sol_vars_def)
qed

lemma parity_es_table:
  assumes cov: "parity_entry_state_terminates_for (declared_global p) p"
      "ctx_vars_cover (prog_cfg p) (parity_es.ctx_succ (declared_global p) p) []
         (parity_entry_state_vars (declared_global p) p)"
  shows "sound_table p (analyse_parity_entry_state_result p) parity_classify_check"
proof (rule sound_table_of_activation
    [where R = "parity_entry_state_context_rel (declared_global p) p" and rc = "[]",
     OF _ _ _ parity_classify_check_proved parity_classify_check_refuted], goal_cases)
  case (1 u)
  show ?case by (simp add: analyse_parity_entry_state_ltr_collect_eq_Union_of_cover [OF cov])
next
  case (2 u ctx)
  show ?case
    using analyse_parity_entry_state_sound_of_cover [OF cov]
    unfolding analyse_parity_entry_state_result_def
      analyse_parity_entry_state_gamma_reader_eq_lookup .
next
  case 3
  show ?case
    using parity_es.vars_finite_of_terminates [OF cov(1)]
    by (simp add: finite_analysis_result_def analyse_parity_entry_state_result_def
        parity_es.result_def parity_es.sol_vars_def)
qed

lemma congruence_es_table:
  assumes cov: "congruence_entry_state_terminates_for (declared_global p) p"
      "ctx_vars_cover (prog_cfg p) (congruence_es.ctx_succ (declared_global p) p) []
         (congruence_entry_state_vars (declared_global p) p)"
  shows "sound_table p (analyse_congruence_entry_state_result p) congruence_classify_check"
proof (rule sound_table_of_activation
    [where R = "congruence_entry_state_context_rel (declared_global p) p" and rc = "[]",
     OF _ _ _ congruence_classify_check_proved congruence_classify_check_refuted],
    goal_cases)
  case (1 u)
  show ?case
    by (simp add: analyse_congruence_entry_state_ltr_collect_eq_Union_of_cover [OF cov])
next
  case (2 u ctx)
  show ?case
    using analyse_congruence_entry_state_sound_of_cover [OF cov]
    unfolding analyse_congruence_entry_state_result_def
      analyse_congruence_entry_state_gamma_reader_eq_lookup .
next
  case 3
  show ?case
    using congruence_es.vars_finite_of_terminates [OF cov(1)]
    by (simp add: finite_analysis_result_def analyse_congruence_entry_state_result_def
        congruence_es.result_def congruence_es.sol_vars_def)
qed

lemma interval_es_table:
  assumes cov: "entry_state_terminates_prog (declared_global p) p"
      "ctx_vars_cover (prog_cfg p) (interval_es.ctx_succ (declared_global p) p) []
         (entry_state_vars_prog (declared_global p) p)"
  shows "sound_table p (analyse_interval_entry_state_result p) interval_classify_check"
proof (rule sound_table_of_activation
    [where R = "entry_state_context_rel (declared_global p) p" and rc = "[]",
     OF _ _ _ interval_classify_check_proved interval_classify_check_refuted], goal_cases)
  case (1 u)
  show ?case by (simp add: entry_state_ltr_collect_eq_Union_of_cover [OF cov])
next
  case (2 u ctx)
  show ?case
    using entry_state_activation_collect_sound_of_cover [OF cov]
    unfolding analyse_interval_entry_state_result_def entry_state_gamma_reader_eq_lookup .
next
  case 3
  show ?case
    using interval_es.vars_finite_of_terminates [OF cov(1)]
    by (simp add: finite_analysis_result_def analyse_interval_entry_state_result_def
        interval_es.result_def interval_es.sol_vars_def)
qed

lemma int_es_table:
  assumes cov: "int_es_terminates (declared_global p) p"
      "ctx_vars_cover (prog_cfg p) (int_es_ctx_succ (declared_global p) p) []
         (int_es_vars (declared_global p) p)"
  shows "sound_table p (analyse_int_entry_state_result_warrow p) int_classify_check"
proof (rule sound_table_of_activation
    [where R = "int_es_ctx_rel (declared_global p) p" and rc = "[]",
     OF _ _ _ int_classify_check_proved int_classify_check_refuted], goal_cases)
  case (1 u)
  show ?case
    by (simp add: analyse_int_entry_state_ltr_collect_eq_Union_of_cover_warrow [OF cov])
next
  case (2 u ctx)
  show ?case
    using analyse_int_entry_state_sound_of_cover_warrow [OF cov]
    by (simp add: analyse_int_entry_state_gamma_reader_eq_lookup_warrow
        analyse_int_entry_state_result_for_warrow_def analyse_int_entry_state_result_warrow_def)
next
  case 3
  show ?case
    using analyse_int_entry_state_vars_finite_warrow [OF cov(1)]
    by (simp add: finite_analysis_result_def analyse_int_entry_state_result_warrow_def
        analyse_int_entry_state_result_for_warrow_def
        routed_dg_pipeline.result_def routed_dg_pipeline.sol_vars_def)
qed

subsection \<open>Call string\<close>

lemma sign_cs_table:
  assumes cov: "sign_cs_terminates k (declared_global p) p"
      "ctx_vars_cover (prog_cfg p) (sign_cs_ctx_succ k (declared_global p) p) []
         (sign_cs_vars k (declared_global p) p)"
  shows "sound_table p (analyse_sign_call_string_result k p) sign_classify_check"
proof (rule sound_table_of_activation
    [where R = "call_context_rel_of_fun (\<lambda>u c t. cs_context k u c t)" and rc = "[]",
     OF _ _ _ sign_classify_check_proved sign_classify_check_refuted], goal_cases)
  case (1 u)
  show ?case
    by (rule equalityD1
          [OF analyse_sign_call_string_ltr_collect_eq_Union [where ctx_fun = "cs_context k"]])
next
  case (2 u ctx)
  show ?case
    using analyse_sign_call_string_sound_of_cover [OF cov, where s = "\<lambda>u c t. t"]
    unfolding analyse_sign_call_string_result_def
      analyse_sign_call_string_gamma_reader_eq_lookup .
next
  case 3
  show ?case
    using analyse_sign_call_string_vars_finite [OF cov(1)]
    by (simp add: finite_analysis_result_def analyse_sign_call_string_result_def
        routed_dg_pipeline.result_def routed_dg_pipeline.sol_vars_def)
qed

lemma parity_cs_table:
  assumes cov: "parity_cs_terminates k (declared_global p) p"
      "ctx_vars_cover (prog_cfg p) (parity_cs_ctx_succ k (declared_global p) p) []
         (parity_cs_vars k (declared_global p) p)"
  shows "sound_table p (analyse_parity_call_string_result k p) parity_classify_check"
proof (rule sound_table_of_activation
    [where R = "call_context_rel_of_fun (\<lambda>u c t. cs_context k u c t)" and rc = "[]",
     OF _ _ _ parity_classify_check_proved parity_classify_check_refuted], goal_cases)
  case (1 u)
  show ?case
    by (rule equalityD1
          [OF analyse_parity_call_string_ltr_collect_eq_Union [where ctx_fun = "cs_context k"]])
next
  case (2 u ctx)
  show ?case
    using analyse_parity_call_string_sound_of_cover [OF cov, where s = "\<lambda>u c t. t"]
    unfolding analyse_parity_call_string_result_def
      analyse_parity_call_string_gamma_reader_eq_lookup .
next
  case 3
  show ?case
    using analyse_parity_call_string_vars_finite [OF cov(1)]
    by (simp add: finite_analysis_result_def analyse_parity_call_string_result_def
        routed_dg_pipeline.result_def routed_dg_pipeline.sol_vars_def)
qed

lemma congruence_cs_table:
  assumes cov: "congruence_cs_terminates k (declared_global p) p"
      "ctx_vars_cover (prog_cfg p) (congruence_cs_ctx_succ k (declared_global p) p) []
         (congruence_cs_vars k (declared_global p) p)"
  shows "sound_table p (analyse_congruence_call_string_result k p) congruence_classify_check"
proof (rule sound_table_of_activation
    [where R = "call_context_rel_of_fun (\<lambda>u c t. cs_context k u c t)" and rc = "[]",
     OF _ _ _ congruence_classify_check_proved congruence_classify_check_refuted],
    goal_cases)
  case (1 u)
  show ?case
    by (rule equalityD1
          [OF analyse_congruence_call_string_ltr_collect_eq_Union
              [where ctx_fun = "cs_context k"]])
next
  case (2 u ctx)
  show ?case
    using analyse_congruence_call_string_sound_of_cover [OF cov, where s = "\<lambda>u c t. t"]
    unfolding analyse_congruence_call_string_result_def
      analyse_congruence_call_string_gamma_reader_eq_lookup .
next
  case 3
  show ?case
    using analyse_congruence_call_string_vars_finite [OF cov(1)]
    by (simp add: finite_analysis_result_def analyse_congruence_call_string_result_def
        routed_dg_pipeline.result_def routed_dg_pipeline.sol_vars_def)
qed

lemma interval_cs_table:
  assumes cov: "interval_cs_terminates k (declared_global p) p"
      "ctx_vars_cover (prog_cfg p) (interval_cs_ctx_succ k (declared_global p) p) []
         (interval_cs_vars k (declared_global p) p)"
  shows "sound_table p (analyse_interval_call_string_result k p) interval_classify_check"
proof (rule sound_table_of_activation
    [where R = "call_context_rel_of_fun (\<lambda>u c t. cs_context k u c t)" and rc = "[]",
     OF _ _ _ interval_classify_check_proved interval_classify_check_refuted], goal_cases)
  case (1 u)
  show ?case
    by (rule equalityD1
          [OF analyse_interval_call_string_ltr_collect_eq_Union
              [where ctx_fun = "cs_context k"]])
next
  case (2 u ctx)
  show ?case
    using analyse_interval_call_string_sound_of_cover [OF cov, where s = "\<lambda>u c t. t"]
    unfolding analyse_interval_call_string_result_def
      analyse_interval_call_string_result_for_def
      analyse_interval_call_string_gamma_reader_eq_lookup .
next
  case 3
  show ?case
    using analyse_interval_call_string_vars_finite [OF cov(1)]
    by (simp add: finite_analysis_result_def analyse_interval_call_string_result_def
        analyse_interval_call_string_result_for_def
        routed_dg_pipeline.result_def routed_dg_pipeline.sol_vars_def)
qed

lemma int_cs_table:
  assumes cov: "int_cs_terminates k (declared_global p) p"
      "ctx_vars_cover (prog_cfg p) (int_cs_ctx_succ k (declared_global p) p) []
         (int_cs_vars k (declared_global p) p)"
  shows "sound_table p (analyse_int_call_string_result_warrow k p) int_classify_check"
proof (rule sound_table_of_activation
    [where R = "call_context_rel_of_fun (\<lambda>u c t. cs_context k u c t)" and rc = "[]",
     OF _ _ _ int_classify_check_proved int_classify_check_refuted], goal_cases)
  case (1 u)
  show ?case
    by (rule equalityD1
          [OF analyse_int_call_string_ltr_collect_eq_Union_warrow
              [where ctx_fun = "cs_context k"]])
next
  case (2 u ctx)
  show ?case
    using analyse_int_call_string_sound_of_cover_warrow [OF cov, where s = "\<lambda>u c t. t"]
    unfolding analyse_int_call_string_result_warrow_def
      analyse_int_call_string_result_for_warrow_def
      analyse_int_call_string_gamma_reader_eq_lookup_warrow .
next
  case 3
  show ?case
    using analyse_int_call_string_vars_finite_warrow [OF cov(1)]
    by (simp add: finite_analysis_result_def analyse_int_call_string_result_warrow_def
        analyse_int_call_string_result_for_warrow_def
        routed_dg_pipeline.result_def routed_dg_pipeline.sol_vars_def)
qed

end

