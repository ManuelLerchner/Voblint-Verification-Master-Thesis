theory Analysis_Run_Ctx_Sound
  imports Analysis_Run_Sound
begin

section \<open>The contextual configurations' tables\<close>

text \<open>
  A context-sensitive table has one entry per point and context. Each domain
  publishes its soundness in activation form: the activation buckets exhaust a
  point --- outright for a call string, which is a function of the call site and
  the caller's context, and for entry state from the totality of its context
  relation --- and each bucket is bounded by the entry filed under its context.
  \<open>sound_table_of_activation\<close> turns that into a \<open>sound_table\<close>, so each
  configuration below names its registration's three published facts and its domain's
  classifier soundness, and nothing else. Every registration takes the global update
  rule as a parameter, so one table per domain and context policy covers all rules.
\<close>

subsection \<open>Entry state\<close>

lemma sign_es_rule_table:
  assumes wf: "wf_program_compile_input p"
    and cov: "sign_es_rule.terminates r (declared_global p) p"
  shows "sound_table p (sign_es_rule.result r (declared_global p) p) sign_classify_check"
proof (rule sound_table_of_activation
    [where R = "sign_es_rule.admitted_contexts r (declared_global p) p" and rc = "[]",
     OF _ _ _ sign_classify_check_proved sign_classify_check_refuted], goal_cases)
  case (1 u)
  show ?case
    by (simp add: sign_es_rule.entry_state_ltr_collect_eq_Union_of_terminates [OF wf cov])
next
  case (2 u ctx)
  show ?case
    using sign_es_rule.entry_state_activation_collect_sound_of_terminates [OF wf cov]
    unfolding sign_es_rule.gamma_reader_eq_lookup .
next
  case 3
  show ?case
    using sign_es_rule.vars_finite_of_terminates [OF cov]
    by (simp add: finite_analysis_result_def sign_es_rule.result_def
        sign_es_rule.sol_vars_def)
qed

lemma interval_es_rule_table:
  assumes wf: "wf_program_compile_input p"
    and cov: "interval_es_rule.terminates r (declared_global p) p"
  shows "sound_table p (interval_es_rule.result r (declared_global p) p)
           interval_classify_check"
proof (rule sound_table_of_activation
    [where R = "interval_es_rule.admitted_contexts r (declared_global p) p" and rc = "[]",
     OF _ _ _ interval_classify_check_proved interval_classify_check_refuted], goal_cases)
  case (1 u)
  show ?case
    by (simp add: interval_es_rule.entry_state_ltr_collect_eq_Union_of_terminates [OF wf cov])
next
  case (2 u ctx)
  show ?case
    using interval_es_rule.entry_state_activation_collect_sound_of_terminates [OF wf cov]
    unfolding interval_es_rule.gamma_reader_eq_lookup .
next
  case 3
  show ?case
    using interval_es_rule.vars_finite_of_terminates [OF cov]
    by (simp add: finite_analysis_result_def interval_es_rule.result_def
        interval_es_rule.sol_vars_def)
qed

lemma int_es_rule_table:
  assumes wf: "wf_program_compile_input p"
    and cov: "int_es_rule.terminates r (declared_global p) p"
  shows "sound_table p (int_es_rule.result r (declared_global p) p) int_classify_check"
proof (rule sound_table_of_activation
    [where R = "int_es_rule.admitted_contexts r (declared_global p) p" and rc = "[]",
     OF _ _ _ int_classify_check_proved int_classify_check_refuted], goal_cases)
  case (1 u)
  show ?case
    by (simp add: int_es_rule.entry_state_ltr_collect_eq_Union_of_terminates [OF wf cov])
next
  case (2 u ctx)
  show ?case
    using int_es_rule.entry_state_activation_collect_sound_of_terminates [OF wf cov]
    unfolding int_es_rule.gamma_reader_eq_lookup .
next
  case 3
  show ?case
    using int_es_rule.vars_finite_of_terminates [OF cov]
    by (simp add: finite_analysis_result_def int_es_rule.result_def
        int_es_rule.sol_vars_def)
qed

lemma parity_es_rule_table:
  assumes wf: "wf_program_compile_input p"
    and cov: "parity_es_rule.terminates r (declared_global p) p"
  shows "sound_table p (parity_es_rule.result r (declared_global p) p) parity_classify_check"
proof (rule sound_table_of_activation
    [where R = "parity_es_rule.admitted_contexts r (declared_global p) p" and rc = "[]",
     OF _ _ _ parity_classify_check_proved parity_classify_check_refuted], goal_cases)
  case (1 u)
  show ?case
    by (simp add: parity_es_rule.entry_state_ltr_collect_eq_Union_of_terminates [OF wf cov])
next
  case (2 u ctx)
  show ?case
    using parity_es_rule.entry_state_activation_collect_sound_of_terminates [OF wf cov]
    unfolding parity_es_rule.gamma_reader_eq_lookup .
next
  case 3
  show ?case
    using parity_es_rule.vars_finite_of_terminates [OF cov]
    by (simp add: finite_analysis_result_def parity_es_rule.result_def
        parity_es_rule.sol_vars_def)
qed

lemma congruence_es_rule_table:
  assumes wf: "wf_program_compile_input p"
    and cov: "congruence_es_rule.terminates r (declared_global p) p"
  shows "sound_table p (congruence_es_rule.result r (declared_global p) p)
           congruence_classify_check"
proof (rule sound_table_of_activation
    [where R = "congruence_es_rule.admitted_contexts r (declared_global p) p" and rc = "[]",
     OF _ _ _ congruence_classify_check_proved congruence_classify_check_refuted],
    goal_cases)
  case (1 u)
  show ?case
    by (simp add: congruence_es_rule.entry_state_ltr_collect_eq_Union_of_terminates [OF wf cov])
next
  case (2 u ctx)
  show ?case
    using congruence_es_rule.entry_state_activation_collect_sound_of_terminates [OF wf cov]
    unfolding congruence_es_rule.gamma_reader_eq_lookup .
next
  case 3
  show ?case
    using congruence_es_rule.vars_finite_of_terminates [OF cov]
    by (simp add: finite_analysis_result_def congruence_es_rule.result_def
        congruence_es_rule.sol_vars_def)
qed

subsection \<open>Call string\<close>

lemma sign_cs_rule_table:
  assumes wf: "wf_program_compile_input p"
    and cov: "sign_cs_rule.terminates k r (declared_global p) p"
  shows "sound_table p (sign_cs_rule.result k r (declared_global p) p) sign_classify_check"
proof (rule sound_table_of_activation
    [where R = "call_context_rel_of_fun (\<lambda>u c t. cs_context k u c t)" and rc = "[]",
     OF _ _ _ sign_classify_check_proved sign_classify_check_refuted], goal_cases)
  case (1 u)
  show ?case
    by (rule equalityD1
          [OF sign_cs_rule.fun_route_ltr_collect_eq_Union [where ctx_fun = "cs_context k"]])
next
  case (2 u ctx)
  show ?case
    using sign_cs_rule.fun_route_activation_collect_sound_of_terminates
            [OF cs_route_context_agree wf cov]
    unfolding sign_cs_rule.gamma_reader_eq_lookup by simp
next
  case 3
  show ?case
    using sign_cs_rule.vars_finite_of_terminates [OF cov]
    by (simp add: finite_analysis_result_def routed_dg_pipeline.result_def
        routed_dg_pipeline.sol_vars_def)
qed

lemma interval_cs_rule_table:
  assumes wf: "wf_program_compile_input p"
    and cov: "interval_cs_rule.terminates k r (declared_global p) p"
  shows "sound_table p (interval_cs_rule.result k r (declared_global p) p) interval_classify_check"
proof (rule sound_table_of_activation
    [where R = "call_context_rel_of_fun (\<lambda>u c t. cs_context k u c t)" and rc = "[]",
     OF _ _ _ interval_classify_check_proved interval_classify_check_refuted], goal_cases)
  case (1 u)
  show ?case
    by (rule equalityD1
          [OF interval_cs_rule.fun_route_ltr_collect_eq_Union [where ctx_fun = "cs_context k"]])
next
  case (2 u ctx)
  show ?case
    using interval_cs_rule.fun_route_activation_collect_sound_of_terminates
            [OF cs_route_context_agree wf cov]
    unfolding interval_cs_rule.gamma_reader_eq_lookup by simp
next
  case 3
  show ?case
    using interval_cs_rule.vars_finite_of_terminates [OF cov]
    by (simp add: finite_analysis_result_def routed_dg_pipeline.result_def
        routed_dg_pipeline.sol_vars_def)
qed

lemma int_cs_rule_table:
  assumes wf: "wf_program_compile_input p"
    and cov: "int_cs_rule.terminates k r (declared_global p) p"
  shows "sound_table p (int_cs_rule.result k r (declared_global p) p) int_classify_check"
proof (rule sound_table_of_activation
    [where R = "call_context_rel_of_fun (\<lambda>u c t. cs_context k u c t)" and rc = "[]",
     OF _ _ _ int_classify_check_proved int_classify_check_refuted], goal_cases)
  case (1 u)
  show ?case
    by (rule equalityD1
          [OF int_cs_rule.fun_route_ltr_collect_eq_Union [where ctx_fun = "cs_context k"]])
next
  case (2 u ctx)
  show ?case
    using int_cs_rule.fun_route_activation_collect_sound_of_terminates
            [OF cs_route_context_agree wf cov]
    unfolding int_cs_rule.gamma_reader_eq_lookup by simp
next
  case 3
  show ?case
    using int_cs_rule.vars_finite_of_terminates [OF cov]
    by (simp add: finite_analysis_result_def routed_dg_pipeline.result_def
        routed_dg_pipeline.sol_vars_def)
qed

lemma parity_cs_rule_table:
  assumes wf: "wf_program_compile_input p"
    and cov: "parity_cs_rule.terminates k r (declared_global p) p"
  shows "sound_table p (parity_cs_rule.result k r (declared_global p) p) parity_classify_check"
proof (rule sound_table_of_activation
    [where R = "call_context_rel_of_fun (\<lambda>u c t. cs_context k u c t)" and rc = "[]",
     OF _ _ _ parity_classify_check_proved parity_classify_check_refuted], goal_cases)
  case (1 u)
  show ?case
    by (rule equalityD1
          [OF parity_cs_rule.fun_route_ltr_collect_eq_Union [where ctx_fun = "cs_context k"]])
next
  case (2 u ctx)
  show ?case
    using parity_cs_rule.fun_route_activation_collect_sound_of_terminates
            [OF cs_route_context_agree wf cov]
    unfolding parity_cs_rule.gamma_reader_eq_lookup by simp
next
  case 3
  show ?case
    using parity_cs_rule.vars_finite_of_terminates [OF cov]
    by (simp add: finite_analysis_result_def routed_dg_pipeline.result_def
        routed_dg_pipeline.sol_vars_def)
qed

lemma congruence_cs_rule_table:
  assumes wf: "wf_program_compile_input p"
    and cov: "congruence_cs_rule.terminates k r (declared_global p) p"
  shows "sound_table p (congruence_cs_rule.result k r (declared_global p) p)
           congruence_classify_check"
proof (rule sound_table_of_activation
    [where R = "call_context_rel_of_fun (\<lambda>u c t. cs_context k u c t)" and rc = "[]",
     OF _ _ _ congruence_classify_check_proved congruence_classify_check_refuted], goal_cases)
  case (1 u)
  show ?case
    by (rule equalityD1
          [OF congruence_cs_rule.fun_route_ltr_collect_eq_Union [where ctx_fun = "cs_context k"]])
next
  case (2 u ctx)
  show ?case
    using congruence_cs_rule.fun_route_activation_collect_sound_of_terminates
            [OF cs_route_context_agree wf cov]
    unfolding congruence_cs_rule.gamma_reader_eq_lookup by simp
next
  case 3
  show ?case
    using congruence_cs_rule.vars_finite_of_terminates [OF cov]
    by (simp add: finite_analysis_result_def routed_dg_pipeline.result_def
        routed_dg_pipeline.sol_vars_def)
qed

end

