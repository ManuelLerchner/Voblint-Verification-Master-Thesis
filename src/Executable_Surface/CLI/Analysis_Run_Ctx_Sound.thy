theory Analysis_Run_Ctx_Sound
  imports Analysis_Run_Sound
begin

section \<open>The contextual configurations' tables\<close>

text \<open>
  A context-sensitive table has one entry per point and context. Each registration
  publishes its soundness in activation form: the activation buckets exhaust a
  point --- outright for a call string, which is a function of the call site and
  the caller's context, and for entry state from the totality of its context
  relation --- and each bucket is bounded by the entry filed under its context.
  \<open>sound_table_of_activation\<close> turns that into a \<open>sound_table\<close>, so each
  configuration below names its registration's three published facts and the
  soundness of the check consumer, and nothing else. Every registration takes the
  activation list and the global update rule as parameters, so one table per
  context policy covers every activation and every rule.
\<close>

subsection \<open>Entry state\<close>

lemma mcp_es_rule_table:
  assumes wf: "wf_program_compile_input p"
    and cov: "mcp_es_rule.terminates as r (declared_global p) p"
  shows "sound_table p (mcp_es_rule.result as r (declared_global p) p)
           (mcp_classify (activation as)) (mcp_gamma_v (activation as))"
proof (rule sound_table_of_activation
    [where R = "mcp_es_rule.admitted_contexts as r (declared_global p) p"
       and rc = mcp_root_ctx,
     OF _ _ _ mcp_classify_proved mcp_classify_refuted], goal_cases)
  case (1 u)
  show ?case
    by (simp add: mcp_es_rule.entry_state_ltr_collect_eq_Union_of_terminates [OF wf cov])
next
  case (2 u ctx)
  show ?case
    using mcp_es_rule.entry_state_activation_collect_sound_of_terminates [OF wf cov]
    unfolding mcp_es_rule.gamma_reader_eq_lookup .
next
  case 3
  show ?case
    using mcp_es_rule.vars_finite_of_terminates [OF cov]
    by (simp add: finite_analysis_result_def routed_dg_pipeline.result_def
        routed_dg_pipeline.sol_vars_def)
qed

subsection \<open>Call string\<close>

lemma mcp_cs_rule_table:
  assumes wf: "wf_program_compile_input p"
    and cov: "mcp_cs_rule.terminates as k r (declared_global p) p"
  shows "sound_table p (mcp_cs_rule.result as k r (declared_global p) p)
           (mcp_classify (activation as)) (mcp_gamma_v (activation as))"
proof (rule sound_table_of_activation
    [where R = "call_context_rel_of_fun (\<lambda>u ctx t. cs_context k u ctx t)" and rc = "[]",
     OF _ _ _ mcp_classify_proved mcp_classify_refuted], goal_cases)
  case (1 u)
  show ?case
    by (rule equalityD1
          [OF mcp_cs_rule.fun_route_ltr_collect_eq_Union [where ctx_fun = "cs_context k"]])
next
  case (2 u ctx)
  show ?case
    using mcp_cs_rule.fun_route_activation_collect_sound_of_terminates
            [OF cs_route_context_agree wf cov]
    unfolding mcp_cs_rule.gamma_reader_eq_lookup by simp
next
  case 3
  show ?case
    using mcp_cs_rule.vars_finite_of_terminates [OF cov]
    by (simp add: finite_analysis_result_def routed_dg_pipeline.result_def
        routed_dg_pipeline.sol_vars_def)
qed

end
