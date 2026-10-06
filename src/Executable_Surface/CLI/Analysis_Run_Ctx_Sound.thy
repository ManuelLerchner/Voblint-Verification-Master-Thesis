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
  \<open>covered_table_of_activation\<close> turns that into a \<open>covered_table\<close>, so each
  configuration below names its registration's three published facts and nothing
  else. Every registration takes the
  activation list and the global update rule as parameters, so one table per
  context policy covers every activation and every rule.
\<close>

subsection \<open>Entry state\<close>

lemma mcp_es_rule_table:
  assumes wf: "wf_program_compile_input p"
    and cov: "mcp_es_rule.terminates as r (declared_global p) p"
  shows "covered_table p (mcp_es_rule.result as r (declared_global p) p)
           (mcp_gamma_v (activation as))"
proof (rule covered_table_of_activation
    [where adm = "mcp_es_rule.admitted_contexts as r (declared_global p) p"
       and rc = mcp_root_ctx], goal_cases)
  case (1 u)
  show ?case
    by (simp add: mcp_es_rule.entry_state_node_collect_eq_Union_of_terminates [OF wf cov])
next
  case (2 u ctx)
  show ?case
    using mcp_es_rule.entry_state_activation_collect_sound_of_terminates [OF wf cov]
    unfolding mcp_es_rule.gamma_reader_eq_lookup .
next
  case 3
  show ?case
    using mcp_es_rule.vars_finite_of_terminates [OF cov]
    by (simp add: finite_solved_table_def dg_pipeline.result_def
        dg_pipeline.sol_vars_def)
qed

subsection \<open>Call string\<close>

text \<open>
  \<open>mcp_cs_rule_table\<close>: a terminating call-string run yields a
  \<open>covered_table\<close>, via the activation collecting soundness of \<open>mcp_cs_rule\<close>.
\<close>

lemma mcp_cs_rule_table:
  assumes wf: "wf_program_compile_input p"
    and cov: "mcp_cs_rule.terminates as k r (declared_global p) p"
  shows "covered_table p (mcp_cs_rule.result as k r (declared_global p) p)
           (mcp_gamma_v (activation as))"
proof (rule covered_table_of_activation
    [where adm = "context_policy_of_fun (\<lambda>u ctx t. cs_context k u ctx t)" and rc = "[]"],
    goal_cases)
  case (1 u)
  show ?case
    by (rule equalityD1
          [OF mcp_cs_rule.fun_route_node_collect_eq_Union [where ctx_fun = "cs_context k"]])
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
    by (simp add: finite_solved_table_def dg_pipeline.result_def
        dg_pipeline.sol_vars_def)
qed

subsection \<open>Program globals on the shared channel\<close>

text \<open>The two contextual tables again, at the shared-globals registrations.\<close>

lemma mcp_split_es_rule_table:
  assumes wf: "wf_program_compile_input p"
    and cov: "mcp_split_es_rule.terminates as r (declared_global p) p"
  shows "covered_table p (mcp_split_es_rule.result as r (declared_global p) p)
           (mcp_gamma_v (activation as))"
proof (rule covered_table_of_activation
    [where adm = "mcp_split_es_rule.admitted_contexts as r (declared_global p) p"
       and rc = mcp_root_ctx], goal_cases)
  case (1 u)
  show ?case
    by (simp add: mcp_split_es_rule.entry_state_node_collect_eq_Union_of_terminates [OF wf cov])
next
  case (2 u ctx)
  show ?case
    using mcp_split_es_rule.entry_state_activation_collect_sound_of_terminates [OF wf cov]
    unfolding mcp_split_es_rule.gamma_reader_eq_lookup .
next
  case 3
  show ?case
    using mcp_split_es_rule.vars_finite_of_terminates [OF cov]
    by (simp add: finite_solved_table_def dg_pipeline.result_def
        dg_pipeline.sol_vars_def)
qed

lemma mcp_split_cs_rule_table:
  assumes wf: "wf_program_compile_input p"
    and cov: "mcp_split_cs_rule.terminates as k r (declared_global p) p"
  shows "covered_table p (mcp_split_cs_rule.result as k r (declared_global p) p)
           (mcp_gamma_v (activation as))"
proof (rule covered_table_of_activation
    [where adm = "context_policy_of_fun (\<lambda>u ctx t. cs_context k u ctx t)" and rc = "[]"],
    goal_cases)
  case (1 u)
  show ?case
    by (rule equalityD1
          [OF mcp_split_cs_rule.fun_route_node_collect_eq_Union [where ctx_fun = "cs_context k"]])
next
  case (2 u ctx)
  show ?case
    using mcp_split_cs_rule.fun_route_activation_collect_sound_of_terminates
            [OF cs_route_context_agree wf cov]
    unfolding mcp_split_cs_rule.gamma_reader_eq_lookup by simp
next
  case 3
  show ?case
    using mcp_split_cs_rule.vars_finite_of_terminates [OF cov]
    by (simp add: finite_solved_table_def dg_pipeline.result_def
        dg_pipeline.sol_vars_def)
qed

end
