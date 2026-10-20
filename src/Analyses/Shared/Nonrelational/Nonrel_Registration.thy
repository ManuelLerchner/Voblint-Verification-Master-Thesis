theory Nonrel_Registration
  imports
    Nonrelational_Transfer
    "Voblint_Result.DG_Live_Unknowns"
    "Voblint_Framework.Call_String_Context"
    "Voblint_Solver.Globals_Rule"
begin

section \<open>Registering a non-relational bundle with the pipeline\<close>

text \<open>
  \<^theory_text>\<open>dg_analysis_execI\<close> leaves a non-relational domain four obligations: the
  context policy's route agreement and seed key, the solver, and the initial state.
  The first three belong to the context policy and the solver, not to the domain, so
  they are discharged here once per policy. A domain supplies its bundle and its
  initial state with the coverage lemma, and one interpretation of the locale for a
  policy registers it there for every update rule \<open>r\<close> (and, for call strings, every
  bound \<open>k\<close>).
\<close>

locale nonrel_registration = sound_nonrelational_ops ops
  for ops :: "'a::numeric_domain nonrelational_ops" +
  fixes init_st :: "'a default_st"
  assumes init_gamma: "\<And>\<G>. cinit_stores \<G> \<subseteq> default_st_gamma \<G> init_st"

subsection \<open>At the unit context\<close>

text \<open>
  One context per callee: every activation is keyed by \<open>()\<close>, so the route reads
  nothing of the entered state and agrees with its abstraction trivially.
\<close>

locale nonrel_unit_rule = nonrel_registration ops init_st for ops init_st +
  fixes r :: globals_rule
begin

sublocale dg_analysis_exec
    "generic_tf_st_for ops" "generic_enter_st_for ops" init_st
    "Analysis_Global ()" Analysis_Global Activation_Seed "\<lambda>_. route_unit" "()"
    "TD_side_rule_Interp_solve r"
    "TD_side_rule_Interp.solve_dom TYPE((unit, unit) global_unknown)
       TYPE(('a default_st lifted, 'a default_st lifted) dg_state) r"
    bot check.classify_check
    skip assign special_transfer backward.branch body ret
    enter_ci_for event "\<lambda>_. route_unit"
    "TD_side_rule_Interp_solve_c r"
  by (rule dg_analysis_execI) (simp_all add: td_certified_solver init_gamma)

end

subsection \<open>At the entry-state context\<close>

text \<open>
  An activation is keyed by the abstract values its formals hold on entry. The
  executable route reads them off the stored state, and
  \<open>exec_formals_route_commute\<close> says it agrees with the route on the abstraction.
\<close>

locale nonrel_es_rule = nonrel_registration ops init_st for ops init_st +
  fixes r :: globals_rule
begin

sublocale dg_analysis_exec
    "generic_tf_st_for ops" "generic_enter_st_for ops" init_st
    "Analysis_Global ()" Analysis_Global Activation_Seed exec_formals_route "[]"
    "TD_side_rule_Interp_solve r"
    "TD_side_rule_Interp.solve_dom TYPE((unit, 'a list) global_unknown)
       TYPE(('a default_st lifted, 'a default_st lifted) dg_state) r"
    bot check.classify_check
    skip assign special_transfer backward.branch body ret
    enter_ci_for event "\<lambda>_. formals_route_lifted_gen"
    "TD_side_rule_Interp_solve_c r"
  by (rule dg_analysis_execI)
     (simp_all add: exec_formals_route_commute[symmetric] td_certified_solver init_gamma)

end

subsection \<open>At the call-string context\<close>

text \<open>
  An activation is keyed by its last \<open>k\<close> call sites. The route reads only the call
  site, never the entered state, which is \<open>cs_route_indep_of_data\<close>.
\<close>

locale nonrel_cs_rule = nonrel_registration ops init_st for ops init_st +
  fixes k :: nat and r :: globals_rule
begin

sublocale dg_analysis_exec
    "generic_tf_st_for ops" "generic_enter_st_for ops" init_st
    Call_String_Context.Global "\<lambda>_. Call_String_Context.Global"
    Call_String_Context.Seed "\<lambda>_. cs_route k" "[]"
    "TD_side_rule_Interp_solve r"
    "TD_side_rule_Interp.solve_dom TYPE(call_string_gk)
       TYPE(('a default_st lifted, 'a default_st lifted) dg_state) r"
    bot check.classify_check
    skip assign special_transfer backward.branch body ret
    enter_ci_for event "\<lambda>_. cs_route k"
    "TD_side_rule_Interp_solve_c r"
  by (rule dg_analysis_execI)
     (simp_all add: cs_route_indep_of_data td_certified_solver init_gamma)

end

text \<open>A domain discharges each policy's locale from the same two facts.\<close>

lemma nonrel_registrationI:
  assumes "sound_nonrelational_ops ops"
    and "\<And>\<G>. cinit_stores \<G> \<subseteq> default_st_gamma \<G> init_st"
  shows "nonrel_registration ops init_st"
  using assms by (intro nonrel_registration.intro nonrel_registration_axioms.intro)

lemma nonrel_unit_ruleI:
  "nonrel_registration ops init_st \<Longrightarrow> nonrel_unit_rule ops init_st"
  by (rule nonrel_unit_rule.intro)

lemma nonrel_es_ruleI:
  "nonrel_registration ops init_st \<Longrightarrow> nonrel_es_rule ops init_st"
  by (rule nonrel_es_rule.intro)

lemma nonrel_cs_ruleI:
  "nonrel_registration ops init_st \<Longrightarrow> nonrel_cs_rule ops init_st"
  by (rule nonrel_cs_rule.intro)

end
