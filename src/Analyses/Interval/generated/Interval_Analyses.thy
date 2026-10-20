theory Interval_Analyses
  imports
    Interval_Sound
    Interval_Classify
    Interval_Transfer
    Interval_Exec
    "Voblint_Nonrelational.Nonrel_Registration"
begin

section \<open>Registering Interval at every context and update rule\<close>

text \<open>
  GENERATED FILE. Source: \<^verbatim>\<open>manifests/analyses.yaml\<close>; generator:
  \<^verbatim>\<open>scripts/gen_analysis_assembly.py\<close>. Regenerate with the generator
  rather than hand-editing; a drift check compares regenerated output against
  this file.

  Interval runs through the shared D/G pipeline at the unit context, keyed by the
  abstract values a callee's formals hold on entry, and keyed by a bounded call
  string. The CLI runs it as a field of the combined state of
  \<open>MCP_Analyses\<close>, whose component and soundness the unit registration
  supplies. Each registration leaves the rule that merges a value side-effected into a
  global as a parameter \<open>r\<close>, and the call-string one also its bound
  \<open>k\<close>. The equation system, the solve, the result table and every
  soundness endpoint come from the interpreted locale; this theory only names the
  domain's own implementation and facts.
\<close>

subsection \<open>At the unit context\<close>

global_interpretation interval_rule:
    nonrel_unit_rule ivl_ops cinit_ivl_st r
  for r
  by (intro nonrel_unit_ruleI nonrel_registrationI
      ivl_tf.sound_nonrelational_ops_axioms interval_cinit_gamma)

subsection \<open>At the entry-state context\<close>

global_interpretation interval_es_rule:
    nonrel_es_rule ivl_ops cinit_ivl_st r
  for r
  by (intro nonrel_es_ruleI nonrel_registrationI
      ivl_tf.sound_nonrelational_ops_axioms interval_cinit_gamma)

subsection \<open>At the call-string context\<close>

global_interpretation interval_cs_rule:
    nonrel_cs_rule ivl_ops cinit_ivl_st k r
  for k r
  by (intro nonrel_cs_ruleI nonrel_registrationI
      ivl_tf.sound_nonrelational_ops_axioms interval_cinit_gamma)

end
