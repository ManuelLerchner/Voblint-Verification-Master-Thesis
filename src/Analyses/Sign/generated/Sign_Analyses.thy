theory Sign_Analyses
  imports
    Sign_Sound
    Sign_Classify
    Sign_Transfer
    Sign_Exec
    "Voblint_Nonrelational.Nonrel_Registration"
begin

section \<open>Registering Sign at every context and update rule\<close>

text \<open>
  GENERATED FILE. Source: \<^verbatim>\<open>manifests/analyses.yaml\<close>; generator:
  \<^verbatim>\<open>scripts/gen_analysis_assembly.py\<close>. Regenerate with the generator
  rather than hand-editing; a drift check compares regenerated output against
  this file.

  Sign runs through the shared D/G pipeline at the unit context. The CLI runs it as a
  field of the combined state of \<open>MCP_Analyses\<close>, whose component and
  soundness the unit registration supplies. Each registration leaves the rule that
  merges a value side-effected into a global as a parameter \<open>r\<close>. The
  equation system, the solve, the result table and every soundness endpoint come from
  the interpreted locale; this theory only names the domain's own implementation and
  facts.
\<close>

subsection \<open>At the unit context\<close>

global_interpretation sign_rule:
    nonrel_unit_rule sign_ops cinit_sign_st r
  for r
  by (intro nonrel_unit_ruleI nonrel_registrationI
      sign_tf.sound_nonrelational_ops_axioms sign_cinit_gamma)

end
