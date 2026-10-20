theory Int_Never_Analyses
  imports
    Int_Sound
    Int_Classify
    Int_Transfer
    Int_Exec
    "Voblint_Nonrelational.Nonrel_Registration"
begin

section \<open>Registering \<open>Int_Never\<close> at every context and update rule\<close>

text \<open>
  GENERATED FILE. Source: \<^verbatim>\<open>manifests/analyses.yaml\<close>; generator:
  \<^verbatim>\<open>scripts/gen_analysis_assembly.py\<close>. Regenerate with the generator
  rather than hand-editing; a drift check compares regenerated output against
  this file.

  \<open>Int_Never\<close> runs through the shared D/G pipeline at the unit context.
  The CLI runs it as a field of the combined state of \<open>MCP_Analyses\<close>,
  whose component and soundness the unit registration supplies. Each registration
  leaves the rule that merges a value side-effected into a global as a parameter
  \<open>r\<close>. The equation system, the solve, the result table and every
  soundness endpoint come from the interpreted locale; this theory only names the
  domain's own implementation and facts.
\<close>

subsection \<open>At the unit context\<close>

global_interpretation int_never_rule:
    nonrel_unit_rule "int_dom_ops Refine_Never" cinit_int_dom_st r
  for r
  by (intro nonrel_unit_ruleI nonrel_registrationI
      int_tf.sound_nonrelational_ops_axioms int_cinit_gamma)

end
