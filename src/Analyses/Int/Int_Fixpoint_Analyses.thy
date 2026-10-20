theory Int_Fixpoint_Analyses
  imports
    Int_Sound
    "Voblint_Nonrelational.Nonrel_Registration"
begin

section \<open>Registering Int under \<^const>\<open>Refine_Fixpoint\<close> at every context and update rule\<close>

text \<open>
  Int under \<^const>\<open>Refine_Fixpoint\<close> runs through the shared D/G pipeline at the unit
  context. The CLI runs it as a field of the combined state of
  \<open>MCP_Analyses\<close>, whose component and soundness the unit registration
  supplies. Each registration leaves the rule that merges a value side-effected into a
  global as a parameter \<open>r\<close>. The equation system, the solve, the result
  table and every soundness endpoint come from the interpreted locale; this theory
  only names the domain's own implementation and facts.
\<close>

subsection \<open>At the unit context\<close>

global_interpretation int_fixpoint_rule:
    nonrel_unit_rule "int_dom_ops Refine_Fixpoint" cinit_int_dom_st r
  for r
  by (intro nonrel_unit_ruleI nonrel_registrationI
      int_tf.sound_nonrelational_ops_axioms int_cinit_gamma)

end
