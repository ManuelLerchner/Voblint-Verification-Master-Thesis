theory Parity_Analyses
  imports
    Parity_Sound
    Parity_Classify
    Parity_Transfer
    Parity_Exec
    "Voblint_Nonrelational.Nonrel_Registration"
begin

section \<open>Registering Parity at every context and update rule\<close>

text \<open>
  GENERATED FILE. Source: \<^verbatim>\<open>manifests/analyses.yaml\<close>; generator:
  \<^verbatim>\<open>scripts/gen_analysis_assembly.py\<close>. Regenerate with the generator
  rather than hand-editing; a drift check compares regenerated output against
  this file.

  Parity runs through the shared D/G pipeline at the unit context. The CLI runs it as
  a field of the combined state of \<open>MCP_Analyses\<close>, whose component and
  soundness the unit registration supplies. Each registration leaves the rule that
  merges a value side-effected into a global as a parameter \<open>r\<close>. The
  equation system, the solve, the result table and every soundness endpoint come from
  the interpreted locale; this theory only names the domain's own implementation and
  facts.
\<close>

subsection \<open>At the unit context\<close>

global_interpretation parity_rule:
    nonrel_unit_rule parity_ops cinit_parity_st r
  for r
  by (intro nonrel_unit_ruleI nonrel_registrationI
      parity_tf.sound_nonrelational_ops_axioms parity_cinit_gamma)

end
