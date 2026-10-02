theory Congruence_Classify
  imports
    Congruence_Exec
begin

section \<open>Deciding a check from a map of residue classes\<close>

text \<open>
  The check classifier is derived from Congruence's bundle: the Boolean recursion
  over \<^typ>\<open>exp\<close> (\<open>Not\<close>, \<open>And\<close>, \<open>Or\<close>), the three-way classification, and the
  node-indexed bridge to \<^const>\<open>checks_proven\<close> come from the comparison tables
  \<^const>\<open>congruence_lt\<close>/\<^const>\<open>congruence_eqb\<close> and the evaluator, through the
  \<open>congruence_tf\<close> interpretation in
  \<^theory>\<open>Voblint_Analysis_Congruence.Congruence_Transfer\<close>. Their facts stay under
  \<open>congruence_tf.check.\<close>; \<open>Congruence_Regression\<close> exercises them.
\<close>

end
