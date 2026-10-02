theory Int_Classify
  imports Int_Exec
begin

section \<open>Int instance of the generic check-discharge interface\<close>

text \<open>
  The check classifier is derived from Int's bundle: the Boolean recursion over
  \<^typ>\<open>exp\<close>, the three-way classification, and the node-indexed bridge to
  \<^const>\<open>checks_proven\<close> come from the comparison queries
  \<^const>\<open>int_less\<close>/\<^const>\<open>int_eq\<close> and the mode's evaluator, through the
  \<open>int_tf\<close> interpretation in \<^theory>\<open>Voblint_Analysis_Int.Int_Transfer\<close>. Their
  soundness is \<open>int_tf.check.classify_check_proved\<close> and
  \<open>int_tf.check.classify_check_refuted\<close>.
\<close>

end
