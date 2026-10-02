theory Parity_Classify
  imports
    Parity_Exec
begin

section \<open>Parity instance of the generic check-discharge interface\<close>

text \<open>
  The check classifier is derived from Parity's bundle, exactly as in
  \<open>Voblint_Analysis_Sign.Sign_Classify\<close>: the Boolean recursion over \<^typ>\<open>exp\<close>,
  the three-way classification, and the node-indexed bridge to
  \<^const>\<open>checks_proven\<close> come from the comparison queries
  \<^const>\<open>parity_less\<close>/\<^const>\<open>parity_eq\<close> and the evaluator, through the
  \<open>parity_tf\<close> interpretation in \<^theory>\<open>Voblint_Analysis_Parity.Parity_Transfer\<close>.
  Their facts stay under \<open>parity_tf.check.\<close>.
\<close>

end
