theory Sign_Classify
  imports
    Sign_Exec
begin

section \<open>Sign instance of the generic check-discharge interface\<close>

text \<open>
  The check classifier is derived from Sign's bundle: the Boolean recursion over
  \<^typ>\<open>exp\<close> (\<open>Not\<close>, \<open>And\<close>, \<open>Or\<close>), the three-way classification, and the
  node-indexed bridge to \<^const>\<open>checks_proven\<close> come from the bundle's queries
  \<^const>\<open>sign_less\<close>/\<^const>\<open>sign_eq\<close> and evaluator, through the
  \<open>sign_tf\<close> interpretation in \<^theory>\<open>Voblint_Analysis_Sign.Sign_Transfer\<close>.
  Their facts stay under \<open>sign_tf.check.\<close>; \<open>classify_check\<close>'s two soundness
  directions are \<open>sign_tf.check.classify_check_proved\<close> and
  \<open>sign_tf.check.classify_check_refuted\<close>.
  \<open>Sign_Regression\<close> in the Sign examples exercises them.
\<close>

end
