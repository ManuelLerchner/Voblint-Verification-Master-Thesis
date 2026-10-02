theory Sign_Exec
  imports
    Sign_Transfer
begin

section \<open>Sign on the executable carrier\<close>

text \<open>
  The executable step and procedure entry are \<^theory>\<open>Voblint_Nonrelational.Nonrelational_Ops\<close>'s
  generic constructions at the bundle, \<open>generic_tf_st_for sign_ops\<close> and
  \<open>generic_enter_st_for sign_ops\<close>, and their agreement with the abstract transfer is
  \<open>sign_tf.tf_st_for_commute\<close> and \<open>sign_tf.enter_st_for_commute\<close>: nothing about them
  is the domain's to state.
\<close>

text \<open>The state a run starts in: a declared global holds \<open>SZero\<close>, a local \<open>STop\<close>.\<close>

abbreviation cinit_sign_st :: "sign default_st" where
  "cinit_sign_st \<equiv> initial_default_st STop SZero"

end
