theory Parity_Exec
  imports
    "Voblint_Exec.Default_St_Reachability"
    "Voblint_Exec.Default_St_Restriction_Refinement"
    "Voblint_Nonrelational.Nonrelational_Ops"
    Parity_Transfer
begin

section \<open>Parity on the executable carrier\<close>

text \<open>
  The executable step and procedure entry are \<^theory>\<open>Voblint_Nonrelational.Nonrelational_Ops\<close>'s
  generic constructions at the bundle, \<open>generic_tf_st_for parity_ops\<close> and
  \<open>generic_enter_st_for parity_ops\<close>, and their agreement with the abstract transfer is
  \<open>parity_tf.tf_st_for_commute\<close> and \<open>parity_tf.enter_st_for_commute\<close>: nothing about them
  is the domain's to state.
\<close>

text \<open>The state a run starts in: a declared global holds \<open>PEven\<close>, a local \<open>PTop\<close>.\<close>

abbreviation cinit_parity_st :: "parity default_st" where
  "cinit_parity_st \<equiv> initial_default_st PTop PEven"

end
