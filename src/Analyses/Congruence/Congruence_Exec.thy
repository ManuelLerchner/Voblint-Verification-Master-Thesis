theory Congruence_Exec
  imports "Voblint_Exec.Default_St_Restriction_Refinement" "Voblint_Nonrelational.Nonrelational_Ops"
    Congruence_Transfer Congruence_Warrowing
begin

section \<open>Congruence on the executable carrier\<close>

text \<open>
  The executable step and procedure entry are \<^theory>\<open>Voblint_Nonrelational.Nonrelational_Ops\<close>'s
  generic constructions at the bundle, \<open>generic_tf_st_for congruence_ops\<close> and
  \<open>generic_enter_st_for congruence_ops\<close>, and their agreement with the abstract transfer is
  \<open>congruence_tf.tf_st_for_commute\<close> and \<open>congruence_tf.enter_st_for_commute\<close>: nothing about them
  is the domain's to state.
\<close>

text \<open>
  The state a run starts in: a declared global holds the single integer \<open>0\<close>, every
  local is unconstrained.
\<close>

abbreviation cinit_congruence_st :: "congruence default_st" where
  "cinit_congruence_st \<equiv> initial_default_st top (congruence_of_int 0)"

end
