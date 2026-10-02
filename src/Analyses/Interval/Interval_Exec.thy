theory Interval_Exec
  imports
    Interval_Domain
begin

section \<open>Interval on the executable carrier\<close>

text \<open>
  The executable step and procedure entry are \<^theory>\<open>Voblint_Nonrelational.Nonrelational_Ops\<close>'s
  generic constructions at the bundle, \<open>generic_tf_st_for ivl_ops\<close> and
  \<open>generic_enter_st_for ivl_ops\<close>, and their agreement with the abstract transfer is
  \<open>ivl_tf.tf_st_for_commute\<close> and \<open>ivl_tf.enter_st_for_commute\<close>: nothing about them
  is the domain's to state.
\<close>

text \<open>The state a run starts in: a declared global holds \<open>[0,0]\<close>, a local is unbounded.\<close>

abbreviation cinit_ivl_st :: "ivl default_st" where
  "cinit_ivl_st \<equiv> initial_default_st (Ivl MinInf PlusInf) (Ivl (Fin 0) (Fin 0))"

end
