theory Int_Exec
  imports
    Int_Transfer
begin

section \<open>The composite integer domain on the executable carrier\<close>

text \<open>
  The executable step and procedure entry are \<^theory>\<open>Voblint_Nonrelational.Nonrelational_Ops\<close>'s
  generic constructions at the bundle, \<open>generic_tf_st_for (int_dom_ops mode)\<close> and
  \<open>generic_enter_st_for (int_dom_ops mode)\<close>, and their agreement with the abstract transfer is
  \<open>int_tf.tf_st_for_commute\<close> and \<open>int_tf.enter_st_for_commute\<close>: nothing about them
  is the domain's to state. The mode is an argument like any other, chosen by public production reporting; it is orthogonal to equation generation and solver choice.
\<close>

text \<open>A declared global holds the abstraction of \<open>0\<close>, a local the whole-value element.\<close>

abbreviation cinit_int_dom_st :: "int_dom default_st" where
  "cinit_int_dom_st \<equiv> initial_default_st top (int_dom_of_int 0)"

end
