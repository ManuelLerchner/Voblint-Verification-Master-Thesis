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

text \<open>
  The entry-state solve's activation seed (\<open>Lifted cinit_ivl_st\<close>, in the
  entry-state equation system) is canonical: neither default (\<open>top\<close> for locals,
  the singleton \<open>{0}\<close> for globals) is witness-bottom, and \<open>cinit_ivl_st\<close> carries
  no explicit override, so \<^const>\<open>default_st_is_bot_for\<close> is false at every
  declared-globals list. This is the base case the entry-state equation system's
  RHS closure induction needs.
\<close>

lemma cinit_ivl_st_not_bot_for:
  assumes globals: "\<And>x. \<G> x = (x \<in> set gl)"
  shows "\<not> default_st_is_bot_for gl cinit_ivl_st"
proof -
  have "\<not> is_empty_state (readback \<G> cinit_ivl_st)"
    unfolding is_empty_state_def by (auto simp: is_bottom_ivl_def split: if_splits)
  then show ?thesis
    by (simp add: default_st_is_bot_for_iff[OF globals])
qed

end
