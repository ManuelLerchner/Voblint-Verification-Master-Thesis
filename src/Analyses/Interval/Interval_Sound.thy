theory Interval_Sound
  imports
    Interval_Exec
begin

section \<open>What the initial abstract state describes\<close>

text \<open>
  Interval's specification and its soundness are not restated here:
  \<open>ivl_tf.spec_exec\<close> is sound against \<open>\<lambda>d g. \<lbrakk>\<rho>\<^bsub>\<G>\<^esub> d\<rbrakk>\<close> by
  \<open>ivl_tf.sound_exec\<close> and \<open>ivl_tf.entry_cover_exec\<close>, which every non-relational
  bundle gets from \<^locale>\<open>sound_nonrelational_ops\<close>.
\<close>

text \<open>
  The initial-state contract, owned here rather than reproved at each of the four
  assembly instances: every concrete store a run may start in is described by
  \<^const>\<open>cinit_ivl_st\<close>. A declared global starts at zero, which the singleton
  interval describes exactly; a local starts unconstrained, which the unbounded
  interval describes trivially. The solver discipline does not enter into it, which
  is why one lemma serves all four.
\<close>

lemma interval_cinit_gamma:
  "cinit_stores \<G> \<subseteq> default_st_gamma \<G> cinit_ivl_st"
  by (auto simp: cinit_stores_def gamma_state_def default_st_gamma_initial)

end
