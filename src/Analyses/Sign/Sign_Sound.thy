theory Sign_Sound
  imports
    "Voblint_Exec.DG_Local_State_Exec_Refinement"
    Sign_Transfer
    Sign_Exec
begin

section \<open>What the initial abstract state describes\<close>

text \<open>
  Sign's specification and its soundness are not restated here:
  \<open>sign_tf.spec_exec\<close> is sound against \<open>\<lambda>d g. \<lbrakk>\<rho>\<^bsub>\<G>\<^esub> d\<rbrakk>\<close> by
  \<open>sign_tf.sound_exec\<close> and \<open>sign_tf.entry_cover_exec\<close>, which every non-relational
  bundle gets from \<^locale>\<open>sound_nonrelational_ops\<close>.
\<close>

text \<open>
  The initial-state contract, owned here rather than reproved at each assembly
  instance: every concrete store a run may start in is described by
  \<^const>\<open>cinit_sign_st\<close>. It holds because a declared global starts at zero, which
  \<^const>\<open>SZero\<close> describes exactly, and a local starts unconstrained, which
  \<^const>\<open>STop\<close> describes trivially --- so it is a fact about Sign's initial state
  and its concretization, and about nothing else.
\<close>

lemma sign_cinit_gamma:
  "cinit_stores \<G> \<subseteq> default_st_gamma \<G> cinit_sign_st"
  by (auto simp: cinit_stores_def gamma_state_def default_st_gamma_initial)

end
