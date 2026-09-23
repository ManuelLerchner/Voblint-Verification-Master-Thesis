theory Sign_Exec
  imports
    "Voblint_Exec.Exec_St_Restriction_Refinement"
    "Voblint_Nonrelational.Numeric_Ops"
    Sign_Transfer
begin

section \<open>Sign per-domain seam: executable transfer mirror and commutation\<close>

instance sign :: bounded_warrowing ..

text \<open>The state a run starts in: a declared global holds \<open>SZero\<close>, a local \<open>STop\<close>.\<close>

abbreviation cinit_sign_st :: "sign resolved_st_q" where
  "cinit_sign_st \<equiv> initial_resolved_st_q STop SZero"

subsection \<open>Classifier-parametric executable transfer\<close>

text \<open>
  The executable mirror of \<open>sign_tf_abs\<close>/\<open>enter_sign_for\<close>, parametric in the
  classifier.

  \<open>sign_ops\<close>, Sign's primitive bundle, is defined beside the abstract transfer in
  \<^theory>\<open>Voblint_Analysis_Sign.Sign_Transfer\<close>, so both layers read one value.
  The two constants below are the generic constructions of
  \<^theory>\<open>Voblint_Nonrelational.Numeric_Ops\<close> instantiated at it, not independent
  definitions; Interval, Parity, Congruence and each of the Int product's three
  refinement modes instantiate the same two at their own bundles. The guard
  transfer needs no third: \<^const>\<open>generic_tf_st_for\<close> reads \<open>n_bfilter\<close> off the
  bundle directly, so naming that projection separately would only rename
  \<^const>\<open>branch_sign_st\<close>.
\<close>

definition sign_enter_st_for ::
  "(vname => bool) => call_info =>
   sign resolved_st_q => sign resolved_st_q" where
  "sign_enter_st_for = generic_enter_st_for sign_ops"

lemma sign_enter_st_for_eq [simp]:
  "sign_enter_st_for \<G> ci s =
    bind_formals_resolved_q \<G> (ci_formals ci)
      (map (\<lambda>e. aval_sign e
        (fun_of_resolved_st_q_for \<G> s)) (ci_args ci))
      (enter_frame_D_resolved_q STop s)"
  by (simp add: sign_enter_st_for_def generic_enter_st_for_def)

definition sign_tf_st_for ::
  "(vname => bool) => edge_action =>
   sign resolved_st_q => sign resolved_st_q" where
  "sign_tf_st_for = generic_tf_st_for sign_ops"

lemmas sign_tf_st_for_simps [simp] =
  generic_tf_st_for.simps [of sign_ops, folded sign_tf_st_for_def]

subsection \<open>Classifier-parametric commutation\<close>

text \<open>The classifier-parametric commutation of the executable and abstract sign
  transfer: the registered D/G pipeline for a program with a real declared global
  needs the executable transfer to commute with the abstract transfer at an
  arbitrary classifier \<open>\<G>\<close>.

  Only the guard is Sign's to discharge. Every other action is settled once for
  any bundle by \<open>sign_tf.tf_st_for_commute\<close>, so what remains is
  \<open>sign_backward_domain\<close>'s own filter commutation, which holds on a live state.\<close>

theorem sign_tf_st_for_commute:
  assumes live: "live_resolved_st_q \<G> s"
  shows
    "fun_of_resolved_st_q_for \<G> (sign_tf_st_for \<G> a s) =
     sign_tf_abs a (fun_of_resolved_st_q_for \<G> s)"
  unfolding sign_tf_st_for_def
  by (rule sign_tf.tf_st_for_commute)
     (simp add: sign_backward_domain.branch_st_commute[OF live])

lemma enter_frame_sign_st_for_commute:
  "fun_of_resolved_st_q_for \<G> (enter_frame_D_resolved_q STop s) =
   enter_frame_sign_for \<G> (fun_of_resolved_st_q_for \<G> s)"
  by (simp add: sign_tf.op_defs)

lemma sign_enter_st_for_commute:
  "fun_of_resolved_st_q_for \<G> (sign_enter_st_for \<G> ci s) =
   enter_sign_ci_for \<G> ci (fun_of_resolved_st_q_for \<G> s)"
  by (simp add: sign_tf.op_defs enter_binding_def enter_frame_def
                enter_frame_sign_st_for_commute)

end

