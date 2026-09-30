theory Sign_Exec
  imports
    "Voblint_Exec.Exec_St_Restriction_Refinement"
    "Voblint_Nonrelational.Nonrelational_Ops"
    Sign_Transfer
begin

section \<open>Sign per-domain seam: executable transfer mirror and commutation\<close>

text \<open>The state a run starts in: a declared global holds \<open>SZero\<close>, a local \<open>STop\<close>.\<close>

abbreviation cinit_sign_st :: "sign default_st" where
  "cinit_sign_st \<equiv> initial_default_st STop SZero"

subsection \<open>Classifier-parametric executable transfer\<close>

text \<open>
  The executable mirror of \<open>sign_tf_abs\<close>/\<open>enter_sign_for\<close>, parametric in the
  classifier.

  \<open>sign_ops\<close>, Sign's primitive bundle, is defined beside the abstract transfer in
  \<^theory>\<open>Voblint_Analysis_Sign.Sign_Transfer\<close>, so both layers read one value.
  The two constants below are the generic constructions of
  \<^theory>\<open>Voblint_Nonrelational.Nonrelational_Ops\<close> instantiated at it, not independent
  definitions; Interval, Parity, Congruence and each of the Int product's three
  refinement modes instantiate the same two at their own bundles. The guard
  transfer needs no third: \<^const>\<open>generic_tf_st_for\<close> derives its filter from
  the bundle's evaluator and refinement operations.
\<close>

definition sign_enter_st_for ::
  "(vname => bool) => call_info =>
   sign default_st => sign default_st" where
  "sign_enter_st_for = generic_enter_st_for sign_ops"

lemma sign_enter_st_for_eq [simp]:
  "sign_enter_st_for \<G> ci s =
    bind_formals_resolved_q \<G> (ci_formals ci)
      (map (\<lambda>e. aval_sign e
        (default_st_to_fun \<G> s)) (ci_args ci))
      (enter_frame_D_resolved_q STop s)"
  by (simp add: sign_enter_st_for_def generic_enter_st_for_def top_sign_def)

definition sign_tf_st_for ::
  "(vname => bool) => edge_action =>
   sign default_st => sign default_st" where
  "sign_tf_st_for = generic_tf_st_for sign_ops"

lemmas sign_tf_st_for_simps [simp] =
  generic_tf_st_for.simps [of sign_ops, folded sign_tf_st_for_def]

subsection \<open>Classifier-parametric commutation\<close>

text \<open>The classifier-parametric commutation of the executable and abstract sign
  transfer: the registered D/G pipeline for a program with a real declared global
  needs the executable transfer to commute with the abstract transfer at an
  arbitrary classifier \<open>\<G>\<close>.

  Nothing here is Sign's to discharge: the guard filter is derived from the
  bundle, so \<open>sign_tf.tf_st_for_commute\<close> settles every action, the guard
  included, on a live state.\<close>

theorem sign_tf_st_for_commute:
  assumes live: "live_default_st \<G> s"
  shows
    "default_st_to_fun \<G> (sign_tf_st_for \<G> a s) =
     sign_tf_abs a (default_st_to_fun \<G> s)"
  unfolding sign_tf_st_for_def
  by (rule sign_tf.tf_st_for_commute[OF live])

lemma enter_frame_sign_st_for_commute:
  "default_st_to_fun \<G> (enter_frame_D_resolved_q STop s) =
   enter_frame_sign_for \<G> (default_st_to_fun \<G> s)"
  by (simp add: sign_tf.op_defs)

lemma sign_enter_st_for_commute:
  "default_st_to_fun \<G> (sign_enter_st_for \<G> ci s) =
   enter_sign_ci_for \<G> ci (default_st_to_fun \<G> s)"
  by (simp add: sign_tf.op_defs enter_binding_def enter_frame_def
                enter_frame_sign_st_for_commute)

end
