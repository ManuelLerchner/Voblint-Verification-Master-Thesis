theory Congruence_Exec
  imports "Voblint_Exec.Exec_St_Restriction_Refinement" "Voblint_Nonrelational.Numeric_Ops"
    Congruence_Transfer Congruence_Warrowing
begin

section \<open>Running the transfer functions on the state the solver actually stores\<close>

text \<open>
  The solver does not hold a function from variables to residue classes; it
  holds a \<^typ>\<open>congruence resolved_st_q\<close>, a compact record with one slot for
  locals, one for globals, and an override list. This theory gives Congruence's
  eight operations on that carrier and proves each agrees with the abstract
  operation once the carrier is read back through
  \<^const>\<open>fun_of_resolved_st_q_for\<close>. That agreement -- \<open>commutation\<close> -- is what
  every later soundness statement is transported along.

  \<open>cinit_congruence_st\<close> below is the state a run starts in: a declared global
  holds the single integer \<open>0\<close>, every local is unconstrained.
\<close>

abbreviation cinit_congruence_st :: "congruence resolved_st_q" where
  "cinit_congruence_st \<equiv> initial_resolved_st_q top (congruence_of_int 0)"

subsection \<open>Classifier-parametric executable transfer\<close>

text \<open>
  \<open>congruence_ops\<close>, Congruence's primitive bundle, is defined beside the abstract
  transfer in \<^theory>\<open>Voblint_Analysis_Congruence.Congruence_Transfer\<close>, so both
  layers read one value. The two constants below are the generic constructions
  of \<^theory>\<open>Voblint_Nonrelational.Numeric_Ops\<close> instantiated at it, not
  independent definitions. The guard transfer needs no third:
  \<^const>\<open>generic_tf_st_for\<close> reads \<open>n_bfilter\<close> off the bundle directly, so naming
  that projection separately would only rename \<^const>\<open>branch_congruence_st\<close>.
\<close>


definition congruence_enter_st_for ::
  "(vname => bool) => call_info =>
   congruence resolved_st_q => congruence resolved_st_q" where
  "congruence_enter_st_for = generic_enter_st_for congruence_ops"

lemma congruence_enter_st_for_eq [simp]:
  "congruence_enter_st_for \<G> ci s =
    bind_formals_resolved_q \<G> (ci_formals ci)
      (map (\<lambda>e. aval_congruence e
        (fun_of_resolved_st_q_for \<G> s)) (ci_args ci))
      (enter_frame_D_resolved_q top s)"
  by (simp add: congruence_enter_st_for_def generic_enter_st_for_def)

definition congruence_tf_st_for ::
  "(vname => bool) => edge_action =>
   congruence resolved_st_q => congruence resolved_st_q" where
  "congruence_tf_st_for = generic_tf_st_for congruence_ops"

lemmas congruence_tf_st_for_simps [simp] =
  generic_tf_st_for.simps [of congruence_ops, folded congruence_tf_st_for_def]

subsection \<open>Classifier-parametric commutation\<close>

text \<open>
  The guard is the only case that needs the liveness premise: the backward
  filter's own commutation is stated on a live state, because a state with no
  live locations reads back as a map the filter can no longer distinguish. Every
  other case is settled for any bundle by \<open>congruence_tf.tf_st_for_commute\<close>.
\<close>

theorem congruence_tf_st_for_commute:
  assumes live: "live_resolved_st_q \<G> s"
  shows
    "fun_of_resolved_st_q_for \<G> (congruence_tf_st_for \<G> a s) =
     congruence_tf_abs a (fun_of_resolved_st_q_for \<G> s)"
  unfolding congruence_tf_st_for_def
  by (rule congruence_tf.tf_st_for_commute)
     (simp add: congruence_backward_domain.branch_st_commute[OF live])

lemma enter_frame_congruence_st_for_commute:
  "fun_of_resolved_st_q_for \<G> (enter_frame_D_resolved_q top s) =
   enter_frame_congruence_for \<G> (fun_of_resolved_st_q_for \<G> s)"
  by (simp add: congruence_tf.op_defs)

lemma congruence_enter_st_for_commute:
  "fun_of_resolved_st_q_for \<G> (congruence_enter_st_for \<G> ci s) =
   enter_congruence_ci_for \<G> ci (fun_of_resolved_st_q_for \<G> s)"
  by (simp add: congruence_tf.op_defs enter_binding_def
                enter_frame_def enter_frame_congruence_st_for_commute)

end
