theory Congruence_Exec
  imports "Voblint_Exec.Default_St_Restriction_Refinement" "Voblint_Nonrelational.Nonrelational_Ops"
    Congruence_Transfer Congruence_Warrowing
begin

section \<open>Running the transfer functions on the state the solver actually stores\<close>

text \<open>
  The solver does not hold a function from variables to residue classes; it
  holds a \<^typ>\<open>congruence default_st\<close>, a compact record with one slot for
  locals, one for globals, and an override list. This theory gives Congruence's
  eight operations on that carrier and proves each agrees with the abstract
  operation on the function a carrier state represents,
  \<^const>\<open>default_st_to_fun\<close>. That agreement -- \<open>commutation\<close> -- is what
  every later soundness statement is transported along.

  \<open>cinit_congruence_st\<close> below is the state a run starts in: a declared global
  holds the single integer \<open>0\<close>, every local is unconstrained.
\<close>

abbreviation cinit_congruence_st :: "congruence default_st" where
  "cinit_congruence_st \<equiv> initial_default_st top (congruence_of_int 0)"

subsection \<open>Classifier-parametric executable transfer\<close>

text \<open>
  \<open>congruence_ops\<close>, Congruence's primitive bundle, is defined beside the abstract
  transfer in \<^theory>\<open>Voblint_Analysis_Congruence.Congruence_Transfer\<close>, so both
  layers read one value. The two constants below are the generic constructions
  of \<^theory>\<open>Voblint_Nonrelational.Nonrelational_Ops\<close> instantiated at it, not
  independent definitions. The guard transfer needs no third:
  \<^const>\<open>generic_tf_st_for\<close> derives its filter from the bundle's evaluator and
  refinement operations.
\<close>

definition congruence_enter_st_for ::
  "(vname => bool) => call_info =>
   congruence default_st => congruence default_st" where
  "congruence_enter_st_for = generic_enter_st_for congruence_ops"

lemma congruence_enter_st_for_eq [simp]:
  "congruence_enter_st_for \<G> ci s =
    bind_formals_default_st \<G> (ci_formals ci)
      (map (\<lambda>e. aval_congruence e
        (default_st_to_fun \<G> s)) (ci_args ci))
      (enter_frame_D_default_st top s)"
  by (simp add: congruence_enter_st_for_def generic_enter_st_for_def)

definition congruence_tf_st_for ::
  "(vname => bool) => edge_action =>
   congruence default_st => congruence default_st" where
  "congruence_tf_st_for = generic_tf_st_for congruence_ops"

lemmas congruence_tf_st_for_simps [simp] =
  generic_tf_st_for.simps [of congruence_ops, folded congruence_tf_st_for_def]

subsection \<open>Classifier-parametric commutation\<close>

text \<open>
  The liveness premise is the guard's: the derived filter's commutation is
  stated on a live state, because a state with no live locations reads back as a
  map the filter can no longer distinguish. \<open>congruence_tf.tf_st_for_commute\<close>
  settles every case, the guard included.
\<close>

theorem congruence_tf_st_for_commute:
  assumes live: "live_default_st \<G> s"
  shows
    "default_st_to_fun \<G> (congruence_tf_st_for \<G> a s) =
     congruence_tf_abs a (default_st_to_fun \<G> s)"
  unfolding congruence_tf_st_for_def
  by (rule congruence_tf.tf_st_for_commute[OF live])

lemma enter_frame_congruence_st_for_commute:
  "default_st_to_fun \<G> (enter_frame_D_default_st top s) =
   enter_frame_congruence_for \<G> (default_st_to_fun \<G> s)"
  by (simp add: congruence_tf.op_defs)

lemma congruence_enter_st_for_commute:
  "default_st_to_fun \<G> (congruence_enter_st_for \<G> ci s) =
   enter_congruence_ci_for \<G> ci (default_st_to_fun \<G> s)"
  by (simp add: congruence_tf.op_defs enter_binding_def
                enter_frame_def enter_frame_congruence_st_for_commute)

end
