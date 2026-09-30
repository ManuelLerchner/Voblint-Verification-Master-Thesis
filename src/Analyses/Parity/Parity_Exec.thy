theory Parity_Exec
  imports
    "Voblint_Exec.Default_St_Reachability"
    "Voblint_Exec.Default_St_Restriction_Refinement"
    "Voblint_Nonrelational.Nonrelational_Ops"
    Parity_Transfer
begin

section \<open>Does the runnable parity step agree with the one soundness talks about?\<close>

text \<open>
  Two parity transfers exist. The soundness proofs are stated over a store that
  is a plain function from variable name to parity; the generated code runs on
  \<open>default_st\<close>, an association list paired with defaults for locals and
  globals. This theory shows the two never disagree: reading back the executable
  store after a step gives the same function as taking the step on the function
  directly, for every edge action and for procedure entry.

  \<open>parity_tf_st_for_commute\<close> is that statement for the transfer function and
  \<open>parity_enter_st_for_commute\<close> for entry.
\<close>

text \<open>The state a run starts in: a declared global holds \<open>PEven\<close>, a local \<open>PTop\<close>.\<close>

abbreviation cinit_parity_st :: "parity default_st" where
  "cinit_parity_st \<equiv> initial_default_st PTop PEven"

subsection \<open>Classifier-parametric executable transfer\<close>

text \<open>The executable mirror of \<open>parity_tf_abs\<close>/\<open>enter_parity_for\<close>, parametric
  in the classifier.

  \<open>parity_ops\<close>, Parity's primitive bundle, is defined beside the abstract transfer
  in \<^theory>\<open>Voblint_Analysis_Parity.Parity_Transfer\<close>, so both layers read one
  value. The two constants below are the generic constructions of
  \<^theory>\<open>Voblint_Nonrelational.Nonrelational_Ops\<close> instantiated at it. The guard
  transfer needs no third: \<^const>\<open>generic_tf_st_for\<close> derives its filter from the
  bundle's evaluator and refinement operations.\<close>

definition parity_enter_st_for ::
  "(vname => bool) => call_info =>
   parity default_st => parity default_st" where
  "parity_enter_st_for = generic_enter_st_for parity_ops"

lemma parity_enter_st_for_eq [simp]:
  "parity_enter_st_for \<G> ci s =
    bind_formals_default_st \<G> (ci_formals ci)
      (map (\<lambda>e. aval_parity e
        (default_st_to_fun \<G> s)) (ci_args ci))
      (enter_frame_D_default_st PTop s)"
  by (simp add: parity_enter_st_for_def generic_enter_st_for_def top_parity_def)

definition parity_tf_st_for ::
  "(vname => bool) => edge_action =>
   parity default_st => parity default_st" where
  "parity_tf_st_for = generic_tf_st_for parity_ops"

lemmas parity_tf_st_for_simps [simp] =
  generic_tf_st_for.simps [of parity_ops, folded parity_tf_st_for_def]

text \<open>The liveness premise is the guard's: the derived filter commutes with the
  abstract branch on a live state. \<open>parity_tf.tf_st_for_commute\<close> settles every
  action, the guard included.\<close>

theorem parity_tf_st_for_commute:
  assumes live: "live_default_st \<G> s"
  shows "default_st_to_fun \<G> (parity_tf_st_for \<G> a s) =
         parity_tf_abs a (default_st_to_fun \<G> s)"
  unfolding parity_tf_st_for_def
  by (rule parity_tf.tf_st_for_commute[OF live])

lemma enter_frame_parity_st_for_commute:
  "default_st_to_fun \<G> (enter_frame_D_default_st PTop s) =
   enter_frame_parity_for \<G> (default_st_to_fun \<G> s)"
  by (simp add: parity_tf.op_defs)

lemma parity_enter_st_for_commute:
  "default_st_to_fun \<G> (parity_enter_st_for \<G> ci s) =
   enter_parity_ci_for \<G> ci (default_st_to_fun \<G> s)"
  by (simp add: parity_tf.op_defs enter_binding_def
                enter_frame_def enter_frame_parity_st_for_commute)

end
