theory Parity_Exec
  imports
    "Voblint_Exec.Exec_St_Reachability"
    "Voblint_Exec.Exec_St_Restriction_Refinement"
    "Voblint_Nonrelational.Numeric_Ops"
    Parity_Transfer
begin

section \<open>Does the runnable parity step agree with the one soundness talks about?\<close>

text \<open>
  Two parity transfers exist. The soundness proofs are stated over a store that
  is a plain function from variable name to parity; the generated code runs on
  \<open>resolved_st_q\<close>, an association list paired with defaults for locals and
  globals. This theory shows the two never disagree: reading back the executable
  store after a step gives the same function as taking the step on the function
  directly, for every edge action and for procedure entry.

  \<open>parity_tf_st_for_commute\<close> is that statement for the transfer function and
  \<open>parity_enter_st_for_commute\<close> for entry.
\<close>

instance parity :: bounded_warrowing ..

text \<open>The state a run starts in: a declared global holds \<open>PEven\<close>, a local \<open>PTop\<close>.\<close>

abbreviation cinit_parity_st :: "parity resolved_st_q" where
  "cinit_parity_st \<equiv> initial_resolved_st_q PTop PEven"

subsection \<open>Classifier-parametric executable transfer\<close>

text \<open>The executable mirror of \<open>parity_tf_abs\<close>/\<open>enter_parity_for\<close>, parametric
  in the classifier.

  \<open>parity_ops\<close>, Parity's primitive bundle, is defined beside the abstract transfer
  in \<^theory>\<open>Voblint_Analysis_Parity.Parity_Transfer\<close>, so both layers read one
  value. The two constants below are the generic constructions of
  \<^theory>\<open>Voblint_Nonrelational.Numeric_Ops\<close> instantiated at it. Parity's branch
  transfer is the identity, so unlike Sign and Interval there is no
  \<open>branch_parity_st_for\<close> at all --- \<open>n_bfilter\<close>'s value here is the identity
  function, and nothing needs to name it separately.\<close>

definition parity_enter_st_for ::
  "(vname => bool) => call_info =>
   parity resolved_st_q => parity resolved_st_q" where
  "parity_enter_st_for = generic_enter_st_for parity_ops"

lemma parity_enter_st_for_eq [simp]:
  "parity_enter_st_for gs ci s =
    bind_formals_resolved_q gs (ci_formals ci)
      (map (\<lambda>e. aval_parity e
        (fun_of_resolved_st_q_for gs s)) (ci_args ci))
      (enter_frame_D_resolved_q PTop s)"
  by (simp add: parity_enter_st_for_def generic_enter_st_for_def)

definition parity_tf_st_for ::
  "(vname => bool) => edge_action =>
   parity resolved_st_q => parity resolved_st_q" where
  "parity_tf_st_for = generic_tf_st_for parity_ops"

lemmas parity_tf_st_for_simps [simp] =
  generic_tf_st_for.simps [of parity_ops, folded parity_tf_st_for_def]

text \<open>Both filters are the identity here, so the guard obligation the generic
  commutation leaves open holds on every executable state, not only a live one.\<close>

theorem parity_tf_st_for_commute:
  "fun_of_resolved_st_q_for gs (parity_tf_st_for gs a s) =
   parity_tf_abs a (fun_of_resolved_st_q_for gs s)"
  unfolding parity_tf_st_for_def
  by (rule parity_tf.tf_st_for_commute) (simp add: branch_parity_def)

text \<open>
  The same commutation in the shape the shared assembly's transfer obligation is
  stated in, which carries a liveness premise because a domain may need it. Parity
  does not: \<^const>\<open>parity_tf_st_for\<close> commutes on every executable state, and
  \<open>parity_tf_st_for_commute\<close> above remains the theorem this domain exports. This
  corollary exists so registration can cite a registration-shaped fact without the
  stronger one being weakened to meet it.
\<close>

lemma parity_tf_st_for_commute_if_live:
  assumes "live_resolved_st_q gs s"
  shows "fun_of_resolved_st_q_for gs (parity_tf_st_for gs a s) =
         parity_tf_abs a (fun_of_resolved_st_q_for gs s)"
  by (rule parity_tf_st_for_commute)

lemma enter_frame_parity_st_for_commute:
  "fun_of_resolved_st_q_for gs (enter_frame_D_resolved_q PTop s) =
   enter_frame_parity_for gs (fun_of_resolved_st_q_for gs s)"
  by (simp add: parity_tf.op_defs)

lemma parity_enter_st_for_commute:
  "fun_of_resolved_st_q_for gs (parity_enter_st_for gs ci s) =
   enter_parity_ci_for gs ci (fun_of_resolved_st_q_for gs s)"
  by (simp add: parity_tf.op_defs enter_binding_def
                enter_frame_def enter_frame_parity_st_for_commute)

end

