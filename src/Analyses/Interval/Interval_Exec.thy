theory Interval_Exec
  imports
    "Voblint_Exec.Exec_St_Restriction_Refinement"
    "Voblint_Nonrelational.Numeric_Ops"
    Interval_Domain
begin

section \<open>Interval executable transfer mirror\<close>

instance ivl :: bounded_warrowing ..


text \<open>
  Executable mirror of @{const ivl_tf_abs} on @{typ "ivl resolved_st_q"}, following
  the sign-domain pattern in \<open>Sign_Exec\<close>. Commutation lemmas hook
  into the generic @{theory Voblint_Exec.Exec_St_Restriction_Refinement} transport; the certified
  end-to-end soundness theory built on this mirror lives in
  \<open>Interval_Analyses\<close>, mirroring \<open>Sign_Analyses\<close>.
\<close>

text \<open>
  \<open>afilter_ivl_st\<close> / \<open>bfilter_ivl_st\<close> and their commutation with
  @{const afilter_ivl} / @{const bfilter_ivl} through
  @{const fun_of_resolved_st_q_for} come from \<open>Interval_Backward\<close> -- the
  interval specialization of the generic @{locale backward_domain} executable
  mirror (\<open>Exec_Backward\<close>). The commutation induction is proved once
  there, not per domain.
\<close>

subsection \<open>Executable transfer function and seeds, generic in the classifier\<close>

text \<open>
  \<open>ivl_ops\<close>, Interval's primitive bundle, is defined beside the abstract transfer
  in \<^theory>\<open>Voblint_Analysis_Interval.Interval_Transfer\<close>, so both layers read one
  value. The three constants below are the generic constructions of
  \<^theory>\<open>Voblint_Nonrelational.Numeric_Ops\<close> instantiated at it, not independent
  definitions.
\<close>

definition branch_ivl_st_for ::
  "(vname => bool) => exp => bool => ivl resolved_st_q => ivl resolved_st_q" where
  "branch_ivl_st_for = n_bfilter ivl_ops"

lemma branch_ivl_st_for_eq [simp]:
  "branch_ivl_st_for \<G> b pol s = branch_ivl_st \<G> b pol s"
  by (simp add: branch_ivl_st_for_def)

definition ivl_enter_st_for ::
  "(vname => bool) => call_info =>
   ivl resolved_st_q => ivl resolved_st_q" where
  "ivl_enter_st_for = generic_enter_st_for ivl_ops"

lemma ivl_enter_st_for_eq [simp]:
  "ivl_enter_st_for \<G> ci s =
    bind_formals_resolved_q \<G> (ci_formals ci)
      (map (\<lambda>e. aval_ivl e
        (fun_of_resolved_st_q_for \<G> s)) (ci_args ci))
      (enter_frame_D_resolved_q ivl_top s)"
  by (simp add: ivl_enter_st_for_def generic_enter_st_for_def)

definition ivl_tf_st_for ::
  "(vname => bool) => edge_action =>
   ivl resolved_st_q => ivl resolved_st_q" where
  "ivl_tf_st_for = generic_tf_st_for ivl_ops"

lemmas ivl_tf_st_for_simps [simp] =
  generic_tf_st_for.simps [of ivl_ops, folded ivl_tf_st_for_def]

text \<open>The state a run starts in: a declared global holds \<open>[0,0]\<close>, a local is unbounded.\<close>

abbreviation cinit_ivl_st :: "ivl resolved_st_q" where
  "cinit_ivl_st \<equiv> initial_resolved_st_q (Ivl MinInf PlusInf) (Ivl (Fin 0) (Fin 0))"

text \<open>
  The entry-state solve's activation seed (\<open>Lifted cinit_ivl_st\<close>, in the
  entry-state equation system) is canonical: neither default (\<open>top\<close> for locals,
  the singleton \<open>{0}\<close> for globals) is witness-bottom, and \<open>cinit_ivl_st\<close> carries
  no explicit override, so \<^const>\<open>resolved_st_q_is_bot_for\<close> is false at every
  declared-globals list. This is the base case the entry-state equation system's
  RHS closure induction needs.
\<close>

lemma cinit_ivl_st_not_bot_for:
  assumes globals: "\<And>x. \<G> x = (x \<in> set gl)"
  shows "\<not> resolved_st_q_is_bot_for gl cinit_ivl_st"
proof -
  have "\<not> is_empty_state (fun_of_resolved_st_q_for \<G> cinit_ivl_st)"
    unfolding is_empty_state_def by (auto simp: is_bottom_ivl_def split: if_splits)
  then show ?thesis
    by (simp add: resolved_st_q_is_bot_for_iff[OF globals])
qed

subsection \<open>Unscoped executable/abstract correspondence, generic in the classifier\<close>

text \<open>Only the guard is Interval's to discharge: every other action is settled
  once for any bundle by \<open>ivl_tf.tf_st_for_commute\<close>.\<close>

lemma ivl_tf_st_for_commute:
  assumes live: "live_resolved_st_q \<G> s"
  shows
    "fun_of_resolved_st_q_for \<G> (ivl_tf_st_for \<G> a s) =
     ivl_tf_abs a (fun_of_resolved_st_q_for \<G> s)"
  unfolding ivl_tf_st_for_def
  by (rule ivl_tf.tf_st_for_commute)
     (simp add: branch_ivl_st_commute[OF live])

lemma ivl_enter_st_for_commute:
  "fun_of_resolved_st_q_for \<G> (ivl_enter_st_for \<G> ci s) =
   enter_ivl_ci_for \<G> ci (fun_of_resolved_st_q_for \<G> s)"
  by (simp add: ivl_tf.op_defs enter_binding_def enter_frame_def)



end

