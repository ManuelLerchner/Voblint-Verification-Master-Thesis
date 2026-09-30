theory Interval_Exec
  imports
    "Voblint_Exec.Default_St_Restriction_Refinement"
    "Voblint_Nonrelational.Nonrelational_Ops"
    Interval_Domain
begin

section \<open>Interval executable transfer mirror\<close>

text \<open>
  Executable mirror of @{const ivl_tf_abs} on @{typ "ivl default_st"}, following
  the sign-domain pattern in \<open>Sign_Exec\<close>. Commutation lemmas hook
  into the generic @{theory Voblint_Exec.Default_St_Restriction_Refinement} transport; the certified
  end-to-end soundness theory built on this mirror lives in
  \<open>Interval_Analyses\<close>, mirroring \<open>Sign_Analyses\<close>.
\<close>

text \<open>
  The executable guard filter is derived from the bundle's evaluator and
  refinement operations (\<^const>\<open>n_bfilter\<close>), and its commutation with
  @{const branch_ivl} through @{const default_st_to_fun} is proved once
  for every certified bundle, not per domain.
\<close>

subsection \<open>Executable transfer function and seeds, generic in the classifier\<close>

text \<open>
  \<open>ivl_ops\<close>, Interval's primitive bundle, is defined beside the abstract transfer
  in \<^theory>\<open>Voblint_Analysis_Interval.Interval_Transfer\<close>, so both layers read one
  value. The two constants below are the generic constructions of
  \<^theory>\<open>Voblint_Nonrelational.Nonrelational_Ops\<close> instantiated at it, not independent
  definitions.
\<close>

definition ivl_enter_st_for ::
  "(vname => bool) => call_info =>
   ivl default_st => ivl default_st" where
  "ivl_enter_st_for = generic_enter_st_for ivl_ops"

lemma ivl_enter_st_for_eq [simp]:
  "ivl_enter_st_for \<G> ci s =
    bind_formals_default_st \<G> (ci_formals ci)
      (map (\<lambda>e. aval_ivl e
        (default_st_to_fun \<G> s)) (ci_args ci))
      (enter_frame_D_default_st ivl_top s)"
  by (simp add: ivl_enter_st_for_def generic_enter_st_for_def top_ivl_def)

definition ivl_tf_st_for ::
  "(vname => bool) => edge_action =>
   ivl default_st => ivl default_st" where
  "ivl_tf_st_for = generic_tf_st_for ivl_ops"

lemmas ivl_tf_st_for_simps [simp] =
  generic_tf_st_for.simps [of ivl_ops, folded ivl_tf_st_for_def]

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
  have "\<not> is_empty_state (default_st_to_fun \<G> cinit_ivl_st)"
    unfolding is_empty_state_def by (auto simp: is_bottom_ivl_def split: if_splits)
  then show ?thesis
    by (simp add: default_st_is_bot_for_iff[OF globals])
qed

subsection \<open>Unscoped executable/abstract correspondence, generic in the classifier\<close>

text \<open>Nothing here is Interval's to discharge: \<open>ivl_tf.tf_st_for_commute\<close>
  settles every action, the guard included, on a live state.\<close>

lemma ivl_tf_st_for_commute:
  assumes live: "live_default_st \<G> s"
  shows
    "default_st_to_fun \<G> (ivl_tf_st_for \<G> a s) =
     ivl_tf_abs a (default_st_to_fun \<G> s)"
  unfolding ivl_tf_st_for_def
  by (rule ivl_tf.tf_st_for_commute[OF live])

lemma ivl_enter_st_for_commute:
  "default_st_to_fun \<G> (ivl_enter_st_for \<G> ci s) =
   enter_ivl_ci_for \<G> ci (default_st_to_fun \<G> s)"
  by (simp add: ivl_tf.op_defs enter_binding_def enter_frame_def)


end
