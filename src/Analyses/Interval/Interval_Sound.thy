theory Interval_Sound
  imports
    "Voblint_Exec.DG_Local_State_Exec_Refinement"
    Interval_Transfer
    Interval_Exec
    "Voblint_Result.DG_Result_Construction"
    "Voblint_Solver.TD_Solver_Bridge"
    "Voblint_Compile.Compile_Invariants"
begin

section \<open>Interval as a D/G analysis, before any context is chosen\<close>

text \<open>
  What Interval supplies to the framework: a specification, a concretization, and
  the soundness of the one against the other. None of the three mentions a
  context, a routing function, a seed key, or a solver.

  Which context a run uses is chosen elsewhere, by composing these facts with
  a routing policy, so the same names serve the context-insensitive run and
  every context-sensitive one without restatement.
\<close>

definition interval_spec ::
  "(vname \<Rightarrow> bool) \<Rightarrow> (ivl exec_dg_st \<Rightarrow> bool)
   \<Rightarrow> ('x, 'k, unit, ivl exec_dg_st lifted, ivl exec_dg_st lifted) dg_spec"
where
  "interval_spec \<G> empty_pred =
     local_state_dg_spec_st_for_lifted \<G> empty_pred (ivl_tf_st_for \<G>) (ivl_enter_st_for \<G>)"

definition interval_abs_spec ::
  "(vname \<Rightarrow> bool) \<Rightarrow> ('x, 'k, unit, ivl abs_state lifted, ivl abs_state lifted) dg_spec"
where
  "interval_abs_spec \<G> = local_state_dg_spec_for_lifted \<G> is_empty_state
     skip_ivl assign_ivl special_ivl branch_ivl body_ivl return_ivl
     (enter_ivl_ci_for \<G>) event_ivl"

declare interval_spec_def [code_unfold]
declare interval_abs_spec_def [code_unfold]

definition interval_gamma ::
    "(vname \<Rightarrow> bool) \<Rightarrow> ivl exec_dg_st lifted \<Rightarrow> ivl exec_dg_st lifted \<Rightarrow> store set" where
  "interval_gamma \<G> d g = \<lbrakk>map_lift (fun_of_resolved_st_q_for \<G>) d\<rbrakk>\<^sub>\<bottom>"

lemma interval_gamma_Bot [simp]: "interval_gamma \<G> Bot g = {}"
  by (simp add: interval_gamma_def)

subsection \<open>Soundness of the specification against the concretization\<close>

text \<open>
  \<^locale>\<open>routed_dg_domain_exec\<close> is the reader-commutation layer, itself free of
  any routing context: its three obligations are Interval's own commute lemmas and
  the exactness of the emptiness test.
\<close>

context
  fixes \<G> :: "vname \<Rightarrow> bool" and empty_pred :: "ivl exec_dg_st \<Rightarrow> bool"
  assumes exact: "\<And>s. empty_pred s = is_empty_state (fun_of_resolved_st_q_for \<G> s)"
begin

interpretation ivl_dom: routed_dg_domain_exec
  \<G> empty_pred "ivl_tf_st_for \<G>" "ivl_enter_st_for \<G>"
  skip_ivl assign_ivl special_ivl branch_ivl body_ivl return_ivl
  "enter_ivl_ci_for \<G>" event_ivl
  by unfold_locales
     (rule ivl_tf_st_for_commute[unfolded ivl_tf.tf_abs_def], assumption,
      rule ivl_enter_st_for_commute, rule exact)

lemma interval_gamma_eq: "interval_gamma \<G> = ivl_dom.gamma_exec"
  by (intro ext) (simp add: interval_gamma_def ivl_dom.gamma_exec_def)

theorem interval_sound_exec:
  "analysis_contract (interval_spec \<G> empty_pred) (interval_gamma \<G>) \<G>"
  unfolding interval_gamma_eq interval_spec_def
  by (rule ivl_dom.analysis_contract_st[OF ivl_tf.is_sound_transfer_for])

text \<open>Entry is stated apart from \<^locale>\<open>analysis_contract\<close>, so a routed instance cites
  it separately; the alternative list is the singleton this Base-style entry answers.\<close>

theorem interval_entry_cover_exec:
  assumes "s \<in> interval_gamma \<G> d g"
  shows "entry_pairs_cover (\<lambda>d'. interval_gamma \<G> d' g) s
           (call_enter \<G> (CallEdge (ci_dst ci) (ci_formals ci) (ci_args ci)) s)
           [(d, transfer_lift empty_pred (ivl_enter_st_for \<G> ci) d)]"
  using assms unfolding interval_gamma_eq ivl_dom.gamma_exec_def
  by (rule ivl_dom.entry_pairs_cover_st[OF ivl_tf.is_sound_transfer_for])

end

subsection \<open>What the initial abstract state describes\<close>

text \<open>
  The initial-state contract, owned here rather than reproved at each of the four
  assembly instances: every concrete store a run may start in is described by
  \<^const>\<open>cinit_ivl_st\<close>. A declared global starts at zero, which the singleton
  interval describes exactly; a local starts unconstrained, which the unbounded
  interval describes trivially. The solver discipline does not enter into it, which
  is why one lemma serves all four.
\<close>

lemma interval_cinit_gamma:
  "cinit_stores \<G>
     \<subseteq> \<lbrakk>map_lift (fun_of_exec_dg_st_for \<G>) (Lifted cinit_ivl_st)\<rbrakk>\<^sub>\<bottom>"
  by (auto simp: cinit_stores_def gamma_state_def fun_of_exec_dg_st_for_def
      fun_of_resolved_st_q_for_def fun_of_initial_resolved_st_q)

end
