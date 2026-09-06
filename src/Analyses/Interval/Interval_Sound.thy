theory Interval_Sound
  imports
    "Voblint_Exec.DG_Local_State_Exec"
    Interval_Transfer
    Interval_Exec_Sound
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
  "interval_spec gs empty_pred =
     local_state_dg_spec_st_for_lifted gs empty_pred (ivl_tf_st_for gs) (ivl_enter_st_for gs)"

definition interval_abs_spec ::
  "(vname \<Rightarrow> bool) \<Rightarrow> ('x, 'k, unit, ivl abs_state lifted, ivl abs_state lifted) dg_spec"
where
  "interval_abs_spec gs = local_state_dg_spec_for_lifted gs is_empty_state
     skip_ivl assign_ivl special_ivl branch_ivl body_ivl return_ivl
     (enter_ivl_ci_for gs) event_ivl"

definition interval_gamma ::
    "(vname \<Rightarrow> bool) \<Rightarrow> ivl exec_dg_st lifted \<Rightarrow> ivl exec_dg_st lifted \<Rightarrow> store set" where
  "interval_gamma gs d g = gamma_state_lift (map_lift (fun_of_resolved_st_q_for gs) d)"

lemma interval_gamma_Bot [simp]: "interval_gamma gs Bot g = {}"
  by (simp add: interval_gamma_def)

subsection \<open>Soundness of the specification against the concretization\<close>

text \<open>
  \<^locale>\<open>routed_dg_domain_exec\<close> is the reader-commutation layer, itself free of
  any routing context: its three obligations are Interval's own commute lemmas and
  the exactness of the emptiness test.
\<close>

context
  fixes gs :: "vname \<Rightarrow> bool" and empty_pred :: "ivl exec_dg_st \<Rightarrow> bool"
  assumes exact: "\<And>s. empty_pred s = is_empty_state (fun_of_resolved_st_q_for gs s)"
begin

interpretation ivl_dom: routed_dg_domain_exec
  gs empty_pred "ivl_tf_st_for gs" "ivl_enter_st_for gs"
  skip_ivl assign_ivl special_ivl branch_ivl body_ivl return_ivl
  "enter_ivl_ci_for gs" event_ivl
  by unfold_locales
     (rule ivl_tf_st_for_commute[unfolded ivl_tf_abs_def], assumption,
      rule ivl_enter_st_for_commute, rule exact)

lemma interval_gamma_eq: "interval_gamma gs = ivl_dom.gamma_exec"
  by (intro ext) (simp add: interval_gamma_def ivl_dom.gamma_exec_def)

theorem interval_sound_exec: "sound_dg_spec_core (interval_spec gs empty_pred) (interval_gamma gs) gs"
  unfolding interval_gamma_eq interval_spec_def
  by (rule ivl_dom.sound_dg_spec_core_st[OF ivl_is_sound_transfer_for])

text \<open>Entry is stated apart from \<^locale>\<open>sound_dg_spec_core\<close>, so a routed instance cites
  it separately; the alternative list is the singleton this Base-style entry answers.\<close>

theorem interval_entry_cover_exec:
  assumes "s \<in> interval_gamma gs d g"
  shows "entry_pairs_cover (\<lambda>d'. interval_gamma gs d' g) s
           (call_enter gs (CallEdge (ci_dst ci) (ci_formals ci) (ci_args ci)) s)
           [(d, transfer_lift empty_pred (ivl_enter_st_for gs ci) d)]"
  using assms unfolding interval_gamma_eq ivl_dom.gamma_exec_def
  by (rule ivl_dom.entry_pairs_cover_st[OF ivl_is_sound_transfer_for])

end

end
