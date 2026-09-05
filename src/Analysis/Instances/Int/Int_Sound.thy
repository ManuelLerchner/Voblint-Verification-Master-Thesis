theory Int_Sound
  imports
    "Voblint_Exec.DG_Local_State_Exec"
    "Voblint_Analysis.Int_Exec_Sound"
    "Voblint_Analysis.Int_Classify"
begin

section \<open>Int as a D/G analysis, before any context is chosen\<close>

text \<open>
  What Int supplies to the framework: a specification, a concretization, and
  the soundness of the one against the other. None of the three mentions a
  context, a routing function, a seed key, or a solver.

  Which context a run uses is chosen elsewhere, by composing these facts with
  a routing policy, so the same names serve the context-insensitive run and
  every context-sensitive one without restatement.
\<close>

definition int_dom_spec ::
  "refine_mode \<Rightarrow> (int_dom exec_dg_st \<Rightarrow> bool) \<Rightarrow> (vname \<Rightarrow> bool)
     \<Rightarrow> ('x, 'k, unit, int_dom exec_dg_st lifted, int_dom exec_dg_st lifted) dg_spec"
where
  "int_dom_spec mode empty_pred gs =
     local_state_dg_spec_st_for_lifted gs empty_pred (int_tf_st_for mode gs) (int_dom_enter_st_for mode gs)"

definition int_dom_abs_spec ::
    "refine_mode \<Rightarrow> (vname \<Rightarrow> bool)
     \<Rightarrow> ('x, 'k, unit, int_dom abs_state lifted, int_dom abs_state lifted) dg_spec" where
  "int_dom_abs_spec mode gs = local_state_dg_spec_for_lifted gs is_empty_state
     skip_int_dom (assign_int_dom mode) (special_int_dom mode) (branch_int_dom_for mode)
     body_int_dom (return_int_dom mode) (enter_int_dom_ci_for mode gs) event_int_dom"

lemma int_tf_st_for_commute:
  assumes "live_resolved_st_q gs s"
  shows
    "fun_of_resolved_st_q_for gs (int_tf_st_for mode gs a s) =
       int_tf_abs mode a (fun_of_resolved_st_q_for gs s)"
  using assms
  by (cases mode)
     (simp_all add: int_tf_st_never_for_commute int_tf_st_once_for_commute int_tf_st_fixpoint_for_commute)

lemma int_dom_enter_st_for_commute:
  "fun_of_resolved_st_q_for gs (int_dom_enter_st_for mode gs ci s) =
     enter_int_dom_ci_for mode gs ci (fun_of_resolved_st_q_for gs s)"
proof (cases mode)
  case Refine_Never
  then show ?thesis
    by (simp only: int_dom_enter_st_for.simps int_dom_enter_never_st_for_commute)
next
  case Refine_Once
  then show ?thesis
    by (simp only: int_dom_enter_st_for.simps int_dom_enter_once_st_for_commute)
next
  case Refine_Fixpoint
  then show ?thesis
    by (simp only: int_dom_enter_st_for.simps int_dom_enter_fixpoint_st_for_commute)
qed

lemma int_dom_abs_spec_sound: "sound_dg_spec_core (int_dom_abs_spec mode gs) gamma_dg_local_state gs"
  unfolding int_dom_abs_spec_def
  by (rule sound_transfer_for.local_state_dg_spec_sound
        [OF int_is_sound_transfer_for is_empty_state_gamma_state_empty])


definition int_dom_gamma ::
    "(vname \<Rightarrow> bool) \<Rightarrow> int_dom exec_dg_st lifted \<Rightarrow> int_dom exec_dg_st lifted \<Rightarrow> store set" where
  "int_dom_gamma gs d g = gamma_state_lift (map_lift (fun_of_resolved_st_q_for gs) d)"

lemma int_dom_gamma_Bot [simp]: "int_dom_gamma gs Bot g = {}"
  by (simp add: int_dom_gamma_def)

subsection \<open>Soundness of the specification against the concretization\<close>

text \<open>
  \<^locale>\<open>routed_dg_domain_exec\<close> is the reader-commutation layer, itself free of
  any routing context: its three obligations are Int's own commute lemmas and
  the exactness of the emptiness test.
\<close>

context
  fixes gs :: "vname \<Rightarrow> bool" and empty_pred :: "int_dom exec_dg_st \<Rightarrow> bool" and mode :: refine_mode
  assumes exact: "\<And>s. empty_pred s = is_empty_state (fun_of_resolved_st_q_for gs s)"
begin

interpretation int_dom: routed_dg_domain_exec
  gs empty_pred "int_tf_st_for mode gs" "int_dom_enter_st_for mode gs"
  skip_int_dom "assign_int_dom mode" "special_int_dom mode" "branch_int_dom_for mode"
  body_int_dom "return_int_dom mode" "enter_int_dom_ci_for mode gs" event_int_dom
  by unfold_locales
     (rule int_tf_st_for_commute[unfolded int_tf_abs_def], assumption,
      rule int_dom_enter_st_for_commute, rule exact)

lemma int_dom_gamma_eq: "int_dom_gamma gs = int_dom.gamma_exec"
  by (intro ext) (simp add: int_dom_gamma_def int_dom.gamma_exec_def)

theorem int_dom_sound_exec: "sound_dg_spec_core (int_dom_spec mode empty_pred gs) (int_dom_gamma gs) gs"
  unfolding int_dom_gamma_eq int_dom_spec_def
  by (rule int_dom.sound_dg_spec_core_st[OF int_is_sound_transfer_for])

text \<open>Entry is stated apart from \<^locale>\<open>sound_dg_spec_core\<close>, so a routed instance cites
  it separately; the alternative list is the singleton this Base-style entry answers.\<close>

theorem int_dom_entry_cover_exec:
  assumes "s \<in> int_dom_gamma gs d g"
  shows "entry_pairs_cover (\<lambda>d'. int_dom_gamma gs d' g) s
           (call_enter gs (CallEdge (ci_dst ci) (ci_formals ci) (ci_args ci)) s)
           [(d, transfer_lift empty_pred (int_dom_enter_st_for mode gs ci) d)]"
  using assms unfolding int_dom_gamma_eq int_dom.gamma_exec_def
  by (rule int_dom.entry_pairs_cover_st[OF int_is_sound_transfer_for])

end

end
