theory Congruence_Sound
  imports
    "Voblint_Exec.DG_Local_State_Exec_Refinement"
    Congruence_Transfer
    Congruence_Exec
begin

section \<open>Congruence as a D/G analysis, before any context is chosen\<close>

text \<open>
  What Congruence supplies to the framework: a specification, a concretization,
  and the soundness of the one against the other. None of the three mentions a
  context, a routing function, a seed key, or a solver -- an analysis is a
  \<^type>\<open>dg_spec\<close> plus a meaning for its values, and that is all this theory
  says.

  Which context a run uses is chosen elsewhere, by composing these facts with a
  routing policy. The same three names serve the context-insensitive run, the
  call-string run and the entry-state run without restatement.

  \<open>cctx_spec\<close> is the whole-state specification over Congruence's
  \<^const>\<open>congruence_tf_st_for\<close> / \<^const>\<open>congruence_enter_st_for\<close> primitives: the
  local unknown carries the entire reachability-lifted abstract state, VIMP
  globals included, so the global channel stays inert. \<open>cctx_abs_spec\<close> is its
  counterpart on the pure carrier, and \<open>cctx_gamma\<close> reads an executable local
  value back as the set of stores it denotes.
\<close>

subsection \<open>The specification\<close>

definition cctx_spec ::
  "(vname \<Rightarrow> bool) \<Rightarrow> (congruence exec_dg_st \<Rightarrow> bool)
   \<Rightarrow> ('x, 'k, unit, congruence exec_dg_st lifted, congruence exec_dg_st lifted) dg_spec"
where
  "cctx_spec gs empty_pred =
     local_state_dg_spec_st_for_lifted gs empty_pred
       (congruence_tf_st_for gs) (congruence_enter_st_for gs)"

definition cctx_abs_spec ::
  "(vname \<Rightarrow> bool)
   \<Rightarrow> ('x, 'k, unit, congruence abs_state lifted, congruence abs_state lifted) dg_spec"
where
  "cctx_abs_spec gs = local_state_dg_spec_for_lifted gs is_empty_state
     skip_congruence assign_congruence special_congruence branch_congruence
     body_congruence return_congruence (enter_congruence_ci_for gs) event_congruence"

subsection \<open>The concretization\<close>

definition cctx_gamma ::
    "(vname \<Rightarrow> bool) \<Rightarrow> congruence exec_dg_st lifted \<Rightarrow> congruence exec_dg_st lifted
       \<Rightarrow> store set" where
  "cctx_gamma gs d g = gamma_state_lift (map_lift (fun_of_resolved_st_q_for gs) d)"

lemma cctx_gamma_Bot [simp]: "cctx_gamma gs Bot g = {}"
  by (simp add: cctx_gamma_def)

subsection \<open>Soundness of the specification against the concretization\<close>

text \<open>
  \<^locale>\<open>routed_dg_domain_exec\<close> is the reader-commutation layer, itself free of
  any routing context: its three obligations are Congruence's own commute lemmas
  and the exactness of the emptiness test. Everything the routed spine later
  needs about Congruence is derived from this one interpretation.
\<close>

context
  fixes gs :: "vname \<Rightarrow> bool" and empty_pred :: "congruence exec_dg_st \<Rightarrow> bool"
  assumes exact: "\<And>s. empty_pred s = is_empty_state (fun_of_resolved_st_q_for gs s)"
begin

interpretation congruence_dom: routed_dg_domain_exec
  gs empty_pred "congruence_tf_st_for gs" "congruence_enter_st_for gs"
  skip_congruence assign_congruence special_congruence branch_congruence
  body_congruence return_congruence "enter_congruence_ci_for gs" event_congruence
  by unfold_locales
     (rule congruence_tf_st_for_commute[unfolded congruence_tf_abs_def], assumption,
      rule congruence_enter_st_for_commute, rule exact)

lemma cctx_gamma_eq: "cctx_gamma gs = congruence_dom.gamma_exec"
  by (intro ext) (simp add: cctx_gamma_def congruence_dom.gamma_exec_def)

theorem cctx_sound_exec: "sound_dg_spec_core (cctx_spec gs empty_pred) (cctx_gamma gs) gs"
  unfolding cctx_gamma_eq cctx_spec_def
  by (rule congruence_dom.sound_dg_spec_core_st[OF congruence_is_sound_transfer_for])

text \<open>Entry is stated apart from \<^locale>\<open>sound_dg_spec_core\<close>, so a routed instance
  cites it separately; the alternative list is the singleton this Base-style entry
  answers.\<close>

theorem cctx_entry_cover_exec:
  assumes "s \<in> cctx_gamma gs d g"
  shows "entry_pairs_cover (\<lambda>d'. cctx_gamma gs d' g) s
           (call_enter gs (CallEdge (ci_dst ci) (ci_formals ci) (ci_args ci)) s)
           [(d, transfer_lift empty_pred (congruence_enter_st_for gs ci) d)]"
  using assms unfolding cctx_gamma_eq congruence_dom.gamma_exec_def
  by (rule congruence_dom.entry_pairs_cover_st[OF congruence_is_sound_transfer_for])

end

subsection \<open>What the initial abstract state describes\<close>

text \<open>
  The initial-state contract, owned here rather than reproved at each assembly
  instance: every concrete store a run may start in is described by
  \<^const>\<open>cinit_congruence_st\<close>. It holds because a declared global starts at zero,
  which the singleton residue class \<^term>\<open>congruence_of_int 0\<close> describes exactly,
  and a local starts unconstrained, which \<^const>\<open>top\<close> describes trivially.
\<close>

lemma congruence_cinit_gamma:
  "cinit_stores gs
     \<subseteq> gamma_state_lift (map_lift (fun_of_exec_dg_st_for gs) (Lifted cinit_congruence_st))"
  by (auto simp: cinit_stores_def gamma_state_def fun_of_exec_dg_st_for_def
      fun_of_resolved_st_q_for_def fun_of_st_cinit_congruence_st_for)

end
