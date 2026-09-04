theory Sign_Sound
  imports
    "Voblint_Exec.DG_Local_State_Exec"
    "Voblint_Analysis.Sign_Transfer"
    "Voblint_Analysis.Sign_Exec"
begin

section \<open>Sign as a D/G analysis, before any context is chosen\<close>

text \<open>
  What Sign supplies to the framework: a specification, a concretization, and
  the soundness of the one against the other. None of the three mentions a
  context, a routing function, a seed key, or a solver -- an analysis is a
  \<^type>\<open>dg_spec\<close> plus a meaning for its values, and that is all this theory
  says.

  Which context a run uses is chosen elsewhere, by composing these facts with
  a routing policy. The same three names serve the context-insensitive run,
  the call-string run and the entry-state run without restatement; that is
  what makes the domain and the policy independently reusable rather than a
  matrix of pairs.

  \<open>sctx_spec\<close> is the whole-state specification over Sign's
  \<^const>\<open>sign_tf_st_for\<close> / \<^const>\<open>sign_enter_st_for\<close> primitives: the local
  unknown carries the entire reachability-lifted abstract state, VIMP globals
  included, so the global channel stays inert. \<open>sctx_abs_spec\<close> is its
  counterpart on the pure carrier, and \<open>sctx_gamma\<close> reads an executable local
  value back as the set of stores it denotes.
\<close>

subsection \<open>The specification\<close>

definition sctx_spec ::
  "(vname \<Rightarrow> bool) \<Rightarrow> (sign exec_dg_st \<Rightarrow> bool)
   \<Rightarrow> ('x, 'k, unit, sign exec_dg_st lifted, sign exec_dg_st lifted) dg_spec"
where
  "sctx_spec gs empty_pred =
     local_state_dg_spec_st_for_lifted gs empty_pred (sign_tf_st_for gs) (sign_enter_st_for gs)"

definition sctx_abs_spec ::
  "(vname \<Rightarrow> bool)
   \<Rightarrow> ('x, 'k, unit, sign abs_state lifted, sign abs_state lifted) dg_spec"
where
  "sctx_abs_spec gs = local_state_dg_spec_for_lifted gs is_empty_state
     skip_sign assign_sign special_sign branch_sign body_sign return_sign
     (enter_sign_ci_for gs) event_sign"

subsection \<open>The concretization\<close>

definition sctx_gamma ::
    "(vname \<Rightarrow> bool) \<Rightarrow> sign exec_dg_st lifted \<Rightarrow> sign exec_dg_st lifted \<Rightarrow> store set" where
  "sctx_gamma gs d g = gamma_state_lift (map_lift (fun_of_resolved_st_q_for gs) d)"

lemma sctx_gamma_Bot [simp]: "sctx_gamma gs Bot g = {}"
  by (simp add: sctx_gamma_def)

subsection \<open>Soundness of the specification against the concretization\<close>

text \<open>
  \<^locale>\<open>routed_dg_domain_exec\<close> is the reader-commutation layer, itself free of
  any routing context: its three obligations are Sign's own commute lemmas and
  the exactness of the emptiness test. Everything the routed spine later needs
  about Sign is derived from this one interpretation.
\<close>

context
  fixes gs :: "vname \<Rightarrow> bool" and empty_pred :: "sign exec_dg_st \<Rightarrow> bool"
  assumes exact: "\<And>s. empty_pred s = is_empty_state (fun_of_resolved_st_q_for gs s)"
begin

interpretation sign_dom: routed_dg_domain_exec
  gs empty_pred "sign_tf_st_for gs" "sign_enter_st_for gs"
  skip_sign assign_sign special_sign branch_sign body_sign return_sign
  "enter_sign_ci_for gs" event_sign
  by unfold_locales
     (rule sign_tf_st_for_commute[unfolded sign_tf_abs_def], assumption,
      rule sign_enter_st_for_commute, rule exact)

lemma sctx_gamma_eq: "sctx_gamma gs = sign_dom.gamma_exec"
  by (intro ext) (simp add: sctx_gamma_def sign_dom.gamma_exec_def)

theorem sctx_sound_exec: "sound_dg_spec (sctx_spec gs empty_pred) (sctx_gamma gs) gs"
  unfolding sctx_gamma_eq sctx_spec_def
  by (rule sign_dom.sound_dg_spec_st[OF sign_is_sound_transfer_for])

text \<open>Entry is stated apart from \<^locale>\<open>sound_dg_spec\<close>, so a routed instance cites
  it separately; the alternative list is the singleton this Base-style entry answers.\<close>

theorem sctx_entry_cover_exec:
  assumes "s \<in> sctx_gamma gs d g"
  shows "entry_pairs_cover (\<lambda>d'. sctx_gamma gs d' g) s
           (call_enter gs (CallEdge (ci_dst ci) (ci_formals ci) (ci_args ci)) s)
           [(d, transfer_lift empty_pred (sign_enter_st_for gs ci) d)]"
  using assms unfolding sctx_gamma_eq sign_dom.gamma_exec_def
  by (rule sign_dom.entry_pairs_cover_st[OF sign_is_sound_transfer_for])

end

end
