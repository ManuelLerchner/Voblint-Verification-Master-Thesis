theory Sign_Sound
  imports
    "Voblint_Exec.DG_Local_State_Exec_Refinement"
    Sign_Transfer
    Sign_Exec
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

  \<open>sign_conf_spec\<close> is the whole-state specification over Sign's
  \<^const>\<open>sign_tf_st_for\<close> / \<^const>\<open>sign_enter_st_for\<close> primitives: the local
  unknown carries the entire reachability-lifted abstract state, VIMP globals
  included, so the global channel stays inert. \<open>sign_conf_abs_spec\<close> is its
  counterpart on the pure carrier, and \<open>sign_conf_gamma\<close> reads an executable local
  value back as the set of stores it denotes.
\<close>

subsection \<open>The specification\<close>

definition sign_conf_spec ::
  "(vname \<Rightarrow> bool) \<Rightarrow> (sign exec_dg_st \<Rightarrow> bool)
   \<Rightarrow> ('x, 'k, unit, sign exec_dg_st lifted, sign exec_dg_st lifted) dg_spec"
where
  "sign_conf_spec \<G> empty_pred =
     local_state_dg_spec_st_for_lifted \<G> empty_pred (sign_tf_st_for \<G>) (sign_enter_st_for \<G>)"

lemma dg_spec_wf_sign_conf_spec [intro, simp]: "dg_spec_wf (sign_conf_spec \<G> empty_pred)"
  by (simp add: sign_conf_spec_def)

definition sign_conf_abs_spec ::
  "(vname \<Rightarrow> bool)
   \<Rightarrow> ('x, 'k, unit, sign abs_state lifted, sign abs_state lifted) dg_spec"
where
  "sign_conf_abs_spec \<G> = local_state_dg_spec_for_lifted \<G> is_empty_state
     skip_sign assign_sign special_sign branch_sign body_sign return_sign
     (enter_sign_ci_for \<G>) event_sign"

declare sign_conf_spec_def [code_unfold]
declare sign_conf_abs_spec_def [code_unfold]

subsection \<open>The concretization\<close>

definition sign_conf_gamma ::
    "(vname \<Rightarrow> bool) \<Rightarrow> sign exec_dg_st lifted \<Rightarrow> sign exec_dg_st lifted \<Rightarrow> store set" where
  "sign_conf_gamma \<G> d g = \<lbrakk>map_lift (fun_of_resolved_st_q_for \<G>) d\<rbrakk>\<^sub>\<bottom>"

lemma sign_conf_gamma_Bot [simp]: "sign_conf_gamma \<G> Bot g = {}"
  by (simp add: sign_conf_gamma_def)

subsection \<open>Soundness of the specification against the concretization\<close>

text \<open>
  \<^locale>\<open>routed_dg_domain_exec\<close> is the reader-commutation layer, itself free of
  any routing context: its three obligations are Sign's own commute lemmas and
  the exactness of the emptiness test. Everything the routed spine later needs
  about Sign is derived from this one interpretation.
\<close>

context
  fixes \<G> :: "vname \<Rightarrow> bool" and empty_pred :: "sign exec_dg_st \<Rightarrow> bool"
  assumes exact: "\<And>s. empty_pred s = is_empty_state (fun_of_resolved_st_q_for \<G> s)"
begin

interpretation sign_dom: routed_dg_domain_exec
  \<G> empty_pred "sign_tf_st_for \<G>" "sign_enter_st_for \<G>"
  skip_sign assign_sign special_sign branch_sign body_sign return_sign
  "enter_sign_ci_for \<G>" event_sign
  by unfold_locales
     (rule sign_tf_st_for_commute[unfolded sign_tf.tf_abs_def], assumption,
      rule sign_enter_st_for_commute, rule exact)

lemma sign_conf_gamma_eq: "sign_conf_gamma \<G> = sign_dom.gamma_exec"
  by (intro ext) (simp add: sign_conf_gamma_def sign_dom.gamma_exec_def)

theorem sign_conf_sound_exec:
  "sound_dg_spec_core (sign_conf_spec \<G> empty_pred) (sign_conf_gamma \<G>) \<G>"
  unfolding sign_conf_gamma_eq sign_conf_spec_def
  by (rule sign_dom.sound_dg_spec_core_st[OF sign_tf.is_sound_transfer_for])

text \<open>Entry is stated apart from \<^locale>\<open>sound_dg_spec_core\<close>, so a routed instance cites
  it separately; the alternative list is the singleton this Base-style entry answers.\<close>

theorem sign_conf_entry_cover_exec:
  assumes "s \<in> sign_conf_gamma \<G> d g"
  shows "entry_pairs_cover (\<lambda>d'. sign_conf_gamma \<G> d' g) s
           (call_enter \<G> (CallEdge (ci_dst ci) (ci_formals ci) (ci_args ci)) s)
           [(d, transfer_lift empty_pred (sign_enter_st_for \<G> ci) d)]"
  using assms unfolding sign_conf_gamma_eq sign_dom.gamma_exec_def
  by (rule sign_dom.entry_pairs_cover_st[OF sign_tf.is_sound_transfer_for])

end

subsection \<open>What the initial abstract state describes\<close>

text \<open>
  The initial-state contract, owned here rather than reproved at each assembly
  instance: every concrete store a run may start in is described by
  \<^const>\<open>cinit_sign_st\<close>. It holds because a declared global starts at zero, which
  \<^const>\<open>SZero\<close> describes exactly, and a local starts unconstrained, which
  \<^const>\<open>STop\<close> describes trivially --- so it is a fact about Sign's initial state
  and its concretization, and about nothing else.
\<close>

lemma sign_cinit_gamma:
  "cinit_stores \<G>
     \<subseteq> \<lbrakk>map_lift (fun_of_exec_dg_st_for \<G>) (Lifted cinit_sign_st)\<rbrakk>\<^sub>\<bottom>"
  by (auto simp: cinit_stores_def gamma_state_def fun_of_exec_dg_st_for_def
      fun_of_resolved_st_q_for_def fun_of_initial_resolved_st_q)

end
