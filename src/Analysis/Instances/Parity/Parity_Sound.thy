theory Parity_Sound
  imports
    "Voblint_Exec.DG_Local_State_Exec"
    "Voblint_Analysis.Parity_Exec"
begin

section \<open>Parity as a D/G analysis, before any context is chosen\<close>

text \<open>
  What Parity supplies to the framework: a specification, a concretization, and
  the soundness of the one against the other. None of the three mentions a
  context, a routing function, a seed key, or a solver.

  Which context a run uses is chosen elsewhere, by composing these facts with
  a routing policy, so the same names serve the context-insensitive run and
  every context-sensitive one without restatement.
\<close>

definition pctx_spec ::
  "(vname \<Rightarrow> bool) \<Rightarrow> (parity exec_dg_st \<Rightarrow> bool)
     \<Rightarrow> ('x, 'k, unit, parity exec_dg_st lifted, parity exec_dg_st lifted) dg_spec"
where
  "pctx_spec gs empty_pred =
     local_state_dg_spec_st_for_lifted gs empty_pred (parity_tf_st_for gs) (parity_enter_st_for gs)"

definition pctx_abs_spec ::
    "(vname \<Rightarrow> bool) \<Rightarrow> ('x, 'k, unit, parity abs_state lifted, parity abs_state lifted) dg_spec" where
  "pctx_abs_spec gs = local_state_dg_spec_for_lifted gs is_empty_state (parity_tf_for gs)"

definition pctx_gamma ::
    "(vname \<Rightarrow> bool) \<Rightarrow> parity exec_dg_st lifted \<Rightarrow> parity exec_dg_st lifted \<Rightarrow> store set" where
  "pctx_gamma gs d g = gamma_state_lift (map_lift (fun_of_resolved_st_q_for gs) d)"

lemma pctx_gamma_Bot [simp]: "pctx_gamma gs Bot g = {}"
  by (simp add: pctx_gamma_def)

subsection \<open>Soundness of the specification against the concretization\<close>

text \<open>
  \<^locale>\<open>routed_dg_domain_exec\<close> is the reader-commutation layer, itself free of
  any routing context: its three obligations are Parity's own commute lemmas and
  the exactness of the emptiness test.
\<close>

context
  fixes gs :: "vname \<Rightarrow> bool" and empty_pred :: "parity exec_dg_st \<Rightarrow> bool"
  assumes exact: "\<And>s. empty_pred s = is_empty_state (fun_of_resolved_st_q_for gs s)"
begin

interpretation parity_dom: routed_dg_domain_exec
  gs empty_pred "parity_tf_st_for gs" "parity_enter_st_for gs" "parity_tf_for gs"
  by unfold_locales
     (rule parity_tf_st_for_commute, rule parity_enter_st_for_commute, rule exact)

lemma pctx_gamma_eq: "pctx_gamma gs = parity_dom.gamma_exec"
  by (intro ext) (simp add: pctx_gamma_def parity_dom.gamma_exec_def)

theorem pctx_sound_exec: "sound_dg_spec (pctx_spec gs empty_pred) (pctx_gamma gs) gs"
  unfolding pctx_gamma_eq pctx_spec_def
  by (rule parity_dom.sound_dg_spec_st[OF parity_is_sound_transfer_for])

end

end
