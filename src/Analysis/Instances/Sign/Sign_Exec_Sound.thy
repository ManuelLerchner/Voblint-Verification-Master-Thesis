theory Sign_Exec_Sound
  imports Sign_Exec
          "Voblint_Core.Solver_Side_RG"
          "TD.TD_side_upd_rule"
          "Voblint_CFG.CFG_Prune"
          "Voblint_VIMP.VIMP_Notation"
          "Voblint_CFG.Compile_Invariants"
          "Voblint_Core.Exec_DG_Bridge"
          "Voblint_Core.DG_Base_Exec"
begin

section \<open>Native D/G runtime API: an arbitrary VIMP program\<close>

text \<open>
  The exported runtime API \<open>analyse\<close> (\<open>Analyse_Dispatch\<close>, downstream in CLI)
  dispatches through the native D/G equation system (\<open>dg_gen_of\<close>,
  \<^theory>\<open>Voblint_Core.Exec_DG_Bridge\<close>) over the Base-style construction
  \<^theory>\<open>Voblint_Core.DG_Base_Exec\<close>, so the local unknown is the whole
  reachability-lifted abstract state -- no VIMP-global split into a separate
  solver-global unknown. Only the raw computation lives here:
  \<open>analyse_sign_for\<close>'s soundness proof needs the \<open>base_dg_exec_analysis\<close> locale
  (\<open>Run_Analysis_Sound\<close>, Formalization session), one session later than Analysis
  in the locked six-session chain, so that half cannot live in this file; it
  stays in \<open>Sign_Entry\<close> (downstream in CLI), which references these
  definitions with \<open>gs\<close>/\<open>p\<close> applied explicitly.

  \<open>G\<close> stays diagonal at \<open>sign exec_dg_st lifted\<close>, matching what the
  \<open>dg_gen_of\<close> solver route needs -- \<open>G\<close>'s content is never read: every field of
  \<^const>\<open>base_dg_spec_st_for_lifted\<close> threads its incoming \<open>g\<close> through unchanged.
\<close>

definition analyse_sign_eqs_for ::
  "(sign exec_dg_st \<Rightarrow> bool) \<Rightarrow> (vname \<Rightarrow> bool) \<Rightarrow> imp_prog \<Rightarrow>
     pp \<times> unit \<Rightarrow> (pp \<times> unit, unit, (sign exec_dg_st lifted, sign exec_dg_st lifted) dg_state) strategy_tree" where
  "analyse_sign_eqs_for is_bot_pred gs p =
     dg_gen_of
       (base_dg_spec_st_for_lifted gs is_bot_pred (sign_tf_st_for gs) (sign_enter_st_for gs))
       (prog_cfg prog_main_name p) bot (Lifted cinit_sign_st) (Lifted cinit_sign_st)"

definition analyse_sign_for :: "(sign exec_dg_st \<Rightarrow> bool) \<Rightarrow> (vname \<Rightarrow> bool) \<Rightarrow> imp_prog \<Rightarrow>
    (pp \<times> unit) set \<times> (pp \<times> unit + unit \<Rightarrow> (sign exec_dg_st lifted, sign exec_dg_st lifted) dg_state)" where
  "analyse_sign_for is_bot_pred gs p =
     TD_side_always_join_Interp_solve (analyse_sign_eqs_for is_bot_pred gs p) (cfg_exit (prog_cfg prog_main_name p), ())"

text \<open>
  \<open>analyse_sign_env_for\<close> reads the local unknown at \<open>v\<close> (\<open>Inl (v, ())\<close>) straight back
  through \<^const>\<open>fun_of_exec_dg_st_for\<close>/\<^const>\<open>map_lift\<close>: the whole abstract state
  already lives there, so there is no locals-from-\<open>D\<close>/globals-from-\<open>G\<close> reconstruction to
  perform -- \<^const>\<open>combine_env_abs\<close> does not appear. A genuinely unreachable local unknown
  (\<open>Bot\<close>) concretizes to \<open>bot\<close>, matching \<^const>\<open>gamma_state_lift\<close>'s own \<open>Bot\<close> case, so
  the collapse to a plain \<^typ>\<open>sign abs_state\<close> stays sound.
\<close>

definition analyse_sign_env_for :: "(sign exec_dg_st \<Rightarrow> bool) \<Rightarrow> (vname \<Rightarrow> bool) \<Rightarrow> imp_prog \<Rightarrow> pp \<Rightarrow> sign abs_state" where
  "analyse_sign_env_for is_bot_pred gs p v =
     (case map_lift (fun_of_exec_dg_st_for gs) (locals (snd (analyse_sign_for is_bot_pred gs p) (Inl (v, ()))))
      of Bot \<Rightarrow> bot | Lifted s \<Rightarrow> s)"

text \<open>
  Same repeated-solve hazard \<open>analyse_sign_report_for_code\<close> below already guards against, one
  layer up: naive definitional unfolding re-runs \<^const>\<open>analyse_sign_for\<close> once per \<open>v\<close> a caller
  queries, not once per solved analysis. A caller that queries several points against the *same*
  solved analysis -- e.g. a full-state GraphViz render walking every CFG node -- must not hit the
  unfolded form. The \<open>[code]\<close> rewrite below is point-free in \<open>v\<close>, so \<^const>\<open>analyse_sign_for\<close>
  is solved exactly once per partial application to \<open>is_bot_pred gs p\<close>, reused for every \<open>v\<close>
  queried afterward against the resulting closure.
\<close>

declare analyse_sign_env_for_def [code del]

lemma analyse_sign_env_for_code [code]:
  "analyse_sign_env_for is_bot_pred gs p =
     (let sol = snd (analyse_sign_for is_bot_pred gs p)
      in (\<lambda>v. case map_lift (fun_of_exec_dg_st_for gs) (locals (sol (Inl (v, ()))))
              of Bot \<Rightarrow> bot | Lifted s \<Rightarrow> s))"
  unfolding analyse_sign_env_for_def Let_def by (rule refl)

text \<open>
  Convenience instances at \<^const>\<open>declared_global\<close> \<open>p\<close>. \<open>is_bot_pred\<close> is fixed
  here to \<^const>\<open>resolved_st_q_is_bot_for\<close> at \<open>p\<close>'s own
  \<^const>\<open>declared_global_vars\<close>, exact for \<^const>\<open>is_bot_state\<close> by
  @{thm resolved_st_q_is_bot_for_iff} (@{thm declared_global_iff}).
\<close>

definition analyse_sign_eqs :: "imp_prog \<Rightarrow>
    pp \<times> unit \<Rightarrow> (pp \<times> unit, unit, (sign exec_dg_st lifted, sign exec_dg_st lifted) dg_state) strategy_tree" where
  "analyse_sign_eqs p = analyse_sign_eqs_for (resolved_st_q_is_bot_for (declared_global_vars p)) (declared_global p) p"

definition analyse_sign :: "imp_prog \<Rightarrow>
    (pp \<times> unit) set \<times> (pp \<times> unit + unit \<Rightarrow> (sign exec_dg_st lifted, sign exec_dg_st lifted) dg_state)" where
  "analyse_sign p = analyse_sign_for (resolved_st_q_is_bot_for (declared_global_vars p)) (declared_global p) p"

definition analyse_sign_env :: "imp_prog \<Rightarrow> pp \<Rightarrow> sign abs_state" where
  "analyse_sign_env p = analyse_sign_env_for (resolved_st_q_is_bot_for (declared_global_vars p)) (declared_global p) p"



end


