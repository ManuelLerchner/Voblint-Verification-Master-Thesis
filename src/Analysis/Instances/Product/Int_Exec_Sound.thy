theory Int_Exec_Sound
  imports
    "Voblint_Core.DG_Base"
    "Voblint_Exec.DG_Base_Exec"
    Int_Exec
    Int_Warrowing
    "Voblint_Exec.Exec_DG_Bridge"
    "Voblint_Compile.Compile_Invariants"
    "Voblint_CFG.CFG_Prune"
    "Voblint_VIMP.VIMP_Program"
    "TD.TD_side_upd_rule"
begin

section \<open>Native D/G runtime API: the composite integer domain, Refine_Fixpoint mode\<close>

text \<open>
  The production route for \<open>int_dom\<close>, mirroring \<open>analyse_interval_dg_eqs_for\<close>/
  \<open>analyse_interval_dg_for\<close>/\<open>analyse_interval_dg_env_for\<close> (\<open>Interval_Exec_Sound\<close>) almost
  verbatim: the local unknown carries the whole reachability-lifted \<open>int_dom exec_dg_st\<close>, so
  a VIMP global lives exactly where a local does, with no separate flow-insensitive
  solver-global summary to route it through.

  Fixed at \<open>Refine_Fixpoint\<close> (\<^const>\<open>int_tf_st_fixpoint_for\<close>,
  \<^const>\<open>int_dom_enter_fixpoint_st_for\<close>, \<^theory>\<open>Voblint_Analysis.Int_Exec\<close>): the most
  precise of the three refinement modes (\<^const>\<open>refine\<close>, \<^theory>\<open>Voblint_Analysis.Int_Refinement\<close>)
  and this composite domain's own natural production default, the same one-pairing-per-domain
  convention \<open>Sign_Analysis\<close>/\<open>Solver_Join\<close> and \<open>Interval_Analysis\<close>/\<open>Solver_Warrow\<close> already fix
  (\<open>Analyse_Dispatch\<close>, Examples session, downstream): \<open>Refine_Never\<close>/\<open>Refine_Once\<close> stay
  reachable through \<^theory>\<open>Voblint_Analysis.Int_Exec\<close>'s own bundles, not exposed here.

  Solved via \<^const>\<open>TD_side_warrowing_apinis_Interp_solve\<close>, not plain join: \<open>int_dom\<close>'s
  \<open>int_ivl\<close> component has the same unbounded integer bound Interval's own carrier does, so a
  loop-carried local value still needs Apinis warrowing for termination, exactly the reason
  Interval's own production route (\<open>analyse_interval_dg_for\<close>) already made this choice.
  \<^theory>\<open>Voblint_Analysis.Int_Warrowing\<close>'s \<open>bounded_warrowing\<close> instance for \<open>int_dom\<close> is what
  makes the local unknown's type admit this solver at all.

  \<open>G\<close> stays diagonal at \<open>int_dom exec_dg_st lifted\<close>, matching what \<^const>\<open>dg_gen_of\<close> needs;
  its content is never read, since every field of \<^const>\<open>base_dg_spec_st_for_lifted\<close> threads
  its incoming \<open>g\<close> through unchanged.
\<close>

text \<open>
  \<open>int_tf_for\<close>/\<open>int_tf_st_for\<close>/\<open>int_dom_enter_st_for\<close> are production-selection
  dispatchers only: each mode case is a bare reference to its own
  \<^theory>\<open>Voblint_Analysis.Int_Transfer\<close>/\<open>Int_Exec\<close> bundle, so none of the three
  bundles' distinct capabilities collapse into these. In particular they do not
  imply a uniform \<open>apply_tf\<close> monotonicity fact across modes -- \<open>Refine_Fixpoint\<close>
  still has none (\<^theory>\<open>Voblint_Analysis.Int_Transfer\<close>'s own header explains why),
  and nothing below requires one; the production soundness route (the
  \<open>base_dg_exec_analysis\<close> locale, one session downstream) never cites transfer
  monotonicity.
\<close>

fun int_tf_for :: "refine_mode \<Rightarrow> (vname \<Rightarrow> bool) \<Rightarrow> int_dom domain_transfer" where
  "int_tf_for Refine_Never gs = int_tf_never_for gs"
| "int_tf_for Refine_Once gs = int_tf_once_for gs"
| "int_tf_for Refine_Fixpoint gs = int_tf_fixpoint_for gs"

fun int_tf_st_for :: "refine_mode \<Rightarrow> (vname \<Rightarrow> bool) \<Rightarrow> edge_action \<Rightarrow>
    int_dom resolved_st_q \<Rightarrow> int_dom resolved_st_q" where
  "int_tf_st_for Refine_Never gs = int_tf_st_never_for gs"
| "int_tf_st_for Refine_Once gs = int_tf_st_once_for gs"
| "int_tf_st_for Refine_Fixpoint gs = int_tf_st_fixpoint_for gs"

fun int_dom_enter_st_for ::
    "refine_mode \<Rightarrow> (vname \<Rightarrow> bool) \<Rightarrow> vname list \<Rightarrow> exp list \<Rightarrow>
      int_dom resolved_st_q \<Rightarrow> int_dom resolved_st_q" where
  "int_dom_enter_st_for Refine_Never gs = int_dom_enter_never_st_for gs"
| "int_dom_enter_st_for Refine_Once gs = int_dom_enter_once_st_for gs"
| "int_dom_enter_st_for Refine_Fixpoint gs = int_dom_enter_fixpoint_st_for gs"

definition analyse_int_dg_eqs_for ::
  "refine_mode \<Rightarrow> (int_dom exec_dg_st \<Rightarrow> bool) \<Rightarrow> (vname \<Rightarrow> bool) \<Rightarrow> imp_prog \<Rightarrow>
     pp \<times> unit \<Rightarrow> (pp \<times> unit, unit, (int_dom exec_dg_st lifted, int_dom exec_dg_st lifted) dg_state) strategy_tree" where
  "analyse_int_dg_eqs_for mode is_bot_pred gs p =
     dg_gen_of
       (base_dg_spec_st_for_lifted gs is_bot_pred (int_tf_st_for mode gs) (int_dom_enter_st_for mode gs))
       (prog_cfg p) bot (Lifted cinit_int_dom_st) (Lifted cinit_int_dom_st)"

definition analyse_int_dg_for :: "refine_mode \<Rightarrow> (int_dom exec_dg_st \<Rightarrow> bool) \<Rightarrow> (vname \<Rightarrow> bool) \<Rightarrow> imp_prog \<Rightarrow>
    (pp \<times> unit) set \<times> (pp \<times> unit + unit \<Rightarrow> (int_dom exec_dg_st lifted, int_dom exec_dg_st lifted) dg_state)" where
  "analyse_int_dg_for mode is_bot_pred gs p =
     TD_side_warrowing_apinis_Interp_solve (analyse_int_dg_eqs_for mode is_bot_pred gs p)
       (cfg_exit (prog_cfg p), ())"

text \<open>
  \<open>analyse_int_dg_env_for\<close> reads the local unknown at \<open>v\<close> (\<open>Inl (v, ())\<close>) straight back
  through \<^const>\<open>fun_of_exec_dg_st_for\<close>/\<^const>\<open>map_lift\<close>, mirroring
  \<open>analyse_interval_dg_env_for\<close> exactly: the whole abstract state already lives there, so
  there is no locals-from-\<open>D\<close>/globals-from-\<open>G\<close> reconstruction to perform. A genuinely
  unreachable local unknown (\<open>Bot\<close>) concretizes to \<open>bot\<close>, matching \<^const>\<open>gamma_state_lift\<close>'s
  own \<open>Bot\<close> case.

  The \<open>[code]\<close> rewrite below is point-free in \<open>v\<close>, the same single-solve-per-report fix
  \<open>analyse_interval_dg_env_for_code\<close> uses: \<^const>\<open>analyse_int_dg_for\<close> is solved exactly
  once per partial application to \<open>is_bot_pred gs p\<close>, reused for every \<open>v\<close> queried afterward
  against the resulting closure.
\<close>

definition analyse_int_dg_env_for ::
    "refine_mode \<Rightarrow> (int_dom exec_dg_st \<Rightarrow> bool) \<Rightarrow> (vname \<Rightarrow> bool) \<Rightarrow> imp_prog \<Rightarrow> pp \<Rightarrow> int_dom abs_state" where
  "analyse_int_dg_env_for mode is_bot_pred gs p v =
     (case map_lift (fun_of_exec_dg_st_for gs) (locals (snd (analyse_int_dg_for mode is_bot_pred gs p) (Inl (v, ()))))
      of Bot \<Rightarrow> bot | Lifted s \<Rightarrow> s)"

declare analyse_int_dg_env_for_def [code del]

lemma analyse_int_dg_env_for_code [code]:
  "analyse_int_dg_env_for mode is_bot_pred gs p =
     (let sol = snd (analyse_int_dg_for mode is_bot_pred gs p)
      in (\<lambda>v. case map_lift (fun_of_exec_dg_st_for gs) (locals (sol (Inl (v, ()))))
              of Bot \<Rightarrow> bot | Lifted s \<Rightarrow> s))"
  unfolding analyse_int_dg_env_for_def Let_def by (rule refl)

text \<open>
  Convenience instances at \<^const>\<open>declared_global\<close> \<open>p\<close>, matching \<open>analyse_interval_dg_eqs\<close>/
  \<open>analyse_interval_dg\<close>/\<open>analyse_interval_dg_env\<close>'s shape. \<open>is_bot_pred\<close> is fixed here
  to \<^const>\<open>resolved_st_q_is_bot_for\<close> at \<open>p\<close>'s own \<^const>\<open>declared_global_vars\<close>, exact for
  \<^const>\<open>is_bot_state\<close> by @{thm resolved_st_q_is_bot_for_iff} (@{thm declared_global_iff}).
\<close>

definition analyse_int_dg_eqs :: "refine_mode \<Rightarrow> imp_prog \<Rightarrow>
    pp \<times> unit \<Rightarrow> (pp \<times> unit, unit, (int_dom exec_dg_st lifted, int_dom exec_dg_st lifted) dg_state) strategy_tree" where
  "analyse_int_dg_eqs mode p =
     analyse_int_dg_eqs_for mode (resolved_st_q_is_bot_for (declared_global_vars p)) (declared_global p) p"

definition analyse_int_dg :: "refine_mode \<Rightarrow> imp_prog \<Rightarrow>
    (pp \<times> unit) set \<times> (pp \<times> unit + unit \<Rightarrow> (int_dom exec_dg_st lifted, int_dom exec_dg_st lifted) dg_state)" where
  "analyse_int_dg mode p =
     analyse_int_dg_for mode (resolved_st_q_is_bot_for (declared_global_vars p)) (declared_global p) p"

definition analyse_int_dg_env :: "refine_mode \<Rightarrow> imp_prog \<Rightarrow> pp \<Rightarrow> int_dom abs_state" where
  "analyse_int_dg_env mode p =
     analyse_int_dg_env_for mode (resolved_st_q_is_bot_for (declared_global_vars p)) (declared_global p) p"

text \<open>
  Solver-choice variants: always-join and per-origin update rules, mirroring
  \<open>Interval_Exec_Sound.analyse_interval_dg_join_for\<close>/\<open>_per_origin_for\<close> exactly ---
  solving the same \<^const>\<open>analyse_int_dg_eqs_for\<close> equation system (\<open>mode\<close> included)
  under \<^const>\<open>TD_side_always_join_Interp_solve\<close>/\<open>TD_side_per_origin_Interp_solve\<close>
  instead of \<^const>\<open>TD_side_warrowing_apinis_Interp_solve\<close>, so the \<open>Analyse_Dispatch\<close>
  runtime dispatcher (Examples session, downstream) can compare update rules on the
  identical equation system, the same role Interval's own join/per-origin variants
  already play there.
\<close>

definition analyse_int_dg_join_for :: "refine_mode \<Rightarrow> (int_dom exec_dg_st \<Rightarrow> bool) \<Rightarrow> (vname \<Rightarrow> bool) \<Rightarrow> imp_prog \<Rightarrow>
    (pp \<times> unit) set \<times> (pp \<times> unit + unit \<Rightarrow> (int_dom exec_dg_st lifted, int_dom exec_dg_st lifted) dg_state)" where
  "analyse_int_dg_join_for mode is_bot_pred gs p =
     TD_side_always_join_Interp_solve (analyse_int_dg_eqs_for mode is_bot_pred gs p)
       (cfg_exit (prog_cfg p), ())"

definition analyse_int_dg_join_env_for ::
    "refine_mode \<Rightarrow> (int_dom exec_dg_st \<Rightarrow> bool) \<Rightarrow> (vname \<Rightarrow> bool) \<Rightarrow> imp_prog \<Rightarrow> pp \<Rightarrow> int_dom abs_state" where
  "analyse_int_dg_join_env_for mode is_bot_pred gs p v =
     (case map_lift (fun_of_exec_dg_st_for gs) (locals (snd (analyse_int_dg_join_for mode is_bot_pred gs p) (Inl (v, ()))))
      of Bot \<Rightarrow> bot | Lifted s \<Rightarrow> s)"

declare analyse_int_dg_join_env_for_def [code del]

lemma analyse_int_dg_join_env_for_code [code]:
  "analyse_int_dg_join_env_for mode is_bot_pred gs p =
     (let sol = snd (analyse_int_dg_join_for mode is_bot_pred gs p)
      in (\<lambda>v. case map_lift (fun_of_exec_dg_st_for gs) (locals (sol (Inl (v, ()))))
              of Bot \<Rightarrow> bot | Lifted s \<Rightarrow> s))"
  unfolding analyse_int_dg_join_env_for_def Let_def by (rule refl)

definition analyse_int_dg_per_origin_for :: "refine_mode \<Rightarrow> (int_dom exec_dg_st \<Rightarrow> bool) \<Rightarrow> (vname \<Rightarrow> bool) \<Rightarrow> imp_prog \<Rightarrow>
    (pp \<times> unit) set \<times> (pp \<times> unit + unit \<Rightarrow> (int_dom exec_dg_st lifted, int_dom exec_dg_st lifted) dg_state)" where
  "analyse_int_dg_per_origin_for mode is_bot_pred gs p =
     TD_side_per_origin_Interp_solve (analyse_int_dg_eqs_for mode is_bot_pred gs p)
       (cfg_exit (prog_cfg p), ())"

definition analyse_int_dg_per_origin_env_for ::
    "refine_mode \<Rightarrow> (int_dom exec_dg_st \<Rightarrow> bool) \<Rightarrow> (vname \<Rightarrow> bool) \<Rightarrow> imp_prog \<Rightarrow> pp \<Rightarrow> int_dom abs_state" where
  "analyse_int_dg_per_origin_env_for mode is_bot_pred gs p v =
     (case map_lift (fun_of_exec_dg_st_for gs) (locals (snd (analyse_int_dg_per_origin_for mode is_bot_pred gs p) (Inl (v, ()))))
      of Bot \<Rightarrow> bot | Lifted s \<Rightarrow> s)"

declare analyse_int_dg_per_origin_env_for_def [code del]

lemma analyse_int_dg_per_origin_env_for_code [code]:
  "analyse_int_dg_per_origin_env_for mode is_bot_pred gs p =
     (let sol = snd (analyse_int_dg_per_origin_for mode is_bot_pred gs p)
      in (\<lambda>v. case map_lift (fun_of_exec_dg_st_for gs) (locals (sol (Inl (v, ()))))
              of Bot \<Rightarrow> bot | Lifted s \<Rightarrow> s))"
  unfolding analyse_int_dg_per_origin_env_for_def Let_def by (rule refl)

end
