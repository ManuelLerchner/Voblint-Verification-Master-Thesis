theory Int_Solver_Analyses
  imports Int_Analyses
begin

chapter \<open>The same Int configurations, at the alternative solver disciplines\<close>

text \<open>
  Which solver runs an equation system is independent of which context policy
  generated it. \<^theory>\<open>Voblint_Analysis.Int_Analyses\<close> fixes the three context
  policies at the default always-join solver; this theory re-runs those same
  equation systems under the PerOrigin, Apinis-warrowing and
  warrowing-per-origin disciplines, and publishes the result and report tables
  each one yields.

  The \<^typ>\<open>refine_mode\<close> parameter is a different axis again, and stays where it
  is: it selects how far the product domain refines its components, which every
  configuration here carries regardless of solver. Nothing in this theory is a
  new analysis, and no fact about the product domain appears.
\<close>

section \<open>PerOrigin solver instantiation, at the same routed unit-context spec\<close>

text \<open>
  Mirrors the always-join instantiation above (\<open>int_conf_eqs\<close>/\<open>int_conf_sol\<close>/\<open>int_conf_terminates\<close>)
  under \<^const>\<open>TD_side_per_origin_Interp_solve\<close> instead, solving the exact same
  \<open>int_conf_eqs\<close> equation system -- mirroring how Int's own Base family
  (\<^theory>\<open>Voblint_Analysis.Int_Exec_Sound\<close>) already solves \<open>analyse_int_dg_eqs_for\<close>
  under three interchangeable update rules, orthogonally to the \<open>refine_mode\<close> axis
  threaded through \<open>mode\<close>. Genuinely sound: \<^locale>\<open>TD_side_upd_rule\<close>'s
  \<open>solve_dom\<close>/\<open>partial_post_solution\<close> are locale-generic over the update rule, so
  \<open>TD_side_per_origin_Interp\<close>'s own \<open>partial_post_solution\<close> instance discharges the same
  obligation \<open>TD_side_always_join_Interp\<close>'s \<open>partial_post_solution\<close> did above, with no
  extra premises.
\<close>

definition int_conf_sol_per_origin ::
    "refine_mode \<Rightarrow> (int_dom exec_dg_st \<Rightarrow> bool) \<Rightarrow> (vname \<Rightarrow> bool) \<Rightarrow> proc_table \<Rightarrow> pname list \<Rightarrow> (pp \<times> unit) set \<times> (pp \<times> unit + (unit, unit) routed_gk \<Rightarrow> (int_dom exec_dg_st lifted, int_dom exec_dg_st lifted) dg_state)" where
  "int_conf_sol_per_origin mode empty_pred gs Pi ps =
     TD_side_per_origin_Interp_solve (int_conf_eqs mode empty_pred gs Pi ps)
       (cfg_exit (compile_prog Pi ps), ())"

definition int_conf_terminates_per_origin ::
    "refine_mode \<Rightarrow> (int_dom exec_dg_st \<Rightarrow> bool) \<Rightarrow> (vname \<Rightarrow> bool) \<Rightarrow> proc_table \<Rightarrow> pname list \<Rightarrow> bool" where
  "int_conf_terminates_per_origin mode empty_pred gs Pi ps =
     TD_side_per_origin_Interp.solve_dom TYPE((unit, unit) routed_gk) TYPE((int_dom exec_dg_st lifted, int_dom exec_dg_st lifted) dg_state)
       (int_conf_eqs mode empty_pred gs Pi ps) (cfg_exit (compile_prog Pi ps), ())"

lemma int_conf_terminates_per_origin_via_solve_c:
  assumes "TD_side_per_origin_Interp_solve_c (int_conf_eqs mode empty_pred gs Pi ps)
             (cfg_exit (compile_prog Pi ps), ()) \<noteq> None"
  shows "int_conf_terminates_per_origin mode empty_pred gs Pi ps"
  unfolding int_conf_terminates_per_origin_def
  by (rule TD_side_per_origin_Interp.solve_dom_of_solve_c[OF assms])

subsection \<open>The PerOrigin instance\<close>

lemma int_conf_per_origin_pp_st:
  "int_conf_terminates_per_origin mode empty_pred gs Pi ps
     \<Longrightarrow> part_post_solution (int_conf_eqs mode empty_pred gs Pi ps)
           (cfg_exit (compile_prog Pi ps), ())
           (snd (int_conf_sol_per_origin mode empty_pred gs Pi ps))
           (fst (int_conf_sol_per_origin mode empty_pred gs Pi ps))"
  unfolding int_conf_sol_per_origin_def int_conf_terminates_per_origin_def
  by (rule TD_side_per_origin_Interp.partial_post_solution[OF _ surjective_pairing])

global_interpretation int_conf_po: int_conf_solved int_conf_sol_per_origin int_conf_terminates_per_origin
  by unfold_locales (rule int_conf_per_origin_pp_st)

lemmas int_conf_result_node_sound_per_origin = int_conf_po.int_conf_result_node_sound
lemmas int_conf_analyse_result_eq_per_origin = int_conf_po.int_conf_analyse_result_eq
lemmas int_conf_cinit_le_cinit_int_dom_st_per_origin = int_conf_po.int_conf_cinit_le_cinit_int_dom_st
lemmas int_conf_activation_collect_sound_per_origin = int_conf_po.int_conf_activation_collect_sound
lemmas int_conf_analyse_report_ctx_proved_sound_per_origin = int_conf_po.int_conf_analyse_report_ctx_proved_sound
lemmas int_conf_analyse_report_ctx_refuted_sound_per_origin = int_conf_po.int_conf_analyse_report_ctx_refuted_sound
lemmas int_conf_analyse_result_per_origin_def = int_conf_po.int_conf_analyse_result_def
lemmas int_conf_analyse_report_ctx_per_origin_def = int_conf_po.int_conf_analyse_report_ctx_def


section \<open>Apinis warrowing solver instantiation, at the same routed unit-context spec\<close>

text \<open>
  Int's default solver: mirrors the always-join instantiation above under
  \<^const>\<open>TD_side_warrowing_apinis_Interp_solve\<close> instead, solving the exact same
  \<open>int_conf_eqs\<close> equation system -- exactly as Interval's own entry-state contextual mode
  already does. No \<open>int_dom\<close>-specific widen/narrow bridging fact is needed: those facts
  are needed only by the Base family's separate \<open>restrict_global_resolved_q\<close>
  bookkeeping for its flow-insensitive global slot
  (\<^theory>\<open>Voblint_Analysis.Int_Exec_Sound\<close>), which the routed spine's keyed-seed
  \<open>Analysis_Global\<close>/\<open>Activation_Seed\<close> globals replace outright. \<^locale>\<open>TD_side_upd_rule\<close>'s
  \<open>solve_dom\<close>/\<open>partial_post_solution\<close> being locale-generic over the update rule (as
  for PerOrigin above) is exactly what makes this a mechanical solver-call swap here too.
\<close>

definition int_conf_sol_warrow ::
    "refine_mode \<Rightarrow> (int_dom exec_dg_st \<Rightarrow> bool) \<Rightarrow> (vname \<Rightarrow> bool) \<Rightarrow> proc_table \<Rightarrow> pname list \<Rightarrow> (pp \<times> unit) set \<times> (pp \<times> unit + (unit, unit) routed_gk \<Rightarrow> (int_dom exec_dg_st lifted, int_dom exec_dg_st lifted) dg_state)" where
  "int_conf_sol_warrow mode empty_pred gs Pi ps =
     TD_side_warrowing_apinis_Interp_solve (int_conf_eqs mode empty_pred gs Pi ps)
       (cfg_exit (compile_prog Pi ps), ())"

definition int_conf_terminates_warrow ::
    "refine_mode \<Rightarrow> (int_dom exec_dg_st \<Rightarrow> bool) \<Rightarrow> (vname \<Rightarrow> bool) \<Rightarrow> proc_table \<Rightarrow> pname list \<Rightarrow> bool" where
  "int_conf_terminates_warrow mode empty_pred gs Pi ps =
     TD_side_warrowing_apinis_Interp.solve_dom TYPE((unit, unit) routed_gk) TYPE((int_dom exec_dg_st lifted, int_dom exec_dg_st lifted) dg_state)
       (int_conf_eqs mode empty_pred gs Pi ps) (cfg_exit (compile_prog Pi ps), ())"

lemma int_conf_terminates_warrow_via_solve_c:
  assumes "TD_side_warrowing_apinis_Interp_solve_c (int_conf_eqs mode empty_pred gs Pi ps)
             (cfg_exit (compile_prog Pi ps), ()) \<noteq> None"
  shows "int_conf_terminates_warrow mode empty_pred gs Pi ps"
  unfolding int_conf_terminates_warrow_def
  by (rule TD_side_warrowing_apinis_Interp.solve_dom_of_solve_c[OF assms])

subsection \<open>The Apinis warrowing instance\<close>

lemma int_conf_warrow_pp_st:
  "int_conf_terminates_warrow mode empty_pred gs Pi ps
     \<Longrightarrow> part_post_solution (int_conf_eqs mode empty_pred gs Pi ps)
           (cfg_exit (compile_prog Pi ps), ())
           (snd (int_conf_sol_warrow mode empty_pred gs Pi ps))
           (fst (int_conf_sol_warrow mode empty_pred gs Pi ps))"
  unfolding int_conf_sol_warrow_def int_conf_terminates_warrow_def
  by (rule TD_side_warrowing_apinis_Interp.partial_post_solution[OF _ surjective_pairing])

global_interpretation int_conf_wa: int_conf_solved int_conf_sol_warrow int_conf_terminates_warrow
  by unfold_locales (rule int_conf_warrow_pp_st)

lemmas int_conf_result_node_sound_warrow = int_conf_wa.int_conf_result_node_sound
lemmas int_conf_analyse_result_eq_warrow = int_conf_wa.int_conf_analyse_result_eq
lemmas int_conf_cinit_le_cinit_int_dom_st_warrow = int_conf_wa.int_conf_cinit_le_cinit_int_dom_st
lemmas int_conf_activation_collect_sound_warrow = int_conf_wa.int_conf_activation_collect_sound
lemmas int_conf_analyse_report_ctx_proved_sound_warrow = int_conf_wa.int_conf_analyse_report_ctx_proved_sound
lemmas int_conf_analyse_report_ctx_refuted_sound_warrow = int_conf_wa.int_conf_analyse_report_ctx_refuted_sound
lemmas int_conf_analyse_result_warrow_def = int_conf_wa.int_conf_analyse_result_def
lemmas int_conf_analyse_report_ctx_warrow_def = int_conf_wa.int_conf_analyse_report_ctx_def

section \<open>Warrowing-per-origin solver instantiation\<close>

text \<open>
  The fourth update rule.  \<^const>\<open>update_global_warrowing_per_origin\<close> widens each origin's
  own contribution and joins afterwards, where \<^const>\<open>update_global_warrowing_apinis\<close>
  widens the value already joined across every origin.
\<close>

definition int_conf_sol_wpo ::
    "refine_mode \<Rightarrow> (int_dom exec_dg_st \<Rightarrow> bool) \<Rightarrow> (vname \<Rightarrow> bool) \<Rightarrow> proc_table \<Rightarrow> pname list \<Rightarrow> (pp \<times> unit) set \<times> (pp \<times> unit + (unit, unit) routed_gk \<Rightarrow> (int_dom exec_dg_st lifted, int_dom exec_dg_st lifted) dg_state)" where
  "int_conf_sol_wpo mode empty_pred gs Pi ps =
     TD_side_warrowing_per_origin_Interp_solve (int_conf_eqs mode empty_pred gs Pi ps)
       (cfg_exit (compile_prog Pi ps), ())"

definition int_conf_terminates_wpo ::
    "refine_mode \<Rightarrow> (int_dom exec_dg_st \<Rightarrow> bool) \<Rightarrow> (vname \<Rightarrow> bool) \<Rightarrow> proc_table \<Rightarrow> pname list \<Rightarrow> bool" where
  "int_conf_terminates_wpo mode empty_pred gs Pi ps =
     TD_side_warrowing_per_origin_Interp.solve_dom TYPE((unit, unit) routed_gk)
       TYPE((int_dom exec_dg_st lifted, int_dom exec_dg_st lifted) dg_state)
       (int_conf_eqs mode empty_pred gs Pi ps) (cfg_exit (compile_prog Pi ps), ())"

lemma int_conf_terminates_wpo_via_solve_c:
  assumes "TD_side_warrowing_per_origin_Interp_solve_c (int_conf_eqs mode empty_pred gs Pi ps)
             (cfg_exit (compile_prog Pi ps), ()) \<noteq> None"
  shows "int_conf_terminates_wpo mode empty_pred gs Pi ps"
  unfolding int_conf_terminates_wpo_def
  by (rule TD_side_warrowing_per_origin_Interp.solve_dom_of_solve_c[OF assms])

lemma int_conf_wpo_pp_st:
  "int_conf_terminates_wpo mode empty_pred gs Pi ps
     \<Longrightarrow> part_post_solution (int_conf_eqs mode empty_pred gs Pi ps)
           (cfg_exit (compile_prog Pi ps), ())
           (snd (int_conf_sol_wpo mode empty_pred gs Pi ps))
           (fst (int_conf_sol_wpo mode empty_pred gs Pi ps))"
  unfolding int_conf_sol_wpo_def int_conf_terminates_wpo_def
  by (rule TD_side_warrowing_per_origin_Interp.partial_post_solution[OF _ surjective_pairing])

global_interpretation int_conf_wpo: int_conf_solved int_conf_sol_wpo int_conf_terminates_wpo
  by unfold_locales (rule int_conf_wpo_pp_st)

lemmas int_conf_result_node_sound_wpo = int_conf_wpo.int_conf_result_node_sound
lemmas int_conf_analyse_result_eq_wpo = int_conf_wpo.int_conf_analyse_result_eq
lemmas int_conf_cinit_le_cinit_int_dom_st_wpo = int_conf_wpo.int_conf_cinit_le_cinit_int_dom_st
lemmas int_conf_activation_collect_sound_wpo = int_conf_wpo.int_conf_activation_collect_sound
lemmas int_conf_analyse_report_ctx_proved_sound_wpo = int_conf_wpo.int_conf_analyse_report_ctx_proved_sound
lemmas int_conf_analyse_report_ctx_refuted_sound_wpo = int_conf_wpo.int_conf_analyse_report_ctx_refuted_sound
lemmas int_conf_analyse_result_wpo_def = int_conf_wpo.int_conf_analyse_result_def
lemmas int_conf_analyse_report_ctx_wpo_def = int_conf_wpo.int_conf_analyse_report_ctx_def


subsection \<open>Solved-result tables: PerOrigin and Apinis warrowing siblings\<close>

text \<open>
  Mirror \<open>int_conf_sol_prog\<close>/\<open>int_conf_terminates_prog\<close>/\<open>analyse_int_ctx_result_for\<close> (the Join
  table above) at the PerOrigin and Apinis warrowing solvers, reading the same
  \<open>int_conf_eqs_prog\<close> equation system: the three-solver orthogonality Int's Base family
  already has (\<open>analyse_int_dg_for\<close>/\<open>_join_for\<close>/\<open>_per_origin_for\<close>,
  \<^theory>\<open>Voblint_Analysis.Int_Exec_Sound\<close>) now also holds at the routed spine, orthogonally
  to the \<open>refine_mode\<close> axis.
\<close>

definition int_conf_sol_prog_per_origin ::
    "refine_mode \<Rightarrow> (vname \<Rightarrow> bool) \<Rightarrow> imp_prog
       \<Rightarrow> (pp \<times> unit) set \<times> (pp \<times> unit + (unit, unit) routed_gk \<Rightarrow> (int_dom exec_dg_st lifted, int_dom exec_dg_st lifted) dg_state)" where
  "int_conf_sol_prog_per_origin mode gs p =
     TD_side_per_origin_Interp_solve (int_conf_eqs_prog mode gs p) (cfg_exit (prog_cfg p), ())"

definition int_conf_terminates_prog_per_origin :: "refine_mode \<Rightarrow> (vname \<Rightarrow> bool) \<Rightarrow> imp_prog \<Rightarrow> bool" where
  "int_conf_terminates_prog_per_origin mode gs p =
     int_conf_terminates_per_origin mode (resolved_st_q_is_bot_for (declared_global_vars p))
       gs (prog_table p) (prog_procs p)"

lemma int_conf_terminates_prog_per_origin_via_solve_c:
  assumes "TD_side_per_origin_Interp_solve_c
             (int_conf_eqs mode (resolved_st_q_is_bot_for (declared_global_vars p))
                gs (prog_table p) (prog_procs p))
             (cfg_exit (compile_prog (prog_table p) (prog_procs p)), ()) \<noteq> None"
  shows "int_conf_terminates_prog_per_origin mode gs p"
  unfolding int_conf_terminates_prog_per_origin_def
  using assms by (rule int_conf_terminates_per_origin_via_solve_c)

definition analyse_int_ctx_result_per_origin_for ::
    "refine_mode \<Rightarrow> (vname \<Rightarrow> bool) \<Rightarrow> imp_prog \<Rightarrow> (unit, int_dom abs_state) analysis_result" where
  "analyse_int_ctx_result_per_origin_for mode gs p =
     Analysis_Result
       (fst (int_conf_sol_prog_per_origin mode gs p))
       (\<lambda>v ctx. normalize_point gs
                  (canonicalize_lift (resolved_st_q_is_bot_for (declared_global_vars p))
                    (locals (snd (int_conf_sol_prog_per_origin mode gs p) (Inl (v, ctx))))))"

declare analyse_int_ctx_result_per_origin_for_def [code del]

lemma analyse_int_ctx_result_per_origin_for_code [code]:
  "analyse_int_ctx_result_per_origin_for mode gs p =
     (let sol = int_conf_sol_prog_per_origin mode gs p; gl = declared_global_vars p
      in Analysis_Result (fst sol)
           (\<lambda>v ctx. normalize_point gs
                      (canonicalize_lift (resolved_st_q_is_bot_for gl)
                        (locals (snd sol (Inl (v, ctx)))))))"
  unfolding analyse_int_ctx_result_per_origin_for_def Let_def by (rule refl)

definition int_conf_sol_prog_warrow ::
    "refine_mode \<Rightarrow> (vname \<Rightarrow> bool) \<Rightarrow> imp_prog
       \<Rightarrow> (pp \<times> unit) set \<times> (pp \<times> unit + (unit, unit) routed_gk \<Rightarrow> (int_dom exec_dg_st lifted, int_dom exec_dg_st lifted) dg_state)" where
  "int_conf_sol_prog_warrow mode gs p =
     TD_side_warrowing_apinis_Interp_solve (int_conf_eqs_prog mode gs p) (cfg_exit (prog_cfg p), ())"

definition int_conf_terminates_prog_warrow :: "refine_mode \<Rightarrow> (vname \<Rightarrow> bool) \<Rightarrow> imp_prog \<Rightarrow> bool" where
  "int_conf_terminates_prog_warrow mode gs p =
     int_conf_terminates_warrow mode (resolved_st_q_is_bot_for (declared_global_vars p))
       gs (prog_table p) (prog_procs p)"

lemma int_conf_terminates_prog_warrow_via_solve_c:
  assumes "TD_side_warrowing_apinis_Interp_solve_c
             (int_conf_eqs mode (resolved_st_q_is_bot_for (declared_global_vars p))
                gs (prog_table p) (prog_procs p))
             (cfg_exit (compile_prog (prog_table p) (prog_procs p)), ()) \<noteq> None"
  shows "int_conf_terminates_prog_warrow mode gs p"
  unfolding int_conf_terminates_prog_warrow_def
  using assms by (rule int_conf_terminates_warrow_via_solve_c)

definition analyse_int_ctx_result_warrow_for ::
    "refine_mode \<Rightarrow> (vname \<Rightarrow> bool) \<Rightarrow> imp_prog \<Rightarrow> (unit, int_dom abs_state) analysis_result" where
  "analyse_int_ctx_result_warrow_for mode gs p =
     Analysis_Result
       (fst (int_conf_sol_prog_warrow mode gs p))
       (\<lambda>v ctx. normalize_point gs
                  (canonicalize_lift (resolved_st_q_is_bot_for (declared_global_vars p))
                    (locals (snd (int_conf_sol_prog_warrow mode gs p) (Inl (v, ctx))))))"

text \<open>\<^const>\<open>ctx_solved_for\<close> at this domain's warrowing solve, with \<^const>\<open>Analysis_Global\<close>
  and \<^const>\<open>Activation_Seed\<close> handed to \<^const>\<open>seed_global_keys\<close> the way \<^const>\<open>routed_entry_seed_tree\<close>
  already takes them. The refinement mode is applied first, leaving the solve in the
  shape \<^const>\<open>ctx_solved_for\<close> takes.\<close>

definition analyse_int_ctx_solved_warrow_for ::
    "refine_mode \<Rightarrow> (vname \<Rightarrow> bool) \<Rightarrow> imp_prog
     \<Rightarrow> (unit, int_dom abs_state) analysis_result
          \<times> (String.literal \<times> int_dom abs_state lifted) list" where
  "analyse_int_ctx_solved_warrow_for mode =
     ctx_solved_for (int_conf_sol_prog_warrow mode) (unit_seed_global_keys (Analysis_Global ()) Activation_Seed)"

lemma fst_analyse_int_ctx_solved_warrow_for:
  "fst (analyse_int_ctx_solved_warrow_for mode gs p)
     = analyse_int_ctx_result_warrow_for mode gs p"
  by (simp add: analyse_int_ctx_solved_warrow_for_def fst_ctx_solved_for
      analyse_int_ctx_result_warrow_for_def Let_def)

declare analyse_int_ctx_result_warrow_for_def [code del]

lemma analyse_int_ctx_result_warrow_for_code [code]:
  "analyse_int_ctx_result_warrow_for mode gs p =
     (let sol = int_conf_sol_prog_warrow mode gs p; gl = declared_global_vars p
      in Analysis_Result (fst sol)
           (\<lambda>v ctx. normalize_point gs
                      (canonicalize_lift (resolved_st_q_is_bot_for gl)
                        (locals (snd sol (Inl (v, ctx)))))))"
  unfolding analyse_int_ctx_result_warrow_for_def Let_def by (rule refl)

subsection \<open>Solved-result table: warrowing per origin\<close>

definition int_conf_sol_prog_wpo ::
    "refine_mode \<Rightarrow> (vname \<Rightarrow> bool) \<Rightarrow> imp_prog
       \<Rightarrow> (pp \<times> unit) set \<times> (pp \<times> unit + (unit, unit) routed_gk \<Rightarrow> (int_dom exec_dg_st lifted, int_dom exec_dg_st lifted) dg_state)" where
  "int_conf_sol_prog_wpo mode gs p =
     TD_side_warrowing_per_origin_Interp_solve (int_conf_eqs_prog mode gs p) (cfg_exit (prog_cfg p), ())"

definition int_conf_terminates_prog_wpo :: "refine_mode \<Rightarrow> (vname \<Rightarrow> bool) \<Rightarrow> imp_prog \<Rightarrow> bool" where
  "int_conf_terminates_prog_wpo mode gs p =
     int_conf_terminates_wpo mode (resolved_st_q_is_bot_for (declared_global_vars p))
       gs (prog_table p) (prog_procs p)"

lemma int_conf_terminates_prog_wpo_via_solve_c:
  assumes "TD_side_warrowing_per_origin_Interp_solve_c
             (int_conf_eqs mode (resolved_st_q_is_bot_for (declared_global_vars p))
                gs (prog_table p) (prog_procs p))
             (cfg_exit (compile_prog (prog_table p) (prog_procs p)), ()) \<noteq> None"
  shows "int_conf_terminates_prog_wpo mode gs p"
  unfolding int_conf_terminates_prog_wpo_def
  using assms by (rule int_conf_terminates_wpo_via_solve_c)

definition analyse_int_ctx_result_wpo_for ::
    "refine_mode \<Rightarrow> (vname \<Rightarrow> bool) \<Rightarrow> imp_prog \<Rightarrow> (unit, int_dom abs_state) analysis_result" where
  "analyse_int_ctx_result_wpo_for mode gs p =
     Analysis_Result
       (fst (int_conf_sol_prog_wpo mode gs p))
       (\<lambda>v ctx. normalize_point gs
                  (canonicalize_lift (resolved_st_q_is_bot_for (declared_global_vars p))
                    (locals (snd (int_conf_sol_prog_wpo mode gs p) (Inl (v, ctx))))))"

declare analyse_int_ctx_result_wpo_for_def [code del]

lemma analyse_int_ctx_result_wpo_for_code [code]:
  "analyse_int_ctx_result_wpo_for mode gs p =
     (let sol = int_conf_sol_prog_wpo mode gs p; gl = declared_global_vars p
      in Analysis_Result (fst sol)
           (\<lambda>v ctx. normalize_point gs
                      (canonicalize_lift (resolved_st_q_is_bot_for gl)
                        (locals (snd sol (Inl (v, ctx)))))))"
  unfolding analyse_int_ctx_result_wpo_for_def Let_def by (rule refl)


subsection \<open>The certified executable post-solution under warrowing\<close>

context
  fixes mode :: refine_mode and gs :: "vname \<Rightarrow> bool" and empty_pred :: "int_dom exec_dg_st \<Rightarrow> bool"
    and Pi :: proc_table and ps :: "pname list" and k :: nat
  assumes solves: "ics_terminates_warrow k mode gs empty_pred Pi ps"
    and exact: "\<And>s. empty_pred s = is_empty_state (fun_of_resolved_st_q_for gs s)"
begin

lemma ics_solve_dom_warrow:
  "TD_side_warrowing_apinis_Interp.solve_dom TYPE(call_string_gk) TYPE((int_dom exec_dg_st lifted, int_dom exec_dg_st lifted) dg_state)
     (ics_eqs k mode gs empty_pred Pi ps) (cfg_exit (compile_prog Pi ps), [])"
  using solves[unfolded ics_terminates_warrow_def] .

lemma ics_pp_st_warrow:
  "part_post_solution (ics_eqs k mode gs empty_pred Pi ps) (cfg_exit (compile_prog Pi ps), [])
     (snd (ics_sol_warrow k mode gs empty_pred Pi ps)) (fst (ics_sol_warrow k mode gs empty_pred Pi ps))"
  using TD_side_warrowing_apinis_Interp.partial_post_solution
          [OF ics_solve_dom_warrow, of "fst (ics_sol_warrow k mode gs empty_pred Pi ps)"
             "snd (ics_sol_warrow k mode gs empty_pred Pi ps)"]
  unfolding ics_sol_warrow_def by simp

theorem ics_pp_routed_warrow:
  "part_post_solution
     (routed_node_rhs intra_predecessor_addr_list (\<lambda>_. Call_String_Context.Global)
        (cs_route k)
        (\<lambda>ctx' src a. dg_spec_edge_tree (int_dom_spec mode empty_pred gs) a src
           (\<lambda>_. Call_String_Context.Global))
        (routed_call_tree (int_dom_spec mode empty_pred gs) Call_String_Context.Global
           Call_String_Context.Seed (static_resolve (compile_prog Pi ps)) (\<lambda>d. d = Bot))
        (routed_entry_seed_tree Call_String_Context.Seed Call_String_Context.Global)
        (compile_prog Pi ps) Bot (Lifted cinit_int_dom_st) Bot)
     (cfg_exit (compile_prog Pi ps), [])
     (snd (ics_sol_warrow k mode gs empty_pred Pi ps))
     (fst (ics_sol_warrow k mode gs empty_pred Pi ps))"
  using ics_pp_st_warrow unfolding ics_eqs_def int_dom_spec_def by (rule int_cs_pp_st_gen[OF exact])
end

subsection \<open>Result table and report under warrowing\<close>

definition analyse_int_call_string_result_for_warrow ::
    "nat \<Rightarrow> (vname \<Rightarrow> bool) \<Rightarrow> imp_prog \<Rightarrow> (call_string, int_dom abs_state) analysis_result" where
  "analyse_int_call_string_result_for_warrow k gs p =
     Analysis_Result
       (fst (ics_sol_prog_warrow k gs p))
       (\<lambda>v ctx. normalize_point gs
                  (canonicalize_lift (resolved_st_q_is_bot_for (declared_global_vars p))
                    (locals (snd (ics_sol_prog_warrow k gs p) (Inl (v, ctx))))))"

declare analyse_int_call_string_result_for_warrow_def [code del]

lemma analyse_int_call_string_result_for_warrow_code [code]:
  "analyse_int_call_string_result_for_warrow k gs p =
     (let sol = ics_sol_prog_warrow k gs p; gl = declared_global_vars p
      in Analysis_Result (fst sol)
           (\<lambda>v ctx. normalize_point gs
                      (canonicalize_lift (resolved_st_q_is_bot_for gl)
                        (locals (snd sol (Inl (v, ctx)))))))"
  unfolding analyse_int_call_string_result_for_warrow_def Let_def by (rule refl)

definition analyse_int_call_string_result_warrow ::
    "nat \<Rightarrow> imp_prog \<Rightarrow> (call_string, int_dom abs_state) analysis_result" where
  "analyse_int_call_string_result_warrow k p =
     analyse_int_call_string_result_for_warrow k (declared_global p) p"

definition ics_verdict_report_prog_warrow ::
    "nat \<Rightarrow> imp_prog \<Rightarrow> (pp \<times> exp \<times> contextual_verdict) list" where
  "ics_verdict_report_prog_warrow k p =
     classify_checks_verdicts (prog_cfg p)
       (analyse_int_call_string_result_for_warrow k (declared_global p) p)
       int_classify_check"

definition analyse_int_call_string_report_warrow ::
    "nat \<Rightarrow> imp_prog \<Rightarrow> (pp \<times> exp \<times> contextual_verdict) list" where
  "analyse_int_call_string_report_warrow k p = ics_verdict_report_prog_warrow k p"


subsection \<open>The certified executable post-solution under warrowing\<close>

context
  fixes mode :: refine_mode and gs :: "vname \<Rightarrow> bool" and empty_pred :: "int_dom exec_dg_st \<Rightarrow> bool"
    and Pi :: proc_table and ps :: "pname list"
  assumes solves: "int_conf_entry_terminates_warrow mode gs empty_pred Pi ps"
    and exact: "\<And>s. empty_pred s = is_empty_state (fun_of_resolved_st_q_for gs s)"
begin

lemma int_conf_entry_solve_dom_warrow:
  "TD_side_warrowing_apinis_Interp.solve_dom TYPE((unit, int_dom list) routed_gk) TYPE((int_dom exec_dg_st lifted, int_dom exec_dg_st lifted) dg_state)
     (int_conf_entry_eqs mode gs empty_pred Pi ps) (cfg_exit (compile_prog Pi ps), [])"
  using solves[unfolded int_conf_entry_terminates_warrow_def] .

lemma int_conf_entry_pp_st_warrow:
  "part_post_solution (int_conf_entry_eqs mode gs empty_pred Pi ps) (cfg_exit (compile_prog Pi ps), [])
     (snd (int_conf_entry_sol_warrow mode gs empty_pred Pi ps)) (fst (int_conf_entry_sol_warrow mode gs empty_pred Pi ps))"
  using TD_side_warrowing_apinis_Interp.partial_post_solution
          [OF int_conf_entry_solve_dom_warrow, of "fst (int_conf_entry_sol_warrow mode gs empty_pred Pi ps)"
             "snd (int_conf_entry_sol_warrow mode gs empty_pred Pi ps)"]
  unfolding int_conf_entry_sol_warrow_def by simp

theorem int_conf_entry_pp_routed_warrow:
  "part_post_solution
     (routed_node_rhs intra_predecessor_addr_list (\<lambda>_. Analysis_Global ())
        (int_conf_entry_route_gen mode gs empty_pred)
        (\<lambda>ctx' src a. dg_spec_edge_tree (int_dom_spec mode empty_pred gs) a src (\<lambda>_. Analysis_Global ()))
        (routed_call_tree (int_dom_spec mode empty_pred gs) (Analysis_Global ()) Activation_Seed
           (static_resolve (compile_prog Pi ps)) (\<lambda>d. d = Bot))
        (routed_entry_seed_tree Activation_Seed (Analysis_Global ()))
        (compile_prog Pi ps) Bot (Lifted cinit_int_dom_st) Bot)
     (cfg_exit (compile_prog Pi ps), [])
     (snd (int_conf_entry_sol_warrow mode gs empty_pred Pi ps))
     (fst (int_conf_entry_sol_warrow mode gs empty_pred Pi ps))"
  using int_conf_entry_pp_st_warrow unfolding int_conf_entry_eqs_def int_dom_spec_def
  by (rule int_es_pp_st_gen[OF exact])

end

subsection \<open>Result table and report under warrowing\<close>

definition analyse_int_entry_state_result_for_warrow ::
    "(vname \<Rightarrow> bool) \<Rightarrow> imp_prog \<Rightarrow> (int_dom list, int_dom abs_state) analysis_result" where
  "analyse_int_entry_state_result_for_warrow gs p =
     Analysis_Result
       (fst (int_conf_entry_sol_prog_warrow gs p))
       (\<lambda>v ctx. normalize_point gs
                  (canonicalize_lift (resolved_st_q_is_bot_for (declared_global_vars p))
                    (locals (snd (int_conf_entry_sol_prog_warrow gs p) (Inl (v, ctx))))))"

declare analyse_int_entry_state_result_for_warrow_def [code del]

lemma analyse_int_entry_state_result_for_warrow_code [code]:
  "analyse_int_entry_state_result_for_warrow gs p =
     (let sol = int_conf_entry_sol_prog_warrow gs p; gl = declared_global_vars p
      in Analysis_Result (fst sol)
           (\<lambda>v ctx. normalize_point gs
                      (canonicalize_lift (resolved_st_q_is_bot_for gl)
                        (locals (snd sol (Inl (v, ctx)))))))"
  unfolding analyse_int_entry_state_result_for_warrow_def Let_def by (rule refl)

definition analyse_int_entry_state_result_warrow ::
    "imp_prog \<Rightarrow> (int_dom list, int_dom abs_state) analysis_result" where
  "analyse_int_entry_state_result_warrow p =
     analyse_int_entry_state_result_for_warrow (declared_global p) p"

definition int_conf_entry_verdict_report_prog_warrow ::
    "imp_prog \<Rightarrow> (pp \<times> exp \<times> contextual_verdict) list" where
  "int_conf_entry_verdict_report_prog_warrow p =
     classify_checks_verdicts (prog_cfg p)
       (analyse_int_entry_state_result_for_warrow (declared_global p) p)
       int_classify_check"

definition analyse_int_entry_state_report_warrow ::
    "imp_prog \<Rightarrow> (pp \<times> exp \<times> contextual_verdict) list" where
  "analyse_int_entry_state_report_warrow p = int_conf_entry_verdict_report_prog_warrow p"

end
