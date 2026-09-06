theory Interval_Solver_Analyses
  imports Interval_Analyses
begin

chapter \<open>The same Interval configurations, at the alternative solver disciplines\<close>

text \<open>
  Which solver runs an equation system is independent of which context policy
  generated it. \<^theory>\<open>Voblint_Analysis.Interval_Analyses\<close> fixes the three
  context policies at the default always-join solver; this theory re-runs those
  same equation systems under the PerOrigin, Apinis-warrowing and
  warrowing-per-origin disciplines, and publishes the result and report tables
  each one yields.

  Nothing here is a new analysis. Each block instantiates an already-defined
  equation system at a different solver, discharges that solver's termination
  hypothesis, and reads the solved table back through the same readback the
  default discipline uses. No fact about interval arithmetic appears.
\<close>

section \<open>PerOrigin solver instantiation, at the same routed unit-context spec\<close>

text \<open>
  Mirrors the always-join instantiation above (\<open>interval_conf_eqs\<close>/\<open>interval_conf_sol\<close>/\<open>interval_conf_terminates\<close>)
  under \<^const>\<open>TD_side_per_origin_Interp_solve\<close> instead, solving the exact same
  \<open>interval_conf_eqs\<close> equation system -- mirroring how Interval's own Base family
  (\<^theory>\<open>Voblint_Analysis.Interval_Exec_Sound\<close>) already solves
  \<open>analyse_interval_dg_eqs_for\<close> under three interchangeable update rules. Genuinely
  sound: \<^locale>\<open>TD_side_upd_rule\<close>'s \<open>solve_dom\<close>/\<open>partial_post_solution\<close> are
  locale-generic over the update rule, so \<open>TD_side_per_origin_Interp\<close>'s own
  \<open>partial_post_solution\<close> instance discharges the same obligation \<open>TD_side_always_join_Interp\<close>'s
  \<open>partial_post_solution\<close> did above, with no extra premises.
\<close>

definition interval_conf_sol_per_origin ::
    "(vname \<Rightarrow> bool) \<Rightarrow> (ivl exec_dg_st \<Rightarrow> bool) \<Rightarrow> proc_table \<Rightarrow> pname list \<Rightarrow> (pp \<times> unit) set \<times> (pp \<times> unit + (unit, unit) routed_gk \<Rightarrow> (ivl exec_dg_st lifted, ivl exec_dg_st lifted) dg_state)" where
  "interval_conf_sol_per_origin gs empty_pred Pi ps =
     TD_side_per_origin_Interp_solve (interval_conf_eqs gs empty_pred Pi ps)
       (cfg_exit (compile_prog Pi ps), ())"

definition interval_conf_terminates_per_origin ::
    "(vname \<Rightarrow> bool) \<Rightarrow> (ivl exec_dg_st \<Rightarrow> bool) \<Rightarrow> proc_table \<Rightarrow> pname list \<Rightarrow> bool" where
  "interval_conf_terminates_per_origin gs empty_pred Pi ps =
     TD_side_per_origin_Interp.solve_dom TYPE((unit, unit) routed_gk) TYPE((ivl exec_dg_st lifted, ivl exec_dg_st lifted) dg_state)
       (interval_conf_eqs gs empty_pred Pi ps) (cfg_exit (compile_prog Pi ps), ())"

lemma interval_conf_terminates_per_origin_via_solve_c:
  assumes "TD_side_per_origin_Interp_solve_c (interval_conf_eqs gs empty_pred Pi ps)
             (cfg_exit (compile_prog Pi ps), ()) \<noteq> None"
  shows "interval_conf_terminates_per_origin gs empty_pred Pi ps"
  unfolding interval_conf_terminates_per_origin_def
  by (rule TD_side_per_origin_Interp.solve_dom_of_solve_c[OF assms])

subsection \<open>The PerOrigin instance\<close>

lemma interval_conf_per_origin_pp_st:
  "interval_conf_terminates_per_origin gs empty_pred Pi ps
     \<Longrightarrow> part_post_solution (interval_conf_eqs gs empty_pred Pi ps)
           (cfg_exit (compile_prog Pi ps), ())
           (snd (interval_conf_sol_per_origin gs empty_pred Pi ps))
           (fst (interval_conf_sol_per_origin gs empty_pred Pi ps))"
  unfolding interval_conf_sol_per_origin_def interval_conf_terminates_per_origin_def
  by (rule TD_side_per_origin_Interp.partial_post_solution[OF _ surjective_pairing])

text \<open>Each solver variant discharges \<open>vars_fin\<close> from the same locale-level
  solver invariant, instantiated at its own update rule.\<close>

lemma interval_conf_per_origin_vars_finite:
  assumes "interval_conf_terminates_per_origin gs empty_pred Pi ps"
  shows "finite (fst (interval_conf_sol_per_origin gs empty_pred Pi ps))"
  using TD_side_per_origin_Interp.finite_stabl_solve[
      OF assms[unfolded interval_conf_terminates_per_origin_def]]
  unfolding interval_conf_sol_per_origin_def TD_side_per_origin_Interp_solve_def
  by simp

global_interpretation interval_conf_po: interval_conf_solved interval_conf_sol_per_origin interval_conf_terminates_per_origin
proof (unfold_locales, goal_cases PpSt VarsFin)
  case (PpSt gs empty_pred Pi ps) thus ?case by (rule interval_conf_per_origin_pp_st)
next
  case (VarsFin gs empty_pred Pi ps) thus ?case
    by (rule interval_conf_per_origin_vars_finite)
qed

lemmas interval_conf_result_node_sound_per_origin = interval_conf_po.result_node_sound
lemmas interval_conf_analyse_result_eq_per_origin = interval_conf_po.analyse_result_eq
lemmas interval_conf_cinit_le_cinit_ivl_st_per_origin = interval_conf_po.cinit_le_cinit_ivl_st
lemmas interval_conf_report_ctx_proved_sound_per_origin = interval_conf_po.report_ctx_proved_sound
lemmas interval_conf_report_ctx_refuted_sound_per_origin = interval_conf_po.report_ctx_refuted_sound

section \<open>Apinis warrowing solver instantiation, at the same routed unit-context spec\<close>

text \<open>
  Interval production's default solver: mirrors the always-join instantiation above under
  \<^const>\<open>TD_side_warrowing_apinis_Interp_solve\<close> instead, solving the exact same \<open>interval_conf_eqs\<close>
  equation system -- exactly as Interval's own entry-state contextual mode
  (the entry-state configuration below) already does. That file's own soundness derivation needs
  no separate globally-restricted-slot bookkeeping the way the Base family's flow-insensitive
  global slot once did (\<^theory>\<open>Voblint_Analysis.Interval_Exec_Sound\<close>): the routed spine's
  keyed-seed \<open>Analysis_Global\<close>/\<open>Activation_Seed\<close> globals replace that mechanism outright. \<open>TD_side_upd_rule\<close>'s
  \<open>solve_dom\<close>/\<open>partial_post_solution\<close> being locale-generic over the update rule (as for
  PerOrigin above) is exactly what makes this a mechanical solver-call swap here too.
\<close>

definition interval_conf_sol_warrow ::
    "(vname \<Rightarrow> bool) \<Rightarrow> (ivl exec_dg_st \<Rightarrow> bool) \<Rightarrow> proc_table \<Rightarrow> pname list \<Rightarrow> (pp \<times> unit) set \<times> (pp \<times> unit + (unit, unit) routed_gk \<Rightarrow> (ivl exec_dg_st lifted, ivl exec_dg_st lifted) dg_state)" where
  "interval_conf_sol_warrow gs empty_pred Pi ps =
     TD_side_warrowing_apinis_Interp_solve (interval_conf_eqs gs empty_pred Pi ps)
       (cfg_exit (compile_prog Pi ps), ())"

definition interval_conf_terminates_warrow ::
    "(vname \<Rightarrow> bool) \<Rightarrow> (ivl exec_dg_st \<Rightarrow> bool) \<Rightarrow> proc_table \<Rightarrow> pname list \<Rightarrow> bool" where
  "interval_conf_terminates_warrow gs empty_pred Pi ps =
     TD_side_warrowing_apinis_Interp.solve_dom TYPE((unit, unit) routed_gk) TYPE((ivl exec_dg_st lifted, ivl exec_dg_st lifted) dg_state)
       (interval_conf_eqs gs empty_pred Pi ps) (cfg_exit (compile_prog Pi ps), ())"

lemma interval_conf_terminates_warrow_via_solve_c:
  assumes "TD_side_warrowing_apinis_Interp_solve_c (interval_conf_eqs gs empty_pred Pi ps)
             (cfg_exit (compile_prog Pi ps), ()) \<noteq> None"
  shows "interval_conf_terminates_warrow gs empty_pred Pi ps"
  unfolding interval_conf_terminates_warrow_def
  by (rule TD_side_warrowing_apinis_Interp.solve_dom_of_solve_c[OF assms])

subsection \<open>The Apinis warrowing instance\<close>

lemma interval_conf_warrow_pp_st:
  "interval_conf_terminates_warrow gs empty_pred Pi ps
     \<Longrightarrow> part_post_solution (interval_conf_eqs gs empty_pred Pi ps)
           (cfg_exit (compile_prog Pi ps), ())
           (snd (interval_conf_sol_warrow gs empty_pred Pi ps))
           (fst (interval_conf_sol_warrow gs empty_pred Pi ps))"
  unfolding interval_conf_sol_warrow_def interval_conf_terminates_warrow_def
  by (rule TD_side_warrowing_apinis_Interp.partial_post_solution[OF _ surjective_pairing])

lemma interval_conf_warrow_vars_finite:
  assumes "interval_conf_terminates_warrow gs empty_pred Pi ps"
  shows "finite (fst (interval_conf_sol_warrow gs empty_pred Pi ps))"
  using TD_side_warrowing_apinis_Interp.finite_stabl_solve[
      OF assms[unfolded interval_conf_terminates_warrow_def]]
  unfolding interval_conf_sol_warrow_def TD_side_warrowing_apinis_Interp_solve_def
  by simp

global_interpretation interval_conf_wa: interval_conf_solved interval_conf_sol_warrow interval_conf_terminates_warrow
proof (unfold_locales, goal_cases PpSt VarsFin)
  case (PpSt gs empty_pred Pi ps) thus ?case by (rule interval_conf_warrow_pp_st)
next
  case (VarsFin gs empty_pred Pi ps) thus ?case by (rule interval_conf_warrow_vars_finite)
qed

lemmas interval_conf_result_node_sound_warrow = interval_conf_wa.result_node_sound
lemmas interval_conf_analyse_result_eq_warrow = interval_conf_wa.analyse_result_eq
lemmas interval_conf_cinit_le_cinit_ivl_st_warrow = interval_conf_wa.cinit_le_cinit_ivl_st
lemmas interval_conf_report_ctx_proved_sound_warrow = interval_conf_wa.report_ctx_proved_sound
lemmas interval_conf_report_ctx_refuted_sound_warrow = interval_conf_wa.report_ctx_refuted_sound

section \<open>Warrowing-per-origin solver instantiation\<close>

text \<open>
  The fourth update rule, and the reason the development above is a locale rather than a
  copied block: \<^const>\<open>update_global_warrowing_per_origin\<close> widens each origin's own
  contribution and joins afterwards, where \<^const>\<open>update_global_warrowing_apinis\<close> widens
  the value already joined across every origin.  Two producers writing different constants
  to one global separate the two.
\<close>

definition interval_conf_sol_wpo ::
    "(vname \<Rightarrow> bool) \<Rightarrow> (ivl exec_dg_st \<Rightarrow> bool) \<Rightarrow> proc_table \<Rightarrow> pname list \<Rightarrow> (pp \<times> unit) set \<times> (pp \<times> unit + (unit, unit) routed_gk \<Rightarrow> (ivl exec_dg_st lifted, ivl exec_dg_st lifted) dg_state)" where
  "interval_conf_sol_wpo gs empty_pred Pi ps =
     TD_side_warrowing_per_origin_Interp_solve (interval_conf_eqs gs empty_pred Pi ps)
       (cfg_exit (compile_prog Pi ps), ())"

definition interval_conf_terminates_wpo ::
    "(vname \<Rightarrow> bool) \<Rightarrow> (ivl exec_dg_st \<Rightarrow> bool) \<Rightarrow> proc_table \<Rightarrow> pname list \<Rightarrow> bool" where
  "interval_conf_terminates_wpo gs empty_pred Pi ps =
     TD_side_warrowing_per_origin_Interp.solve_dom TYPE((unit, unit) routed_gk)
       TYPE((ivl exec_dg_st lifted, ivl exec_dg_st lifted) dg_state)
       (interval_conf_eqs gs empty_pred Pi ps) (cfg_exit (compile_prog Pi ps), ())"

lemma interval_conf_terminates_wpo_via_solve_c:
  assumes "TD_side_warrowing_per_origin_Interp_solve_c (interval_conf_eqs gs empty_pred Pi ps)
             (cfg_exit (compile_prog Pi ps), ()) \<noteq> None"
  shows "interval_conf_terminates_wpo gs empty_pred Pi ps"
  unfolding interval_conf_terminates_wpo_def
  by (rule TD_side_warrowing_per_origin_Interp.solve_dom_of_solve_c[OF assms])

lemma interval_conf_wpo_pp_st:
  "interval_conf_terminates_wpo gs empty_pred Pi ps
     \<Longrightarrow> part_post_solution (interval_conf_eqs gs empty_pred Pi ps)
           (cfg_exit (compile_prog Pi ps), ())
           (snd (interval_conf_sol_wpo gs empty_pred Pi ps))
           (fst (interval_conf_sol_wpo gs empty_pred Pi ps))"
  unfolding interval_conf_sol_wpo_def interval_conf_terminates_wpo_def
  by (rule TD_side_warrowing_per_origin_Interp.partial_post_solution[OF _ surjective_pairing])

lemma interval_conf_wpo_vars_finite:
  assumes "interval_conf_terminates_wpo gs empty_pred Pi ps"
  shows "finite (fst (interval_conf_sol_wpo gs empty_pred Pi ps))"
  using TD_side_warrowing_per_origin_Interp.finite_stabl_solve[
      OF assms[unfolded interval_conf_terminates_wpo_def]]
  unfolding interval_conf_sol_wpo_def TD_side_warrowing_per_origin_Interp_solve_def
  by simp

global_interpretation interval_conf_wpo: interval_conf_solved interval_conf_sol_wpo interval_conf_terminates_wpo
proof (unfold_locales, goal_cases PpSt VarsFin)
  case (PpSt gs empty_pred Pi ps) thus ?case by (rule interval_conf_wpo_pp_st)
next
  case (VarsFin gs empty_pred Pi ps) thus ?case by (rule interval_conf_wpo_vars_finite)
qed

lemmas interval_conf_result_node_sound_wpo = interval_conf_wpo.result_node_sound
lemmas interval_conf_analyse_result_eq_wpo = interval_conf_wpo.analyse_result_eq
lemmas interval_conf_cinit_le_cinit_ivl_st_wpo = interval_conf_wpo.cinit_le_cinit_ivl_st
lemmas interval_conf_report_ctx_proved_sound_wpo = interval_conf_wpo.report_ctx_proved_sound
lemmas interval_conf_report_ctx_refuted_sound_wpo = interval_conf_wpo.report_ctx_refuted_sound

subsection \<open>Solved-result tables: PerOrigin and Apinis warrowing siblings\<close>

text \<open>
  Mirror \<open>interval_conf_sol_prog\<close>/\<open>interval_conf_terminates_prog\<close>/\<open>analyse_interval_ctx_result_for\<close> (the Join
  table above) at the PerOrigin and Apinis warrowing solvers, reading the same
  \<open>interval_conf_eqs_prog\<close> equation system: the three-solver orthogonality Interval's Base family
  already has (\<open>analyse_interval_dg_for\<close>/\<open>_join_for\<close>/\<open>_per_origin_for\<close>,
  \<^theory>\<open>Voblint_Analysis.Interval_Exec_Sound\<close>) now also holds at the routed spine.
\<close>

definition interval_conf_sol_prog_per_origin ::
    "(vname \<Rightarrow> bool) \<Rightarrow> imp_prog
       \<Rightarrow> (pp \<times> unit) set \<times> (pp \<times> unit + (unit, unit) routed_gk \<Rightarrow> (ivl exec_dg_st lifted, ivl exec_dg_st lifted) dg_state)" where
  "interval_conf_sol_prog_per_origin gs p =
     TD_side_per_origin_Interp_solve (interval_conf_eqs_prog gs p) (cfg_exit (prog_cfg p), ())"

definition interval_conf_terminates_prog_per_origin :: "(vname \<Rightarrow> bool) \<Rightarrow> imp_prog \<Rightarrow> bool" where
  "interval_conf_terminates_prog_per_origin gs p =
     interval_conf_terminates_per_origin gs (resolved_st_q_is_bot_for (declared_global_vars p))
       (prog_table p) (prog_procs p)"

lemma interval_conf_terminates_prog_per_origin_via_solve_c:
  assumes "TD_side_per_origin_Interp_solve_c
             (interval_conf_eqs gs (resolved_st_q_is_bot_for (declared_global_vars p))
                (prog_table p) (prog_procs p))
             (cfg_exit (compile_prog (prog_table p) (prog_procs p)), ()) \<noteq> None"
  shows "interval_conf_terminates_prog_per_origin gs p"
  unfolding interval_conf_terminates_prog_per_origin_def
  using assms by (rule interval_conf_terminates_per_origin_via_solve_c)

definition analyse_interval_ctx_result_per_origin_for ::
    "(vname \<Rightarrow> bool) \<Rightarrow> imp_prog \<Rightarrow> (unit, ivl abs_state) analysis_result" where
  "analyse_interval_ctx_result_per_origin_for gs p =
     Analysis_Result
       (fst (interval_conf_sol_prog_per_origin gs p))
       (\<lambda>v ctx. normalize_point gs
                  (canonicalize_lift (resolved_st_q_is_bot_for (declared_global_vars p))
                    (locals (snd (interval_conf_sol_prog_per_origin gs p) (Inl (v, ctx))))))"

declare analyse_interval_ctx_result_per_origin_for_def [code del]

lemma analyse_interval_ctx_result_per_origin_for_code [code]:
  "analyse_interval_ctx_result_per_origin_for gs p =
     (let sol = interval_conf_sol_prog_per_origin gs p; gl = declared_global_vars p
      in Analysis_Result (fst sol)
           (\<lambda>v ctx. normalize_point gs
                      (canonicalize_lift (resolved_st_q_is_bot_for gl)
                        (locals (snd sol (Inl (v, ctx)))))))"
  unfolding analyse_interval_ctx_result_per_origin_for_def Let_def by (rule refl)

definition analyse_interval_ctx_result_per_origin :: "imp_prog \<Rightarrow> (unit, ivl abs_state) analysis_result" where
  "analyse_interval_ctx_result_per_origin p =
     analyse_interval_ctx_result_per_origin_for (declared_global p) p"

definition interval_conf_sol_prog_warrow ::
    "(vname \<Rightarrow> bool) \<Rightarrow> imp_prog
       \<Rightarrow> (pp \<times> unit) set \<times> (pp \<times> unit + (unit, unit) routed_gk \<Rightarrow> (ivl exec_dg_st lifted, ivl exec_dg_st lifted) dg_state)" where
  "interval_conf_sol_prog_warrow gs p =
     TD_side_warrowing_apinis_Interp_solve (interval_conf_eqs_prog gs p) (cfg_exit (prog_cfg p), ())"

definition interval_conf_terminates_prog_warrow :: "(vname \<Rightarrow> bool) \<Rightarrow> imp_prog \<Rightarrow> bool" where
  "interval_conf_terminates_prog_warrow gs p =
     interval_conf_terminates_warrow gs (resolved_st_q_is_bot_for (declared_global_vars p))
       (prog_table p) (prog_procs p)"

lemma interval_conf_terminates_prog_warrow_via_solve_c:
  assumes "TD_side_warrowing_apinis_Interp_solve_c
             (interval_conf_eqs gs (resolved_st_q_is_bot_for (declared_global_vars p))
                (prog_table p) (prog_procs p))
             (cfg_exit (compile_prog (prog_table p) (prog_procs p)), ()) \<noteq> None"
  shows "interval_conf_terminates_prog_warrow gs p"
  unfolding interval_conf_terminates_prog_warrow_def
  using assms by (rule interval_conf_terminates_warrow_via_solve_c)

definition analyse_interval_ctx_result_warrow_for ::
    "(vname \<Rightarrow> bool) \<Rightarrow> imp_prog \<Rightarrow> (unit, ivl abs_state) analysis_result" where
  "analyse_interval_ctx_result_warrow_for gs p =
     Analysis_Result
       (fst (interval_conf_sol_prog_warrow gs p))
       (\<lambda>v ctx. normalize_point gs
                  (canonicalize_lift (resolved_st_q_is_bot_for (declared_global_vars p))
                    (locals (snd (interval_conf_sol_prog_warrow gs p) (Inl (v, ctx))))))"

declare analyse_interval_ctx_result_warrow_for_def [code del]

lemma analyse_interval_ctx_result_warrow_for_code [code]:
  "analyse_interval_ctx_result_warrow_for gs p =
     (let sol = interval_conf_sol_prog_warrow gs p; gl = declared_global_vars p
      in Analysis_Result (fst sol)
           (\<lambda>v ctx. normalize_point gs
                      (canonicalize_lift (resolved_st_q_is_bot_for gl)
                        (locals (snd sol (Inl (v, ctx)))))))"
  unfolding analyse_interval_ctx_result_warrow_for_def Let_def by (rule refl)

definition analyse_interval_ctx_result_warrow :: "imp_prog \<Rightarrow> (unit, ivl abs_state) analysis_result" where
  "analyse_interval_ctx_result_warrow p =
     analyse_interval_ctx_result_warrow_for (declared_global p) p"

subsection \<open>The global unknowns the same solve side-effects\<close>

text \<open>
  \<^const>\<open>ctx_solved_for\<close> at this domain's warrowing solve, with \<^const>\<open>Analysis_Global\<close> and
  \<^const>\<open>Activation_Seed\<close> handed to \<^const>\<open>seed_global_keys\<close> the way \<^const>\<open>routed_entry_seed_tree\<close>
  already takes them. Nothing here is domain-specific but the solve and the two
  constructors.
\<close>

definition analyse_interval_ctx_solved_warrow_for ::
    "(vname \<Rightarrow> bool) \<Rightarrow> imp_prog
     \<Rightarrow> (unit, ivl abs_state) analysis_result
          \<times> (String.literal \<times> ivl abs_state lifted) list" where
  "analyse_interval_ctx_solved_warrow_for =
     ctx_solved_for interval_conf_sol_prog_warrow (unit_seed_global_keys (Analysis_Global ()) Activation_Seed)"

lemma fst_analyse_interval_ctx_solved_warrow_for:
  "fst (analyse_interval_ctx_solved_warrow_for gs p)
     = analyse_interval_ctx_result_warrow_for gs p"
  by (simp add: analyse_interval_ctx_solved_warrow_for_def fst_ctx_solved_for
      analyse_interval_ctx_result_warrow_for_def Let_def)

subsection \<open>Solved-result table: warrowing per origin\<close>

definition interval_conf_sol_prog_wpo ::
    "(vname \<Rightarrow> bool) \<Rightarrow> imp_prog
       \<Rightarrow> (pp \<times> unit) set \<times> (pp \<times> unit + (unit, unit) routed_gk \<Rightarrow> (ivl exec_dg_st lifted, ivl exec_dg_st lifted) dg_state)" where
  "interval_conf_sol_prog_wpo gs p =
     TD_side_warrowing_per_origin_Interp_solve (interval_conf_eqs_prog gs p) (cfg_exit (prog_cfg p), ())"

definition interval_conf_terminates_prog_wpo :: "(vname \<Rightarrow> bool) \<Rightarrow> imp_prog \<Rightarrow> bool" where
  "interval_conf_terminates_prog_wpo gs p =
     interval_conf_terminates_wpo gs (resolved_st_q_is_bot_for (declared_global_vars p))
       (prog_table p) (prog_procs p)"

lemma interval_conf_terminates_prog_wpo_via_solve_c:
  assumes "TD_side_warrowing_per_origin_Interp_solve_c
             (interval_conf_eqs gs (resolved_st_q_is_bot_for (declared_global_vars p))
                (prog_table p) (prog_procs p))
             (cfg_exit (compile_prog (prog_table p) (prog_procs p)), ()) \<noteq> None"
  shows "interval_conf_terminates_prog_wpo gs p"
  unfolding interval_conf_terminates_prog_wpo_def
  using assms by (rule interval_conf_terminates_wpo_via_solve_c)

definition analyse_interval_ctx_result_wpo_for ::
    "(vname \<Rightarrow> bool) \<Rightarrow> imp_prog \<Rightarrow> (unit, ivl abs_state) analysis_result" where
  "analyse_interval_ctx_result_wpo_for gs p =
     Analysis_Result
       (fst (interval_conf_sol_prog_wpo gs p))
       (\<lambda>v ctx. normalize_point gs
                  (canonicalize_lift (resolved_st_q_is_bot_for (declared_global_vars p))
                    (locals (snd (interval_conf_sol_prog_wpo gs p) (Inl (v, ctx))))))"

declare analyse_interval_ctx_result_wpo_for_def [code del]

lemma analyse_interval_ctx_result_wpo_for_code [code]:
  "analyse_interval_ctx_result_wpo_for gs p =
     (let sol = interval_conf_sol_prog_wpo gs p; gl = declared_global_vars p
      in Analysis_Result (fst sol)
           (\<lambda>v ctx. normalize_point gs
                      (canonicalize_lift (resolved_st_q_is_bot_for gl)
                        (locals (snd sol (Inl (v, ctx)))))))"
  unfolding analyse_interval_ctx_result_wpo_for_def Let_def by (rule refl)

definition analyse_interval_ctx_result_wpo :: "imp_prog \<Rightarrow> (unit, ivl abs_state) analysis_result" where
  "analyse_interval_ctx_result_wpo p =
     analyse_interval_ctx_result_wpo_for (declared_global p) p"


section \<open>Solver-choice generalization\<close>

text \<open>
  \<^const>\<open>cs_call_string_eqs\<close> names no solve function -- only \<open>interval_spec\<close> and
  the routing policy -- so it is exactly as solver-independent as
  \<open>interval_conf_eqs\<close> at \<open>Ctx_None\<close> (\<^theory>\<open>Voblint_Analysis.Interval_Exec_Sound\<close>'s
  \<open>analyse_interval_dg_join_for\<close>/\<open>_per_origin_for\<close> alongside the Warrow
  default). The same routed system is solved under every discipline
  below, mirroring that pattern precisely; \<open>cs_call_string_sol_prog\<close> (Warrow,
  the shipped default) is untouched.
\<close>

definition cs_call_string_sol_prog_join ::
    "nat \<Rightarrow> (vname \<Rightarrow> bool) \<Rightarrow> imp_prog
       \<Rightarrow> (pp \<times> call_string) set \<times> (pp \<times> call_string + call_string_gk \<Rightarrow> (ivl exec_dg_st lifted, ivl exec_dg_st lifted) dg_state)" where
  "cs_call_string_sol_prog_join k gs p =
     TD_side_always_join_Interp_solve (cs_call_string_eqs_prog k gs p)
       (cfg_exit (prog_cfg p), [])"

definition cs_call_string_sol_prog_per_origin ::
    "nat \<Rightarrow> (vname \<Rightarrow> bool) \<Rightarrow> imp_prog
       \<Rightarrow> (pp \<times> call_string) set \<times> (pp \<times> call_string + call_string_gk \<Rightarrow> (ivl exec_dg_st lifted, ivl exec_dg_st lifted) dg_state)" where
  "cs_call_string_sol_prog_per_origin k gs p =
     TD_side_per_origin_Interp_solve (cs_call_string_eqs_prog k gs p)
       (cfg_exit (prog_cfg p), [])"

definition analyse_interval_call_string_result_for_join ::
    "nat \<Rightarrow> (vname \<Rightarrow> bool) \<Rightarrow> imp_prog \<Rightarrow> (call_string, ivl abs_state) analysis_result" where
  "analyse_interval_call_string_result_for_join k gs p =
     Analysis_Result
       (fst (cs_call_string_sol_prog_join k gs p))
       (\<lambda>v ctx. normalize_point gs
                  (canonicalize_lift (resolved_st_q_is_bot_for (declared_global_vars p))
                    (locals (snd (cs_call_string_sol_prog_join k gs p) (Inl (v, ctx))))))"

declare analyse_interval_call_string_result_for_join_def [code del]

lemma analyse_interval_call_string_result_for_join_code [code]:
  "analyse_interval_call_string_result_for_join k gs p =
     (let sol = cs_call_string_sol_prog_join k gs p; gl = declared_global_vars p
      in Analysis_Result (fst sol)
           (\<lambda>v ctx. normalize_point gs
                      (canonicalize_lift (resolved_st_q_is_bot_for gl)
                        (locals (snd sol (Inl (v, ctx)))))))"
  unfolding analyse_interval_call_string_result_for_join_def Let_def by (rule refl)

definition analyse_interval_call_string_result_for_per_origin ::
    "nat \<Rightarrow> (vname \<Rightarrow> bool) \<Rightarrow> imp_prog \<Rightarrow> (call_string, ivl abs_state) analysis_result" where
  "analyse_interval_call_string_result_for_per_origin k gs p =
     Analysis_Result
       (fst (cs_call_string_sol_prog_per_origin k gs p))
       (\<lambda>v ctx. normalize_point gs
                  (canonicalize_lift (resolved_st_q_is_bot_for (declared_global_vars p))
                    (locals (snd (cs_call_string_sol_prog_per_origin k gs p) (Inl (v, ctx))))))"

declare analyse_interval_call_string_result_for_per_origin_def [code del]

lemma analyse_interval_call_string_result_for_per_origin_code [code]:
  "analyse_interval_call_string_result_for_per_origin k gs p =
     (let sol = cs_call_string_sol_prog_per_origin k gs p; gl = declared_global_vars p
      in Analysis_Result (fst sol)
           (\<lambda>v ctx. normalize_point gs
                      (canonicalize_lift (resolved_st_q_is_bot_for gl)
                        (locals (snd sol (Inl (v, ctx)))))))"
  unfolding analyse_interval_call_string_result_for_per_origin_def Let_def by (rule refl)

definition cs_call_string_verdict_report_prog_join ::
    "nat \<Rightarrow> imp_prog \<Rightarrow> (pp \<times> exp \<times> contextual_verdict) list" where
  "cs_call_string_verdict_report_prog_join k p =
     classify_checks_verdicts (prog_cfg p)
       (analyse_interval_call_string_result_for_join k (declared_global p) p)
       interval_classify_check"

definition cs_call_string_verdict_report_prog_per_origin ::
    "nat \<Rightarrow> imp_prog \<Rightarrow> (pp \<times> exp \<times> contextual_verdict) list" where
  "cs_call_string_verdict_report_prog_per_origin k p =
     classify_checks_verdicts (prog_cfg p)
       (analyse_interval_call_string_result_for_per_origin k (declared_global p) p)
       interval_classify_check"

definition analyse_interval_call_string_report_join ::
    "nat \<Rightarrow> imp_prog \<Rightarrow> (pp \<times> exp \<times> contextual_verdict) list" where
  "analyse_interval_call_string_report_join k p =
     cs_call_string_verdict_report_prog_join k p"

definition analyse_interval_call_string_report_per_origin ::
    "nat \<Rightarrow> imp_prog \<Rightarrow> (pp \<times> exp \<times> contextual_verdict) list" where
  "analyse_interval_call_string_report_per_origin k p =
     cs_call_string_verdict_report_prog_per_origin k p"

definition cs_call_string_sol_prog_wpo ::
    "nat \<Rightarrow> (vname \<Rightarrow> bool) \<Rightarrow> imp_prog
       \<Rightarrow> (pp \<times> call_string) set \<times> (pp \<times> call_string + call_string_gk \<Rightarrow> (ivl exec_dg_st lifted, ivl exec_dg_st lifted) dg_state)" where
  "cs_call_string_sol_prog_wpo k gs p =
     TD_side_warrowing_per_origin_Interp_solve (cs_call_string_eqs_prog k gs p)
       (cfg_exit (prog_cfg p), [])"

definition analyse_interval_call_string_result_for_wpo ::
    "nat \<Rightarrow> (vname \<Rightarrow> bool) \<Rightarrow> imp_prog \<Rightarrow> (call_string, ivl abs_state) analysis_result" where
  "analyse_interval_call_string_result_for_wpo k gs p =
     Analysis_Result
       (fst (cs_call_string_sol_prog_wpo k gs p))
       (\<lambda>v ctx. normalize_point gs
                  (canonicalize_lift (resolved_st_q_is_bot_for (declared_global_vars p))
                    (locals (snd (cs_call_string_sol_prog_wpo k gs p) (Inl (v, ctx))))))"

declare analyse_interval_call_string_result_for_wpo_def [code del]

lemma analyse_interval_call_string_result_for_wpo_code [code]:
  "analyse_interval_call_string_result_for_wpo k gs p =
     (let sol = cs_call_string_sol_prog_wpo k gs p; gl = declared_global_vars p
      in Analysis_Result (fst sol)
           (\<lambda>v ctx. normalize_point gs
                      (canonicalize_lift (resolved_st_q_is_bot_for gl)
                        (locals (snd sol (Inl (v, ctx)))))))"
  unfolding analyse_interval_call_string_result_for_wpo_def Let_def by (rule refl)

definition cs_call_string_verdict_report_prog_wpo ::
    "nat \<Rightarrow> imp_prog \<Rightarrow> (pp \<times> exp \<times> contextual_verdict) list" where
  "cs_call_string_verdict_report_prog_wpo k p =
     classify_checks_verdicts (prog_cfg p)
       (analyse_interval_call_string_result_for_wpo k (declared_global p) p)
       interval_classify_check"

definition analyse_interval_call_string_report_wpo ::
    "nat \<Rightarrow> imp_prog \<Rightarrow> (pp \<times> exp \<times> contextual_verdict) list" where
  "analyse_interval_call_string_report_wpo k p =
     cs_call_string_verdict_report_prog_wpo k p"


section \<open>Solver-choice generalization\<close>

text \<open>
  \<^const>\<open>entry_state_eqs\<close> names no solve function -- only \<open>interval_spec\<close> and
  the routing policy -- so it is exactly as solver-independent as
  \<open>interval_conf_eqs\<close> at \<open>Ctx_None\<close>
  (\<^theory>\<open>Voblint_Analysis.Interval_Exec_Sound\<close>'s \<open>analyse_interval_dg_join_for\<close>/
  \<open>_per_origin_for\<close> alongside the Warrow default), and exactly as its own
  the call-string configuration above sibling solves the routed call-string
  system under every discipline. \<^const>\<open>entry_state_sol_prog\<close> (Warrow,
  the shipped default) is untouched.
\<close>

definition entry_state_sol_prog_join ::
    "(vname \<Rightarrow> bool) \<Rightarrow> imp_prog
       \<Rightarrow> (pp \<times> ivl list) set \<times> (pp \<times> ivl list + (unit, ivl list) routed_gk \<Rightarrow> (ivl exec_dg_st lifted, ivl exec_dg_st lifted) dg_state)" where
  "entry_state_sol_prog_join gs p =
     TD_side_always_join_Interp_solve (entry_state_eqs_prog gs p)
       (cfg_exit (prog_cfg p), [])"

definition entry_state_sol_prog_per_origin ::
    "(vname \<Rightarrow> bool) \<Rightarrow> imp_prog
       \<Rightarrow> (pp \<times> ivl list) set \<times> (pp \<times> ivl list + (unit, ivl list) routed_gk \<Rightarrow> (ivl exec_dg_st lifted, ivl exec_dg_st lifted) dg_state)" where
  "entry_state_sol_prog_per_origin gs p =
     TD_side_per_origin_Interp_solve (entry_state_eqs_prog gs p)
       (cfg_exit (prog_cfg p), [])"

definition analyse_interval_entry_state_result_for_join ::
    "(vname \<Rightarrow> bool) \<Rightarrow> imp_prog \<Rightarrow> (ivl list, ivl abs_state) analysis_result" where
  "analyse_interval_entry_state_result_for_join gs p =
     Analysis_Result
       (fst (entry_state_sol_prog_join gs p))
       (\<lambda>v ctx. normalize_point gs
                  (canonicalize_lift (resolved_st_q_is_bot_for (declared_global_vars p))
                    (locals (snd (entry_state_sol_prog_join gs p) (Inl (v, ctx))))))"

declare analyse_interval_entry_state_result_for_join_def [code del]

lemma analyse_interval_entry_state_result_for_join_code [code]:
  "analyse_interval_entry_state_result_for_join gs p =
     (let sol = entry_state_sol_prog_join gs p; gl = declared_global_vars p
      in Analysis_Result (fst sol)
           (\<lambda>v ctx. normalize_point gs
                      (canonicalize_lift (resolved_st_q_is_bot_for gl)
                        (locals (snd sol (Inl (v, ctx)))))))"
  unfolding analyse_interval_entry_state_result_for_join_def Let_def by (rule refl)

definition analyse_interval_entry_state_result_for_per_origin ::
    "(vname \<Rightarrow> bool) \<Rightarrow> imp_prog \<Rightarrow> (ivl list, ivl abs_state) analysis_result" where
  "analyse_interval_entry_state_result_for_per_origin gs p =
     Analysis_Result
       (fst (entry_state_sol_prog_per_origin gs p))
       (\<lambda>v ctx. normalize_point gs
                  (canonicalize_lift (resolved_st_q_is_bot_for (declared_global_vars p))
                    (locals (snd (entry_state_sol_prog_per_origin gs p) (Inl (v, ctx))))))"

declare analyse_interval_entry_state_result_for_per_origin_def [code del]

lemma analyse_interval_entry_state_result_for_per_origin_code [code]:
  "analyse_interval_entry_state_result_for_per_origin gs p =
     (let sol = entry_state_sol_prog_per_origin gs p; gl = declared_global_vars p
      in Analysis_Result (fst sol)
           (\<lambda>v ctx. normalize_point gs
                      (canonicalize_lift (resolved_st_q_is_bot_for gl)
                        (locals (snd sol (Inl (v, ctx)))))))"
  unfolding analyse_interval_entry_state_result_for_per_origin_def Let_def by (rule refl)

definition entry_state_verdict_report_prog_join ::
    "imp_prog \<Rightarrow> (pp \<times> exp \<times> contextual_verdict) list" where
  "entry_state_verdict_report_prog_join p =
     classify_checks_verdicts (prog_cfg p)
       (analyse_interval_entry_state_result_for_join (declared_global p) p)
       interval_classify_check"

definition entry_state_verdict_report_prog_per_origin ::
    "imp_prog \<Rightarrow> (pp \<times> exp \<times> contextual_verdict) list" where
  "entry_state_verdict_report_prog_per_origin p =
     classify_checks_verdicts (prog_cfg p)
       (analyse_interval_entry_state_result_for_per_origin (declared_global p) p)
       interval_classify_check"

definition analyse_interval_entry_state_join ::
    "imp_prog \<Rightarrow> (pp \<times> exp \<times> contextual_verdict) list" where
  "analyse_interval_entry_state_join p = entry_state_verdict_report_prog_join p"

definition analyse_interval_entry_state_per_origin ::
    "imp_prog \<Rightarrow> (pp \<times> exp \<times> contextual_verdict) list" where
  "analyse_interval_entry_state_per_origin p =
     entry_state_verdict_report_prog_per_origin p"

definition entry_state_sol_prog_wpo ::
    "(vname \<Rightarrow> bool) \<Rightarrow> imp_prog
       \<Rightarrow> (pp \<times> ivl list) set \<times> (pp \<times> ivl list + (unit, ivl list) routed_gk \<Rightarrow> (ivl exec_dg_st lifted, ivl exec_dg_st lifted) dg_state)" where
  "entry_state_sol_prog_wpo gs p =
     TD_side_warrowing_per_origin_Interp_solve (entry_state_eqs_prog gs p)
       (cfg_exit (prog_cfg p), [])"

definition analyse_interval_entry_state_result_for_wpo ::
    "(vname \<Rightarrow> bool) \<Rightarrow> imp_prog \<Rightarrow> (ivl list, ivl abs_state) analysis_result" where
  "analyse_interval_entry_state_result_for_wpo gs p =
     Analysis_Result
       (fst (entry_state_sol_prog_wpo gs p))
       (\<lambda>v ctx. normalize_point gs
                  (canonicalize_lift (resolved_st_q_is_bot_for (declared_global_vars p))
                    (locals (snd (entry_state_sol_prog_wpo gs p) (Inl (v, ctx))))))"

declare analyse_interval_entry_state_result_for_wpo_def [code del]

lemma analyse_interval_entry_state_result_for_wpo_code [code]:
  "analyse_interval_entry_state_result_for_wpo gs p =
     (let sol = entry_state_sol_prog_wpo gs p; gl = declared_global_vars p
      in Analysis_Result (fst sol)
           (\<lambda>v ctx. normalize_point gs
                      (canonicalize_lift (resolved_st_q_is_bot_for gl)
                        (locals (snd sol (Inl (v, ctx)))))))"
  unfolding analyse_interval_entry_state_result_for_wpo_def Let_def by (rule refl)

definition entry_state_verdict_report_prog_wpo ::
    "imp_prog \<Rightarrow> (pp \<times> exp \<times> contextual_verdict) list" where
  "entry_state_verdict_report_prog_wpo p =
     classify_checks_verdicts (prog_cfg p)
       (analyse_interval_entry_state_result_for_wpo (declared_global p) p)
       interval_classify_check"

definition analyse_interval_entry_state_wpo ::
    "imp_prog \<Rightarrow> (pp \<times> exp \<times> contextual_verdict) list" where
  "analyse_interval_entry_state_wpo p =
     entry_state_verdict_report_prog_wpo p"

end
