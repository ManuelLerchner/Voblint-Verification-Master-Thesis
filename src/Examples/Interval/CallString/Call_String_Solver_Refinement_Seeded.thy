theory Call_String_Solver_Refinement_Seeded
  imports Example_Interval_DG_CallString_K2 "Voblint_Core.Call_String_Solver_Projection"
begin

section \<open>Probing the fine solution's variable set\<close>

text \<open>Explicit list form of the fine solution's variable set, needed because the generic
  seeding infrastructure (\<^const>\<open>seed_eqs\<close>, \<^const>\<open>seed_sides\<close>, \<^const>\<open>proj_local\<close>,
  \<^const>\<open>proj_global\<close>) folds over a \<^typ>\<open>'g list\<close>, not a \<^typ>\<open>'g set\<close>, to avoid a
  \<^const>\<open>Finite_Set.fold\<close> commutativity proof obligation. Order is irrelevant since every
  fold below only ever combines values with \<open>\<squnion>\<close>.\<close>
definition nest_2_vars_lst :: "(cfg_node \<times> cfg_node list) list" where
  "nest_2_vars_lst =
     [(Statement 0, [Statement 2, Statement 6]), (FunctionResult (STR ''g''), [Statement 2, Statement 6]),
      (Statement 2, [Statement 6]), (Statement 3, [Statement 6]), (FunctionResult (STR ''f''), [Statement 6]),
      (Statement 0, [Statement 2, Statement 5]), (FunctionResult (STR ''g''), [Statement 2, Statement 5]),
      (Statement 2, [Statement 5]), (Statement 3, [Statement 5]), (FunctionResult (STR ''f''), [Statement 5]),
      (Statement 5, []), (Statement 6, []), (Statement 7, []), (FunctionResult (STR ''main''), []),
      (FunctionEntry (STR ''g''), [Statement 2, Statement 6]), (FunctionEntry (STR ''f''), [Statement 6]),
      (FunctionEntry (STR ''g''), [Statement 2, Statement 5]), (FunctionEntry (STR ''f''), [Statement 5]),
      (FunctionEntry (STR ''main''), [])]"

lemma nest_2_vars_lst_set: "set nest_2_vars_lst = fst nest_2_sol"
  unfolding nest_2_vars_lst_def nest_2_sol_def nest_2_eqs_def by eval

section \<open>The seeded k=1 equation system and its solution\<close>

text \<open>A thin instantiation of \<^theory>\<open>Voblint_Core.Call_String_Solver_Projection\<close>'s
  fully generic construction at \<open>k1 = 1\<close>, this program's own \<open>nest_1_eqs\<close>, and the fine
  solution/variable list defined above. Nothing CallString-specific is proved here: the
  projection, the seeding, and the closure argument are all inherited.\<close>
definition nest_1_seeded_eqs ::
  "(pp \<times> cfg_node list, call_string_gk,
     (ivl exec_dg_st lifted, ivl exec_dg_st lifted) dg_state) eqsT" where
  "nest_1_seeded_eqs =
     project_seeded_eqs 1 nest_2_vars_lst (snd nest_2_sol) nest_1_eqs (cfg_exit nest_cfg, [])"

lemma nest_1_seeded_terminates:
  "TD_side_warrowing_apinis_Interp_solve_c nest_1_seeded_eqs (cfg_exit nest_cfg, []) \<noteq> None"
  by eval

definition nest_1_seeded_sol ::
  "(pp \<times> cfg_node list) set
     \<times> (pp \<times> cfg_node list + call_string_gk
          \<Rightarrow> (ivl exec_dg_st lifted, ivl exec_dg_st lifted) dg_state)" where
  "nest_1_seeded_sol = TD_side_warrowing_apinis_Interp_solve nest_1_seeded_eqs
                          (cfg_exit nest_cfg, [])"

lemma nest_1_seeded_solve_dom:
  "TD_side_warrowing_apinis_Interp.solve_dom TYPE(call_string_gk)
     TYPE((ivl exec_dg_st lifted, ivl exec_dg_st lifted) dg_state)
     nest_1_seeded_eqs (cfg_exit nest_cfg, [])"
  by (rule TD_side_warrowing_apinis_Interp.solve_dom_of_solve_c[OF nest_1_seeded_terminates])

lemma nest_1_seeded_pp_st:
  "part_post_solution nest_1_seeded_eqs (cfg_exit nest_cfg, [])
     (snd nest_1_seeded_sol) (fst nest_1_seeded_sol)"
  using TD_side_warrowing_apinis_Interp.partial_post_solution
          [OF nest_1_seeded_solve_dom, of "fst nest_1_seeded_sol" "snd nest_1_seeded_sol"]
  unfolding nest_1_seeded_sol_def by simp

section \<open>The refinement theorem\<close>

text \<open>A short corollary of
  \<^theory>\<open>Voblint_Core.Call_String_Solver_Projection\<close>'s fully generic
  \<open>call_string_projection_refinement\<close>, instantiated at this program's own data. No
  per-node case analysis is needed: the solver's own worklist propagation closes
  those nodes, and the
  projection/closure argument itself is proved once, generically, not per concrete
  example.\<close>
theorem nest_1_seeded_refinement:
  "part_post_solution nest_1_eqs (cfg_exit nest_cfg, [])
     (snd nest_1_seeded_sol) (fst nest_1_seeded_sol)"
  "\<forall>u \<in> fst nest_1_seeded_sol.
     proj_P 1 nest_2_vars_lst (snd nest_2_sol) (Inl u) \<le> snd nest_1_seeded_sol (Inl u)"
  "\<forall>g \<in> set (proj_global_keys 1 nest_2_vars_lst).
     proj_P 1 nest_2_vars_lst (snd nest_2_sol) (Inr g) \<le> snd nest_1_seeded_sol (Inr g)"
  using call_string_projection_refinement[OF nest_1_seeded_pp_st[unfolded nest_1_seeded_eqs_def]]
  unfolding nest_1_seeded_eqs_def by auto

end

