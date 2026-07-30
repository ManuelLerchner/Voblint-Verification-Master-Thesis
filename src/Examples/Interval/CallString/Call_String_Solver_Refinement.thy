theory Call_String_Solver_Refinement
  imports Example_Interval_DG_CallString_K2
begin

definition project_sigma :: "pp \<times> cfg_node list + gk_1 \<Rightarrow> (ivl st, ivl st) dg_state" where
  "project_sigma x =
     (case x of
        Inl (v, ctx1) \<Rightarrow>
          (if (v, ctx1) = (Statement 0, [Statement 2]) then
             snd nest_2_sol (Inl (Statement 0, [Statement 2, Statement 5]))
               \<squnion> snd nest_2_sol (Inl (Statement 0, [Statement 2, Statement 6]))
           else if (v, ctx1) = (FunctionResult ''g'', [Statement 2]) then
             snd nest_2_sol (Inl (FunctionResult ''g'', [Statement 2, Statement 5]))
               \<squnion> snd nest_2_sol (Inl (FunctionResult ''g'', [Statement 2, Statement 6]))
           else if (v, ctx1) = (FunctionEntry ''g'', [Statement 2]) then
             snd nest_2_sol (Inl (FunctionEntry ''g'', [Statement 2, Statement 5]))
               \<squnion> snd nest_2_sol (Inl (FunctionEntry ''g'', [Statement 2, Statement 6]))
           else snd nest_2_sol (Inl (v, ctx1)))
      | Inr Global1 \<Rightarrow> snd nest_2_sol (Inr Global2)
      | Inr (Seed1 v ctx1) \<Rightarrow>
          (if (v, ctx1) = (FunctionEntry ''g'', [Statement 2]) then
             snd nest_2_sol (Inr (Seed2 v [Statement 2, Statement 5]))
               \<squnion> snd nest_2_sol (Inr (Seed2 v [Statement 2, Statement 6]))
           else snd nest_2_sol (Inr (Seed2 v ctx1))))"

subsection \<open>FunctionEntry g -- pure seed read, no intra, no comb\<close>

lemma entry_g_no_intra: "intra_predecessor_list nest_cfg (FunctionEntry ''g'') = []"
  by eval

lemma entry_g_no_return: "return_call_action_list nest_cfg (FunctionEntry ''g'') = []"
  by eval

lemma entry_g_no_calls: "call_successor_list nest_cfg (FunctionEntry ''g'') = []"
  by eval

lemma nest_1_eqs_entry_g:
  "nest_1_eqs (FunctionEntry ''g'', [Statement 2])
     = QueryG (Seed1 (FunctionEntry ''g'') [Statement 2]) (\<lambda>d. answer_local (globs d))"
  unfolding nest_1_eqs_def side_cfg_T_eff_keyed_seed_dg_def routed_extra_def
  by (simp add: entry_g_no_intra entry_g_no_return entry_g_no_calls nest_entry
                side_rhs_fold_dg.simps seqcomp_tree.simps)

lemma dep_L_entry_g:
  "dep\<^sub>L nest_1_eqs project_sigma (FunctionEntry ''g'', [Statement 2]) = {}"
  unfolding dep\<^sub>L_def dep_def nest_1_eqs_entry_g
  by simp

lemma sides_of_rhs_entry_g:
  "sides_of_rhs (nest_1_eqs (FunctionEntry ''g'', [Statement 2])) project_sigma = bot"
  unfolding nest_1_eqs_entry_g
  by (simp add: bot_fun_def)

lemma project_sigma_dep_L_entry_g:
  "dep\<^sub>L nest_1_eqs project_sigma (FunctionEntry ''g'', [Statement 2]) \<subseteq> fst nest_1_sol"
  by (simp add: dep_L_entry_g)

lemma project_sigma_sides_entry_g:
  "sides_of_rhs (nest_1_eqs (FunctionEntry ''g'', [Statement 2])) project_sigma \<le> project_sigma"
  by (simp add: sides_of_rhs_entry_g)

subsection \<open>FunctionResult g -- the return/combine path, per the CFG\<close>

text \<open>\<open>FunctionResult ''g''\<close> is reached only by the intra return edge from \<open>Statement 0\<close>
  (\<open>nest_intra\<close>); it is never a \<open>return_call_action_list\<close> continuation, so its equation
  carries no COMB fragment. The actual COMB nodes are the call continuations
  (\<open>Statement 3\<close>, \<open>Statement 6\<close>, \<open>Statement 7\<close>).\<close>

lemma result_g_no_comb: "return_call_action_list nest_cfg (FunctionResult ''g'') = []"
  by eval

lemma result_g_no_calls: "call_successor_list nest_cfg (FunctionResult ''g'') = []"
  by eval

lemma result_g_intra:
  "intra_predecessor_list nest_cfg (FunctionResult ''g'')
     = [(Statement 0, EA_Ret (Some (Plus (VIMP_Syntax.V ''p'') (VIMP_Syntax.V ''p''))) ''g'')]"
  by eval

lemma nest_1_eqs_result_g:
  "nest_1_eqs (FunctionResult ''g'', [Statement 2])
     = QueryL (Statement 0, [Statement 2]) (\<lambda>d. QueryG Global1 (\<lambda>gv.
         Side Global1
           (DG bot (fst (dg_spec_step Spoly
                 (EA_Ret (Some (Plus (VIMP_Syntax.V ''p'') (VIMP_Syntax.V ''p''))) ''g'')
                 (locals d) (globs gv))))
           (Answer (DG (snd (dg_spec_step Spoly
                 (EA_Ret (Some (Plus (VIMP_Syntax.V ''p'') (VIMP_Syntax.V ''p''))) ''g'')
                 (locals d) (globs gv))) bot))))"
  unfolding nest_1_eqs_def side_cfg_T_eff_keyed_seed_dg_def routed_extra_def
            apply_dg_spec_def dg_edge_tree_def
  by (simp add: result_g_intra result_g_no_comb result_g_no_calls nest_entry
                side_rhs_fold_dg.simps seqcomp_tree.simps)

lemma dep_L_result_g:
  "dep\<^sub>L nest_1_eqs project_sigma (FunctionResult ''g'', [Statement 2]) = {(Statement 0, [Statement 2])}"
  unfolding dep\<^sub>L_def dep_def nest_1_eqs_result_g
  by simp

lemma statement_0_covered_1: "(Statement 0, [Statement 2]) \<in> fst nest_1_sol"
  unfolding nest_1_sol_def nest_1_eqs_def by eval

lemma project_sigma_dep_L_result_g:
  "dep\<^sub>L nest_1_eqs project_sigma (FunctionResult ''g'', [Statement 2]) \<subseteq> fst nest_1_sol"
  by (simp add: dep_L_result_g statement_0_covered_1)

lemma sides_of_rhs_result_g:
  "sides_of_rhs (nest_1_eqs (FunctionResult ''g'', [Statement 2])) project_sigma
     = (\<lambda>_. bot)(Inr Global1 :=
         DG bot (fst (dg_spec_step Spoly
               (EA_Ret (Some (Plus (VIMP_Syntax.V ''p'') (VIMP_Syntax.V ''p''))) ''g'')
               (locals (project_sigma (Inl (Statement 0, [Statement 2]))))
               (globs (project_sigma (Inr Global1))))))"
  unfolding nest_1_eqs_result_g
  by (simp add: bot_fun_def)

lemma restrict_global_st_update_ret_var:
  "restrict_global_st (update_st s ret_var v) = restrict_global_st s"
  by (rule st_eqI_lookup) (auto simp: lookup_restrict_global_st ret_var_not_global)

lemma restrict_global_st_le: "restrict_global_st s \<le> s"
  by (simp add: le_st_iff lookup_restrict_global_st)

lemma fst_dgs_assign_ret_g:
  "fst (dgs_assign Spoly ret_var (Plus (VIMP_Syntax.V ''p'') (VIMP_Syntax.V ''p'')) d g)
     = restrict_global_st d \<squnion> restrict_global_st g"
  unfolding Spoly_def unit_dg_spec_st_def unit_step_st_def Let_def
  by (simp add: restrict_global_st_update_ret_var restrict_global_st_sup_restrict_global_st)

lemma fst_dg_spec_step_ret_g:
  "fst (dg_spec_step Spoly (EA_Ret (Some (Plus (VIMP_Syntax.V ''p'') (VIMP_Syntax.V ''p''))) ''g'') d g)
     = restrict_global_st d \<squnion> restrict_global_st g"
  by (simp add: fst_dgs_assign_ret_g)

subsection \<open>The same node, one level down in \<open>nest_2_eqs\<close>, at each child context\<close>

lemma result_g_intra_2:
  "intra_predecessor_list nest_cfg (FunctionResult ''g'')
     = [(Statement 0, EA_Ret (Some (Plus (VIMP_Syntax.V ''p'') (VIMP_Syntax.V ''p''))) ''g'')]"
  by eval

lemma nest_2_eqs_result_g:
  assumes "ctx = [Statement 2, Statement 5] \<or> ctx = [Statement 2, Statement 6]"
  shows "nest_2_eqs (FunctionResult ''g'', ctx)
     = QueryL (Statement 0, ctx) (\<lambda>d. QueryG Global2 (\<lambda>gv.
         Side Global2
           (DG bot (fst (dg_spec_step Spoly
                 (EA_Ret (Some (Plus (VIMP_Syntax.V ''p'') (VIMP_Syntax.V ''p''))) ''g'')
                 (locals d) (globs gv))))
           (Answer (DG (snd (dg_spec_step Spoly
                 (EA_Ret (Some (Plus (VIMP_Syntax.V ''p'') (VIMP_Syntax.V ''p''))) ''g'')
                 (locals d) (globs gv))) bot))))"
  using assms
  unfolding nest_2_eqs_def side_cfg_T_eff_keyed_seed_dg_def routed_extra_def
            apply_dg_spec_def dg_edge_tree_def
  by (auto simp: result_g_intra_2 result_g_no_comb result_g_no_calls nest_entry
                 side_rhs_fold_dg.simps seqcomp_tree.simps)

lemma sides_of_rhs_result_g_2:
  assumes "ctx = [Statement 2, Statement 5] \<or> ctx = [Statement 2, Statement 6]"
  shows "sides_of_rhs (nest_2_eqs (FunctionResult ''g'', ctx)) (snd nest_2_sol)
     = (\<lambda>_. bot)(Inr Global2 :=
         DG bot (fst (dg_spec_step Spoly
               (EA_Ret (Some (Plus (VIMP_Syntax.V ''p'') (VIMP_Syntax.V ''p''))) ''g'')
               (locals (snd nest_2_sol (Inl (Statement 0, ctx))))
               (globs (snd nest_2_sol (Inr Global2))))))"
  unfolding nest_2_eqs_result_g[OF assms]
  by (simp add: bot_fun_def)

lemma part_post_sides_2:
  assumes "u \<in> fst nest_2_sol"
  shows "sides_of_rhs (nest_2_eqs u) (snd nest_2_sol) \<le> snd nest_2_sol"
  using nest_2_pp_st assms by blast

lemma result_g_covered_2_A: "(FunctionResult ''g'', [Statement 2, Statement 5]) \<in> fst nest_2_sol"
  unfolding nest_2_sol_def nest_2_eqs_def by eval

lemma result_g_covered_2_B: "(FunctionResult ''g'', [Statement 2, Statement 6]) \<in> fst nest_2_sol"
  unfolding nest_2_sol_def nest_2_eqs_def by eval

lemma project_sigma_sides_result_g:
  "sides_of_rhs (nest_1_eqs (FunctionResult ''g'', [Statement 2])) project_sigma \<le> project_sigma"
proof -
  let ?dA = "snd nest_2_sol (Inl (Statement 0, [Statement 2, Statement 5]))"
  let ?dB = "snd nest_2_sol (Inl (Statement 0, [Statement 2, Statement 6]))"
  let ?g0 = "snd nest_2_sol (Inr Global2)"
  have d0: "locals (project_sigma (Inl (Statement 0, [Statement 2]))) = locals ?dA \<squnion> locals ?dB"
    by (simp add: project_sigma_def sup_dg_state_def)
  have restrict_boundA: "restrict_global_st (locals ?dA) \<le> globs ?g0"
    using part_post_sides_2[OF result_g_covered_2_A,
            unfolded sides_of_rhs_result_g_2[of "[Statement 2, Statement 5]", OF disjI1[OF refl]],
            THEN le_funD, of "Inr Global2"]
    by (simp add: less_eq_dg_state_def fst_dgs_assign_ret_g)
  have restrict_boundB: "restrict_global_st (locals ?dB) \<le> globs ?g0"
    using part_post_sides_2[OF result_g_covered_2_B,
            unfolded sides_of_rhs_result_g_2[of "[Statement 2, Statement 6]", OF disjI2[OF refl]],
            THEN le_funD, of "Inr Global2"]
    by (simp add: less_eq_dg_state_def fst_dgs_assign_ret_g)
  have split_d0: "restrict_global_st (locals (project_sigma (Inl (Statement 0, [Statement 2]))))
       = restrict_global_st (locals ?dA) \<squnion> restrict_global_st (locals ?dB)"
    by (simp add: d0 restrict_global_st_sup_restrict_global_st[symmetric])
  have key_bound:
    "fst (dg_spec_step Spoly (EA_Ret (Some (Plus (VIMP_Syntax.V ''p'') (VIMP_Syntax.V ''p''))) ''g'')
           (locals (project_sigma (Inl (Statement 0, [Statement 2]))))
           (globs (project_sigma (Inr Global1))))
       \<le> globs (project_sigma (Inr Global1))"
  proof -
    have "fst (dg_spec_step Spoly (EA_Ret (Some (Plus (VIMP_Syntax.V ''p'') (VIMP_Syntax.V ''p''))) ''g'')
             (locals (project_sigma (Inl (Statement 0, [Statement 2]))))
             (globs (project_sigma (Inr Global1))))
        = restrict_global_st (locals (project_sigma (Inl (Statement 0, [Statement 2]))))
            \<squnion> restrict_global_st (globs (project_sigma (Inr Global1)))"
      by (simp add: fst_dgs_assign_ret_g)
    also have "\<dots> = restrict_global_st (locals ?dA) \<squnion> restrict_global_st (locals ?dB)
                       \<squnion> restrict_global_st (globs ?g0)"
      by (simp add: split_d0 project_sigma_def restrict_global_st_sup_restrict_global_st
          sup_dg_state_def)
    also have "\<dots> \<le> globs ?g0"
      by (intro sup_least restrict_boundA restrict_boundB restrict_global_st_le)
    finally show ?thesis by (simp add: project_sigma_def)
  qed
  show ?thesis
    unfolding sides_of_rhs_result_g
    using key_bound by (auto simp: le_fun_def less_eq_dg_state_def bot_fun_def bot_dg_state_def)
qed

end

