theory Call_String_Solver_Refinement
  imports Example_Interval_DG_CallString_K2
begin

text \<open>
  The merge is not a property of a node's own context fiber; it is a property of
  \<^emph>\<open>dependency reachability\<close> from a node whose fiber genuinely splits. \<open>Statement 0\<close>,
  \<open>FunctionResult ''g''\<close>, and \<open>FunctionEntry ''g''\<close> have two-element k=2 fibers, because
  \<open>g\<close> is entered from two distinct k=2 call strings that \<open>cs_route\<close> collapses to the same
  k=1 string \<open>[Statement 2]\<close>. Every other node in this witness keeps a singleton fiber
  (its own context never grows past k=1 regardless of \<open>k\<close>) -- but seven of those
  singleton-fiber nodes still transitively \<^emph>\<open>read\<close> a merged unknown, through an intra
  edge or a \<open>routed_cmb\<close> combine: \<open>Statement 3\<close> and \<open>FunctionResult ''f''\<close> (both contexts,
  since \<open>f\<close>'s call to \<open>g\<close> is the read site), then \<open>Statement 6\<close>, \<open>Statement 7\<close>, and
  \<open>FunctionResult ''main''\<close> (the chain of \<open>f\<close>-returns downstream of that). Those seven
  need the same widening even though their own fiber never splits, because the k=1
  equation they solve reads a merged dependency through \<^const>\<open>cs_route\<close>'s collapse, while
  a naive k=2 passthrough at their own (unsplit) context would only ever reflect one
  branch. This is the full dependency closure of the three genuinely-split unknowns under
  \<open>intra\<close>/\<open>calls\<close> reachability in \<open>nest_cfg\<close> -- nothing else in the program depends on the
  merge. Each downstream case is defined by re-evaluating its own equation with the
  already-widened dependency substituted in directly (never through a self-reference:
  \<open>definition\<close> cannot recurse), the same construction \<^const>\<open>eq\<close> would perform at that
  node once its inputs are known -- so far only for \<open>Statement 3\<close>, the case that exposed
  the gap (\<open>project_sigma_eq_statement3\<close>, proved by unfolding both sides to the same
  term); \<open>FunctionResult ''f''\<close>, \<open>Statement 6\<close>, \<open>Statement 7\<close>, and
  \<open>FunctionResult ''main''\<close> still need the same treatment before the \<open>_all\<close> lemmas below
  can close.
\<close>

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
           else if (v, ctx1) = (Statement 3, [Statement 5]) \<or> (v, ctx1) = (Statement 3, [Statement 6]) then
             DG (combine_local Spoly (Some ''t'')
                   (locals (snd nest_2_sol (Inl (Statement 2, ctx1))))
                   (locals (snd nest_2_sol (Inl (FunctionResult ''g'', [Statement 2, Statement 5]))
                              \<squnion> snd nest_2_sol (Inl (FunctionResult ''g'', [Statement 2, Statement 6]))))
                   (globs (snd nest_2_sol (Inr Global2))))
                bot
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

lemma part_post_eq_2:
  assumes "u \<in> fst nest_2_sol"
  shows "eq nest_2_eqs u (snd nest_2_sol) \<le> snd nest_2_sol (Inl u)"
  using nest_2_pp_st assms by blast

lemma nest_2_eqs_entry_g:
  assumes "ctx = [Statement 2, Statement 5] \<or> ctx = [Statement 2, Statement 6]"
  shows "nest_2_eqs (FunctionEntry ''g'', ctx)
     = QueryG (Seed2 (FunctionEntry ''g'') ctx) (\<lambda>d. answer_local (globs d))"
  using assms
  unfolding nest_2_eqs_def side_cfg_T_eff_keyed_seed_dg_def routed_extra_def
  by (auto simp: entry_g_no_intra entry_g_no_return entry_g_no_calls nest_entry
                 side_rhs_fold_dg.simps seqcomp_tree.simps)

lemma eq_entry_g_2:
  assumes "ctx = [Statement 2, Statement 5] \<or> ctx = [Statement 2, Statement 6]"
  shows "eq nest_2_eqs (FunctionEntry ''g'', ctx) (snd nest_2_sol)
       = DG (globs (snd nest_2_sol (Inr (Seed2 (FunctionEntry ''g'') ctx)))) bot"
  unfolding nest_2_eqs_entry_g[OF assms]
  by simp

lemma seed_le_entry_g_5:
  "globs (snd nest_2_sol (Inr (Seed2 (FunctionEntry ''g'') [Statement 2, Statement 5])))
     \<le> locals (snd nest_2_sol (Inl (FunctionEntry ''g'', [Statement 2, Statement 5])))"
  using part_post_eq_2[OF callee_covered_g_f3_2] eq_entry_g_2[of "[Statement 2, Statement 5]"]
  by (simp add: less_eq_dg_state_def)

lemma seed_le_entry_g_6:
  "globs (snd nest_2_sol (Inr (Seed2 (FunctionEntry ''g'') [Statement 2, Statement 6])))
     \<le> locals (snd nest_2_sol (Inl (FunctionEntry ''g'', [Statement 2, Statement 6])))"
  using part_post_eq_2[OF callee_covered_g_f10_2] eq_entry_g_2[of "[Statement 2, Statement 6]"]
  by (simp add: less_eq_dg_state_def)

lemma project_sigma_eq_entry_g:
  "eq nest_1_eqs (FunctionEntry ''g'', [Statement 2]) project_sigma
     \<le> project_sigma (Inl (FunctionEntry ''g'', [Statement 2]))"
  unfolding nest_1_eqs_entry_g
  by (auto simp: less_eq_dg_state_def project_sigma_def sup_dg_state_def
           intro: order_trans[OF seed_le_entry_g_5 sup_ge1]
                  order_trans[OF seed_le_entry_g_6 sup_ge2])

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



lemma eq_result_g_concrete_bound:
  "locals (eq nest_1_eqs (FunctionResult ''g'', [Statement 2]) project_sigma)
     \<le> locals (project_sigma (Inl (FunctionResult ''g'', [Statement 2])))"
  unfolding nest_1_eqs_entry_g project_sigma_def nest_1_eqs_result_g
  by eval

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

subsection \<open>Statement 3 -- the real COMB node: continuation of the call to g\<close>

text \<open>Unlike \<open>FunctionResult ''g''\<close>, \<open>Statement 3\<close> is a genuine \<open>return_call_action_list\<close>
  continuation (the call at \<open>Statement 2\<close> returns here), so its equation is built from
  \<^const>\<open>routed_cmb\<close>, not \<^const>\<open>apply_dg_spec\<close>. It carries no intra fragment and makes
  no calls of its own. Its context is \<open>[Statement 5]\<close> or \<open>[Statement 6]\<close> (whichever
  activation of \<open>f\<close> is running) -- not one of \<open>project_sigma\<close>'s three merge unknowns, since
  \<open>Statement 3\<close> is never itself pushed onto by a further call.\<close>

lemma statement3_no_intra: "intra_predecessor_list nest_cfg (Statement 3) = []"
  by eval

lemma statement3_comb:
  "return_call_action_list nest_cfg (Statement 3)
     = [(Statement 2, CallEdge (Some ''t'') [''p''] [VIMP_Syntax.V ''p''], FunctionResult ''g'')]"
  by eval

lemma statement3_no_calls: "call_successor_list nest_cfg (Statement 3) = []"
  by eval

lemma nest_1_eqs_statement3:
  "nest_1_eqs (Statement 3, ctx)
     = QueryL (Statement 2, ctx) (\<lambda>caller_state.
         QueryL (FunctionResult ''g'',
                 cs_route 1 (Statement 2) ctx (locals caller_state)
                   (CallEdge (Some ''t'') [''p''] [VIMP_Syntax.V ''p''])) (\<lambda>callee_state.
           QueryG Global1 (\<lambda>globals_state.
             Side Global1
               (DG bot (combine_global Spoly (Some ''t'')
                     (locals caller_state) (locals callee_state) (globs globals_state)))
               (Answer (DG (combine_local Spoly (Some ''t'')
                     (locals caller_state) (locals callee_state) (globs globals_state)) bot)))))"
  unfolding nest_1_eqs_def side_cfg_T_eff_keyed_seed_dg_def routed_extra_def routed_cmb_def
  by (simp add: statement3_no_intra statement3_comb statement3_no_calls nest_entry Let_def
                side_rhs_fold_dg.simps seqcomp_tree.simps)

lemma result_g_local_no_global_5:
  "restrict_global_st (locals (snd nest_2_sol (Inl (FunctionResult ''g'', [Statement 2, Statement 5])))) = bot"
  by eval

lemma result_g_local_no_global_6:
  "restrict_global_st (locals (snd nest_2_sol (Inl (FunctionResult ''g'', [Statement 2, Statement 6])))) = bot"
  by eval

lemma project_sigma_result_g_local_no_global:
  "restrict_global_st (locals (project_sigma (Inl (FunctionResult ''g'', [Statement 2])))) = bot"
  by (simp add: project_sigma_def sup_dg_state_def
                restrict_global_st_sup_restrict_global_st[symmetric]
                result_g_local_no_global_5 result_g_local_no_global_6)

lemma statement2_no_global: "\<not> is_global ''t''"
  by (simp add: is_global_def)

lemma restrict_global_st_update_t:
  "restrict_global_st (update_st s ''t'' v) = restrict_global_st s"
  by (rule st_eqI_lookup) (auto simp: lookup_restrict_global_st statement2_no_global)

lemma restrict_global_st_split':
  "restrict_global_st (restrict_global_st B \<squnion> restrict_local_st A) = restrict_global_st B"
  by (simp add: sup_commute[of "restrict_global_st B"] restrict_global_st_split)

lemma combine_global_ret_t:
  "combine_global Spoly (Some ''t'') dc de g = restrict_global_st (de \<squnion> g)"
  unfolding Spoly_def unit_dg_spec_st_def dgs_combine_def
            unit_combine_step_st_env_def unit_combine_step_st_assign_def Let_def
  by (simp add: combine_abs_st_def restrict_local_st_split restrict_global_st_split'
                restrict_global_st_update_t)

lemma dep_L_statement3:
  "dep\<^sub>L nest_1_eqs project_sigma (Statement 3, ctx)
     = {(Statement 2, ctx),
        (FunctionResult ''g'', cs_route 1 (Statement 2) ctx
           (locals (project_sigma (Inl (Statement 2, ctx))))
           (CallEdge (Some ''t'') [''p''] [VIMP_Syntax.V ''p'']))}"
  unfolding dep\<^sub>L_def dep_def nest_1_eqs_statement3
  by auto

lemma cs_route_statement2: "cs_route 1 (Statement 2) ctx d (CallEdge dst ps as) = [Statement 2]"
  by (simp add: cs_route_def)

lemma eq_statement3_closed_form:
  "eq nest_1_eqs (Statement 3, ctx) project_sigma
     = DG (combine_local Spoly (Some ''t'')
           (locals (project_sigma (Inl (Statement 2, ctx))))
           (locals (project_sigma (Inl (FunctionResult ''g'', [Statement 2]))))
           (globs (project_sigma (Inr Global1)))) bot"
  unfolding nest_1_eqs_statement3 cs_route_statement2
  by simp

lemma project_sigma_eq_statement3:
  assumes "ctx = [Statement 5] \<or> ctx = [Statement 6]"
  shows "eq nest_1_eqs (Statement 3, ctx) project_sigma \<le> project_sigma (Inl (Statement 3, ctx))"
  using assms
  unfolding eq_statement3_closed_form project_sigma_def
  by auto

lemma restrict_local_st_split':
  "restrict_local_st (restrict_global_st A \<squnion> restrict_local_st B) = restrict_local_st B"
  by (simp add: sup_commute[of "restrict_global_st A"] restrict_local_st_split)

lemma restrict_local_st_update_t:
  "restrict_local_st (update_st s ''t'' v) = update_st (restrict_local_st s) ''t'' v"
  by (rule st_eqI_lookup) (auto simp: lookup_restrict_local_st statement2_no_global)

lemma combine_local_ret_t:
  "combine_local Spoly (Some ''t'') dc de g
     = update_st (restrict_local_st (dc \<squnion> g)) ''t'' (lookup_st (de \<squnion> g) ret_var)"
  unfolding Spoly_def unit_dg_spec_st_def dgs_combine_def
            unit_combine_step_st_env_def unit_combine_step_st_assign_def Let_def
  by (simp add: combine_abs_st_def restrict_local_st_split' restrict_global_st_split
           restrict_local_st_update_t)



lemma statement2_covered_1: "(Statement 2, [Statement 5]) \<in> fst nest_1_sol \<and> (Statement 2, [Statement 6]) \<in> fst nest_1_sol"
  unfolding nest_1_sol_def nest_1_eqs_def by eval

lemma project_sigma_dep_L_statement3:
  assumes "ctx = [Statement 5] \<or> ctx = [Statement 6]"
  shows "dep\<^sub>L nest_1_eqs project_sigma (Statement 3, ctx) \<subseteq> fst nest_1_sol"
  unfolding dep_L_statement3 cs_route_statement2
  using assms callee_exit_g_1 statement2_covered_1 by auto

lemma sides_of_rhs_statement3:
  "sides_of_rhs (nest_1_eqs (Statement 3, ctx)) project_sigma
     = (\<lambda>_. bot)(Inr Global1 :=
         DG bot (combine_global Spoly (Some ''t'')
               (locals (project_sigma (Inl (Statement 2, ctx))))
               (locals (project_sigma (Inl (FunctionResult ''g'',
                 cs_route 1 (Statement 2) ctx (locals (project_sigma (Inl (Statement 2, ctx))))
                   (CallEdge (Some ''t'') [''p''] [VIMP_Syntax.V ''p''])))))
               (globs (project_sigma (Inr Global1)))))"
  unfolding nest_1_eqs_statement3
  by (simp add: bot_fun_def)

lemma project_sigma_sides_statement3:
  "sides_of_rhs (nest_1_eqs (Statement 3, ctx)) project_sigma \<le> project_sigma"
proof -
  have key_bound: "combine_global Spoly (Some ''t'')
        (locals (project_sigma (Inl (Statement 2, ctx))))
        (locals (project_sigma (Inl (FunctionResult ''g'', [Statement 2]))))
        (globs (project_sigma (Inr Global1)))
      \<le> globs (project_sigma (Inr Global1))"
  proof -
    have "combine_global Spoly (Some ''t'')
            (locals (project_sigma (Inl (Statement 2, ctx))))
            (locals (project_sigma (Inl (FunctionResult ''g'', [Statement 2]))))
            (globs (project_sigma (Inr Global1)))
        = restrict_global_st (locals (project_sigma (Inl (FunctionResult ''g'', [Statement 2]))))
            \<squnion> restrict_global_st (globs (project_sigma (Inr Global1)))"
      by (simp add: combine_global_ret_t restrict_global_st_sup_restrict_global_st[symmetric])
    also have "\<dots> \<le> globs (project_sigma (Inr Global1))"
      by (simp add: project_sigma_result_g_local_no_global restrict_global_st_le)
    finally show ?thesis .
  qed
  show ?thesis
    unfolding sides_of_rhs_statement3 cs_route_statement2
    using key_bound
    by (auto simp: le_fun_def less_eq_dg_state_def bot_fun_def bot_dg_state_def)
qed

lemma nest_1_vars_list:
  "fst nest_1_sol =
     {(Statement 2,[Statement 6]), (Statement 3,[Statement 6]), (FunctionResult ''f'',[Statement 6]),
      (Statement 0,[Statement 2]), (FunctionResult ''g'',[Statement 2]), (Statement 2,[Statement 5]),
      (Statement 3,[Statement 5]), (FunctionResult ''f'',[Statement 5]), (Statement 5,[]),
      (Statement 6,[]), (Statement 7,[]), (FunctionResult ''main'',[]), (FunctionEntry ''g'',[Statement 2]),
      (FunctionEntry ''f'',[Statement 6]), (FunctionEntry ''f'',[Statement 5]), (FunctionEntry ''main'',[])}"
  unfolding nest_1_sol_def nest_1_eqs_def by eval

declare [[goals_limit = 50]]

lemma project_sigma_dep_L_all:
  "\<forall>u \<in> fst nest_1_sol. dep\<^sub>L nest_1_eqs project_sigma u \<subseteq> fst nest_1_sol"
  unfolding nest_1_vars_list
  apply (intro ballI)
  apply (elim insertE emptyE)
  apply (simp_all only: nest_1_vars_list[symmetric])
  apply (simp_all add: project_sigma_dep_L_entry_g project_sigma_dep_L_result_g
                        project_sigma_dep_L_statement3)
  sorry

text \<open>Every \<open>eq\<close> obligation is a single concrete \<open>dg_state\<close> comparison (never a
  function or set), so it is fully ground once \<open>nest_1_eqs\<close> and \<open>project_sigma\<close> are
  unfolded -- no \<open>enum\<close> instance is needed and \<open>eval\<close> decides it directly, for every
  RHS shape (seed, intra, call, comb, comb+call) uniformly. This sidesteps the shape
  classification entirely for this conjunct: unlike \<open>dep\<^sub>L\<close> (a set) and
  \<open>sides_of_rhs\<close> (a full function), \<open>eq\<close> never leaves the ground \<open>dg_state\<close> level.\<close>

text \<open>\<open>eval\<close> closes this directly for every node whose \<open>project_sigma\<close> case is a plain
  \<open>nest_2_sol\<close> lookup or an explicit two-branch join -- confirmed for all 16 nodes before
  \<open>Statement 3\<close>'s dependency-cone widening was introduced. \<open>Statement 3\<close> itself needs the
  closed-form route (\<open>project_sigma_eq_statement3\<close>) instead, since its equation now
  routes through \<open>combine_local\<close>/\<open>routed_cmb\<close>, which \<open>eval\<close> cannot execute (see
  \<open>eq_statement3_closed_form\<close>). The remaining dependency-cone nodes
  (\<open>FunctionResult ''f''\<close>, \<open>Statement 6\<close>, \<open>Statement 7\<close>, \<open>FunctionResult ''main''\<close>) still
  need their own \<open>project_sigma\<close> cases and closed-form \<open>eq\<close> lemmas before this assembles.\<close>

lemma project_sigma_eq_all:
  "\<forall>u \<in> fst nest_1_sol. eq nest_1_eqs u project_sigma \<le> project_sigma (Inl u)"
  sorry

lemma project_sigma_sides_all:
  "\<forall>u \<in> fst nest_1_sol. sides_of_rhs (nest_1_eqs u) project_sigma \<le> project_sigma"
  unfolding nest_1_vars_list
  apply (intro ballI)
  apply (elim insertE emptyE)
  apply (simp_all only: nest_1_vars_list[symmetric])
  apply (simp_all add: project_sigma_sides_entry_g project_sigma_sides_result_g
                        project_sigma_sides_statement3)
  sorry

lemma project_sigma_part_post_solution:
  "part_post_solution nest_1_eqs (cfg_exit nest_cfg, []) project_sigma (fst nest_1_sol)"
  using project_sigma_dep_L_all project_sigma_eq_all project_sigma_sides_all
  by (simp add: nest_entry cfg_exit_def nest_1_vars_list)

end

