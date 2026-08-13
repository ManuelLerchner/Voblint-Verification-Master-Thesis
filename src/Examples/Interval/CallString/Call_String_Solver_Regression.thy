theory Call_String_Solver_Regression
  imports Example_Interval_DG_CallString_K2
begin

section \<open>Exact equation-tree snapshots\<close>

text \<open>Regression coverage for the shape \<^const>\<open>DG_Framework.side_cfg_T_eff_keyed_seed_dg\<close>
  generates at a genuine \<^const>\<open>routed_cmb\<close> continuation, at both k=1 and k=2: this locks
  in that the routed context (\<open>cs_route k\<close>), the seed-publish, and the callee-exit read all
  still live in \<open>Statement 3\<close>'s own equation (candidate B's whole-call-lifecycle design,
  \<open>#114\<close>), not in the call site's. \<open>Call_String_Solver_Refinement_Seeded.thy\<close>'s generic
  refinement proof never needs these closed forms -- they only guard against silent
  regressions in \<^const>\<open>routed_cmb\<close>/\<^const>\<open>side_cfg_T_eff_keyed_seed_dg\<close> generation
  itself.\<close>

lemma statement3_no_intra: "intra_predecessor_list nest_cfg (Statement 3) = []"
  by eval

lemma statement3_comb:
  "return_call_action_list nest_cfg (Statement 3)
     = [(Statement 2, CallEdge (Some (STR ''t'')) [(STR ''p'')] [VIMP_Syntax.V (STR ''p'')], FunctionResult (STR ''g''))]"
  by eval

lemma statement3_no_calls: "call_successor_list nest_cfg (Statement 3) = []"
  by eval

lemma nest_2_eqs_statement3:
  "nest_2_eqs (Statement 3, ctx)
     = QueryL (Statement 2, ctx) (\<lambda>caller_state.
         QueryG Global (\<lambda>globals_state1.
           Side (Seed (FunctionEntry (STR ''g''))
                   (cs_route 2 (Statement 2) ctx (locals caller_state)
                     (CallEdge (Some (STR ''t'')) [(STR ''p'')] [VIMP_Syntax.V (STR ''p'')])))
             (DG bot (enter_local Spoly [(STR ''p'')] [VIMP_Syntax.V (STR ''p'')]
                   (locals caller_state) (globs globals_state1)))
             (QueryL (FunctionResult (STR ''g''),
                     cs_route 2 (Statement 2) ctx (locals caller_state)
                       (CallEdge (Some (STR ''t'')) [(STR ''p'')] [VIMP_Syntax.V (STR ''p'')])) (\<lambda>callee_state.
               QueryG Global (\<lambda>globals_state2.
                 Side Global
                   (DG bot (enter_global Spoly [(STR ''p'')] [VIMP_Syntax.V (STR ''p'')]
                         (locals caller_state) (globs globals_state1)
                       \<squnion> combine_global Spoly (Some (STR ''t''))
                           (locals caller_state) (locals callee_state) (globs globals_state2)))
                   (Answer (DG (combine_local Spoly (Some (STR ''t''))
                         (locals caller_state) (locals callee_state) (globs globals_state2)) bot)))))))"
  unfolding nest_2_eqs_def side_cfg_T_eff_keyed_seed_dg_def routed_extra_def routed_cmb_def
  by (simp add: statement3_no_intra statement3_comb statement3_no_calls nest_entry Let_def)

lemma nest_1_eqs_statement3:
  "nest_1_eqs (Statement 3, ctx)
     = QueryL (Statement 2, ctx) (\<lambda>caller_state.
         QueryG Global (\<lambda>globals_state1.
           Side (Seed (FunctionEntry (STR ''g''))
                   (cs_route 1 (Statement 2) ctx (locals caller_state)
                     (CallEdge (Some (STR ''t'')) [(STR ''p'')] [VIMP_Syntax.V (STR ''p'')])))
             (DG bot (enter_local Spoly [(STR ''p'')] [VIMP_Syntax.V (STR ''p'')]
                   (locals caller_state) (globs globals_state1)))
             (QueryL (FunctionResult (STR ''g''),
                     cs_route 1 (Statement 2) ctx (locals caller_state)
                       (CallEdge (Some (STR ''t'')) [(STR ''p'')] [VIMP_Syntax.V (STR ''p'')])) (\<lambda>callee_state.
               QueryG Global (\<lambda>globals_state2.
                 Side Global
                   (DG bot (enter_global Spoly [(STR ''p'')] [VIMP_Syntax.V (STR ''p'')]
                         (locals caller_state) (globs globals_state1)
                       \<squnion> combine_global Spoly (Some (STR ''t''))
                           (locals caller_state) (locals callee_state) (globs globals_state2)))
                   (Answer (DG (combine_local Spoly (Some (STR ''t''))
                         (locals caller_state) (locals callee_state) (globs globals_state2)) bot)))))))"
  unfolding nest_1_eqs_def side_cfg_T_eff_keyed_seed_dg_def routed_extra_def routed_cmb_def
  by (simp add: statement3_no_intra statement3_comb statement3_no_calls nest_entry Let_def)

end
