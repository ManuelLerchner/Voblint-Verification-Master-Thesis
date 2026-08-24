theory Call_String_Solver_Regression
  imports Example_Interval_DG_CallString_K2
begin

section \<open>Exact equation-tree snapshots\<close>

text \<open>Regression coverage for the shape \<^const>\<open>DG_Framework.side_cfg_T_eff_keyed_seed_dg\<close>
  generates at a genuine \<^const>\<open>routed_cmb_g\<close> continuation, at both k=1 and k=2: this locks
  in that the routed context (\<open>cs_route k\<close>), the seed publication, and the callee-exit read
  all still live in \<open>Statement 3\<close>'s own equation, not in the call site's, and that the seed
  payload rides the \<^const>\<open>locals\<close> half of the published \<^type>\<open>dg_state\<close> while the shared
  \<open>Global\<close> slot keeps its own \<^const>\<open>globs\<close> half. The closed forms also pin the entered
  callee frame down to one occurrence: the context, the seed payload and the callee-exit
  key all read \<open>enter_local nest_S_st\<close> applied to the same caller state \<^emph>\<open>and\<close> the same
  \<open>Global\<close> value. The site is a single tree: the caller state and \<open>Global\<close> are read
  once, the resolver names the callees, and \<^const>\<open>side_rhs_fold_dg\<close> folds their
  contributions. \<open>Call_String_Solver_Refinement_Seeded\<close>'s
  generic refinement proof never needs these closed forms -- they only guard against silent
  regressions in \<^const>\<open>routed_cmb_g\<close>/\<^const>\<open>side_cfg_T_eff_keyed_seed_dg\<close> generation
  itself.\<close>

lemma statement3_no_intra: "intra_predecessor_list nest_cfg (Statement 3) = []"
  by eval

lemma statement3_comb:
  "call_site_list nest_cfg (Statement 3)
     = [(Statement 2, CallEdge (Some (STR ''t'')) [(STR ''p'')] [VIMP_Syntax.V (STR ''p'')])]"
  by eval

lemma statement3_targets:
  "static_resolve nest_cfg (Statement 3) (Statement 2)
       (CallEdge (Some (STR ''t'')) [(STR ''p'')] [VIMP_Syntax.V (STR ''p'')]) d
     = [STR ''g'']"
  unfolding static_resolve_def by eval

lemma statement3_no_calls: "call_successor_list nest_cfg (Statement 3) = []"
  by eval

text \<open>The call metadata the continuation is pinned to: built from the call edge
  and the callee that \<^const>\<open>routed_cmb_g\<close> reads off the exit node, not from a
  destination guessed at the return.\<close>

abbreviation nest_ci :: call_info where
  "nest_ci \<equiv>
     call_info_of (CallEdge (Some (STR ''t'')) [(STR ''p'')] [VIMP_Syntax.V (STR ''p'')])
       (STR ''g'')"

lemma nest_2_eqs_statement3:
  "nest_2_eqs (Statement 3, ctx)
     = read_local_cont (Statement 2, ctx) (\<lambda>caller_state.
         read_global_cont Global (\<lambda>globals_state1.
           side_rhs_fold_dg bot
             [depend_on (Seed (FunctionEntry (STR ''g''))
                     (cs_route 2 (Statement 2) ctx
                       (enter_local nest_S_st [(STR ''p'')] [VIMP_Syntax.V (STR ''p'')]
                          (locals caller_state) (globs globals_state1))
                       (CallEdge (Some (STR ''t'')) [(STR ''p'')] [VIMP_Syntax.V (STR ''p'')])))
                (DG (enter_local nest_S_st [(STR ''p'')] [VIMP_Syntax.V (STR ''p'')]
                      (locals caller_state) (globs globals_state1)) Bot)
                (read_local_cont (FunctionResult (STR ''g''),
                        cs_route 2 (Statement 2) ctx
                          (enter_local nest_S_st [(STR ''p'')] [VIMP_Syntax.V (STR ''p'')]
                             (locals caller_state) (globs globals_state1))
                          (CallEdge (Some (STR ''t'')) [(STR ''p'')] [VIMP_Syntax.V (STR ''p'')]))
                    (\<lambda>callee_state.
                  read_global_cont Global (\<lambda>globals_state2.
                    depend_on Global
                      (DG Bot (enter_global nest_S_st [(STR ''p'')] [VIMP_Syntax.V (STR ''p'')]
                            (locals caller_state) (globs globals_state1)
                          \<squnion> combine_global nest_S_st nest_ci
                             (caller_cont nest_S_st nest_ci (locals caller_state) (globs globals_state1))
                             (locals callee_state) (globs globals_state2)))
                     (answer (DG (combine_local nest_S_st nest_ci
                           (caller_cont nest_S_st nest_ci (locals caller_state) (globs globals_state1))
                           (locals callee_state) (globs globals_state2)) Bot)))))]))"
  unfolding nest_2_eqs_def side_cfg_T_eff_keyed_seed_dg_def routed_extra_g_def
    routed_cmb_g_def routed_cmb_g_at_def
  by (simp add: intra_predecessor_addr_list_def statement3_no_intra statement3_comb
        statement3_targets statement3_no_calls nest_entry Let_def)

lemma nest_1_eqs_statement3:
  "nest_1_eqs (Statement 3, ctx)
     = read_local_cont (Statement 2, ctx) (\<lambda>caller_state.
         read_global_cont Global (\<lambda>globals_state1.
           side_rhs_fold_dg bot
             [depend_on (Seed (FunctionEntry (STR ''g''))
                     (cs_route 1 (Statement 2) ctx
                       (enter_local nest_S_st [(STR ''p'')] [VIMP_Syntax.V (STR ''p'')]
                          (locals caller_state) (globs globals_state1))
                       (CallEdge (Some (STR ''t'')) [(STR ''p'')] [VIMP_Syntax.V (STR ''p'')])))
                (DG (enter_local nest_S_st [(STR ''p'')] [VIMP_Syntax.V (STR ''p'')]
                      (locals caller_state) (globs globals_state1)) Bot)
                (read_local_cont (FunctionResult (STR ''g''),
                        cs_route 1 (Statement 2) ctx
                          (enter_local nest_S_st [(STR ''p'')] [VIMP_Syntax.V (STR ''p'')]
                             (locals caller_state) (globs globals_state1))
                          (CallEdge (Some (STR ''t'')) [(STR ''p'')] [VIMP_Syntax.V (STR ''p'')]))
                    (\<lambda>callee_state.
                  read_global_cont Global (\<lambda>globals_state2.
                    depend_on Global
                      (DG Bot (enter_global nest_S_st [(STR ''p'')] [VIMP_Syntax.V (STR ''p'')]
                            (locals caller_state) (globs globals_state1)
                          \<squnion> combine_global nest_S_st nest_ci
                             (caller_cont nest_S_st nest_ci (locals caller_state) (globs globals_state1))
                             (locals callee_state) (globs globals_state2)))
                     (answer (DG (combine_local nest_S_st nest_ci
                           (caller_cont nest_S_st nest_ci (locals caller_state) (globs globals_state1))
                           (locals callee_state) (globs globals_state2)) Bot)))))]))"
  unfolding nest_1_eqs_def side_cfg_T_eff_keyed_seed_dg_def routed_extra_g_def
    routed_cmb_g_def routed_cmb_g_at_def
  by (simp add: intra_predecessor_addr_list_def statement3_no_intra statement3_comb
        statement3_targets statement3_no_calls nest_entry Let_def)

end

