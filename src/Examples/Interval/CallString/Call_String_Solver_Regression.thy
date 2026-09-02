theory Call_String_Solver_Regression
  imports Example_Interval_DG_CallString_K2
begin

section \<open>Exact equation-tree snapshots\<close>

text \<open>Regression coverage for the shape \<^const>\<open>DG_Keyed_Generator.side_cfg_T_eff_keyed_seed_dg\<close>
  generates at a genuine \<^const>\<open>routed_cmb_g\<close> continuation, at both k=1 and k=2: this locks
  in that the routed context (\<open>cs_route k\<close>), the seed publication, and the callee-exit read
  all still live in \<open>Statement 3\<close>'s own equation, not in the call site's, and that the seed
  payload rides the \<^const>\<open>locals\<close> half of the published \<^type>\<open>dg_state\<close> while the shared
  \<open>Global\<close> slot keeps its own \<^const>\<open>globs\<close> half. The closed forms also pin the entered
  callee frame down to one occurrence: the context, the seed payload and the callee-exit
  key all read one entered frame: \<^const>\<open>nest_S_st\<close>'s own \<^const>\<open>dgs_enter\<close>, run against a
  manager built once from the caller state and the \<open>Global\<close> key. The site is a single
  tree: the caller state is read once by the outer \<^const>\<open>QueryL\<close>, the resolver names
  the callees, and their contributions are folded. Because the transfers are
  manager-native, the call site itself issues no \<open>Global\<close> read --- one appears only if
  the spec's own enter or combine transfer asks for it. These closed forms guard against silent
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
     = QueryL (Statement 2, ctx)
         (\<lambda>d. sp_run_with (\<lambda>x. DG x Bot)
                 (dgs_enter nest_S_st nest_ci (mk_dg_man (locals d) (\<lambda>_. Global)))
               \<bind> (\<lambda>entry_state.
                     side_effect
                       (Seed (FunctionEntry (STR ''g''))
                          (cs_route 2 (Statement 2) ctx (locals entry_state)
                            (CallEdge (Some (STR ''t'')) [(STR ''p'')] [VIMP_Syntax.V (STR ''p'')])))
                       (DG (locals entry_state) Bot)
                       (QueryL (FunctionResult (STR ''g''),
                            cs_route 2 (Statement 2) ctx (locals entry_state)
                              (CallEdge (Some (STR ''t'')) [(STR ''p'')]
                                [VIMP_Syntax.V (STR ''p'')]))
                          (\<lambda>da. sp_run_with (\<lambda>x. DG x Bot)
                                  (dg_spec_combine_transfer nest_S_st nest_ci
                                     (mk_dg_man (locals d) (\<lambda>_. Global)) (locals da)))))
               \<bind> (\<lambda>res. answer (DG (locals res) Bot))
               \<bind> (\<lambda>res. answer (DG (locals res) Bot)))"
  unfolding nest_2_eqs_def side_cfg_T_eff_keyed_seed_dg_def routed_extra_g_def
    routed_cmb_g_def routed_cmb_g_at_def
  by (simp add: intra_predecessor_addr_list_def statement3_no_intra statement3_comb
        statement3_targets statement3_no_calls nest_entry Let_def)

lemma nest_1_eqs_statement3:
  "nest_1_eqs (Statement 3, ctx)
     = QueryL (Statement 2, ctx)
         (\<lambda>d. sp_run_with (\<lambda>x. DG x Bot)
                 (dgs_enter nest_S_st nest_ci (mk_dg_man (locals d) (\<lambda>_. Global)))
               \<bind> (\<lambda>entry_state.
                     side_effect
                       (Seed (FunctionEntry (STR ''g''))
                          (cs_route 1 (Statement 2) ctx (locals entry_state)
                            (CallEdge (Some (STR ''t'')) [(STR ''p'')] [VIMP_Syntax.V (STR ''p'')])))
                       (DG (locals entry_state) Bot)
                       (QueryL (FunctionResult (STR ''g''),
                            cs_route 1 (Statement 2) ctx (locals entry_state)
                              (CallEdge (Some (STR ''t'')) [(STR ''p'')]
                                [VIMP_Syntax.V (STR ''p'')]))
                          (\<lambda>da. sp_run_with (\<lambda>x. DG x Bot)
                                  (dg_spec_combine_transfer nest_S_st nest_ci
                                     (mk_dg_man (locals d) (\<lambda>_. Global)) (locals da)))))
               \<bind> (\<lambda>res. answer (DG (locals res) Bot))
               \<bind> (\<lambda>res. answer (DG (locals res) Bot)))"
  unfolding nest_1_eqs_def side_cfg_T_eff_keyed_seed_dg_def routed_extra_g_def
    routed_cmb_g_def routed_cmb_g_at_def
  by (simp add: intra_predecessor_addr_list_def statement3_no_intra statement3_comb
        statement3_targets statement3_no_calls nest_entry Let_def)

end

