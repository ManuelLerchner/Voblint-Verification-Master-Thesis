theory Call_String_Solver_Regression
  imports Example_Interval_DG_CallString_K2
begin

section \<open>Exact equation-tree snapshots\<close>

text \<open>Regression coverage for the shape \<^const>\<open>DG_Keyed_Generator.routed_node_rhs\<close>
  generates at a genuine \<^const>\<open>routed_call_tree\<close> continuation, at both k=1 and k=2: this locks
  in that the whole call boundary --- the routed context (\<open>cs_route k\<close>), the seed
  publication and the callee-exit read, all packaged by
  \<^const>\<open>routed_call_alternative_tree\<close> --- still lives in \<open>Statement 3\<close>'s own equation, not in the
  call site's. The closed forms pin the alternative the call runs on: exactly one, whose
  continuation half is the caller state itself and whose callee-entry half is
  \<^const>\<open>nest_S_st\<close>'s own entry transfer applied to it. The site is a single tree: the
  caller state is read once by the outer \<^const>\<open>QueryL\<close>, the resolver names the callees,
  and their contributions are folded. Because the transfers are manager-native, the call
  site itself issues no \<open>Global\<close> read --- one appears only if the spec's own enter or
  combine transfer asks for it. These closed forms guard against silent regressions in
  \<^const>\<open>routed_call_tree\<close>/\<^const>\<open>routed_node_rhs\<close> generation itself.\<close>

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
  and the callee that \<^const>\<open>routed_call_tree\<close> reads off the exit node, not from a
  destination guessed at the return.\<close>

abbreviation nest_ci :: call_info where
  "nest_ci \<equiv>
     call_info_of (CallEdge (Some (STR ''t'')) [(STR ''p'')] [VIMP_Syntax.V (STR ''p'')])
       (STR ''g'')"

lemma nest_2_eqs_statement3:
  "nest_2_eqs (Statement 3, ctx)
     = QueryL (Statement 2, ctx)
         (\<lambda>d. sp_lift_tree (sp_lift_tree (sp_lift_tree
                 (routed_call_alternative_tree nest_S_st Global Seed (cs_route 2) (\<lambda>x. x = Bot) ctx
                    (CallEdge (Some (STR ''t'')) [(STR ''p'')] [VIMP_Syntax.V (STR ''p'')])
                    (Statement 2) (STR ''g'')
                    (locals d,
                     transfer_lift nest_empty_pred (ivl_enter_st_for nest_gs nest_ci) (locals d)))
                 (\<lambda>res. Answer (DG (locals res) Bot)))
               (\<lambda>res. Answer (DG (locals res) Bot)))
             (\<lambda>res. Answer (DG (locals res) Bot)))"
  unfolding nest_2_eqs_def routed_node_rhs_def routed_contribution_trees_def
    routed_entry_seed_tree_def
    routed_call_tree_def routed_callee_call_tree_def nest_S_st_def dgs_enter_local_state_st_for_lifted
  by (simp add: intra_predecessor_addr_list_def statement3_no_intra statement3_comb
        statement3_targets statement3_no_calls nest_entry Let_def
        sp_compile_def sp_compile_with_bind sp_bind_def sp_return_def local_enter_transfer_def)

lemma nest_1_eqs_statement3:
  "nest_1_eqs (Statement 3, ctx)
     = QueryL (Statement 2, ctx)
         (\<lambda>d. sp_lift_tree (sp_lift_tree (sp_lift_tree
                 (routed_call_alternative_tree nest_S_st Global Seed (cs_route 1) (\<lambda>x. x = Bot) ctx
                    (CallEdge (Some (STR ''t'')) [(STR ''p'')] [VIMP_Syntax.V (STR ''p'')])
                    (Statement 2) (STR ''g'')
                    (locals d,
                     transfer_lift nest_empty_pred (ivl_enter_st_for nest_gs nest_ci) (locals d)))
                 (\<lambda>res. Answer (DG (locals res) Bot)))
               (\<lambda>res. Answer (DG (locals res) Bot)))
             (\<lambda>res. Answer (DG (locals res) Bot)))"
  unfolding nest_1_eqs_def routed_node_rhs_def routed_contribution_trees_def
    routed_entry_seed_tree_def
    routed_call_tree_def routed_callee_call_tree_def nest_S_st_def dgs_enter_local_state_st_for_lifted
  by (simp add: intra_predecessor_addr_list_def statement3_no_intra statement3_comb
        statement3_targets statement3_no_calls nest_entry Let_def
        sp_compile_def sp_compile_with_bind sp_bind_def sp_return_def local_enter_transfer_def)

end

