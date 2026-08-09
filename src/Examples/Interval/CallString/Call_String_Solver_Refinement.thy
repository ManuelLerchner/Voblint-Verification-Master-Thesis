theory Call_String_Solver_Refinement
  imports Example_Interval_DG_CallString_K2 "Voblint_Core.Context_Refinement"
begin

lemma st_eqI_lookup:
  fixes s t :: "('a::bot) resolved_st_q"
  assumes "\<And>loc. lookup_resolved_st_q s loc = lookup_resolved_st_q t loc"
  shows "s = t"
  using assms
  by (simp add: resolved_st_q_eq_iff fun_eq_iff)

lemma restrict_global_resolved_q_sup_restrict_global_resolved_q:
  fixes s t :: "('a::bounded_semilattice_sup_bot) resolved_st_q"
  shows "restrict_global_resolved_q (s \<squnion> t) =
    restrict_global_resolved_q s \<squnion> restrict_global_resolved_q t"
  apply (rule st_eqI_lookup)
  apply (case_tac loc)
  by (simp_all add: lookup_sup_resolved_st_q)

lemma restrict_local_resolved_q_sup_restrict_local_resolved_q:
  fixes s t :: "('a::bounded_semilattice_sup_bot) resolved_st_q"
  shows "restrict_local_resolved_q (s \<squnion> t) =
    restrict_local_resolved_q s \<squnion> restrict_local_resolved_q t"
  apply (rule st_eqI_lookup)
  apply (case_tac loc)
  by (simp_all add: lookup_sup_resolved_st_q)

text \<open>

  The merge is not a property of a node's own context fiber; it is a property of
  \<^emph>\<open>dependency reachability\<close> from a node whose fiber genuinely splits. \<open>Statement 0\<close>,
  \<open>FunctionResult (STR ''g'')\<close>, and \<open>FunctionEntry (STR ''g'')\<close> have two-element k=2 fibers, because
  \<open>g\<close> is entered from two distinct k=2 call strings that \<open>cs_route\<close> collapses to the same
  k=1 string \<open>[Statement 2]\<close>. Every other node in this witness keeps a singleton fiber
  (its own context never grows past k=1 regardless of \<open>k\<close>) -- but seven of those
  singleton-fiber nodes still transitively \<^emph>\<open>read\<close> a merged unknown, through an intra
  edge or a \<open>routed_cmb\<close> combine: \<open>Statement 3\<close> and \<open>FunctionResult (STR ''f'')\<close> (both contexts,
  since \<open>f\<close>'s call to \<open>g\<close> is the read site), then \<open>Statement 6\<close>, \<open>Statement 7\<close>, and
  \<open>FunctionResult (STR ''main'')\<close> (the chain of \<open>f\<close>-returns downstream of that). Those seven
  need the same widening even though their own fiber never splits, because the k=1
  equation they solve reads a merged dependency through \<^const>\<open>cs_route\<close>'s collapse, while
  a naive k=2 passthrough at their own (unsplit) context would only ever reflect one
  branch. This is the full dependency closure of the three genuinely-split unknowns under
  \<open>intra\<close>/\<open>calls\<close> reachability in \<open>nest_cfg\<close> -- nothing else in the program depends on the
  merge. Each downstream case is defined by re-evaluating its own equation with the
  already-widened dependency substituted in directly (never through a self-reference:
  \<open>definition\<close> cannot recurse), the same construction \<^const>\<open>eq\<close> would perform at that
  node once its inputs are known. \<open>project_sigma_eq_statement3\<close> is the case that exposed
  this pattern, proved by unfolding both sides to the same term; the same treatment
  closes \<open>FunctionResult (STR ''f'')\<close>, \<open>Statement 6\<close>, \<open>Statement 7\<close>, and
  \<open>FunctionResult (STR ''main'')\<close>. The sixteen per-node cases assemble into the headline
  theorem, \<open>project_sigma_part_post_solution\<close>, which keeps \<open>project_sigma\<close> a
  \<^verbatim>\<open>part_post_solution\<close> of \<open>nest_1_eqs\<close>.
\<close>
lemma bind_formals_resolved_q_singleton:
  "bind_formals_resolved_q gs [x] [a] s =
    update_resolved_st_q s (location_of gs x) a"
  by transfer (simp add: bind_formals_resolved_def eq_resolved_st_def)


text \<open>
  Named closed forms for the downstream-cone values, so \<open>project_sigma\<close> plugs in one
  constant per node instead of re-inlining the same subterm at every site that reads it
  (\<open>merged_result_g\<close> alone would otherwise appear once in \<open>project_sigma\<close>'s own
  \<open>FunctionResult (STR ''g'')\<close> case and again inside every downstream case that reads it).
  None of these may mention \<open>project_sigma\<close> itself -- a \<open>definition\<close> cannot recurse --
  so each is built directly from \<open>nest_2_sol\<close> and the constants already defined earlier
  in the chain, mirroring exactly what \<open>eq\<close> would compute at that node once its own inputs are
  fixed.
\<close>

definition merged_result_g :: "(ivl exec_dg_st, ivl exec_dg_st) dg_state" where
  "merged_result_g = snd nest_2_sol (Inl (FunctionResult (STR ''g''), [Statement 2, Statement 5]))
                        \<squnion> snd nest_2_sol (Inl (FunctionResult (STR ''g''), [Statement 2, Statement 6]))"

definition statement3_val :: "cfg_node list \<Rightarrow> (ivl exec_dg_st, ivl exec_dg_st) dg_state" where
  "statement3_val ctx1 = DG (combine_local Spoly (Some (STR ''t''))
        (locals (snd nest_2_sol (Inl (Statement 2, ctx1))))
        (locals merged_result_g)
        (globs (snd nest_2_sol (Inr Global2)))) bot"

definition result_f_val :: "cfg_node list \<Rightarrow> (ivl exec_dg_st, ivl exec_dg_st) dg_state" where
  "result_f_val ctx1 = DG (snd (dg_spec_step Spoly (EA_Ret (Some (VIMP_Syntax.V (STR ''t''))) (STR ''f''))
        (locals (statement3_val ctx1)) (globs (snd nest_2_sol (Inr Global2))))) bot"

definition statement6_val :: "(ivl exec_dg_st, ivl exec_dg_st) dg_state" where
  "statement6_val = DG (combine_local Spoly (Some (STR ''x''))
        (locals (snd nest_2_sol (Inl (Statement 5, []))))
        (locals (result_f_val [Statement 5]))
        (globs (snd nest_2_sol (Inr Global2)))) bot"

definition statement7_val :: "(ivl exec_dg_st, ivl exec_dg_st) dg_state" where
  "statement7_val = DG (combine_local Spoly (Some (STR ''y''))
        (locals statement6_val)
        (locals (result_f_val [Statement 6]))
        (globs (snd nest_2_sol (Inr Global2)))) bot"

definition result_main_val :: "(ivl exec_dg_st, ivl exec_dg_st) dg_state" where
  "result_main_val = DG (snd (dg_spec_step Spoly (EA_Ret None (STR ''main''))
        (locals statement7_val) (globs (snd nest_2_sol (Inr Global2))))) bot"

definition project_sigma :: "pp \<times> cfg_node list + gk_1 \<Rightarrow> (ivl exec_dg_st, ivl exec_dg_st) dg_state" where
  "project_sigma x =
     (case x of
        Inl (v, ctx1) \<Rightarrow>
          (if (v, ctx1) = (Statement 0, [Statement 2]) then
             snd nest_2_sol (Inl (Statement 0, [Statement 2, Statement 5]))
               \<squnion> snd nest_2_sol (Inl (Statement 0, [Statement 2, Statement 6]))
           else if (v, ctx1) = (FunctionResult (STR ''g''), [Statement 2]) then merged_result_g
           else if (v, ctx1) = (FunctionEntry (STR ''g''), [Statement 2]) then
             snd nest_2_sol (Inl (FunctionEntry (STR ''g''), [Statement 2, Statement 5]))
               \<squnion> snd nest_2_sol (Inl (FunctionEntry (STR ''g''), [Statement 2, Statement 6]))
           else if (v, ctx1) = (Statement 3, [Statement 5]) \<or> (v, ctx1) = (Statement 3, [Statement 6]) then
             statement3_val ctx1
           else if (v, ctx1) = (FunctionResult (STR ''f''), [Statement 5])
                 \<or> (v, ctx1) = (FunctionResult (STR ''f''), [Statement 6]) then
             result_f_val ctx1
           else if (v, ctx1) = (Statement 6, []) then statement6_val
           else if (v, ctx1) = (Statement 7, []) then statement7_val
           else if (v, ctx1) = (FunctionResult (STR ''main''), []) then result_main_val
           else snd nest_2_sol (Inl (v, ctx1)))
      | Inr Global1 \<Rightarrow> snd nest_2_sol (Inr Global2)
      | Inr (Seed1 v ctx1) \<Rightarrow>
          (if (v, ctx1) = (FunctionEntry (STR ''g''), [Statement 2]) then
             snd nest_2_sol (Inr (Seed2 v [Statement 2, Statement 5]))
               \<squnion> snd nest_2_sol (Inr (Seed2 v [Statement 2, Statement 6]))
           else snd nest_2_sol (Inr (Seed2 v ctx1))))"

subsection \<open>FunctionEntry g -- pure seed read, no intra, no comb\<close>

lemma entry_g_no_intra: "intra_predecessor_list nest_cfg (FunctionEntry (STR ''g'')) = []"
  by eval

lemma entry_g_no_return: "return_call_action_list nest_cfg (FunctionEntry (STR ''g'')) = []"
  by eval

lemma entry_g_no_calls: "call_successor_list nest_cfg (FunctionEntry (STR ''g'')) = []"
  by eval

lemma nest_1_eqs_entry_g:
  "nest_1_eqs (FunctionEntry (STR ''g''), [Statement 2])
     = QueryG (Seed1 (FunctionEntry (STR ''g'')) [Statement 2]) (\<lambda>d. answer_local (globs d))"
  unfolding nest_1_eqs_def side_cfg_T_eff_keyed_seed_dg_def routed_extra_def
  by (simp add: entry_g_no_intra entry_g_no_return entry_g_no_calls nest_entry
                side_rhs_fold_dg.simps seqcomp_tree.simps)

lemma dep_L_entry_g:
  "dep\<^sub>L nest_1_eqs project_sigma (FunctionEntry (STR ''g''), [Statement 2]) = {}"
  unfolding dep\<^sub>L_def dep_def nest_1_eqs_entry_g
  by simp

lemma sides_of_rhs_entry_g:
  "sides_of_rhs (nest_1_eqs (FunctionEntry (STR ''g''), [Statement 2])) project_sigma = bot"
  unfolding nest_1_eqs_entry_g
  by (simp add: bot_fun_def)

lemma project_sigma_dep_L_entry_g:
  "dep\<^sub>L nest_1_eqs project_sigma (FunctionEntry (STR ''g''), [Statement 2]) \<subseteq> fst nest_1_sol"
  by (simp add: dep_L_entry_g)

lemma project_sigma_sides_entry_g:
  "sides_of_rhs (nest_1_eqs (FunctionEntry (STR ''g''), [Statement 2])) project_sigma \<le> project_sigma"
  by (simp add: sides_of_rhs_entry_g)

lemma part_post_eq_2:
  assumes "u \<in> fst nest_2_sol"
  shows "eq nest_2_eqs u (snd nest_2_sol) \<le> snd nest_2_sol (Inl u)"
  using nest_2_pp_st assms by blast

lemma nest_2_eqs_entry_g:
  assumes "ctx = [Statement 2, Statement 5] \<or> ctx = [Statement 2, Statement 6]"
  shows "nest_2_eqs (FunctionEntry (STR ''g''), ctx)
     = QueryG (Seed2 (FunctionEntry (STR ''g'')) ctx) (\<lambda>d. answer_local (globs d))"
  using assms
  unfolding nest_2_eqs_def side_cfg_T_eff_keyed_seed_dg_def routed_extra_def
  by (auto simp: entry_g_no_intra entry_g_no_return entry_g_no_calls nest_entry
                 side_rhs_fold_dg.simps seqcomp_tree.simps)

lemma eq_entry_g_2:
  assumes "ctx = [Statement 2, Statement 5] \<or> ctx = [Statement 2, Statement 6]"
  shows "eq nest_2_eqs (FunctionEntry (STR ''g''), ctx) (snd nest_2_sol)
       = DG (globs (snd nest_2_sol (Inr (Seed2 (FunctionEntry (STR ''g'')) ctx)))) bot"
  unfolding nest_2_eqs_entry_g[OF assms]
  by simp

lemma seed_le_entry_g_5:
  "globs (snd nest_2_sol (Inr (Seed2 (FunctionEntry (STR ''g'')) [Statement 2, Statement 5])))
     \<le> locals (snd nest_2_sol (Inl (FunctionEntry (STR ''g''), [Statement 2, Statement 5])))"
  using part_post_eq_2[OF callee_covered_g_f3_2] eq_entry_g_2[of "[Statement 2, Statement 5]"]
  by (simp add: less_eq_dg_state_def)

lemma seed_le_entry_g_6:
  "globs (snd nest_2_sol (Inr (Seed2 (FunctionEntry (STR ''g'')) [Statement 2, Statement 6])))
     \<le> locals (snd nest_2_sol (Inl (FunctionEntry (STR ''g''), [Statement 2, Statement 6])))"
  using part_post_eq_2[OF callee_covered_g_f10_2] eq_entry_g_2[of "[Statement 2, Statement 6]"]
  by (simp add: less_eq_dg_state_def)

lemma project_sigma_eq_entry_g:
  "eq nest_1_eqs (FunctionEntry (STR ''g''), [Statement 2]) project_sigma
     \<le> project_sigma (Inl (FunctionEntry (STR ''g''), [Statement 2]))"
  unfolding nest_1_eqs_entry_g
  by (auto simp: less_eq_dg_state_def project_sigma_def sup_dg_state_def
           intro: order_trans[OF seed_le_entry_g_5 sup_ge1]
                  order_trans[OF seed_le_entry_g_6 sup_ge2])

subsection \<open>FunctionResult g -- the return/combine path, per the CFG\<close>

text \<open>\<open>FunctionResult (STR ''g'')\<close> is reached only by the intra return edge from \<open>Statement 0\<close>;
  it is never a \<open>return_call_action_list\<close> continuation, so its equation
  carries no COMB fragment. The actual COMB nodes are the call continuations
  (\<open>Statement 3\<close>, \<open>Statement 6\<close>, \<open>Statement 7\<close>).\<close>

lemma result_g_no_comb: "return_call_action_list nest_cfg (FunctionResult (STR ''g'')) = []"
  by eval

lemma result_g_no_calls: "call_successor_list nest_cfg (FunctionResult (STR ''g'')) = []"
  by eval

lemma result_g_intra:
  "intra_predecessor_list nest_cfg (FunctionResult (STR ''g''))
     = [(Statement 0, EA_Ret (Some (Plus (VIMP_Syntax.V (STR ''p'')) (VIMP_Syntax.V (STR ''p'')))) (STR ''g''))]"
  by eval

lemma nest_1_eqs_result_g:
  "nest_1_eqs (FunctionResult (STR ''g''), [Statement 2])
     = QueryL (Statement 0, [Statement 2]) (\<lambda>d. QueryG Global1 (\<lambda>gv.
         Side Global1
           (DG bot (fst (dg_spec_step Spoly
                 (EA_Ret (Some (Plus (VIMP_Syntax.V (STR ''p'')) (VIMP_Syntax.V (STR ''p'')))) (STR ''g''))
                 (locals d) (globs gv))))
           (Answer (DG (snd (dg_spec_step Spoly
                 (EA_Ret (Some (Plus (VIMP_Syntax.V (STR ''p'')) (VIMP_Syntax.V (STR ''p'')))) (STR ''g''))
                 (locals d) (globs gv))) bot))))"
  unfolding nest_1_eqs_def side_cfg_T_eff_keyed_seed_dg_def routed_extra_def
            apply_dg_spec_def dg_edge_tree_def
  by (simp add: result_g_intra result_g_no_comb result_g_no_calls nest_entry
                side_rhs_fold_dg.simps seqcomp_tree.simps)

lemma dep_L_result_g:
  "dep\<^sub>L nest_1_eqs project_sigma (FunctionResult (STR ''g''), [Statement 2]) = {(Statement 0, [Statement 2])}"
  unfolding dep\<^sub>L_def dep_def nest_1_eqs_result_g
  by simp

lemma statement_0_covered_1: "(Statement 0, [Statement 2]) \<in> fst nest_1_sol"
  unfolding nest_1_sol_def nest_1_eqs_def by eval

lemma project_sigma_dep_L_result_g:
  "dep\<^sub>L nest_1_eqs project_sigma (FunctionResult (STR ''g''), [Statement 2]) \<subseteq> fst nest_1_sol"
  by (simp add: dep_L_result_g statement_0_covered_1)

lemma sides_of_rhs_result_g:
  "sides_of_rhs (nest_1_eqs (FunctionResult (STR ''g''), [Statement 2])) project_sigma
     = (\<lambda>_. bot)(Inr Global1 :=
         DG bot (fst (dg_spec_step Spoly
               (EA_Ret (Some (Plus (VIMP_Syntax.V (STR ''p'')) (VIMP_Syntax.V (STR ''p'')))) (STR ''g''))
               (locals (project_sigma (Inl (Statement 0, [Statement 2]))))
               (globs (project_sigma (Inr Global1))))))"
  unfolding nest_1_eqs_result_g
  by (simp add: bot_fun_def)

text \<open>\<open>declared_global_iff\<close> is already \<open>[simp]\<close> and rewrites \<open>nest_gs x\<close> to the
  \<open>declared_global_vars\<close> membership form before this lemma's own \<open>nest_gs\<close>-headed
  form would ever match, so \<open>nest_declared_global_vars\<close> (not \<open>nest_gs_false\<close>) carries
  the \<open>[simp]\<close> attribute: it closes the goal \<open>declared_global_iff\<close> already
  produced, instead of competing with it on the same redex.\<close>
lemma nest_declared_global_vars [simp]: "declared_global_vars nest_program = []"
  unfolding nest_program_def by eval

lemma nest_gs_false: "\<not> nest_gs x"
  by simp

lemma restrict_global_resolved_q_update_ret_var:
  "restrict_global_resolved_q (nest_update_exec_dg_st s ret_var v) = restrict_global_resolved_q s"
  apply (rule st_eqI_lookup)
  apply (case_tac loc)
  by (simp_all add: lookup_restrict_global_resolved_q nest_gs_false
      lookup_resolved_st_q_update_diff location_of_def)



lemma eq_result_g_concrete_bound:
  "locals (eq nest_1_eqs (FunctionResult (STR ''g''), [Statement 2]) project_sigma)
     \<le> locals (project_sigma (Inl (FunctionResult (STR ''g''), [Statement 2])))"
  unfolding nest_1_eqs_entry_g project_sigma_def nest_1_eqs_result_g
  by eval

lemma restrict_global_resolved_q_le: "restrict_global_resolved_q s \<le> s"
  apply (simp only: le_resolved_st_q_iff)
  apply (rule allI)
  apply (case_tac loc)
  by simp_all

lemma fst_dgs_assign_ret_g:
  "fst (dgs_assign Spoly ret_var a d g) = restrict_global_resolved_q d \<squnion> restrict_global_resolved_q g"
  unfolding Spoly_def fst_dgs_assign_for
  by (simp add: ivl_tf_st_for.simps restrict_global_resolved_q_update_ret_var
                restrict_global_resolved_q_sup_restrict_global_resolved_q)

lemma fst_dg_spec_step_ret_g:
  "fst (dg_spec_step Spoly (EA_Ret (Some a) p) d g) = restrict_global_resolved_q d \<squnion> restrict_global_resolved_q g"
  by (simp add: fst_dgs_assign_ret_g)

lemma fst_dgs_nop:
  "fst (dgs_nop Spoly d g) = restrict_global_resolved_q d \<squnion> restrict_global_resolved_q g"
  unfolding Spoly_def fst_dgs_nop_for
  by (simp add: ivl_tf_st_for.simps restrict_global_resolved_q_sup_restrict_global_resolved_q)

lemma fst_dg_spec_step_ret_none:
  "fst (dg_spec_step Spoly (EA_Ret None p) d g) = restrict_global_resolved_q d \<squnion> restrict_global_resolved_q g"
  by (simp add: fst_dgs_nop)

subsection \<open>The same node, one level down in \<open>nest_2_eqs\<close>, at each child context\<close>

lemma result_g_intra_2:
  "intra_predecessor_list nest_cfg (FunctionResult (STR ''g''))
     = [(Statement 0, EA_Ret (Some (Plus (VIMP_Syntax.V (STR ''p'')) (VIMP_Syntax.V (STR ''p'')))) (STR ''g''))]"
  by eval

lemma nest_2_eqs_result_g:
  assumes "ctx = [Statement 2, Statement 5] \<or> ctx = [Statement 2, Statement 6]"
  shows "nest_2_eqs (FunctionResult (STR ''g''), ctx)
     = QueryL (Statement 0, ctx) (\<lambda>d. QueryG Global2 (\<lambda>gv.
         Side Global2
           (DG bot (fst (dg_spec_step Spoly
                 (EA_Ret (Some (Plus (VIMP_Syntax.V (STR ''p'')) (VIMP_Syntax.V (STR ''p'')))) (STR ''g''))
                 (locals d) (globs gv))))
           (Answer (DG (snd (dg_spec_step Spoly
                 (EA_Ret (Some (Plus (VIMP_Syntax.V (STR ''p'')) (VIMP_Syntax.V (STR ''p'')))) (STR ''g''))
                 (locals d) (globs gv))) bot))))"
  using assms
  unfolding nest_2_eqs_def side_cfg_T_eff_keyed_seed_dg_def routed_extra_def
            apply_dg_spec_def dg_edge_tree_def
  by (auto simp: result_g_intra_2 result_g_no_comb result_g_no_calls nest_entry
                 side_rhs_fold_dg.simps seqcomp_tree.simps)

lemma sides_of_rhs_result_g_2:
  assumes "ctx = [Statement 2, Statement 5] \<or> ctx = [Statement 2, Statement 6]"
  shows "sides_of_rhs (nest_2_eqs (FunctionResult (STR ''g''), ctx)) (snd nest_2_sol)
     = (\<lambda>_. bot)(Inr Global2 :=
         DG bot (fst (dg_spec_step Spoly
               (EA_Ret (Some (Plus (VIMP_Syntax.V (STR ''p'')) (VIMP_Syntax.V (STR ''p'')))) (STR ''g''))
               (locals (snd nest_2_sol (Inl (Statement 0, ctx))))
               (globs (snd nest_2_sol (Inr Global2))))))"
  unfolding nest_2_eqs_result_g[OF assms]
  by (simp add: bot_fun_def)

lemma part_post_sides_2:
  assumes "u \<in> fst nest_2_sol"
  shows "sides_of_rhs (nest_2_eqs u) (snd nest_2_sol) \<le> snd nest_2_sol"
  using nest_2_pp_st assms by blast

lemma result_g_covered_2_A: "(FunctionResult (STR ''g''), [Statement 2, Statement 5]) \<in> fst nest_2_sol"
  unfolding nest_2_sol_def nest_2_eqs_def by eval

lemma result_g_covered_2_B: "(FunctionResult (STR ''g''), [Statement 2, Statement 6]) \<in> fst nest_2_sol"
  unfolding nest_2_sol_def nest_2_eqs_def by eval

lemma project_sigma_sides_result_g:
  "sides_of_rhs (nest_1_eqs (FunctionResult (STR ''g''), [Statement 2])) project_sigma \<le> project_sigma"
proof -
  let ?dA = "snd nest_2_sol (Inl (Statement 0, [Statement 2, Statement 5]))"
  let ?dB = "snd nest_2_sol (Inl (Statement 0, [Statement 2, Statement 6]))"
  let ?g0 = "snd nest_2_sol (Inr Global2)"
  have d0: "locals (project_sigma (Inl (Statement 0, [Statement 2]))) = locals ?dA \<squnion> locals ?dB"
    by (simp add: project_sigma_def sup_dg_state_def)
  have restrict_boundA: "restrict_global_resolved_q (locals ?dA) \<le> globs ?g0"
    using part_post_sides_2[OF result_g_covered_2_A,
            unfolded sides_of_rhs_result_g_2[of "[Statement 2, Statement 5]", OF disjI1[OF refl]],
            THEN le_funD, of "Inr Global2"]
    by (simp add: less_eq_dg_state_def fst_dgs_assign_ret_g)
  have restrict_boundB: "restrict_global_resolved_q (locals ?dB) \<le> globs ?g0"
    using part_post_sides_2[OF result_g_covered_2_B,
            unfolded sides_of_rhs_result_g_2[of "[Statement 2, Statement 6]", OF disjI2[OF refl]],
            THEN le_funD, of "Inr Global2"]
    by (simp add: less_eq_dg_state_def fst_dgs_assign_ret_g)
  have split_d0: "restrict_global_resolved_q (locals (project_sigma (Inl (Statement 0, [Statement 2]))))
       = restrict_global_resolved_q (locals ?dA) \<squnion> restrict_global_resolved_q (locals ?dB)"
    by (simp add: d0 restrict_global_resolved_q_sup_restrict_global_resolved_q[symmetric])
  have key_bound:
    "fst (dg_spec_step Spoly (EA_Ret (Some (Plus (VIMP_Syntax.V (STR ''p'')) (VIMP_Syntax.V (STR ''p'')))) (STR ''g''))
           (locals (project_sigma (Inl (Statement 0, [Statement 2]))))
           (globs (project_sigma (Inr Global1))))
       \<le> globs (project_sigma (Inr Global1))"
  proof -
    have "fst (dg_spec_step Spoly (EA_Ret (Some (Plus (VIMP_Syntax.V (STR ''p'')) (VIMP_Syntax.V (STR ''p'')))) (STR ''g''))
             (locals (project_sigma (Inl (Statement 0, [Statement 2]))))
             (globs (project_sigma (Inr Global1))))
        = restrict_global_resolved_q (locals (project_sigma (Inl (Statement 0, [Statement 2]))))
            \<squnion> restrict_global_resolved_q (globs (project_sigma (Inr Global1)))"
      by (simp add: fst_dgs_assign_ret_g)
    also have "\<dots> = restrict_global_resolved_q (locals ?dA) \<squnion> restrict_global_resolved_q (locals ?dB)
                       \<squnion> restrict_global_resolved_q (globs ?g0)"
      by (simp add: split_d0 project_sigma_def restrict_global_resolved_q_sup_restrict_global_resolved_q
          sup_dg_state_def)
    also have "\<dots> \<le> globs ?g0"
      by (intro sup_least restrict_boundA restrict_boundB restrict_global_resolved_q_le)
    finally show ?thesis by (simp add: project_sigma_def)
  qed
  show ?thesis
    unfolding sides_of_rhs_result_g
    using key_bound by (auto simp: le_fun_def less_eq_dg_state_def bot_fun_def bot_dg_state_def)
qed

subsection \<open>Statement 3 -- the real COMB node: continuation of the call to g\<close>

text \<open>Unlike \<open>FunctionResult (STR ''g'')\<close>, \<open>Statement 3\<close> is a genuine \<open>return_call_action_list\<close>
  continuation (the call at \<open>Statement 2\<close> returns here), so its equation is built from
  \<^const>\<open>routed_cmb\<close>, not \<^const>\<open>apply_dg_spec\<close>. It carries no intra fragment and makes
  no calls of its own. Its context is \<open>[Statement 5]\<close> or \<open>[Statement 6]\<close> (whichever
  activation of \<open>f\<close> is running) -- not one of \<open>project_sigma\<close>'s three merge unknowns, since
  \<open>Statement 3\<close> is never itself pushed onto by a further call.\<close>

lemma statement3_no_intra: "intra_predecessor_list nest_cfg (Statement 3) = []"
  by eval

lemma statement3_comb:
  "return_call_action_list nest_cfg (Statement 3)
     = [(Statement 2, CallEdge (Some (STR ''t'')) [(STR ''p'')] [VIMP_Syntax.V (STR ''p'')], FunctionResult (STR ''g''))]"
  by eval

lemma statement3_no_calls: "call_successor_list nest_cfg (Statement 3) = []"
  by eval

lemma nest_1_eqs_statement3:
  "nest_1_eqs (Statement 3, ctx)
     = QueryL (Statement 2, ctx) (\<lambda>caller_state.
         QueryL (FunctionResult (STR ''g''),
                 cs_route 1 (Statement 2) ctx (locals caller_state)
                   (CallEdge (Some (STR ''t'')) [(STR ''p'')] [VIMP_Syntax.V (STR ''p'')])) (\<lambda>callee_state.
           QueryG Global1 (\<lambda>globals_state.
             Side Global1
               (DG bot (combine_global Spoly (Some (STR ''t''))
                     (locals caller_state) (locals callee_state) (globs globals_state)))
               (Answer (DG (combine_local Spoly (Some (STR ''t''))
                     (locals caller_state) (locals callee_state) (globs globals_state)) bot)))))"
  unfolding nest_1_eqs_def side_cfg_T_eff_keyed_seed_dg_def routed_extra_def routed_cmb_def
  by (simp add: statement3_no_intra statement3_comb statement3_no_calls nest_entry Let_def
                side_rhs_fold_dg.simps seqcomp_tree.simps)

lemma result_g_local_no_global_5:
  "restrict_global_resolved_q (locals (snd nest_2_sol (Inl (FunctionResult (STR ''g''), [Statement 2, Statement 5])))) = bot"
  by eval

lemma result_g_local_no_global_6:
  "restrict_global_resolved_q (locals (snd nest_2_sol (Inl (FunctionResult (STR ''g''), [Statement 2, Statement 6])))) = bot"
  by eval

lemma project_sigma_result_g_local_no_global:
  "restrict_global_resolved_q (locals (project_sigma (Inl (FunctionResult (STR ''g''), [Statement 2])))) = bot"
  by (simp add: project_sigma_def merged_result_g_def sup_dg_state_def
                restrict_global_resolved_q_sup_restrict_global_resolved_q
                result_g_local_no_global_5 result_g_local_no_global_6)

lemma statement2_no_global: "\<not> nest_gs (STR ''t'')"
  by simp

lemma restrict_global_resolved_q_update_var:
  "\<not> nest_gs w \<Longrightarrow> restrict_global_resolved_q (nest_update_exec_dg_st s w v) = restrict_global_resolved_q s"
  apply (rule st_eqI_lookup)
  apply (case_tac loc)
  by (simp_all add: lookup_restrict_global_resolved_q
      lookup_resolved_st_q_update_diff location_of_def)

lemma restrict_global_resolved_q_combine_assign_local:
  "\<not> nest_gs w \<Longrightarrow>
    restrict_global_resolved_q (combine_assign_resolved_q nest_gs (Some w) v s) =
    restrict_global_resolved_q s"
  apply (rule st_eqI_lookup)
  apply (case_tac loc)
  by (simp_all add: lookup_restrict_global_resolved_q
      lookup_combine_assign_resolved_q location_of_def)

lemma restrict_global_resolved_q_split':
  "restrict_global_resolved_q (restrict_global_resolved_q B \<squnion> restrict_local_resolved_q A) = restrict_global_resolved_q B"
  by (simp add: sup_commute[of "restrict_global_resolved_q B"] restrict_global_resolved_q_split)

lemma combine_global_ret_var:
  "\<not> nest_gs w \<Longrightarrow> combine_global Spoly (Some w) dc de g = restrict_global_resolved_q (de \<squnion> g)"
  unfolding Spoly_def dgs_combine_def fst_dgs_combine_assign_for
  by (simp add: fst_dgs_combine_env_for snd_dgs_combine_env_for
                restrict_local_resolved_q_split restrict_global_resolved_q_split'
                restrict_global_resolved_q_combine_assign_local)

lemma dep_L_statement3:
  "dep\<^sub>L nest_1_eqs project_sigma (Statement 3, ctx)
     = {(Statement 2, ctx),
        (FunctionResult (STR ''g''), cs_route 1 (Statement 2) ctx
           (locals (project_sigma (Inl (Statement 2, ctx))))
           (CallEdge (Some (STR ''t'')) [(STR ''p'')] [VIMP_Syntax.V (STR ''p'')]))}"
  unfolding dep\<^sub>L_def dep_def nest_1_eqs_statement3
  by auto

lemma cs_route_k1: "cs_route 1 u ctx d (CallEdge dst ps as) = [u]"
  by (simp add: cs_route_def)

lemma eq_statement3_closed_form:
  "eq nest_1_eqs (Statement 3, ctx) project_sigma
     = DG (combine_local Spoly (Some (STR ''t''))
           (locals (project_sigma (Inl (Statement 2, ctx))))
           (locals (project_sigma (Inl (FunctionResult (STR ''g''), [Statement 2]))))
           (globs (project_sigma (Inr Global1)))) bot"
  unfolding nest_1_eqs_statement3 cs_route_k1
  by simp

lemma project_sigma_eq_statement3:
  assumes "ctx = [Statement 5] \<or> ctx = [Statement 6]"
  shows "eq nest_1_eqs (Statement 3, ctx) project_sigma \<le> project_sigma (Inl (Statement 3, ctx))"
  using assms
  unfolding eq_statement3_closed_form project_sigma_def statement3_val_def
  by auto

lemma restrict_local_resolved_q_split':
  "restrict_local_resolved_q (restrict_global_resolved_q A \<squnion> restrict_local_resolved_q B) = restrict_local_resolved_q B"
  by (simp add: sup_commute[of "restrict_global_resolved_q A"] restrict_local_resolved_q_split)


lemma restrict_local_resolved_q_update_var:
  "\<not> nest_gs w \<Longrightarrow> restrict_local_resolved_q (nest_update_exec_dg_st s w v) = nest_update_exec_dg_st (restrict_local_resolved_q s) w v"
  apply (rule st_eqI_lookup)
  apply (case_tac loc)
  apply (case_tac "x1 = w")
  by (simp_all add: lookup_restrict_local_resolved_q
      lookup_resolved_st_q_update_diff location_of_def)

lemma restrict_local_resolved_q_combine_assign_local:
  "\<not> nest_gs w \<Longrightarrow>
    restrict_local_resolved_q (combine_assign_resolved_q nest_gs (Some w) v s) =
    nest_update_exec_dg_st (restrict_local_resolved_q s) w v"
  apply (rule st_eqI_lookup)
  apply (case_tac loc)
  apply (case_tac "x1 = w")
  by (simp_all add: lookup_restrict_local_resolved_q
      lookup_combine_assign_resolved_q lookup_resolved_st_q_update_diff location_of_def)

lemma combine_local_ret_var:
  "\<not> nest_gs w \<Longrightarrow> combine_local Spoly (Some w) dc de g
     = nest_update_exec_dg_st (restrict_local_resolved_q (dc \<squnion> g)) w (nest_lookup_exec_dg_st (de \<squnion> g) ret_var)"
  unfolding Spoly_def dgs_combine_def snd_dgs_combine_assign_for
  by (simp add: fst_dgs_combine_env_for snd_dgs_combine_env_for
                restrict_local_resolved_q_split' restrict_global_resolved_q_split
                restrict_local_resolved_q_combine_assign_local)

lemma restrict_global_resolved_q_restrict_local_resolved_q:
  "restrict_global_resolved_q (restrict_local_resolved_q s) = bot"
  apply (rule st_eqI_lookup)
  apply (case_tac loc)
  by (simp_all add: lookup_restrict_global_resolved_q lookup_restrict_local_resolved_q)

lemma combine_local_no_global:
  "\<not> nest_gs w \<Longrightarrow> restrict_global_resolved_q (combine_local Spoly (Some w) dc de g) = bot"
  by (simp add: combine_local_ret_var restrict_global_resolved_q_update_var
                restrict_global_resolved_q_restrict_local_resolved_q)

lemma var_x_no_global: "\<not> nest_gs (STR ''x'')"
  by simp

lemma var_y_no_global: "\<not> nest_gs (STR ''y'')"
  by simp



lemma statement2_covered_1: "(Statement 2, [Statement 5]) \<in> fst nest_1_sol \<and> (Statement 2, [Statement 6]) \<in> fst nest_1_sol"
  unfolding nest_1_sol_def nest_1_eqs_def by eval

lemma project_sigma_dep_L_statement3:
  assumes "ctx = [Statement 5] \<or> ctx = [Statement 6]"
  shows "dep\<^sub>L nest_1_eqs project_sigma (Statement 3, ctx) \<subseteq> fst nest_1_sol"
  unfolding dep_L_statement3 cs_route_k1
  using assms callee_exit_g_1 statement2_covered_1 by auto

lemma sides_of_rhs_statement3:
  "sides_of_rhs (nest_1_eqs (Statement 3, ctx)) project_sigma
     = (\<lambda>_. bot)(Inr Global1 :=
         DG bot (combine_global Spoly (Some (STR ''t''))
               (locals (project_sigma (Inl (Statement 2, ctx))))
               (locals (project_sigma (Inl (FunctionResult (STR ''g''),
                 cs_route 1 (Statement 2) ctx (locals (project_sigma (Inl (Statement 2, ctx))))
                   (CallEdge (Some (STR ''t'')) [(STR ''p'')] [VIMP_Syntax.V (STR ''p'')])))))
               (globs (project_sigma (Inr Global1)))))"
  unfolding nest_1_eqs_statement3
  by (simp add: bot_fun_def)

lemma project_sigma_sides_statement3:
  "sides_of_rhs (nest_1_eqs (Statement 3, ctx)) project_sigma \<le> project_sigma"
proof -
  have key_bound: "combine_global Spoly (Some (STR ''t''))
        (locals (project_sigma (Inl (Statement 2, ctx))))
        (locals (project_sigma (Inl (FunctionResult (STR ''g''), [Statement 2]))))
        (globs (project_sigma (Inr Global1)))
      \<le> globs (project_sigma (Inr Global1))"
  proof -
    have "combine_global Spoly (Some (STR ''t''))
            (locals (project_sigma (Inl (Statement 2, ctx))))
            (locals (project_sigma (Inl (FunctionResult (STR ''g''), [Statement 2]))))
            (globs (project_sigma (Inr Global1)))
        = restrict_global_resolved_q (locals (project_sigma (Inl (FunctionResult (STR ''g''), [Statement 2]))))
            \<squnion> restrict_global_resolved_q (globs (project_sigma (Inr Global1)))"
      by (simp add: combine_global_ret_var[OF statement2_no_global]
                    restrict_global_resolved_q_sup_restrict_global_resolved_q[symmetric])
    also have "\<dots> \<le> globs (project_sigma (Inr Global1))"
      by (simp add: project_sigma_result_g_local_no_global restrict_global_resolved_q_le)
    finally show ?thesis .
  qed
  show ?thesis
    unfolding sides_of_rhs_statement3 cs_route_k1
    using key_bound
    by (auto simp: le_fun_def less_eq_dg_state_def bot_fun_def bot_dg_state_def)
qed

subsection \<open>FunctionResult f -- intra return from Statement 3, both activations\<close>

text \<open>Same shape as \<open>FunctionResult (STR ''g'')\<close>: reached only by the intra return edge from
  \<open>Statement 3\<close>, no COMB, no outgoing calls. Its context (\<open>[Statement 5]\<close>
  or \<open>[Statement 6]\<close>) never merges, but it reads \<open>Statement 3\<close> which does, through
  \<open>project_sigma\<close>'s widened case.\<close>

lemma result_f_no_comb: "return_call_action_list nest_cfg (FunctionResult (STR ''f'')) = []"
  by eval

lemma result_f_no_calls: "call_successor_list nest_cfg (FunctionResult (STR ''f'')) = []"
  by eval

lemma result_f_intra:
  "intra_predecessor_list nest_cfg (FunctionResult (STR ''f''))
     = [(Statement 3, EA_Ret (Some (VIMP_Syntax.V (STR ''t''))) (STR ''f''))]"
  by eval

lemma nest_1_eqs_result_f:
  assumes "ctx = [Statement 5] \<or> ctx = [Statement 6]"
  shows "nest_1_eqs (FunctionResult (STR ''f''), ctx)
     = QueryL (Statement 3, ctx) (\<lambda>d. QueryG Global1 (\<lambda>gv.
         Side Global1
           (DG bot (fst (dg_spec_step Spoly
                 (EA_Ret (Some (VIMP_Syntax.V (STR ''t''))) (STR ''f'')) (locals d) (globs gv))))
           (Answer (DG (snd (dg_spec_step Spoly
                 (EA_Ret (Some (VIMP_Syntax.V (STR ''t''))) (STR ''f'')) (locals d) (globs gv))) bot))))"
  using assms
  unfolding nest_1_eqs_def side_cfg_T_eff_keyed_seed_dg_def routed_extra_def
            apply_dg_spec_def dg_edge_tree_def
  by (auto simp: result_f_intra result_f_no_comb result_f_no_calls nest_entry
                 side_rhs_fold_dg.simps seqcomp_tree.simps)

lemma dep_L_result_f:
  assumes "ctx = [Statement 5] \<or> ctx = [Statement 6]"
  shows "dep\<^sub>L nest_1_eqs project_sigma (FunctionResult (STR ''f''), ctx) = {(Statement 3, ctx)}"
  using assms unfolding dep\<^sub>L_def dep_def nest_1_eqs_result_f[OF assms]
  by simp

lemma statement3_covered_1:
  "(Statement 3, [Statement 5]) \<in> fst nest_1_sol \<and> (Statement 3, [Statement 6]) \<in> fst nest_1_sol"
  unfolding nest_1_sol_def nest_1_eqs_def by eval

lemma project_sigma_dep_L_result_f:
  assumes "ctx = [Statement 5] \<or> ctx = [Statement 6]"
  shows "dep\<^sub>L nest_1_eqs project_sigma (FunctionResult (STR ''f''), ctx) \<subseteq> fst nest_1_sol"
  using assms by (auto simp: dep_L_result_f statement3_covered_1)

lemma eq_result_f_concrete_bound:
  assumes "ctx = [Statement 5] \<or> ctx = [Statement 6]"
  shows "locals (eq nest_1_eqs (FunctionResult (STR ''f''), ctx) project_sigma)
     \<le> locals (project_sigma (Inl (FunctionResult (STR ''f''), ctx)))"
  using assms
proof
  assume c: "ctx = [Statement 5]"
  show ?thesis unfolding c nest_1_eqs_result_f[OF assms] project_sigma_def by eval
next
  assume c: "ctx = [Statement 6]"
  show ?thesis unfolding c nest_1_eqs_result_f[OF assms] project_sigma_def by eval
qed

lemma sides_of_rhs_result_f:
  assumes "ctx = [Statement 5] \<or> ctx = [Statement 6]"
  shows "sides_of_rhs (nest_1_eqs (FunctionResult (STR ''f''), ctx)) project_sigma
     = (\<lambda>_. bot)(Inr Global1 :=
         DG bot (fst (dg_spec_step Spoly
               (EA_Ret (Some (VIMP_Syntax.V (STR ''t''))) (STR ''f''))
               (locals (project_sigma (Inl (Statement 3, ctx))))
               (globs (project_sigma (Inr Global1))))))"
  unfolding nest_1_eqs_result_f[OF assms]
  by (simp add: bot_fun_def)

lemma statement3_val_local_no_global:
  "restrict_global_resolved_q (locals (statement3_val ctx)) = bot"
  by (simp add: statement3_val_def combine_local_no_global[OF statement2_no_global])

lemma project_sigma_sides_result_f:
  assumes "ctx = [Statement 5] \<or> ctx = [Statement 6]"
  shows "sides_of_rhs (nest_1_eqs (FunctionResult (STR ''f''), ctx)) project_sigma \<le> project_sigma"
proof -
  have key_bound: "fst (dg_spec_step Spoly (EA_Ret (Some (VIMP_Syntax.V (STR ''t''))) (STR ''f''))
        (locals (project_sigma (Inl (Statement 3, ctx))))
        (globs (project_sigma (Inr Global1))))
      \<le> globs (project_sigma (Inr Global1))"
  proof -
    have "fst (dg_spec_step Spoly (EA_Ret (Some (VIMP_Syntax.V (STR ''t''))) (STR ''f''))
             (locals (project_sigma (Inl (Statement 3, ctx))))
             (globs (project_sigma (Inr Global1))))
        = restrict_global_resolved_q (locals (project_sigma (Inl (Statement 3, ctx))))
            \<squnion> restrict_global_resolved_q (globs (project_sigma (Inr Global1)))"
      by (simp add: fst_dg_spec_step_ret_g fst_dgs_assign_ret_g)
    also have "\<dots> \<le> globs (project_sigma (Inr Global1))"
      using assms
      by (auto simp: project_sigma_def statement3_val_local_no_global restrict_global_resolved_q_le)
    finally show ?thesis .
  qed
  show ?thesis
    unfolding sides_of_rhs_result_f[OF assms]
    using key_bound by (auto simp: le_fun_def less_eq_dg_state_def bot_fun_def bot_dg_state_def)
qed

subsection \<open>Statement 6 -- dual role: COMB continuation of f's first call, and calls f again\<close>

text \<open>\<open>Statement 6\<close> is both a \<open>return_call_action_list\<close> continuation (the call to \<open>f\<close> at
  \<open>Statement 5\<close> returns here) and itself a call source (\<open>call_successor_list\<close> to
  \<open>FunctionEntry (STR ''f'')\<close>, continuation \<open>Statement 7\<close>). The \<open>calls\<close> fragment only ever
  publishes \<open>Side\<close>-effects (the global slot via \<open>enter_global\<close>, the callee's seed via
  \<open>enter_local\<close>); its own local \<open>Answer\<close> comes solely from the \<open>comb\<close> fragment, exactly as
  for a COMB-only node -- confirmed via \<open>side_cfg_T_eff_keyed_seed_dg\<close>'s single accumulator
  fold (\<open>routed_context.routed_seed_publish_bound\<close>). This section discovers the closed
  \<open>nest_1_eqs\<close> form via a \<open>schematic_goal\<close> rather than hand-typing the deeply nested
  \<open>QueryL/QueryG/Side/Answer\<close> term.\<close>

lemma statement6_no_intra: "intra_predecessor_list nest_cfg (Statement 6) = []"
  by eval

lemma statement6_comb:
  "return_call_action_list nest_cfg (Statement 6)
     = [(Statement 5, CallEdge (Some (STR ''x'')) [(STR ''p'')] [aexp.N 3], FunctionResult (STR ''f''))]"
  by eval

lemma statement6_calls:
  "call_successor_list nest_cfg (Statement 6)
     = [(FunctionEntry (STR ''f''), CallEdge (Some (STR ''y'')) [(STR ''p'')] [aexp.N 10], Statement 7)]"
  by eval

schematic_goal nest_1_eqs_statement6_form:
  "nest_1_eqs (Statement 6, ctx) = ?rhs"
  unfolding nest_1_eqs_def side_cfg_T_eff_keyed_seed_dg_def routed_extra_def routed_cmb_def
            apply_dg_spec_def dg_edge_tree_def
  apply (simp add: statement6_no_intra statement6_comb statement6_calls nest_entry Let_def
                side_rhs_fold_dg.simps seqcomp_tree.simps)
  done

lemmas nest_1_eqs_statement6 = nest_1_eqs_statement6_form

lemma eq_statement6_closed_form:
  "eq nest_1_eqs (Statement 6, ctx) project_sigma
     = DG (combine_local Spoly (Some (STR ''x''))
           (locals (project_sigma (Inl (Statement 5, ctx))))
           (locals (project_sigma (Inl (FunctionResult (STR ''f''), [Statement 5]))))
           (globs (project_sigma (Inr Global1)))) bot"
  unfolding nest_1_eqs_statement6
  by (simp add: cs_route_def)

lemma project_sigma_eq_statement6:
  "eq nest_1_eqs (Statement 6, []) project_sigma \<le> project_sigma (Inl (Statement 6, []))"
  unfolding eq_statement6_closed_form project_sigma_def statement6_val_def
  by auto

lemma dep_L_statement6:
  "dep\<^sub>L nest_1_eqs project_sigma (Statement 6, ctx)
     = {(Statement 5, ctx),
        (FunctionResult (STR ''f''), cs_route 1 (Statement 5) ctx
           (locals (project_sigma (Inl (Statement 5, ctx))))
           (CallEdge (Some (STR ''x'')) [(STR ''p'')] [aexp.N 3])),
        (Statement 6, ctx)}"
  unfolding dep\<^sub>L_def dep_def nest_1_eqs_statement6
  by auto

lemma statement5_covered: "(Statement 5, []) \<in> fst nest_1_sol"
  unfolding nest_1_sol_def nest_1_eqs_def by eval

lemma statement6_covered: "(Statement 6, []) \<in> fst nest_1_sol"
  unfolding nest_1_sol_def nest_1_eqs_def by eval

lemma result_f_covered_5: "(FunctionResult (STR ''f''), [Statement 5]) \<in> fst nest_1_sol"
  unfolding nest_1_sol_def nest_1_eqs_def by eval

lemma project_sigma_dep_L_statement6:
  "dep\<^sub>L nest_1_eqs project_sigma (Statement 6, []) \<subseteq> fst nest_1_sol"
  unfolding dep_L_statement6 cs_route_def
  using statement5_covered statement6_covered result_f_covered_5 by auto

schematic_goal sides_of_rhs_statement6_form:
  "sides_of_rhs (nest_1_eqs (Statement 6, ctx)) project_sigma = ?rhs"
  unfolding nest_1_eqs_statement6
  apply (simp add: cs_route_def bot_fun_def)
  done

schematic_goal enter_local_n10_form:
  "enter_local Spoly [(STR ''p'')] [aexp.N 10] d g = ?rhs"
  unfolding Spoly_def snd_dgs_enter_for ivl_enter_st_for_def
  apply (simp add: Let_def)
  done

text \<open>The fixed-top-value specialisation of \<^const>\<open>enter_frame_D_resolved_q\<close> this file's
  \<open>enter_local\<close>/\<open>enter_global\<close> facts reduce to, at the interval top value.\<close>
definition enter_ivl_st :: "ivl resolved_st_q \<Rightarrow> ivl resolved_st_q" where
  "enter_ivl_st s = enter_frame_D_resolved_q ivl_top s"

text \<open>\<^const>\<open>enter_frame_D_resolved_q\<close> resets every local slot to the fixed top value
  and leaves globals untouched (\<open>lookup_enter_frame_D_resolved_q\<close>); restricting to
  locals therefore keeps only that fixed top value and discards \<open>s\<close>/\<open>s'\<close> entirely.\<close>
lemma restrict_local_resolved_q_enter_frame_D_st_indep:
  "restrict_local_resolved_q (enter_ivl_st s) = restrict_local_resolved_q (enter_ivl_st s')"
  unfolding enter_ivl_st_def
  by (rule st_eqI_lookup) (simp split: location.splits)

lemma var_p_no_global: "\<not> nest_gs (STR ''p'')"
  by simp

lemma enter_local_n10_indep:
  "enter_local Spoly [(STR ''p'')] [aexp.N 10] d g = enter_local Spoly [(STR ''p'')] [aexp.N 10] bot bot"
proof -
  have h:
      "restrict_local_resolved_q (enter_frame_D_resolved_q ivl_top (d \<squnion> g)) =
       restrict_local_resolved_q (enter_frame_D_resolved_q ivl_top bot)"
    by (rule restrict_local_resolved_q_enter_frame_D_st_indep[unfolded enter_ivl_st_def])
  show ?thesis
    unfolding enter_local_n10_form
    by (simp add: bind_formals_resolved_q_singleton
                  restrict_local_resolved_q_update_var[OF var_p_no_global] h)
qed

lemma snd_dg_spec_step_ret_no_global:
  "restrict_global_resolved_q (snd (dg_spec_step Spoly (EA_Ret e p) d g)) = bot"
  unfolding Spoly_def
  by (cases e) (simp_all add: snd_dgs_nop_for snd_dgs_assign_for
      restrict_global_resolved_q_restrict_local_resolved_q)

lemma snd_dgs_assign_no_global:
  "restrict_global_resolved_q (snd (dgs_assign Spoly w a d g)) = bot"
  unfolding Spoly_def snd_dgs_assign_for
  by (simp add: restrict_global_resolved_q_restrict_local_resolved_q)

lemma result_f_val_local_no_global:
  "restrict_global_resolved_q (locals (result_f_val ctx)) = bot"
  by (simp add: result_f_val_def snd_dgs_assign_no_global)

lemma restrict_global_resolved_q_enter_frame_D_st:
  "restrict_global_resolved_q (enter_ivl_st s) = restrict_global_resolved_q s"
  apply (rule st_eqI_lookup)
  apply (case_tac loc)
  by (simp_all add: lookup_restrict_global_resolved_q enter_ivl_st_def)

lemma enter_global_ret_var:
  "enter_global Spoly [(STR ''p'')] [a] d g = restrict_global_resolved_q d \<squnion> restrict_global_resolved_q g"
  unfolding Spoly_def fst_dgs_enter_for ivl_enter_st_for_def
  by (simp add: Let_def bind_formals_abs_def
                bind_formals_resolved_q_singleton
                restrict_global_resolved_q_update_var[OF var_p_no_global]
                restrict_global_resolved_q_enter_frame_D_st[unfolded enter_ivl_st_def]
                restrict_global_resolved_q_sup_restrict_global_resolved_q)

lemma statement6_val_local_no_global:
  "restrict_global_resolved_q (locals statement6_val) = bot"
  by (simp add: statement6_val_def combine_local_no_global[OF var_x_no_global])

lemma seed_f_6_bound_ground:
  "enter_local Spoly [(STR ''p'')] [aexp.N 10] bot bot
     \<le> globs (snd nest_2_sol (Inr (Seed2 (FunctionEntry (STR ''f'')) [Statement 6])))"
  by eval

lemma project_sigma_sides_statement6:
  assumes "ctx = []"
  shows "sides_of_rhs (nest_1_eqs (Statement 6, ctx)) project_sigma \<le> project_sigma"
proof -
  have global1_bound: "enter_global Spoly [(STR ''p'')] [aexp.N 10]
        (locals (project_sigma (Inl (Statement 6, ctx))))
        (globs (project_sigma (Inr Global1)))
      \<squnion> combine_global Spoly (Some (STR ''x''))
          (locals (project_sigma (Inl (Statement 5, ctx))))
          (locals (project_sigma (Inl (FunctionResult (STR ''f''), [Statement 5]))))
          (globs (project_sigma (Inr Global1)))
      \<le> globs (project_sigma (Inr Global1))"
  proof (rule sup_least)
    show "enter_global Spoly [(STR ''p'')] [aexp.N 10]
            (locals (project_sigma (Inl (Statement 6, ctx))))
            (globs (project_sigma (Inr Global1)))
          \<le> globs (project_sigma (Inr Global1))"
      unfolding enter_global_ret_var
      using assms
      by (auto simp: project_sigma_def statement6_val_local_no_global
                     restrict_global_resolved_q_sup_restrict_global_resolved_q restrict_global_resolved_q_le)
  next
    show "combine_global Spoly (Some (STR ''x''))
            (locals (project_sigma (Inl (Statement 5, ctx))))
            (locals (project_sigma (Inl (FunctionResult (STR ''f''), [Statement 5]))))
            (globs (project_sigma (Inr Global1)))
          \<le> globs (project_sigma (Inr Global1))"
      unfolding combine_global_ret_var[OF var_x_no_global]
      by (simp add: project_sigma_def result_f_val_local_no_global
                    restrict_global_resolved_q_sup_restrict_global_resolved_q restrict_global_resolved_q_le)
  qed
  have seed_bound: "enter_local Spoly [(STR ''p'')] [aexp.N 10]
        (locals (project_sigma (Inl (Statement 6, ctx))))
        (globs (project_sigma (Inr Global1)))
      \<le> globs (project_sigma (Inr (Seed1 (FunctionEntry (STR ''f'')) [Statement 6])))"
  proof -
    have "enter_local Spoly [(STR ''p'')] [aexp.N 10]
            (locals (project_sigma (Inl (Statement 6, ctx))))
            (globs (project_sigma (Inr Global1)))
        = enter_local Spoly [(STR ''p'')] [aexp.N 10] bot bot"
      by (rule enter_local_n10_indep)
    also have "\<dots> \<le> globs (project_sigma (Inr (Seed1 (FunctionEntry (STR ''f'')) [Statement 6])))"
      by (simp add: project_sigma_def seed_f_6_bound_ground)
    finally show ?thesis .
  qed
  show ?thesis
    unfolding sides_of_rhs_statement6_form cs_route_def
    using global1_bound seed_bound
    by (auto simp: le_fun_def less_eq_dg_state_def bot_fun_def bot_dg_state_def
                   sup_dg_state_def project_sigma_def)
qed

subsection \<open>Statement 7 -- COMB-only, continuation of the second call to f\<close>

text \<open>Same shape as \<open>Statement 3\<close>: a genuine \<open>return_call_action_list\<close> continuation (the
  call at \<open>Statement 6\<close> returns here), no intra fragment, no outgoing calls of its own.\<close>

lemma statement7_no_intra: "intra_predecessor_list nest_cfg (Statement 7) = []"
  by eval

lemma statement7_comb:
  "return_call_action_list nest_cfg (Statement 7)
     = [(Statement 6, CallEdge (Some (STR ''y'')) [(STR ''p'')] [aexp.N 10], FunctionResult (STR ''f''))]"
  by eval

lemma statement7_no_calls: "call_successor_list nest_cfg (Statement 7) = []"
  by eval

lemma nest_1_eqs_statement7:
  "nest_1_eqs (Statement 7, ctx)
     = QueryL (Statement 6, ctx) (\<lambda>caller_state.
         QueryL (FunctionResult (STR ''f''),
                 cs_route 1 (Statement 6) ctx (locals caller_state)
                   (CallEdge (Some (STR ''y'')) [(STR ''p'')] [aexp.N 10])) (\<lambda>callee_state.
           QueryG Global1 (\<lambda>globals_state.
             Side Global1
               (DG bot (combine_global Spoly (Some (STR ''y''))
                     (locals caller_state) (locals callee_state) (globs globals_state)))
               (Answer (DG (combine_local Spoly (Some (STR ''y''))
                     (locals caller_state) (locals callee_state) (globs globals_state)) bot)))))"
  unfolding nest_1_eqs_def side_cfg_T_eff_keyed_seed_dg_def routed_extra_def routed_cmb_def
  by (simp add: statement7_no_intra statement7_comb statement7_no_calls nest_entry Let_def
                side_rhs_fold_dg.simps seqcomp_tree.simps)

lemma eq_statement7_closed_form:
  "eq nest_1_eqs (Statement 7, ctx) project_sigma
     = DG (combine_local Spoly (Some (STR ''y''))
           (locals (project_sigma (Inl (Statement 6, ctx))))
           (locals (project_sigma (Inl (FunctionResult (STR ''f''), [Statement 6]))))
           (globs (project_sigma (Inr Global1)))) bot"
  unfolding nest_1_eqs_statement7
  by (simp add: cs_route_def)

lemma project_sigma_eq_statement7:
  "eq nest_1_eqs (Statement 7, []) project_sigma \<le> project_sigma (Inl (Statement 7, []))"
  unfolding eq_statement7_closed_form project_sigma_def statement7_val_def
  by auto

lemma dep_L_statement7:
  "dep\<^sub>L nest_1_eqs project_sigma (Statement 7, ctx)
     = {(Statement 6, ctx),
        (FunctionResult (STR ''f''), cs_route 1 (Statement 6) ctx
           (locals (project_sigma (Inl (Statement 6, ctx))))
           (CallEdge (Some (STR ''y'')) [(STR ''p'')] [aexp.N 10]))}"
  unfolding dep\<^sub>L_def dep_def nest_1_eqs_statement7
  by auto

lemma result_f_covered_6: "(FunctionResult (STR ''f''), [Statement 6]) \<in> fst nest_1_sol"
  unfolding nest_1_sol_def nest_1_eqs_def by eval

lemma project_sigma_dep_L_statement7:
  "dep\<^sub>L nest_1_eqs project_sigma (Statement 7, []) \<subseteq> fst nest_1_sol"
  unfolding dep_L_statement7 cs_route_def
  using statement6_covered result_f_covered_6 by auto

lemma sides_of_rhs_statement7:
  "sides_of_rhs (nest_1_eqs (Statement 7, ctx)) project_sigma
     = (\<lambda>_. bot)(Inr Global1 :=
         DG bot (combine_global Spoly (Some (STR ''y''))
               (locals (project_sigma (Inl (Statement 6, ctx))))
               (locals (project_sigma (Inl (FunctionResult (STR ''f''),
                 cs_route 1 (Statement 6) ctx (locals (project_sigma (Inl (Statement 6, ctx))))
                   (CallEdge (Some (STR ''y'')) [(STR ''p'')] [aexp.N 10])))))
               (globs (project_sigma (Inr Global1)))))"
  unfolding nest_1_eqs_statement7
  by (simp add: bot_fun_def)

lemma result_f_val_6_local_no_global:
  "restrict_global_resolved_q (locals (result_f_val [Statement 6])) = bot"
  by (rule result_f_val_local_no_global)

lemma project_sigma_sides_statement7:
  "sides_of_rhs (nest_1_eqs (Statement 7, ctx)) project_sigma \<le> project_sigma"
proof -
  have key_bound: "combine_global Spoly (Some (STR ''y''))
        (locals (project_sigma (Inl (Statement 6, ctx))))
        (locals (project_sigma (Inl (FunctionResult (STR ''f''), [Statement 6]))))
        (globs (project_sigma (Inr Global1)))
      \<le> globs (project_sigma (Inr Global1))"
    unfolding combine_global_ret_var[OF var_y_no_global]
    by (simp add: project_sigma_def result_f_val_local_no_global
                  restrict_global_resolved_q_sup_restrict_global_resolved_q restrict_global_resolved_q_le)
  show ?thesis
    unfolding sides_of_rhs_statement7 cs_route_def
    using key_bound
    by (auto simp: le_fun_def less_eq_dg_state_def bot_fun_def bot_dg_state_def)
qed

subsection \<open>FunctionResult main -- intra return from Statement 7, the program's exit\<close>

text \<open>Same shape as \<open>FunctionResult (STR ''g'')\<close>/\<open>FunctionResult (STR ''f'')\<close>: reached only by the
  intra return edge from \<open>Statement 7\<close>. \<open>main\<close> returns nothing (\<open>EA_Ret None\<close>), so there
  is no assigned variable to reason about.\<close>

lemma result_main_no_comb: "return_call_action_list nest_cfg (FunctionResult (STR ''main'')) = []"
  by eval

lemma result_main_no_calls: "call_successor_list nest_cfg (FunctionResult (STR ''main'')) = []"
  by eval

lemma result_main_intra:
  "intra_predecessor_list nest_cfg (FunctionResult (STR ''main''))
     = [(Statement 7, EA_Ret None (STR ''main''))]"
  by eval

lemma nest_1_eqs_result_main:
  "nest_1_eqs (FunctionResult (STR ''main''), [])
     = QueryL (Statement 7, []) (\<lambda>d. QueryG Global1 (\<lambda>gv.
         Side Global1
           (DG bot (fst (dg_spec_step Spoly (EA_Ret None (STR ''main'')) (locals d) (globs gv))))
           (Answer (DG (snd (dg_spec_step Spoly (EA_Ret None (STR ''main'')) (locals d) (globs gv))) bot))))"
  unfolding nest_1_eqs_def side_cfg_T_eff_keyed_seed_dg_def routed_extra_def
            apply_dg_spec_def dg_edge_tree_def
  by (simp add: result_main_intra result_main_no_comb result_main_no_calls nest_entry
                side_rhs_fold_dg.simps seqcomp_tree.simps)

lemma dep_L_result_main:
  "dep\<^sub>L nest_1_eqs project_sigma (FunctionResult (STR ''main''), []) = {(Statement 7, [])}"
  unfolding dep\<^sub>L_def dep_def nest_1_eqs_result_main
  by simp

lemma statement7_covered: "(Statement 7, []) \<in> fst nest_1_sol"
  unfolding nest_1_sol_def nest_1_eqs_def by eval

lemma project_sigma_dep_L_result_main:
  "dep\<^sub>L nest_1_eqs project_sigma (FunctionResult (STR ''main''), []) \<subseteq> fst nest_1_sol"
  by (simp add: dep_L_result_main statement7_covered)

lemma eq_result_main_concrete_bound:
  "locals (eq nest_1_eqs (FunctionResult (STR ''main''), []) project_sigma)
     \<le> locals (project_sigma (Inl (FunctionResult (STR ''main''), [])))"
  unfolding nest_1_eqs_result_main project_sigma_def
  by eval

lemma sides_of_rhs_result_main:
  "sides_of_rhs (nest_1_eqs (FunctionResult (STR ''main''), [])) project_sigma
     = (\<lambda>_. bot)(Inr Global1 :=
         DG bot (fst (dg_spec_step Spoly (EA_Ret None (STR ''main''))
               (locals (project_sigma (Inl (Statement 7, []))))
               (globs (project_sigma (Inr Global1))))))"
  unfolding nest_1_eqs_result_main
  by (simp add: bot_fun_def)

lemma statement7_val_local_no_global:
  "restrict_global_resolved_q (locals statement7_val) = bot"
  by (simp add: statement7_val_def combine_local_no_global[OF var_y_no_global])

lemma project_sigma_sides_result_main:
  "sides_of_rhs (nest_1_eqs (FunctionResult (STR ''main''), [])) project_sigma \<le> project_sigma"
proof -
  have key_bound: "fst (dg_spec_step Spoly (EA_Ret None (STR ''main''))
        (locals (project_sigma (Inl (Statement 7, []))))
        (globs (project_sigma (Inr Global1))))
      \<le> globs (project_sigma (Inr Global1))"
    unfolding fst_dg_spec_step_ret_none
    by (simp add: project_sigma_def statement7_val_local_no_global
                  restrict_global_resolved_q_sup_restrict_global_resolved_q restrict_global_resolved_q_le)
  show ?thesis
    unfolding sides_of_rhs_result_main
    using key_bound by (auto simp: le_fun_def less_eq_dg_state_def bot_fun_def bot_dg_state_def)
qed

lemma nest_1_vars_list:
  "fst nest_1_sol =
     {(Statement 2,[Statement 6]), (Statement 3,[Statement 6]), (FunctionResult (STR ''f''),[Statement 6]),
      (Statement 0,[Statement 2]), (FunctionResult (STR ''g''),[Statement 2]), (Statement 2,[Statement 5]),
      (Statement 3,[Statement 5]), (FunctionResult (STR ''f''),[Statement 5]), (Statement 5,[]),
      (Statement 6,[]), (Statement 7,[]), (FunctionResult (STR ''main''),[]), (FunctionEntry (STR ''g''),[Statement 2]),
      (FunctionEntry (STR ''f''),[Statement 6]), (FunctionEntry (STR ''f''),[Statement 5]), (FunctionEntry (STR ''main''),[])}"
  unfolding nest_1_sol_def nest_1_eqs_def by eval

declare [[goals_limit = 50]]

subsection \<open>FunctionEntry f, FunctionEntry main -- pure seed reads, no widening\<close>

text \<open>Same shape as \<open>FunctionEntry (STR ''g'')\<close>: no intra, no comb, no calls. Neither seed
  context is a merge point (each activation of \<open>f\<close> keeps its own distinct k=1 context,
  and \<open>main\<close> is only ever entered once), so \<open>project_sigma\<close>'s \<open>Inr (Seed1 ...)\<close> case
  falls to its default passthrough for both.\<close>

lemma entry_f_no_intra: "intra_predecessor_list nest_cfg (FunctionEntry (STR ''f'')) = []"
  by eval

lemma entry_f_no_return: "return_call_action_list nest_cfg (FunctionEntry (STR ''f'')) = []"
  by eval

lemma entry_f_no_calls: "call_successor_list nest_cfg (FunctionEntry (STR ''f'')) = []"
  by eval

lemma nest_1_eqs_entry_f:
  assumes "ctx = [Statement 5] \<or> ctx = [Statement 6]"
  shows "nest_1_eqs (FunctionEntry (STR ''f''), ctx)
     = QueryG (Seed1 (FunctionEntry (STR ''f'')) ctx) (\<lambda>d. answer_local (globs d))"
  using assms
  unfolding nest_1_eqs_def side_cfg_T_eff_keyed_seed_dg_def routed_extra_def
  by (auto simp: entry_f_no_intra entry_f_no_return entry_f_no_calls nest_entry
                 side_rhs_fold_dg.simps seqcomp_tree.simps)

lemma dep_L_entry_f:
  assumes "ctx = [Statement 5] \<or> ctx = [Statement 6]"
  shows "dep\<^sub>L nest_1_eqs project_sigma (FunctionEntry (STR ''f''), ctx) = {}"
  unfolding dep\<^sub>L_def dep_def nest_1_eqs_entry_f[OF assms]
  by simp

lemma project_sigma_dep_L_entry_f:
  assumes "ctx = [Statement 5] \<or> ctx = [Statement 6]"
  shows "dep\<^sub>L nest_1_eqs project_sigma (FunctionEntry (STR ''f''), ctx) \<subseteq> fst nest_1_sol"
  by (simp add: dep_L_entry_f[OF assms])

lemma sides_of_rhs_entry_f:
  assumes "ctx = [Statement 5] \<or> ctx = [Statement 6]"
  shows "sides_of_rhs (nest_1_eqs (FunctionEntry (STR ''f''), ctx)) project_sigma = bot"
  unfolding nest_1_eqs_entry_f[OF assms]
  by (simp add: bot_fun_def)

lemma project_sigma_sides_entry_f:
  assumes "ctx = [Statement 5] \<or> ctx = [Statement 6]"
  shows "sides_of_rhs (nest_1_eqs (FunctionEntry (STR ''f''), ctx)) project_sigma \<le> project_sigma"
  by (simp add: sides_of_rhs_entry_f[OF assms])

lemma eq_entry_f_concrete_bound:
  assumes "ctx = [Statement 5] \<or> ctx = [Statement 6]"
  shows "locals (eq nest_1_eqs (FunctionEntry (STR ''f''), ctx) project_sigma)
     \<le> locals (project_sigma (Inl (FunctionEntry (STR ''f''), ctx)))"
  using assms
proof
  assume c: "ctx = [Statement 5]"
  show ?thesis unfolding c nest_1_eqs_entry_f[OF assms] project_sigma_def by eval
next
  assume c: "ctx = [Statement 6]"
  show ?thesis unfolding c nest_1_eqs_entry_f[OF assms] project_sigma_def by eval
qed

lemma entry_main_no_intra: "intra_predecessor_list nest_cfg (FunctionEntry (STR ''main'')) = []"
  by eval

lemma entry_main_no_return: "return_call_action_list nest_cfg (FunctionEntry (STR ''main'')) = []"
  by eval

lemma entry_main_no_calls: "call_successor_list nest_cfg (FunctionEntry (STR ''main'')) = []"
  by eval

schematic_goal nest_1_eqs_entry_main_form:
  "nest_1_eqs (FunctionEntry (STR ''main''), []) = ?rhs"
  unfolding nest_1_eqs_def side_cfg_T_eff_keyed_seed_dg_def routed_extra_def
  apply (simp add: entry_main_no_intra entry_main_no_return entry_main_no_calls nest_entry
                side_rhs_fold_dg.simps seqcomp_tree.simps)
  done

lemmas nest_1_eqs_entry_main = nest_1_eqs_entry_main_form

lemma dep_L_entry_main:
  "dep\<^sub>L nest_1_eqs project_sigma (FunctionEntry (STR ''main''), []) = {}"
  unfolding dep\<^sub>L_def dep_def nest_1_eqs_entry_main
  by simp

lemma project_sigma_dep_L_entry_main:
  "dep\<^sub>L nest_1_eqs project_sigma (FunctionEntry (STR ''main''), []) \<subseteq> fst nest_1_sol"
  by (simp add: dep_L_entry_main)

lemma sides_of_rhs_entry_main:
  "sides_of_rhs (nest_1_eqs (FunctionEntry (STR ''main''), [])) project_sigma
     = (\<lambda>_. bot)(Inr Global1 := DG bot (restrict_global_resolved_q cinit_ivl_st))"
  unfolding nest_1_eqs_entry_main
  by (simp add: bot_fun_def)

lemma cinit_ivl_st_global_bound:
  "restrict_global_resolved_q cinit_ivl_st \<le> globs (project_sigma (Inr Global1))"
  unfolding project_sigma_def
  by eval

lemma project_sigma_sides_entry_main:
  "sides_of_rhs (nest_1_eqs (FunctionEntry (STR ''main''), [])) project_sigma \<le> project_sigma"
  unfolding sides_of_rhs_entry_main
  using cinit_ivl_st_global_bound
  by (auto simp: le_fun_def less_eq_dg_state_def bot_fun_def bot_dg_state_def)

lemma eq_entry_main_concrete_bound:
  "locals (eq nest_1_eqs (FunctionEntry (STR ''main''), []) project_sigma)
     \<le> locals (project_sigma (Inl (FunctionEntry (STR ''main''), [])))"
  unfolding nest_1_eqs_entry_main project_sigma_def
  by eval

subsection \<open>Statement 2, Statement 5 -- intra + calls, no comb, no widening\<close>

text \<open>Both are call sites (not return continuations): \<open>Statement 2\<close> calls \<open>g\<close>, \<open>Statement 5\<close>
  calls \<open>f\<close>. Neither is itself reached by a call, so neither is a merge point; each keeps a
  plain \<open>nest_2_sol\<close> passthrough in \<open>project_sigma\<close>. As with \<open>Statement 6\<close>'s calls fragment,
  the outgoing-call part only ever contributes \<open>Side\<close>-effects (global slot, callee seed);
  the node's own \<open>Answer\<close> comes solely from its intra fragment.\<close>

lemma statement2_no_comb: "return_call_action_list nest_cfg (Statement 2) = []"
  by eval

lemma statement2_intra:
  "intra_predecessor_list nest_cfg (Statement 2) = [(FunctionEntry (STR ''f''), EA_Nop)]"
  by eval

lemma statement2_calls:
  "call_successor_list nest_cfg (Statement 2)
     = [(FunctionEntry (STR ''g''), CallEdge (Some (STR ''t'')) [(STR ''p'')] [VIMP_Syntax.V (STR ''p'')], Statement 3)]"
  by eval

schematic_goal nest_1_eqs_statement2_form:
  "nest_1_eqs (Statement 2, ctx) = ?rhs"
  unfolding nest_1_eqs_def side_cfg_T_eff_keyed_seed_dg_def routed_extra_def
            apply_dg_spec_def dg_edge_tree_def
  apply (simp add: statement2_intra statement2_no_comb statement2_calls nest_entry Let_def
                side_rhs_fold_dg.simps seqcomp_tree.simps)
  done

lemmas nest_1_eqs_statement2 = nest_1_eqs_statement2_form

lemma eq_statement2_closed_form:
  "eq nest_1_eqs (Statement 2, ctx) project_sigma
     = DG (snd (dg_spec_step Spoly EA_Nop
           (locals (project_sigma (Inl (FunctionEntry (STR ''f''), ctx))))
           (globs (project_sigma (Inr Global1))))) bot"
  unfolding nest_1_eqs_statement2
  by (simp add: cs_route_def)

lemma project_sigma_eq_statement2:
  assumes "ctx = [Statement 5] \<or> ctx = [Statement 6]"
  shows "eq nest_1_eqs (Statement 2, ctx) project_sigma \<le> project_sigma (Inl (Statement 2, ctx))"
  using assms
proof
  assume c: "ctx = [Statement 5]"
  show ?thesis unfolding c eq_statement2_closed_form project_sigma_def by eval
next
  assume c: "ctx = [Statement 6]"
  show ?thesis unfolding c eq_statement2_closed_form project_sigma_def by eval
qed

lemma dep_L_statement2:
  "dep\<^sub>L nest_1_eqs project_sigma (Statement 2, ctx)
     = {(FunctionEntry (STR ''f''), ctx), (Statement 2, ctx)}"
  unfolding dep\<^sub>L_def dep_def nest_1_eqs_statement2
  by auto

lemma entry_f_covered:
  "(FunctionEntry (STR ''f''), [Statement 5]) \<in> fst nest_1_sol \<and> (FunctionEntry (STR ''f''), [Statement 6]) \<in> fst nest_1_sol"
  unfolding nest_1_sol_def nest_1_eqs_def by eval

lemma project_sigma_dep_L_statement2:
  assumes "ctx = [Statement 5] \<or> ctx = [Statement 6]"
  shows "dep\<^sub>L nest_1_eqs project_sigma (Statement 2, ctx) \<subseteq> fst nest_1_sol"
  unfolding dep_L_statement2
  using assms statement2_covered_1 entry_f_covered by auto

lemma statement5_no_comb: "return_call_action_list nest_cfg (Statement 5) = []"
  by eval

lemma statement5_intra:
  "intra_predecessor_list nest_cfg (Statement 5) = [(FunctionEntry (STR ''main''), EA_Nop)]"
  by eval

lemma statement5_calls:
  "call_successor_list nest_cfg (Statement 5)
     = [(FunctionEntry (STR ''f''), CallEdge (Some (STR ''x'')) [(STR ''p'')] [aexp.N 3], Statement 6)]"
  by eval

schematic_goal nest_1_eqs_statement5_form:
  "nest_1_eqs (Statement 5, ctx) = ?rhs"
  unfolding nest_1_eqs_def side_cfg_T_eff_keyed_seed_dg_def routed_extra_def
            apply_dg_spec_def dg_edge_tree_def
  apply (simp add: statement5_intra statement5_no_comb statement5_calls nest_entry Let_def
                side_rhs_fold_dg.simps seqcomp_tree.simps)
  done

lemmas nest_1_eqs_statement5 = nest_1_eqs_statement5_form

lemma eq_statement5_closed_form:
  "eq nest_1_eqs (Statement 5, ctx) project_sigma
     = DG (snd (dg_spec_step Spoly EA_Nop
           (locals (project_sigma (Inl (FunctionEntry (STR ''main''), ctx))))
           (globs (project_sigma (Inr Global1))))) bot"
  unfolding nest_1_eqs_statement5
  by (simp add: cs_route_def)

lemma project_sigma_eq_statement5:
  "eq nest_1_eqs (Statement 5, []) project_sigma \<le> project_sigma (Inl (Statement 5, []))"
  unfolding eq_statement5_closed_form project_sigma_def
  by eval

lemma dep_L_statement5:
  "dep\<^sub>L nest_1_eqs project_sigma (Statement 5, ctx)
     = {(FunctionEntry (STR ''main''), ctx), (Statement 5, ctx)}"
  unfolding dep\<^sub>L_def dep_def nest_1_eqs_statement5
  by auto

lemma entry_main_covered: "(FunctionEntry (STR ''main''), []) \<in> fst nest_1_sol"
  unfolding nest_1_sol_def nest_1_eqs_def by eval

lemma project_sigma_dep_L_statement5:
  "dep\<^sub>L nest_1_eqs project_sigma (Statement 5, []) \<subseteq> fst nest_1_sol"
  unfolding dep_L_statement5
  using statement5_covered entry_main_covered by auto

text \<open>\<open>Statement 2\<close>'s calls fragment routes to \<open>Seed1 (FunctionEntry (STR ''g'')) [Statement 2]\<close>
  -- one of the three genuinely-merged unknowns -- since \<open>cs_route 1\<close> always collapses to
  \<open>[Statement 2]\<close> regardless of which activation of \<open>f\<close> is calling. The sides bound is
  therefore the same two-branch join pattern used for \<open>FunctionEntry (STR ''g'')\<close> itself
  (\<open>seed_le_entry_g_5\<close>/\<open>seed_le_entry_g_6\<close>), reusing \<open>nest_2_sol\<close>'s own established bound
  at each activation separately.\<close>

schematic_goal nest_2_eqs_statement2_form:
  assumes "ctx = [Statement 5] \<or> ctx = [Statement 6]"
  shows "nest_2_eqs (Statement 2, ctx) = ?rhs"
  using assms
  unfolding nest_2_eqs_def side_cfg_T_eff_keyed_seed_dg_def routed_extra_def
            apply_dg_spec_def dg_edge_tree_def
  apply (auto simp: statement2_intra statement2_no_comb statement2_calls nest_entry Let_def
                side_rhs_fold_dg.simps seqcomp_tree.simps)
  done

lemmas nest_2_eqs_statement2 = nest_2_eqs_statement2_form

lemma statement2_covered_2_A: "(Statement 2, [Statement 5]) \<in> fst nest_2_sol"
  unfolding nest_2_sol_def nest_2_eqs_def by eval

lemma statement2_covered_2_B: "(Statement 2, [Statement 6]) \<in> fst nest_2_sol"
  unfolding nest_2_sol_def nest_2_eqs_def by eval

schematic_goal sides_of_rhs_statement2_2_form:
  assumes "ctx = [Statement 5] \<or> ctx = [Statement 6]"
  shows "sides_of_rhs (nest_2_eqs (Statement 2, ctx)) (snd nest_2_sol) = ?rhs"
  using assms
  unfolding nest_2_eqs_statement2[OF assms]
  apply (simp add: bot_fun_def)
  done

lemmas sides_of_rhs_statement2_2 = sides_of_rhs_statement2_2_form

lemma cs_route_2_statement2:
  "cs_route 2 (Statement 2) ctx d ca = [Statement 2] @ take 1 ctx"
  by (simp add: cs_route_def)

lemma seed_le_statement2_5:
  "enter_local Spoly [(STR ''p'')] [VIMP_Syntax.V (STR ''p'')]
       (locals (snd nest_2_sol (Inl (Statement 2, [Statement 5]))))
       (globs (snd nest_2_sol (Inr Global2)))
     \<le> globs (snd nest_2_sol (Inr (Seed2 (FunctionEntry (STR ''g'')) [Statement 2, Statement 5])))"
  using part_post_sides_2[OF statement2_covered_2_A,
          unfolded sides_of_rhs_statement2_2[of "[Statement 5]", OF disjI1[OF refl]]
                   cs_route_2_statement2,
          THEN le_funD, of "Inr (Seed2 (FunctionEntry (STR ''g'')) [Statement 2, Statement 5])"]
  by (simp add: less_eq_dg_state_def)

lemma seed_le_statement2_6:
  "enter_local Spoly [(STR ''p'')] [VIMP_Syntax.V (STR ''p'')]
       (locals (snd nest_2_sol (Inl (Statement 2, [Statement 6]))))
       (globs (snd nest_2_sol (Inr Global2)))
     \<le> globs (snd nest_2_sol (Inr (Seed2 (FunctionEntry (STR ''g'')) [Statement 2, Statement 6])))"
  using part_post_sides_2[OF statement2_covered_2_B,
          unfolded sides_of_rhs_statement2_2[of "[Statement 6]", OF disjI2[OF refl]]
                   cs_route_2_statement2,
          THEN le_funD, of "Inr (Seed2 (FunctionEntry (STR ''g'')) [Statement 2, Statement 6])"]
  by (simp add: less_eq_dg_state_def)


lemma snd_dgs_nop_no_global:
  "restrict_global_resolved_q (snd (dgs_nop Spoly d g)) = bot"
  unfolding Spoly_def snd_dgs_nop_for
  by (simp add: restrict_global_resolved_q_restrict_local_resolved_q)

lemma statement2_val_local_no_global:
  assumes "ctx = [Statement 5] \<or> ctx = [Statement 6]"
  shows "restrict_global_resolved_q (locals (project_sigma (Inl (Statement 2, ctx)))) = bot"
  using assms
proof
  assume c: "ctx = [Statement 5]"
  show ?thesis unfolding c project_sigma_def by eval
next
  assume c: "ctx = [Statement 6]"
  show ?thesis unfolding c project_sigma_def by eval
qed

lemma entry_f_val_local_no_global:
  assumes "ctx = [Statement 5] \<or> ctx = [Statement 6]"
  shows "restrict_global_resolved_q (locals (project_sigma (Inl (FunctionEntry (STR ''f''), ctx)))) = bot"
  using assms
proof
  assume c: "ctx = [Statement 5]"
  show ?thesis unfolding c project_sigma_def by eval
next
  assume c: "ctx = [Statement 6]"
  show ?thesis unfolding c project_sigma_def by eval
qed

schematic_goal sides_of_rhs_statement2_form:
  assumes "ctx = [Statement 5] \<or> ctx = [Statement 6]"
  shows "sides_of_rhs (nest_1_eqs (Statement 2, ctx)) project_sigma = ?rhs"
  using assms
  unfolding nest_1_eqs_statement2
  apply (simp add: cs_route_def bot_fun_def)
  done

lemmas sides_of_rhs_statement2 = sides_of_rhs_statement2_form

lemma project_sigma_sides_statement2:
  assumes "ctx = [Statement 5] \<or> ctx = [Statement 6]"
  shows "sides_of_rhs (nest_1_eqs (Statement 2, ctx)) project_sigma \<le> project_sigma"
proof -
  have seed_bound: "enter_local Spoly [(STR ''p'')] [VIMP_Syntax.V (STR ''p'')]
        (locals (project_sigma (Inl (Statement 2, ctx))))
        (globs (project_sigma (Inr Global1)))
      \<le> globs (project_sigma (Inr (Seed1 (FunctionEntry (STR ''g'')) [Statement 2])))"
    using assms
  proof
    assume c: "ctx = [Statement 5]"
    show ?thesis
      unfolding c project_sigma_def
      by (auto simp: sup_dg_state_def order_trans[OF seed_le_statement2_5 sup_ge1])
  next
    assume c: "ctx = [Statement 6]"
    show ?thesis
      unfolding c project_sigma_def
      by (auto simp: sup_dg_state_def order_trans[OF seed_le_statement2_6 sup_ge2])
  qed
  have global1_bound: "enter_global Spoly [(STR ''p'')] [VIMP_Syntax.V (STR ''p'')]
        (locals (project_sigma (Inl (Statement 2, ctx))))
        (globs (project_sigma (Inr Global1)))
      \<squnion> fst (dgs_nop Spoly (locals (project_sigma (Inl (FunctionEntry (STR ''f''), ctx))))
             (globs (project_sigma (Inr Global1))))
      \<le> globs (project_sigma (Inr Global1))"
    unfolding enter_global_ret_var fst_dgs_nop
    using statement2_val_local_no_global[OF assms] entry_f_val_local_no_global[OF assms]
    by (auto simp: restrict_global_resolved_q_sup_restrict_global_resolved_q restrict_global_resolved_q_le)
  show ?thesis
    unfolding sides_of_rhs_statement2[OF assms]
    using seed_bound global1_bound
    by (auto simp: le_fun_def less_eq_dg_state_def bot_fun_def bot_dg_state_def
                   sup_dg_state_def project_sigma_def)
qed

text \<open>\<open>Statement 5\<close>'s calls fragment routes to \<open>Seed1 (FunctionEntry (STR ''f'')) [Statement 5]\<close>,
  which is \<^emph>\<open>not\<close> a merge point (\<open>f\<close>'s two activations come from distinct call sites, so
  neither of \<open>FunctionEntry (STR ''f'')\<close>'s two seed contexts collapses). \<open>project_sigma\<close> passes
  this slot through unchanged, so the bound is a direct reuse of \<open>nest_2_sol\<close>'s own
  established bound at the identical key -- no join needed, unlike \<open>Statement 2\<close>.\<close>

lemma statement5_covered_2: "(Statement 5, []) \<in> fst nest_2_sol"
  unfolding nest_2_sol_def nest_2_eqs_def by eval

schematic_goal nest_2_eqs_statement5_form:
  "nest_2_eqs (Statement 5, []) = ?rhs"
  unfolding nest_2_eqs_def side_cfg_T_eff_keyed_seed_dg_def routed_extra_def
            apply_dg_spec_def dg_edge_tree_def
  apply (simp add: statement5_intra statement5_no_comb statement5_calls nest_entry Let_def
                side_rhs_fold_dg.simps seqcomp_tree.simps)
  done

lemmas nest_2_eqs_statement5 = nest_2_eqs_statement5_form

schematic_goal sides_of_rhs_statement5_2_form:
  "sides_of_rhs (nest_2_eqs (Statement 5, [])) (snd nest_2_sol) = ?rhs"
  unfolding nest_2_eqs_statement5
  apply (simp add: cs_route_def bot_fun_def)
  done

lemmas sides_of_rhs_statement5_2 = sides_of_rhs_statement5_2_form

lemma seed_le_statement5:
  "enter_local Spoly [(STR ''p'')] [aexp.N 3]
       (locals (snd nest_2_sol (Inl (Statement 5, []))))
       (globs (snd nest_2_sol (Inr Global2)))
     \<le> globs (snd nest_2_sol (Inr (Seed2 (FunctionEntry (STR ''f'')) [Statement 5])))"
  using part_post_sides_2[OF statement5_covered_2, unfolded sides_of_rhs_statement5_2,
          THEN le_funD, of "Inr (Seed2 (FunctionEntry (STR ''f'')) [Statement 5])"]
  by (simp add: less_eq_dg_state_def)

lemma statement5_val_local_no_global:
  "restrict_global_resolved_q (locals (project_sigma (Inl (Statement 5, [])))) = bot"
  unfolding project_sigma_def
  by eval

lemma entry_main_val_global_bound:
  "restrict_global_resolved_q (locals (project_sigma (Inl (FunctionEntry (STR ''main''), []))))
     \<le> globs (project_sigma (Inr Global1))"
  unfolding project_sigma_def
  by eval

schematic_goal sides_of_rhs_statement5_form:
  "sides_of_rhs (nest_1_eqs (Statement 5, [])) project_sigma = ?rhs"
  unfolding nest_1_eqs_statement5
  apply (simp add: cs_route_def bot_fun_def)
  done

lemmas sides_of_rhs_statement5 = sides_of_rhs_statement5_form

lemma project_sigma_sides_statement5:
  "sides_of_rhs (nest_1_eqs (Statement 5, [])) project_sigma \<le> project_sigma"
proof -
  have seed_bound: "enter_local Spoly [(STR ''p'')] [aexp.N 3]
        (locals (project_sigma (Inl (Statement 5, []))))
        (globs (project_sigma (Inr Global1)))
      \<le> globs (project_sigma (Inr (Seed1 (FunctionEntry (STR ''f'')) [Statement 5])))"
    unfolding project_sigma_def
    by (simp add: seed_le_statement5)
  have global1_bound: "enter_global Spoly [(STR ''p'')] [aexp.N 3]
        (locals (project_sigma (Inl (Statement 5, []))))
        (globs (project_sigma (Inr Global1)))
      \<squnion> fst (dgs_nop Spoly (locals (project_sigma (Inl (FunctionEntry (STR ''main''), []))))
             (globs (project_sigma (Inr Global1))))
      \<le> globs (project_sigma (Inr Global1))"
    unfolding enter_global_ret_var fst_dgs_nop
    using statement5_val_local_no_global entry_main_val_global_bound
    by (auto simp: restrict_global_resolved_q_sup_restrict_global_resolved_q restrict_global_resolved_q_le)
  show ?thesis
    unfolding sides_of_rhs_statement5
    using seed_bound global1_bound
    by (auto simp: le_fun_def less_eq_dg_state_def bot_fun_def bot_dg_state_def
                   sup_dg_state_def project_sigma_def)
qed

subsection \<open>Statement 0 -- the last missing node: intra from FunctionEntry g, a merge point\<close>

text \<open>\<open>Statement 0\<close> is reached only by the intra \<open>EA_Nop\<close> edge from \<open>FunctionEntry (STR ''g'')\<close>.
  Its own context \<open>[Statement 2]\<close> is one of the three genuinely-merged unknowns (a two-branch
  join, already given by \<open>project_sigma\<close>'s first case). Unlike the downstream-cone nodes, its
  value is not a recomputation with a widened input substituted in -- it is literally the
  join of \<open>nest_2_sol\<close>'s own two branches, so the \<open>eq\<close> bound follows the same distributivity
  argument as \<open>project_sigma_sides_result_g\<close>'s \<open>split_d0\<close> step, applied to \<^const>\<open>restrict_local_resolved_q\<close>
  instead of \<^const>\<open>restrict_global_resolved_q\<close>.\<close>

lemma statement0_no_comb: "return_call_action_list nest_cfg (Statement 0) = []"
  by eval

lemma statement0_no_calls: "call_successor_list nest_cfg (Statement 0) = []"
  by eval

lemma statement0_intra:
  "intra_predecessor_list nest_cfg (Statement 0) = [(FunctionEntry (STR ''g''), EA_Nop)]"
  by eval

schematic_goal nest_1_eqs_statement0_form:
  "nest_1_eqs (Statement 0, [Statement 2]) = ?rhs"
  unfolding nest_1_eqs_def side_cfg_T_eff_keyed_seed_dg_def routed_extra_def
            apply_dg_spec_def dg_edge_tree_def
  apply (simp add: statement0_intra statement0_no_comb statement0_no_calls nest_entry
                side_rhs_fold_dg.simps seqcomp_tree.simps)
  done

lemmas nest_1_eqs_statement0 = nest_1_eqs_statement0_form

lemma dep_L_statement0:
  "dep\<^sub>L nest_1_eqs project_sigma (Statement 0, [Statement 2]) = {(FunctionEntry (STR ''g''), [Statement 2])}"
  unfolding dep\<^sub>L_def dep_def nest_1_eqs_statement0
  by simp

lemma entry_g_covered_1: "(FunctionEntry (STR ''g''), [Statement 2]) \<in> fst nest_1_sol"
  unfolding nest_1_sol_def nest_1_eqs_def by eval

lemma project_sigma_dep_L_statement0:
  "dep\<^sub>L nest_1_eqs project_sigma (Statement 0, [Statement 2]) \<subseteq> fst nest_1_sol"
  by (simp add: dep_L_statement0 entry_g_covered_1)

schematic_goal nest_2_eqs_statement0_form:
  assumes "ctx = [Statement 2, Statement 5] \<or> ctx = [Statement 2, Statement 6]"
  shows "nest_2_eqs (Statement 0, ctx) = ?rhs"
  using assms
  unfolding nest_2_eqs_def side_cfg_T_eff_keyed_seed_dg_def routed_extra_def
            apply_dg_spec_def dg_edge_tree_def
  apply (auto simp: statement0_intra statement0_no_comb statement0_no_calls nest_entry
                side_rhs_fold_dg.simps seqcomp_tree.simps)
  done

lemmas nest_2_eqs_statement0 = nest_2_eqs_statement0_form

lemma statement0_covered_2_A: "(Statement 0, [Statement 2, Statement 5]) \<in> fst nest_2_sol"
  unfolding nest_2_sol_def nest_2_eqs_def by eval

lemma statement0_covered_2_B: "(Statement 0, [Statement 2, Statement 6]) \<in> fst nest_2_sol"
  unfolding nest_2_sol_def nest_2_eqs_def by eval

lemma eq_le_statement0_5:
  "locals (eq nest_2_eqs (Statement 0, [Statement 2, Statement 5]) (snd nest_2_sol))
     \<le> locals (snd nest_2_sol (Inl (Statement 0, [Statement 2, Statement 5])))"
  using part_post_eq_2[OF statement0_covered_2_A]
  by (simp add: less_eq_dg_state_def)

lemma eq_le_statement0_6:
  "locals (eq nest_2_eqs (Statement 0, [Statement 2, Statement 6]) (snd nest_2_sol))
     \<le> locals (snd nest_2_sol (Inl (Statement 0, [Statement 2, Statement 6])))"
  using part_post_eq_2[OF statement0_covered_2_B]
  by (simp add: less_eq_dg_state_def)


lemma eq_le_statement0_5':
  "restrict_local_resolved_q (locals (snd nest_2_sol (Inl (FunctionEntry (STR ''g''), [Statement 2, Statement 5])))
        \<squnion> globs (snd nest_2_sol (Inr Global2)))
     \<le> locals (snd nest_2_sol (Inl (Statement 0, [Statement 2, Statement 5])))"
  using eq_le_statement0_5
  by (simp add: nest_2_eqs_statement0[of "[Statement 2, Statement 5]", OF disjI1[OF refl]]
                Spoly_def snd_dgs_nop_for)

lemma eq_le_statement0_6':
  "restrict_local_resolved_q (locals (snd nest_2_sol (Inl (FunctionEntry (STR ''g''), [Statement 2, Statement 6])))
        \<squnion> globs (snd nest_2_sol (Inr Global2)))
     \<le> locals (snd nest_2_sol (Inl (Statement 0, [Statement 2, Statement 6])))"
  using eq_le_statement0_6
  by (simp add: nest_2_eqs_statement0[of "[Statement 2, Statement 6]", OF disjI2[OF refl]]
                Spoly_def snd_dgs_nop_for)

lemma project_sigma_eq_statement0:
  "eq nest_1_eqs (Statement 0, [Statement 2]) project_sigma
     \<le> project_sigma (Inl (Statement 0, [Statement 2]))"
proof -
  let ?dA = "snd nest_2_sol (Inl (FunctionEntry (STR ''g''), [Statement 2, Statement 5]))"
  let ?dB = "snd nest_2_sol (Inl (FunctionEntry (STR ''g''), [Statement 2, Statement 6]))"
  have entry_g_split: "locals (project_sigma (Inl (FunctionEntry (STR ''g''), [Statement 2])))
       = locals ?dA \<squnion> locals ?dB"
    by (simp add: project_sigma_def sup_dg_state_def)
  have global1_eq: "globs (project_sigma (Inr Global1)) = globs (snd nest_2_sol (Inr Global2))"
    by (simp add: project_sigma_def)
  have locals_le: "locals (eq nest_1_eqs (Statement 0, [Statement 2]) project_sigma)
      \<le> locals (project_sigma (Inl (Statement 0, [Statement 2])))"
  proof -
    have "locals (eq nest_1_eqs (Statement 0, [Statement 2]) project_sigma)
        = restrict_local_resolved_q ((locals ?dA \<squnion> locals ?dB) \<squnion> globs (snd nest_2_sol (Inr Global2)))"
      by (simp add: nest_1_eqs_statement0 entry_g_split global1_eq Spoly_def snd_dgs_nop_for)
    also have "\<dots> = restrict_local_resolved_q (locals ?dA \<squnion> globs (snd nest_2_sol (Inr Global2)))
                    \<squnion> restrict_local_resolved_q (locals ?dB \<squnion> globs (snd nest_2_sol (Inr Global2)))"
      by (simp add: sup_commute sup_assoc sup_left_commute
                    restrict_local_resolved_q_sup_restrict_local_resolved_q)
    also have "\<dots> \<le> locals (snd nest_2_sol (Inl (Statement 0, [Statement 2, Statement 5])))
                    \<squnion> locals (snd nest_2_sol (Inl (Statement 0, [Statement 2, Statement 6])))"
      by (intro sup_mono eq_le_statement0_5' eq_le_statement0_6')
    also have "\<dots> = locals (project_sigma (Inl (Statement 0, [Statement 2])))"
      by (simp add: project_sigma_def sup_dg_state_def)
    finally show ?thesis .
  qed
  show ?thesis
    unfolding nest_1_eqs_statement0
    using locals_le[unfolded nest_1_eqs_statement0]
    by (auto simp: less_eq_dg_state_def)
qed


lemma sides_of_rhs_statement0:
  "sides_of_rhs (nest_1_eqs (Statement 0, [Statement 2])) project_sigma
     = (\<lambda>_. bot)(Inr Global1 :=
         DG bot (fst (dgs_nop Spoly
               (locals (project_sigma (Inl (FunctionEntry (STR ''g''), [Statement 2]))))
               (globs (project_sigma (Inr Global1))))))"
  unfolding nest_1_eqs_statement0
  by (simp add: bot_fun_def)

lemma entry_g_local_no_global_5:
  "restrict_global_resolved_q (locals (snd nest_2_sol (Inl (FunctionEntry (STR ''g''), [Statement 2, Statement 5])))) = bot"
  by eval

lemma entry_g_local_no_global_6:
  "restrict_global_resolved_q (locals (snd nest_2_sol (Inl (FunctionEntry (STR ''g''), [Statement 2, Statement 6])))) = bot"
  by eval

lemma entry_g_val_local_no_global:
  "restrict_global_resolved_q (locals (project_sigma (Inl (FunctionEntry (STR ''g''), [Statement 2])))) = bot"
  by (simp add: project_sigma_def sup_dg_state_def
                restrict_global_resolved_q_sup_restrict_global_resolved_q
                entry_g_local_no_global_5 entry_g_local_no_global_6)

lemma project_sigma_sides_statement0:
  "sides_of_rhs (nest_1_eqs (Statement 0, [Statement 2])) project_sigma \<le> project_sigma"
proof -
  have key_bound: "fst (dgs_nop Spoly
        (locals (project_sigma (Inl (FunctionEntry (STR ''g''), [Statement 2]))))
        (globs (project_sigma (Inr Global1))))
      \<le> globs (project_sigma (Inr Global1))"
    unfolding fst_dgs_nop
    by (simp add: entry_g_val_local_no_global restrict_global_resolved_q_le)
  show ?thesis
    unfolding sides_of_rhs_statement0
    using key_bound by (auto simp: le_fun_def less_eq_dg_state_def bot_fun_def bot_dg_state_def)
qed

lemma project_sigma_dep_L_all:
  "\<forall>u \<in> fst nest_1_sol. dep\<^sub>L nest_1_eqs project_sigma u \<subseteq> fst nest_1_sol"
  unfolding nest_1_vars_list
  apply (intro ballI)
  apply (elim insertE emptyE)
  apply (simp_all only: nest_1_vars_list[symmetric])
  by (simp_all add: project_sigma_dep_L_entry_g project_sigma_dep_L_result_g
                     project_sigma_dep_L_statement3 project_sigma_dep_L_result_f
                     project_sigma_dep_L_statement6 project_sigma_dep_L_statement7
                     project_sigma_dep_L_result_main project_sigma_dep_L_statement2
                     project_sigma_dep_L_statement0 project_sigma_dep_L_statement5
                     project_sigma_dep_L_entry_f project_sigma_dep_L_entry_main)

lemma eq_result_g_globs_bot:
  "globs (eq nest_1_eqs (FunctionResult (STR ''g''), [Statement 2]) project_sigma) = bot"
  unfolding nest_1_eqs_result_g by simp

lemma eq_result_f_globs_bot:
  assumes "ctx = [Statement 5] \<or> ctx = [Statement 6]"
  shows "globs (eq nest_1_eqs (FunctionResult (STR ''f''), ctx) project_sigma) = bot"
  unfolding nest_1_eqs_result_f[OF assms] by simp

lemma eq_result_main_globs_bot:
  "globs (eq nest_1_eqs (FunctionResult (STR ''main''), []) project_sigma) = bot"
  unfolding nest_1_eqs_result_main by simp

lemma eq_entry_f_globs_bot:
  assumes "ctx = [Statement 5] \<or> ctx = [Statement 6]"
  shows "globs (eq nest_1_eqs (FunctionEntry (STR ''f''), ctx) project_sigma) = bot"
  unfolding nest_1_eqs_entry_f[OF assms] by simp

lemma eq_entry_main_globs_bot:
  "globs (eq nest_1_eqs (FunctionEntry (STR ''main''), []) project_sigma) = bot"
  unfolding nest_1_eqs_entry_main by simp

lemma project_sigma_eq_result_g:
  "eq nest_1_eqs (FunctionResult (STR ''g''), [Statement 2]) project_sigma
     \<le> project_sigma (Inl (FunctionResult (STR ''g''), [Statement 2]))"
  using eq_result_g_concrete_bound eq_result_g_globs_bot by (simp add: less_eq_dg_state_def)

lemma project_sigma_eq_result_f:
  assumes "ctx = [Statement 5] \<or> ctx = [Statement 6]"
  shows "eq nest_1_eqs (FunctionResult (STR ''f''), ctx) project_sigma
     \<le> project_sigma (Inl (FunctionResult (STR ''f''), ctx))"
  using eq_result_f_concrete_bound[OF assms] eq_result_f_globs_bot[OF assms]
  by (simp add: less_eq_dg_state_def)

lemma project_sigma_eq_result_main:
  "eq nest_1_eqs (FunctionResult (STR ''main''), []) project_sigma
     \<le> project_sigma (Inl (FunctionResult (STR ''main''), []))"
  using eq_result_main_concrete_bound eq_result_main_globs_bot
  by (simp add: less_eq_dg_state_def)

lemma project_sigma_eq_entry_f:
  assumes "ctx = [Statement 5] \<or> ctx = [Statement 6]"
  shows "eq nest_1_eqs (FunctionEntry (STR ''f''), ctx) project_sigma
     \<le> project_sigma (Inl (FunctionEntry (STR ''f''), ctx))"
  using eq_entry_f_concrete_bound[OF assms] eq_entry_f_globs_bot[OF assms]
  by (simp add: less_eq_dg_state_def)

lemma project_sigma_eq_entry_main:
  "eq nest_1_eqs (FunctionEntry (STR ''main''), []) project_sigma
     \<le> project_sigma (Inl (FunctionEntry (STR ''main''), []))"
  using eq_entry_main_concrete_bound eq_entry_main_globs_bot
  by (simp add: less_eq_dg_state_def)

lemma project_sigma_eq_all:
  "\<forall>u \<in> fst nest_1_sol. eq nest_1_eqs u project_sigma \<le> project_sigma (Inl u)"
  unfolding nest_1_vars_list
  apply (intro ballI)
  apply (elim insertE emptyE)
  apply (simp_all only: nest_1_vars_list[symmetric])
  by (simp_all add: project_sigma_eq_statement0 project_sigma_eq_entry_g
                     project_sigma_eq_result_g project_sigma_eq_statement3
                     project_sigma_eq_result_f project_sigma_eq_statement2
                     project_sigma_eq_statement5 project_sigma_eq_statement6
                     project_sigma_eq_statement7 project_sigma_eq_result_main
                     project_sigma_eq_entry_f project_sigma_eq_entry_main)

lemma project_sigma_sides_all:
  "\<forall>u \<in> fst nest_1_sol. sides_of_rhs (nest_1_eqs u) project_sigma \<le> project_sigma"
  unfolding nest_1_vars_list
  apply (intro ballI)
  apply (elim insertE emptyE)
  apply (simp_all only: nest_1_vars_list[symmetric])
  by (simp_all add: project_sigma_sides_entry_g project_sigma_sides_result_g
                     project_sigma_sides_statement3 project_sigma_sides_result_f
                     project_sigma_sides_statement6 project_sigma_sides_statement7
                     project_sigma_sides_result_main project_sigma_sides_statement2
                     project_sigma_sides_statement0 project_sigma_sides_statement5
                     project_sigma_sides_entry_f project_sigma_sides_entry_main)

lemma project_sigma_part_post_solution:
  "part_post_solution nest_1_eqs (cfg_exit nest_cfg, []) project_sigma (fst nest_1_sol)"
proof (rule projected_part_post_solution)
  show "\<forall>u \<in> fst nest_1_sol. dep\<^sub>L nest_1_eqs project_sigma u \<subseteq> fst nest_1_sol"
    by (rule project_sigma_dep_L_all)
next
  show "\<forall>u \<in> fst nest_1_sol. eq nest_1_eqs u project_sigma \<le> project_sigma (Inl u)"
    by (rule project_sigma_eq_all)
next
  show "\<forall>u \<in> fst nest_1_sol. sides_of_rhs (nest_1_eqs u) project_sigma \<le> project_sigma"
    by (rule project_sigma_sides_all)
next
  show "(cfg_exit nest_cfg, []) \<in> fst nest_1_sol"
    by (simp add: nest_entry cfg_exit_def nest_1_vars_list)
qed


end







