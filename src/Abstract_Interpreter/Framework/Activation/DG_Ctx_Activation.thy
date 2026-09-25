theory DG_Ctx_Activation
  imports DG_Spec_Sound DG_Keyed_Generator
    "Voblint_Domain.Nonrelational_State" "Voblint_Solver.Strategy_Tree_Post_Solution"
begin

section \<open>What a solved routed system says about one program point\<close>

text \<open>
  A post-solution bounds a right-hand side by the value at its own unknown and
  every published side effect by the value at its target key.
  \<open>dg_ctx_activation_base\<close> fixes such a solution over the routed generator, a
  set \<open>vars\<close> of keys whose own equations it bounds, and a reader \<open>sg\<close> that
  answers the empty set off \<open>vars\<close>. The set may contain every key the solver
  visited or any subset. These facts derive the EDGE and COMB obligations the
  activation backbone asks for. Entry and callee-seed coverage remain with the
  concrete analysis.

  Both carriers are parameters: \<open>\<gamma>\<^sub>D\<^sub>G\<close> interprets a D/G pair, while
  \<open>\<gamma>\<^sub>M\<close> interprets whatever \<open>sg\<close> returns. An analysis whose reader is not an
  \<open>abs_state\<close> therefore instantiates this locale directly. Solutions carry one
  shared global slot \<open>Inr gk0\<close>, and \<open>sg_cov\<close> ties the reader at a covered key
  to \<open>\<gamma>\<^sub>D\<^sub>G\<close> of the local slot against that global.
\<close>

locale dg_ctx_activation_base = analysis_contract S \<gamma>\<^sub>D\<^sub>G \<G>
  for S :: "(pp \<times> 'c, 'k, unit, 'D::bounded_semilattice_sup_bot,
              'G::bounded_semilattice_sup_bot) dg_spec"
    and \<gamma>\<^sub>D\<^sub>G :: "'D \<Rightarrow> 'G \<Rightarrow> store set"
    and \<G> :: "vname \<Rightarrow> bool" +
  fixes g :: cfg and gk0 :: 'k
    and route :: "pp \<Rightarrow> 'c \<Rightarrow> 'D \<Rightarrow> call_action \<Rightarrow> 'c"
    and cmb :: "(pp \<Rightarrow> 'c \<Rightarrow> 'D \<Rightarrow> call_action \<Rightarrow> 'c) \<Rightarrow> 'c \<Rightarrow> call_action \<Rightarrow> pp \<Rightarrow> pp
                  \<Rightarrow> (pp \<times> 'c, 'k, ('D, 'G) dg_state, ('D, 'G) dg_state) strategy_program"
      \<comment> \<open>one program per call site: the site's own resolver decides which callees it folds\<close>
    and extra :: "(pp \<Rightarrow> 'c \<Rightarrow> 'D \<Rightarrow> call_action \<Rightarrow> 'c) \<Rightarrow> 'c \<Rightarrow> pp
                  \<Rightarrow> (pp \<times> 'c, 'k, ('D, 'G) dg_state, ('D, 'G) dg_state) strategy_program list"
    and bot0 s0d :: 'D and s0g :: 'G
    and sigma :: "pp \<times> 'c + 'k \<Rightarrow> ('D, 'G) dg_state"
    and vars :: "(pp \<times> 'c) set" and x0 :: "pp \<times> 'c"
    and sg :: "pp \<times> 'c + 'k \<Rightarrow> 'M"
    and \<gamma>\<^sub>M :: "'M \<Rightarrow> store set"
  assumes cmb_wf: "\<And>c ca cc v. sp_wf (cmb route c ca cc v)"
    and extra_wf: "\<And>c v q. q \<in> set (extra route c v) \<Longrightarrow> sp_wf q"
    and finE: "finite (intra g)"
    and pp: "post_bounded
               (routed_node_rhs intra_predecessor_addr_list call_site_list (\<lambda>_. gk0)
                  route (\<lambda>c src a. dg_spec_edge_program S a src (\<lambda>_. gk0)) cmb extra g bot0 s0d s0g)
               x0 sigma vars"
    and sg_cov[simp]: "\<And>v c. (v, c) \<in> vars
        \<Longrightarrow> \<gamma>\<^sub>M (sg (Inl (v, c))) =
          \<gamma>\<^sub>D\<^sub>G (locals (sigma (Inl (v, c)))) (globs (sigma (Inr gk0)))"
    and sg_uncov[simp]: "\<And>v c. (v, c) \<notin> vars
        \<Longrightarrow> \<gamma>\<^sub>M (sg (Inl (v, c))) = {}"
    and fwd: "\<And>u a v c. (u, c) \<in> vars
        \<Longrightarrow> \<gamma>\<^sub>D\<^sub>G (locals (sigma (Inl (u, c)))) (globs (sigma (Inr gk0))) \<noteq> {}
        \<Longrightarrow> (u, a, v) \<in> intra g
        \<Longrightarrow> (v, c) \<in> vars"
begin

abbreviation Gen :: "(pp \<times> 'c, 'k, ('D, 'G) dg_state) eqsT" where
  "Gen \<equiv> routed_node_rhs intra_predecessor_addr_list call_site_list (\<lambda>_. gk0)
           route (\<lambda>c src a. dg_spec_edge_program S a src (\<lambda>_. gk0)) cmb extra g bot0 s0d s0g"

abbreviation acc0 :: "pp \<Rightarrow> 'D" where
  "acc0 v \<equiv> (if v = cfg_entry g then bot0 \<squnion> s0d else bot0)"

abbreviation contribs :: "pp \<Rightarrow> 'c
    \<Rightarrow> (pp \<times> 'c, 'k, ('D, 'G) dg_state, ('D, 'G) dg_state) strategy_program list" where
  "contribs v ctx \<equiv>
     routed_contribution_programs intra_predecessor_addr_list call_site_list route
       (\<lambda>c src a. dg_spec_edge_program S a src (\<lambda>_. gk0)) cmb extra g ctx v"

text \<open>The reader's claim at a covered point (\<open>sg_cov\<close>) and the manager its call
  programs run under. Input-only, so facts of theory-level interpretations keep printing
  the explicit terms.\<close>
abbreviation (input) gamma_at :: "pp \<Rightarrow> 'c \<Rightarrow> store set" where
  "gamma_at v ctx \<equiv> \<gamma>\<^sub>D\<^sub>G (locals (sigma (Inl (v, ctx)))) (globs (sigma (Inr gk0)))"

abbreviation (input) man_at where
  "man_at v ctx \<equiv> mk_dg_man (locals (sigma (Inl (v, ctx)))) (\<lambda>_. gk0)"

text \<open>Every contribution the routed generator folds here runs its continuation
  once: the edge hook is a compiled specification step, and the call and extra
  hooks carry their own well-formedness as locale assumptions.\<close>

lemma contribs_wf [simp]: "\<forall>q \<in> set (contribs v ctx). sp_wf q"
  by (rule routed_contribution_programs_wf)
     (auto intro: sp_wf_dg_spec_edge_program[OF spec_wf] cmb_wf extra_wf)

subsection \<open>Post-solution elimination\<close>

text \<open>The solver hypothesis, unpacked once into the two bounds every later proof uses: at a
  covered unknown the generated right-hand side is below the stored local, and its side
  writes are below the stored globals.  Everything downstream cites these instead of
  \<^const>\<open>part_post_solution\<close>.\<close>
lemma pp_eq_bound:
  "(v, ctx) \<in> vars \<Longrightarrow> eq Gen (v, ctx) sigma \<le> sigma (Inl (v, ctx))"
  by (rule tree_covered_at_local[OF post_boundedD[OF pp]])

lemma pp_sides_bound:
  "(v, ctx) \<in> vars \<Longrightarrow> sides_of_rhs (Gen (v, ctx)) sigma \<le> sigma"
  by (rule tree_covered_at_sides[OF post_boundedD[OF pp]])

lemma pp_entry_s0g_bound:
  assumes cov: "(cfg_entry g, ctx) \<in> vars"
  shows "s0g \<le> globs (sigma (Inr gk0))"
proof -
  have "s0g \<le> globs (sides_of_rhs (Gen (cfg_entry g, ctx)) sigma (Inr gk0))"
    unfolding routed_node_rhs_def Let_def
    by (simp add: Let_def sup_dg_state_def)
  also have "\<dots> \<le> globs (sigma (Inr gk0))"
    using pp_sides_bound[OF cov, THEN le_funD, of "Inr gk0"]
    by (simp add: less_eq_dg_state_def)
  finally show ?thesis .
qed

text \<open>The local-carrier twin, proved the same way: \<open>Gen\<close>'s entry accumulator starts at
  \<open>bot0 \<squnion> s0d\<close>, \<open>side_acc_dg_ge_acc\<close> only grows it, and \<open>pp_eq_bound\<close> transports the
  bound across a covered point's own equation.\<close>

lemma pp_entry_s0d_bound:
  assumes cov: "(cfg_entry g, ctx) \<in> vars"
  shows "s0d \<le> locals (sigma (Inl (cfg_entry g, ctx)))"
proof -
  have "s0d \<le> locals (eq Gen (cfg_entry g, ctx) sigma)"
    by (simp add: eq_routed_node_rhs[OF contribs_wf])
       (rule order_trans[OF _ side_acc_dg_ge_acc], simp add: le_supI2)
  also have "\<dots> \<le> locals (sigma (Inl (cfg_entry g, ctx)))"
    using pp_eq_bound[OF cov] by (simp add: less_eq_dg_state_def)
  finally show ?thesis .
qed

subsection \<open>The entry Side wrapper only grows the sides\<close>

text \<open>At the entry the generator wraps its fold in one extra \<open>Side\<close> carrying the seed
  global, so a side read of the wrapped tree dominates the same read of the fold.  Bounds
  proved against the fold therefore transport to \<^const>\<open>routed_node_rhs\<close> without a separate
  entry case.\<close>
lemma sides_fold_le_Gen:
  "sides_of_rhs (sp_compile (side_rhs_fold_dg (acc0 v) (contribs v ctx))) sigma k
   \<le> sides_of_rhs (Gen (v, ctx)) sigma k"
  unfolding routed_node_rhs_def Let_def
  by (cases "v = cfg_entry g") (auto simp: Let_def intro: sup.cobounded1)

subsection \<open>EDGE: the routed intra bounds and the guarded transport\<close>

text \<open>Every intra predecessor of \<open>v\<close> contributes its edge program to \<open>v\<close>'s own fold, so
  both bounds below are the post-solution read off that one membership.\<close>

lemma edge_program_mem_contribs:
  assumes e: "(u, a, v) \<in> intra g"
  shows "dg_spec_edge_program S a (Inl (u, ctx)) (\<lambda>_. gk0) \<in> set (contribs v ctx)"
proof -
  have "(Inl (u, ctx), a) \<in> set (intra_predecessor_addr_list g v ctx)"
    using e by (force simp: intra_predecessor_addr_list_def
        set_intra_predecessor_list[OF finE] intra_predecessors_def)
  thus ?thesis by (force simp: routed_contribution_programs_def)
qed

lemma edge_bound_local:
  assumes cov_v: "(v, ctx) \<in> vars"
    and e: "(u, a, v) \<in> intra g"
  shows "locals (traverse_program (dg_spec_edge_program S a (Inl (u, ctx)) (\<lambda>_. gk0)) sigma)
           \<le> locals (sigma (Inl (v, ctx)))"
proof -
  have "locals (traverse_program (dg_spec_edge_program S a (Inl (u, ctx)) (\<lambda>_. gk0)) sigma)
      \<le> side_acc_dg (acc0 v) sigma (contribs v ctx)"
    using locals_traverse_le_side_acc_dg[OF edge_program_mem_contribs[OF e]] .
  also have "\<dots> = locals (eq Gen (v, ctx) sigma)"
    by (simp add: eq_routed_node_rhs[OF contribs_wf])
  also have "\<dots> \<le> locals (sigma (Inl (v, ctx)))"
    using pp_eq_bound[OF cov_v] by (simp add: less_eq_dg_state_def)
  finally show ?thesis .
qed

lemma edge_bound_global:
  assumes cov_v: "(v, ctx) \<in> vars"
    and e: "(u, a, v) \<in> intra g"
  shows "globs (sides_of_program (dg_spec_edge_program S a (Inl (u, ctx)) (\<lambda>_. gk0))
                  sigma (Inr gk0))
           \<le> globs (sigma (Inr gk0))"
proof -
  have "globs (sides_of_program (dg_spec_edge_program S a (Inl (u, ctx)) (\<lambda>_. gk0))
                 sigma (Inr gk0))
      \<le> globs (sides_of_rhs (sp_compile (side_rhs_fold_dg (acc0 v) (contribs v ctx)))
                   sigma (Inr gk0))"
    using sides_le_side_rhs_fold_dg[OF contribs_wf edge_program_mem_contribs[OF e],
        where k = "Inr gk0"]
    by (simp add: less_eq_dg_state_def)
  also have "\<dots> \<le> globs (sides_of_rhs (Gen (v, ctx)) sigma (Inr gk0))"
    using sides_fold_le_Gen[where k = "Inr gk0"]
    by (simp add: less_eq_dg_state_def)
  also have "\<dots> \<le> globs (sigma (Inr gk0))"
    using pp_sides_bound[OF cov_v, THEN le_funD, of "Inr gk0"]
    by (simp add: less_eq_dg_state_def)
  finally show ?thesis .
qed

theorem dg_ctx_act_edge:
  assumes e: "(u, a, v) \<in> intra g"
    and sin: "s \<in> \<gamma>\<^sub>M (sg (Inl (u, ctx)))" and st: "s' \<in> edge_step a s"
  shows "s' \<in> \<gamma>\<^sub>M (sg (Inl (v, ctx)))"
proof (cases "(u, ctx) \<in> vars")
  case False
  hence "\<gamma>\<^sub>M (sg (Inl (u, ctx))) = {}" by (rule sg_uncov)
  thus ?thesis using sin by simp
next
  case True
  let ?d = "locals (sigma (Inl (u, ctx)))"
  let ?g = "globs (sigma (Inr gk0))"
  have sin': "s \<in> \<gamma>\<^sub>D\<^sub>G ?d ?g"
    using sin True by simp
  have cov_v: "(v, ctx) \<in> vars"
    using True _ e by (rule fwd) (use sin' in blast)
  have "{s} \<subseteq> \<gamma>\<^sub>D\<^sub>G ?d ?g" using sin' by simp
  hence "edge_collect a {s} \<subseteq> edge_collect a (\<gamma>\<^sub>D\<^sub>G ?d ?g)" by (rule edge_collect_mono)
  moreover have "s' \<in> edge_collect a {s}" using st by (simp add: edge_collect_single)
  ultimately have "s' \<in> edge_collect a (\<gamma>\<^sub>D\<^sub>G ?d ?g)" by blast
  hence "s' \<in> \<gamma>\<^sub>D\<^sub>G
      (locals (traverse_program (dg_spec_edge_program S a (Inl (u, ctx)) (\<lambda>_. gk0)) sigma))
      (globs (sides_of_program (dg_spec_edge_program S a (Inl (u, ctx)) (\<lambda>_. gk0))
                sigma (Inr gk0)))"
    using step_sound[of a sigma "Inl (u, ctx)" gk0] by blast
  also have "\<dots> \<subseteq> gamma_at v ctx"
    by (rule gammaDG_mono[OF edge_bound_local[OF cov_v e] edge_bound_global[OF cov_v e]])
  also have "\<dots> = \<gamma>\<^sub>M (sg (Inl (v, ctx)))"
    using cov_v by simp
  finally show ?thesis .
qed

subsection \<open>COMB: the guarded combine transport\<close>

text \<open>The caller, callee-result and continuation slots are transported independently; which
  caller a return belongs to is settled by the trace semantics, so this layer never has to
  reconstruct the activation pairing itself.  The two bounds are assumptions because the
  combine program that establishes them is built by the routed call generator, not here.\<close>

lemma dg_ctx_act_comb_covered:
  assumes covCl: "(cl, c1) \<in> vars"
    and covEx: "(ex, c2) \<in> vars"
    and covV: "(v, cv) \<in> vars"
    and s: "s \<in> \<gamma>\<^sub>M (sg (Inl (cl, c1)))"
    and t: "t \<in> \<gamma>\<^sub>M (sg (Inl (ex, c2)))"
    and bound_local:
      "locals (traverse_program
                 (dg_spec_combine_program S ci (Inl (cl, c1)) (Inl (ex, c2)) (\<lambda>_. gk0)) sigma)
       \<le> locals (sigma (Inl (v, cv)))"
    and bound_global:
      "globs (sides_of_program
                (dg_spec_combine_program S ci (Inl (cl, c1)) (Inl (ex, c2)) (\<lambda>_. gk0)) sigma
                (Inr gk0))
       \<le> globs (sigma (Inr gk0))"
  shows "combine_collect \<G> (ci_dst ci) s t \<in> \<gamma>\<^sub>M (sg (Inl (v, cv)))"
proof -
  let ?Dc = "locals (sigma (Inl (cl, c1)))"
  let ?De = "locals (sigma (Inl (ex, c2)))"
  let ?G = "globs (sigma (Inr gk0))"
  have sin: "s \<in> \<gamma>\<^sub>D\<^sub>G ?Dc ?G"
    using s covCl by simp
  have tin: "t \<in> \<gamma>\<^sub>D\<^sub>G ?De ?G"
    using t covEx by simp
  have "combine_collect \<G> (ci_dst ci) s t
        \<in> \<gamma>\<^sub>D\<^sub>G
            (locals (traverse_program
               (dg_spec_combine_program S ci (Inl (cl, c1)) (Inl (ex, c2)) (\<lambda>_. gk0)) sigma))
            (globs (sides_of_program
               (dg_spec_combine_program S ci (Inl (cl, c1)) (Inl (ex, c2)) (\<lambda>_. gk0)) sigma
               (Inr gk0)))"
    using combine_sound_program[where \<tau> = sigma and src_cc = "Inl (cl, c1)"
        and src_ex = "Inl (ex, c2)" and gk = gk0 and ci = ci, OF sin tin] .
  also have "\<dots> \<subseteq> \<gamma>\<^sub>D\<^sub>G (locals (sigma (Inl (v, cv)))) ?G"
    by (rule gammaDG_mono[OF bound_local bound_global])
  also have "\<dots> = \<gamma>\<^sub>M (sg (Inl (v, cv)))"
    using covV by simp
  finally show ?thesis .
qed

end

end
