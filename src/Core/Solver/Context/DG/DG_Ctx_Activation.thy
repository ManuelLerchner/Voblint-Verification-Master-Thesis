theory DG_Ctx_Activation
  imports DG_Soundness
begin

section \<open>DG-native discharge of the activation obligations\<close>

text \<open>
  \<open>dg_ctx_activation_base\<close> derives the edge and combine closure obligations from a
  \<^const>\<open>part_post_solution\<close>, a sound D/G specification, the routing hooks, and a guarded
  solution reader.  Concrete analyses supply the entry and callee-seed coverage obligations.

  Both carriers and both concretizations are free parameters: \<open>gammaDG\<close> interprets a
  D/G pair, \<open>gammaM\<close> interprets whatever the reader \<open>sg\<close> returns.  This matches
  \<^locale>\<open>sound_dg_spec\<close>'s own genericity, so an analysis whose reader is not an
  \<open>abs_state\<close> instantiates the locale directly.  Solutions carry one shared global slot
  \<open>Inr gk0\<close>, and the reader's coverage assumption ties \<open>gammaM (sg (Inl (v, c)))\<close>
  to \<open>gammaDG\<close> of the local slot against that global.

  The D/G layer transports abstract states at the caller, callee-result, and continuation
  slots.  The trace semantics supplies the matched caller/callee relation, so this layer does
  not reconstruct activation pairing.
\<close>

locale dg_ctx_activation_base = sound_dg_spec S gammaDG gs
  for S :: "('D::bounded_semilattice_sup_bot, 'G::bounded_semilattice_sup_bot) dg_spec"
    and gammaDG :: "'D \<Rightarrow> 'G \<Rightarrow> store set"
    and gs :: "vname \<Rightarrow> bool" +
  fixes g :: cfg and gk0 :: 'k
    and route :: "pp \<Rightarrow> 'c \<Rightarrow> 'D \<Rightarrow> call_action \<Rightarrow> 'c"
    and cmb :: "(pp \<Rightarrow> 'c \<Rightarrow> 'D \<Rightarrow> call_action \<Rightarrow> 'c) \<Rightarrow> 'c \<Rightarrow> call_action \<Rightarrow> pp \<Rightarrow> pp
                  \<Rightarrow> (pp \<times> 'c, 'k, ('D, 'G) dg_state) strategy_tree"
    and extra :: "(pp \<Rightarrow> 'c \<Rightarrow> 'D \<Rightarrow> call_action \<Rightarrow> 'c) \<Rightarrow> 'c \<Rightarrow> pp
                  \<Rightarrow> (pp \<times> 'c, 'k, ('D, 'G) dg_state) strategy_tree list"
    and bot0 s0d :: 'D and s0g :: 'G
    and sigma :: "pp \<times> 'c + 'k \<Rightarrow> ('D, 'G) dg_state"
    and vars :: "(pp \<times> 'c) set" and x0 :: "pp \<times> 'c"
    and sg :: "pp \<times> 'c + 'k \<Rightarrow> 'M"
    and gammaM :: "'M \<Rightarrow> store set"
  assumes finE[intro]: "finite (intra g)"
    and pp: "part_post_solution
               (side_cfg_T_eff_keyed_seed_dg intra_predecessor_addr_list (\<lambda>_. gk0)
                  route cmb extra g S bot0 s0d s0g) x0 sigma vars"
    and sg_cov[simp]: "\<And>v c. (v, c) \<in> vars
        \<Longrightarrow> gammaM (sg (Inl (v, c))) =
          gammaDG (locals (sigma (Inl (v, c)))) (globs (sigma (Inr gk0)))"
    and sg_uncov[simp]: "\<And>v c. (v, c) \<notin> vars
        \<Longrightarrow> gammaM (sg (Inl (v, c))) = {}"
    and fwd[intro]: "\<And>u a v c. (u, c) \<in> vars
        \<Longrightarrow> (u, a, v) \<in> intra g
        \<Longrightarrow> (v, c) \<in> vars"
begin

abbreviation Gen :: "(pp \<times> 'c, 'k, ('D, 'G) dg_state) eqsT" where
  "Gen \<equiv> side_cfg_T_eff_keyed_seed_dg intra_predecessor_addr_list (\<lambda>_. gk0)
           route cmb extra g S bot0 s0d s0g"

abbreviation acc0 :: "pp \<Rightarrow> 'D" where
  "acc0 v \<equiv> (if v = cfg_entry g then bot0 \<squnion> s0d else bot0)"

abbreviation trees :: "pp \<Rightarrow> 'c
    \<Rightarrow> (pp \<times> 'c, 'k, ('D, 'G) dg_state) strategy_tree list" where
  "trees v ctx \<equiv>
     map (\<lambda>(src, a). apply_dg_spec_at S a src gk0) (intra_predecessor_addr_list g v ctx)
     @ map (\<lambda>(cc, ca, ex). cmb route ctx ca cc ex) (return_call_action_list g v)
     @ extra route ctx v"

subsection \<open>Post-solution elimination\<close>

lemma pp_eq_bound:
  "(v, ctx) \<in> vars \<Longrightarrow> eq Gen (v, ctx) sigma \<le> sigma (Inl (v, ctx))"
  using se_constraint_holds_local[OF part_post_solution_imp_se_constraint_holds[OF pp]]
  by blast

lemma pp_sides_bound:
  "(v, ctx) \<in> vars \<Longrightarrow> sides_of_rhs (Gen (v, ctx)) sigma \<le> sigma"
  using se_constraint_holds_sides[OF part_post_solution_imp_se_constraint_holds[OF pp]]
  by blast

lemma pp_entry_s0g_bound:
  assumes cov: "(cfg_entry g, ctx) \<in> vars"
  shows "s0g \<le> globs (sigma (Inr gk0))"
proof -
  have "s0g \<le> globs (sides_of_rhs (Gen (cfg_entry g, ctx)) sigma (Inr gk0))"
    unfolding side_cfg_T_eff_keyed_seed_dg_def Let_def
    by (simp add: Let_def sup_dg_state_def)
  also have "\<dots> \<le> globs (sigma (Inr gk0))"
    using pp_sides_bound[OF cov, THEN le_funD, of "Inr gk0"]
    by (simp add: less_eq_dg_state_def)
  finally show ?thesis .
qed

subsection \<open>The guarded reader\<close>

lemma sg_uncovered_empty: "(v, ctx) \<notin> vars \<Longrightarrow> gammaM (sg (Inl (v, ctx))) = {}"
  by (rule sg_uncov)

subsection \<open>Routed intra edge tree denotation\<close>

lemma edge_tree_local_ctx:
  "locals (traverse_rhs (apply_dg_spec_at S a src gk0) sigma)
   = snd (dg_spec_step S a (locals (sigma src)) (globs (sigma (Inr gk0))))"
  by (simp add: apply_dg_spec_at_def traverse_dg_edge_tree_at)

lemma edge_tree_global_ctx:
  "globs (sides_of_rhs (apply_dg_spec_at S a src gk0) sigma (Inr gk0))
   = fst (dg_spec_step S a (locals (sigma src)) (globs (sigma (Inr gk0))))"
  by (simp add: apply_dg_spec_at_def sides_dg_edge_tree_at)

subsection \<open>The entry Side wrapper only grows the sides\<close>

lemma sides_fold_le_Gen:
  "sides_of_rhs (side_rhs_fold_dg (acc0 v) (trees v ctx)) sigma k
   \<le> sides_of_rhs (Gen (v, ctx)) sigma k"
  unfolding side_cfg_T_eff_keyed_seed_dg_def Let_def
  by (cases "v = cfg_entry g") (auto simp: Let_def intro: sup.cobounded1)

subsection \<open>EDGE: the routed intra bounds and the guarded transport\<close>

lemma edge_bound_local:
  assumes cov_v: "(v, ctx) \<in> vars"
    and e: "(u, a, v) \<in> intra g"
  shows "snd (dg_spec_step S a (locals (sigma (Inl (u, ctx)))) (globs (sigma (Inr gk0))))
           \<le> locals (sigma (Inl (v, ctx)))"
proof -
  let ?t = "apply_dg_spec_at S a (Inl (u, ctx)) gk0"
  have pred: "(Inl (u, ctx), a) \<in> set (intra_predecessor_addr_list g v ctx)"
    using e by (force simp: intra_predecessor_addr_list_def
        set_intra_predecessor_list[OF finE] intra_predecessors_def)
  hence mem: "?t \<in> set (trees v ctx)" by (force intro: rev_image_eqI)
  have "snd (dg_spec_step S a (locals (sigma (Inl (u, ctx)))) (globs (sigma (Inr gk0))))
      = locals (traverse_rhs ?t sigma)"
    by (simp add: edge_tree_local_ctx)
  also have "\<dots> \<le> side_acc_dg (acc0 v) sigma (trees v ctx)"
    using locals_traverse_le_side_acc_dg[OF mem] .
  also have "\<dots> = locals (eq Gen (v, ctx) sigma)"
    by (simp add: eq_side_cfg_T_eff_keyed_seed_dg)
  also have "\<dots> \<le> locals (sigma (Inl (v, ctx)))"
    using pp_eq_bound[OF cov_v] by (simp add: less_eq_dg_state_def)
  finally show ?thesis .
qed

lemma edge_bound_global:
  assumes cov_v: "(v, ctx) \<in> vars"
    and e: "(u, a, v) \<in> intra g"
  shows "fst (dg_spec_step S a (locals (sigma (Inl (u, ctx)))) (globs (sigma (Inr gk0))))
           \<le> globs (sigma (Inr gk0))"
proof -
  let ?t = "apply_dg_spec_at S a (Inl (u, ctx)) gk0"
  have pred: "(Inl (u, ctx), a) \<in> set (intra_predecessor_addr_list g v ctx)"
    using e by (force simp: intra_predecessor_addr_list_def
        set_intra_predecessor_list[OF finE] intra_predecessors_def)
  hence mem: "?t \<in> set (trees v ctx)" by (force intro: rev_image_eqI)
  have "fst (dg_spec_step S a (locals (sigma (Inl (u, ctx)))) (globs (sigma (Inr gk0))))
      = globs (sides_of_rhs ?t sigma (Inr gk0))"
    by (simp add: edge_tree_global_ctx)
  also have "\<dots> \<le> globs (sides_of_rhs (side_rhs_fold_dg (acc0 v) (trees v ctx)) sigma (Inr gk0))"
    using sides_le_side_rhs_fold_dg[OF mem, where k = "Inr gk0"]
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
    and sin: "s \<in> gammaM (sg (Inl (u, ctx)))" and st: "s' \<in> edge_step a s"
  shows "s' \<in> gammaM (sg (Inl (v, ctx)))"
proof (cases "(u, ctx) \<in> vars")
  case False
  hence "gammaM (sg (Inl (u, ctx))) = {}" by (rule sg_uncovered_empty)
  thus ?thesis using sin by simp
next
  case True
  hence cov_v: "(v, ctx) \<in> vars" using e by (rule fwd)
  let ?d = "locals (sigma (Inl (u, ctx)))"
  let ?g = "globs (sigma (Inr gk0))"
  have sin': "s \<in> gammaDG ?d ?g"
    using sin True by (simp add: sg_cov)
  have "{s} \<subseteq> gammaDG ?d ?g" using sin' by simp
  hence "edge_collect a {s} \<subseteq> edge_collect a (gammaDG ?d ?g)" by (rule edge_collect_mono)
  moreover have "s' \<in> edge_collect a {s}" using st by (simp add: edge_collect_single)
  ultimately have "s' \<in> edge_collect a (gammaDG ?d ?g)" by blast
  hence "s' \<in> gammaDG (snd (dg_spec_step S a ?d ?g)) (fst (dg_spec_step S a ?d ?g))"
    using step_sound_fs by blast
  also have "\<dots> \<subseteq> gammaDG (locals (sigma (Inl (v, ctx)))) (globs (sigma (Inr gk0)))"
    by (rule gammaDG_mono[OF edge_bound_local[OF cov_v e] edge_bound_global[OF cov_v e]])
  also have "\<dots> = gammaM (sg (Inl (v, ctx)))"
    using cov_v by (simp add: sg_cov)
  finally show ?thesis .
qed

subsection \<open>COMB: the guarded combine transport\<close>

lemma dg_ctx_act_comb_covered:
  assumes covCl: "(cl, c1) \<in> vars"
    and covEx: "(ex, c2) \<in> vars"
    and covV: "(v, cv) \<in> vars"
    and s: "s \<in> gammaM (sg (Inl (cl, c1)))"
    and t: "t \<in> gammaM (sg (Inl (ex, c2)))"
    and bound_local:
      "snd (dgs_combine S ci
              (dgs_caller_cont S ci (locals (sigma (Inl (cl, c1)))) (globs (sigma (Inr gk0))))
              (locals (sigma (Inl (ex, c2))))
              (globs (sigma (Inr gk0))))
       \<le> locals (sigma (Inl (v, cv)))"
    and bound_global:
      "fst (dgs_combine S ci
              (dgs_caller_cont S ci (locals (sigma (Inl (cl, c1)))) (globs (sigma (Inr gk0))))
              (locals (sigma (Inl (ex, c2))))
              (globs (sigma (Inr gk0))))
       \<le> globs (sigma (Inr gk0))"
  shows "combine_collect gs (ci_dst ci) s t \<in> gammaM (sg (Inl (v, cv)))"
proof -
  let ?Dc = "locals (sigma (Inl (cl, c1)))"
  let ?De = "locals (sigma (Inl (ex, c2)))"
  let ?G = "globs (sigma (Inr gk0))"
  have sin: "s \<in> gammaDG ?Dc ?G"
    using s covCl by (simp add: sg_cov)
  have tin: "t \<in> gammaDG ?De ?G"
    using t covEx by (simp add: sg_cov)
  have "combine_collect gs (ci_dst ci) s t
        \<in> gammaDG (snd (dgs_combine S ci (dgs_caller_cont S ci ?Dc ?G) ?De ?G))
                   (fst (dgs_combine S ci (dgs_caller_cont S ci ?Dc ?G) ?De ?G))"
    using combine_sound_at_call_fs[where ci = ci, OF sin tin order_refl] .
  also have "\<dots> \<subseteq> gammaDG (locals (sigma (Inl (v, cv)))) ?G"
    by (rule gammaDG_mono[OF bound_local bound_global])
  also have "\<dots> = gammaM (sg (Inl (v, cv)))"
    using covV by (simp add: sg_cov)
  finally show ?thesis .
qed

end

end
