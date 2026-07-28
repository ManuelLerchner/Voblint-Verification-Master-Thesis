theory DG_Ctx_Activation
  imports DG_Soundness
begin

section \<open>DG-native discharge of the activation obligations\<close>

text \<open>
  The routed generator interprets solutions through \<^const>\<open>gamma_unit\<close> with one shared
  global slot \<open>Inr gk0\<close>.  This locale derives the edge and combine closure obligations from a
  \<^const>\<open>part_post_solution\<close>, a sound D/G specification, the routing hooks, and a guarded
  solution reader.  Concrete analyses supply the entry and callee-seed coverage obligations.

  The D/G layer transports abstract states at the caller, callee-result, and continuation
  slots.  The trace semantics supplies the matched caller/callee relation, so this layer does
  not reconstruct activation pairing.
\<close>

locale dg_ctx_activation = sound_dg_spec S gamma_unit
  for S :: "('a::sound_domain abs_state, 'a abs_state) dg_spec" +
  fixes g :: cfg and gk0 :: 'k
    and route :: "pp \<Rightarrow> 'c \<Rightarrow> 'a abs_state \<Rightarrow> call_action \<Rightarrow> 'c"
    and cmb :: "(pp \<Rightarrow> 'c \<Rightarrow> 'a abs_state \<Rightarrow> call_action \<Rightarrow> 'c) \<Rightarrow> 'c \<Rightarrow> call_action \<Rightarrow> pp \<Rightarrow> pp
                  \<Rightarrow> (pp \<times> 'c, 'k, ('a abs_state, 'a abs_state) dg_state) strategy_tree"
    and extra :: "(pp \<Rightarrow> 'c \<Rightarrow> 'a abs_state \<Rightarrow> call_action \<Rightarrow> 'c) \<Rightarrow> 'c \<Rightarrow> pp
                  \<Rightarrow> (pp \<times> 'c, 'k, ('a abs_state, 'a abs_state) dg_state) strategy_tree list"
    and bot0 s0d s0g :: "'a abs_state"
    and sigma :: "pp \<times> 'c + 'k \<Rightarrow> ('a abs_state, 'a abs_state) dg_state"
    and vars :: "(pp \<times> 'c) set" and x0 :: "pp \<times> 'c"
    and sg :: "pp \<times> 'c + 'k \<Rightarrow> 'a abs_state"
  assumes finE: "finite (intra g)"
    and pp: "part_post_solution
               (side_cfg_T_eff_keyed_seed_dg intra_predecessor_list (\<lambda>_. gk0)
                  route cmb extra g S bot0 s0d s0g) x0 sigma vars"
    and sg_cov: "\<And>v c. (v, c) \<in> vars
        \<Longrightarrow> sg (Inl (v, c)) = locals (sigma (Inl (v, c))) \<squnion> globs (sigma (Inr gk0))"
    and sg_uncov: "\<And>v c. (v, c) \<notin> vars \<Longrightarrow> \<lbrakk>sg (Inl (v, c))\<rbrakk> = {}"
    and fwd: "\<And>u a v c. (u, c) \<in> vars \<Longrightarrow> (u, a, v) \<in> intra g
        \<Longrightarrow> (v, c) \<in> vars"
begin

abbreviation Gen :: "(pp \<times> 'c, 'k, ('a abs_state, 'a abs_state) dg_state) eqsT" where
  "Gen \<equiv> side_cfg_T_eff_keyed_seed_dg intra_predecessor_list (\<lambda>_. gk0)
           route cmb extra g S bot0 s0d s0g"

abbreviation acc0 :: "pp \<Rightarrow> 'a abs_state" where
  "acc0 v \<equiv> (if v = cfg_entry g then bot0 \<squnion> s0d else bot0)"

abbreviation trees :: "pp \<Rightarrow> 'c
    \<Rightarrow> (pp \<times> 'c, 'k, ('a abs_state, 'a abs_state) dg_state) strategy_tree list" where
  "trees v ctx \<equiv>
     map (\<lambda>(u, a). map_gtree (\<lambda>_. gk0) (map_ltree (\<lambda>w. (w, ctx)) (apply_dg_spec S a u)))
         (intra_predecessor_list g v)
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

subsection \<open>The guarded reader\<close>

lemma sg_uncovered_empty: "(v, ctx) \<notin> vars \<Longrightarrow> \<lbrakk>sg (Inl (v, ctx))\<rbrakk> = {}"
  by (rule sg_uncov)

subsection \<open>Routed intra edge tree denotation\<close>

lemma edge_tree_local_ctx:
  "locals (traverse_rhs
       (map_gtree (\<lambda>_. gk0) (map_ltree (\<lambda>w. (w, ctx)) (apply_dg_spec S a u))) sigma)
   = snd (dg_spec_step S a (locals (sigma (Inl (u, ctx)))) (globs (sigma (Inr gk0))))"
  unfolding apply_dg_spec_def
  by (subst traverse_intra_keyed) (simp add: traverse_dg_edge_tree)

lemma edge_tree_global_ctx:
  "globs (sides_of_rhs
       (map_gtree (\<lambda>_. gk0) (map_ltree (\<lambda>w. (w, ctx)) (apply_dg_spec S a u)))
       sigma (Inr gk0))
   = fst (dg_spec_step S a (locals (sigma (Inl (u, ctx)))) (globs (sigma (Inr gk0))))"
proof -
  have step1:
    "sides_of_rhs (map_gtree (\<lambda>_. gk0) (map_ltree (\<lambda>w. (w, ctx)) (apply_dg_spec S a u)))
       sigma (Inr gk0)
     = sides_of_rhs (apply_dg_spec S a u)
         (\<lambda>z. sigma (map_sum (\<lambda>w. (w, ctx)) (\<lambda>_. gk0) z)) (Inr ())"
  proof -
    have "sides_of_rhs (map_gtree (\<lambda>_. gk0) (map_ltree (\<lambda>w. (w, ctx)) (apply_dg_spec S a u)))
            sigma (Inr ((\<lambda>_. gk0) ()))
        = sides_of_rhs (map_ltree (\<lambda>w. (w, ctx)) (apply_dg_spec S a u))
            (\<lambda>z. sigma (map_sum id (\<lambda>_. gk0) z)) (Inr ())"
      by (rule sides_map_gtree_unit)
    thus ?thesis by (simp add: sides_map_ltree_Inr sum.map_comp o_def)
  qed
  have "globs (sides_of_rhs (map_gtree (\<lambda>_. gk0) (map_ltree (\<lambda>w. (w, ctx)) (apply_dg_spec S a u)))
          sigma (Inr gk0))
      = globs (sides_of_rhs (apply_dg_spec S a u)
          (\<lambda>z. sigma (map_sum (\<lambda>w. (w, ctx)) (\<lambda>_. gk0) z)) (Inr ()))"
    by (rule arg_cong[OF step1])
  also have "\<dots> = fst (dg_spec_step S a (locals (sigma (Inl (u, ctx)))) (globs (sigma (Inr gk0))))"
    unfolding apply_dg_spec_def by (simp add: sides_dg_edge_tree_Inr)
  finally show ?thesis .
qed

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
  let ?t = "map_gtree (\<lambda>_. gk0) (map_ltree (\<lambda>w. (w, ctx)) (apply_dg_spec S a u))"
  have pred: "(u, a) \<in> set (intra_predecessor_list g v)"
    using e by (simp add: set_intra_predecessor_list[OF finE] intra_predecessors_def)
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
  let ?t = "map_gtree (\<lambda>_. gk0) (map_ltree (\<lambda>w. (w, ctx)) (apply_dg_spec S a u))"
  have pred: "(u, a) \<in> set (intra_predecessor_list g v)"
    using e by (simp add: set_intra_predecessor_list[OF finE] intra_predecessors_def)
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
    and sin: "s \<in> \<lbrakk>sg (Inl (u, ctx))\<rbrakk>" and st: "edge_step a s = Some s'"
  shows "s' \<in> \<lbrakk>sg (Inl (v, ctx))\<rbrakk>"
proof (cases "(u, ctx) \<in> vars")
  case False
  hence "\<lbrakk>sg (Inl (u, ctx))\<rbrakk> = {}" by (rule sg_uncovered_empty)
  thus ?thesis using sin by simp
next
  case True
  hence cov_v: "(v, ctx) \<in> vars" using e by (rule fwd)
  let ?d = "locals (sigma (Inl (u, ctx)))"
  let ?g = "globs (sigma (Inr gk0))"
  have sin': "s \<in> gamma_unit ?d ?g"
    using sin True by (simp add: sg_cov gamma_unit_def)
  have "{s} \<subseteq> gamma_unit ?d ?g" using sin' by simp
  hence "edge_collect a {s} \<subseteq> edge_collect a (gamma_unit ?d ?g)" by (rule edge_collect_mono)
  moreover have "s' \<in> edge_collect a {s}" using st by (simp add: edge_collect_single)
  ultimately have "s' \<in> edge_collect a (gamma_unit ?d ?g)" by blast
  also have "\<dots> \<subseteq> (case dg_spec_step S a ?d ?g of (g', d') \<Rightarrow> gamma_unit d' g')"
    by (rule step_sound)
  finally have "s' \<in> (case dg_spec_step S a ?d ?g of (g', d') \<Rightarrow> gamma_unit d' g')" .
  hence "s' \<in> gamma_unit (snd (dg_spec_step S a ?d ?g)) (fst (dg_spec_step S a ?d ?g))"
    by (simp add: case_prod_beta)
  also have "\<dots> \<subseteq> gamma_unit (locals (sigma (Inl (v, ctx)))) (globs (sigma (Inr gk0)))"
    by (rule gamma_unit_mono[OF edge_bound_local[OF cov_v e] edge_bound_global[OF cov_v e]])
  also have "\<dots> = \<lbrakk>sg (Inl (v, ctx))\<rbrakk>"
    using cov_v by (simp add: sg_cov gamma_unit_def)
  finally show ?thesis .
qed

subsection \<open>COMB: the guarded combine transport\<close>

text \<open>The combine analogue of \<open>dg_ctx_act_edge\<close>'s covered branch: given covered caller /
  callee-exit / return slots and the abstract combine bound at those slots, the return
  combine lands in the resumed reader.  The abstract bound is stated over \<open>S\<close> directly, so
  the concrete witness supplies it from its post-solution or executable evaluation without
  re-deriving the \<^const>\<open>gamma_unit\<close> transport.  Both caller and callee exit read the same
  shared global slot \<open>Inr gk0\<close>.\<close>

lemma dg_ctx_act_comb_covered:
  assumes covCl: "(cl, c1) \<in> vars"
    and covEx: "(ex, c2) \<in> vars"
    and covV: "(v, cv) \<in> vars"
    and s: "s \<in> \<lbrakk>sg (Inl (cl, c1))\<rbrakk>"
    and t: "t \<in> \<lbrakk>sg (Inl (ex, c2))\<rbrakk>"
    and bound:
      "snd (dgs_combine S dst (locals (sigma (Inl (cl, c1)))) (locals (sigma (Inl (ex, c2))))
              (globs (sigma (Inr gk0))))
       \<squnion> fst (dgs_combine S dst (locals (sigma (Inl (cl, c1)))) (locals (sigma (Inl (ex, c2))))
              (globs (sigma (Inr gk0))))
       \<le> locals (sigma (Inl (v, cv))) \<squnion> globs (sigma (Inr gk0))"
  shows "combine_collect dst s t \<in> \<lbrakk>sg (Inl (v, cv))\<rbrakk>"
proof -
  let ?Dc = "locals (sigma (Inl (cl, c1)))"
  let ?De = "locals (sigma (Inl (ex, c2)))"
  let ?G = "globs (sigma (Inr gk0))"
  have sin: "s \<in> gamma_unit ?Dc ?G"
    using s covCl by (simp add: sg_cov gamma_unit_def)
  have tin: "t \<in> gamma_unit ?De ?G"
    using t covEx by (simp add: sg_cov gamma_unit_def)
  have "combine_collect dst s t
        \<in> (case dgs_combine S dst ?Dc ?De ?G of (g', d') \<Rightarrow> gamma_unit d' g')"
    by (rule combine_sound[OF sin tin])
  hence "combine_collect dst s t
        \<in> gamma_unit (snd (dgs_combine S dst ?Dc ?De ?G)) (fst (dgs_combine S dst ?Dc ?De ?G))"
    by (simp add: case_prod_beta)
  also have "\<dots> \<subseteq> gamma_unit (locals (sigma (Inl (v, cv)))) ?G"
    unfolding gamma_unit_def
    by (rule gamma_state_mono) (rule bound[unfolded gamma_unit_def])
  also have "\<dots> = \<lbrakk>sg (Inl (v, cv))\<rbrakk>"
    using covV by (simp add: sg_cov gamma_unit_def)
  finally show ?thesis .
qed

end

end
