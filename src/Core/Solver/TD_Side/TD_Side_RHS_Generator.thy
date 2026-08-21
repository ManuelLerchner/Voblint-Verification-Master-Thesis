theory TD_Side_RHS_Generator
  imports TD_Side_Eff_Pipeline
begin

section \<open>Effectful RHS generator locales\<close>

text \<open>
  @{term unit_etf_of_transfer} and @{term mixed_etf_of_transfer} share combine-tree
  shape and differ only in per-edge tree dispatch.  These locales bundle the
  transfer-tree shape, dependency-staticness facts, and solver-side monotonicity
  packaging for each shape.
\<close>

subsection \<open>Shared combine-tree infrastructure\<close>

locale sound_rhs_generator_base =
  fixes gs :: "vname \<Rightarrow> bool"
    and etf :: "(unit, 'a::sound_domain) effectful_domain_transfer"
    and Fc :: "call_info \<Rightarrow> 'a abs_state \<Rightarrow> 'a abs_state \<Rightarrow> 'a abs_state"
  assumes comb[simp]:
    "\<And>cc ex ci.
       etf_combine_collect etf ci cc ex =
       unit_combine_tree gs (Fc ci) cc ex"
begin

lemma dep_aux_comb_call:
  "Inl cc \<in> dep_aux \<sigma> (etf_combine_collect etf ci cc ex)"
  by (simp add: comb unit_combine_tree_def)

lemma dep_aux_comb_exit:
  "Inl ex \<in> dep_aux \<sigma> (etf_combine_collect etf ci cc ex)"
  by (simp add: comb unit_combine_tree_def)

lemma comb_inr:
  "\<And>cc ex ci \<sigma> g. local_bot_on_locals_lift gs (sides_of_rhs (etf_combine_collect etf ci cc ex) \<sigma> (Inr g))"
  unfolding comb by (rule sides_inr_local_bot_unit_combine_tree)

lemma comb_coherent:
  "\<And>cc ex ci \<sigma>. reachability_coherent_tree (etf_combine_collect etf ci cc ex) \<sigma>"
  unfolding comb by (rule reachability_coherent_unit_combine_tree)

end

locale sound_rhs_generator_static = sound_rhs_generator_base
begin

lemma static_deps_comb:
  "static_deps (etf_combine_collect etf dst cc ex)"
  by (simp add: comb static_deps_def unit_combine_tree_def Let_def)

end


subsection \<open>Mixed local/unit edge-tree generator\<close>

lemma static_deps_local_edge_tree:
  "static_deps (local_edge_tree gs f u)"
  unfolding static_deps_def using dep_aux_local_edge_tree by blast

lemma dep_aux_local_edge_tree_src:
  "Inl u \<in> dep_aux \<sigma> (local_edge_tree gs f u)"
  by (rule Inl_dep_aux_local_edge_tree)

lemma static_deps_unit_edge_tree:
  "static_deps (unit_edge_tree gs f u)"
  unfolding static_deps_def unit_edge_tree_def Let_def by simp

lemma dep_aux_unit_edge_tree_src:
  "Inl u \<in> dep_aux \<sigma> (unit_edge_tree gs f u)"
  unfolding unit_edge_tree_def by simp

text \<open>Each per-edge tree is a local or a unit edge tree.  The disjunction form
  subsumes both the pure-unit generator (always the unit disjunct) and a genuine
  local/unit mix, so one locale covers both.\<close>
locale mixed_rhs_generator = sound_rhs_generator_static +
  fixes F :: "edge_action \<Rightarrow> 'a::sound_domain abs_state \<Rightarrow> 'a abs_state"
    and Fe :: "vname list \<Rightarrow> exp list \<Rightarrow> 'a abs_state \<Rightarrow> 'a abs_state"
  assumes edge:
      "\<And>a u.
         apply_etf etf a u = local_edge_tree gs (F a) u
       \<or> apply_etf etf a u = unit_edge_tree gs (F a) u"
    and enter[simp]:
      "\<And>cl fs as.
         etf_enter etf fs as cl = unit_edge_tree gs (Fe fs as) cl"
begin

lemma edge_inr:
  "local_bot_on_locals_lift gs (sides_of_rhs (apply_etf etf a u) \<sigma> (Inr g))"
  using edge[of a u]
  by (elim disjE)
     (simp_all add: sides_inr_local_bot_local_edge_tree sides_inr_local_bot_unit_edge_tree)

lemma static_deps_edge:
  "static_deps (apply_etf etf a u)"
  using edge[of a u]
  by (elim disjE) (simp_all add: static_deps_local_edge_tree static_deps_unit_edge_tree)

lemma dep_aux_edge:
  "Inl u \<in> dep_aux \<sigma> (apply_etf etf a u)"
  using edge[of a u]
  by (elim disjE) (simp_all add: dep_aux_local_edge_tree_src dep_aux_unit_edge_tree_src)

lemma enter_inr:
  "local_bot_on_locals_lift gs (sides_of_rhs (etf_enter etf fs as cl) \<sigma> (Inr g))"
  unfolding enter by (rule sides_inr_local_bot_unit_edge_tree)

lemma static_deps_enter:
  "static_deps (etf_enter etf fs as cl)"
  unfolding enter by (rule static_deps_unit_edge_tree)

lemma dep_aux_enter:
  "Inl cl \<in> dep_aux \<sigma> (etf_enter etf fs as cl)"
  unfolding enter by (rule dep_aux_unit_edge_tree_src)

lemma edge_coherent:
  "reachability_coherent_tree (apply_etf etf a u) \<sigma>"
  using edge[of a u]
  by (elim disjE)
     (simp_all add: reachability_coherent_local_edge_tree reachability_coherent_unit_edge_tree)

lemma enter_coherent:
  "reachability_coherent_tree (etf_enter etf fs as cl) \<sigma>"
  unfolding enter by (rule reachability_coherent_unit_edge_tree)

lemma cone_compatible:
  "cone_compatible_etf gs etf"
  unfolding cone_compatible_etf_def
  by (intro conjI allI)
     (rule dep_aux_edge, rule dep_aux_comb_call, rule dep_aux_comb_exit, rule dep_aux_enter,
      rule static_deps_edge, rule static_deps_comb, rule static_deps_enter,
      rule edge_inr, rule comb_inr, rule enter_inr,
      rule edge_coherent, rule comb_coherent, rule enter_coherent)

end

locale mixed_rhs_generator_mono = mixed_rhs_generator +
  assumes F_mono:
      "\<And>a s1 s2. s1 \<le> s2 \<Longrightarrow> F a s1 \<le> F a s2"
    and Fe_mono:
      "\<And>fs as s1 s2. s1 \<le> s2 \<Longrightarrow> Fe fs as s1 \<le> Fe fs as s2"
    and Fc_mono:
      "\<And>dst s1 s2 t1 t2. s1 \<le> s2 \<Longrightarrow> t1 \<le> t2 \<Longrightarrow> Fc dst s1 t1 \<le> Fc dst s2 t2"
begin

lemma is_mono_eq:
  "is_mono_eq (side_cfg_T_eff gs g etf bot0 s0 ())"
  apply (rule side_cfg_T_eff_is_mono_eq_gen)
  subgoal for a u s1 s2
  proof -
    assume le: "s1 \<le> s2"
    show "traverse_rhs (apply_etf etf a u) s1 \<le> traverse_rhs (apply_etf etf a u) s2"
    proof (cases "apply_etf etf a u = local_edge_tree gs (F a) u")
      case True
      then have eq: "apply_etf etf a u = local_edge_tree gs (F a) u" .
      have lu: "s1 (Inl u) \<le> s2 (Inl u)" by (rule le_funD[OF le])
      have lg: "s1 (Inr ()) \<le> s2 (Inr ())" by (rule le_funD[OF le])
      show ?thesis unfolding eq traverse_local_edge_tree
        by (rule res_local_mono[OF F_mono le])
    next
      case False
      then have eq: "apply_etf etf a u = unit_edge_tree gs (F a) u" using edge[of a u] by blast
      show ?thesis unfolding eq traverse_unit_edge_tree
        by (rule map_lift_mono[OF restrict_local_for_mono res_edge_mono[OF F_mono le]])
    qed
  qed
  subgoal for cl fs as s1 s2
    by (simp add: enter traverse_unit_edge_tree)
       (auto intro: map_lift_mono restrict_local_for_mono res_edge_mono[OF Fe_mono])
  subgoal for cc ex dst s1 s2
    by (simp add: comb traverse_unit_combine_tree)
       (auto intro: map_lift_mono restrict_local_for_mono res_combine_mono[OF Fc_mono])
  done

lemma mono_sides:
  "mono_sides (side_cfg_T_eff gs g etf bot0 s0 ())"
  apply (rule side_cfg_T_eff_mono_sides_gen)
  subgoal for a u s1 s2
  proof -
    assume le: "s1 \<le> s2"
    show "sides_of_rhs (apply_etf etf a u) s1 \<le> sides_of_rhs (apply_etf etf a u) s2"
    proof (rule le_funI)
      fix k
      show "sides_of_rhs (apply_etf etf a u) s1 k \<le> sides_of_rhs (apply_etf etf a u) s2 k"
      proof (cases "apply_etf etf a u = local_edge_tree gs (F a) u")
        case True
        then have eq: "apply_etf etf a u = local_edge_tree gs (F a) u" .
        show ?thesis unfolding eq
          by (cases k; simp add: sides_local_edge_tree_Inl sides_local_edge_tree_Inr)
      next
        case False
        then have eq: "apply_etf etf a u = unit_edge_tree gs (F a) u" using edge[of a u] by blast
        show ?thesis
        proof (cases k)
          case (Inl x)
          show ?thesis
            by (simp add: eq Inl unit_edge_tree_def Let_def)
        next
          case (Inr y)
          show ?thesis
            using Inr le
            by (cases y)
               (simp add: eq sides_unit_edge_tree_Inr,
                rule map_lift_mono[OF restrict_global_for_mono res_edge_mono[OF F_mono le]])
        qed
      qed
    qed
  qed
  subgoal for cl fs as s1 s2
  proof -
    assume le: "s1 \<le> s2"
    show "sides_of_rhs (etf_enter etf fs as cl) s1 \<le> sides_of_rhs (etf_enter etf fs as cl) s2"
    proof (rule le_funI)
      fix k
      show "sides_of_rhs (etf_enter etf fs as cl) s1 k \<le> sides_of_rhs (etf_enter etf fs as cl) s2 k"
      proof (cases k)
        case (Inl x)
        show ?thesis
          by (simp add: enter Inl unit_edge_tree_def Let_def)
      next
        case (Inr y)
        show ?thesis
          using Inr le
          by (cases y)
             (simp add: enter sides_unit_edge_tree_Inr,
              rule map_lift_mono[OF restrict_global_for_mono res_edge_mono[OF Fe_mono le]])
      qed
    qed
  qed
  subgoal for cc dst ex s1 s2
  proof -
    assume le: "s1 \<le> s2"
    show "sides_of_rhs (etf_combine_collect etf dst cc ex) s1 \<le> sides_of_rhs (etf_combine_collect etf dst cc ex) s2"
    proof (rule le_funI)
      fix k
      show "sides_of_rhs (etf_combine_collect etf dst cc ex) s1 k \<le> sides_of_rhs (etf_combine_collect etf dst cc ex) s2 k"
      proof (cases k)
        case (Inl x)
        show ?thesis
          by (simp add: comb Inl unit_combine_tree_def Let_def)
      next
        case (Inr y)
        show ?thesis
          using Inr le
          by (cases y)
             (simp add: comb sides_unit_combine_tree_Inr,
              rule map_lift_mono[OF restrict_global_for_mono
                res_combine_mono[OF Fc_mono le]])
      qed
    qed
  qed
  done

lemma mono_deps:
  "mono_deps (side_cfg_T_eff gs g etf bot0 s0 ())"
  apply (rule side_cfg_T_eff_mono_deps_gen)
  using static_deps_edge static_deps_enter static_deps_comb
  by simp_all

lemma threefold_mono:
  "threefold_mono (side_cfg_T_eff gs g etf bot0 s0 ())"
  unfolding threefold_mono_def
  using is_mono_eq mono_sides mono_deps
  by blast

end

subsection \<open>Mixed local/unit/local-branch edge-tree generator\<close>

text \<open>
  \<open>local_branch_tree\<close>'s counterpart of the local/unit \<open>static_deps\<close> facts above:
  \<open>local_branch_tree\<close> reads only the queried local unknown (\<open>su <- read_local u\<close>,
  see its own docstring), so its dependency set is the same regardless of the
  environment, exactly as for \<open>local_edge_tree\<close>.
\<close>
lemma static_deps_local_branch_tree:
  "static_deps (local_branch_tree gs h u)"
  unfolding static_deps_def using dep_aux_local_branch_tree by blast

lemma dep_aux_local_branch_tree_src:
  "Inl u \<in> dep_aux \<sigma> (local_branch_tree gs h u)"
  by (rule Inl_dep_aux_local_branch_tree)

text \<open>
  \<open>mixed_rhs_generator\<close>'s generalization for a domain whose branch transfer is
  lifted: a branch edge (\<open>EA_Assume\<close>/\<open>EA_AssumeNot\<close>) may additionally route
  through \<^const>\<open>local_branch_tree\<close> against \<open>Fb\<close> -- the domain's own
  \<open>branch_lifted\<close> wrapped to the uniform \<open>edge_action \<Rightarrow> 'a abs_state \<Rightarrow>
  'a abs_state lifted\<close> shape (\<open>Fb (EA_Assume b) = branch_lifted b True\<close>,
  \<open>Fb (EA_AssumeNot b) = branch_lifted b False\<close>, arbitrary elsewhere) -- rather
  than only ever \<^const>\<open>local_edge_tree\<close> against the same \<open>F\<close> every other local
  action uses. \<open>F\<close> alone still covers every action's \<^const>\<open>unit_edge_tree\<close>
  disjunct, branch included, since the domain's plain \<open>branch\<close> field is a
  legitimate (if imprecise about \<^const>\<open>Bot\<close>) `apply_tf`-shaped transfer there;
  M3 established that \<^const>\<open>unit_edge_tree\<close> already collapses a whole-state-
  \<^const>\<open>bot\<close> branch result to outer \<^const>\<open>Bot\<close> correctly, so it needs no
  lifted counterpart of its own.
\<close>
locale mixed_branch_rhs_generator = sound_rhs_generator_static +
  fixes F :: "edge_action \<Rightarrow> 'a::sound_domain abs_state \<Rightarrow> 'a abs_state"
    and Fe :: "vname list \<Rightarrow> exp list \<Rightarrow> 'a abs_state \<Rightarrow> 'a abs_state"
    and Fb :: "edge_action \<Rightarrow> 'a abs_state \<Rightarrow> 'a abs_state lifted"
  assumes edge:
      "\<And>a u.
         apply_etf etf a u = local_edge_tree gs (F a) u
       \<or> apply_etf etf a u = unit_edge_tree gs (F a) u
       \<or> apply_etf etf a u = local_branch_tree gs (Fb a) u"
    and enter[simp]:
      "\<And>cl fs as.
         etf_enter etf fs as cl = unit_edge_tree gs (Fe fs as) cl"
begin

lemma edge_inr:
  "local_bot_on_locals_lift gs (sides_of_rhs (apply_etf etf a u) \<sigma> (Inr g))"
  using edge[of a u]
  by (elim disjE)
     (simp_all add: sides_inr_local_bot_local_edge_tree sides_inr_local_bot_unit_edge_tree
        sides_inr_local_bot_local_branch_tree)

lemma static_deps_edge:
  "static_deps (apply_etf etf a u)"
  using edge[of a u]
  by (elim disjE)
     (simp_all add: static_deps_local_edge_tree static_deps_unit_edge_tree
        static_deps_local_branch_tree)

lemma dep_aux_edge:
  "Inl u \<in> dep_aux \<sigma> (apply_etf etf a u)"
  using edge[of a u]
  by (elim disjE)
     (simp_all add: dep_aux_local_edge_tree_src dep_aux_unit_edge_tree_src
        dep_aux_local_branch_tree_src)

lemma enter_inr:
  "local_bot_on_locals_lift gs (sides_of_rhs (etf_enter etf fs as cl) \<sigma> (Inr g))"
  unfolding enter by (rule sides_inr_local_bot_unit_edge_tree)

lemma static_deps_enter:
  "static_deps (etf_enter etf fs as cl)"
  unfolding enter by (rule static_deps_unit_edge_tree)

lemma dep_aux_enter:
  "Inl cl \<in> dep_aux \<sigma> (etf_enter etf fs as cl)"
  unfolding enter by (rule dep_aux_unit_edge_tree_src)

lemma edge_coherent:
  "reachability_coherent_tree (apply_etf etf a u) \<sigma>"
  using edge[of a u]
  by (elim disjE)
     (simp_all add: reachability_coherent_local_edge_tree reachability_coherent_unit_edge_tree
        reachability_coherent_local_branch_tree)

lemma enter_coherent:
  "reachability_coherent_tree (etf_enter etf fs as cl) \<sigma>"
  unfolding enter by (rule reachability_coherent_unit_edge_tree)

lemma cone_compatible:
  "cone_compatible_etf gs etf"
  unfolding cone_compatible_etf_def
  by (intro conjI allI)
     (rule dep_aux_edge, rule dep_aux_comb_call, rule dep_aux_comb_exit, rule dep_aux_enter,
      rule static_deps_edge, rule static_deps_comb, rule static_deps_enter,
      rule edge_inr, rule comb_inr, rule enter_inr,
      rule edge_coherent, rule comb_coherent, rule enter_coherent)

end

locale mixed_branch_rhs_generator_mono = mixed_branch_rhs_generator +
  assumes F_mono:
      "\<And>a s1 s2. s1 \<le> s2 \<Longrightarrow> F a s1 \<le> F a s2"
    and Fe_mono:
      "\<And>fs as s1 s2. s1 \<le> s2 \<Longrightarrow> Fe fs as s1 \<le> Fe fs as s2"
    and Fb_mono:
      "\<And>a s1 s2. s1 \<le> s2 \<Longrightarrow> Fb a s1 \<le> Fb a s2"
    and Fc_mono:
      "\<And>dst s1 s2 t1 t2. s1 \<le> s2 \<Longrightarrow> t1 \<le> t2 \<Longrightarrow> Fc dst s1 t1 \<le> Fc dst s2 t2"
begin

lemma is_mono_eq:
  "is_mono_eq (side_cfg_T_eff gs g etf bot0 s0 ())"
  apply (rule side_cfg_T_eff_is_mono_eq_gen)
  subgoal for a u s1 s2
  proof -
    assume le: "s1 \<le> s2"
    show "traverse_rhs (apply_etf etf a u) s1 \<le> traverse_rhs (apply_etf etf a u) s2"
    proof (cases "apply_etf etf a u = local_edge_tree gs (F a) u")
      case True
      then have eq: "apply_etf etf a u = local_edge_tree gs (F a) u" .
      show ?thesis unfolding eq traverse_local_edge_tree
        by (rule res_local_mono[OF F_mono le])
    next
      case not_local: False
      show ?thesis
      proof (cases "apply_etf etf a u = unit_edge_tree gs (F a) u")
        case True
        then have eq: "apply_etf etf a u = unit_edge_tree gs (F a) u" .
        show ?thesis unfolding eq traverse_unit_edge_tree
          by (rule map_lift_mono[OF restrict_local_for_mono res_edge_mono[OF F_mono le]])
      next
        case False
        then have eq: "apply_etf etf a u = local_branch_tree gs (Fb a) u"
          using not_local edge[of a u] by blast
        show ?thesis unfolding eq traverse_local_branch_tree
          by (rule res_local_branch_mono[OF Fb_mono le])
      qed
    qed
  qed
  subgoal for cl fs as s1 s2
    by (simp add: enter traverse_unit_edge_tree)
       (auto intro: map_lift_mono restrict_local_for_mono res_edge_mono[OF Fe_mono])
  subgoal for cc ex dst s1 s2
    by (simp add: comb traverse_unit_combine_tree)
       (auto intro: map_lift_mono restrict_local_for_mono res_combine_mono[OF Fc_mono])
  done

lemma mono_sides:
  "mono_sides (side_cfg_T_eff gs g etf bot0 s0 ())"
  apply (rule side_cfg_T_eff_mono_sides_gen)
  subgoal for a u s1 s2
  proof -
    assume le: "s1 \<le> s2"
    show "sides_of_rhs (apply_etf etf a u) s1 \<le> sides_of_rhs (apply_etf etf a u) s2"
    proof (rule le_funI)
      fix k
      show "sides_of_rhs (apply_etf etf a u) s1 k \<le> sides_of_rhs (apply_etf etf a u) s2 k"
      proof (cases "apply_etf etf a u = local_edge_tree gs (F a) u")
        case True
        then have eq: "apply_etf etf a u = local_edge_tree gs (F a) u" .
        show ?thesis unfolding eq
          by (cases k; simp add: sides_local_edge_tree_Inl sides_local_edge_tree_Inr)
      next
        case not_local: False
        show ?thesis
        proof (cases "apply_etf etf a u = unit_edge_tree gs (F a) u")
          case True
          then have eq: "apply_etf etf a u = unit_edge_tree gs (F a) u" .
          show ?thesis
          proof (cases k)
            case (Inl x)
            show ?thesis
              by (simp add: eq Inl unit_edge_tree_def Let_def)
          next
            case (Inr y)
            show ?thesis
              using Inr le
              by (cases y)
                 (simp add: eq sides_unit_edge_tree_Inr,
                  rule map_lift_mono[OF restrict_global_for_mono res_edge_mono[OF F_mono le]])
          qed
        next
          case False
          then have eq: "apply_etf etf a u = local_branch_tree gs (Fb a) u"
            using not_local edge[of a u] by blast
          show ?thesis unfolding eq
            by (cases k; simp add: sides_local_branch_tree_Inl sides_local_branch_tree_Inr)
        qed
      qed
    qed
  qed
  subgoal for cl fs as s1 s2
  proof -
    assume le: "s1 \<le> s2"
    show "sides_of_rhs (etf_enter etf fs as cl) s1 \<le> sides_of_rhs (etf_enter etf fs as cl) s2"
    proof (rule le_funI)
      fix k
      show "sides_of_rhs (etf_enter etf fs as cl) s1 k \<le> sides_of_rhs (etf_enter etf fs as cl) s2 k"
      proof (cases k)
        case (Inl x)
        show ?thesis
          by (simp add: enter Inl unit_edge_tree_def Let_def)
      next
        case (Inr y)
        show ?thesis
          using Inr le
          by (cases y)
             (simp add: enter sides_unit_edge_tree_Inr,
              rule map_lift_mono[OF restrict_global_for_mono res_edge_mono[OF Fe_mono le]])
      qed
    qed
  qed
  subgoal for cc dst ex s1 s2
  proof -
    assume le: "s1 \<le> s2"
    show "sides_of_rhs (etf_combine_collect etf dst cc ex) s1 \<le> sides_of_rhs (etf_combine_collect etf dst cc ex) s2"
    proof (rule le_funI)
      fix k
      show "sides_of_rhs (etf_combine_collect etf dst cc ex) s1 k \<le> sides_of_rhs (etf_combine_collect etf dst cc ex) s2 k"
      proof (cases k)
        case (Inl x)
        show ?thesis
          by (simp add: comb Inl unit_combine_tree_def Let_def)
      next
        case (Inr y)
        show ?thesis
          using Inr le
          by (cases y)
             (simp add: comb sides_unit_combine_tree_Inr,
              rule map_lift_mono[OF restrict_global_for_mono
                res_combine_mono[OF Fc_mono le]])
      qed
    qed
  qed
  done

lemma mono_deps:
  "mono_deps (side_cfg_T_eff gs g etf bot0 s0 ())"
  apply (rule side_cfg_T_eff_mono_deps_gen)
  using static_deps_edge static_deps_enter static_deps_comb
  by simp_all

lemma threefold_mono:
  "threefold_mono (side_cfg_T_eff gs g etf bot0 s0 ())"
  unfolding threefold_mono_def
  using is_mono_eq mono_sides mono_deps
  by blast

end

end

