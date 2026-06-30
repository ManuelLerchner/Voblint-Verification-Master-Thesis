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
  fixes etf :: "(unit, 'a::bounded_semilattice_sup_bot) effectful_domain_transfer"
  assumes comb: "\<And>cc ex. etf_combine etf cc ex = unit_combine_tree cc ex"
begin

lemma dep_aux_comb_call:
  "Inl cc \<in> dep_aux \<sigma> (etf_combine etf cc ex)"
  by (simp add: comb unit_combine_tree_def)

lemma dep_aux_comb_exit:
  "Inl ex \<in> dep_aux \<sigma> (etf_combine etf cc ex)"
  by (simp add: comb unit_combine_tree_def)

lemma comb_inr:
  "\<And>cc ex \<sigma> g. local_bot_on_locals (sides_of_rhs (etf_combine etf cc ex) \<sigma> (Inr g))"
  unfolding comb by (rule sides_inr_local_bot_unit_combine_tree)

end

locale sound_rhs_generator_static = sound_rhs_generator_base
begin

lemma static_deps_comb:
  "static_deps (etf_combine etf cc ex)"
  by (simp add: comb static_deps_def unit_combine_tree_def Let_def)

end

locale sound_rhs_generator_mono = sound_rhs_generator_static etf
  for etf :: "(unit, 'a::bounded_semilattice_sup_bot) effectful_domain_transfer" +
  fixes T :: "('x, 'g, 'a) eqsT"
  assumes is_mono_eq: "is_mono_eq T"
  assumes mono_sides: "mono_sides T"
  assumes mono_deps: "mono_deps T"
begin

lemma threefold_mono:
  "threefold_mono T"
  unfolding threefold_mono_def
  using is_mono_eq mono_sides mono_deps
  by blast

end

subsection \<open>Unit edge-tree generator\<close>

locale unit_rhs_generator = sound_rhs_generator_static +
  fixes F :: "edge_action \<Rightarrow> 'a::bounded_semilattice_sup_bot abs_state \<Rightarrow> 'a abs_state"
  assumes edge: "\<And>a u. apply_etf etf a u = unit_edge_tree (F a) u"
begin

lemma dep_aux_edge:
  "Inl u \<in> dep_aux \<sigma> (apply_etf etf a u)"
  by (simp add: edge unit_edge_tree_def)

lemma static_deps_edge:
  "static_deps (apply_etf etf a u)"
  by (simp add: edge static_deps_def unit_edge_tree_def Let_def)

lemma edge_inr:
  "\<And>a u \<sigma> g. local_bot_on_locals (sides_of_rhs (apply_etf etf a u) \<sigma> (Inr g))"
  unfolding edge by (rule sides_inr_local_bot_unit_edge_tree)

lemma cone_compatible:
  "cone_compatible_etf etf"
  unfolding cone_compatible_etf_def
  using dep_aux_edge static_deps_edge dep_aux_comb_call dep_aux_comb_exit
        static_deps_comb edge_inr comb_inr
  by blast

end

locale sound_rhs_generator_unit = unit_rhs_generator

locale unit_rhs_generator_mono = unit_rhs_generator +
  assumes F_mono: "\<And>a s1 s2. s1 \<le> s2 \<Longrightarrow> F a s1 \<le> F a s2"
begin

lemma is_mono_eq:
  "is_mono_eq (side_cfg_T_eff g etf bot0 s0 ())"
  apply (rule side_cfg_T_eff_is_mono_eq_gen)
  subgoal for a u s1 s2
    by (simp add: edge traverse_unit_edge_tree)
       (rule restrict_local_mono, rule F_mono, intro sup_mono; simp add: le_fun_def)
  subgoal for cc ex s1 s2
    by (simp add: comb traverse_unit_combine_tree)
       (rule restrict_local_mono, intro sup_mono; simp add: le_fun_def)
  done

lemma mono_sides:
  "mono_sides (side_cfg_T_eff g etf bot0 s0 ())"
  apply (rule side_cfg_T_eff_mono_sides_gen)
  subgoal for a u s1 s2
  proof -
    assume le: "s1 \<le> s2"
    show "sides_of_rhs (apply_etf etf a u) s1 \<le> sides_of_rhs (apply_etf etf a u) s2"
    proof (rule le_funI)
      fix k
      show "sides_of_rhs (apply_etf etf a u) s1 k \<le> sides_of_rhs (apply_etf etf a u) s2 k"
      proof (cases k)
        case (Inl x)
        show ?thesis
          by (simp add: edge Inl unit_edge_tree_def Let_def)
      next
        case (Inr y)
        show ?thesis
          using Inr le
          by (cases y)
             (simp add: edge sides_unit_edge_tree_Inr,
              rule restrict_global_mono, rule F_mono, intro sup_mono; simp add: le_fun_def)
      qed
    qed
  qed
  subgoal for cc ex s1 s2
  proof -
    assume le: "s1 \<le> s2"
    show "sides_of_rhs (etf_combine etf cc ex) s1 \<le> sides_of_rhs (etf_combine etf cc ex) s2"
    proof (rule le_funI)
      fix k
      show "sides_of_rhs (etf_combine etf cc ex) s1 k \<le> sides_of_rhs (etf_combine etf cc ex) s2 k"
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
              rule restrict_global_mono, intro sup_mono; simp add: le_fun_def)
      qed
    qed
  qed
  done

lemma mono_deps:
  "mono_deps (side_cfg_T_eff g etf bot0 s0 ())"
  apply (rule side_cfg_T_eff_mono_deps_gen)
  using static_deps_edge static_deps_comb
  by simp_all

lemma threefold_mono:
  "threefold_mono (side_cfg_T_eff g etf bot0 s0 ())"
  unfolding threefold_mono_def
  using is_mono_eq mono_sides mono_deps
  by blast

end

locale sound_rhs_generator_unit_mono = unit_rhs_generator_mono

subsection \<open>Mixed local/unit edge-tree generator\<close>

lemma static_deps_local_edge_tree:
  "static_deps (local_edge_tree f u)"
  unfolding static_deps_def using dep_aux_local_edge_tree by blast

lemma dep_aux_local_edge_tree_src:
  "Inl u \<in> dep_aux \<sigma> (local_edge_tree f u)"
  by (rule Inl_dep_aux_local_edge_tree)

lemma static_deps_unit_edge_tree:
  "static_deps (unit_edge_tree f u)"
  unfolding static_deps_def unit_edge_tree_def Let_def by simp

lemma dep_aux_unit_edge_tree_src:
  "Inl u \<in> dep_aux \<sigma> (unit_edge_tree f u)"
  unfolding unit_edge_tree_def by simp

locale mixed_rhs_generator = sound_rhs_generator_static +
  fixes F :: "edge_action \<Rightarrow> 'a::bounded_semilattice_sup_bot abs_state \<Rightarrow> 'a abs_state"
  assumes edge: "\<And>a u. apply_etf etf a u =
    (if local_edge_action a then local_edge_tree (F a) u
     else unit_edge_tree (F a) u)"
begin

lemma edge_inr:
  "\<And>a u \<sigma> g. local_bot_on_locals (sides_of_rhs (apply_etf etf a u) \<sigma> (Inr g))"
  by (simp add: edge sides_inr_local_bot_local_edge_tree
      sides_inr_local_bot_unit_edge_tree)

lemma static_deps_edge:
  "static_deps (apply_etf etf a u)"
  using edge static_deps_local_edge_tree static_deps_unit_edge_tree
  by (auto simp: static_deps_def unit_edge_tree_def Let_def local_edge_tree_def
       split: if_split_asm)

lemma cone_compatible:
  "cone_compatible_etf etf"
  unfolding cone_compatible_etf_def
  using edge comb dep_aux_local_edge_tree_src dep_aux_unit_edge_tree_src
        static_deps_local_edge_tree static_deps_unit_edge_tree
        dep_aux_comb_call dep_aux_comb_exit static_deps_comb
        edge_inr comb_inr
  by (auto split: if_split_asm)

end

locale sound_rhs_generator_mixed = mixed_rhs_generator

locale mixed_rhs_generator_mono = mixed_rhs_generator +
  assumes F_mono: "\<And>a s1 s2. s1 \<le> s2 \<Longrightarrow> F a s1 \<le> F a s2"
begin

lemma is_mono_eq:
  "is_mono_eq (side_cfg_T_eff g etf bot0 s0 ())"
  apply (rule side_cfg_T_eff_is_mono_eq_gen)
  subgoal for a u s1 s2
  proof -
    assume le: "s1 \<le> s2"
    show "traverse_rhs (apply_etf etf a u) s1 \<le> traverse_rhs (apply_etf etf a u) s2"
    proof (cases "local_edge_action a")
      case True
      then have eq: "apply_etf etf a u = local_edge_tree (F a) u" using edge by simp
      have lu: "s1 (Inl u) \<le> s2 (Inl u)" by (rule le_funD[OF le])
      have lg: "s1 (Inr ()) \<le> s2 (Inr ())" by (rule le_funD[OF le])
      show ?thesis unfolding eq traverse_local_edge_tree
        by (intro sup_mono restrict_local_mono restrict_global_mono F_mono;
            simp add: lu lg)
    next
      case False
      then have eq: "apply_etf etf a u = unit_edge_tree (F a) u" using edge by simp
      show ?thesis unfolding eq traverse_unit_edge_tree
        by (intro restrict_local_mono F_mono sup_mono; simp add: le le_funD)
    qed
  qed
  subgoal for cc ex s1 s2
    by (simp add: comb traverse_unit_combine_tree)
       (intro restrict_local_mono sup_mono; simp add: le_funD)
  done

lemma mono_sides:
  "mono_sides (side_cfg_T_eff g etf bot0 s0 ())"
  apply (rule side_cfg_T_eff_mono_sides_gen)
  subgoal for a u s1 s2
  proof -
    assume le: "s1 \<le> s2"
    show "sides_of_rhs (apply_etf etf a u) s1 \<le> sides_of_rhs (apply_etf etf a u) s2"
    proof (rule le_funI)
      fix k
      show "sides_of_rhs (apply_etf etf a u) s1 k \<le> sides_of_rhs (apply_etf etf a u) s2 k"
      proof (cases "local_edge_action a")
        case True
        then have eq: "apply_etf etf a u = local_edge_tree (F a) u" using edge by simp
        show ?thesis unfolding eq
          by (cases k; simp add: sides_local_edge_tree_Inl sides_local_edge_tree_Inr)
      next
        case False
        then have eq: "apply_etf etf a u = unit_edge_tree (F a) u" using edge by simp
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
                rule restrict_global_mono, rule F_mono, intro sup_mono; simp add: le_fun_def)
        qed
      qed
    qed
  qed
  subgoal for cc ex s1 s2
  proof -
    assume le: "s1 \<le> s2"
    show "sides_of_rhs (etf_combine etf cc ex) s1 \<le> sides_of_rhs (etf_combine etf cc ex) s2"
    proof (rule le_funI)
      fix k
      show "sides_of_rhs (etf_combine etf cc ex) s1 k \<le> sides_of_rhs (etf_combine etf cc ex) s2 k"
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
              rule restrict_global_mono, intro sup_mono; simp add: le_fun_def)
      qed
    qed
  qed
  done

lemma mono_deps:
  "mono_deps (side_cfg_T_eff g etf bot0 s0 ())"
  apply (rule side_cfg_T_eff_mono_deps_gen)
  using static_deps_edge static_deps_comb
  by simp_all

lemma threefold_mono:
  "threefold_mono (side_cfg_T_eff g etf bot0 s0 ())"
  unfolding threefold_mono_def
  using is_mono_eq mono_sides mono_deps
  by blast

end

locale sound_rhs_generator_mixed_mono = mixed_rhs_generator_mono

end
