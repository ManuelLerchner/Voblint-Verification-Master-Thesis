theory TD_Side_Eff_Pipeline
  imports TD_Side_Eff_Bounds TD_Side_Eff_Sound TD_Side_Eff_Interface
begin

section \<open>Standalone effectful pipeline\<close>

text \<open>The pipeline derives the solver interface from monotonicity and static
  dependencies of each strategy tree. A partial post-solution bounds every contribution,
  and a sound effectful transfer turns those bounds into collecting-semantics soundness.
  Effectful analyses discharge the tree contracts compositionally.\<close>

subsection \<open>Threefold monotonicity\<close>

text \<open>\<open>threefold_mono\<close> bundles the conditions required by the optimized
  solver: equation values and side effects are monotone in the environment, while
  dependency sets can only shrink as the environment grows. Together they guarantee a
  least partial post-solution.\<close>

definition threefold_mono ::
  "('x, 'g, 'd::bounded_semilattice_sup_bot) eqsT \<Rightarrow> bool"
where
  "threefold_mono T \<equiv> is_mono_eq T \<and> mono_sides T \<and> mono_deps T"

lemma threefold_monoD_eq:   "threefold_mono T \<Longrightarrow> is_mono_eq T"
  unfolding threefold_mono_def by blast

lemma threefold_monoD_sides: "threefold_mono T \<Longrightarrow> mono_sides T"
  unfolding threefold_mono_def by blast

lemma threefold_monoD_deps:  "threefold_mono T \<Longrightarrow> mono_deps T"
  unfolding threefold_mono_def by blast

subsection \<open>Solver interface from the per-tree contract\<close>

lemma td_cfg_side_solver_eff_gen:
  fixes g :: cfg
    and etf :: "('g::finite, 'a::bounded_semilattice_sup_bot) effectful_domain_transfer"
    and bot0 s0 :: "'a abs_state" and gseed :: 'g
  assumes edge_mono:
    "\<And>a u s1 s2. s1 \<le> s2 \<Longrightarrow>
       traverse_rhs (apply_etf etf a u) s1 \<le> traverse_rhs (apply_etf etf a u) s2"
  assumes enter_mono:
    "\<And>cl fs as s1 s2. s1 \<le> s2 \<Longrightarrow>
       traverse_rhs (etf_enter etf fs as cl) s1 \<le> traverse_rhs (etf_enter etf fs as cl) s2"
  assumes comb_mono:
    "\<And>cc ex dst s1 s2. s1 \<le> s2 \<Longrightarrow>
       traverse_rhs (etf_combine etf dst cc ex) s1 \<le> traverse_rhs (etf_combine etf dst cc ex) s2"
  assumes edge_sides_mono:
    "\<And>a u s1 s2. s1 \<le> s2 \<Longrightarrow>
       sides_of_rhs (apply_etf etf a u) s1 \<le> sides_of_rhs (apply_etf etf a u) s2"
  assumes enter_sides_mono:
    "\<And>cl fs as s1 s2. s1 \<le> s2 \<Longrightarrow>
       sides_of_rhs (etf_enter etf fs as cl) s1 \<le> sides_of_rhs (etf_enter etf fs as cl) s2"
  assumes comb_sides_mono:
    "\<And>cc ex dst s1 s2. s1 \<le> s2 \<Longrightarrow>
       sides_of_rhs (etf_combine etf dst cc ex) s1 \<le> sides_of_rhs (etf_combine etf dst cc ex) s2"
  assumes edge_static: "\<And>a u. static_deps (apply_etf etf a u)"
  assumes enter_static: "\<And>cl fs as. static_deps (etf_enter etf fs as cl)"
  assumes comb_static: "\<And>cc ex dst. static_deps (etf_combine etf dst cc ex)"
  shows "td_cfg_side_solver_eff gs g etf bot0 s0 gseed"
proof unfold_locales
  show "is_mono_eq (side_cfg_T_eff gs g etf bot0 s0 gseed)"
    by (rule side_cfg_T_eff_is_mono_eq_gen[OF edge_mono enter_mono comb_mono])
  show "mono_sides (side_cfg_T_eff gs g etf bot0 s0 gseed)"
    by (rule side_cfg_T_eff_mono_sides_gen[OF edge_sides_mono enter_sides_mono comb_sides_mono])
  show "mono_deps (side_cfg_T_eff gs g etf bot0 s0 gseed)"
    by (rule side_cfg_T_eff_mono_deps_gen[OF edge_static enter_static comb_static])
qed

subsection \<open>Collecting soundness from a post-solution\<close>

text \<open>Cone-compatibility conditions for cone-restricted effectful soundness.\<close>
subsection \<open>Cone-compatibility\<close>

text \<open>
  cone_compatible_etf bundles the five structural conditions that guarantee the
  solver's stable set reaches the program entry (the cone argument in
  side_cone_in_vars_eff).

  The first three are self-reference conditions: each edge/combine tree queries
  its own source program points.  The last two say the queried unknowns are
  independent of the environment (static_deps), so the cone is determined
  structurally rather than by the abstract state.
\<close>

definition cone_compatible_etf ::
  "(vname \<Rightarrow> bool) \<Rightarrow> ('g::finite, 'a::bounded_semilattice_sup_bot) effectful_domain_transfer \<Rightarrow> bool"
where
  "cone_compatible_etf gs etf \<equiv>
     (\<forall>b z \<sigma>'. Inl z \<in> dep_aux \<sigma>' (apply_etf etf b z)) \<and>
     (\<forall>c2 e2 d2 \<sigma>'. Inl c2 \<in> dep_aux \<sigma>' (etf_combine etf d2 c2 e2)) \<and>
     (\<forall>c2 e2 d2 \<sigma>'. Inl e2 \<in> dep_aux \<sigma>' (etf_combine etf d2 c2 e2)) \<and>
     (\<forall>cl fs as \<sigma>'. Inl cl \<in> dep_aux \<sigma>' (etf_enter etf fs as cl)) \<and>
     (\<forall>a u. static_deps (apply_etf etf a u)) \<and>
     (\<forall>cc ex dst. static_deps (etf_combine etf dst cc ex)) \<and>
     (\<forall>cl fs as. static_deps (etf_enter etf fs as cl)) \<and>
     (\<forall>a u \<sigma>' g. local_bot_on_locals gs (sides_of_rhs (apply_etf etf a u) \<sigma>' (Inr g))) \<and>
     (\<forall>cc ex dst \<sigma>' g. local_bot_on_locals gs (sides_of_rhs (etf_combine etf dst cc ex) \<sigma>' (Inr g))) \<and>
     (\<forall>cl fs as \<sigma>' g. local_bot_on_locals gs (sides_of_rhs (etf_enter etf fs as cl) \<sigma>' (Inr g)))"



lemma cone_compatible_etf_edge_dep:
  "cone_compatible_etf gs etf \<Longrightarrow> Inl z \<in> dep_aux \<sigma>' (apply_etf etf b z)"
  unfolding cone_compatible_etf_def by auto


lemma cone_compatible_etf_comb_dep1:
  "cone_compatible_etf gs etf \<Longrightarrow> Inl c2 \<in> dep_aux \<sigma>' (etf_combine etf d2 c2 e2)"
  unfolding cone_compatible_etf_def by auto


lemma cone_compatible_etf_comb_dep2:
  "cone_compatible_etf gs etf \<Longrightarrow> Inl e2 \<in> dep_aux \<sigma>' (etf_combine etf d2 c2 e2)"
  unfolding cone_compatible_etf_def by auto

lemma cone_compatible_etf_edge_static:
  "cone_compatible_etf gs etf \<Longrightarrow> static_deps (apply_etf etf a u)"
  unfolding cone_compatible_etf_def by auto

lemma cone_compatible_etf_comb_static:
  "cone_compatible_etf gs etf \<Longrightarrow> static_deps (etf_combine etf dst cc ex)"
  unfolding cone_compatible_etf_def by auto

lemma cone_compatible_etf_edge_inr:
  "cone_compatible_etf gs etf \<Longrightarrow>
     local_bot_on_locals gs (sides_of_rhs (apply_etf etf a u) \<sigma>' (Inr g))"
  unfolding cone_compatible_etf_def by auto

lemma cone_compatible_etf_comb_inr:
  "cone_compatible_etf gs etf \<Longrightarrow>
     local_bot_on_locals gs (sides_of_rhs (etf_combine etf dst cc ex) \<sigma>' (Inr g))"
  unfolding cone_compatible_etf_def by auto

lemma cone_compatible_etf_enter_dep:
  "cone_compatible_etf gs etf \<Longrightarrow> Inl cl \<in> dep_aux \<sigma>' (etf_enter etf fs as cl)"
  unfolding cone_compatible_etf_def by auto

lemma cone_compatible_etf_enter_static:
  "cone_compatible_etf gs etf \<Longrightarrow> static_deps (etf_enter etf fs as cl)"
  unfolding cone_compatible_etf_def by auto

lemma cone_compatible_etf_enter_inr:
  "cone_compatible_etf gs etf \<Longrightarrow>
     local_bot_on_locals gs (sides_of_rhs (etf_enter etf fs as cl) \<sigma>' (Inr g))"
  unfolding cone_compatible_etf_def by auto


end
