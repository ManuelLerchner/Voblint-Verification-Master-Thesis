theory Constraint_System_Sound
  imports Constraint_System "Voblint_CFG.CFG_Collect"
begin

section \<open>Constraint system: soundness theorem\<close>

text \<open>
  Main result: any post-fixpoint of the equation system overapproximates the CFG
  collecting semantics.

  Proof strategy:
    1. Per-step bounds (no gamma): every edge value and every combine value at v
       is below rhs ... v, and the seed s0 is below rhs ... (cfg_entry g).
    2. Per-step soundness (sound_transfer): edge_collect / combine_states on the
       concretisation factor through apply_tf / combine_abs in the abstract domain.
    3. Glue via the witness predicate cfg_witness, then lift to the lfp
       cfg_collect by lfp_lowerbound.

  This is the ''big bridge'' in the pipeline connecting the abstract constraint
  system back to concrete program behaviour.
\<close>

subsection \<open>Per-step rhs bounds (no gamma needed)\<close>

lemma apply_tf_le_rhs:
  fixes g :: cfg and tf :: "'a::bounded_semilattice_sup_bot domain_transfer"
    and env :: "pp \<Rightarrow> 'a abs_state" and s0 :: "'a abs_state"
  assumes finE: "finite (edges g)"
  assumes finC: "finite (combines g)"
  assumes uav: "(u, a, v) \<in> edges g"
  shows "apply_tf tf a (env u) \<le> rhs g tf (\<squnion>) bot s0 env v"
proof -
  define edge_vals where
    "edge_vals = image (\<lambda>(u, a). apply_tf tf a (env u)) (predecessors g v)"
  define comb_vals where
    "comb_vals = image (\<lambda>(c, e). combine_abs (env c) (env e)) (combine_predecessors g v)"
  define base where
    "base = (if v = cfg_entry g then insert s0 (edge_vals \<union> comb_vals)
            else edge_vals \<union> comb_vals)"
  have fin_edge: "finite edge_vals"
    unfolding edge_vals_def using finE by (simp add: finite_predecessors)
  have fin_comb: "finite comb_vals"
    unfolding comb_vals_def using finC by (simp add: finite_combine_predecessors)
  have fin_base: "finite base"
    unfolding base_def using fin_edge fin_comb by simp
  have mem_base: "apply_tf tf a (env u) \<in> base"
    using uav unfolding base_def edge_vals_def predecessors_def by auto
  have "apply_tf tf a (env u) \<le> abs_join_set (\<squnion>) bot base"
    using sup_fold_ge_state[OF fin_base mem_base] unfolding abs_join_set_def by simp
  also have "\<dots> = rhs g tf (\<squnion>) bot s0 env v"
    unfolding rhs_def Let_def base_def edge_vals_def comb_vals_def
      predecessors_def combine_predecessors_def by simp
  finally show ?thesis .
qed

lemma combine_abs_le_rhs:
  fixes g :: cfg and tf :: "'a::bounded_semilattice_sup_bot domain_transfer"
    and env :: "pp \<Rightarrow> 'a abs_state" and s0 :: "'a abs_state"
  assumes finE: "finite (edges g)"
  assumes finC: "finite (combines g)"
  assumes uce: "(c, e, v) \<in> combines g"
  shows "combine_abs (env c) (env e) \<le> rhs g tf (\<squnion>) bot s0 env v"
proof -
  define edge_vals where
    "edge_vals = image (\<lambda>(u, a). apply_tf tf a (env u)) (predecessors g v)"
  define comb_vals where
    "comb_vals = image (\<lambda>(c, e). combine_abs (env c) (env e)) (combine_predecessors g v)"
  define base where
    "base = (if v = cfg_entry g then insert s0 (edge_vals \<union> comb_vals)
            else edge_vals \<union> comb_vals)"
  have fin_edge: "finite edge_vals"
    unfolding edge_vals_def using finE by (simp add: finite_predecessors)
  have fin_comb: "finite comb_vals"
    unfolding comb_vals_def using finC by (simp add: finite_combine_predecessors)
  have fin_base: "finite base"
    unfolding base_def using fin_edge fin_comb by simp
  have mem_base: "combine_abs (env c) (env e) \<in> base"
    using uce unfolding base_def comb_vals_def combine_predecessors_def by auto
  have "combine_abs (env c) (env e) \<le> abs_join_set (\<squnion>) bot base"
    using sup_fold_ge_state[OF fin_base mem_base] unfolding abs_join_set_def by simp
  also have "\<dots> = rhs g tf (\<squnion>) bot s0 env v"
    unfolding rhs_def Let_def base_def edge_vals_def comb_vals_def
      predecessors_def combine_predecessors_def by simp
  finally show ?thesis .
qed

lemma s0_le_rhs_entry:
  fixes g :: cfg and tf :: "'a::bounded_semilattice_sup_bot domain_transfer"
    and env :: "pp \<Rightarrow> 'a abs_state" and s0 :: "'a abs_state"
  assumes finE: "finite (edges g)"
  assumes finC: "finite (combines g)"
  shows "s0 \<le> rhs g tf (\<squnion>) bot s0 env (cfg_entry g)"
proof -
  define edge_vals where
    "edge_vals = image (\<lambda>(u, a). apply_tf tf a (env u)) (predecessors g (cfg_entry g))"
  define comb_vals where
    "comb_vals = image (\<lambda>(c, e). combine_abs (env c) (env e)) (combine_predecessors g (cfg_entry g))"
  define base where "base = insert s0 (edge_vals \<union> comb_vals)"
  have fin_edge: "finite edge_vals"
    unfolding edge_vals_def using finE by (simp add: finite_predecessors)
  have fin_comb: "finite comb_vals"
    unfolding comb_vals_def using finC by (simp add: finite_combine_predecessors)
  have fin_base: "finite base"
    unfolding base_def using fin_edge fin_comb by simp
  have mem_base: "s0 \<in> base" unfolding base_def by simp
  have "s0 \<le> abs_join_set (\<squnion>) bot base"
    using sup_fold_ge_state[OF fin_base mem_base] unfolding abs_join_set_def by simp
  also have "\<dots> = rhs g tf (\<squnion>) bot s0 env (cfg_entry g)"
    unfolding rhs_def Let_def base_def edge_vals_def comb_vals_def
      predecessors_def combine_predecessors_def by simp
  finally show ?thesis .
qed

subsection \<open>Per-step soundness and the main theorem\<close>

context sound_transfer
begin

(* Per-edge soundness: edge_collect on concretisation factors through
   apply_tf in the abstract domain. *)
lemma edge_collect_apply_tf_sound:
  shows "edge_collect a (gamma_state \<sigma>) \<subseteq> gamma_state (apply_tf tf a \<sigma>)"
proof (cases a)
  case EA_Nop
  then show ?thesis by simp
next
  case (EA_Assign x ax)
  show ?thesis
    unfolding EA_Assign apply_tf.simps edge_collect.simps
    using tf_sound_assign by blast
next
  case (EA_Assume b)
  show ?thesis
    unfolding EA_Assume apply_tf.simps edge_collect.simps
    using tf_sound_assume by blast
next
  case (EA_AssumeNot b)
  show ?thesis
    unfolding EA_AssumeNot apply_tf.simps edge_collect.simps
    using tf_sound_assume_not by blast
next
  case EA_Enter
  then show ?thesis
    unfolding EA_Enter apply_tf.simps edge_collect.simps
    using tf_sound_enter by auto
qed

lemma collect_pp_abstract_sound:
  assumes fin: "finite (edges g)"
  assumes finC: "finite (combines g)"
  assumes post_fp: "is_post_fixpoint g tf (\<squnion>) bot s0 env"
  shows "collect_pp g (\<lambda>v. gamma_state (env v)) v \<subseteq> gamma_state (env v)"
proof
  fix x
  assume xin: "x \<in> collect_pp g (\<lambda>v. gamma_state (env v)) v"
  then obtain u a where uav: "(u, a, v) \<in> edges g"
    and xin': "x \<in> edge_collect a (gamma_state (env u))"
    unfolding collect_pp_def by blast
  have step1: "x \<in> gamma_state (apply_tf tf a (env u))"
    using edge_collect_apply_tf_sound xin' by blast
  have le_rhs: "apply_tf tf a (env u) \<le> rhs g tf (\<squnion>) bot s0 env v"
    by (rule apply_tf_le_rhs[OF fin finC uav])
  have le_env: "rhs g tf (\<squnion>) bot s0 env v \<le> env v"
    using post_fp unfolding is_post_fixpoint_def by simp
  show "x \<in> gamma_state (env v)"
    using gamma_state_mono[OF order_trans[OF le_rhs le_env]] step1 by blast
qed

lemma collect_combine_pp_abstract_sound:
  assumes fin: "finite (edges g)"
  assumes finC: "finite (combines g)"
  assumes post_fp: "is_post_fixpoint g tf (\<squnion>) bot s0 env"
  shows "collect_combine_pp g (\<lambda>v. gamma_state (env v)) v
         \<subseteq> gamma_state (env v)"
proof
  fix x
  assume xin: "x \<in> collect_combine_pp g (\<lambda>v. gamma_state (env v)) v"
  from xin obtain c ex ret s t where
        h: "(c, ex, ret) \<in> combines g" "ret = v"
    and st: "s \<in> gamma_state (env c)" "t \<in> gamma_state (env ex)"
    and x: "x = combine_states s t"
    unfolding collect_combine_pp_def by blast
  have step: "x \<in> gamma_state (combine_abs (env c) (env ex))"
    using combine_states_sound[OF st] x by simp
  have uce: "(c, ex, v) \<in> combines g"
    using h(1,2) by force
  have le_rhs: "combine_abs (env c) (env ex) \<le> rhs g tf (\<squnion>) bot s0 env v"
    by (rule combine_abs_le_rhs[OF fin finC uce])
  have le_env: "rhs g tf (\<squnion>) bot s0 env v \<le> env v"
    using post_fp unfolding is_post_fixpoint_def by simp
  show "x \<in> gamma_state (env v)"
    using gamma_state_mono[OF order_trans[OF le_rhs le_env]] step by blast
qed

lemma cfg_witness_gamma:
  fixes g :: cfg and env :: "pp \<Rightarrow> 'a abs_state" and s0 :: "'a abs_state" and S :: "store set"
  assumes fin: "finite (edges g)"
  assumes finC: "finite (combines g)"
  assumes step_le:
    "\<And>u a w. (u, a, w) \<in> edges g \<Longrightarrow> apply_tf tf a (env u) \<le> env w"
  assumes combine_le:
    "\<And>c ex ret. (c, ex, ret) \<in> combines g \<Longrightarrow>
       combine_abs (env c) (env ex) \<le> env ret"
  assumes entry_le: "s0 \<le> env (cfg_entry g)"
  assumes S_le: "S \<le> gamma_state s0"
  assumes wit: "cfg_witness g S v st"
  shows "st \<in> gamma_state (env v)"
proof -
  from wit S_le show "st \<in> gamma_state (env v)"
  proof (induction rule: cfg_witness.induct)
    case (entry v s Sa)
    show ?case using S_le entry_le gamma_state_mono entry by blast
  next
    case (edge u a v S s t)
    have s_g: "s \<in> gamma_state (env u)" using edge by simp
    have t_ec: "t \<in> edge_collect a {s}" using edge by simp
    have step1: "t \<in> gamma_state (apply_tf tf a (env u))"
    proof -
      have sub: "{s} \<subseteq> gamma_state (env u)" using s_g by simp
      have ec: "edge_collect a (gamma_state (env u))
        \<subseteq> gamma_state (apply_tf tf a (env u))"
        using edge_collect_apply_tf_sound by blast
      have "edge_collect a {s} \<subseteq> edge_collect a (gamma_state (env u))"
        using edge_collect_mono[OF sub] by blast
      thus ?thesis using t_ec ec by blast
    qed
    show ?case using gamma_state_mono[OF step_le[OF edge(1)]] step1 by blast
  next
    case (combine c ex v S s t)
    have sc: "s \<in> gamma_state (env c)" and tc: "t \<in> gamma_state (env ex)"
      apply (auto simp add: combine.IH(1) combine.prems)
      by (simp add: combine.IH(2) combine.prems)
    have step: "combine_states s t \<in> gamma_state (combine_abs (env c) (env ex))"
      using combine_states_sound[OF sc tc] by simp
    show ?case using gamma_state_mono[OF combine_le[OF combine(1)]] step by blast
  qed
qed

lemma post_fixpoint_sound_at:
  fixes g :: cfg and env :: "pp \<Rightarrow> 'a abs_state" and s0 :: "'a abs_state"
    and S :: "store set" and v0 :: pp
  assumes fin: "finite (edges g)"
  assumes finC: "finite (combines g)"
  assumes S_sound: "S \<le> gamma_state s0"
  assumes step_le:
    "\<And>u a w. (u, a, w) \<in> edges g \<Longrightarrow> apply_tf tf a (env u) \<le> env w"
  assumes combine_le:
    "\<And>c ex ret. (c, ex, ret) \<in> combines g \<Longrightarrow>
       combine_abs (env c) (env ex) \<le> env ret"
  assumes entry_le: "s0 \<le> env (cfg_entry g)"
  shows "cfg_collect g S v0 \<le> gamma_state (env v0)"
proof -
  have paths: "cfg_collect g S v0 \<subseteq> cfg_collect_paths g S v0"
    by (rule cfg_collect_le_paths)
  show ?thesis
  proof
    fix t
    assume "t \<in> cfg_collect g S v0"
    with paths have wit: "cfg_witness g S v0 t"
      unfolding cfg_collect_paths_def by auto
    show "t \<in> gamma_state (env v0)"
      using S_sound combine_le entry_le fin finC cfg_witness_gamma step_le wit by blast
  qed
qed

theorem post_fixpoint_sound:
  assumes fin: "finite (edges g)"
  assumes finC: "finite (combines g)"
  assumes post_fp: "is_post_fixpoint g tf (\<squnion>) bot s0 env"
  assumes S_sound: "S \<le> gamma_state s0"
  shows "\<forall>v. cfg_collect g S v \<le> gamma_state (env v)"
proof -
  have coll_le: "\<And>v. collect_pp g (\<lambda>v. gamma_state (env v)) v \<le> gamma_state (env v)"
    by (rule collect_pp_abstract_sound[OF fin finC post_fp])
  have comb_le: "\<And>v. collect_combine_pp g (\<lambda>v. gamma_state (env v)) v
                  \<le> gamma_state (env v)"
    by (rule collect_combine_pp_abstract_sound[OF fin finC post_fp])
  have s0_le_env: "s0 \<le> env (cfg_entry g)"
    using s0_le_rhs_entry[OF fin finC]
          post_fp[unfolded is_post_fixpoint_def, rule_format, of "cfg_entry g"]
    by (rule order_trans)
  have S_le_env: "S \<le> gamma_state (env (cfg_entry g))"
    using S_sound gamma_state_mono[OF s0_le_env] by blast
  have key: "cfg_collect_F g S (\<lambda>v. gamma_state (env v)) \<le> (\<lambda>v. gamma_state (env v))"
  proof (rule le_funI)
    fix v
    show "cfg_collect_F g S (\<lambda>v. gamma_state (env v)) v \<le> gamma_state (env v)"
      unfolding cfg_collect_F_def
      using coll_le comb_le S_le_env by auto
  qed
  have "cfg_collect g S \<le> (\<lambda>v. gamma_state (env v))"
    unfolding cfg_collect_def
    by (simp add: key lfp_lowerbound)
  then show ?thesis by (auto simp: le_fun_def)
qed

end

end
