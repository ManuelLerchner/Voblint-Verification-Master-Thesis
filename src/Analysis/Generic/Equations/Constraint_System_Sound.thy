theory Constraint_System_Sound
  imports Constraint_System "Voblint_CFG.CFG_Transfer"
begin

section \<open>Constraint system: soundness theorem\<close>
text \<open>
  Generic transfer facts for the constraint-system interface.
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
    "comb_vals = image (\<lambda>(c, ex, dst). combine_collect_abs dst (env c) (env ex))
                       (combine_predecessors g v)"
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
      predecessors_def combine_predecessors_eq by simp
  finally show ?thesis .
qed

lemma combine_collect_abs_le_rhs:
  fixes g :: cfg and tf :: "'a::bounded_semilattice_sup_bot domain_transfer"
    and env :: "pp \<Rightarrow> 'a abs_state" and s0 :: "'a abs_state"
  assumes finE: "finite (edges g)"
  assumes finC: "finite (combines g)"
  assumes uce: "(c, ex, v, dst) \<in> combines g"
  shows "combine_collect_abs dst (env c) (env ex)
           \<le> rhs g tf (\<squnion>) bot s0 env v"
proof -
  define edge_vals where
    "edge_vals = image (\<lambda>(u, a). apply_tf tf a (env u)) (predecessors g v)"
  define comb_vals where
    "comb_vals = image (\<lambda>(c, ex, dst). combine_collect_abs dst (env c) (env ex))
                       (combine_predecessors g v)"
  define base where
    "base = (if v = cfg_entry g then insert s0 (edge_vals \<union> comb_vals)
            else edge_vals \<union> comb_vals)"
  have fin_edge: "finite edge_vals"
    unfolding edge_vals_def using finE by (simp add: finite_predecessors)
  have fin_comb: "finite comb_vals"
    unfolding comb_vals_def using finC by (simp add: finite_combine_predecessors)
  have fin_base: "finite base"
    unfolding base_def using fin_edge fin_comb by simp
  have mem_comb: "combine_collect_abs dst (env c) (env ex) \<in> comb_vals"
    unfolding comb_vals_def combine_predecessors_eq
    using uce by (intro image_eqI[where x = "(c, ex, dst)"]) auto
  have mem_base: "combine_collect_abs dst (env c) (env ex) \<in> base"
    using mem_comb unfolding base_def by auto
  have "combine_collect_abs dst (env c) (env ex)
          \<le> abs_join_set (\<squnion>) bot base"
    using sup_fold_ge_state[OF fin_base mem_base] unfolding abs_join_set_def by simp
  also have "\<dots> = rhs g tf (\<squnion>) bot s0 env v"
    unfolding rhs_def Let_def base_def edge_vals_def comb_vals_def
      predecessors_def combine_predecessors_eq by simp
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
    "comb_vals = image (\<lambda>(c, ex, dst). combine_collect_abs dst (env c) (env ex))
                       (combine_predecessors g (cfg_entry g))"
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
      predecessors_def combine_predecessors_eq by simp
  finally show ?thesis .
qed

subsection \<open>Per-step soundness and the main theorem\<close>

subsection \<open>Per-step soundness and the main theorem\<close>

context sound_transfer
begin

(* Per-edge soundness: edge_collect on concretisation factors through
   apply_tf in the abstract domain. *)
lemma edge_collect_apply_tf_sound:
  shows "edge_collect a \<lbrakk>\<sigma>\<rbrakk> \<subseteq> \<lbrakk>apply_tf tf a \<sigma>\<rbrakk>"
proof (cases a)
  case EA_Nop
  then show ?thesis by simp
next
  case (EA_Assign x ax)
  show ?thesis
    unfolding EA_Assign apply_tf.simps edge_collect_simps
    using tf_sound_assign by blast
next
  case (EA_Assume b)
  show ?thesis
    unfolding EA_Assume apply_tf.simps edge_collect_simps
    using tf_sound_assume by blast
next
  case (EA_AssumeNot b)
  show ?thesis
    unfolding EA_AssumeNot apply_tf.simps edge_collect_simps
    using tf_sound_assume_not by blast
next
  case (EA_Enter xs es)
  show ?thesis
    unfolding EA_Enter apply_tf.simps edge_collect_simps
    using tf_sound_enter by blast
qed

text \<open>Single-store edge soundness under a post-fixpoint bound: if the abstract transfer
  over \<open>A\<close> is dominated by \<open>B\<close>, a concrete step from a store in \<open>[[A]]\<close> lands in \<open>[[B]]\<close>.
  A domain-level consequence of \<open>edge_collect_apply_tf_sound\<close> and monotonicity, shared
  by the R_read / DG local-slot spines.\<close>
lemma edge_of_bound:
  assumes bound: "apply_tf tf a A \<le> B"
    and s: "s \<in> \<lbrakk>A\<rbrakk>"
    and step: "edge_step a s = Some s'"
  shows "s' \<in> \<lbrakk>B\<rbrakk>"
proof -
  have m: "s' \<in> edge_collect a {s}" using step by (simp add: edge_collect_single)
  have "edge_collect a {s} \<subseteq> edge_collect a \<lbrakk>A\<rbrakk>" using s edge_collect_mono by blast
  also have "... \<subseteq> \<lbrakk>apply_tf tf a A\<rbrakk>" by (rule edge_collect_apply_tf_sound)
  also have "... \<subseteq> \<lbrakk>B\<rbrakk>" using gamma_state_mono[OF bound] by blast
  finally show ?thesis using m by blast
qed





end

end

