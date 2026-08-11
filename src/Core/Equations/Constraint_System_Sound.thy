theory Constraint_System_Sound
  imports Constraint_System "Voblint_CFG.CFG_Transfer"
begin

section \<open>Constraint system: soundness theorem\<close>
text \<open>
  Generic transfer facts for the constraint-system interface.
\<close>

subsection \<open>Per-step rhs bounds (no gamma needed)\<close>

text \<open>The equation right-hand side is a finite join over ordinary edges,
  procedure entries, and return combinations.  One shared family definition
  determines both the executable equation and these soundness bounds.\<close>

lemma finite_rhs_edge_sources:
  assumes "finite (intra g)"
  shows "finite (rhs_edge_sources g tf env v)"
  unfolding rhs_edge_sources_def
  using assms finite_intra_predecessors by blast

lemma finite_rhs_entry_sources:
  assumes "finite (calls g)"
  shows "finite (rhs_entry_sources g tf env v)"
  unfolding rhs_entry_sources_def
  using assms finite_entry_calls by blast

lemma finite_rhs_combine_sources:
  assumes "finite (calls g)"
  shows "finite (rhs_combine_sources g tf env v)"
  unfolding rhs_combine_sources_def
  using assms finite_return_calls by blast

lemma finite_rhs_sources:
  assumes "finite (intra g)" and "finite (calls g)"
  shows "finite (rhs_sources g tf env v)"
  unfolding rhs_sources_def
  using finite_rhs_edge_sources finite_rhs_entry_sources finite_rhs_combine_sources assms
  by blast

lemma rhs_eq_join_sources:
  "rhs g tf (\<squnion>) bot s0 env v =
     abs_join_set (\<squnion>) bot
       (if v = cfg_entry g then insert s0 (rhs_sources g tf env v)
        else rhs_sources g tf env v)"
  unfolding rhs_def by simp

lemma le_rhs_of_mem:
  fixes g :: cfg and tf :: "'a::bounded_semilattice_sup_bot domain_transfer"
  assumes finI: "finite (intra g)" and finC: "finite (calls g)"
    and mem: "x \<in> rhs_sources g tf env v"
  shows "x \<le> rhs g tf (\<squnion>) bot s0 env v"
proof -
  have fin: "finite (rhs_sources g tf env v)"
    by (rule finite_rhs_sources[OF finI finC])
  show ?thesis
  proof (cases "v = cfg_entry g")
    case True
    have "x \<le> abs_join_set (\<squnion>) bot (insert s0 (rhs_sources g tf env v))"
      using sup_fold_ge_state[OF _ insertI2[OF mem]] fin unfolding abs_join_set_def by simp
    thus ?thesis using True by (simp add: rhs_eq_join_sources)
  next
    case False
    have "x \<le> abs_join_set (\<squnion>) bot (rhs_sources g tf env v)"
      using sup_fold_ge_state[OF fin mem] unfolding abs_join_set_def by simp
    thus ?thesis using False by (simp add: rhs_eq_join_sources)
  qed
qed

lemma apply_tf_le_rhs:
  fixes g :: cfg and tf :: "'a::bounded_semilattice_sup_bot domain_transfer"
    and env :: "pp \<Rightarrow> 'a abs_state" and s0 :: "'a abs_state"
  assumes finI: "finite (intra g)" and finC: "finite (calls g)"
    and uav: "(u, a, v) \<in> intra g"
  shows "apply_tf tf a (env u) \<le> rhs g tf (\<squnion>) bot s0 env v"
proof (rule le_rhs_of_mem[OF finI finC])
  show "apply_tf tf a (env u) \<in> rhs_sources g tf env v"
    unfolding rhs_sources_def
    using uav rhs_edge_sources_iff by blast
qed

lemma tf_enter_le_rhs:
  fixes g :: cfg and tf :: "'a::bounded_semilattice_sup_bot domain_transfer"
    and env :: "pp \<Rightarrow> 'a abs_state" and s0 :: "'a abs_state"
  assumes finI: "finite (intra g)" and finC: "finite (calls g)"
    and uce: "(c, CallEdge dst fs as, v, k) \<in> calls g"
  shows "enter\<^sup># tf fs as (env c) \<le> rhs g tf (\<squnion>) bot s0 env v"
proof (rule le_rhs_of_mem[OF finI finC])
  have "enter\<^sup># tf fs as (env c) \<in> rhs_entry_sources g tf env v"
    by (rule rhs_entry_sourcesI[OF uce])
  thus "enter\<^sup># tf fs as (env c) \<in> rhs_sources g tf env v"
    unfolding rhs_sources_def by blast
qed

lemma tf_combine_le_rhs:
  fixes g :: cfg and tf :: "'a::bounded_semilattice_sup_bot domain_transfer"
    and env :: "pp \<Rightarrow> 'a abs_state" and s0 :: "'a abs_state"
  assumes finI: "finite (intra g)" and finC: "finite (calls g)"
    and uce: "(c, CallEdge dst fs as, FunctionEntry p, v) \<in> calls g"
  shows "tf_combine_collect_abs tf dst (env c) (env (FunctionResult p))
           \<le> rhs g tf (\<squnion>) bot s0 env v"
proof (rule le_rhs_of_mem[OF finI finC])
  have "tf_combine_collect_abs tf dst (env c) (env (FunctionResult p))
        \<in> rhs_combine_sources g tf env v"
    by (rule rhs_combine_sourcesI[OF uce])
  thus "tf_combine_collect_abs tf dst (env c) (env (FunctionResult p))
        \<in> rhs_sources g tf env v"
    unfolding rhs_sources_def by blast
qed

lemma s0_le_rhs_entry:
  fixes g :: cfg and tf :: "'a::bounded_semilattice_sup_bot domain_transfer"
    and env :: "pp \<Rightarrow> 'a abs_state" and s0 :: "'a abs_state"
  assumes finI: "finite (intra g)" and finC: "finite (calls g)"
  shows "s0 \<le> rhs g tf (\<squnion>) bot s0 env (cfg_entry g)"
proof -
  let ?base = "insert s0 (rhs_sources g tf env (cfg_entry g))"
  have fin: "finite ?base" using finite_rhs_sources[OF finI finC] by simp
  have "s0 \<le> abs_join_set (\<squnion>) bot ?base"
    using sup_fold_ge_state[OF fin insertI1] unfolding abs_join_set_def by simp
  thus ?thesis by (simp add: rhs_eq_join_sources)
qed

subsection \<open>Per-step soundness and the main theorem\<close>

context sound_transfer_for
begin

lemma edge_collect_apply_tf_sound_for:
  "edge_collect a \<lbrakk>\<sigma>\<rbrakk> \<subseteq> \<lbrakk>apply_tf tf a \<sigma>\<rbrakk>"
  apply(cases a) by (auto split:option.splits)

text \<open>Single-store edge soundness under a post-fixpoint bound: if the abstract transfer
  over \<open>A\<close> is dominated by \<open>B\<close>, a concrete step from a store in \<open>[[A]]\<close> lands in \<open>[[B]]\<close>.
  A domain-level consequence of \<open>edge_collect_apply_tf_sound_for\<close> and monotonicity, shared
  by the R_read / DG local-slot spines. Generic in the classifier: neither premise nor
  conclusion mentions \<open>gs\<close>.\<close>
lemma edge_of_bound:
  assumes bound: "apply_tf tf a A \<le> B"
    and s: "s \<in> \<lbrakk>A\<rbrakk>"
    and step: "s' \<in> edge_step a s"
  shows "s' \<in> \<lbrakk>B\<rbrakk>"
proof -
  have m: "s' \<in> edge_collect a {s}" using step by (simp add: edge_collect_single)
  have "edge_collect a {s} \<subseteq> edge_collect a \<lbrakk>A\<rbrakk>" using s edge_collect_mono by blast
  also have "... \<subseteq> \<lbrakk>apply_tf tf a A\<rbrakk>" by (rule edge_collect_apply_tf_sound_for)
  also have "... \<subseteq> \<lbrakk>B\<rbrakk>" using gamma_state_mono[OF bound] by blast
  finally show ?thesis using m by blast
qed

text \<open>Call-entry companion of \<open>edge_of_bound\<close>, generic in the classifier: if the
  abstract enter transfer over \<open>A\<close> is dominated by \<open>B\<close>, the concrete callee-entry
  store built from a caller store in \<open>[[A]]\<close> lies in \<open>[[B]]\<close>.\<close>
lemma call_enter_of_bound_for:
  assumes bound: "enter\<^sup># tf pars args A \<le> B"
    and s: "s \<in> \<lbrakk>A\<rbrakk>"
  shows "call_enter gs (CallEdge dst pars args) s \<in> \<lbrakk>B\<rbrakk>"
proof -
  have "call_enter gs (CallEdge dst pars args) s \<in> \<lbrakk>enter\<^sup># tf pars args A\<rbrakk>"
    using tf_sound_enter_forD[OF s] by (simp add: call_enter_CallEdge)
  thus ?thesis using gamma_state_mono[OF bound] by blast
qed

text \<open>Return-combine companion of \<open>edge_of_bound\<close>/\<open>call_enter_of_bound_for\<close>, generic
  in the classifier: if the per-analysis return combine over \<open>A\<close>, \<open>B\<close> is dominated by
  \<open>C\<close>, the concrete return combine of stores sound for \<open>A\<close>, \<open>B\<close> lies in \<open>[[C]]\<close>.\<close>
lemma combine_of_bound_for:
  assumes bound: "tf_combine_collect_abs tf dst A B \<le> C"
    and s: "s \<in> \<lbrakk>A\<rbrakk>" and t: "t \<in> \<lbrakk>B\<rbrakk>"
  shows "combine_collect gs dst s t \<in> \<lbrakk>C\<rbrakk>"
proof -
  have step: "combine_collect gs dst s t \<in> \<lbrakk>tf_combine_collect_abs tf dst A B\<rbrakk>"
  proof (cases dst)
    case None
    then show ?thesis
      using tf_sound_combine_forD[OF s t]
      by (simp add: combine_collect_def tf_combine_collect_abs_def)
  next
    case (Some x)
    have base: "combine_env gs s t \<in> \<lbrakk>tf_combine tf A B\<rbrakk>"
      using tf_sound_combine_forD[OF s t] .
    have ret: "t ret_var \<in> gamma (B ret_var)"
      using t unfolding gamma_state_def by auto
    show ?thesis
      using base ret Some
      unfolding gamma_state_def combine_collect_def tf_combine_collect_abs_def
      by auto
  qed
  thus ?thesis using gamma_state_mono[OF bound] by blast
qed

end


end

