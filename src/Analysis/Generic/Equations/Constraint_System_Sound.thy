theory Constraint_System_Sound
  imports Constraint_System "Voblint_CFG.CFG_Transfer"
begin

section \<open>Constraint system: soundness theorem\<close>
text \<open>
  Generic transfer facts for the constraint-system interface.
\<close>

subsection \<open>Per-step rhs bounds (no gamma needed)\<close>

text \<open>The equation right-hand side is a finite join over three sources: ordinary intra
  predecessors (\<^const>\<open>apply_tf\<close>), callee-entry contributions (\<^const>\<open>tf_enter\<close>), and return
  contributions (\<^const>\<open>combine_collect_abs\<close>).  Each is finite when the intra and call
  relations are, so every single contribution lies below the join.\<close>

definition rhs_base ::
    "cfg \<Rightarrow> 'a::bounded_semilattice_sup_bot domain_transfer \<Rightarrow> (pp \<Rightarrow> 'a abs_state)
     \<Rightarrow> pp \<Rightarrow> 'a abs_state set" where
  "rhs_base g tf env v =
     (\<lambda>(u, a). apply_tf tf a (env u)) ` intra_predecessors g v
     \<union> (\<lambda>(c, ca). case ca of CallEdge dst fs as \<Rightarrow> tf_enter tf fs as (env c)) ` entry_calls g v
     \<union> (\<lambda>(c, dst, ex). combine_collect_abs dst (env c) (env ex)) ` return_calls g v"

lemma finite_rhs_base:
  assumes "finite (intra g)" and "finite (calls g)"
  shows "finite (rhs_base g tf env v)"
  unfolding rhs_base_def
  using assms finite_intra_predecessors finite_entry_calls finite_return_calls by blast

lemma rhs_eq_join_base:
  "rhs g tf (\<squnion>) bot s0 env v =
     abs_join_set (\<squnion>) bot
       (if v = cfg_entry g then insert s0 (rhs_base g tf env v) else rhs_base g tf env v)"
  unfolding rhs_def Let_def rhs_base_def by (simp add: Un_assoc)

lemma le_rhs_of_mem:
  fixes g :: cfg and tf :: "'a::bounded_semilattice_sup_bot domain_transfer"
  assumes finI: "finite (intra g)" and finC: "finite (calls g)"
    and mem: "x \<in> rhs_base g tf env v"
  shows "x \<le> rhs g tf (\<squnion>) bot s0 env v"
proof -
  have fin: "finite (rhs_base g tf env v)" by (rule finite_rhs_base[OF finI finC])
  show ?thesis
  proof (cases "v = cfg_entry g")
    case True
    have "x \<le> abs_join_set (\<squnion>) bot (insert s0 (rhs_base g tf env v))"
      using sup_fold_ge_state[OF _ insertI2[OF mem]] fin unfolding abs_join_set_def by simp
    thus ?thesis using True by (simp add: rhs_eq_join_base)
  next
    case False
    have "x \<le> abs_join_set (\<squnion>) bot (rhs_base g tf env v)"
      using sup_fold_ge_state[OF fin mem] unfolding abs_join_set_def by simp
    thus ?thesis using False by (simp add: rhs_eq_join_base)
  qed
qed

lemma apply_tf_le_rhs:
  fixes g :: cfg and tf :: "'a::bounded_semilattice_sup_bot domain_transfer"
    and env :: "pp \<Rightarrow> 'a abs_state" and s0 :: "'a abs_state"
  assumes finI: "finite (intra g)" and finC: "finite (calls g)"
    and uav: "(u, a, v) \<in> intra g"
  shows "apply_tf tf a (env u) \<le> rhs g tf (\<squnion>) bot s0 env v"
proof (rule le_rhs_of_mem[OF finI finC])
  show "apply_tf tf a (env u) \<in> rhs_base g tf env v"
    unfolding rhs_base_def using uav by (auto simp: intra_predecessors_def)
qed

lemma tf_enter_le_rhs:
  fixes g :: cfg and tf :: "'a::bounded_semilattice_sup_bot domain_transfer"
    and env :: "pp \<Rightarrow> 'a abs_state" and s0 :: "'a abs_state"
  assumes finI: "finite (intra g)" and finC: "finite (calls g)"
    and uce: "(c, CallEdge dst fs as, v, k) \<in> calls g"
  shows "tf_enter tf fs as (env c) \<le> rhs g tf (\<squnion>) bot s0 env v"
proof (rule le_rhs_of_mem[OF finI finC])
  have "(c, CallEdge dst fs as) \<in> entry_calls g v"
    using uce by (auto simp: entry_calls_def)
  thus "tf_enter tf fs as (env c) \<in> rhs_base g tf env v"
    unfolding rhs_base_def by (force simp: image_iff)
qed

lemma combine_abs_le_rhs:
  fixes g :: cfg and tf :: "'a::bounded_semilattice_sup_bot domain_transfer"
    and env :: "pp \<Rightarrow> 'a abs_state" and s0 :: "'a abs_state"
  assumes finI: "finite (intra g)" and finC: "finite (calls g)"
    and uce: "(c, CallEdge dst fs as, FunctionEntry p, v) \<in> calls g"
  shows "combine_collect_abs dst (env c) (env (FunctionResult p))
           \<le> rhs g tf (\<squnion>) bot s0 env v"
proof (rule le_rhs_of_mem[OF finI finC])
  have "(c, dst, FunctionResult p) \<in> return_calls g v"
    using uce by (auto simp: return_calls_def)
  thus "combine_collect_abs dst (env c) (env (FunctionResult p)) \<in> rhs_base g tf env v"
    unfolding rhs_base_def by (force simp: image_iff)
qed

lemma s0_le_rhs_entry:
  fixes g :: cfg and tf :: "'a::bounded_semilattice_sup_bot domain_transfer"
    and env :: "pp \<Rightarrow> 'a abs_state" and s0 :: "'a abs_state"
  assumes finI: "finite (intra g)" and finC: "finite (calls g)"
  shows "s0 \<le> rhs g tf (\<squnion>) bot s0 env (cfg_entry g)"
proof -
  let ?base = "insert s0 (rhs_base g tf env (cfg_entry g))"
  have fin: "finite ?base" using finite_rhs_base[OF finI finC] by simp
  have "s0 \<le> abs_join_set (\<squnion>) bot ?base"
    using sup_fold_ge_state[OF fin insertI1] unfolding abs_join_set_def by simp
  thus ?thesis by (simp add: rhs_eq_join_base)
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
  case (EA_Ret e p)
  show ?thesis
  proof (cases e)
    case None
    then show ?thesis unfolding EA_Ret by (auto simp: edge_collect_def)
  next
    case (Some a)
    show ?thesis
      unfolding EA_Ret Some apply_tf.simps edge_collect_simps option.simps
      using tf_sound_assign by blast
  qed
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

text \<open>Call-entry companion of \<open>edge_of_bound\<close>: if the abstract enter transfer over \<open>A\<close> is
  dominated by \<open>B\<close>, the concrete callee-entry store built from a caller store in \<open>[[A]]\<close> lies
  in \<open>[[B]]\<close>.  The enter analogue of the intra \<open>edge_of_bound\<close>, shared by the LTR and DG
  call-routing soundness spines.\<close>
lemma call_enter_of_bound:
  assumes bound: "tf_enter tf pars args A \<le> B"
    and s: "s \<in> \<lbrakk>A\<rbrakk>"
  shows "call_enter (CallEdge dst pars args) s \<in> \<lbrakk>B\<rbrakk>"
proof -
  have "call_enter (CallEdge dst pars args) s \<in> \<lbrakk>tf_enter tf pars args A\<rbrakk>"
    using tf_sound_enter[rule_format, OF s] by (simp add: call_enter_CallEdge)
  thus ?thesis using gamma_state_mono[OF bound] by blast
qed





end

end

