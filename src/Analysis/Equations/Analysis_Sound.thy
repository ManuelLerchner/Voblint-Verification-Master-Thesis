theory Analysis_Sound
  imports Constraint_System_Sound
begin

section \<open>Analysis soundness\<close>

text \<open>
  The interprocedural soundness proof builds a concrete post-fixpoint witness for
  cfg_collect_F from the shared piece lemmas (collect_pp_abstract_sound and
  collect_combine_pp_abstract_sound), then applies the lfp lower-bound rule for
  cfg_collect.
\<close>

subsection \<open>Post-fixpoint soundness for cfg_collect\<close>

lemma cfg_collect_post_fixpoint_sound:
  assumes "cfg_collect_F g S B \<le> B"
  shows "cfg_collect g S v \<le> B v"
proof -
  have "lfp (cfg_collect_F g S) \<le> B"
    using assms cfg_collect_F_mono lfp_lowerbound by blast
  then show ?thesis
    unfolding cfg_collect_def le_fun_def by simp
qed

context sound_transfer
begin

subsection \<open>Interprocedural soundness via the engine\<close>

lemma unified_post_fixpoint_sound:
  fixes g :: cfg and env :: "pp \<Rightarrow> 'a abs_state" and s0 :: "'a abs_state"
  assumes fin: "finite (edges g)"
  assumes finC: "finite (combines g)"
  assumes post_fp: "is_post_fixpoint g tf (\<squnion>) bot s0 env"
  assumes S_sound: "S \<le> \<lbrakk>s0\<rbrakk>"
  shows "cfg_collect g S v \<le> \<lbrakk>env v\<rbrakk>"
proof -
  have coll_le: "\<And>v. collect_pp g (\<lambda>v. \<lbrakk>env v\<rbrakk>) v \<le> \<lbrakk>env v\<rbrakk>"
    by (rule collect_pp_abstract_sound[OF fin finC post_fp])
  have comb_le: "\<And>v. collect_combine_pp g (\<lambda>v. \<lbrakk>env v\<rbrakk>) v \<le> \<lbrakk>env v\<rbrakk>"
    by (rule collect_combine_pp_abstract_sound[OF fin finC post_fp])
  have s0_le_env: "s0 \<le> env (cfg_entry g)"
    using s0_le_rhs_entry[OF fin finC]
          post_fp[unfolded is_post_fixpoint_def, rule_format, of "cfg_entry g"]
    by (rule order_trans)
  have S_le_env: "S \<le> \<lbrakk>env (cfg_entry g)\<rbrakk>"
    using S_sound gamma_state_mono[OF s0_le_env] by blast
  have key: "cfg_collect_F g S (\<lambda>v. \<lbrakk>env v\<rbrakk>) \<le> (\<lambda>v. \<lbrakk>env v\<rbrakk>)"
  proof (rule le_funI)
    fix v
    show "cfg_collect_F g S (\<lambda>v. \<lbrakk>env v\<rbrakk>) v \<le> \<lbrakk>env v\<rbrakk>"
      unfolding cfg_collect_F_def
      using coll_le comb_le S_le_env by auto
  qed
  show ?thesis
    by (rule cfg_collect_post_fixpoint_sound[OF key])
qed

end

end

