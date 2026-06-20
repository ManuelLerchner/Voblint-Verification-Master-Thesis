theory Analysis_Sound
  imports "Voblint_CFG.CFG_Collect_Unified" Constraint_System_Sound
begin

section \<open>Analysis soundness: one engine\<close>

text \<open>
  The interprocedural soundness proof shares a single final step with any future
  combine_at variant: \<gamma> o env is a post-fixpoint of the collecting functional F,
  so the lfp collect sits below it (lfp_lowerbound).  That step is captured ONCE
  by the collecting locale (CFG_Collect_Unified) as collect_post_fixpoint_sound.

  unified_post_fixpoint_sound constructs the per-instance post-fixpoint witness
  (key) from the shared piece lemmas (collect_pp_abstract_sound,
  collect_combine_pp_abstract_sound) and delegates to the generic locale lemma.
  A new combine_at hook obtains soundness the same way -- construct key for its F,
  apply collect_post_fixpoint_sound -- without forking another soundness stack.
\<close>

subsection \<open>Generic engine: lfp soundness from a post-fixpoint witness\<close>

lemma (in collecting) collect_post_fixpoint_sound:
  assumes "F g S B \<le> B"
  shows "collect g S v \<le> B v"
  using collect_lowerbound[OF assms] by (auto simp: le_fun_def)

context sound_transfer
begin

subsection \<open>Interprocedural soundness via the engine\<close>

lemma unified_post_fixpoint_sound:
  fixes g :: cfg and env :: "pp \<Rightarrow> 'a abs_state" and s0 :: "'a abs_state"
  assumes fin: "finite (edges g)"
  assumes finC: "finite (combines g)"
  assumes post_fp: "is_post_fixpoint g tf (\<squnion>) bot s0 env"
  assumes S_sound: "S \<le> gamma_state s0"
  shows "cfg_collect g S v \<le> gamma_state (env v)"
proof -
  have coll_le: "\<And>v. collect_pp g (\<lambda>v. gamma_state (env v)) v \<le> gamma_state (env v)"
    by (rule collect_pp_abstract_sound[OF fin finC post_fp])
  have comb_le: "\<And>v. collect_combine_pp g (\<lambda>v. gamma_state (env v)) v \<le> gamma_state (env v)"
    by (rule collect_combine_pp_abstract_sound[OF fin finC post_fp])
  have s0_le_env: "s0 \<le> env (cfg_entry g)"
    using s0_le_rhs_entry[OF fin finC]
          post_fp[unfolded is_post_fixpoint_def, rule_format, of "cfg_entry g"]
    by (rule order_trans)
  have S_le_env: "S \<le> gamma_state (env (cfg_entry g))"
    using S_sound gamma_state_mono[OF s0_le_env] by blast
  have key: "cfg.F g S (\<lambda>v. gamma_state (env v)) \<le> (\<lambda>v. gamma_state (env v))"
  proof (rule le_funI)
    fix v
    show "cfg.F g S (\<lambda>v. gamma_state (env v)) v \<le> gamma_state (env v)"
      unfolding cfg_F_eq cfg_collect_F_def
      using coll_le comb_le S_le_env by auto
  qed
  have "cfg.collect g S v \<le> gamma_state (env v)"
    by (rule cfg.collect_post_fixpoint_sound[OF key])
  thus ?thesis unfolding cfg_collect_eq .
qed

end

end
