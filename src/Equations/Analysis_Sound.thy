theory Analysis_Sound
  imports CFG_Collect_Unified Constraint_System_Sound Constraint_System_IP_Sound
begin

(*
  U2 (unified-analysis migration): one soundness engine.

  Both the intra-procedural soundness (post_fixpoint_sound, Constraint_System_Sound)
  and the interprocedural soundness (post_fixpoint_sound_ip, Constraint_System_IP_Sound)
  share the same final step: gamma \<circ> env is a post-fixpoint of the collecting
  functional F, hence the lfp collect is below it (lfp_lowerbound).  That step is
  captured ONCE by the collecting locale (CFG_Collect_Unified) as
  collect_post_fixpoint_sound.

  unified_post_fixpoint_sound / _ip below re-derive the intra and IP soundness
  conclusions through this single engine: each only constructs the per-instance
  post-fixpoint witness (key) from the already-shared piece lemmas
  (collect_pp_abstract_sound[_ip], collect_combine_pp_abstract_sound) and calls
  the generic locale lemma.  A new combine_at hook (e.g. M4's digest-indexed join)
  obtains soundness the same way -- construct key for its F, apply
  collect_post_fixpoint_sound -- instead of forking a fifth soundness stack.
*)

(* -- Generic engine: lfp soundness from a post-fixpoint witness ------------ *)

lemma (in collecting) collect_post_fixpoint_sound:
  assumes "F g S B \<le> B"
  shows "collect g S v \<le> B v"
  using collect_lowerbound[OF assms] by (auto simp: le_fun_def)

context sound_transfer
begin

(* -- Intra-procedural soundness via the engine ---------------------------- *)

lemma unified_post_fixpoint_sound:
  fixes g :: cfg and env :: "pp \<Rightarrow> 'a abs_state" and s0 :: "'a abs_state"
  assumes fin: "finite (edges g)"
  assumes post_fp: "is_post_fixpoint g tf (\<squnion>) bot s0 env"
  assumes S_sound: "S \<le> gamma_state s0"
  shows "cfg_collect g S v \<le> gamma_state (env v)"
proof -
  have coll_le: "\<And>v. collect_pp g (\<lambda>v. gamma_state (env v)) v \<le> gamma_state (env v)"
    by (rule collect_pp_abstract_sound[OF fin post_fp])
  have s0_le_env: "s0 \<le> env (cfg_entry g)"
    using s0_le_rhs_entry[OF fin]
          post_fp[unfolded is_post_fixpoint_def, rule_format, of "cfg_entry g"]
    by (rule order_trans)
  have S_le_env: "S \<le> gamma_state (env (cfg_entry g))"
    using S_sound gamma_state_mono[OF s0_le_env] by blast
  have key: "intra.F g S (\<lambda>v. gamma_state (env v)) \<le> (\<lambda>v. gamma_state (env v))"
  proof (rule le_funI)
    fix v
    show "intra.F g S (\<lambda>v. gamma_state (env v)) v \<le> gamma_state (env v)"
      unfolding intra_F_eq cfg_collect_F_def
      using coll_le S_le_env by auto
  qed
  have "intra.collect g S v \<le> gamma_state (env v)"
    by (rule intra.collect_post_fixpoint_sound[OF key])
  thus ?thesis unfolding intra_collect_eq .
qed

(* -- Interprocedural soundness via the engine ----------------------------- *)

lemma unified_post_fixpoint_sound_ip:
  fixes g :: cfg and env :: "pp \<Rightarrow> 'a abs_state" and s0 :: "'a abs_state"
  assumes fin: "finite (edges g)"
  assumes finC: "finite (combines g)"
  assumes post_fp: "is_post_fixpoint_ip g tf (\<squnion>) bot s0 env"
  assumes S_sound: "S \<le> gamma_state s0"
  shows "cfg_collect_ip g S v \<le> gamma_state (env v)"
proof -
  have coll_le: "\<And>v. collect_pp g (\<lambda>v. gamma_state (env v)) v \<le> gamma_state (env v)"
    by (rule collect_pp_abstract_sound_ip[OF fin finC post_fp])
  have comb_le: "\<And>v. collect_combine_pp g (\<lambda>v. gamma_state (env v)) v \<le> gamma_state (env v)"
    by (rule collect_combine_pp_abstract_sound[OF fin finC post_fp])
  have s0_le_env: "s0 \<le> env (cfg_entry g)"
    using s0_le_rhs_ip_entry[OF fin finC]
          post_fp[unfolded is_post_fixpoint_ip_def, rule_format, of "cfg_entry g"]
    by (rule order_trans)
  have S_le_env: "S \<le> gamma_state (env (cfg_entry g))"
    using S_sound gamma_state_mono[OF s0_le_env] by blast
  have key: "ip.F g S (\<lambda>v. gamma_state (env v)) \<le> (\<lambda>v. gamma_state (env v))"
  proof (rule le_funI)
    fix v
    show "ip.F g S (\<lambda>v. gamma_state (env v)) v \<le> gamma_state (env v)"
      unfolding ip_F_eq cfg_collect_ip_F_def
      using coll_le comb_le S_le_env by auto
  qed
  have "ip.collect g S v \<le> gamma_state (env v)"
    by (rule ip.collect_post_fixpoint_sound[OF key])
  thus ?thesis unfolding ip_collect_eq .
qed

end

end
