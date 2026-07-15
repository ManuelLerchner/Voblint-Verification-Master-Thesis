theory TD_Side_Eff_Sound
  imports TD_Side_Tree TD_Side_CFG Constraint_System_Sound
begin

section \<open>Effectful IP soundness: post-fixpoint over-approximates collecting\<close>

text \<open>
  The genuinely effectful counterpart of sound_transfer.post_fixpoint_sound_at:
  a post-fixpoint of the effectful equation system soundly over-approximates the
  interprocedural CFG collecting semantics.  Where the pure development uses
  apply_tf tf a, this uses etf_full (apply_etf etf a u) sigma -- the reassembled
  full result of the per-edge strategy tree -- and draws its concrete soundness
  from the sound_effectful_transfer contract instead of sound_transfer.

  The combine and entry arguments are unchanged: they rest on sound_domain facts
  (combine_states_sound, gamma_state_mono), which sound_effectful_transfer
  inherits.  Only the per-edge step differs, isolated in edge_collect_etf_sound.
\<close>

context sound_effectful_transfer
begin

subsection \<open>Per-edge concretisation soundness\<close>

text \<open>
  edge_collect on the concretisation of the combined source state factors through
  the reassembled effectful result.  The five cases are discharged by the five
  contract obligations (mirrors edge_collect_apply_tf_sound).
\<close>

lemma edge_collect_etf_sound:
  assumes inr: "inr_slot_locals_bot \<sigma>"
  shows "edge_collect a \<lbrakk>side_env \<sigma> u\<rbrakk>
   \<subseteq> \<lbrakk>etf_collecting_full (apply_etf etf a u) \<sigma>\<rbrakk>"
proof (cases a)
  case EA_Nop
  show ?thesis
    unfolding EA_Nop apply_etf.simps edge_collect.simps side_env_def
    using etf_sound_nop inr by auto
next
  case (EA_Assign x ax)
  show ?thesis
    unfolding EA_Assign apply_etf.simps edge_collect.simps side_env_def
    using etf_sound_assign inr by auto
next
  case (EA_Assume b)
  show ?thesis
    unfolding EA_Assume apply_etf.simps edge_collect.simps side_env_def
    using etf_sound_assume inr by auto
next
  case (EA_AssumeNot b)
  show ?thesis
    unfolding EA_AssumeNot apply_etf.simps edge_collect.simps side_env_def
    using etf_sound_assume_not inr by auto
next
  case EA_Enter
  show ?thesis
    unfolding EA_Enter apply_etf.simps edge_collect.simps side_env_def
    using etf_sound_enter inr by auto
qed

subsection \<open>Witness soundness and post-fixpoint soundness\<close>

text \<open>
  Effectful witness soundness (mirrors cfg_witness_gamma).  The abstract post-state
  of an edge is etf_full (apply_etf etf a u) sigma; its concrete soundness is
  edge_collect_etf_sound.  The combine and entry cases are identical to the pure
  development.
\<close>

lemma cfg_witness_gamma_eff:
  fixes g :: cfg and \<sigma> :: "pp + 'g \<Rightarrow> 'a abs_state"
    and s0 :: "'a abs_state" and S :: "store set"
  assumes inr: "inr_slot_locals_bot \<sigma>"
  assumes step_le:
    "\<And>u a w. (u, a, w) \<in> edges g
       \<Longrightarrow> etf_full (apply_etf etf a u) \<sigma> \<le> side_env \<sigma> w"
  assumes combine_le:
    "\<And>c ex ret dst. (c, ex, ret, dst) \<in> combines g \<Longrightarrow>
       etf_full (etf_combine etf dst c ex) \<sigma> \<le> side_env \<sigma> ret"
  assumes entry_le: "s0 \<le> side_env \<sigma> (cfg_entry g)"
  assumes S_le: "S \<le> \<lbrakk>s0\<rbrakk>"
  assumes wit: "cfg_witness g S v st"
  shows "st \<in> \<lbrakk>side_env \<sigma> v\<rbrakk>"
proof -
  from wit S_le show "st \<in> \<lbrakk>side_env \<sigma> v\<rbrakk>"
  proof (induction rule: cfg_witness.induct)
    case (entry v s Sa)
    show ?case using S_le entry_le gamma_state_mono entry by blast
  next
    case (edge u a v S s t)
    have s_g: "s \<in> \<lbrakk>side_env \<sigma> u\<rbrakk>" using edge by simp
    have t_ec: "t \<in> edge_collect a {s}" using edge by simp
    have step1: "t \<in> \<lbrakk>etf_collecting_full (apply_etf etf a u) \<sigma>\<rbrakk>"
    proof -
      have sub: "{s} \<subseteq> \<lbrakk>side_env \<sigma> u\<rbrakk>" using s_g by simp
      have "edge_collect a {s} \<subseteq> edge_collect a \<lbrakk>side_env \<sigma> u\<rbrakk>"
        using edge_collect_mono[OF sub] by blast
      thus ?thesis using t_ec edge_collect_etf_sound[OF inr] by blast
    qed
    have collect_le: "etf_collecting_full (apply_etf etf a u) \<sigma> \<le> side_env \<sigma> v"
      using etf_collecting_full_le_side_env[OF step_le[OF edge(1)]] .
    show ?case using gamma_state_mono[OF collect_le] step1 by blast
  next
    case (combine c ex v dst S s t u)
    have sc: "s \<in> \<lbrakk>side_env \<sigma> c\<rbrakk>" and tc: "t \<in> \<lbrakk>side_env \<sigma> ex\<rbrakk>"
      apply (auto simp add: combine.IH(1) combine.prems)
      by (simp add: combine.IH(2) combine.prems)
    have step: "combine_collect dst s t
                  \<in> \<lbrakk>etf_full (etf_combine etf dst c ex) \<sigma>\<rbrakk>"
      using etf_sound_combine inr sc tc unfolding side_env_def by auto
    have u_eq: "u = combine_collect dst s t" using combine.hyps(4) .
    show ?case
      unfolding u_eq
      using gamma_state_mono[OF combine_le[OF combine.hyps(1)]] step by blast
  qed
qed

text \<open>
  Effectful collecting soundness at a program point (mirrors
  post_fixpoint_sound_at): under the per-edge / per-combine post-fixpoint
  bounds, the combined env of an effectful post-solution over-approximates the
  IP collecting semantics.
\<close>

theorem post_fixpoint_sound_at_eff:
  fixes g :: cfg and \<sigma> :: "pp + 'g \<Rightarrow> 'a abs_state"
    and s0 :: "'a abs_state" and S :: "store set" and v0 :: pp
  assumes inr: "inr_slot_locals_bot \<sigma>"
  assumes S_sound: "S \<le> \<lbrakk>s0\<rbrakk>"
  assumes step_le:
    "\<And>u a w. (u, a, w) \<in> edges g
       \<Longrightarrow> etf_full (apply_etf etf a u) \<sigma> \<le> side_env \<sigma> w"
  assumes combine_le:
    "\<And>c ex ret dst. (c, ex, ret, dst) \<in> combines g \<Longrightarrow>
       etf_full (etf_combine etf dst c ex) \<sigma> \<le> side_env \<sigma> ret"
  assumes entry_le: "s0 \<le> side_env \<sigma> (cfg_entry g)"
  shows "cfg_collect g S v0 \<le> \<lbrakk>side_env \<sigma> v0\<rbrakk>"
proof
  fix t
  assume "t \<in> cfg_collect g S v0"
  with cfg_collect_le_paths have wit: "cfg_witness g S v0 t"
    unfolding cfg_collect_paths_def by auto
  show "t \<in> \<lbrakk>side_env \<sigma> v0\<rbrakk>"
    using cfg_witness_gamma_eff[OF inr step_le combine_le entry_le S_sound wit] .
qed

end

end

