theory TD_Side_IP_Eff_Sound
  imports TD_Side_IP_Tree Constraint_System_IP_Sound
begin

section \<open>Effectful IP soundness: post-fixpoint over-approximates collecting\<close>

text \<open>
  The genuinely effectful counterpart of sound_transfer.post_fixpoint_sound_at_ip:
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
  "edge_collect a (gamma_state (side_env \<sigma> u))
   \<subseteq> gamma_state (etf_full (apply_etf etf a u) \<sigma>)"
proof (cases a)
  case EA_Nop
  show ?thesis
    unfolding EA_Nop apply_etf.simps edge_collect.simps side_env_def
    using etf_sound_nop by blast
next
  case (EA_Assign x ax)
  show ?thesis
    unfolding EA_Assign apply_etf.simps edge_collect.simps side_env_def
    using etf_sound_assign by blast
next
  case (EA_Assume b)
  show ?thesis
    unfolding EA_Assume apply_etf.simps edge_collect.simps side_env_def
    using etf_sound_assume by blast
next
  case (EA_AssumeNot b)
  show ?thesis
    unfolding EA_AssumeNot apply_etf.simps edge_collect.simps side_env_def
    using etf_sound_assume_not by blast
next
  case EA_Enter
  show ?thesis
    unfolding EA_Enter apply_etf.simps edge_collect.simps side_env_def
    using etf_sound_enter by blast
qed

subsection \<open>Witness soundness and post-fixpoint soundness\<close>

text \<open>
  Effectful witness soundness (mirrors ip_witness_gamma).  The abstract post-state
  of an edge is etf_full (apply_etf etf a u) sigma; its concrete soundness is
  edge_collect_etf_sound.  The combine and entry cases are identical to the pure
  development.
\<close>

lemma ip_witness_gamma_eff:
  fixes g :: cfg and \<sigma> :: "pp + unit \<Rightarrow> 'a abs_state"
    and s0 :: "'a abs_state" and S :: "store set"
  assumes step_le:
    "\<And>u a w. (u, a, w) \<in> edges g
       \<Longrightarrow> etf_full (apply_etf etf a u) \<sigma> \<le> side_env \<sigma> w"
  assumes combine_le:
    "\<And>c ex ret. (c, ex, ret) \<in> combines g \<Longrightarrow>
       etf_full (etf_combine etf c ex) \<sigma> \<le> side_env \<sigma> ret"
  assumes entry_le: "s0 \<le> side_env \<sigma> (cfg_entry g)"
  assumes S_le: "S \<le> gamma_state s0"
  assumes wit: "ip_witness g S v st"
  shows "st \<in> gamma_state (side_env \<sigma> v)"
proof -
  from wit S_le show "st \<in> gamma_state (side_env \<sigma> v)"
  proof (induction rule: ip_witness.induct)
    case (entry v s Sa)
    show ?case using S_le entry_le gamma_state_mono entry by blast
  next
    case (edge u a v S s t)
    have s_g: "s \<in> gamma_state (side_env \<sigma> u)" using edge by simp
    have t_ec: "t \<in> edge_collect a {s}" using edge by simp
    have step1: "t \<in> gamma_state (etf_full (apply_etf etf a u) \<sigma>)"
    proof -
      have sub: "{s} \<subseteq> gamma_state (side_env \<sigma> u)" using s_g by simp
      have "edge_collect a {s} \<subseteq> edge_collect a (gamma_state (side_env \<sigma> u))"
        using edge_collect_mono[OF sub] by blast
      thus ?thesis using t_ec edge_collect_etf_sound by blast
    qed
    show ?case using gamma_state_mono[OF step_le[OF edge(1)]] step1 by blast
  next
    case (combine c ex v S s t)
    have sc: "s \<in> gamma_state (side_env \<sigma> c)" and tc: "t \<in> gamma_state (side_env \<sigma> ex)"
      apply (auto simp add: combine.IH(1) combine.prems)
      by (simp add: combine.IH(2) combine.prems)
    have step: "combine_states s t \<in> gamma_state (etf_full (etf_combine etf c ex) \<sigma>)"
      using etf_sound_combine sc tc unfolding side_env_def by blast
    show ?case using gamma_state_mono[OF combine_le[OF combine(1)]] step by blast
  qed
qed

text \<open>
  Effectful collecting soundness at a program point (mirrors
  post_fixpoint_sound_at_ip): under the per-edge / per-combine post-fixpoint
  bounds, the combined env of an effectful post-solution over-approximates the
  IP collecting semantics.
\<close>

theorem post_fixpoint_sound_at_ip_eff:
  fixes g :: cfg and \<sigma> :: "pp + unit \<Rightarrow> 'a abs_state"
    and s0 :: "'a abs_state" and S :: "store set" and v0 :: pp
  assumes S_sound: "S \<le> gamma_state s0"
  assumes step_le:
    "\<And>u a w. (u, a, w) \<in> edges g
       \<Longrightarrow> etf_full (apply_etf etf a u) \<sigma> \<le> side_env \<sigma> w"
  assumes combine_le:
    "\<And>c ex ret. (c, ex, ret) \<in> combines g \<Longrightarrow>
       etf_full (etf_combine etf c ex) \<sigma> \<le> side_env \<sigma> ret"
  assumes entry_le: "s0 \<le> side_env \<sigma> (cfg_entry g)"
  shows "cfg_collect_ip g S v0 \<le> gamma_state (side_env \<sigma> v0)"
proof
  fix t
  assume "t \<in> cfg_collect_ip g S v0"
  with cfg_collect_ip_le_paths have wit: "ip_witness g S v0 t"
    unfolding cfg_collect_ip_paths_def by auto
  show "t \<in> gamma_state (side_env \<sigma> v0)"
    using ip_witness_gamma_eff[OF step_le combine_le entry_le S_sound wit] .
qed

end

end
