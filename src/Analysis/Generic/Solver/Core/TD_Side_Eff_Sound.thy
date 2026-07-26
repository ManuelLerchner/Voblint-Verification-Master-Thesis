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
    unfolding EA_Nop apply_etf.simps edge_collect_simps side_env_def
    using etf_sound_nop inr by auto
next
  case (EA_Assign x ax)
  show ?thesis
    unfolding EA_Assign apply_etf.simps edge_collect_simps side_env_def
    using etf_sound_assign inr by auto
next
  case (EA_Assume b)
  show ?thesis
    unfolding EA_Assume apply_etf.simps edge_collect_simps side_env_def
    using etf_sound_assume inr by auto
next
  case (EA_AssumeNot b)
  show ?thesis
    unfolding EA_AssumeNot apply_etf.simps edge_collect_simps side_env_def
    using etf_sound_assume_not inr by auto
next
  case (EA_Ret e p)
  show ?thesis
  proof (cases e)
    case None
    show ?thesis
      unfolding EA_Ret None apply_etf.simps edge_collect_simps side_env_def
      using etf_sound_nop inr by (auto simp: fun_upd_triv)
  next
    case (Some a)
    show ?thesis
      unfolding EA_Ret Some apply_etf.simps edge_collect_simps side_env_def
      using etf_sound_assign inr by auto
  qed
qed



end

end

