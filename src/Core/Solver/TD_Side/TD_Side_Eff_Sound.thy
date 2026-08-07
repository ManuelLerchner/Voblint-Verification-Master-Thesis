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


lemma etf_sound_assignD [intro]:
  assumes "inr_slot_locals_bot gs \<sigma>"
      and "s \<in> \<lbrakk>side_env \<sigma> u\<rbrakk>"
  shows
    "s(x := aval e s)
       \<in> \<lbrakk>etf_collecting_full (etf_assign etf x e u) \<sigma>\<rbrakk>"
  using assms etf_sound_assign unfolding side_env_def
  by blast

lemma etf_sound_randomD [intro]:
  assumes "inr_slot_locals_bot gs \<sigma>"
      and "s \<in> \<lbrakk>side_env \<sigma> u\<rbrakk>"
  shows
    "s(x := v)
       \<in> \<lbrakk>etf_collecting_full (etf_random etf x u) \<sigma>\<rbrakk>"
  using assms etf_sound_random unfolding side_env_def
  by blast

lemma etf_sound_assumeD [intro]:
  assumes "inr_slot_locals_bot gs \<sigma>"
      and "s \<in> \<lbrakk>side_env \<sigma> u\<rbrakk>"
      and "bval b s"
  shows
    "s \<in> \<lbrakk>etf_collecting_full (etf_assume etf b u) \<sigma>\<rbrakk>"
  using assms etf_sound_assume unfolding side_env_def
  by blast

lemma etf_sound_assume_notD [intro]:
  assumes "inr_slot_locals_bot gs \<sigma>"
      and "s \<in> \<lbrakk>side_env \<sigma> u\<rbrakk>"
      and "\<not> bval b s"
  shows
    "s \<in> \<lbrakk>etf_collecting_full (etf_assume_not etf b u) \<sigma>\<rbrakk>"
  using assms etf_sound_assume_not unfolding side_env_def
  by blast


lemma edge_collect_etf_sound:
  assumes inr: "inr_slot_locals_bot gs \<sigma>"
  shows
    "edge_collect a \<lbrakk>side_env \<sigma> u\<rbrakk>
       \<subseteq> \<lbrakk>etf_collecting_full (apply_etf etf a u) \<sigma>\<rbrakk>"
  using inr
  by (cases a;
      auto simp: etf_sound_nop side_env_apply
           split: option.splits)

end

end

