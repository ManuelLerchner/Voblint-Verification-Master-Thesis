theory Transfer_Interface_Sound
  imports Transfer_Interface "Voblint_CFG.CFG_Transfer"
begin

section \<open>Transfer interface: soundness theorem\<close>
text \<open>
  Generic transfer facts for \<^theory>\<open>Voblint_Core.Transfer_Interface\<close>'s
  \<^locale>\<open>sound_transfer_for\<close>: the D/G equation-system soundness proof cites these to
  discharge its per-step obligations from a domain's transfer soundness alone.
\<close>

subsection \<open>Per-step soundness and the main theorem\<close>

context sound_transfer_for
begin

lemma edge_collect_apply_tf_sound_for:
  "edge_collect a \<lbrakk>\<sigma>\<rbrakk> \<subseteq> \<lbrakk>apply_tf tf a \<sigma>\<rbrakk>"
proof (cases a)
  case (EA_Special sc x)
  then show ?thesis by (cases sc) auto
qed auto

text \<open>A \<open>dg_spec\<close> instance dispatches its own \<open>EA_Check\<close> case through its own
  \<open>dgs_event\<close> field, matching \<^const>\<open>apply_tf\<close>'s own \<open>event\<^sup>#\<close>
  dispatch: this is the per-domain soundness bound each such instance needs at
  that dispatch point.\<close>
lemma edge_collect_check_sound_for:
  "edge_collect (EA_Check c) \<lbrakk>\<sigma>\<rbrakk> \<subseteq> \<lbrakk>event\<^sup># tf (Check_Event c) \<sigma>\<rbrakk>"
  by auto

end


end

