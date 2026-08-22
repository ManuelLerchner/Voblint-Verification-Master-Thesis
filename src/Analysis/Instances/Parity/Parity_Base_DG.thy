theory Parity_Base_DG
  imports "Voblint_Core.DG_Base" "Voblint_Core.DG_Base_Exec" Parity_Exec
begin

section \<open>Parity on the generic Base DG construction\<close>

text \<open>
  Parity supplies only its existing transfer-soundness fact
  (\<open>parity_is_sound_transfer_for\<close>) and the domain-generic
  \<^const>\<open>is_bot_state\<close>/\<open>is_bot_state_gamma_state_empty\<close> pair; every DG
  obligation is discharged once, generically, by \<open>base_dg_spec_sound\<close>,
  mirroring Sign's own Base DG registration. No local/global packaging,
  no \<open>combine_env_abs\<close>/\<open>restrict_local_for\<close> reasoning: \<open>gs\<close> here plays only
  its role-1 VIMP call-scoping part, already baked into \<^const>\<open>parity_tf_for\<close>'s
  own \<open>tf_enter\<close>/\<open>tf_combine_env\<close> fields.
\<close>

context
  fixes gs :: "vname \<Rightarrow> bool"
begin

interpretation parity_base_dg:
  sound_dg_spec "base_dg_spec_for_lifted gs is_bot_state (parity_tf_for gs)" gamma_dg_base gs
  by (rule base_dg_spec_sound[OF parity_is_sound_transfer_for is_bot_state_gamma_state_empty])

end

section \<open>Executable parity on the generic Base DG construction\<close>

text \<open>
  Parity supplies only its existing executable/mathematical commute facts
  (\<open>parity_tf_st_for_commute\<close>, \<open>parity_enter_st_for_commute\<close>); the whole-record
  correspondence, including the combine field, is discharged once, generically,
  by \<^theory>\<open>Voblint_Core.DG_Base_Exec\<close>'s commute theorems. The passive
  \<open>is_bot_pred\<close> choice below makes the \<open>exact\<close> obligation each of those
  theorems needs trivially \<open>refl\<close>.
\<close>

context
  fixes gs :: "vname \<Rightarrow> bool"
begin

theorem parity_base_dg_spec_step_commute:
  "map_prod (map_lift (fun_of_exec_dg_st_for gs)) (map_lift (fun_of_exec_dg_st_for gs))
     (dg_spec_step (base_dg_spec_st_for_lifted gs (\<lambda>s. is_bot_state (fun_of_exec_dg_st_for gs s))
                     (parity_tf_st_for gs) (parity_enter_st_for gs)) a d g) =
   dg_spec_step (base_dg_spec_for_lifted gs is_bot_state (parity_tf_for gs)) a
     (map_lift (fun_of_exec_dg_st_for gs) d) (map_lift (fun_of_exec_dg_st_for gs) g)"
  by (rule base_dg_spec_st_for_lifted_dg_spec_step_commute
        [OF parity_tf_st_for_commute[folded fun_of_exec_dg_st_for_def]])
     simp

theorem parity_base_dg_spec_enter_commute:
  "map_prod (map_lift (fun_of_exec_dg_st_for gs)) (map_lift (fun_of_exec_dg_st_for gs))
     (dgs_enter (base_dg_spec_st_for_lifted gs (\<lambda>s. is_bot_state (fun_of_exec_dg_st_for gs s))
                  (parity_tf_st_for gs) (parity_enter_st_for gs)) xs es d g) =
   dgs_enter (base_dg_spec_for_lifted gs is_bot_state (parity_tf_for gs)) xs es
     (map_lift (fun_of_exec_dg_st_for gs) d) (map_lift (fun_of_exec_dg_st_for gs) g)"
  by (rule base_dg_spec_st_for_lifted_dgs_enter_commute
        [OF parity_enter_st_for_commute[folded fun_of_exec_dg_st_for_def]])
     simp

theorem parity_base_dg_spec_combine_commute:
  "map_prod (map_lift (fun_of_exec_dg_st_for gs)) (map_lift (fun_of_exec_dg_st_for gs))
     (dgs_combine (base_dg_spec_st_for_lifted gs (\<lambda>s. is_bot_state (fun_of_exec_dg_st_for gs s))
                    (parity_tf_st_for gs) (parity_enter_st_for gs)) dst dc de g) =
   dgs_combine (base_dg_spec_for_lifted gs is_bot_state (parity_tf_for gs)) dst
     (map_lift (fun_of_exec_dg_st_for gs) dc) (map_lift (fun_of_exec_dg_st_for gs) de)
     (map_lift (fun_of_exec_dg_st_for gs) g)"
  by (rule base_dg_spec_st_for_lifted_dgs_combine_commute) simp

end

end
