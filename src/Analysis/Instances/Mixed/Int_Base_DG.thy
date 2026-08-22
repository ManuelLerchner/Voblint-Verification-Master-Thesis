theory Int_Base_DG
  imports "Voblint_Core.DG_Base" "Voblint_Core.DG_Base_Exec" Int_Exec
begin

section \<open>Composite integer domain on the generic Base DG construction\<close>

text \<open>
  Registers each of the three mode-specific transfer bundles
  (\<open>int_tf_never_for\<close>, \<open>int_tf_once_for\<close>, \<open>int_tf_fixpoint_for\<close>) against the
  generic Base construction \<^const>\<open>base_dg_spec_for_lifted\<close>, mirroring
  Sign's own Base DG registration. int_dom supplies only its existing
  transfer-soundness facts (\<open>int_never_is_sound_transfer_for\<close> etc, already
  proved in \<^theory>\<open>Voblint_Analysis.Int_Transfer\<close>) and the domain-generic
  \<^const>\<open>is_bot_state\<close>/\<open>is_bot_state_gamma_state_empty\<close> pair; every DG
  obligation is discharged once, generically, by \<open>base_dg_spec_sound\<close>. As in
  \<^theory>\<open>Voblint_Analysis.Int_DG\<close>, the three refinement modes stay separate at
  this layer rather than hiding the asymmetry behind one mode-parameterised
  registration. No local/global packaging, no \<open>combine_env_abs\<close>/
  \<open>restrict_local_for\<close> reasoning: \<open>gs\<close> here plays only its role-1 VIMP
  call-scoping part, already baked into each mode's own \<open>tf_enter\<close>/
  \<open>tf_combine_env\<close> fields.
\<close>

context
  fixes gs :: "vname \<Rightarrow> bool"
begin

interpretation int_never_base_dg:
  sound_dg_spec "base_dg_spec_for_lifted gs is_bot_state (int_tf_never_for gs)" gamma_dg_base gs
  by (rule base_dg_spec_sound[OF int_never_is_sound_transfer_for is_bot_state_gamma_state_empty])

interpretation int_once_base_dg:
  sound_dg_spec "base_dg_spec_for_lifted gs is_bot_state (int_tf_once_for gs)" gamma_dg_base gs
  by (rule base_dg_spec_sound[OF int_once_is_sound_transfer_for is_bot_state_gamma_state_empty])

interpretation int_fixpoint_base_dg:
  sound_dg_spec "base_dg_spec_for_lifted gs is_bot_state (int_tf_fixpoint_for gs)" gamma_dg_base gs
  by (rule base_dg_spec_sound[OF int_fixpoint_is_sound_transfer_for is_bot_state_gamma_state_empty])

end

section \<open>Executable composite integer domain on the generic Base DG construction\<close>

text \<open>
  int_dom supplies only its existing executable/mathematical commute facts
  per mode (\<open>int_tf_st_never_for_commute\<close>/\<open>int_dom_enter_never_st_for_commute\<close>
  and their \<open>once\<close>/\<open>fixpoint\<close> counterparts, all from
  \<^theory>\<open>Voblint_Analysis.Int_Exec\<close>); the whole-record correspondence,
  including the combine field, is discharged once, generically, by
  \<^theory>\<open>Voblint_Core.DG_Base_Exec\<close>'s commute theorems. The passive
  \<open>is_bot_pred\<close> choice below makes the \<open>exact\<close> obligation each of those
  theorems needs trivially \<open>refl\<close>.
\<close>

context
  fixes gs :: "vname \<Rightarrow> bool"
begin

subsection \<open>Refine_Never\<close>

theorem int_never_base_dg_spec_step_commute:
  "map_prod (map_lift (fun_of_exec_dg_st_for gs)) (map_lift (fun_of_exec_dg_st_for gs))
     (dg_spec_step (base_dg_spec_st_for_lifted gs (\<lambda>s. is_bot_state (fun_of_exec_dg_st_for gs s))
                     (int_tf_st_never_for gs) (int_dom_enter_never_st_for gs)) a d g) =
   dg_spec_step (base_dg_spec_for_lifted gs is_bot_state (int_tf_never_for gs)) a
     (map_lift (fun_of_exec_dg_st_for gs) d) (map_lift (fun_of_exec_dg_st_for gs) g)"
  by (rule base_dg_spec_st_for_lifted_dg_spec_step_commute
        [OF int_tf_st_never_for_commute[folded fun_of_exec_dg_st_for_def]])
     simp

theorem int_never_base_dg_spec_enter_commute:
  "map_prod (map_lift (fun_of_exec_dg_st_for gs)) (map_lift (fun_of_exec_dg_st_for gs))
     (dgs_enter (base_dg_spec_st_for_lifted gs (\<lambda>s. is_bot_state (fun_of_exec_dg_st_for gs s))
                  (int_tf_st_never_for gs) (int_dom_enter_never_st_for gs)) xs es d g) =
   dgs_enter (base_dg_spec_for_lifted gs is_bot_state (int_tf_never_for gs)) xs es
     (map_lift (fun_of_exec_dg_st_for gs) d) (map_lift (fun_of_exec_dg_st_for gs) g)"
  by (rule base_dg_spec_st_for_lifted_dgs_enter_commute
        [OF int_dom_enter_never_st_for_commute[folded fun_of_exec_dg_st_for_def]])
     simp

theorem int_never_base_dg_spec_combine_commute:
  "map_prod (map_lift (fun_of_exec_dg_st_for gs)) (map_lift (fun_of_exec_dg_st_for gs))
     (dgs_combine (base_dg_spec_st_for_lifted gs (\<lambda>s. is_bot_state (fun_of_exec_dg_st_for gs s))
                    (int_tf_st_never_for gs) (int_dom_enter_never_st_for gs)) dst dc de g) =
   dgs_combine (base_dg_spec_for_lifted gs is_bot_state (int_tf_never_for gs)) dst
     (map_lift (fun_of_exec_dg_st_for gs) dc) (map_lift (fun_of_exec_dg_st_for gs) de)
     (map_lift (fun_of_exec_dg_st_for gs) g)"
  by (rule base_dg_spec_st_for_lifted_dgs_combine_commute) simp

subsection \<open>Refine_Once\<close>

theorem int_once_base_dg_spec_step_commute:
  "map_prod (map_lift (fun_of_exec_dg_st_for gs)) (map_lift (fun_of_exec_dg_st_for gs))
     (dg_spec_step (base_dg_spec_st_for_lifted gs (\<lambda>s. is_bot_state (fun_of_exec_dg_st_for gs s))
                     (int_tf_st_once_for gs) (int_dom_enter_once_st_for gs)) a d g) =
   dg_spec_step (base_dg_spec_for_lifted gs is_bot_state (int_tf_once_for gs)) a
     (map_lift (fun_of_exec_dg_st_for gs) d) (map_lift (fun_of_exec_dg_st_for gs) g)"
  by (rule base_dg_spec_st_for_lifted_dg_spec_step_commute
        [OF int_tf_st_once_for_commute[folded fun_of_exec_dg_st_for_def]])
     simp

theorem int_once_base_dg_spec_enter_commute:
  "map_prod (map_lift (fun_of_exec_dg_st_for gs)) (map_lift (fun_of_exec_dg_st_for gs))
     (dgs_enter (base_dg_spec_st_for_lifted gs (\<lambda>s. is_bot_state (fun_of_exec_dg_st_for gs s))
                  (int_tf_st_once_for gs) (int_dom_enter_once_st_for gs)) xs es d g) =
   dgs_enter (base_dg_spec_for_lifted gs is_bot_state (int_tf_once_for gs)) xs es
     (map_lift (fun_of_exec_dg_st_for gs) d) (map_lift (fun_of_exec_dg_st_for gs) g)"
  by (rule base_dg_spec_st_for_lifted_dgs_enter_commute
        [OF int_dom_enter_once_st_for_commute[folded fun_of_exec_dg_st_for_def]])
     simp

theorem int_once_base_dg_spec_combine_commute:
  "map_prod (map_lift (fun_of_exec_dg_st_for gs)) (map_lift (fun_of_exec_dg_st_for gs))
     (dgs_combine (base_dg_spec_st_for_lifted gs (\<lambda>s. is_bot_state (fun_of_exec_dg_st_for gs s))
                    (int_tf_st_once_for gs) (int_dom_enter_once_st_for gs)) dst dc de g) =
   dgs_combine (base_dg_spec_for_lifted gs is_bot_state (int_tf_once_for gs)) dst
     (map_lift (fun_of_exec_dg_st_for gs) dc) (map_lift (fun_of_exec_dg_st_for gs) de)
     (map_lift (fun_of_exec_dg_st_for gs) g)"
  by (rule base_dg_spec_st_for_lifted_dgs_combine_commute) simp

subsection \<open>Refine_Fixpoint\<close>

theorem int_fixpoint_base_dg_spec_step_commute:
  "map_prod (map_lift (fun_of_exec_dg_st_for gs)) (map_lift (fun_of_exec_dg_st_for gs))
     (dg_spec_step (base_dg_spec_st_for_lifted gs (\<lambda>s. is_bot_state (fun_of_exec_dg_st_for gs s))
                     (int_tf_st_fixpoint_for gs) (int_dom_enter_fixpoint_st_for gs)) a d g) =
   dg_spec_step (base_dg_spec_for_lifted gs is_bot_state (int_tf_fixpoint_for gs)) a
     (map_lift (fun_of_exec_dg_st_for gs) d) (map_lift (fun_of_exec_dg_st_for gs) g)"
  by (rule base_dg_spec_st_for_lifted_dg_spec_step_commute
        [OF int_tf_st_fixpoint_for_commute[folded fun_of_exec_dg_st_for_def]])
     simp

theorem int_fixpoint_base_dg_spec_enter_commute:
  "map_prod (map_lift (fun_of_exec_dg_st_for gs)) (map_lift (fun_of_exec_dg_st_for gs))
     (dgs_enter (base_dg_spec_st_for_lifted gs (\<lambda>s. is_bot_state (fun_of_exec_dg_st_for gs s))
                  (int_tf_st_fixpoint_for gs) (int_dom_enter_fixpoint_st_for gs)) xs es d g) =
   dgs_enter (base_dg_spec_for_lifted gs is_bot_state (int_tf_fixpoint_for gs)) xs es
     (map_lift (fun_of_exec_dg_st_for gs) d) (map_lift (fun_of_exec_dg_st_for gs) g)"
  by (rule base_dg_spec_st_for_lifted_dgs_enter_commute
        [OF int_dom_enter_fixpoint_st_for_commute[folded fun_of_exec_dg_st_for_def]])
     simp

theorem int_fixpoint_base_dg_spec_combine_commute:
  "map_prod (map_lift (fun_of_exec_dg_st_for gs)) (map_lift (fun_of_exec_dg_st_for gs))
     (dgs_combine (base_dg_spec_st_for_lifted gs (\<lambda>s. is_bot_state (fun_of_exec_dg_st_for gs s))
                    (int_tf_st_fixpoint_for gs) (int_dom_enter_fixpoint_st_for gs)) dst dc de g) =
   dgs_combine (base_dg_spec_for_lifted gs is_bot_state (int_tf_fixpoint_for gs)) dst
     (map_lift (fun_of_exec_dg_st_for gs) dc) (map_lift (fun_of_exec_dg_st_for gs) de)
     (map_lift (fun_of_exec_dg_st_for gs) g)"
  by (rule base_dg_spec_st_for_lifted_dgs_combine_commute) simp

end

end
