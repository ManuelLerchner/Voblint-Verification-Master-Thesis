theory DG_Local_State_Exec
  imports "Voblint_Framework.DG_Local_State_Spec"
    Ownership_Split_Exec
    Exec_St_Reachability
begin

section \<open>Executable Base-style DG construction\<close>

text \<open>
  Executable mirror of \<^const>\<open>local_state_dg_spec_for_lifted\<close>: the same
  \<^const>\<open>local_dg_spec\<close> shape, over \<open>'a exec_dg_st lifted\<close> instead of
  \<open>'a abs_state lifted\<close>, with \<open>tf_st\<close> a bare \<open>edge_action \<Rightarrow> _\<close> dispatcher
  -- the executable side dispatches on the action rather than naming one operation
  per edge kind -- and \<open>enter_st\<close> its enter counterpart. Local-only means it reads no global and
  publishes none, so its compiled equations carry no \<open>QueryG\<close> and no \<open>Side\<close>
  -- exactly as on the mathematical side.

  One field differs from the mathematical construction: the env stage of \<open>combine\<close>
  is not the identity here. \<^const>\<open>combine_assign_resolved_q\<close> (unlike
  \<^const>\<open>combine_collect_abs\<close>) does not itself select
  locals-from-caller/globals-from-callee; that selection is what
  \<^const>\<open>combine_resolved_st_q\<close> computes, so the env stage must compute it
  explicitly before the assign stage writes the return value.
\<close>

definition local_state_dg_spec_st_for_lifted ::
  "(vname \<Rightarrow> bool)
   \<Rightarrow> ('a::bounded_semilattice_sup_bot exec_dg_st \<Rightarrow> bool)
   \<Rightarrow> (edge_action \<Rightarrow> 'a exec_dg_st \<Rightarrow> 'a exec_dg_st)
   \<Rightarrow> (call_info \<Rightarrow> 'a exec_dg_st \<Rightarrow> 'a exec_dg_st)
   \<Rightarrow> ('x,'k,unit,'a exec_dg_st lifted,'g::bounded_semilattice_sup_bot) dg_spec"
where
  "local_state_dg_spec_st_for_lifted gs empty_pred tf_st enter_st = local_dg_spec
     (transfer_lift empty_pred (tf_st EA_Nop))
     (\<lambda>x e. transfer_lift empty_pred (tf_st (EA_Assign x e)))
     (\<lambda>sc x. transfer_lift empty_pred (tf_st (EA_Special sc x)))
     (\<lambda>b pol. transfer_lift empty_pred
        (tf_st (if pol then EA_Assume b else EA_AssumeNot b)))
     (\<lambda>p. transfer_lift empty_pred (tf_st (EA_Body p)))
     (\<lambda>e p. transfer_lift empty_pred (tf_st (EA_Ret e p)))
     (\<lambda>ci d. [(d, transfer_lift empty_pred (enter_st ci) d)])
     (\<lambda>ev. transfer_lift empty_pred
        (tf_st (case ev of Check_Event bc \<Rightarrow> EA_Check bc)))
     (\<lambda>ci dc de. case dc of Bot \<Rightarrow> Bot | Lifted x \<Rightarrow>
        (case de of Bot \<Rightarrow> Bot | Lifted y \<Rightarrow> Lifted (combine_resolved_st_q x y)))
     (\<lambda>ci dcM de. transfer_lift2 empty_pred
        (\<lambda>env0 de0. combine_assign_resolved_q gs (ci_dst ci)
             (lookup_resolved_st_q de0 (location_of gs ret_var)) env0)
        dcM de)"

text \<open>Consumed at code-generation time like every other specification builder
  (see \<^theory>\<open>Voblint_Framework.DG_Spec\<close>): the executable carrier changes what a
  transfer computes, not whether the specification can be exported.\<close>

declare local_state_dg_spec_st_for_lifted_def [code_unfold]

subsection \<open>Basic equations\<close>

lemma local_spec_step_transfer_lift_tf_st:
  "local_spec_step
     (transfer_lift empty_pred (tf_st EA_Nop))
     (\<lambda>x e. transfer_lift empty_pred (tf_st (EA_Assign x e)))
     (\<lambda>sc x. transfer_lift empty_pred (tf_st (EA_Special sc x)))
     (\<lambda>b pol. transfer_lift empty_pred
        (tf_st (if pol then EA_Assume b else EA_AssumeNot b)))
     (\<lambda>p. transfer_lift empty_pred (tf_st (EA_Body p)))
     (\<lambda>e p. transfer_lift empty_pred (tf_st (EA_Ret e p)))
     (\<lambda>ev. transfer_lift empty_pred
        (tf_st (case ev of Check_Event bc \<Rightarrow> EA_Check bc))) a
     = transfer_lift empty_pred (tf_st a)"
  by (cases a) simp_all

lemma dg_spec_step_local_state_st_for_lifted:
  "dg_spec_step (local_state_dg_spec_st_for_lifted gs empty_pred tf_st enter_st) a
     = local_transfer (transfer_lift empty_pred (tf_st a))"
  by (simp add: local_state_dg_spec_st_for_lifted_def local_spec_step_transfer_lift_tf_st)

lemma dgs_enter_local_state_st_for_lifted:
  "enter\<^sup># (local_state_dg_spec_st_for_lifted gs empty_pred tf_st enter_st) ci
     = local_enter_transfer (\<lambda>d. [(d, transfer_lift empty_pred (enter_st ci) d)])"
  by (simp add: local_state_dg_spec_st_for_lifted_def)

text \<open>The caller half of \<open>enter\<close> is the identity for the same reason as in the
  abstract Base record: the carrier relates no two locations, so a call has
  nothing in it to invalidate. What the env stage then merges is the raw
  call-site value against the callee exit.\<close>

definition combine_env_st_lifted ::
  "'a::bounded_semilattice_sup_bot exec_dg_st lifted \<Rightarrow> 'a exec_dg_st lifted
   \<Rightarrow> 'a exec_dg_st lifted"
where
  "combine_env_st_lifted dc de =
     (case dc of Bot \<Rightarrow> Bot | Lifted x \<Rightarrow>
        (case de of Bot \<Rightarrow> Bot | Lifted y \<Rightarrow> Lifted (combine_resolved_st_q x y)))"

lemma dg_spec_combine_transfer_local_state_st_for_lifted:
  "dg_spec_combine_transfer (local_state_dg_spec_st_for_lifted gs empty_pred tf_st enter_st) ci
     = local_combine_transfer
         (\<lambda>dc de. transfer_lift2 empty_pred
            (\<lambda>env0 de0. combine_assign_resolved_q gs (ci_dst ci)
                 (lookup_resolved_st_q de0 (location_of gs ret_var)) env0)
            (combine_env_st_lifted dc de) de)"
  by (simp add: local_state_dg_spec_st_for_lifted_def combine_env_st_lifted_def)

end
