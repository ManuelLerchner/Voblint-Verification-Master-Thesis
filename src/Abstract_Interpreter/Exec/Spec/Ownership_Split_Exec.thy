theory Ownership_Split_Exec
  imports
    Exec_DG_State
    "Voblint_Framework.DG_Ownership_Split_Spec"
    "Voblint_Framework.DG_Spec_Sound"
    "Voblint_Framework.DG_Keyed_Generator"
    "Voblint_Framework.Routed_Context"
begin

section \<open>The ownership-splitting analysis at the executable carrier\<close>

text \<open>
  \<^const>\<open>ownership_split_transfer_gen\<close> asks only that a carrier can merge a local and a
  global half and project each back out. The association-list carrier answers
  with \<^const>\<open>combine_resolved_st_q\<close> and the two \<open>restrict_\<dots>_resolved_q\<close>
  projections, so the executable analysis is that transfer at those three
  arguments -- not a second definition of what the analysis does.
\<close>

definition ownership_split_transfer_st ::
  "('x,'k,unit,'a::bounded_semilattice_sup_bot exec_dg_st,'a exec_dg_st) man_transfer
   \<Rightarrow> ('x,'k,unit,'a exec_dg_st,'a exec_dg_st) man_transfer"
where
  "ownership_split_transfer_st =
     ownership_split_transfer_gen combine_resolved_st_q restrict_global_resolved_q restrict_local_resolved_q"

text \<open>
  Entry is the same wrapping one step up in arity: it answers a list of
  caller-continuation/callee-entry pairs rather than one successor value, so the
  executable carrier supplies the same three operations to
  \<^const>\<open>ownership_split_enter_transfer_gen\<close>.
\<close>

definition ownership_split_enter_transfer_st ::
  "('x,'k,unit,'a::bounded_semilattice_sup_bot exec_dg_st,'a exec_dg_st) man_enter_transfer
   \<Rightarrow> ('x,'k,unit,'a exec_dg_st,'a exec_dg_st) man_enter_transfer"
where
  "ownership_split_enter_transfer_st =
     ownership_split_enter_transfer_gen combine_resolved_st_q restrict_global_resolved_q
       restrict_local_resolved_q"

text \<open>
  The callee exit reaches the wrapped stage merged against the same shared fact,
  like the caller continuation. The return slot is read off it at the classifier's
  own location for \<^const>\<open>ret_var\<close>; that name is local, so the merge leaves it
  at the callee's own value.
\<close>

definition ownership_split_combine_transfer_st ::
  "(vname \<Rightarrow> bool) \<Rightarrow> call_info
   \<Rightarrow> ('x,'k,unit,'a::bounded_semilattice_sup_bot exec_dg_st,'a exec_dg_st) man_combine_transfer"
where
  "ownership_split_combine_transfer_st \<G> ci =
     ownership_split_combine_transfer_gen combine_resolved_st_q restrict_global_resolved_q
       restrict_local_resolved_q
       (local_combine_transfer
          (\<lambda>env de. combine_assign_resolved_q \<G> (ci_dst ci)
                      (lookup_resolved_st_q de (location_of \<G> ret_var)) env))"

definition ownership_split_dg_spec_st_for ::
  "(vname \<Rightarrow> bool)
   \<Rightarrow> (edge_action \<Rightarrow> 'a::bounded_semilattice_sup_bot exec_dg_st \<Rightarrow> 'a exec_dg_st)
   \<Rightarrow> (call_info \<Rightarrow> 'a exec_dg_st \<Rightarrow> 'a exec_dg_st)
   \<Rightarrow> ('x,'k,unit,'a exec_dg_st,'a exec_dg_st) dg_spec"
where
  "ownership_split_dg_spec_st_for \<G> tf_st enter_st = local_dg_spec_template\<lparr>
     dgs_skip := ownership_split_transfer_st (local_transfer (tf_st EA_Nop)),
     dgs_assign := (\<lambda>x e. ownership_split_transfer_st (local_transfer (tf_st (EA_Assign x e)))),
     dgs_special := (\<lambda>sc x. ownership_split_transfer_st (local_transfer (tf_st (EA_Special sc x)))),
     dgs_branch := (\<lambda>b pol. ownership_split_transfer_st
                      (local_transfer (tf_st (if pol then EA_Assume b else EA_AssumeNot b)))),
     dgs_body := (\<lambda>p. ownership_split_transfer_st (local_transfer (tf_st (EA_Body p)))),
     dgs_return := (\<lambda>e p. ownership_split_transfer_st (local_transfer (tf_st (EA_Ret e p)))),
     dgs_enter := (\<lambda>ci. ownership_split_enter_transfer_st
                          (local_enter_transfer (\<lambda>d. [(d, enter_st ci d)]))),
     dgs_event := (\<lambda>ev. case ev of Check_Event bc
                     \<Rightarrow> ownership_split_transfer_st (local_transfer (tf_st (EA_Check bc)))),
     dgs_combine_assign := ownership_split_combine_transfer_st \<G> \<rparr>"

lemma dg_spec_step_ownership_split_st_for:
  "dg_spec_step (ownership_split_dg_spec_st_for \<G> tf_st enter_st) a
     = ownership_split_transfer_st (local_transfer (tf_st a))"
  unfolding ownership_split_dg_spec_st_for_def
  by (cases a) simp_all

lemma dgs_enter_ownership_split_dg_spec_st_for:
  "enter\<^sup># (ownership_split_dg_spec_st_for \<G> tf_st enter_st) ci
     = ownership_split_enter_transfer_st (local_enter_transfer (\<lambda>d. [(d, enter_st ci d)]))"
  unfolding ownership_split_dg_spec_st_for_def by simp

lemma dg_spec_combine_transfer_ownership_split_dg_spec_st_for:
  "dg_spec_combine_transfer (ownership_split_dg_spec_st_for \<G> tf_st enter_st) ci m de
     = ownership_split_combine_transfer_st \<G> ci m de"
  unfolding dg_spec_combine_transfer_def ownership_split_dg_spec_st_for_def
  by (simp add: local_transfer_def local_combine_transfer_def)

end
