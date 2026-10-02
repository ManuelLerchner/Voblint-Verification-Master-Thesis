theory DG_Local_State_Exec
  imports
    Ownership_Split_Exec
    Default_St_Reachability
begin

unbundle default_st_syntax

section \<open>Executable Base-style DG construction\<close>

text \<open>
  Executable mirror of \<^const>\<open>lifted_state_dg_spec\<close>: a component
  over \<open>'a default_st lifted\<close> instead of \<open>'a abs_state lifted\<close>, with \<open>tf_st\<close> a
  bare \<open>edge_action \<Rightarrow> _\<close> dispatcher -- the executable side dispatches on the
  action rather than naming one operation per edge kind -- and \<open>enter_st\<close> its
  enter counterpart. Local-only means it reads no global and publishes none, so
  its compiled equations carry no \<open>QueryG\<close> and no \<open>Side\<close> -- exactly as on the
  mathematical side.

  One field differs from the mathematical construction: the env stage of \<open>combine\<close>
  is not the identity here. \<^const>\<open>combine_assign_default_st\<close> (unlike
  \<^const>\<open>combine_collect_abs\<close>) does not itself select
  locals-from-caller/globals-from-callee; that selection is what
  \<^const>\<open>combine_default_st\<close> computes, so the env stage must compute it
  explicitly before the assign stage writes the return value.
\<close>

text \<open>The caller half of \<open>enter\<close> is the identity for the same reason as in the
  abstract Base record: the carrier relates no two locations, so a call has
  nothing in it to invalidate. What the env stage then merges is the raw
  call-site value against the callee exit.\<close>

definition combine_env_st_lifted ::
  "'a::bounded_semilattice_sup_bot default_st lifted \<Rightarrow> 'a default_st lifted
   \<Rightarrow> 'a default_st lifted"
where
  "combine_env_st_lifted dc de =
     (case dc of Bot \<Rightarrow> Bot | Lifted x \<Rightarrow>
        (case de of Bot \<Rightarrow> Bot | Lifted y \<Rightarrow> Lifted (combine_default_st x y)))"

text \<open>
  The executable analysis is a component whose edge transfers are the one
  dispatcher \<open>tf_st\<close>, lifted over the unreachable state. Its handler answers
  nothing.
\<close>

definition exec_local_spec ::
  "(vname \<Rightarrow> bool) \<Rightarrow> ('a::bounded_semilattice_sup_bot default_st \<Rightarrow> bool)
   \<Rightarrow> (edge_action \<Rightarrow> 'a default_st \<Rightarrow> 'a default_st)
   \<Rightarrow> (call_info \<Rightarrow> 'a default_st \<Rightarrow> 'a default_st)
   \<Rightarrow> 'a default_st lifted local_spec" where
  "exec_local_spec \<G> empty_pred tf_st enter_st = make_local_spec
     (\<lambda>_ _. \<top>)
     (\<lambda>_ a. transfer_lift empty_pred (tf_st a))
     (\<lambda>_ ci p. [(fst p, transfer_lift empty_pred (enter_st ci) (fst p))])
     (\<lambda>_ _ ci. combine_env_st_lifted)
     (\<lambda>_ ci. transfer_lift2 empty_pred
        (\<lambda>env0 de0. combine_assign_default_st \<G> (ci_dst ci)
             de0\<langle>location_of \<G> ret_var\<rangle> env0))"

lemma ls_step_exec_local_spec [simp]:
  "ls_step (exec_local_spec \<G> empty_pred tf_st enter_st) A a = transfer_lift empty_pred (tf_st a)"
  by (simp add: exec_local_spec_def)

lemma closed_step_exec_local_spec [simp]:
  "closed_step (exec_local_spec \<G> empty_pred tf_st enter_st) a
     = transfer_lift empty_pred (tf_st a)"
  by (simp add: closed_step_def fun_eq_iff)

lemma ls_enter_exec_local_spec [simp]:
  "ls_enter (exec_local_spec \<G> empty_pred tf_st enter_st) A ci (d, d)
   = [(d, transfer_lift empty_pred (enter_st ci) d)]"
  by (simp add: exec_local_spec_def)

definition exec_dg_spec ::
  "(vname \<Rightarrow> bool)
   \<Rightarrow> ('a::bounded_semilattice_sup_bot default_st \<Rightarrow> bool)
   \<Rightarrow> (edge_action \<Rightarrow> 'a default_st \<Rightarrow> 'a default_st)
   \<Rightarrow> (call_info \<Rightarrow> 'a default_st \<Rightarrow> 'a default_st)
   \<Rightarrow> ('x,'k,unit,'a default_st lifted,'g::bounded_semilattice_sup_bot) dg_spec"
where
  "exec_dg_spec \<G> empty_pred tf_st enter_st
     = dg_spec_of (exec_local_spec \<G> empty_pred tf_st enter_st)"

text \<open>Consumed at code-generation time like every other specification builder
  (see \<^theory>\<open>Voblint_Framework.DG_Spec\<close>): the executable carrier changes what a
  transfer computes, not whether the specification can be exported.\<close>

declare exec_dg_spec_def [code_unfold]

subsection \<open>Basic equations\<close>

text \<open>
  Unfolding equations for each field of \<open>exec_dg_spec\<close>: step, entry and
  combine are the executable transfers lifted over reachability.
\<close>

lemma dg_spec_step_exec_dg_spec:
  "dg_spec_step (exec_dg_spec \<G> empty_pred tf_st enter_st) a
     = local_transfer (transfer_lift empty_pred (tf_st a))"
  by (simp add: exec_dg_spec_def)

lemma dg_spec_wf_exec_dg_spec [intro, simp]:
  "dg_spec_wf (exec_dg_spec \<G> empty_pred tf_st enter_st)"
  by (simp add: exec_dg_spec_def)

lemma dgs_enter_exec_dg_spec:
  "enter\<^sup># (exec_dg_spec \<G> empty_pred tf_st enter_st) ci
     = local_enter_transfer (\<lambda>d. [(d, transfer_lift empty_pred (enter_st ci) d)])"
  by (simp add: exec_dg_spec_def)

lemma dg_spec_combine_transfer_exec_dg_spec:
  "dg_spec_combine_transfer (exec_dg_spec \<G> empty_pred tf_st enter_st) ci
     = local_combine_transfer
         (\<lambda>dc de. transfer_lift2 empty_pred
            (\<lambda>env0 de0. combine_assign_default_st \<G> (ci_dst ci)
                 de0\<langle>location_of \<G> ret_var\<rangle> env0)
            (combine_env_st_lifted dc de) de)"
  by (simp add: exec_dg_spec_def exec_local_spec_def)

unbundle no default_st_syntax

end
