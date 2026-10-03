theory DG_Local_State_Spec
  imports "Voblint_Framework.MCP_Spec" Transfer_Algebra "Voblint_Domain.Nonrelational_Reachability"
begin

section \<open>What a whole-state analysis supplies, and when it is sound\<close>

text \<open>
  A Base-style analysis answers from one pointwise abstract state per program
  point and never touches a global: its transfers read the manager's local value,
  compute, and return, so the compiled equations carry no \<open>QueryG\<close> and no
  \<open>Side\<close>. Such an analysis supplies seven pure edge-operation families ---
  skip, assign, special, branch, body, return, event, with branch covering both
  \<open>EA_Assume\<close> and \<open>EA_AssumeNot\<close> --- plus the callee entry, and this theory
  turns them into a
  \<^type>\<open>dg_spec\<close> two ways: \<open>state_dg_spec\<close> on the raw
  states, and \<open>lifted_state_dg_spec\<close> on states carrying an
  explicit unreachable value, where a dead point collapses to \<^const>\<open>Bot\<close>
  before any transfer runs.

  \<open>sound_nonrelational_transfer\<close> is the contract those operations owe: every
  concrete transition the collecting semantics allows must land inside the
  concretization of what the corresponding operation computes. A domain discharges
  it once, by \<open>interpretation\<close>, and \<open>state_dg_spec\<close> becomes a sound
  specification. \<open>lifted_state_dg_spec\<close> is the structural target its
  executable mirror refines; \<open>DG_Local_State_Exec_Refinement\<close> proves that
  mirror sound directly.

  The call boundary is fixed here rather than supplied. A call answers exactly one
  alternative, whose continuation is the caller value unchanged. That is sound
  because of what the fixed combine does later, not because of anything about the
  carrier: the continuation is kept for its \<^emph>\<open>local\<close> part, and whatever the
  callee may have invalidated --- the globals --- is taken from the callee exit
  instead. A nonrelational caller still holds global facts a callee can
  invalidate; it is the combine protocol that repairs them, not the absence of
  relations. The environment stage passes that continuation through, and the
  whole return happens in the assign stage as
  \<^const>\<open>combine_collect_abs\<close>: caller locals, callee globals, and the callee's
  \<^const>\<open>ret_var\<close> written to the destination. An analysis that needs a
  different boundary overrides those three fields of its own specification instead
  of using these builders, the way \<open>varEq\<close> supplies its own
  \<open>combine_env\<close> upstream.
\<close>

subsection \<open>The transfer contract\<close>

text \<open>One assumption per operation, each an inference rule from a concrete store
  in an abstract state's concretization to the corresponding concrete successor in
  the operation's own result. A domain proves one fact per operation about its
  own functions and interprets this locale once; nothing below asks it for
  more.\<close>

locale sound_nonrelational_transfer =
  fixes \<G> :: "vname \<Rightarrow> bool"
    and sk :: "'a::numeric_domain abs_state \<Rightarrow> 'a abs_state"
    and asn :: "vname \<Rightarrow> exp \<Rightarrow> 'a abs_state \<Rightarrow> 'a abs_state"
    and sp :: "special_call \<Rightarrow> vname \<Rightarrow> 'a abs_state \<Rightarrow> 'a abs_state"
    and br :: "exp \<Rightarrow> bool \<Rightarrow> 'a abs_state \<Rightarrow> 'a abs_state"
    and bd :: "pname \<Rightarrow> 'a abs_state \<Rightarrow> 'a abs_state"
    and rt :: "exp option \<Rightarrow> pname \<Rightarrow> 'a abs_state \<Rightarrow> 'a abs_state"
    and en :: "call_info \<Rightarrow> 'a abs_state \<Rightarrow> 'a abs_state"
    and ev :: "analysis_event \<Rightarrow> 'a abs_state \<Rightarrow> 'a abs_state"
  assumes tf_sound_assign_for[intro]:
    "s \<in> \<lbrakk>\<sigma>\<rbrakk> \<Longrightarrow> s(x := \<lbrakk>a\<rbrakk>\<^sub>e s) \<in> \<lbrakk>asn x a \<sigma>\<rbrakk>"
  assumes tf_sound_special_for[intro]:
    "s \<in> \<lbrakk>\<sigma>\<rbrakk> \<Longrightarrow> special_result sc s v \<Longrightarrow> s(x := v) \<in> \<lbrakk>sp sc x \<sigma>\<rbrakk>"
  assumes tf_sound_branch_for[intro]:
    "s \<in> \<lbrakk>\<sigma>\<rbrakk> \<Longrightarrow> truthy (\<lbrakk>b\<rbrakk>\<^sub>e s) = pol \<Longrightarrow> s \<in> \<lbrakk>br b pol \<sigma>\<rbrakk>"
  assumes tf_sound_skip_for[intro]:
    "s \<in> \<lbrakk>\<sigma>\<rbrakk> \<Longrightarrow> s \<in> \<lbrakk>sk \<sigma>\<rbrakk>"
  assumes tf_sound_body_for[intro]:
    "s \<in> \<lbrakk>\<sigma>\<rbrakk> \<Longrightarrow> s \<in> \<lbrakk>bd p \<sigma>\<rbrakk>"
  assumes tf_sound_return_for[intro]:
    "s \<in> \<lbrakk>\<sigma>\<rbrakk> \<Longrightarrow>
       s(ret_var := (case e of None \<Rightarrow> s ret_var | Some a \<Rightarrow> \<lbrakk>a\<rbrakk>\<^sub>e s))
         \<in> \<lbrakk>rt e p \<sigma>\<rbrakk>"
  assumes tf_sound_enter_entry_for[intro]:
    "s \<in> \<lbrakk>\<sigma>\<rbrakk> \<Longrightarrow>
       bind_formals (ci_formals ci) (map (\<lambda>e. \<lbrakk>e\<rbrakk>\<^sub>e s) (ci_args ci)) (enter_state \<G> s)
         \<in> \<lbrakk>en ci \<sigma>\<rbrakk>"
  assumes tf_sound_event_for[intro]:
    "s \<in> \<lbrakk>\<sigma>\<rbrakk> \<Longrightarrow> s \<in> \<lbrakk>ev evt \<sigma>\<rbrakk>"

text \<open>Each obligation is stated directly as an inference rule
  (\<open>P\<^sub>1 \<Longrightarrow> ... \<Longrightarrow> P\<^sub>n \<Longrightarrow> Q\<close>). Variables not fixed by the locale are
  implicitly generalized, so the assumptions compose directly with \<open>rule\<close>,
  \<open>OF\<close>, and \<open>auto\<close>; no separate Horn-clause restatement is needed.\<close>

context sound_nonrelational_transfer
begin

text \<open>The per-edge dispatcher's soundness, which is what an equation generator's
  step obligation asks for: \<^const>\<open>local_spec_step\<close> selects the operation the
  action names, and each selected operation is sound by one locale assumption.\<close>

lemma step_sound_for[intro]:
  "edge_collect a \<lbrakk>\<sigma>\<rbrakk> \<subseteq> \<lbrakk>local_spec_step sk asn sp br bd rt ev a \<sigma>\<rbrakk>"
proof (cases a)
  case (EA_Special sc x)
  then show ?thesis by (cases sc) auto
qed auto

end

subsection \<open>The operations as a component\<close>

text \<open>What a whole-state analysis actually supplies: eight pure operations over
  \<^typ>\<open>'a abs_state\<close>, packaged as a component whose handler answers nothing, whose
  entry yields the one callee state and leaves the caller's own value untouched,
  and whose return runs the fixed combine in the assign stage. The lifted sibling
  further down differs only in carrying the dead-code lift.\<close>

definition state_local_spec ::
  "(vname \<Rightarrow> bool)
   \<Rightarrow> ('a::numeric_domain abs_state \<Rightarrow> 'a abs_state)
   \<Rightarrow> (vname \<Rightarrow> exp \<Rightarrow> 'a abs_state \<Rightarrow> 'a abs_state)
   \<Rightarrow> (special_call \<Rightarrow> vname \<Rightarrow> 'a abs_state \<Rightarrow> 'a abs_state)
   \<Rightarrow> (exp \<Rightarrow> bool \<Rightarrow> 'a abs_state \<Rightarrow> 'a abs_state)
   \<Rightarrow> (pname \<Rightarrow> 'a abs_state \<Rightarrow> 'a abs_state)
   \<Rightarrow> (exp option \<Rightarrow> pname \<Rightarrow> 'a abs_state \<Rightarrow> 'a abs_state)
   \<Rightarrow> (call_info \<Rightarrow> 'a abs_state \<Rightarrow> 'a abs_state)
   \<Rightarrow> (analysis_event \<Rightarrow> 'a abs_state \<Rightarrow> 'a abs_state)
   \<Rightarrow> 'a abs_state local_spec"
where
  "state_local_spec \<G> sk asn sp br bd rt en ev = \<lparr>
     ls_query = (\<lambda>_ _. \<top>),
     ls_skip = (\<lambda>_. sk), ls_assign = (\<lambda>_. asn), ls_special = (\<lambda>_. sp),
     ls_branch = (\<lambda>_. br), ls_body = (\<lambda>_. bd), ls_return = (\<lambda>_. rt), ls_event = (\<lambda>_. ev),
     ls_enter = (\<lambda>_ ci p. [(fst p, en ci (fst p))]),
     ls_combine_env = (\<lambda>_ _ ci dc de. dc),
     ls_combine_assign = (\<lambda>_ ci. combine\<^sup># \<G> (ci_dst ci)) \<rparr>"

lemma closed_step_state_local_spec [simp]:
  "closed_step (state_local_spec \<G> sk asn sp br bd rt en ev) a
     = local_spec_step sk asn sp br bd rt ev a"
  by (simp add: closed_step_def ls_step_def state_local_spec_def fun_eq_iff)

lemma ls_step_state_local_spec [simp]:
  "ls_step (state_local_spec \<G> sk asn sp br bd rt en ev) A a
     = local_spec_step sk asn sp br bd rt ev a"
  by (simp add: ls_step_def state_local_spec_def)

lemma ls_combine_state_local_spec [simp]:
  "ls_combine (state_local_spec \<G> sk asn sp br bd rt en ev) A B ci dc de
     = combine\<^sup># \<G> (ci_dst ci) dc de"
  by (simp add: state_local_spec_def)

context sound_nonrelational_transfer
begin

abbreviation tf_spec :: "'a abs_state local_spec" where
  "tf_spec \<equiv> state_local_spec \<G> sk asn sp br bd rt en ev"

theorem state_local_spec_sound: "sound_local_spec \<G> gamma_state tf_spec"
proof -
  have step: "edge_collect a (\<lbrakk>d\<rbrakk> \<inter> Collect (eval_query.oracle_holds A))
      \<subseteq> \<lbrakk>ls_step tf_spec A a d\<rbrakk>" for a A and d :: "'a abs_state"
    by (simp only: ls_step_state_local_spec)
       (rule subset_trans[OF edge_collect_mono[OF Int_lower1] step_sound_for])
  show ?thesis
    unfolding sound_local_spec_def
    using gamma_state_mono step
    by (auto simp: state_local_spec_def call_enter_CallEdge combine_collect_sound)
qed

end

subsection \<open>The unlifted specification\<close>

text \<open>
  \<open>state_dg_spec\<close> turns the state-level local specification into an
  equation-system specification via \<open>dg_spec_of\<close>, without the reachability
  lifting.
\<close>

definition state_dg_spec ::
  "(vname \<Rightarrow> bool)
   \<Rightarrow> ('a::numeric_domain abs_state \<Rightarrow> 'a abs_state)
   \<Rightarrow> (vname \<Rightarrow> exp \<Rightarrow> 'a abs_state \<Rightarrow> 'a abs_state)
   \<Rightarrow> (special_call \<Rightarrow> vname \<Rightarrow> 'a abs_state \<Rightarrow> 'a abs_state)
   \<Rightarrow> (exp \<Rightarrow> bool \<Rightarrow> 'a abs_state \<Rightarrow> 'a abs_state)
   \<Rightarrow> (pname \<Rightarrow> 'a abs_state \<Rightarrow> 'a abs_state)
   \<Rightarrow> (exp option \<Rightarrow> pname \<Rightarrow> 'a abs_state \<Rightarrow> 'a abs_state)
   \<Rightarrow> (call_info \<Rightarrow> 'a abs_state \<Rightarrow> 'a abs_state)
   \<Rightarrow> (analysis_event \<Rightarrow> 'a abs_state \<Rightarrow> 'a abs_state)
   \<Rightarrow> ('x,'k,unit,'a abs_state,'g::bounded_semilattice_sup_bot) dg_spec"
where [code_unfold]:
  "state_dg_spec \<G> sk asn sp br bd rt en ev
     = dg_spec_of (state_local_spec \<G> sk asn sp br bd rt en ev)"


lemma dg_spec_step_state_dg_spec:
  "dg_spec_step (state_dg_spec \<G> sk asn sp br bd rt en ev) a
     = local_transfer (local_spec_step sk asn sp br bd rt ev a)"
  by (simp add: state_dg_spec_def)

lemma dg_spec_wf_state_dg_spec [intro, simp]:
  "dg_spec_wf (state_dg_spec \<G> sk asn sp br bd rt en ev)"
  by (simp add: state_dg_spec_def)

theorem (in sound_nonrelational_transfer) state_dg_spec_contract:
  "analysis_contract (state_dg_spec \<G> sk asn sp br bd rt en ev) (\<lambda>d g. \<lbrakk>d\<rbrakk>) \<G>"
  unfolding state_dg_spec_def by (rule dg_spec_of_contract[OF state_local_spec_sound])


subsection \<open>The reachability-lifted construction\<close>

text \<open>
  The same operations, each wrapped in \<^const>\<open>transfer_lift\<close>: a \<^const>\<open>Bot\<close> input
  stays \<^const>\<open>Bot\<close>, and a result the supplied emptiness predicate flags
  collapses to it.
\<close>

definition lifted_state_local_spec ::
  "(vname \<Rightarrow> bool)
   \<Rightarrow> ('a abs_state \<Rightarrow> bool)
   \<Rightarrow> ('a::numeric_domain abs_state \<Rightarrow> 'a abs_state)
   \<Rightarrow> (vname \<Rightarrow> exp \<Rightarrow> 'a abs_state \<Rightarrow> 'a abs_state)
   \<Rightarrow> (special_call \<Rightarrow> vname \<Rightarrow> 'a abs_state \<Rightarrow> 'a abs_state)
   \<Rightarrow> (exp \<Rightarrow> bool \<Rightarrow> 'a abs_state \<Rightarrow> 'a abs_state)
   \<Rightarrow> (pname \<Rightarrow> 'a abs_state \<Rightarrow> 'a abs_state)
   \<Rightarrow> (exp option \<Rightarrow> pname \<Rightarrow> 'a abs_state \<Rightarrow> 'a abs_state)
   \<Rightarrow> (call_info \<Rightarrow> 'a abs_state \<Rightarrow> 'a abs_state)
   \<Rightarrow> (analysis_event \<Rightarrow> 'a abs_state \<Rightarrow> 'a abs_state)
   \<Rightarrow> 'a abs_state lifted local_spec"
where
  "lifted_state_local_spec \<G> empty_pred sk asn sp br bd rt en ev = \<lparr>
     ls_query = (\<lambda>_ _. \<top>),
     ls_skip = (\<lambda>_. transfer_lift empty_pred sk),
     ls_assign = (\<lambda>_ x e. transfer_lift empty_pred (asn x e)),
     ls_special = (\<lambda>_ sc x. transfer_lift empty_pred (sp sc x)),
     ls_branch = (\<lambda>_ b pol. transfer_lift empty_pred (br b pol)),
     ls_body = (\<lambda>_ p. transfer_lift empty_pred (bd p)),
     ls_return = (\<lambda>_ e p. transfer_lift empty_pred (rt e p)),
     ls_event = (\<lambda>_ evt. transfer_lift empty_pred (ev evt)),
     ls_enter = (\<lambda>_ ci p. [(fst p, transfer_lift empty_pred (en ci) (fst p))]),
     ls_combine_env = (\<lambda>_ _ ci dc de. dc),
     ls_combine_assign = (\<lambda>_ ci dcM de.
        transfer_lift2 empty_pred (combine\<^sup># \<G> (ci_dst ci)) dcM de) \<rparr>"

definition lifted_state_dg_spec ::
  "(vname \<Rightarrow> bool)
   \<Rightarrow> ('a abs_state \<Rightarrow> bool)
   \<Rightarrow> ('a::numeric_domain abs_state \<Rightarrow> 'a abs_state)
   \<Rightarrow> (vname \<Rightarrow> exp \<Rightarrow> 'a abs_state \<Rightarrow> 'a abs_state)
   \<Rightarrow> (special_call \<Rightarrow> vname \<Rightarrow> 'a abs_state \<Rightarrow> 'a abs_state)
   \<Rightarrow> (exp \<Rightarrow> bool \<Rightarrow> 'a abs_state \<Rightarrow> 'a abs_state)
   \<Rightarrow> (pname \<Rightarrow> 'a abs_state \<Rightarrow> 'a abs_state)
   \<Rightarrow> (exp option \<Rightarrow> pname \<Rightarrow> 'a abs_state \<Rightarrow> 'a abs_state)
   \<Rightarrow> (call_info \<Rightarrow> 'a abs_state \<Rightarrow> 'a abs_state)
   \<Rightarrow> (analysis_event \<Rightarrow> 'a abs_state \<Rightarrow> 'a abs_state)
   \<Rightarrow> ('x,'k,unit,'a abs_state lifted,'g::bounded_semilattice_sup_bot) dg_spec"
where [code_unfold]:
  "lifted_state_dg_spec \<G> empty_pred sk asn sp br bd rt en ev
     = dg_spec_of (lifted_state_local_spec \<G> empty_pred sk asn sp br bd rt en ev)"


lemma local_spec_step_transfer_lift:
  "local_spec_step (transfer_lift empty_pred sk)
     (\<lambda>x e. transfer_lift empty_pred (asn x e))
     (\<lambda>sc x. transfer_lift empty_pred (sp sc x))
     (\<lambda>b pol. transfer_lift empty_pred (br b pol))
     (\<lambda>p. transfer_lift empty_pred (bd p))
     (\<lambda>e p. transfer_lift empty_pred (rt e p))
     (\<lambda>evt. transfer_lift empty_pred (ev evt)) a
     = transfer_lift empty_pred (local_spec_step sk asn sp br bd rt ev a)"
  by (cases a) simp_all

lemma ls_step_lifted_state_local_spec [simp]:
  "ls_step (lifted_state_local_spec \<G> empty_pred sk asn sp br bd rt en ev) A a
     = transfer_lift empty_pred (local_spec_step sk asn sp br bd rt ev a)"
  by (simp add: ls_step_def lifted_state_local_spec_def local_spec_step_transfer_lift)

lemma closed_step_lifted_state_local_spec [simp]:
  "closed_step (lifted_state_local_spec \<G> empty_pred sk asn sp br bd rt en ev) a
     = transfer_lift empty_pred (local_spec_step sk asn sp br bd rt ev a)"
  by (simp add: closed_step_def fun_eq_iff)

lemma dg_spec_step_lifted_state_dg_spec:
  "dg_spec_step (lifted_state_dg_spec \<G> empty_pred sk asn sp br bd rt en ev) a
     = local_transfer (transfer_lift empty_pred (local_spec_step sk asn sp br bd rt ev a))"
  by (simp add: lifted_state_dg_spec_def)

lemma dg_spec_wf_lifted_state_dg_spec [intro, simp]:
  "dg_spec_wf (lifted_state_dg_spec \<G> empty_pred sk asn sp br bd rt en ev)"
  by (simp add: lifted_state_dg_spec_def)

lemma dgs_enter_lifted_state_dg_spec:
  "enter\<^sup># (lifted_state_dg_spec \<G> empty_pred sk asn sp br bd rt en ev) ci
     = local_enter_transfer (\<lambda>d. [(d, transfer_lift empty_pred (en ci) d)])"
  by (simp add: lifted_state_dg_spec_def lifted_state_local_spec_def)

text \<open>The caller continuation and the env stage are both identities, so the
  whole return pipeline is the return assignment applied to the raw call-site
  value and the callee exit.\<close>

lemma dg_spec_combine_transfer_lifted_state_dg_spec:
  "dg_spec_combine_transfer
     (lifted_state_dg_spec \<G> empty_pred sk asn sp br bd rt en ev) ci
     = local_combine_transfer
         (\<lambda>dc de. transfer_lift2 empty_pred (combine\<^sup># \<G> (ci_dst ci)) dc de)"
  by (simp add: lifted_state_dg_spec_def lifted_state_local_spec_def)

end
