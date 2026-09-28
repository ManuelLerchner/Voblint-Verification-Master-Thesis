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
  \<^type>\<open>dg_spec\<close> two ways: \<open>local_state_dg_spec_for\<close> on the raw
  states, and \<open>local_state_dg_spec_for_lifted\<close> on states carrying an
  explicit unreachable value, where a dead point collapses to \<^const>\<open>Bot\<close>
  before any transfer runs.

  \<open>sound_transfer_for\<close> is the contract those operations owe: every
  concrete transition the collecting semantics allows must land inside the
  concretization of what the corresponding operation computes. A domain discharges
  it once, by \<open>interpretation\<close>, and both constructions become sound
  specifications.

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

locale sound_transfer_for =
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

context sound_transfer_for
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

definition state_component ::
  "(vname \<Rightarrow> bool)
   \<Rightarrow> ('a::numeric_domain abs_state \<Rightarrow> 'a abs_state)
   \<Rightarrow> (vname \<Rightarrow> exp \<Rightarrow> 'a abs_state \<Rightarrow> 'a abs_state)
   \<Rightarrow> (special_call \<Rightarrow> vname \<Rightarrow> 'a abs_state \<Rightarrow> 'a abs_state)
   \<Rightarrow> (exp \<Rightarrow> bool \<Rightarrow> 'a abs_state \<Rightarrow> 'a abs_state)
   \<Rightarrow> (pname \<Rightarrow> 'a abs_state \<Rightarrow> 'a abs_state)
   \<Rightarrow> (exp option \<Rightarrow> pname \<Rightarrow> 'a abs_state \<Rightarrow> 'a abs_state)
   \<Rightarrow> (call_info \<Rightarrow> 'a abs_state \<Rightarrow> 'a abs_state)
   \<Rightarrow> (analysis_event \<Rightarrow> 'a abs_state \<Rightarrow> 'a abs_state)
   \<Rightarrow> 'a abs_state mcp_component"
where
  "state_component \<G> sk asn sp br bd rt en ev = \<lparr>
     mc_query = (\<lambda>_ _. \<top>),
     mc_skip = (\<lambda>_. sk), mc_assign = (\<lambda>_. asn), mc_special = (\<lambda>_. sp),
     mc_branch = (\<lambda>_. br), mc_body = (\<lambda>_. bd), mc_return = (\<lambda>_. rt), mc_event = (\<lambda>_. ev),
     mc_enter = (\<lambda>_ ci p. [(fst p, en ci (fst p))]),
     mc_combine_env = (\<lambda>_ _ ci dc de. dc),
     mc_combine_assign = (\<lambda>_ ci. combine\<^sup># \<G> (ci_dst ci)) \<rparr>"

lemma component_step_state_component [simp]:
  "component_step (state_component \<G> sk asn sp br bd rt en ev) a
     = local_spec_step sk asn sp br bd rt ev a"
  by (simp add: component_step_def mc_step_def state_component_def fun_eq_iff)

lemma mc_step_state_component [simp]:
  "mc_step (state_component \<G> sk asn sp br bd rt en ev) A a
     = local_spec_step sk asn sp br bd rt ev a"
  by (simp add: mc_step_def state_component_def)

lemma mc_combine_state_component [simp]:
  "mc_combine (state_component \<G> sk asn sp br bd rt en ev) A B ci dc de
     = combine\<^sup># \<G> (ci_dst ci) dc de"
  by (simp add: state_component_def)

context sound_transfer_for
begin

abbreviation tf_component :: "'a abs_state mcp_component" where
  "tf_component \<equiv> state_component \<G> sk asn sp br bd rt en ev"

theorem state_component_sound: "mcp_component_sound \<G> gamma_state tf_component"
proof -
  have step: "edge_collect a (\<lbrakk>d\<rbrakk> \<inter> Collect (eval_query.oracle_holds A))
      \<subseteq> \<lbrakk>mc_step tf_component A a d\<rbrakk>" for a A and d :: "'a abs_state"
    by (simp only: mc_step_state_component)
       (rule subset_trans[OF edge_collect_mono[OF Int_lower1] step_sound_for])
  show ?thesis
    unfolding mcp_component_sound_def
    using gamma_state_mono step
    by (auto simp: state_component_def call_enter_CallEdge combine_collect_sound)
qed

end

subsection \<open>The unlifted specification\<close>

definition local_state_dg_spec_for ::
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
where
  "local_state_dg_spec_for \<G> sk asn sp br bd rt en ev
     = component_spec (state_component \<G> sk asn sp br bd rt en ev)"

declare local_state_dg_spec_for_def [code_unfold]

lemma dg_spec_step_local_state_for:
  "dg_spec_step (local_state_dg_spec_for \<G> sk asn sp br bd rt en ev) a
     = local_transfer (local_spec_step sk asn sp br bd rt ev a)"
  by (simp add: local_state_dg_spec_for_def)

lemma dg_spec_wf_local_state_dg_spec_for [intro, simp]:
  "dg_spec_wf (local_state_dg_spec_for \<G> sk asn sp br bd rt en ev)"
  by (simp add: local_state_dg_spec_for_def)

theorem (in sound_transfer_for) local_state_dg_spec_for_contract:
  "analysis_contract (local_state_dg_spec_for \<G> sk asn sp br bd rt en ev) (\<lambda>d g. \<lbrakk>d\<rbrakk>) \<G>"
  unfolding local_state_dg_spec_for_def by (rule component_contract[OF state_component_sound])


subsection \<open>Transporting soundness through the reachability lift\<close>

text \<open>
  The bottom bookkeeping the lift needs --- \<open>transfer_lift_sound_collect\<close>,
  \<open>transfer_lift_sound_mem\<close>, \<open>transfer_lift2_sound_mem\<close> --- is proved once in
  \<^theory>\<open>Voblint_Domain.Nonrelational_Reachability\<close>, beside the
  concretization it is about, and the commute laws in
  \<^theory>\<open>Voblint_Domain.Reachability_Lift\<close> beside the lift itself. Neither
  concerns a \<^type>\<open>dg_spec\<close>; this theory only applies them.
\<close>
subsection \<open>The reachability-lifted construction\<close>

definition lifted_state_component ::
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
   \<Rightarrow> 'a abs_state lifted mcp_component"
where
  "lifted_state_component \<G> empty_pred sk asn sp br bd rt en ev = \<lparr>
     mc_query = (\<lambda>_ _. \<top>),
     mc_skip = (\<lambda>_. transfer_lift empty_pred sk),
     mc_assign = (\<lambda>_ x e. transfer_lift empty_pred (asn x e)),
     mc_special = (\<lambda>_ sc x. transfer_lift empty_pred (sp sc x)),
     mc_branch = (\<lambda>_ b pol. transfer_lift empty_pred (br b pol)),
     mc_body = (\<lambda>_ p. transfer_lift empty_pred (bd p)),
     mc_return = (\<lambda>_ e p. transfer_lift empty_pred (rt e p)),
     mc_event = (\<lambda>_ evt. transfer_lift empty_pred (ev evt)),
     mc_enter = (\<lambda>_ ci p. [(fst p, transfer_lift empty_pred (en ci) (fst p))]),
     mc_combine_env = (\<lambda>_ _ ci dc de. dc),
     mc_combine_assign = (\<lambda>_ ci dcM de.
        transfer_lift2 empty_pred (combine\<^sup># \<G> (ci_dst ci)) dcM de) \<rparr>"

definition local_state_dg_spec_for_lifted ::
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
where
  "local_state_dg_spec_for_lifted \<G> empty_pred sk asn sp br bd rt en ev
     = component_spec (lifted_state_component \<G> empty_pred sk asn sp br bd rt en ev)"

declare local_state_dg_spec_for_lifted_def [code_unfold]

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

lemma mc_step_lifted_state_component [simp]:
  "mc_step (lifted_state_component \<G> empty_pred sk asn sp br bd rt en ev) A a
     = transfer_lift empty_pred (local_spec_step sk asn sp br bd rt ev a)"
  by (simp add: mc_step_def lifted_state_component_def local_spec_step_transfer_lift)

lemma component_step_lifted_state_component [simp]:
  "component_step (lifted_state_component \<G> empty_pred sk asn sp br bd rt en ev) a
     = transfer_lift empty_pred (local_spec_step sk asn sp br bd rt ev a)"
  by (simp add: component_step_def fun_eq_iff)

lemma dg_spec_step_local_state_for_lifted:
  "dg_spec_step (local_state_dg_spec_for_lifted \<G> empty_pred sk asn sp br bd rt en ev) a
     = local_transfer (transfer_lift empty_pred (local_spec_step sk asn sp br bd rt ev a))"
  by (simp add: local_state_dg_spec_for_lifted_def)

lemma dg_spec_wf_local_state_dg_spec_for_lifted [intro, simp]:
  "dg_spec_wf (local_state_dg_spec_for_lifted \<G> empty_pred sk asn sp br bd rt en ev)"
  by (simp add: local_state_dg_spec_for_lifted_def)

lemma dgs_enter_local_state_for_lifted:
  "enter\<^sup># (local_state_dg_spec_for_lifted \<G> empty_pred sk asn sp br bd rt en ev) ci
     = local_enter_transfer (\<lambda>d. [(d, transfer_lift empty_pred (en ci) d)])"
  by (simp add: local_state_dg_spec_for_lifted_def lifted_state_component_def)

text \<open>The caller continuation and the env stage are both identities, so the
  whole return pipeline is the return assignment applied to the raw call-site
  value and the callee exit.\<close>

lemma dg_spec_combine_transfer_local_state_for_lifted:
  "dg_spec_combine_transfer
     (local_state_dg_spec_for_lifted \<G> empty_pred sk asn sp br bd rt en ev) ci
     = local_combine_transfer
         (\<lambda>dc de. transfer_lift2 empty_pred (combine\<^sup># \<G> (ci_dst ci)) dc de)"
  by (simp add: local_state_dg_spec_for_lifted_def lifted_state_component_def)

subsection \<open>Soundness of the lifted construction\<close>

text \<open>
  The meaning of a Base-style equation never depends on the global slot:
  nothing in \<^const>\<open>local_state_dg_spec_for_lifted\<close> ever publishes to or reads
  from it, so \<open>gamma_dg_local_state\<close> ignores its global argument entirely and the
  component's obligations are the transported pure facts.
\<close>

definition gamma_dg_local_state ::
  "'a::numeric_domain abs_state lifted \<Rightarrow> 'g::bounded_semilattice_sup_bot \<Rightarrow> store set"
where
  "gamma_dg_local_state d g = \<lbrakk>d\<rbrakk>\<^sub>\<bottom>"

context sound_transfer_for
begin

abbreviation lifted_tf_component ::
  "('a abs_state \<Rightarrow> bool) \<Rightarrow> 'a abs_state lifted mcp_component" where
  "lifted_tf_component empty_pred \<equiv>
     lifted_state_component \<G> empty_pred sk asn sp br bd rt en ev"

theorem lifted_state_component_sound:
  assumes empty_pred_sound: "\<And>\<sigma>. empty_pred \<sigma> \<Longrightarrow> \<lbrakk>\<sigma>\<rbrakk> = {}"
  shows "mcp_component_sound \<G> (\<lambda>d. \<lbrakk>d\<rbrakk>\<^sub>\<bottom>) (lifted_tf_component empty_pred)"
proof -
  have step: "edge_collect a (\<lbrakk>d\<rbrakk>\<^sub>\<bottom> \<inter> Collect (eval_query.oracle_holds A))
      \<subseteq> \<lbrakk>mc_step (lifted_tf_component empty_pred) A a d\<rbrakk>\<^sub>\<bottom>" for a A and d :: "'a abs_state lifted"
    by (simp only: mc_step_lifted_state_component)
       (rule subset_trans[OF edge_collect_mono[OF Int_lower1] transfer_lift_sound_collect
          [OF step_sound_for edge_collect_empty_set empty_pred_sound]])
  have enter: "call_enter \<G> (CallEdge (ci_dst ci) (ci_formals ci) (ci_args ci)) s
      \<in> \<lbrakk>transfer_lift empty_pred (en ci) d\<rbrakk>\<^sub>\<bottom>" if "s \<in> \<lbrakk>d\<rbrakk>\<^sub>\<bottom>" for s d ci
    by (rule transfer_lift_sound_mem[OF _ empty_pred_sound that])
       (simp add: call_enter_CallEdge tf_sound_enter_entry_for)
  have comb: "combine_collect \<G> (ci_dst ci) s t
      \<in> \<lbrakk>transfer_lift2 empty_pred (combine\<^sup># \<G> (ci_dst ci)) dc de\<rbrakk>\<^sub>\<bottom>"
    if "s \<in> \<lbrakk>dc\<rbrakk>\<^sub>\<bottom>" "t \<in> \<lbrakk>de\<rbrakk>\<^sub>\<bottom>" for s t dc de ci
    by (rule transfer_lift2_sound_mem[OF combine_collect_sound empty_pred_sound that])
  have mono: "\<forall>x y. x \<le> y \<longrightarrow> \<lbrakk>x\<rbrakk>\<^sub>\<bottom> \<subseteq> \<lbrakk>y\<rbrakk>\<^sub>\<bottom>"
    by (meson gamma_lift_mono gamma_state_mono)
  show ?thesis
    unfolding mcp_component_sound_def
    using mono step enter comb by (auto simp: lifted_state_component_def)
qed

theorem local_state_dg_spec_for_lifted_contract:
  assumes empty_pred_sound: "\<And>\<sigma>. empty_pred \<sigma> \<Longrightarrow> \<lbrakk>\<sigma>\<rbrakk> = {}"
  shows "analysis_contract (local_state_dg_spec_for_lifted \<G> empty_pred sk asn sp br bd rt en ev)
           gamma_dg_local_state \<G>"
  unfolding local_state_dg_spec_for_lifted_def gamma_dg_local_state_def[abs_def]
  by (rule component_contract[OF lifted_state_component_sound[OF empty_pred_sound]])

end

end
