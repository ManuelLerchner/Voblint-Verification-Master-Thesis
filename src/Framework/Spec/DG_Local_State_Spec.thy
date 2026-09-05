theory DG_Local_State_Spec
  imports DG_Spec_Sound Transfer_Algebra "Voblint_Domain.Nonrelational_Reachability"
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
  fixes gs :: "vname \<Rightarrow> bool"
    and sk :: "'a::sound_domain abs_state \<Rightarrow> 'a abs_state"
    and asn :: "vname \<Rightarrow> exp \<Rightarrow> 'a abs_state \<Rightarrow> 'a abs_state"
    and sp :: "special_call \<Rightarrow> vname \<Rightarrow> 'a abs_state \<Rightarrow> 'a abs_state"
    and br :: "exp \<Rightarrow> bool \<Rightarrow> 'a abs_state \<Rightarrow> 'a abs_state"
    and bd :: "pname \<Rightarrow> 'a abs_state \<Rightarrow> 'a abs_state"
    and rt :: "exp option \<Rightarrow> pname \<Rightarrow> 'a abs_state \<Rightarrow> 'a abs_state"
    and en :: "call_info \<Rightarrow> 'a abs_state \<Rightarrow> 'a abs_state"
    and ev :: "analysis_event \<Rightarrow> 'a abs_state \<Rightarrow> 'a abs_state"
  assumes tf_sound_assign_for[intro]:
    "s \<in> \<lbrakk>\<sigma>\<rbrakk> \<Longrightarrow> s(x := aval a s) \<in> \<lbrakk>asn x a \<sigma>\<rbrakk>"
  assumes tf_sound_special_for[intro]:
    "s \<in> \<lbrakk>\<sigma>\<rbrakk> \<Longrightarrow> special_result sc s v \<Longrightarrow> s(x := v) \<in> \<lbrakk>sp sc x \<sigma>\<rbrakk>"
  assumes tf_sound_branch_for[intro]:
    "s \<in> \<lbrakk>\<sigma>\<rbrakk> \<Longrightarrow> truthy (aval b s) = pol \<Longrightarrow> s \<in> \<lbrakk>br b pol \<sigma>\<rbrakk>"
  assumes tf_sound_skip_for[intro]:
    "s \<in> \<lbrakk>\<sigma>\<rbrakk> \<Longrightarrow> s \<in> \<lbrakk>sk \<sigma>\<rbrakk>"
  assumes tf_sound_body_for[intro]:
    "s \<in> \<lbrakk>\<sigma>\<rbrakk> \<Longrightarrow> s \<in> \<lbrakk>bd p \<sigma>\<rbrakk>"
  assumes tf_sound_return_for[intro]:
    "s \<in> \<lbrakk>\<sigma>\<rbrakk> \<Longrightarrow>
       s(ret_var := (case e of None \<Rightarrow> s ret_var | Some a \<Rightarrow> aval a s))
         \<in> \<lbrakk>rt e p \<sigma>\<rbrakk>"
  assumes tf_sound_enter_entry_for[intro]:
    "s \<in> \<lbrakk>\<sigma>\<rbrakk> \<Longrightarrow>
       bind_formals (ci_formals ci) (map (\<lambda>e. aval e s) (ci_args ci)) (enter_state gs s)
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

text \<open>The contract is exactly \<^locale>\<open>sound_local_dg_spec\<close> at the fixed Base call
  boundary, so every specification built below inherits its soundness rather than
  re-deriving it.\<close>

sublocale sound_transfer_for \<subseteq> base: sound_local_dg_spec
  sk asn sp br bd rt "\<lambda>ci d. [(d, en ci d)]" ev "\<lambda>ci dc de. dc"
  "\<lambda>ci. combine\<^sup># gs (ci_dst ci)" gamma_state gs
proof (unfold_locales, goal_cases)
  case 1
  then show ?case by (rule gamma_state_mono)
next
  case 2
  then show ?case by (rule step_sound_for)
next
  case (3 s d ci)
  then show ?case
    by (auto simp: call_enter_CallEdge)
next
  case 4
  then show ?case by (simp add: combine_collect_sound)
qed

subsection \<open>The unlifted core\<close>

definition local_state_dg_spec_for ::
  "(vname \<Rightarrow> bool)
   \<Rightarrow> ('a::sound_domain abs_state \<Rightarrow> 'a abs_state)
   \<Rightarrow> (vname \<Rightarrow> exp \<Rightarrow> 'a abs_state \<Rightarrow> 'a abs_state)
   \<Rightarrow> (special_call \<Rightarrow> vname \<Rightarrow> 'a abs_state \<Rightarrow> 'a abs_state)
   \<Rightarrow> (exp \<Rightarrow> bool \<Rightarrow> 'a abs_state \<Rightarrow> 'a abs_state)
   \<Rightarrow> (pname \<Rightarrow> 'a abs_state \<Rightarrow> 'a abs_state)
   \<Rightarrow> (exp option \<Rightarrow> pname \<Rightarrow> 'a abs_state \<Rightarrow> 'a abs_state)
   \<Rightarrow> (call_info \<Rightarrow> 'a abs_state \<Rightarrow> 'a abs_state)
   \<Rightarrow> (analysis_event \<Rightarrow> 'a abs_state \<Rightarrow> 'a abs_state)
   \<Rightarrow> ('x,'k,unit,'a abs_state,'g::bounded_semilattice_sup_bot) dg_spec"
where
  "local_state_dg_spec_for gs sk asn sp br bd rt en ev = local_dg_spec
     sk asn sp br bd rt (\<lambda>ci d. [(d, en ci d)]) ev
     (\<lambda>ci dc de. dc) (\<lambda>ci. combine\<^sup># gs (ci_dst ci))"

declare local_state_dg_spec_for_def [code_unfold]

lemma dg_spec_step_local_state_for:
  "dg_spec_step (local_state_dg_spec_for gs sk asn sp br bd rt en ev) a
     = local_transfer (local_spec_step sk asn sp br bd rt ev a)"
  by (simp add: local_state_dg_spec_for_def)

theorem (in sound_transfer_for) local_state_dg_spec_for_core_sound:
  "sound_dg_spec_core (local_state_dg_spec_for gs sk asn sp br bd rt en ev) (\<lambda>d g. \<lbrakk>d\<rbrakk>) gs"
  unfolding local_state_dg_spec_for_def by (rule base.local_spec_sound)


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

definition local_state_dg_spec_for_lifted ::
  "(vname \<Rightarrow> bool)
   \<Rightarrow> ('a abs_state \<Rightarrow> bool)
   \<Rightarrow> ('a::sound_domain abs_state \<Rightarrow> 'a abs_state)
   \<Rightarrow> (vname \<Rightarrow> exp \<Rightarrow> 'a abs_state \<Rightarrow> 'a abs_state)
   \<Rightarrow> (special_call \<Rightarrow> vname \<Rightarrow> 'a abs_state \<Rightarrow> 'a abs_state)
   \<Rightarrow> (exp \<Rightarrow> bool \<Rightarrow> 'a abs_state \<Rightarrow> 'a abs_state)
   \<Rightarrow> (pname \<Rightarrow> 'a abs_state \<Rightarrow> 'a abs_state)
   \<Rightarrow> (exp option \<Rightarrow> pname \<Rightarrow> 'a abs_state \<Rightarrow> 'a abs_state)
   \<Rightarrow> (call_info \<Rightarrow> 'a abs_state \<Rightarrow> 'a abs_state)
   \<Rightarrow> (analysis_event \<Rightarrow> 'a abs_state \<Rightarrow> 'a abs_state)
   \<Rightarrow> ('x,'k,unit,'a abs_state lifted,'g::bounded_semilattice_sup_bot) dg_spec"
where
  "local_state_dg_spec_for_lifted gs empty_pred sk asn sp br bd rt en ev = local_dg_spec
     (transfer_lift empty_pred sk)
     (\<lambda>x e. transfer_lift empty_pred (asn x e))
     (\<lambda>sc x. transfer_lift empty_pred (sp sc x))
     (\<lambda>b pol. transfer_lift empty_pred (br b pol))
     (\<lambda>p. transfer_lift empty_pred (bd p))
     (\<lambda>e p. transfer_lift empty_pred (rt e p))
     (\<lambda>ci d. [(d, transfer_lift empty_pred (en ci) d)])
     (\<lambda>evt. transfer_lift empty_pred (ev evt))
     (\<lambda>ci dc de. dc)
     (\<lambda>ci dcM de. transfer_lift2 empty_pred (combine\<^sup># gs (ci_dst ci)) dcM de)"

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

lemma dg_spec_step_local_state_for_lifted:
  "dg_spec_step (local_state_dg_spec_for_lifted gs empty_pred sk asn sp br bd rt en ev) a
     = local_transfer (transfer_lift empty_pred (local_spec_step sk asn sp br bd rt ev a))"
  by (simp add: local_state_dg_spec_for_lifted_def local_spec_step_transfer_lift)

lemma dgs_enter_local_state_for_lifted:
  "enter\<^sup># (local_state_dg_spec_for_lifted gs empty_pred sk asn sp br bd rt en ev) ci
     = local_enter_transfer (\<lambda>d. [(d, transfer_lift empty_pred (en ci) d)])"
  by (simp add: local_state_dg_spec_for_lifted_def)

text \<open>The caller continuation and the env stage are both identities, so the
  whole return pipeline is the return assignment applied to the raw call-site
  value and the callee exit.\<close>

lemma dg_spec_combine_transfer_local_state_for_lifted:
  "dg_spec_combine_transfer (local_state_dg_spec_for_lifted gs empty_pred sk asn sp br bd rt en ev) ci
     = local_combine_transfer
         (\<lambda>dc de. transfer_lift2 empty_pred (combine\<^sup># gs (ci_dst ci)) dc de)"
  by (simp add: local_state_dg_spec_for_lifted_def)

subsection \<open>Packaging correspondence\<close>

subsection \<open>Soundness of the lifted construction\<close>

text \<open>
  The meaning of a Base-style equation never depends on the global slot:
  nothing in \<^const>\<open>local_state_dg_spec_for_lifted\<close> ever publishes to or reads
  from it, so \<open>gamma_dg_local_state\<close> ignores its global argument entirely and the
  \<^const>\<open>sound_local_dg_spec\<close> obligations are the transported pure facts.
\<close>

definition gamma_dg_local_state ::
  "'a::sound_domain abs_state lifted \<Rightarrow> 'g::bounded_semilattice_sup_bot \<Rightarrow> store set"
where
  "gamma_dg_local_state d g = gamma_state_lift d"

theorem (in sound_transfer_for) local_state_dg_spec_for_lifted_core_sound:
  assumes empty_pred_sound: "\<And>sigma. empty_pred sigma \<Longrightarrow> \<lbrakk>sigma\<rbrakk> = {}"
  shows "sound_dg_spec_core (local_state_dg_spec_for_lifted gs empty_pred sk asn sp br bd rt en ev)
           gamma_dg_local_state gs"
proof -
  have geq: "gamma_dg_local_state = (\<lambda>d g. gamma_state_lift d)"
    by (simp add: fun_eq_iff gamma_dg_local_state_def)
  show ?thesis
    unfolding local_state_dg_spec_for_lifted_def geq
  proof (rule sound_local_dg_spec.local_spec_sound, unfold_locales, goal_cases)
    case 1
    then show ?case by (meson gamma_lift_mono gamma_state_mono)
  next
    case (2 a d)
    show ?case
      by (simp add: local_spec_step_transfer_lift)
         (rule transfer_lift_sound_collect
            [OF step_sound_for edge_collect_empty_set empty_pred_sound])
  next
    case (3 s d ci)
    have "call_enter gs (CallEdge (ci_dst ci) (ci_formals ci) (ci_args ci)) s
            \<in> gamma_state_lift (transfer_lift empty_pred (en ci) d)"
    proof (rule transfer_lift_sound_mem
          [where h = "call_enter gs (CallEdge (ci_dst ci) (ci_formals ci) (ci_args ci))"])
      show "\<And>\<sigma>. s \<in> \<lbrakk>\<sigma>\<rbrakk> \<Longrightarrow>
          call_enter gs (CallEdge (ci_dst ci) (ci_formals ci) (ci_args ci)) s \<in> \<lbrakk>en ci \<sigma>\<rbrakk>"
        by (simp add: call_enter_CallEdge tf_sound_enter_entry_for)
      show "\<And>\<sigma>. empty_pred \<sigma> \<Longrightarrow> \<lbrakk>\<sigma>\<rbrakk> = {}" by (rule empty_pred_sound)
      show "s \<in> gamma_state_lift d" by (rule 3)
    qed
    with 3 show ?case by (auto simp: entry_pairs_cover_def)
  next
    case (4 s dc t de ci)
    show ?case
    proof (rule transfer_lift2_sound_mem[where h = "combine_collect gs (ci_dst ci)"])
      show "\<And>\<sigma>1 \<sigma>2. s \<in> \<lbrakk>\<sigma>1\<rbrakk> \<Longrightarrow> t \<in> \<lbrakk>\<sigma>2\<rbrakk> \<Longrightarrow>
          combine_collect gs (ci_dst ci) s t \<in> \<lbrakk>combine\<^sup># gs (ci_dst ci) \<sigma>1 \<sigma>2\<rbrakk>"
        by (rule combine_collect_sound)
      show "\<And>\<sigma>. empty_pred \<sigma> \<Longrightarrow> \<lbrakk>\<sigma>\<rbrakk> = {}" by (rule empty_pred_sound)
      show "s \<in> gamma_state_lift dc" by (rule 4(1))
      show "t \<in> gamma_state_lift de" by (rule 4(2))
    qed
  qed
qed


end

