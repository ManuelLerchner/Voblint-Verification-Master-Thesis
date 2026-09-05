theory DG_Local_State_Spec
  imports DG_Spec_Sound Transfer_Algebra "Voblint_Domain.Nonrelational_Reachability"
begin

section \<open>What a whole-state analysis supplies, and when it is sound\<close>

text \<open>
  A Base-style analysis answers from one pointwise abstract state per program
  point and never touches a global: its transfers read the manager's local value,
  compute, and return, so the compiled equations carry no \<open>QueryG\<close> and no
  \<open>Side\<close>. Such an analysis supplies eight pure operations -- one per edge
  action, plus the callee entry -- and this theory turns them into a
  \<^type>\<open>dg_spec\<close> two ways: \<open>local_state_dg_spec_for\<close> on the raw
  states, and \<open>local_state_dg_spec_for_lifted\<close> on states carrying an
  explicit unreachable value, where a dead point collapses to \<^const>\<open>Bot\<close>
  before any transfer runs.

  \<open>sound_transfer_for\<close> is the contract those eight operations owe: every
  concrete transition the collecting semantics allows must land inside the
  concretization of what the corresponding operation computes. A domain discharges
  it once, by \<open>interpretation\<close>, and both constructions become sound
  specifications.

  The call boundary is fixed here rather than supplied. A call answers exactly one
  alternative, whose continuation is the caller value unchanged -- the pointwise
  carrier relates no two variables, so a call has nothing in it for a callee to
  invalidate. The environment stage passes that continuation through, and the
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
  the operation's own result. A domain proves the eight facts about its own
  functions and interprets this locale once; nothing below asks it for more.\<close>

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

text \<open>A specification dispatches its own \<open>EA_Check\<close> case through its own event
  operation, matching \<^const>\<open>local_spec_step\<close>'s own dispatch: this is the
  per-domain soundness bound each such instance needs at that dispatch point.

  Untagged, unlike \<^const>\<open>local_spec_step\<close>'s own rule above. Unfolding the
  dispatcher at \<open>EA_Check\<close> turns that rule into this one, so tagging both puts
  two routes to the same conclusion into the classical set --- and this one's
  conclusion mentions \<open>ev\<close> rather than the dispatcher, so it also fires on
  goals the dispatcher rule would leave alone.\<close>

lemma edge_collect_check_sound_for:
  "edge_collect (EA_Check c) \<lbrakk>\<sigma>\<rbrakk> \<subseteq> \<lbrakk>ev (Check_Event c) \<sigma>\<rbrakk>"
  by auto

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
    by (auto simp: call_enter_CallEdge intro: tf_sound_enter_entry_for)
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
  by (simp add: local_state_dg_spec_for_def dg_spec_step_local_dg_spec)

theorem (in sound_transfer_for) local_state_dg_spec_for_sound:
  "sound_dg_spec_core (local_state_dg_spec_for gs sk asn sp br bd rt en ev) (\<lambda>d g. \<lbrakk>d\<rbrakk>) gs"
  unfolding local_state_dg_spec_for_def by (rule base.local_spec_sound)


subsection \<open>Transporting soundness through the reachability lift\<close>

text \<open>
  A pure transfer's soundness fact carries over the \<^const>\<open>transfer_lift\<close>
  wrapper by one case split: \<^const>\<open>Bot\<close>'s concretization is empty, and a
  \<^const>\<open>normalize_lift\<close> collapse to \<^const>\<open>Bot\<close> only ever fires when
  \<open>empty_pred\<close> holds, whose concretization is empty by assumption.
\<close>

lemma transfer_lift_sound_collect:
  assumes step: "\<And>\<sigma>. C \<lbrakk>\<sigma>\<rbrakk> \<subseteq> \<lbrakk>f \<sigma>\<rbrakk>"
    and Cempty: "C {} = {}"
    and empty_pred_sound: "\<And>\<sigma>. empty_pred \<sigma> \<Longrightarrow> \<lbrakk>\<sigma>\<rbrakk> = {}"
  shows "C (gamma_state_lift d) \<subseteq> gamma_state_lift (transfer_lift empty_pred f d)"
proof (cases d)
  case Bot
  then show ?thesis by (simp add: Cempty)
next
  case (Lifted \<sigma>)
  have "C \<lbrakk>\<sigma>\<rbrakk> \<subseteq> \<lbrakk>f \<sigma>\<rbrakk>" by (rule step)
  then show ?thesis
    using Lifted empty_pred_sound[of "f \<sigma>"] by (auto simp: normalize_lift_def)
qed

lemma transfer_lift_sound_mem:
  assumes step: "\<And>\<sigma>. s \<in> \<lbrakk>\<sigma>\<rbrakk> \<Longrightarrow> h s \<in> \<lbrakk>f \<sigma>\<rbrakk>"
    and empty_pred_sound: "\<And>\<sigma>. empty_pred \<sigma> \<Longrightarrow> \<lbrakk>\<sigma>\<rbrakk> = {}"
    and s: "s \<in> gamma_state_lift d"
  shows "h s \<in> gamma_state_lift (transfer_lift empty_pred f d)"
proof (cases d)
  case Bot
  then show ?thesis using s by simp
next
  case (Lifted \<sigma>)
  with s have "s \<in> \<lbrakk>\<sigma>\<rbrakk>" by simp
  then have hs: "h s \<in> \<lbrakk>f \<sigma>\<rbrakk>" by (rule step)
  then have "\<not> empty_pred (f \<sigma>)" using empty_pred_sound by auto
  with Lifted hs show ?thesis by simp
qed

lemma transfer_lift2_sound_mem:
  assumes step: "\<And>\<sigma>1 \<sigma>2. s \<in> \<lbrakk>\<sigma>1\<rbrakk> \<Longrightarrow> t \<in> \<lbrakk>\<sigma>2\<rbrakk> \<Longrightarrow> h s t \<in> \<lbrakk>f \<sigma>1 \<sigma>2\<rbrakk>"
    and empty_pred_sound: "\<And>\<sigma>. empty_pred \<sigma> \<Longrightarrow> \<lbrakk>\<sigma>\<rbrakk> = {}"
    and s: "s \<in> gamma_state_lift d1"
    and t: "t \<in> gamma_state_lift d2"
  shows "h s t \<in> gamma_state_lift (transfer_lift2 empty_pred f d1 d2)"
proof (cases d1)
  case Bot
  then show ?thesis using s by simp
next
  case (Lifted \<sigma>1)
  show ?thesis
  proof (cases d2)
    case Bot
    then show ?thesis using t by simp
  next
    case (Lifted \<sigma>2)
    with \<open>d1 = Lifted \<sigma>1\<close> s t have "s \<in> \<lbrakk>\<sigma>1\<rbrakk>" "t \<in> \<lbrakk>\<sigma>2\<rbrakk>" by simp_all
    then have hst: "h s t \<in> \<lbrakk>f \<sigma>1 \<sigma>2\<rbrakk>" by (rule step)
    then have "\<not> empty_pred (f \<sigma>1 \<sigma>2)" using empty_pred_sound by auto
    with \<open>d1 = Lifted \<sigma>1\<close> Lifted hst show ?thesis by simp
  qed
qed

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
  by (simp add: local_state_dg_spec_for_lifted_def dg_spec_step_local_dg_spec
      local_spec_step_transfer_lift)

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
  by (simp add: local_state_dg_spec_for_lifted_def dg_spec_combine_transfer_local_dg_spec)

subsection \<open>Packaging correspondence\<close>

text \<open>
  Generic executable/mathematical commute for \<^const>\<open>transfer_lift\<close>/
  \<^const>\<open>transfer_lift2\<close> themselves, independent of any executable state
  representation: this is the one fact an executable Base mirror needs per
  field, proved once here rather than once per domain.
\<close>

lemma transfer_lift_commute:
  assumes commute: "\<And>s. phi (f s) = F (phi s)"
    and exact: "\<And>s. empty_pred s = empty_pred' (phi s)"
  shows "map_lift phi (transfer_lift empty_pred f d) = transfer_lift empty_pred' F (map_lift phi d)"
  by (cases d) (simp_all add: transfer_lift_def normalize_lift_def commute exact)

lemma transfer_lift2_commute:
  assumes commute: "\<And>s t. phi (f s t) = F (phi s) (phi t)"
    and exact: "\<And>s. empty_pred s = empty_pred' (phi s)"
  shows "map_lift phi (transfer_lift2 empty_pred f d1 d2) =
           transfer_lift2 empty_pred' F (map_lift phi d1) (map_lift phi d2)"
  by (cases d1; cases d2) (simp_all add: transfer_lift2_def normalize_lift_def commute exact)

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

theorem (in sound_transfer_for) local_state_dg_spec_sound:
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

