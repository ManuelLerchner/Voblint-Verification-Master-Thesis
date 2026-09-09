theory Congruence_Transfer
  imports Congruence_Backward Congruence_Special
    "Voblint_Framework.DG_Local_State_Spec" "Voblint_VIMP.VIMP_Globals"
begin

section \<open>What each kind of edge does to a map from variables to residue classes\<close>

text \<open>
  One operation per edge the framework can hand a domain. An assignment writes
  the evaluated right-hand side; a guard runs Congruence's backward filter, so
  \<open>x + 1 == 3\<close> narrows \<open>x\<close> to a single integer rather than leaving it alone; a
  call binds the actuals into a fresh frame; a return publishes its expression
  to \<^const>\<open>ret_var\<close>. Skip, body entry and check observation change nothing.

  Together they discharge \<^locale>\<open>sound_transfer_for\<close>, the framework's contract:
  whatever concrete store the edge could produce is described by the abstract
  state the operation produces. \<open>congruence_tf_abs\<close> bundles the eight into the
  per-edge dispatcher the executable side is later shown to agree with.
\<close>

subsection \<open>Abstract assignment\<close>

definition assign_congruence ::
    "vname => exp => (vname => congruence) => (vname => congruence)"
where
  "assign_congruence x a \<sigma> = \<sigma>(x := aval_congruence a \<sigma>)"

lemma assign_congruence_sound:
  assumes gs: "s \<in> \<lbrakk>\<sigma>\<rbrakk>"
  shows "s(x := aval a s) \<in> \<lbrakk>assign_congruence x a \<sigma>\<rbrakk>"
  unfolding assign_congruence_def gamma_state_def
proof safe
  fix y
  from gs have V: "\<forall>z. s z \<in> gamma (\<sigma> z)" using gamma_stateD[OF gs] by blast
  show "(s(x := aval a s)) y \<in> gamma ((\<sigma>(x := aval_congruence a \<sigma>)) y)"
  proof (cases "y = x")
    case True
    with V show ?thesis using congruence_arith.aval_dom_sound by simp
  next
    case False
    with V show ?thesis by simp
  qed
qed

lemma assign_congruence_mono:
  "sigma1 \<le> sigma2 \<Longrightarrow> assign_congruence x a sigma1 \<le> assign_congruence x a sigma2"
  by (simp add: assign_congruence_def congruence_arith.aval_dom_mono le_funD le_funI)

subsection \<open>Guards, through the backward filter\<close>

text \<open>
  \<^const>\<open>branch_congruence\<close> is \<^locale>\<open>backward_domain\<close>'s own branch: a forward
  \<^const>\<open>congruence_tobool\<close> feasibility test ahead of \<^const>\<open>bfilter_congruence\<close>,
  matching Goblint's \<open>Base.branch\<close> structure. Both come from the interpretation
  in \<^theory>\<open>Voblint_Analysis_Congruence.Congruence_Backward\<close>, so nothing about
  modular arithmetic is restated here.
\<close>

lemma bfilter_congruence_sound:
  "s \<in> \<lbrakk>\<sigma>\<rbrakk> \<Longrightarrow> truthy (aval b s) = res \<Longrightarrow> s \<in> \<lbrakk>bfilter_congruence b res \<sigma>\<rbrakk>"
  using congruence_backward_domain.bfilter_sound by simp

lemma branch_congruence_sound:
  "s \<in> \<lbrakk>\<sigma>\<rbrakk> \<Longrightarrow> truthy (aval b s) = res \<Longrightarrow> s \<in> \<lbrakk>branch_congruence b res \<sigma>\<rbrakk>"
  using congruence_backward_domain.branch_sound by simp

lemma branch_congruence_mono:
  "sigma1 \<le> sigma2 \<Longrightarrow> branch_congruence b res sigma1 \<le> branch_congruence b res sigma2"
  using congruence_backward_domain.branch_mono by (simp add: branch_congruence_def)

subsection \<open>Skip, body-entry, and return\<close>

text \<open>Congruence has no lifecycle-specific abstract information: skip and body entry
  are the identity, and the return operation publishes the returned expression's value
  to \<^const>\<open>ret_var\<close>, which is where the collecting semantics reads it back.\<close>

definition skip_congruence :: "(vname => congruence) => (vname => congruence)" where
  "skip_congruence \<sigma> = \<sigma>"

definition body_congruence :: "pname => (vname => congruence) => (vname => congruence)" where
  "body_congruence p \<sigma> = \<sigma>"

definition return_congruence ::
    "exp option => pname => (vname => congruence) => (vname => congruence)"
where
  "return_congruence e p \<sigma> =
     (case e of None \<Rightarrow> \<sigma> | Some a \<Rightarrow> assign_congruence ret_var a \<sigma>)"

text \<open>A check observes its condition but never refines the state (that is
  \<open>abstract_check_domain\<close>'s job), so \<open>event_congruence\<close> is the identity like
  \<open>skip_congruence\<close>/\<open>body_congruence\<close>.\<close>

definition event_congruence ::
    "analysis_event => (vname => congruence) => (vname => congruence)" where
  "event_congruence ev \<sigma> = \<sigma>"

lemma skip_congruence_sound: "s \<in> \<lbrakk>\<sigma>\<rbrakk> \<Longrightarrow> s \<in> \<lbrakk>skip_congruence \<sigma>\<rbrakk>"
  by (simp add: skip_congruence_def)

lemma body_congruence_sound: "s \<in> \<lbrakk>\<sigma>\<rbrakk> \<Longrightarrow> s \<in> \<lbrakk>body_congruence p \<sigma>\<rbrakk>"
  by (simp add: body_congruence_def)

lemma event_congruence_sound: "s \<in> \<lbrakk>\<sigma>\<rbrakk> \<Longrightarrow> s \<in> \<lbrakk>event_congruence ev \<sigma>\<rbrakk>"
  by (simp add: event_congruence_def)

lemma return_congruence_sound:
  assumes gs: "s \<in> \<lbrakk>\<sigma>\<rbrakk>"
  shows "s(ret_var := (case e of None \<Rightarrow> s ret_var | Some a \<Rightarrow> aval a s))
           \<in> \<lbrakk>return_congruence e p \<sigma>\<rbrakk>"
  using assign_congruence_sound[OF gs] gs
  by (cases e) (simp_all add: return_congruence_def)

lemma skip_congruence_mono:
  "sigma1 \<le> sigma2 \<Longrightarrow> skip_congruence sigma1 \<le> skip_congruence sigma2"
  by (simp add: skip_congruence_def)

lemma body_congruence_mono:
  "sigma1 \<le> sigma2 \<Longrightarrow> body_congruence p sigma1 \<le> body_congruence p sigma2"
  by (simp add: body_congruence_def)

lemma event_congruence_mono:
  "sigma1 \<le> sigma2 \<Longrightarrow> event_congruence ev sigma1 \<le> event_congruence ev sigma2"
  by (simp add: event_congruence_def)

lemma return_congruence_mono:
  "sigma1 \<le> sigma2 \<Longrightarrow> return_congruence e p sigma1 \<le> return_congruence e p sigma2"
  by (cases e) (simp_all add: return_congruence_def assign_congruence_mono)

subsection \<open>Classifier-parametric transfer\<close>

text \<open>
  Entry and combine are the only fields that consult a classifier (inside
  \<^const>\<open>enter_frame\<close> and \<^const>\<open>combine_env\<close>); assignment and guard
  transfer never do, so the bundled transfer function is parametric in the
  classifier throughout (mirroring \<open>enter_sign_for\<close> for the sign domain).
\<close>

definition enter_frame_congruence_for ::
    "(vname => bool) => congruence abs_state => congruence abs_state" where
  "enter_frame_congruence_for gs = enter_frame gs top"

definition enter_congruence_for ::
    "(vname => bool) => vname list => exp list =>
      congruence abs_state => congruence abs_state" where
  "enter_congruence_for gs = enter_binding gs top aval_congruence"

lemma enter_frame_congruence_for_sound:
  assumes gs: "s \<in> \<lbrakk>\<sigma>\<rbrakk>"
  shows "enter_state cls s \<in> \<lbrakk>enter_frame_congruence_for cls \<sigma>\<rbrakk>"
  unfolding enter_frame_congruence_for_def
proof (rule enter_frame_sound[OF gs])
  show "gamma (top :: congruence) = UNIV" by simp
qed

lemma enter_congruence_for_sound:
  assumes gs: "s \<in> \<lbrakk>\<sigma>\<rbrakk>"
  shows "bind_formals xs (map (\<lambda>e. aval e s) es) (enter_state cls s)
           \<in> \<lbrakk>enter_congruence_for cls xs es \<sigma>\<rbrakk>"
  unfolding enter_congruence_for_def enter_binding_concrete[symmetric]
proof (rule enter_binding_sound[OF gs])
  show "gamma (top :: congruence) = UNIV" by simp
next
  fix e
  have V: "\<forall>z. s z \<in> gamma (\<sigma> z)" using gamma_stateD[OF gs] by blast
  show "aval e s \<in> gamma (aval_congruence e \<sigma>)"
    by (rule congruence_arith.aval_dom_sound[OF V])
qed

definition enter_congruence_ci_for ::
    "(vname => bool) => call_info => congruence abs_state => congruence abs_state" where
  "enter_congruence_ci_for gs ci = enter_congruence_for gs (ci_formals ci) (ci_args ci)"

lemma enter_congruence_ci_for_sound:
  assumes gs: "s \<in> \<lbrakk>\<sigma>\<rbrakk>"
  shows "bind_formals (ci_formals ci) (map (\<lambda>e. aval e s) (ci_args ci)) (enter_state cls s)
           \<in> \<lbrakk>enter_congruence_ci_for cls ci \<sigma>\<rbrakk>"
  using enter_congruence_for_sound[OF gs, of "ci_formals ci" "ci_args ci"]
  by (simp add: enter_congruence_ci_for_def)

text \<open>Congruence's eight transfer operations, discharging the framework's contract in
  one \<open>unfold_locales\<close>: the call boundary the contract fixes is the structural one, so
  only the per-edge operations and the callee entry are Congruence's own.\<close>

lemma congruence_is_sound_transfer_for:
  "sound_transfer_for gs skip_congruence assign_congruence special_congruence
     branch_congruence body_congruence return_congruence (enter_congruence_ci_for gs)
     event_congruence"
  by unfold_locales
     (simp_all add: assign_congruence_sound special_congruence_sound branch_congruence_sound
        skip_congruence_sound body_congruence_sound return_congruence_sound
        enter_congruence_ci_for_sound event_congruence_sound)

text \<open>The per-edge dispatcher, the abstract counterpart of \<open>congruence_tf_st_for\<close>: the
  executable side dispatches on the action, so the readback equations relating the two
  are stated at this shape rather than one lemma per operation.\<close>

definition congruence_tf_abs ::
    "edge_action => congruence abs_state => congruence abs_state" where
  "congruence_tf_abs = local_spec_step skip_congruence assign_congruence special_congruence
     branch_congruence body_congruence return_congruence event_congruence"

lemma congruence_tf_abs_simps [simp]:
  "congruence_tf_abs EA_Nop = skip_congruence"
  "congruence_tf_abs (EA_Assign x e) = assign_congruence x e"
  "congruence_tf_abs (EA_Special sc y) = special_congruence sc y"
  "congruence_tf_abs (EA_Assume b) = branch_congruence b True"
  "congruence_tf_abs (EA_AssumeNot b) = branch_congruence b False"
  "congruence_tf_abs (EA_Body p) = body_congruence p"
  "congruence_tf_abs (EA_Ret eo p) = return_congruence eo p"
  "congruence_tf_abs (EA_Check c) = event_congruence (Check_Event c)"
  by (simp_all add: congruence_tf_abs_def)

lemma enter_frame_congruence_for_mono:
  assumes "s1 \<le> s2"
  shows "enter_frame_congruence_for gs s1 \<le> enter_frame_congruence_for gs s2"
  unfolding enter_frame_congruence_for_def by (rule enter_frame_mono[OF assms])

lemma enter_congruence_for_mono:
  assumes "s1 \<le> s2"
  shows "enter_congruence_for gs xs es s1 \<le> enter_congruence_for gs xs es s2"
  unfolding enter_congruence_for_def
proof (rule enter_binding_mono[OF assms])
  fix e
  show "aval_congruence e s1 \<le> aval_congruence e s2"
    using assms by (rule congruence_arith.aval_dom_mono)
qed

lemma enter_congruence_ci_for_mono:
  assumes "s1 \<le> s2"
  shows "enter_congruence_ci_for gs ci s1 \<le> enter_congruence_ci_for gs ci s2"
  using enter_congruence_for_mono[OF assms, of gs "ci_formals ci" "ci_args ci"]
  by (simp add: enter_congruence_ci_for_def)

lemma congruence_tf_abs_mono:
  "s1 \<le> s2 \<Longrightarrow> congruence_tf_abs a s1 \<le> congruence_tf_abs a s2"
  by (cases a)
     (auto simp: congruence_tf_abs_def assign_congruence_mono special_congruence_mono
                 branch_congruence_mono skip_congruence_mono body_congruence_mono
                 return_congruence_mono event_congruence_mono)

end
