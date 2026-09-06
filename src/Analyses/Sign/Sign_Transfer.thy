theory Sign_Transfer
  imports Sign_Backward Sign_Special "Voblint_Framework.DG_Local_State_Spec" "Voblint_VIMP.VIMP_Globals"

begin

section \<open>Sign transfer functions\<close>

subsection \<open>Abstract assignment\<close>

definition assign_sign ::
    "vname => exp => (vname => sign) => (vname => sign)"
where
  "assign_sign x a \<sigma> = \<sigma>(x := aval_sign a \<sigma>)"

lemma assign_sign_sound:
  assumes gs: "s \<in> \<lbrakk>\<sigma>\<rbrakk>"
  shows "s(x := aval a s) \<in> \<lbrakk>assign_sign x a \<sigma>\<rbrakk>"
  unfolding assign_sign_def gamma_state_def
proof safe
  fix y
  from gs have V: "\<forall>z. s z \<in> gamma_sign (\<sigma> z)"
    using gamma_stateD[OF gs] by simp
  show "(s(x := aval a s)) y \<in> gamma ((\<sigma>(x := aval_sign a \<sigma>)) y)"
  proof (cases "y = x")
    case True
    with V show ?thesis by (simp add: aval_sign_sound)
  next
    case False
    with V show ?thesis by simp
  qed
qed

text \<open>Nondeterministic and other special-call assignment (\<open>special_sign\<close>) lives
  in \<^theory>\<open>Voblint_Analysis_Sign.Sign_Special\<close>, reused below.\<close>
subsection \<open>Bundled transfer functions\<close>

lemma assign_sign_mono:
  "sigma1 \<le> sigma2 \<Longrightarrow> assign_sign x a sigma1 \<le> assign_sign x a sigma2"
  by (simp add: assign_sign_def aval_sign_mono le_funD le_funI)

subsection \<open>Skip, body-entry, and return\<close>

text \<open>Sign has no lifecycle-specific abstract information: skip and body entry are
  the identity, and the return operation publishes the returned expression's value to
  \<^const>\<open>ret_var\<close>, which is where the collecting semantics reads it back.\<close>


definition skip_sign :: "(vname => sign) => (vname => sign)" where
  "skip_sign \<sigma> = \<sigma>"

definition body_sign :: "pname => (vname => sign) => (vname => sign)" where
  "body_sign p \<sigma> = \<sigma>"

definition return_sign ::
    "exp option => pname => (vname => sign) => (vname => sign)"
where
  "return_sign e p \<sigma> = (case e of None \<Rightarrow> \<sigma> | Some a \<Rightarrow> assign_sign ret_var a \<sigma>)"

text \<open>A check observes its condition but never refines the state (that is
  \<open>abstract_check_domain\<close>'s job): Sign has no notion of that observation
  either, so \<open>event_sign\<close> is the identity like \<open>skip_sign\<close>/\<open>body_sign\<close>.\<close>
definition event_sign :: "analysis_event => (vname => sign) => (vname => sign)" where
  "event_sign ev \<sigma> = \<sigma>"

lemma skip_sign_sound: "s \<in> \<lbrakk>\<sigma>\<rbrakk> \<Longrightarrow> s \<in> \<lbrakk>skip_sign \<sigma>\<rbrakk>"
  by (simp add: skip_sign_def)

lemma body_sign_sound: "s \<in> \<lbrakk>\<sigma>\<rbrakk> \<Longrightarrow> s \<in> \<lbrakk>body_sign p \<sigma>\<rbrakk>"
  by (simp add: body_sign_def)

lemma event_sign_sound: "s \<in> \<lbrakk>\<sigma>\<rbrakk> \<Longrightarrow> s \<in> \<lbrakk>event_sign ev \<sigma>\<rbrakk>"
  by (simp add: event_sign_def)

lemma return_sign_sound:
  assumes gs: "s \<in> \<lbrakk>\<sigma>\<rbrakk>"
  shows "s(ret_var := (case e of None \<Rightarrow> s ret_var | Some a \<Rightarrow> aval a s)) \<in> \<lbrakk>return_sign e p \<sigma>\<rbrakk>"
  using assign_sign_sound[OF gs] gs
  by (cases e) (simp_all add: return_sign_def)

lemma skip_sign_mono: "sigma1 \<le> sigma2 \<Longrightarrow> skip_sign sigma1 \<le> skip_sign sigma2"
  by (simp add: skip_sign_def)

lemma body_sign_mono: "sigma1 \<le> sigma2 \<Longrightarrow> body_sign p sigma1 \<le> body_sign p sigma2"
  by (simp add: body_sign_def)

lemma event_sign_mono: "sigma1 \<le> sigma2 \<Longrightarrow> event_sign ev sigma1 \<le> event_sign ev sigma2"
  by (simp add: event_sign_def)

lemma return_sign_mono:
  "sigma1 \<le> sigma2 \<Longrightarrow> return_sign e p sigma1 \<le> return_sign e p sigma2"
  by (cases e) (simp_all add: return_sign_def assign_sign_mono)

subsection \<open>Classifier-parametric transfer\<close>

text \<open>
  Entry and combine are the only fields that consult a classifier (inside
  \<^const>\<open>enter_frame\<close> and \<^const>\<open>combine_env\<close>); assignment and guard
  transfer never do, so the bundled transfer function is parametric in the
  classifier throughout (mirroring \<open>enter_ivl_for\<close> for the interval domain).
\<close>

definition enter_frame_sign_for ::
    "(vname => bool) => sign abs_state => sign abs_state" where
  "enter_frame_sign_for gs = enter_frame gs STop"

definition enter_sign_for ::
    "(vname => bool) => vname list => exp list =>
      sign abs_state => sign abs_state" where
  "enter_sign_for gs = enter_binding gs STop aval_sign"

lemma enter_frame_sign_for_sound:
  assumes gs: "s \<in> \<lbrakk>\<sigma>\<rbrakk>"
  shows "enter_state cls s \<in> \<lbrakk>enter_frame_sign_for cls \<sigma>\<rbrakk>"
  unfolding enter_frame_sign_for_def
proof (rule enter_frame_sound[OF gs])
  show "gamma STop = UNIV" by simp
qed

lemma enter_sign_for_sound:
  assumes gs: "s \<in> \<lbrakk>\<sigma>\<rbrakk>"
  shows "bind_formals xs (map (\<lambda>e. aval e s) es) (enter_state cls s)
           \<in> \<lbrakk>enter_sign_for cls xs es \<sigma>\<rbrakk>"
  unfolding enter_sign_for_def enter_binding_concrete[symmetric]
proof (rule enter_binding_sound[OF gs])
  show "gamma STop = UNIV" by simp
next
  fix e
  have V: "\<forall>z. s z \<in> gamma_sign (\<sigma> z)"
    using gamma_stateD[OF gs] by simp
  show "aval e s \<in> gamma (aval_sign e \<sigma>)"
    using V by (simp add: aval_sign_sound)
qed

definition enter_sign_ci_for ::
    "(vname => bool) => call_info => sign abs_state => sign abs_state" where
  "enter_sign_ci_for gs ci = enter_sign_for gs (ci_formals ci) (ci_args ci)"

lemma enter_sign_ci_for_sound:
  assumes gs: "s \<in> \<lbrakk>\<sigma>\<rbrakk>"
  shows "bind_formals (ci_formals ci) (map (\<lambda>e. aval e s) (ci_args ci)) (enter_state cls s)
           \<in> \<lbrakk>enter_sign_ci_for cls ci \<sigma>\<rbrakk>"
  using enter_sign_for_sound[OF gs, of "ci_formals ci" "ci_args ci"]
  by (simp add: enter_sign_ci_for_def)


text \<open>Sign's eight transfer operations, discharging the framework's contract in one
  \<open>unfold_locales\<close>: the call boundary the contract fixes is the structural one, so
  only the per-edge operations and the callee entry are Sign's own.\<close>

lemma sign_is_sound_transfer_for:
  "sound_transfer_for gs skip_sign assign_sign special_sign branch_sign body_sign return_sign
     (enter_sign_ci_for gs) event_sign"
  by unfold_locales
     (simp_all add: assign_sign_sound special_sign_sound branch_sign_sound
        skip_sign_sound body_sign_sound return_sign_sound enter_sign_ci_for_sound
        event_sign_sound)

text \<open>The per-edge dispatcher, the abstract counterpart of \<open>sign_tf_st_for\<close>: the
  executable side dispatches on the action, so the readback equations relating the two
  are stated at this shape rather than one lemma per operation.\<close>

definition sign_tf_abs :: "edge_action => sign abs_state => sign abs_state" where
  "sign_tf_abs = local_spec_step skip_sign assign_sign special_sign branch_sign
     body_sign return_sign event_sign"

lemma sign_tf_abs_simps [simp]:
  "sign_tf_abs EA_Nop = skip_sign"
  "sign_tf_abs (EA_Assign x e) = assign_sign x e"
  "sign_tf_abs (EA_Special sc y) = special_sign sc y"
  "sign_tf_abs (EA_Assume b) = branch_sign b True"
  "sign_tf_abs (EA_AssumeNot b) = branch_sign b False"
  "sign_tf_abs (EA_Body p) = body_sign p"
  "sign_tf_abs (EA_Ret eo p) = return_sign eo p"
  "sign_tf_abs (EA_Check c) = event_sign (Check_Event c)"
  by (simp_all add: sign_tf_abs_def)

lemma enter_frame_sign_for_mono:
  assumes "s1 \<le> s2"
  shows "enter_frame_sign_for gs s1 \<le> enter_frame_sign_for gs s2"
  unfolding enter_frame_sign_for_def by (rule enter_frame_mono[OF assms])

lemma enter_sign_for_mono:
  assumes "s1 \<le> s2"
  shows "enter_sign_for gs xs es s1 \<le> enter_sign_for gs xs es s2"
  unfolding enter_sign_for_def
proof (rule enter_binding_mono[OF assms])
  fix e
  show "aval_sign e s1 \<le> aval_sign e s2"
    using assms by (simp add: aval_sign_mono)
qed

lemma enter_sign_ci_for_mono:
  assumes "s1 \<le> s2"
  shows "enter_sign_ci_for gs ci s1 \<le> enter_sign_ci_for gs ci s2"
  using enter_sign_for_mono[OF assms, of gs "ci_formals ci" "ci_args ci"]
  by (simp add: enter_sign_ci_for_def)

lemma sign_tf_abs_mono:
  "s1 \<le> s2 \<Longrightarrow> sign_tf_abs a s1 \<le> sign_tf_abs a s2"
  by (cases a)
     (auto simp: sign_tf_abs_def assign_sign_mono special_sign_mono branch_sign_mono
                 skip_sign_mono body_sign_mono return_sign_mono event_sign_mono)


end
