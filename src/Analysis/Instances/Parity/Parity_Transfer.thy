theory Parity_Transfer
  imports Parity_Domain Parity_Special "Voblint_Framework.DG_Local_State_Spec" "Voblint_VIMP.VIMP_Globals"
begin

section \<open>Parity transfer functions\<close>

subsection \<open>Abstract assignment\<close>

definition assign_parity ::
    "vname => exp => (vname => parity) => (vname => parity)" where
  "assign_parity x a \<sigma> = \<sigma>(x := aval_parity a \<sigma>)"

lemma assign_parity_sound:
  assumes gs: "s \<in> \<lbrakk>\<sigma>\<rbrakk>"
  shows "s(x := aval a s) \<in> \<lbrakk>assign_parity x a \<sigma>\<rbrakk>"
  unfolding assign_parity_def gamma_state_def
proof safe
  fix y
  from gs have V: "\<forall>z. s z \<in> gamma_parity (\<sigma> z)" unfolding gamma_state_def by simp
  show "(s(x := aval a s)) y \<in> gamma ((\<sigma>(x := aval_parity a \<sigma>)) y)"
  proof (cases "y = x")
    case True with V show ?thesis by (simp add: aval_parity_sound)
  next
    case False with V show ?thesis by simp
  qed
qed

text \<open>Nondeterministic and other special-call assignment (\<open>special_parity\<close>)
  lives in \<open>Parity_Special\<close>, reused below.\<close>

subsection \<open>Branch: parity does not refine guards, so the transfer is the identity\<close>

text \<open>
  No boolean guard in the language constrains the parity of a variable, so the
  sound and most precise parity branch keeps the incoming state unchanged --
  the identity is trivially polarity-independent, matching the framework's single
  polarity-parametrized branch operation directly (no separate assume/assume-not
  case, since both bodies coincide).
\<close>


definition branch_parity :: "exp => bool => (vname => parity) => (vname => parity)" where
  "branch_parity b pol \<sigma> = \<sigma>"

lemma branch_parity_sound: "s \<in> \<lbrakk>\<sigma>\<rbrakk> \<Longrightarrow> truthy (aval b s) = pol \<Longrightarrow> s \<in> \<lbrakk>branch_parity b pol \<sigma>\<rbrakk>"
  by (simp add: branch_parity_def)

subsection \<open>Bundled transfer functions\<close>

lemma assign_parity_mono:
  "sigma1 \<le> sigma2 \<Longrightarrow> assign_parity x a sigma1 \<le> assign_parity x a sigma2"
  by (simp add: assign_parity_def aval_parity_mono le_funD le_funI)

lemma branch_parity_mono:
  "sigma1 \<le> sigma2 \<Longrightarrow> branch_parity b pol sigma1 \<le> branch_parity b pol sigma2"
  by (simp add: branch_parity_def)

subsection \<open>Skip, body-entry, and return\<close>

text \<open>Parity has no lifecycle-specific abstract information: skip and body entry are
  the identity, and the return operation publishes the returned expression's value to
  \<^const>\<open>ret_var\<close>, which is where the collecting semantics reads it back.\<close>

definition skip_parity :: "(vname => parity) => (vname => parity)" where
  "skip_parity \<sigma> = \<sigma>"

definition body_parity :: "pname => (vname => parity) => (vname => parity)" where
  "body_parity p \<sigma> = \<sigma>"

definition return_parity ::
    "exp option => pname => (vname => parity) => (vname => parity)"
where
  "return_parity e p \<sigma> = (case e of None \<Rightarrow> \<sigma> | Some a \<Rightarrow> assign_parity ret_var a \<sigma>)"

text \<open>A check observes its condition but never refines the state (that is
  \<open>abstract_check_domain\<close>'s job): Parity has no notion of that observation
  either, so \<open>event_parity\<close> is the identity like \<open>skip_parity\<close>/\<open>body_parity\<close>.\<close>
definition event_parity :: "analysis_event => (vname => parity) => (vname => parity)" where
  "event_parity ev \<sigma> = \<sigma>"

lemma skip_parity_sound: "s \<in> \<lbrakk>\<sigma>\<rbrakk> \<Longrightarrow> s \<in> \<lbrakk>skip_parity \<sigma>\<rbrakk>"
  by (simp add: skip_parity_def)

lemma body_parity_sound: "s \<in> \<lbrakk>\<sigma>\<rbrakk> \<Longrightarrow> s \<in> \<lbrakk>body_parity p \<sigma>\<rbrakk>"
  by (simp add: body_parity_def)

lemma event_parity_sound: "s \<in> \<lbrakk>\<sigma>\<rbrakk> \<Longrightarrow> s \<in> \<lbrakk>event_parity ev \<sigma>\<rbrakk>"
  by (simp add: event_parity_def)

lemma return_parity_sound:
  assumes gs: "s \<in> \<lbrakk>\<sigma>\<rbrakk>"
  shows "s(ret_var := (case e of None \<Rightarrow> s ret_var | Some a \<Rightarrow> aval a s)) \<in> \<lbrakk>return_parity e p \<sigma>\<rbrakk>"
  using assign_parity_sound[OF gs] gs
  by (cases e) (simp_all add: return_parity_def)

lemma skip_parity_mono: "sigma1 \<le> sigma2 \<Longrightarrow> skip_parity sigma1 \<le> skip_parity sigma2"
  by (simp add: skip_parity_def)

lemma body_parity_mono: "sigma1 \<le> sigma2 \<Longrightarrow> body_parity p sigma1 \<le> body_parity p sigma2"
  by (simp add: body_parity_def)

lemma event_parity_mono: "sigma1 \<le> sigma2 \<Longrightarrow> event_parity ev sigma1 \<le> event_parity ev sigma2"
  by (simp add: event_parity_def)

lemma return_parity_mono:
  "sigma1 \<le> sigma2 \<Longrightarrow> return_parity e p sigma1 \<le> return_parity e p sigma2"
  by (cases e) (simp_all add: return_parity_def assign_parity_mono)

subsection \<open>Classifier-parametric transfer\<close>

text \<open>
  Entry and combine are the only fields that consult a classifier (inside
  \<^const>\<open>enter_frame\<close> and \<^const>\<open>combine_env\<close>); assignment and guard
  transfer never do, so the bundled transfer function is parametric in the
  classifier throughout (mirroring \<open>enter_sign_for\<close> for the sign domain).
\<close>

definition enter_frame_parity_for ::
    "(vname => bool) => parity abs_state => parity abs_state" where
  "enter_frame_parity_for gs = enter_frame gs PTop"

definition enter_parity_for ::
    "(vname => bool) => vname list => exp list =>
      parity abs_state => parity abs_state" where
  "enter_parity_for gs = enter_binding gs PTop aval_parity"

lemma enter_frame_parity_for_sound:
  assumes gs: "s \<in> \<lbrakk>\<sigma>\<rbrakk>"
  shows "enter_state cls s \<in> \<lbrakk>enter_frame_parity_for cls \<sigma>\<rbrakk>"
  unfolding enter_frame_parity_for_def
proof (rule enter_frame_sound[OF gs])
  show "gamma PTop = UNIV" by simp
qed

lemma enter_parity_for_sound:
  assumes gs: "s \<in> \<lbrakk>\<sigma>\<rbrakk>"
  shows "bind_formals xs (map (\<lambda>e. aval e s) es) (enter_state cls s)
           \<in> \<lbrakk>enter_parity_for cls xs es \<sigma>\<rbrakk>"
  unfolding enter_parity_for_def enter_binding_concrete[symmetric]
proof (rule enter_binding_sound[OF gs])
  show "gamma PTop = UNIV" by simp
next
  fix e
  have V: "\<forall>z. s z \<in> gamma_parity (\<sigma> z)"
    using gamma_stateD[OF gs] by simp
  show "aval e s \<in> gamma (aval_parity e \<sigma>)"
    using V by (simp add: aval_parity_sound)
qed

definition enter_parity_ci_for ::
    "(vname => bool) => call_info => parity abs_state => parity abs_state" where
  "enter_parity_ci_for gs ci = enter_parity_for gs (ci_formals ci) (ci_args ci)"

lemma enter_parity_ci_for_sound:
  assumes gs: "s \<in> \<lbrakk>\<sigma>\<rbrakk>"
  shows "bind_formals (ci_formals ci) (map (\<lambda>e. aval e s) (ci_args ci)) (enter_state cls s)
           \<in> \<lbrakk>enter_parity_ci_for cls ci \<sigma>\<rbrakk>"
  using enter_parity_for_sound[OF gs, of "ci_formals ci" "ci_args ci"]
  by (simp add: enter_parity_ci_for_def)

lemma parity_is_sound_transfer_for:
  "sound_transfer_for gs skip_parity assign_parity special_parity branch_parity
     body_parity return_parity (enter_parity_ci_for gs) event_parity"
  by unfold_locales
     (simp_all add: assign_parity_sound special_parity_sound branch_parity_sound
        skip_parity_sound body_parity_sound return_parity_sound enter_parity_ci_for_sound
        event_parity_sound)

definition parity_tf_abs :: "edge_action => parity abs_state => parity abs_state" where
  "parity_tf_abs = local_spec_step skip_parity assign_parity special_parity branch_parity
     return_parity event_parity"

lemma parity_tf_abs_simps [simp]:
  "parity_tf_abs EA_Nop = skip_parity"
  "parity_tf_abs (EA_Assign x e) = assign_parity x e"
  "parity_tf_abs (EA_Special sc y) = special_parity sc y"
  "parity_tf_abs (EA_Assume b) = branch_parity b True"
  "parity_tf_abs (EA_AssumeNot b) = branch_parity b False"
  "parity_tf_abs (EA_Ret eo p) = return_parity eo p"
  "parity_tf_abs (EA_Check c) = event_parity (Check_Event c)"
  by (simp_all add: parity_tf_abs_def)

lemma enter_frame_parity_for_mono:
  assumes "s1 \<le> s2"
  shows "enter_frame_parity_for gs s1 \<le> enter_frame_parity_for gs s2"
  unfolding enter_frame_parity_for_def by (rule enter_frame_mono[OF assms])

lemma enter_parity_for_mono:
  assumes "s1 \<le> s2"
  shows "enter_parity_for gs xs es s1 \<le> enter_parity_for gs xs es s2"
  unfolding enter_parity_for_def
proof (rule enter_binding_mono[OF assms])
  fix e
  show "aval_parity e s1 \<le> aval_parity e s2"
    using assms by (simp add: aval_parity_mono)
qed

lemma enter_parity_ci_for_mono:
  assumes "s1 \<le> s2"
  shows "enter_parity_ci_for gs ci s1 \<le> enter_parity_ci_for gs ci s2"
  using enter_parity_for_mono[OF assms, of gs "ci_formals ci" "ci_args ci"]
  by (simp add: enter_parity_ci_for_def)

lemma parity_tf_abs_mono:
  "s1 \<le> s2 \<Longrightarrow> parity_tf_abs a s1 \<le> parity_tf_abs a s2"
  by (cases a)
     (auto simp: assign_parity_mono special_parity_mono branch_parity_mono
                 skip_parity_mono body_parity_mono return_parity_mono
                 event_parity_mono)


end
