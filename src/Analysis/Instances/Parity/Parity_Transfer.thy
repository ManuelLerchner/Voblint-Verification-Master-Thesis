theory Parity_Transfer
  imports Parity_Domain Voblint_Core.Constraint_System "Voblint_VIMP.VIMP_Globals"
begin

section \<open>Parity transfer functions\<close>

subsection \<open>Abstract assignment\<close>

definition assign_parity ::
    "vname => aexp => (vname => parity) => (vname => parity)" where
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

subsection \<open>Abstract nondeterministic assignment\<close>

definition random_parity ::
    "vname => (vname => parity) => (vname => parity)" where
  "random_parity x \<sigma> = \<sigma>(x := PTop)"

lemma random_parity_sound:
  assumes gs: "s \<in> \<lbrakk>\<sigma>\<rbrakk>"
  shows "s(x := v) \<in> \<lbrakk>random_parity x \<sigma>\<rbrakk>"
  unfolding random_parity_def gamma_state_def
proof safe
  fix y
  from gs have V: "\<forall>z. s z \<in> gamma_parity (\<sigma> z)" unfolding gamma_state_def by simp
  show "(s(x := v)) y \<in> gamma ((\<sigma>(x := PTop)) y)"
  proof (cases "y = x")
    case True then show ?thesis by simp
  next
    case False with V show ?thesis by simp
  qed
qed

lemma random_parity_mono:
  "sigma1 \<le> sigma2 \<Longrightarrow> random_parity x sigma1 \<le> random_parity x sigma2"
  by (simp add: random_parity_def le_funD le_funI)

subsection \<open>Branch: parity does not refine guards, so the transfer is the identity\<close>

text \<open>
  No boolean guard in the language constrains the parity of a variable, so the
  sound and most precise parity branch keeps the incoming state unchanged --
  the identity is trivially polarity-independent, matching @{const tf_branch}'s
  shape directly (no separate assume/assume-not case, since both bodies coincide).
\<close>

definition branch_parity :: "bexp => bool => (vname => parity) => (vname => parity)" where
  "branch_parity b pol \<sigma> = \<sigma>"

lemma branch_parity_sound: "s \<in> \<lbrakk>\<sigma>\<rbrakk> \<Longrightarrow> bval b s = pol \<Longrightarrow> s \<in> \<lbrakk>branch_parity b pol \<sigma>\<rbrakk>"
  by (simp add: branch_parity_def)

subsection \<open>Bundled transfer functions\<close>

lemma assign_parity_mono:
  "sigma1 \<le> sigma2 \<Longrightarrow> assign_parity x a sigma1 \<le> assign_parity x a sigma2"
  by (simp add: assign_parity_def aval_parity_mono le_funD le_funI)

lemma branch_parity_mono:
  "sigma1 \<le> sigma2 \<Longrightarrow> branch_parity b pol sigma1 \<le> branch_parity b pol sigma2"
  by (simp add: branch_parity_def)

subsection \<open>Skip, body-entry, and return\<close>

text \<open>Parity has no lifecycle-specific abstract information: \<open>skip\<^sup>#\<close>/\<open>body\<^sup>#\<close> are
  the identity, and \<open>return\<^sup>#\<close> reuses the same \<open>EA_Ret\<close>-publishes-to-\<open>ret_var\<close>
  behaviour \<^const>\<open>apply_tf\<close> used to hardcode for every domain.\<close>

definition skip_parity :: "(vname => parity) => (vname => parity)" where
  "skip_parity \<sigma> = \<sigma>"

definition body_parity :: "pname => (vname => parity) => (vname => parity)" where
  "body_parity p \<sigma> = \<sigma>"

definition return_parity ::
    "aexp option => pname => (vname => parity) => (vname => parity)"
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
  \<^const>\<open>enter_frame_D\<close> and \<^const>\<open>combine_env_abs\<close>); assignment and guard
  transfer never do, so the bundled transfer function is parametric in the
  classifier throughout (mirroring \<open>sign_tf_for\<close> for the sign domain).
\<close>

definition enter_frame_parity_for ::
    "(vname => bool) => parity abs_state => parity abs_state" where
  "enter_frame_parity_for gs = enter_frame_D gs PTop"

definition enter_parity_for ::
    "(vname => bool) => vname list => aexp list =>
      parity abs_state => parity abs_state" where
  "enter_parity_for gs = enter_D gs PTop aval_parity"

lemma enter_frame_parity_for_sound:
  assumes gs: "s \<in> \<lbrakk>\<sigma>\<rbrakk>"
  shows "enter_state cls s \<in> \<lbrakk>enter_frame_parity_for cls \<sigma>\<rbrakk>"
  unfolding enter_frame_parity_for_def
proof (rule enter_frame_D_sound[OF gs])
  show "gamma PTop = UNIV" by simp
qed

lemma enter_parity_for_sound:
  assumes gs: "s \<in> \<lbrakk>\<sigma>\<rbrakk>"
  shows "bind_formals xs (map (\<lambda>e. aval e s) es) (enter_state cls s)
           \<in> \<lbrakk>enter_parity_for cls xs es \<sigma>\<rbrakk>"
  unfolding enter_parity_for_def
proof (rule enter_D_sound[OF gs])
  show "gamma PTop = UNIV" by simp
next
  have V: "\<forall>z. s z \<in> gamma_parity (\<sigma> z)"
    using gamma_stateD[OF gs] by simp
  show "list_all2 (\<lambda>v a. v \<in> gamma a)
          (map (\<lambda>e. aval e s) es) (map (\<lambda>e. aval_parity e \<sigma>) es)"
    using V by (simp add: list_all2_conv_all_nth aval_parity_sound)
qed

definition parity_tf_for :: "(vname => bool) => parity domain_transfer" where
  "parity_tf_for gs = (| tf_assign  = assign_parity,
                         tf_random  = random_parity,
                         tf_branch  = branch_parity,
                         tf_skip    = skip_parity,
                         tf_body    = body_parity,
                         tf_return  = return_parity,
                         tf_enter   = enter_parity_for gs,
                         tf_event   = event_parity,
                         tf_combine = combine_env\<^sup># gs |)"

lemma parity_is_sound_transfer_for: "sound_transfer_for gs (parity_tf_for gs)"
  unfolding parity_tf_for_def
  apply unfold_locales
  subgoal by (simp add: assign_parity_sound)
  subgoal by (simp add: random_parity_sound)
  subgoal by (simp add: branch_parity_sound)
  subgoal by (simp add: skip_parity_sound)
  subgoal by (simp add: body_parity_sound)
  subgoal by (simp add: return_parity_sound)
  subgoal by (simp add: enter_parity_for_sound)
  subgoal by (simp add: event_parity_sound)
  subgoal by (simp add: combine_env_sound)
  done

lemma enter_frame_parity_for_mono:
  assumes "s1 \<le> s2"
  shows "enter_frame_parity_for gs s1 \<le> enter_frame_parity_for gs s2"
  unfolding enter_frame_parity_for_def by (rule enter_frame_D_mono[OF assms])

lemma enter_parity_for_mono:
  assumes "s1 \<le> s2"
  shows "enter_parity_for gs xs es s1 \<le> enter_parity_for gs xs es s2"
  unfolding enter_parity_for_def
proof (rule enter_D_mono[OF assms])
  show "list_all2 (\<le>) (map (\<lambda>e. aval_parity e s1) es)
                       (map (\<lambda>e. aval_parity e s2) es)"
    using assms by (simp add: list_all2_conv_all_nth aval_parity_mono)
qed

lemma parity_tf_for_mono:
  "s1 \<le> s2 \<Longrightarrow> apply_tf (parity_tf_for gs) a s1 \<le> apply_tf (parity_tf_for gs) a s2"
  by (cases a)
     (auto simp: parity_tf_for_def assign_parity_mono random_parity_mono branch_parity_mono
                 skip_parity_mono body_parity_mono return_parity_mono enter_parity_for_mono
                 event_parity_mono)

end
