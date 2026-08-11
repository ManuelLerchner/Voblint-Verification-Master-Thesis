theory Sign_Transfer
  imports Sign_Backward Voblint_Core.Constraint_System "Voblint_VIMP.VIMP_Globals"

begin

section \<open>Sign transfer functions\<close>

subsection \<open>Abstract assignment\<close>

definition assign_sign ::
    "vname => aexp => (vname => sign) => (vname => sign)"
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

subsection \<open>Abstract nondeterministic assignment\<close>

definition random_sign ::
    "vname => (vname => sign) => (vname => sign)"
where
  "random_sign x \<sigma> = \<sigma>(x := STop)"

lemma random_sign_sound:
  assumes gs: "s \<in> \<lbrakk>\<sigma>\<rbrakk>"
  shows "s(x := v) \<in> \<lbrakk>random_sign x \<sigma>\<rbrakk>"
  unfolding random_sign_def gamma_state_def
proof safe
  fix y
  from gs have V: "\<forall>z. s z \<in> gamma_sign (\<sigma> z)"
    using gamma_stateD[OF gs] by simp
  show "(s(x := v)) y \<in> gamma ((\<sigma>(x := STop)) y)"
  proof (cases "y = x")
    case True
    then show ?thesis by simp
  next
    case False
    with V show ?thesis by simp
  qed
qed

lemma random_sign_mono:
  "sigma1 \<le> sigma2 \<Longrightarrow> random_sign x sigma1 \<le> random_sign x sigma2"
  by (simp add: random_sign_def le_funD le_funI)

subsection \<open>Bundled transfer functions\<close>

lemma assign_sign_mono:
  "sigma1 \<le> sigma2 \<Longrightarrow> assign_sign x a sigma1 \<le> assign_sign x a sigma2"
  by (simp add: assign_sign_def aval_sign_mono le_funD le_funI)

lemma assume_sign_mono:
  "sigma1 \<le> sigma2 \<Longrightarrow> assume_sign b sigma1 \<le> assume_sign b sigma2"
  unfolding assume_sign_def
  by (rule bfilter_sign_mono)

lemma assume_not_sign_mono:
  "sigma1 \<le> sigma2 \<Longrightarrow> assume_not_sign b sigma1 \<le> assume_not_sign b sigma2"
  unfolding assume_not_sign_def
  by (rule bfilter_sign_mono)

subsection \<open>Classifier-parametric transfer\<close>

text \<open>
  Entry and combine are the only fields that consult a classifier (inside
  \<^const>\<open>enter_frame_D\<close> and \<^const>\<open>combine_env_abs\<close>); assignment and guard
  transfer never do, so the bundled transfer function is parametric in the
  classifier throughout (mirroring \<open>ivl_tf_for\<close> for the interval domain).
\<close>

definition enter_frame_sign_for ::
    "(vname => bool) => sign abs_state => sign abs_state" where
  "enter_frame_sign_for gs = enter_frame_D gs STop"

definition enter_sign_for ::
    "(vname => bool) => vname list => aexp list =>
      sign abs_state => sign abs_state" where
  "enter_sign_for gs = enter_D gs STop aval_sign"

lemma enter_frame_sign_for_sound:
  assumes gs: "s \<in> \<lbrakk>\<sigma>\<rbrakk>"
  shows "enter_state cls s \<in> \<lbrakk>enter_frame_sign_for cls \<sigma>\<rbrakk>"
  unfolding enter_frame_sign_for_def
proof (rule enter_frame_D_sound[OF gs])
  show "gamma STop = UNIV" by simp
qed

lemma enter_sign_for_sound:
  assumes gs: "s \<in> \<lbrakk>\<sigma>\<rbrakk>"
  shows "bind_formals xs (map (\<lambda>e. aval e s) es) (enter_state cls s)
           \<in> \<lbrakk>enter_sign_for cls xs es \<sigma>\<rbrakk>"
  unfolding enter_sign_for_def
proof (rule enter_D_sound[OF gs])
  show "gamma STop = UNIV" by simp
next
  have V: "\<forall>z. s z \<in> gamma_sign (\<sigma> z)"
    using gamma_stateD[OF gs] by simp
  show "list_all2 (\<lambda>v a. v \<in> gamma a)
          (map (\<lambda>e. aval e s) es) (map (\<lambda>e. aval_sign e \<sigma>) es)"
    using V by (simp add: list_all2_conv_all_nth aval_sign_sound)
qed

definition sign_tf_for :: "(vname => bool) => sign domain_transfer" where
  "sign_tf_for gs = (| tf_assign     = assign_sign,
                       tf_random     = random_sign,
                       tf_assume     = assume_sign,
                       tf_assume_not = assume_not_sign,
                       tf_enter      = enter_sign_for gs,
                       tf_combine    = combine_env\<^sup># gs |)"

lemma sign_is_sound_transfer_for: "sound_transfer_for gs (sign_tf_for gs)"
  unfolding sign_tf_for_def
  apply unfold_locales
  subgoal by (simp add: assign_sign_sound)
  subgoal by (simp add: random_sign_sound)
  subgoal by (simp add: assume_sign_sound)
  subgoal by (simp add: assume_not_sign_sound)
  subgoal by (simp add: enter_sign_for_sound)
  subgoal by (simp add: combine_env_sound)
  done

lemma enter_frame_sign_for_mono:
  assumes "s1 \<le> s2"
  shows "enter_frame_sign_for gs s1 \<le> enter_frame_sign_for gs s2"
  unfolding enter_frame_sign_for_def by (rule enter_frame_D_mono[OF assms])

lemma enter_sign_for_mono:
  assumes "s1 \<le> s2"
  shows "enter_sign_for gs xs es s1 \<le> enter_sign_for gs xs es s2"
  unfolding enter_sign_for_def
proof (rule enter_D_mono[OF assms])
  show "list_all2 (\<le>) (map (\<lambda>e. aval_sign e s1) es)
                       (map (\<lambda>e. aval_sign e s2) es)"
    using assms by (simp add: list_all2_conv_all_nth aval_sign_mono)
qed

lemma sign_tf_for_mono:
  "s1 \<le> s2 \<Longrightarrow> apply_tf (sign_tf_for gs) a s1 \<le> apply_tf (sign_tf_for gs) a s2"
  by (cases a)
     (auto simp: sign_tf_for_def assign_sign_mono random_sign_mono assume_sign_mono
                 assume_not_sign_mono enter_sign_for_mono split: option.splits)

end
