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
                         tf_enter   = enter_parity_for gs,
                         tf_combine = combine_env\<^sup># gs |)"

lemma parity_is_sound_transfer_for: "sound_transfer_for gs (parity_tf_for gs)"
  unfolding parity_tf_for_def
  apply unfold_locales
  subgoal by (simp add: assign_parity_sound)
  subgoal by (simp add: random_parity_sound)
  subgoal by (simp add: branch_parity_sound)
  subgoal by (simp add: enter_parity_for_sound)
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
                 enter_parity_for_mono split: option.splits)

end
