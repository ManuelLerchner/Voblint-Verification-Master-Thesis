theory Sign_Transfer
  imports Sign_Backward Constraint_System "Voblint_VIMP.VIMP_Globals"

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

subsection \<open>Bundled transfer functions\<close>

(* Procedure entry: keep globals, reset locals to Top (unknown), then bind the
   formals to the abstract values of the actuals evaluated in the caller.
   Generic via enter_frame_D/enter_D (Constraint_System.thy), parameterised
   by STop as the domain's fully-imprecise reset value. *)
definition enter_frame_sign :: "sign abs_state => sign abs_state" where
  "enter_frame_sign = enter_frame_D STop"

definition enter_sign ::
    "vname list => aexp list => sign abs_state => sign abs_state" where
  "enter_sign = enter_D STop aval_sign"

lemma enter_frame_sign_sound:
  assumes gs: "s \<in> \<lbrakk>\<sigma>\<rbrakk>"
  shows "enter_state s \<in> \<lbrakk>enter_frame_sign \<sigma>\<rbrakk>"
  unfolding enter_frame_sign_def
proof (rule enter_frame_D_sound[OF gs])
  show "gamma STop = UNIV" by simp
qed

lemma enter_sign_sound:
  assumes gs: "s \<in> \<lbrakk>\<sigma>\<rbrakk>"
  shows "bind_formals xs (map (\<lambda>e. aval e s) es) (enter_state s)
           \<in> \<lbrakk>enter_sign xs es \<sigma>\<rbrakk>"
  unfolding enter_sign_def
proof (rule enter_D_sound[OF gs])
  show "gamma STop = UNIV" by simp
next
  have V: "\<forall>z. s z \<in> gamma_sign (\<sigma> z)"
    using gamma_stateD[OF gs] by simp
  show "list_all2 (\<lambda>v a. v \<in> gamma a)
          (map (\<lambda>e. aval e s) es) (map (\<lambda>e. aval_sign e \<sigma>) es)"
    using V by (simp add: list_all2_conv_all_nth aval_sign_sound)
qed

lemma enter_frame_sign_mono:
  assumes "s1 \<le> s2"
  shows "enter_frame_sign s1 \<le> enter_frame_sign s2"
  unfolding enter_frame_sign_def by (rule enter_frame_D_mono[OF assms])

lemma enter_sign_mono:
  assumes "s1 \<le> s2"
  shows "enter_sign xs es s1 \<le> enter_sign xs es s2"
  unfolding enter_sign_def
proof (rule enter_D_mono[OF assms])
  show "list_all2 (\<le>) (map (\<lambda>e. aval_sign e s1) es)
                       (map (\<lambda>e. aval_sign e s2) es)"
    using assms by (simp add: list_all2_conv_all_nth aval_sign_mono)
qed

definition sign_tf :: "sign domain_transfer" where
  "sign_tf = (| tf_assign     = assign_sign,
                tf_assume     = assume_sign,
                tf_assume_not = assume_not_sign,
                tf_enter      = enter_sign,
                tf_combine    = combine_abs |)"

text \<open>
  The four transfer-function soundness facts for the sign domain, bundled once
  so example theories cite them instead of re-proving the same blocks.  These
  are the tf_sound_* premises of unified_post_fixpoint_sound / the
  per-solver soundness theorems.
\<close>
lemma sign_tf_sound_assign:
  "\<forall>x a \<sigma>. \<forall>st \<in> \<lbrakk>\<sigma>\<rbrakk>. st(x := aval a st) \<in> \<lbrakk>tf_assign sign_tf x a \<sigma>\<rbrakk>"
  unfolding sign_tf_def by (simp add: assign_sign_sound)

lemma sign_tf_sound_assume:
  "\<forall>b \<sigma>. \<forall>st \<in> \<lbrakk>\<sigma>\<rbrakk>. bval b st \<longrightarrow> st \<in> \<lbrakk>tf_assume sign_tf b \<sigma>\<rbrakk>"
  unfolding sign_tf_def by (simp add: assume_sign_sound)

lemma sign_tf_sound_assume_not:
  "\<forall>b \<sigma>. \<forall>st \<in> \<lbrakk>\<sigma>\<rbrakk>. \<not> bval b st \<longrightarrow> st \<in> \<lbrakk>tf_assume_not sign_tf b \<sigma>\<rbrakk>"
  unfolding sign_tf_def by (simp add: assume_not_sign_sound)

lemma sign_tf_sound_enter:
  "\<forall>xs (es::aexp list) \<sigma>. \<forall>st \<in> \<lbrakk>\<sigma>\<rbrakk>.
     bind_formals xs (map (\<lambda>e. aval e st) es) (enter_state st)
       \<in> \<lbrakk>tf_enter sign_tf xs es \<sigma>\<rbrakk>"
  unfolding sign_tf_def by (simp add: enter_sign_sound)

interpretation sign_sound_tf: sound_transfer sign_tf
proof (rule sound_transferI)
  show "\<And>x a \<sigma> s. s \<in> \<lbrakk>\<sigma>\<rbrakk> \<Longrightarrow> s(x := aval a s) \<in> \<lbrakk>tf_assign sign_tf x a \<sigma>\<rbrakk>"
    using sign_tf_sound_assign by blast
  show "\<And>b \<sigma> s. s \<in> \<lbrakk>\<sigma>\<rbrakk> \<Longrightarrow> bval b s \<Longrightarrow> s \<in> \<lbrakk>tf_assume sign_tf b \<sigma>\<rbrakk>"
    using sign_tf_sound_assume by blast
  show "\<And>b \<sigma> s. s \<in> \<lbrakk>\<sigma>\<rbrakk> \<Longrightarrow> \<not> bval b s \<Longrightarrow> s \<in> \<lbrakk>tf_assume_not sign_tf b \<sigma>\<rbrakk>"
    using sign_tf_sound_assume_not by blast
  show "\<And>xs es \<sigma> s. s \<in> \<lbrakk>\<sigma>\<rbrakk> \<Longrightarrow>
     bind_formals xs (map (\<lambda>e. aval e s) es) (enter_state s) \<in> \<lbrakk>tf_enter sign_tf xs es \<sigma>\<rbrakk>"
    using sign_tf_sound_enter by blast
  show "tf_combine sign_tf = combine_abs"
    unfolding sign_tf_def by simp
qed

lemma sign_is_sound_transfer: "sound_transfer sign_tf"
  by (rule sign_sound_tf.sound_transfer_axioms)

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

lemma sign_tf_mono:
  "s1 \<le> s2 \<Longrightarrow> apply_tf sign_tf a s1 \<le> apply_tf sign_tf a s2"
  by (cases a)
     (auto simp: sign_tf_def assign_sign_mono assume_sign_mono assume_not_sign_mono
                 enter_sign_mono split: option.splits)

end
