theory Sign_Transfer
  imports Sign_Backward Constraint_System "Voblint_IMP2.IMP2_Globals"

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
   formals to the abstract values of the actuals evaluated in the caller. *)
definition enter_frame_sign :: "sign abs_state => sign abs_state" where
  "enter_frame_sign \<sigma> = (\<lambda>x. if is_global x then \<sigma> x else STop)"

definition enter_sign ::
    "vname list => aexp list => sign abs_state => sign abs_state" where
  "enter_sign xs es \<sigma> =
     bind_formals_abs xs (map (\<lambda>e. aval_sign e \<sigma>) es) (enter_frame_sign \<sigma>)"

lemma enter_frame_sign_sound:
  assumes gs: "s \<in> \<lbrakk>\<sigma>\<rbrakk>"
  shows "enter_state s \<in> \<lbrakk>enter_frame_sign \<sigma>\<rbrakk>"
proof -
  from gs have V: "\<forall>z. s z \<in> gamma_sign (\<sigma> z)"
    using gamma_stateD[OF gs] by simp
  show ?thesis
    unfolding gamma_state_def enter_frame_sign_def
    by (intro CollectI allI; cases "is_global x";
        auto simp: enter_state_def V)
qed

lemma enter_sign_sound:
  assumes gs: "s \<in> \<lbrakk>\<sigma>\<rbrakk>"
  shows "bind_formals xs (map (\<lambda>e. aval e s) es) (enter_state s)
           \<in> \<lbrakk>enter_sign xs es \<sigma>\<rbrakk>"
proof -
  have base: "enter_state s \<in> \<lbrakk>enter_frame_sign \<sigma>\<rbrakk>"
    by (rule enter_frame_sign_sound[OF gs])
  have V: "\<forall>z. s z \<in> gamma_sign (\<sigma> z)"
    using gamma_stateD[OF gs] by simp
  have "list_all2 (\<lambda>v a. v \<in> gamma a)
          (map (\<lambda>e. aval e s) es) (map (\<lambda>e. aval_sign e \<sigma>) es)"
    using V by (simp add: list_all2_conv_all_nth aval_sign_sound)
  from bind_formals_abs_sound[OF base this]
  show ?thesis unfolding enter_sign_def .
qed

lemma enter_frame_sign_mono:
  assumes "s1 \<le> s2"
  shows "enter_frame_sign s1 \<le> enter_frame_sign s2"
proof (rule le_funI)
  fix x
  show "enter_frame_sign s1 x \<le> enter_frame_sign s2 x"
  proof (cases "is_global x")
    assume g: "is_global x"
    from assms have "s1 x \<le> s2 x" by (simp add: le_funD)
    thus ?thesis using g unfolding enter_frame_sign_def less_eq_sign_def by simp
  next
    assume "\<not> is_global x"
    thus ?thesis unfolding enter_frame_sign_def less_eq_sign_def
      by (simp add: sign_le_refl)
  qed
qed

lemma enter_sign_mono:
  assumes "s1 \<le> s2"
  shows "enter_sign xs es s1 \<le> enter_sign xs es s2"
  unfolding enter_sign_def
proof (rule bind_formals_abs_mono)
  show "enter_frame_sign s1 \<le> enter_frame_sign s2"
    by (rule enter_frame_sign_mono[OF assms])
  show "list_all2 (\<le>) (map (\<lambda>e. aval_sign e s1) es)
                       (map (\<lambda>e. aval_sign e s2) es)"
    using assms by (simp add: list_all2_conv_all_nth aval_sign_mono)
qed

definition combine_sign :: "sign abs_state \<Rightarrow> sign abs_state \<Rightarrow> sign abs_state" where
  "combine_sign = combine_abs"

lemma combine_sign_sound:
  assumes gs: "s \<in> \<lbrakk>sigma_c\<rbrakk>"
      and ge: "t \<in> \<lbrakk>sigma_e\<rbrakk>"
  shows "<s|t> \<in> \<lbrakk>combine_sign sigma_c sigma_e\<rbrakk>"
proof -
  from gs have Vc: "\<forall>z. s z \<in> gamma_sign (sigma_c z)"
    using gamma_stateD[OF gs] by simp
  from ge have Ve: "\<forall>z. t z \<in> gamma_sign (sigma_e z)"
    using gamma_stateD[OF ge] by simp
  show ?thesis
    unfolding gamma_state_def combine_sign_def combine_abs_def combine_states_def
    by (intro CollectI allI; cases "is_global x"; auto simp: Vc Ve)
qed

definition sign_tf :: "sign domain_transfer" where
  "sign_tf = (| tf_assign     = assign_sign,
                tf_assume     = assume_sign,
                tf_assume_not = assume_not_sign,
                tf_enter      = enter_sign,
                tf_combine    = combine_sign |)"

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

lemma sign_tf_sound_combine:
  "\<forall>\<sigma>c \<sigma>e. \<forall>s \<in> \<lbrakk>\<sigma>c\<rbrakk>. \<forall>t \<in> \<lbrakk>\<sigma>e\<rbrakk>. combine_states s t \<in> \<lbrakk>tf_combine sign_tf \<sigma>c \<sigma>e\<rbrakk>"
  unfolding sign_tf_def using combine_sign_sound by simp

interpretation sign_sound_tf: sound_transfer sign_tf
proof unfold_locales
  show "\<forall>x a \<sigma>. \<forall>s \<in> \<lbrakk>\<sigma>\<rbrakk>. s(x := aval a s) \<in> \<lbrakk>tf_assign sign_tf x a \<sigma>\<rbrakk>"
    by (rule sign_tf_sound_assign)
  show "\<forall>b \<sigma>. \<forall>s \<in> \<lbrakk>\<sigma>\<rbrakk>. bval b s \<longrightarrow> s \<in> \<lbrakk>tf_assume sign_tf b \<sigma>\<rbrakk>"
    by (rule sign_tf_sound_assume)
  show "\<forall>b \<sigma>. \<forall>s \<in> \<lbrakk>\<sigma>\<rbrakk>. \<not> bval b s \<longrightarrow> s \<in> \<lbrakk>tf_assume_not sign_tf b \<sigma>\<rbrakk>"
    by (rule sign_tf_sound_assume_not)
  show "\<forall>xs (es::aexp list) \<sigma>. \<forall>s \<in> \<lbrakk>\<sigma>\<rbrakk>.
     bind_formals xs (map (\<lambda>e. aval e s) es) (enter_state s)
       \<in> \<lbrakk>tf_enter sign_tf xs es \<sigma>\<rbrakk>"
    by (rule sign_tf_sound_enter)
  show "\<forall>\<sigma>c \<sigma>e. \<forall>s \<in> \<lbrakk>\<sigma>c\<rbrakk>. \<forall>t \<in> \<lbrakk>\<sigma>e\<rbrakk>. combine_states s t \<in> \<lbrakk>tf_combine sign_tf \<sigma>c \<sigma>e\<rbrakk>"
    by (rule sign_tf_sound_combine)
qed

lemma sign_is_sound_transfer: "sound_transfer sign_tf"
  by (unfold_locales)
     (fact sign_tf_sound_assign sign_tf_sound_assume sign_tf_sound_assume_not
           sign_tf_sound_enter sign_tf_sound_combine)+

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
