theory Parity_Transfer
  imports Parity_Domain Constraint_System "Voblint_VIMP.VIMP_Globals"
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

subsection \<open>Assume: parity does not refine guards, so the transfer is the identity\<close>

text \<open>
  No boolean guard in the language constrains the parity of a variable, so the
  sound and most precise parity assume keeps the incoming state unchanged.
\<close>

definition assume_parity :: "bexp => (vname => parity) => (vname => parity)" where
  "assume_parity b \<sigma> = \<sigma>"

definition assume_not_parity :: "bexp => (vname => parity) => (vname => parity)" where
  "assume_not_parity b \<sigma> = \<sigma>"

lemma assume_parity_sound: "s \<in> \<lbrakk>\<sigma>\<rbrakk> \<Longrightarrow> bval b s \<Longrightarrow> s \<in> \<lbrakk>assume_parity b \<sigma>\<rbrakk>"
  by (simp add: assume_parity_def)

lemma assume_not_parity_sound: "s \<in> \<lbrakk>\<sigma>\<rbrakk> \<Longrightarrow> \<not> bval b s \<Longrightarrow> s \<in> \<lbrakk>assume_not_parity b \<sigma>\<rbrakk>"
  by (simp add: assume_not_parity_def)

subsection \<open>Bundled transfer functions\<close>

(* Procedure entry: keep globals, reset locals to Top (unknown), then bind the
   formals to the abstract values of the actuals evaluated in the caller.
   Generic via enter_frame_D/enter_D (Constraint_System.thy), parameterised
   by PTop as the domain's fully-imprecise reset value. *)
definition enter_frame_parity :: "parity abs_state => parity abs_state" where
  "enter_frame_parity = enter_frame_D PTop"

definition enter_parity ::
    "vname list => aexp list => parity abs_state => parity abs_state" where
  "enter_parity = enter_D PTop aval_parity"

lemma enter_frame_parity_sound:
  assumes gs: "s \<in> \<lbrakk>\<sigma>\<rbrakk>"
  shows "enter_state s \<in> \<lbrakk>enter_frame_parity \<sigma>\<rbrakk>"
  unfolding enter_frame_parity_def
proof (rule enter_frame_D_sound[OF gs])
  show "gamma PTop = UNIV" by simp
qed

lemma enter_parity_sound:
  assumes gs: "s \<in> \<lbrakk>\<sigma>\<rbrakk>"
  shows "bind_formals xs (map (\<lambda>e. aval e s) es) (enter_state s)
           \<in> \<lbrakk>enter_parity xs es \<sigma>\<rbrakk>"
  unfolding enter_parity_def
proof (rule enter_D_sound[OF gs])
  show "gamma PTop = UNIV" by simp
next
  have V: "\<forall>z. s z \<in> gamma_parity (\<sigma> z)"
    using gamma_stateD[OF gs] by simp
  show "list_all2 (\<lambda>v a. v \<in> gamma a)
          (map (\<lambda>e. aval e s) es) (map (\<lambda>e. aval_parity e \<sigma>) es)"
    using V by (simp add: list_all2_conv_all_nth aval_parity_sound)
qed

lemma enter_frame_parity_mono:
  assumes "s1 \<le> s2"
  shows "enter_frame_parity s1 \<le> enter_frame_parity s2"
  unfolding enter_frame_parity_def by (rule enter_frame_D_mono[OF assms])

lemma enter_parity_mono:
  assumes "s1 \<le> s2"
  shows "enter_parity xs es s1 \<le> enter_parity xs es s2"
  unfolding enter_parity_def
proof (rule enter_D_mono[OF assms])
  show "list_all2 (\<le>) (map (\<lambda>e. aval_parity e s1) es)
                       (map (\<lambda>e. aval_parity e s2) es)"
    using assms by (simp add: list_all2_conv_all_nth aval_parity_mono)
qed

definition parity_tf :: "parity domain_transfer" where
  "parity_tf = (| tf_assign     = assign_parity,
                  tf_assume     = assume_parity,
                  tf_assume_not = assume_not_parity,
                  tf_enter      = enter_parity,
                  tf_combine    = combine_abs |)"

text \<open>
  The four transfer-function soundness facts for the parity domain, bundled
  once so example theories cite them instead of re-proving the same blocks.
  These are the tf_sound_* premises of unified_post_fixpoint_sound / the
  per-solver soundness theorems.
\<close>
lemma parity_tf_sound_assign:
  "\<forall>x a \<sigma>. \<forall>st \<in> \<lbrakk>\<sigma>\<rbrakk>. st(x := aval a st) \<in> \<lbrakk>tf_assign parity_tf x a \<sigma>\<rbrakk>"
  unfolding parity_tf_def by (simp add: assign_parity_sound)

lemma parity_tf_sound_assume:
  "\<forall>b \<sigma>. \<forall>st \<in> \<lbrakk>\<sigma>\<rbrakk>. bval b st \<longrightarrow> st \<in> \<lbrakk>tf_assume parity_tf b \<sigma>\<rbrakk>"
  unfolding parity_tf_def by (simp add: assume_parity_sound)

lemma parity_tf_sound_assume_not:
  "\<forall>b \<sigma>. \<forall>st \<in> \<lbrakk>\<sigma>\<rbrakk>. \<not> bval b st \<longrightarrow> st \<in> \<lbrakk>tf_assume_not parity_tf b \<sigma>\<rbrakk>"
  unfolding parity_tf_def by (simp add: assume_not_parity_sound)

lemma parity_tf_sound_enter:
  "\<forall>xs (es::aexp list) \<sigma>. \<forall>st \<in> \<lbrakk>\<sigma>\<rbrakk>.
     bind_formals xs (map (\<lambda>e. aval e st) es) (enter_state st) \<in> \<lbrakk>tf_enter parity_tf xs es \<sigma>\<rbrakk>"
  unfolding parity_tf_def by (simp add: enter_parity_sound)

interpretation parity_sound_tf: sound_transfer parity_tf
proof (rule sound_transferI)
  show "\<And>x a \<sigma> s. s \<in> \<lbrakk>\<sigma>\<rbrakk> \<Longrightarrow> s(x := aval a s) \<in> \<lbrakk>tf_assign parity_tf x a \<sigma>\<rbrakk>"
    using parity_tf_sound_assign by blast
  show "\<And>b \<sigma> s. s \<in> \<lbrakk>\<sigma>\<rbrakk> \<Longrightarrow> bval b s \<Longrightarrow> s \<in> \<lbrakk>tf_assume parity_tf b \<sigma>\<rbrakk>"
    using parity_tf_sound_assume by blast
  show "\<And>b \<sigma> s. s \<in> \<lbrakk>\<sigma>\<rbrakk> \<Longrightarrow> \<not> bval b s \<Longrightarrow> s \<in> \<lbrakk>tf_assume_not parity_tf b \<sigma>\<rbrakk>"
    using parity_tf_sound_assume_not by blast
  show "\<And>xs es \<sigma> s. s \<in> \<lbrakk>\<sigma>\<rbrakk> \<Longrightarrow>
     bind_formals xs (map (\<lambda>e. aval e s) es) (enter_state s) \<in> \<lbrakk>tf_enter parity_tf xs es \<sigma>\<rbrakk>"
    using parity_tf_sound_enter by blast
  show "tf_combine parity_tf = combine_abs"
    unfolding parity_tf_def by simp
qed

lemma parity_is_sound_transfer: "sound_transfer parity_tf"
  by (rule parity_sound_tf.sound_transfer_axioms)

lemma assign_parity_mono:
  "sigma1 \<le> sigma2 \<Longrightarrow> assign_parity x a sigma1 \<le> assign_parity x a sigma2"
  by (simp add: assign_parity_def aval_parity_mono le_funD le_funI)

lemma assume_parity_mono:
  "sigma1 \<le> sigma2 \<Longrightarrow> assume_parity b sigma1 \<le> assume_parity b sigma2"
  by (simp add: assume_parity_def)

lemma assume_not_parity_mono:
  "sigma1 \<le> sigma2 \<Longrightarrow> assume_not_parity b sigma1 \<le> assume_not_parity b sigma2"
  by (simp add: assume_not_parity_def)

lemma parity_tf_mono:
  "s1 \<le> s2 \<Longrightarrow> apply_tf parity_tf a s1 \<le> apply_tf parity_tf a s2"
  by (cases a)
     (auto simp: parity_tf_def assign_parity_mono assume_parity_mono assume_not_parity_mono
                 enter_parity_mono split: option.splits)

end
