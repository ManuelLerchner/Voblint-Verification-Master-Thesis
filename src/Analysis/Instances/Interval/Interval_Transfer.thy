theory Interval_Transfer
  imports Interval_Backward Voblint_Core.Constraint_System "Voblint_VIMP.VIMP_Globals"
begin

section \<open>Interval transfer functions\<close>

subsection \<open>Abstract assume and assignment\<close>

text \<open>
  Both guards delegate to the generic @{text bfilter} proved sound in
  @{locale backward_domain}.  @{text "assume_ivl b \<sigma>"} filters for @{text "bval b"},
  @{text "assume_not_ivl b \<sigma>"} for @{text "\<not> bval b"}.
\<close>

definition assume_ivl :: "bexp => (vname => ivl) => (vname => ivl)" where
  "assume_ivl b \<sigma> = bfilter_ivl b True \<sigma>"

lemma assume_ivl_sound:
  "s \<in> \<lbrakk>\<sigma>\<rbrakk> \<Longrightarrow> bval b s \<Longrightarrow> s \<in> \<lbrakk>assume_ivl b \<sigma>\<rbrakk>"
  unfolding assume_ivl_def
  using ivl_backward_domain.bfilter_sound by simp

definition assume_not_ivl :: "bexp => (vname => ivl) => (vname => ivl)" where
  "assume_not_ivl b \<sigma> = bfilter_ivl b False \<sigma>"

lemma assume_not_ivl_sound:
  "s \<in> \<lbrakk>\<sigma>\<rbrakk> \<Longrightarrow> \<not> bval b s \<Longrightarrow> s \<in> \<lbrakk>assume_not_ivl b \<sigma>\<rbrakk>"
  unfolding assume_not_ivl_def
  using ivl_backward_domain.bfilter_sound by simp

definition assign_ivl ::
    "vname => aexp => (vname => ivl) => (vname => ivl)"
where
  "assign_ivl x a \<sigma> = \<sigma>(x := aval_ivl a \<sigma>)"

lemma assign_ivl_sound:
  "s \<in> \<lbrakk>\<sigma>\<rbrakk>
   \<Longrightarrow> s(x := aval a s) \<in> \<lbrakk>assign_ivl x a \<sigma>\<rbrakk>"
  unfolding gamma_state_def assign_ivl_def
  by (auto simp: aval_ivl_sound)

subsection \<open>Abstract nondeterministic assignment\<close>

definition random_ivl ::
    "vname => (vname => ivl) => (vname => ivl)"
where
  "random_ivl x \<sigma> = \<sigma>(x := ivl_top)"

lemma random_ivl_sound:
  "s \<in> \<lbrakk>\<sigma>\<rbrakk>
   \<Longrightarrow> s(x := v) \<in> \<lbrakk>random_ivl x \<sigma>\<rbrakk>"
  unfolding gamma_state_def random_ivl_def
  by (auto simp: gamma_ivl_top)

lemma random_ivl_mono:
  "sigma1 \<le> sigma2 \<Longrightarrow> random_ivl x sigma1 \<le> random_ivl x sigma2"
  by (simp add: random_ivl_def le_funD le_funI)

subsection \<open>Procedure entry and bundled transfer functions\<close>

text \<open>Procedure entry: keep globals, reset locals to the full interval, then bind
  the formals to the abstract values of the actuals evaluated in the caller.
  Generic via enter_frame_D/enter_D (Constraint_System.thy), parameterised by
  ivl_top as the domain's fully-imprecise reset value.\<close>
definition enter_frame_ivl :: "ivl abs_state \<Rightarrow> ivl abs_state" where
  "enter_frame_ivl = enter_frame_D is_global ivl_top"

definition enter_ivl ::
    "vname list \<Rightarrow> aexp list \<Rightarrow> ivl abs_state \<Rightarrow> ivl abs_state" where
  "enter_ivl = enter_D is_global ivl_top aval_ivl"

lemma enter_frame_ivl_sound:
  assumes gs: "s \<in> \<lbrakk>\<sigma>\<rbrakk>"
  shows "enter_state is_global s \<in> \<lbrakk>enter_frame_ivl \<sigma>\<rbrakk>"
  unfolding enter_frame_ivl_def
proof (rule enter_frame_D_sound[OF gs])
  show "gamma ivl_top = UNIV" by (simp add: gamma_ivl_top)
qed

lemma enter_ivl_sound:
  assumes gs: "s \<in> \<lbrakk>\<sigma>\<rbrakk>"
  shows "bind_formals xs (map (\<lambda>e. aval e s) es) (enter_state is_global s)
           \<in> \<lbrakk>enter_ivl xs es \<sigma>\<rbrakk>"
  unfolding enter_ivl_def
proof (rule enter_D_sound[OF gs])
  show "gamma ivl_top = UNIV" by (simp add: gamma_ivl_top)
next
  have V: "\<forall>x. s x \<in> gamma_ivl (\<sigma> x)"
    using gs unfolding gamma_state_def by simp
  show "list_all2 (\<lambda>v a. v \<in> gamma a)
          (map (\<lambda>e. aval e s) es) (map (\<lambda>e. aval_ivl e \<sigma>) es)"
    using V by (simp add: list_all2_conv_all_nth aval_ivl_sound)
qed

definition ivl_tf :: "ivl domain_transfer" where
  "ivl_tf = (| tf_assign     = assign_ivl,
               tf_random     = random_ivl,
               tf_assume     = assume_ivl,
               tf_assume_not = assume_not_ivl,
               tf_enter      = enter_ivl,
               tf_combine    = combine_abs is_global |)"

lemma ivl_tf_sound_assign:
  "\<forall>x a \<sigma>. \<forall>st \<in> \<lbrakk>\<sigma>\<rbrakk>. st(x := aval a st) \<in> \<lbrakk>tf_assign ivl_tf x a \<sigma>\<rbrakk>"
  unfolding ivl_tf_def by (simp add: assign_ivl_sound)

lemma ivl_tf_sound_random:
  "\<forall>x \<sigma>. \<forall>st \<in> \<lbrakk>\<sigma>\<rbrakk>. \<forall>v. st(x := v) \<in> \<lbrakk>tf_random ivl_tf x \<sigma>\<rbrakk>"
  unfolding ivl_tf_def by (simp add: random_ivl_sound)

lemma ivl_tf_sound_assume:
  "\<forall>b \<sigma>. \<forall>st \<in> \<lbrakk>\<sigma>\<rbrakk>. bval b st \<longrightarrow> st \<in> \<lbrakk>tf_assume ivl_tf b \<sigma>\<rbrakk>"
  unfolding ivl_tf_def by (simp add: assume_ivl_sound)

lemma ivl_tf_sound_assume_not:
  "\<forall>b \<sigma>. \<forall>st \<in> \<lbrakk>\<sigma>\<rbrakk>. \<not> bval b st \<longrightarrow> st \<in> \<lbrakk>tf_assume_not ivl_tf b \<sigma>\<rbrakk>"
  unfolding ivl_tf_def by (simp add: assume_not_ivl_sound)

lemma ivl_tf_sound_enter:
  "\<forall>xs (es::aexp list) \<sigma>. \<forall>st \<in> \<lbrakk>\<sigma>\<rbrakk>.
     bind_formals xs (map (\<lambda>e. aval e st) es) (enter_state is_global st)
       \<in> \<lbrakk>tf_enter ivl_tf xs es \<sigma>\<rbrakk>"
  unfolding ivl_tf_def by (simp add: enter_ivl_sound)

interpretation ivl_sound_tf: sound_transfer ivl_tf
proof (rule sound_transferI)
  show "\<And>x a \<sigma> s. s \<in> \<lbrakk>\<sigma>\<rbrakk> \<Longrightarrow> s(x := aval a s) \<in> \<lbrakk>tf_assign ivl_tf x a \<sigma>\<rbrakk>"
    using ivl_tf_sound_assign by blast
  show "\<And>x \<sigma> s v. s \<in> \<lbrakk>\<sigma>\<rbrakk> \<Longrightarrow> s(x := v) \<in> \<lbrakk>tf_random ivl_tf x \<sigma>\<rbrakk>"
    using ivl_tf_sound_random by blast
  show "\<And>b \<sigma> s. s \<in> \<lbrakk>\<sigma>\<rbrakk> \<Longrightarrow> bval b s \<Longrightarrow> s \<in> \<lbrakk>tf_assume ivl_tf b \<sigma>\<rbrakk>"
    using ivl_tf_sound_assume by blast
  show "\<And>b \<sigma> s. s \<in> \<lbrakk>\<sigma>\<rbrakk> \<Longrightarrow> \<not> bval b s \<Longrightarrow> s \<in> \<lbrakk>tf_assume_not ivl_tf b \<sigma>\<rbrakk>"
    using ivl_tf_sound_assume_not by blast
  show "\<And>xs es \<sigma> s. s \<in> \<lbrakk>\<sigma>\<rbrakk> \<Longrightarrow>
     bind_formals xs (map (\<lambda>e. aval e s) es) (enter_state is_global s)
       \<in> \<lbrakk>tf_enter ivl_tf xs es \<sigma>\<rbrakk>"
    using ivl_tf_sound_enter by blast
  show "tf_combine ivl_tf = combine_abs is_global"
    unfolding ivl_tf_def by simp
qed

lemma ivl_is_sound_transfer: "sound_transfer ivl_tf"
  by (rule ivl_sound_tf.sound_transfer_axioms)

subsection \<open>Classifier-parametric transfer\<close>

text \<open>
  \<^const>\<open>ivl_tf\<close> fixes the legacy \<^const>\<open>is_global\<close> classifier inside
  \<^const>\<open>enter_frame_D\<close> and \<^const>\<open>combine_abs\<close>.  Placement analyses split
  store components by a declaration-driven classifier instead, so entry and
  combine need a version parametric in that classifier.  Assignment and guard
  transfer never consult a classifier, so only the entry and combine fields
  change shape.
\<close>

definition enter_frame_ivl_for ::
    "(vname => bool) => ivl abs_state => ivl abs_state" where
  "enter_frame_ivl_for gs = enter_frame_D gs ivl_top"

definition enter_ivl_for ::
    "(vname => bool) => vname list => aexp list =>
      ivl abs_state => ivl abs_state" where
  "enter_ivl_for gs = enter_D gs ivl_top aval_ivl"

lemma enter_frame_ivl_for_sound:
  assumes gs: "s \<in> \<lbrakk>\<sigma>\<rbrakk>"
  shows "enter_state cls s \<in> \<lbrakk>enter_frame_ivl_for cls \<sigma>\<rbrakk>"
  unfolding enter_frame_ivl_for_def
proof (rule enter_frame_D_sound[OF gs])
  show "gamma ivl_top = UNIV" by (simp add: gamma_ivl_top)
qed

lemma enter_ivl_for_sound:
  assumes gs: "s \<in> \<lbrakk>\<sigma>\<rbrakk>"
  shows "bind_formals xs (map (\<lambda>e. aval e s) es) (enter_state cls s)
           \<in> \<lbrakk>enter_ivl_for cls xs es \<sigma>\<rbrakk>"
  unfolding enter_ivl_for_def
proof (rule enter_D_sound[OF gs])
  show "gamma ivl_top = UNIV" by (simp add: gamma_ivl_top)
next
  have V: "\<forall>x. s x \<in> gamma_ivl (\<sigma> x)"
    using gs unfolding gamma_state_def by simp
  show "list_all2 (\<lambda>v a. v \<in> gamma a)
          (map (\<lambda>e. aval e s) es) (map (\<lambda>e. aval_ivl e \<sigma>) es)"
    using V by (simp add: list_all2_conv_all_nth aval_ivl_sound)
qed

definition ivl_tf_for :: "(vname => bool) => ivl domain_transfer" where
  "ivl_tf_for gs = (| tf_assign     = assign_ivl,
                       tf_random     = random_ivl,
                       tf_assume     = assume_ivl,
                       tf_assume_not = assume_not_ivl,
                       tf_enter      = enter_ivl_for gs,
                       tf_combine    = combine_abs gs |)"

lemma ivl_is_sound_transfer_for: "sound_transfer_for gs (ivl_tf_for gs)"
  unfolding ivl_tf_for_def
  apply unfold_locales
  subgoal by (simp add: assign_ivl_sound)
  subgoal by (simp add: random_ivl_sound)
  subgoal by (simp add: assume_ivl_sound)
  subgoal by (simp add: assume_not_ivl_sound)
  subgoal by (simp add: enter_ivl_for_sound)
  subgoal by (simp add: combine_states_sound)
  done

text \<open>Conservative generalization: the classifier-fixed definitions are the
  \<^const>\<open>is_global\<close> instance of the classifier-parametric ones.\<close>

lemma enter_frame_ivl_for_is_global:
  "enter_frame_ivl_for is_global = enter_frame_ivl"
  unfolding enter_frame_ivl_for_def enter_frame_ivl_def by (rule refl)

lemma enter_ivl_for_is_global:
  "enter_ivl_for is_global = enter_ivl"
  unfolding enter_ivl_for_def enter_ivl_def by (rule refl)

lemma ivl_tf_for_is_global:
  "ivl_tf_for is_global = ivl_tf"
  unfolding ivl_tf_for_def ivl_tf_def enter_ivl_for_is_global by (rule refl)


lemma assume_ivl_mono:
  "sigma1 \<le> sigma2 \<Longrightarrow> assume_ivl b sigma1 \<le> assume_ivl b sigma2"
  unfolding assume_ivl_def
  by (rule bfilter_ivl_mono)

lemma assume_not_ivl_mono:
  "sigma1 \<le> sigma2 \<Longrightarrow> assume_not_ivl b sigma1 \<le> assume_not_ivl b sigma2"
  unfolding assume_not_ivl_def
  by (rule bfilter_ivl_mono)

lemma enter_frame_ivl_mono:
  assumes "s1 \<le> s2"
  shows "enter_frame_ivl s1 \<le> enter_frame_ivl s2"
  unfolding enter_frame_ivl_def by (rule enter_frame_D_mono[OF assms])

lemma enter_ivl_mono:
  assumes "s1 \<le> s2"
  shows "enter_ivl xs es s1 \<le> enter_ivl xs es s2"
  unfolding enter_ivl_def
proof (rule enter_D_mono[OF assms])
  show "list_all2 (\<le>) (map (\<lambda>e. aval_ivl e s1) es)
                       (map (\<lambda>e. aval_ivl e s2) es)"
    using assms by (simp add: list_all2_conv_all_nth aval_ivl_mono)
qed

lemma assign_ivl_mono:
  "sigma1 \<le> sigma2 \<Longrightarrow> assign_ivl x a sigma1 \<le> assign_ivl x a sigma2"
  by (simp add: assign_ivl_def aval_ivl_mono le_funD le_funI)

lemma ivl_tf_mono:
  "s1 \<le> s2 \<Longrightarrow> apply_tf ivl_tf a s1 \<le> apply_tf ivl_tf a s2"
  by (cases a)
     (auto simp: ivl_tf_def assign_ivl_mono random_ivl_mono assume_ivl_mono
                 assume_not_ivl_mono enter_ivl_mono split: option.splits)

text \<open>
  Reusable simp bundle for post-fixpoint proofs over the interval domain.
  Covers the core evaluation rules shared by all interval examples.
  Examples with multiplication also need @{thm [source] times_ivl_def},
  @{thm [source] ivl_times_core.simps}, @{thm [source] ivl_nonempty.simps};
  examples with assume edges also need @{thm [source] assume_ivl_def},
  @{thm [source] assume_not_ivl_def}, @{thm [source] ivl_backward_domain.bfilter.simps};
  examples with procedure calls also need @{thm [source] enter_ivl_def},
  @{thm [source] enter_frame_ivl_def}, @{thm [source] bind_formals_abs_def},
  @{thm [source] combine_abs_def}, @{thm [source] is_global_def}.
\<close>
lemmas ivl_eval_simps =
  ivl_tf_def assign_ivl_def
  aval_ivl.simps
  plus_ivl.simps plus_eint.simps
  less_eq_ivl_def le_fun_def

end
