theory Interval_Transfer
  imports Interval_Backward Constraint_System "Voblint_IMP2.IMP2_Globals"
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

subsection \<open>Procedure entry and bundled transfer functions\<close>

text \<open>Procedure entry: keep globals, reset locals to the full interval, then bind
  the formals to the abstract values of the actuals evaluated in the caller.\<close>
definition enter_frame_ivl :: "ivl abs_state \<Rightarrow> ivl abs_state" where
  "enter_frame_ivl \<sigma> =
     (\<lambda>x. if is_global x then \<sigma> x else Ivl MinInf PlusInf)"

definition enter_ivl ::
    "vname list \<Rightarrow> aexp list \<Rightarrow> ivl abs_state \<Rightarrow> ivl abs_state" where
  "enter_ivl xs es \<sigma> =
     bind_formals_abs xs (map (\<lambda>e. aval_ivl e \<sigma>) es) (enter_frame_ivl \<sigma>)"

lemma enter_frame_ivl_sound:
  assumes "s \<in> \<lbrakk>\<sigma>\<rbrakk>"
  shows "enter_state s \<in> \<lbrakk>enter_frame_ivl \<sigma>\<rbrakk>"
  using assms unfolding gamma_state_def enter_frame_ivl_def enter_state_def
  by (intro CollectI allI) auto

lemma enter_ivl_sound:
  assumes gs: "s \<in> \<lbrakk>\<sigma>\<rbrakk>"
  shows "bind_formals xs (map (\<lambda>e. aval e s) es) (enter_state s)
           \<in> \<lbrakk>enter_ivl xs es \<sigma>\<rbrakk>"
proof -
  have base: "enter_state s \<in> \<lbrakk>enter_frame_ivl \<sigma>\<rbrakk>"
    by (rule enter_frame_ivl_sound[OF gs])
  have V: "\<forall>x. s x \<in> gamma_ivl (\<sigma> x)"
    using gs unfolding gamma_state_def by simp
  have "list_all2 (\<lambda>v a. v \<in> gamma a)
          (map (\<lambda>e. aval e s) es) (map (\<lambda>e. aval_ivl e \<sigma>) es)"
    using V by (simp add: list_all2_conv_all_nth aval_ivl_sound)
  from bind_formals_abs_sound[OF base this]
  show ?thesis unfolding enter_ivl_def .
qed

definition ivl_tf :: "ivl domain_transfer" where
  "ivl_tf = (| tf_assign     = assign_ivl,
               tf_assume     = assume_ivl,
               tf_assume_not = assume_not_ivl,
               tf_enter      = enter_ivl,
               tf_combine    = combine_abs |)"

lemma ivl_tf_sound_assign:
  "\<forall>x a \<sigma>. \<forall>st \<in> \<lbrakk>\<sigma>\<rbrakk>. st(x := aval a st) \<in> \<lbrakk>tf_assign ivl_tf x a \<sigma>\<rbrakk>"
  unfolding ivl_tf_def by (simp add: assign_ivl_sound)

lemma ivl_tf_sound_assume:
  "\<forall>b \<sigma>. \<forall>st \<in> \<lbrakk>\<sigma>\<rbrakk>. bval b st \<longrightarrow> st \<in> \<lbrakk>tf_assume ivl_tf b \<sigma>\<rbrakk>"
  unfolding ivl_tf_def by (simp add: assume_ivl_sound)

lemma ivl_tf_sound_assume_not:
  "\<forall>b \<sigma>. \<forall>st \<in> \<lbrakk>\<sigma>\<rbrakk>. \<not> bval b st \<longrightarrow> st \<in> \<lbrakk>tf_assume_not ivl_tf b \<sigma>\<rbrakk>"
  unfolding ivl_tf_def by (simp add: assume_not_ivl_sound)

lemma ivl_tf_sound_enter:
  "\<forall>xs (es::aexp list) \<sigma>. \<forall>st \<in> \<lbrakk>\<sigma>\<rbrakk>.
     bind_formals xs (map (\<lambda>e. aval e st) es) (enter_state st)
       \<in> \<lbrakk>tf_enter ivl_tf xs es \<sigma>\<rbrakk>"
  unfolding ivl_tf_def by (simp add: enter_ivl_sound)

lemma ivl_tf_sound_combine:
  "\<forall>\<sigma>c \<sigma>e. \<forall>s \<in> \<lbrakk>\<sigma>c\<rbrakk>. \<forall>t \<in> \<lbrakk>\<sigma>e\<rbrakk>. combine_states s t \<in> \<lbrakk>tf_combine ivl_tf \<sigma>c \<sigma>e\<rbrakk>"
  unfolding ivl_tf_def by (simp add: combine_states_sound)

interpretation ivl_sound_tf: sound_transfer ivl_tf
proof unfold_locales
  show "\<forall>x a \<sigma>. \<forall>s \<in> \<lbrakk>\<sigma>\<rbrakk>. s(x := aval a s) \<in> \<lbrakk>tf_assign ivl_tf x a \<sigma>\<rbrakk>"
    by (rule ivl_tf_sound_assign)
  show "\<forall>b \<sigma>. \<forall>s \<in> \<lbrakk>\<sigma>\<rbrakk>. bval b s \<longrightarrow> s \<in> \<lbrakk>tf_assume ivl_tf b \<sigma>\<rbrakk>"
    by (rule ivl_tf_sound_assume)
  show "\<forall>b \<sigma>. \<forall>s \<in> \<lbrakk>\<sigma>\<rbrakk>. \<not> bval b s \<longrightarrow> s \<in> \<lbrakk>tf_assume_not ivl_tf b \<sigma>\<rbrakk>"
    by (rule ivl_tf_sound_assume_not)
  show "\<forall>xs (es::aexp list) \<sigma>. \<forall>s \<in> \<lbrakk>\<sigma>\<rbrakk>.
     bind_formals xs (map (\<lambda>e. aval e s) es) (enter_state s)
       \<in> \<lbrakk>tf_enter ivl_tf xs es \<sigma>\<rbrakk>"
    by (rule ivl_tf_sound_enter)
  show "\<forall>\<sigma>c \<sigma>e. \<forall>s \<in> \<lbrakk>\<sigma>c\<rbrakk>. \<forall>t \<in> \<lbrakk>\<sigma>e\<rbrakk>. combine_states s t \<in> \<lbrakk>tf_combine ivl_tf \<sigma>c \<sigma>e\<rbrakk>"
    by (rule ivl_tf_sound_combine)
qed

lemma ivl_is_sound_transfer: "sound_transfer ivl_tf"
  by (unfold_locales)
     (fact ivl_tf_sound_assign ivl_tf_sound_assume ivl_tf_sound_assume_not
           ivl_tf_sound_enter ivl_tf_sound_combine)+


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
proof (rule le_funI)
  fix x
  show "enter_frame_ivl s1 x \<le> enter_frame_ivl s2 x"
  proof (cases "is_global x")
    case True
    from assms have "s1 x \<le> s2 x" by (simp add: le_funD)
    with True show ?thesis unfolding enter_frame_ivl_def by simp
  next
    case False
    thus ?thesis unfolding enter_frame_ivl_def by simp
  qed
qed

lemma enter_ivl_mono:
  assumes "s1 \<le> s2"
  shows "enter_ivl xs es s1 \<le> enter_ivl xs es s2"
  unfolding enter_ivl_def
proof (rule bind_formals_abs_mono)
  show "enter_frame_ivl s1 \<le> enter_frame_ivl s2"
    by (rule enter_frame_ivl_mono[OF assms])
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
     (auto simp: ivl_tf_def assign_ivl_mono assume_ivl_mono assume_not_ivl_mono
                 enter_ivl_mono split: option.splits)

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
  aval_ivl.simps aval_ivl_hol.simps
  plus_ivl.simps plus_eint.simps
  less_eq_ivl_def le_fun_def

end
