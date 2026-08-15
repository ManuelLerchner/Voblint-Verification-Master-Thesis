theory Interval_Transfer
  imports Interval_Backward Interval_Special Voblint_Core.Constraint_System
    "Voblint_VIMP.VIMP_Globals"
begin

section \<open>Interval transfer functions\<close>

subsection \<open>Abstract branch and assignment\<close>

text \<open>
  Guard refinement delegates to the generic @{text bfilter} proved sound in
  @{locale backward_domain}. @{const bfilter_ivl} narrows on the branch selected
  by its boolean polarity argument (@{text True} for @{text "bval b"}, @{text False}
  for @{text "\<not> bval b"}) -- this is @{text ivl_tf_for}'s @{text tf_branch} instance
  directly, matching Goblint's single polarity-parametrized @{text Spec.branch}.
\<close>

lemma bfilter_ivl_sound:
  "s \<in> \<lbrakk>\<sigma>\<rbrakk> \<Longrightarrow> bval b s = res \<Longrightarrow> s \<in> \<lbrakk>bfilter_ivl b res \<sigma>\<rbrakk>"
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

text \<open>Nondeterministic and other special-call assignment (\<open>special_ivl\<close>) lives
  in \<open>Interval_Special\<close>, reused below.\<close>

lemma assign_ivl_mono:
  "sigma1 \<le> sigma2 \<Longrightarrow> assign_ivl x a sigma1 \<le> assign_ivl x a sigma2"
  by (simp add: assign_ivl_def aval_ivl_mono le_funD le_funI)

subsection \<open>Skip, body-entry, and return\<close>

text \<open>Interval has no lifecycle-specific abstract information: \<open>skip\<^sup>#\<close>/\<open>body\<^sup>#\<close>
  are the identity, and \<open>return\<^sup>#\<close> reuses the same \<open>EA_Ret\<close>-publishes-to-\<open>ret_var\<close>
  behaviour \<^const>\<open>apply_tf\<close> used to hardcode for every domain.\<close>

definition skip_ivl :: "(vname => ivl) => (vname => ivl)" where
  "skip_ivl \<sigma> = \<sigma>"

definition body_ivl :: "pname => (vname => ivl) => (vname => ivl)" where
  "body_ivl p \<sigma> = \<sigma>"

definition return_ivl ::
    "aexp option => pname => (vname => ivl) => (vname => ivl)"
where
  "return_ivl e p \<sigma> = (case e of None \<Rightarrow> \<sigma> | Some a \<Rightarrow> assign_ivl ret_var a \<sigma>)"

text \<open>A check observes its condition but never refines the state (that is
  \<open>abstract_check_domain\<close>'s job): Interval has no notion of that observation
  either, so \<open>event_ivl\<close> is the identity like \<open>skip_ivl\<close>/\<open>body_ivl\<close>.\<close>
definition event_ivl :: "analysis_event => (vname => ivl) => (vname => ivl)" where
  "event_ivl ev \<sigma> = \<sigma>"

lemma skip_ivl_sound: "s \<in> \<lbrakk>\<sigma>\<rbrakk> \<Longrightarrow> s \<in> \<lbrakk>skip_ivl \<sigma>\<rbrakk>"
  by (simp add: skip_ivl_def)

lemma body_ivl_sound: "s \<in> \<lbrakk>\<sigma>\<rbrakk> \<Longrightarrow> s \<in> \<lbrakk>body_ivl p \<sigma>\<rbrakk>"
  by (simp add: body_ivl_def)

lemma event_ivl_sound: "s \<in> \<lbrakk>\<sigma>\<rbrakk> \<Longrightarrow> s \<in> \<lbrakk>event_ivl ev \<sigma>\<rbrakk>"
  by (simp add: event_ivl_def)

lemma return_ivl_sound:
  assumes gs: "s \<in> \<lbrakk>\<sigma>\<rbrakk>"
  shows "s(ret_var := (case e of None \<Rightarrow> s ret_var | Some a \<Rightarrow> aval a s)) \<in> \<lbrakk>return_ivl e p \<sigma>\<rbrakk>"
  using assign_ivl_sound[OF gs] gs
  by (cases e) (simp_all add: return_ivl_def)

lemma skip_ivl_mono: "sigma1 \<le> sigma2 \<Longrightarrow> skip_ivl sigma1 \<le> skip_ivl sigma2"
  by (simp add: skip_ivl_def)

lemma body_ivl_mono: "sigma1 \<le> sigma2 \<Longrightarrow> body_ivl p sigma1 \<le> body_ivl p sigma2"
  by (simp add: body_ivl_def)

lemma event_ivl_mono: "sigma1 \<le> sigma2 \<Longrightarrow> event_ivl ev sigma1 \<le> event_ivl ev sigma2"
  by (simp add: event_ivl_def)

lemma return_ivl_mono:
  "sigma1 \<le> sigma2 \<Longrightarrow> return_ivl e p sigma1 \<le> return_ivl e p sigma2"
  by (cases e) (simp_all add: return_ivl_def assign_ivl_mono)

subsection \<open>Classifier-parametric procedure entry and bundled transfer functions\<close>

text \<open>Procedure entry: keep globals, reset locals to the full interval, then bind
  the formals to the abstract values of the actuals evaluated in the caller.
  Generic via enter_frame_D/enter_D (Constraint_System.thy), parameterised by
  ivl_top as the domain's fully-imprecise reset value.  Entry and combine are
  the only fields that consult a classifier, so the bundled transfer function
  is parametric in the classifier throughout.\<close>

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
  "ivl_tf_for gs = (| tf_assign  = assign_ivl,
                       tf_special = special_ivl,
                       tf_branch  = bfilter_ivl,
                       tf_skip    = skip_ivl,
                       tf_body    = body_ivl,
                       tf_return  = return_ivl,
                       tf_enter   = enter_ivl_for gs,
                       tf_event   = event_ivl,
                       tf_combine_env = combine_env_abs gs |)"

lemma ivl_is_sound_transfer_for: "sound_transfer_for gs (ivl_tf_for gs)"
  unfolding ivl_tf_for_def
  apply unfold_locales
  subgoal by (simp add: assign_ivl_sound)
  subgoal by (simp add: special_ivl_sound)
  subgoal by (simp add: bfilter_ivl_sound)
  subgoal by (simp add: skip_ivl_sound)
  subgoal by (simp add: body_ivl_sound)
  subgoal by (simp add: return_ivl_sound)
  subgoal by (simp add: enter_ivl_for_sound)
  subgoal by (simp add: event_ivl_sound)
  subgoal by (simp add: combine_env_sound)
  done

lemma enter_frame_ivl_for_mono:
  assumes "s1 \<le> s2"
  shows "enter_frame_ivl_for gs s1 \<le> enter_frame_ivl_for gs s2"
  unfolding enter_frame_ivl_for_def by (rule enter_frame_D_mono[OF assms])

lemma enter_ivl_for_mono:
  assumes "s1 \<le> s2"
  shows "enter_ivl_for gs xs es s1 \<le> enter_ivl_for gs xs es s2"
  unfolding enter_ivl_for_def
proof (rule enter_D_mono[OF assms])
  show "list_all2 (\<le>) (map (\<lambda>e. aval_ivl e s1) es)
                       (map (\<lambda>e. aval_ivl e s2) es)"
    using assms by (simp add: list_all2_conv_all_nth aval_ivl_mono)
qed

lemma ivl_tf_for_mono:
  "s1 \<le> s2 \<Longrightarrow> apply_tf (ivl_tf_for gs) a s1 \<le> apply_tf (ivl_tf_for gs) a s2"
  by (cases a)
     (auto simp: ivl_tf_for_def assign_ivl_mono special_ivl_mono bfilter_ivl_mono
                 skip_ivl_mono body_ivl_mono return_ivl_mono enter_ivl_for_mono
                 event_ivl_mono)

text \<open>
  Reusable simp bundle for post-fixpoint proofs over the interval domain.
  Covers the core evaluation rules shared by all interval examples.
  Examples with multiplication also need @{thm [source] times_ivl_def},
  @{thm [source] ivl_times_core.simps}, @{thm [source] ivl_nonempty.simps};
  examples with branch edges also need @{thm [source] ivl_backward_domain.bfilter.simps};
  examples with procedure calls also need @{thm [source] enter_ivl_for_def},
  @{thm [source] enter_frame_ivl_for_def}, @{thm [source] bind_formals_abs_def},
  @{thm [source] combine_env_abs_def}.
\<close>
lemmas ivl_eval_simps =
  ivl_tf_for_def assign_ivl_def
  aval_ivl.simps
  plus_ivl.simps plus_eint.simps
  less_eq_ivl_def le_fun_def

end
