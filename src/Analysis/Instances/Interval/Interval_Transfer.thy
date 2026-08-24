theory Interval_Transfer
  imports Interval_Backward Interval_Special Voblint_Core.Constraint_System
    "Voblint_VIMP.VIMP_Globals"
begin

section \<open>Interval transfer functions\<close>

subsection \<open>Abstract branch and assignment\<close>

text \<open>
  Guard refinement delegates to the generic @{text bfilter} proved sound in
  @{locale backward_domain}. @{const bfilter_ivl} narrows on the branch selected
  by its boolean polarity argument (@{text True} for @{text "truthy (taval_syn \<Gamma> b s)"},
  @{text False} for @{text "\<not> truthy (taval_syn \<Gamma> b s)"}) -- this is @{text ivl_tf_for}'s
  @{text tf_branch} instance
  directly, matching Goblint's single polarity-parametrized @{text Spec.branch}.
\<close>

lemma bfilter_ivl_sound:
  "s \<in> \<lbrakk>\<sigma>\<rbrakk> \<Longrightarrow> truthy (taval_syn \<Gamma> b s) = res \<Longrightarrow> styped \<Gamma> s \<Longrightarrow>
   wt_exp \<Gamma> b (opk (esyn \<Gamma> b)) \<Longrightarrow> s \<in> \<lbrakk>bfilter_ivl \<Gamma> b res \<sigma>\<rbrakk>"
  using ivl_backward_domain.bfilter_sound by simp

text \<open>
  @{const branch_ivl} is Interval's \<open>tf_branch\<close> instance: a forward
  @{const interval_tobool} feasibility check ahead of @{const bfilter_ivl},
  matching Goblint's \<open>Base.branch\<close> structure. Proved once, generically, as
  @{thm [source] backward_domain.branch_sound}.
\<close>

lemma branch_ivl_sound:
  "s \<in> \<lbrakk>\<sigma>\<rbrakk> \<Longrightarrow> truthy (taval_syn \<Gamma> b s) = res \<Longrightarrow> styped \<Gamma> s \<Longrightarrow>
   wt_exp \<Gamma> b (opk (esyn \<Gamma> b)) \<Longrightarrow> s \<in> \<lbrakk>branch_ivl \<Gamma> b res \<sigma>\<rbrakk>"
  using ivl_backward_domain.branch_sound by simp

definition assign_ivl ::
    "tyenv => vname => exp => (vname => ivl) => (vname => ivl)"
where
  "assign_ivl \<Gamma> x a \<sigma> = \<sigma>(x := ivl_cast (\<Gamma> x) (aval_ivl_t (elaborate_syn \<Gamma> a) \<sigma>))"

lemma assign_ivl_sound:
  assumes gs: "s \<in> \<lbrakk>\<sigma>\<rbrakk>"
  shows "s(x := ik_norm (\<Gamma> x) (taval_syn \<Gamma> a s)) \<in> \<lbrakk>assign_ivl \<Gamma> x a \<sigma>\<rbrakk>"
  unfolding assign_ivl_def gamma_state_def
proof safe
  fix y
  from gs have V: "\<forall>z. s z \<in> gamma_ivl (\<sigma> z)"
    using gamma_stateD[OF gs] by simp
  have av: "taval_syn \<Gamma> a s \<in> gamma_ivl (aval_ivl_t (elaborate_syn \<Gamma> a) \<sigma>)"
    using aval_ivl_t_sound_syn[OF V] .
  show "(s(x := ik_norm (\<Gamma> x) (taval_syn \<Gamma> a s))) y
          \<in> gamma ((\<sigma>(x := ivl_cast (\<Gamma> x) (aval_ivl_t (elaborate_syn \<Gamma> a) \<sigma>))) y)"
  proof (cases "y = x")
    case True
    with V av show ?thesis by (simp add: gamma_abs_ivl ivl_cast_sound)
  next
    case False
    with V show ?thesis by simp
  qed
qed

text \<open>Nondeterministic and other special-call assignment (\<open>special_ivl\<close>) lives
  in \<open>Interval_Special\<close>, reused below.\<close>

lemma assign_ivl_mono:
  "sigma1 \<le> sigma2 \<Longrightarrow> assign_ivl \<Gamma> x a sigma1 \<le> assign_ivl \<Gamma> x a sigma2"
  by (simp add: assign_ivl_def aval_ivl_mono le_funD le_funI ivl_cast_mono)

subsection \<open>Skip, body-entry, and return\<close>

text \<open>Interval has no lifecycle-specific abstract information: \<open>skip\<^sup>#\<close>/\<open>body\<^sup>#\<close> are
  the identity. \<open>return\<^sup>#\<close> cannot reuse \<open>assign_ivl\<close>: \<^const>\<open>apply_tf\<close>'s
  \<open>EA_Ret\<close> case does not pass the edge's own baked return kind \<open>rk\<close> through
  to \<open>tf_return\<close> at all (\<open>sound_transfer_for\<close>'s \<open>tf_sound_return_for\<close> quantifies
  over every \<open>rk\<close> universally), so \<open>return\<^sup>#\<close>'s single output must already be
  sound for whichever \<open>rk\<close> the compiled edge actually used -- unlike an
  ordinary assignment, there is no declared kind here to cast against, only
  an unknown one, so \<open>ret_var\<close> widens to \<^const>\<open>ivl_top\<close> whenever the return
  carries a value.\<close>

definition skip_ivl :: "(vname => ivl) => (vname => ivl)" where
  "skip_ivl \<sigma> = \<sigma>"

definition body_ivl :: "pname => (vname => ivl) => (vname => ivl)" where
  "body_ivl p \<sigma> = \<sigma>"

definition return_ivl ::
    "exp option => pname => (vname => ivl) => (vname => ivl)"
where
  "return_ivl e p \<sigma> = (case e of None \<Rightarrow> \<sigma> | Some a \<Rightarrow> \<sigma>(ret_var := ivl_top))"

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
  shows "s(ret_var := (case e of None \<Rightarrow> s ret_var | Some a \<Rightarrow> ik_norm rk (taval_syn \<Gamma> a s)))
           \<in> \<lbrakk>return_ivl e p \<sigma>\<rbrakk>"
  using gs unfolding gamma_state_def
  by (cases e) (auto simp: return_ivl_def gamma_ivl_top)

lemma skip_ivl_mono: "sigma1 \<le> sigma2 \<Longrightarrow> skip_ivl sigma1 \<le> skip_ivl sigma2"
  by (simp add: skip_ivl_def)

lemma body_ivl_mono: "sigma1 \<le> sigma2 \<Longrightarrow> body_ivl p sigma1 \<le> body_ivl p sigma2"
  by (simp add: body_ivl_def)

lemma event_ivl_mono: "sigma1 \<le> sigma2 \<Longrightarrow> event_ivl ev sigma1 \<le> event_ivl ev sigma2"
  by (simp add: event_ivl_def)

lemma return_ivl_mono:
  "sigma1 \<le> sigma2 \<Longrightarrow> return_ivl e p sigma1 \<le> return_ivl e p sigma2"
  by (cases e) (simp_all add: return_ivl_def le_fun_def)

subsection \<open>Classifier-parametric transfer\<close>

text \<open>
  Entry and combine are the only fields that consult a classifier (inside
  \<^const>\<open>enter_frame_D\<close> and \<^const>\<open>combine_env_abs\<close>); assignment and guard
  transfer never do, so the bundled transfer function is parametric in the
  classifier throughout (mirroring \<open>sign_tf_for\<close> for the sign domain).
\<close>

definition enter_frame_ivl_for ::
    "(vname => bool) => ivl abs_state => ivl abs_state" where
  "enter_frame_ivl_for gs = enter_frame_D gs ivl_top"

definition enter_ivl_for ::
    "(vname => bool) => tyenv => vname list => exp list =>
      ivl abs_state => ivl abs_state" where
  "enter_ivl_for gs \<Gamma> = enter_D_typed gs ivl_top \<Gamma> ivl_cast aval_ivl_t"

lemma enter_frame_ivl_for_sound:
  assumes gs: "s \<in> \<lbrakk>\<sigma>\<rbrakk>"
  shows "enter_state cls s \<in> \<lbrakk>enter_frame_ivl_for cls \<sigma>\<rbrakk>"
  unfolding enter_frame_ivl_for_def
proof (rule enter_frame_D_sound[OF gs])
  show "gamma ivl_top = UNIV" by (simp add: gamma_ivl_top)
qed

lemma enter_ivl_for_sound:
  assumes gs: "s \<in> \<lbrakk>\<sigma>\<rbrakk>"
  shows "bind_formals xs (map2 (\<lambda>x e. ik_norm (\<Gamma> x) (taval_syn \<Gamma> e s)) xs es) (enter_state cls s)
           \<in> \<lbrakk>enter_ivl_for cls \<Gamma> xs es \<sigma>\<rbrakk>"
  unfolding enter_ivl_for_def
proof (rule enter_D_typed_sound[OF gs])
  show "gamma ivl_top = UNIV" by (simp add: gamma_ivl_top)
next
  fix ik v a show "v \<in> gamma a \<Longrightarrow> ik_norm ik v \<in> gamma (ivl_cast ik a)"
    by (simp add: gamma_abs_ivl ivl_cast_sound)
next
  fix ik e' s' \<sigma>' show "(\<forall>x. s' x \<in> gamma (\<sigma>' x)) \<Longrightarrow>
                          taval \<Gamma> ik e' s' \<in> gamma (aval_ivl_t (elaborate \<Gamma> ik e') \<sigma>')"
    by (simp add: gamma_abs_ivl aval_ivl_sound)
qed

definition ivl_tf_for :: "(vname => bool) => tyenv => ivl domain_transfer" where
  "ivl_tf_for gs \<Gamma> = (| tf_assign  = assign_ivl \<Gamma>,
                       tf_special = special_ivl \<Gamma>,
                       tf_branch  = branch_ivl \<Gamma>,
                       tf_skip    = skip_ivl,
                       tf_body    = body_ivl,
                       tf_return  = return_ivl,
                       tf_enter   = enter_ivl_for gs \<Gamma>,
                       tf_event   = event_ivl,
                       tf_caller_cont = (\<lambda>_ \<sigma>. \<sigma>),
                       tf_combine_env = (\<lambda>_. combine_env_abs gs) |)"

text \<open>
  The branch obligation below is unresolved: @{thm [source] branch_ivl_sound}
  requires \<open>styped \<Gamma> s\<close> and \<open>wt_exp \<Gamma> b (opk (esyn \<Gamma> b))\<close>, premises that
  \<open>sound_transfer_for\<close>'s \<open>tf_sound_branch_for\<close> obligation does not supply.
  Closing this needs a well-typedness invariant threaded through the whole
  \<open>sound_transfer_for\<close> soundness chain, not a local fix to this lemma. This is
  the same gap \<open>sign_is_sound_transfer_for\<close> defers for Sign.
\<close>
lemma ivl_is_sound_transfer_for: "sound_transfer_for gs (ivl_tf_for gs \<Gamma>) \<Gamma>"
  unfolding ivl_tf_for_def
  apply unfold_locales
  subgoal by (simp add: assign_ivl_sound)
  subgoal by (simp add: special_ivl_sound)
  subgoal sorry
  subgoal by (simp add: skip_ivl_sound)
  subgoal by (simp add: body_ivl_sound)
  subgoal by (simp add: return_ivl_sound)
  subgoal by (simp add: enter_ivl_for_sound)
  subgoal by (simp add: event_ivl_sound)
  subgoal by simp
  subgoal by (simp add: combine_env_sound)
  done

lemma enter_frame_ivl_for_mono:
  assumes "s1 \<le> s2"
  shows "enter_frame_ivl_for gs s1 \<le> enter_frame_ivl_for gs s2"
  unfolding enter_frame_ivl_for_def by (rule enter_frame_D_mono[OF assms])

lemma enter_ivl_for_mono:
  assumes "s1 \<le> s2"
  shows "enter_ivl_for gs \<Gamma> xs es s1 \<le> enter_ivl_for gs \<Gamma> xs es s2"
  unfolding enter_ivl_for_def
proof (rule enter_D_typed_mono[OF assms])
  show "\<And>ik a1 a2. a1 \<le> a2 \<Longrightarrow> ivl_cast ik a1 \<le> ivl_cast ik a2"
    by (rule ivl_cast_mono)
next
  show "\<And>ik e' \<tau>1 \<tau>2. \<tau>1 \<le> \<tau>2 \<Longrightarrow>
          aval_ivl_t (elaborate \<Gamma> ik e') \<tau>1 \<le> aval_ivl_t (elaborate \<Gamma> ik e') \<tau>2"
    by (rule aval_ivl_t_mono)
qed

lemma ivl_tf_for_mono:
  "s1 \<le> s2 \<Longrightarrow>
   apply_tf (ivl_tf_for gs \<Gamma>) a s1 \<le> apply_tf (ivl_tf_for gs \<Gamma>) a s2"
  by (cases a)
     (auto simp: ivl_tf_for_def assign_ivl_mono special_ivl_mono branch_ivl_mono
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
  aval_ivl_t.simps aval_ivl_def elaborate.simps elaborate_syn_def
  plus_ivl.simps plus_eint.simps
  less_eq_ivl_def le_fun_def

end

