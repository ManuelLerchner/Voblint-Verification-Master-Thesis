theory Sign_Transfer
  imports Sign_Backward Sign_Special Voblint_Core.Constraint_System "Voblint_VIMP.VIMP_Globals"

begin

section \<open>Sign transfer functions\<close>

subsection \<open>Abstract assignment\<close>

definition assign_sign ::
    "tyenv => vname => exp => (vname => sign) => (vname => sign)"
where
  "assign_sign \<Gamma> x a \<sigma> = \<sigma>(x := sign_cast (\<Gamma> x) (aval_sign_t (elaborate_syn \<Gamma> a) \<sigma>))"

lemma assign_sign_sound:
  assumes gs: "s \<in> \<lbrakk>\<sigma>\<rbrakk>"
  shows "s(x := ik_norm (\<Gamma> x) (taval_syn \<Gamma> a s)) \<in> \<lbrakk>assign_sign \<Gamma> x a \<sigma>\<rbrakk>"
  unfolding assign_sign_def gamma_state_def
proof safe
  fix y
  from gs have V: "\<forall>z. s z \<in> gamma_sign (\<sigma> z)"
    using gamma_stateD[OF gs] by simp
  have av: "taval_syn \<Gamma> a s \<in> gamma_sign (aval_sign_t (elaborate_syn \<Gamma> a) \<sigma>)"
    using aval_sign_t_sound_syn[OF V] .
  show "(s(x := ik_norm (\<Gamma> x) (taval_syn \<Gamma> a s))) y
          \<in> gamma ((\<sigma>(x := sign_cast (\<Gamma> x) (aval_sign_t (elaborate_syn \<Gamma> a) \<sigma>))) y)"
  proof (cases "y = x")
    case True
    with V av show ?thesis by (simp add: gamma_abs_sign sign_cast_sound_sign)
  next
    case False
    with V show ?thesis by simp
  qed
qed

text \<open>Nondeterministic and other special-call assignment (\<open>special_sign\<close>) lives
  in \<^theory>\<open>Voblint_Analysis.Sign_Special\<close>, reused below.\<close>
subsection \<open>Bundled transfer functions\<close>

lemma assign_sign_mono:
  "sigma1 \<le> sigma2 \<Longrightarrow> assign_sign \<Gamma> x a sigma1 \<le> assign_sign \<Gamma> x a sigma2"
  by (simp add: assign_sign_def aval_sign_mono le_funD le_funI sign_cast_mono)

subsection \<open>Skip, body-entry, and return\<close>

text \<open>Sign has no lifecycle-specific abstract information: \<open>skip\<^sup>#\<close>/\<open>body\<^sup>#\<close> are
  the identity. \<open>return\<^sup>#\<close> cannot reuse \<open>assign_sign\<close>: \<^const>\<open>apply_tf\<close>'s
  \<open>EA_Ret\<close> case does not pass the edge's own baked return kind \<open>rk\<close> through
  to \<open>tf_return\<close> at all (\<open>sound_transfer_for\<close>'s \<open>tf_sound_return_for\<close> quantifies
  over every \<open>rk\<close> universally), so \<open>return\<^sup>#\<close>'s single output must already be
  sound for whichever \<open>rk\<close> the compiled edge actually used -- unlike an
  ordinary assignment, there is no declared kind here to cast against, only
  an unknown one, so \<open>ret_var\<close> widens to \<^const>\<open>STop\<close> whenever the return
  carries a value.\<close>

definition skip_sign :: "(vname => sign) => (vname => sign)" where
  "skip_sign \<sigma> = \<sigma>"

definition body_sign :: "pname => (vname => sign) => (vname => sign)" where
  "body_sign p \<sigma> = \<sigma>"

definition return_sign ::
    "exp option => pname => (vname => sign) => (vname => sign)"
where
  "return_sign e p \<sigma> = (case e of None \<Rightarrow> \<sigma> | Some a \<Rightarrow> \<sigma>(ret_var := STop))"

text \<open>A check observes its condition but never refines the state (that is
  \<open>abstract_check_domain\<close>'s job): Sign has no notion of that observation
  either, so \<open>event_sign\<close> is the identity like \<open>skip_sign\<close>/\<open>body_sign\<close>.\<close>
definition event_sign :: "analysis_event => (vname => sign) => (vname => sign)" where
  "event_sign ev \<sigma> = \<sigma>"

lemma skip_sign_sound: "s \<in> \<lbrakk>\<sigma>\<rbrakk> \<Longrightarrow> s \<in> \<lbrakk>skip_sign \<sigma>\<rbrakk>"
  by (simp add: skip_sign_def)

lemma body_sign_sound: "s \<in> \<lbrakk>\<sigma>\<rbrakk> \<Longrightarrow> s \<in> \<lbrakk>body_sign p \<sigma>\<rbrakk>"
  by (simp add: body_sign_def)

lemma event_sign_sound: "s \<in> \<lbrakk>\<sigma>\<rbrakk> \<Longrightarrow> s \<in> \<lbrakk>event_sign ev \<sigma>\<rbrakk>"
  by (simp add: event_sign_def)

lemma return_sign_sound:
  assumes gs: "s \<in> \<lbrakk>\<sigma>\<rbrakk>"
  shows "s(ret_var := (case e of None \<Rightarrow> s ret_var | Some a \<Rightarrow> ik_norm rk (taval_syn \<Gamma> a s)))
           \<in> \<lbrakk>return_sign e p \<sigma>\<rbrakk>"
  using gs unfolding gamma_state_def
  by (cases e) (auto simp: return_sign_def gamma_sign_top)

lemma skip_sign_mono: "sigma1 \<le> sigma2 \<Longrightarrow> skip_sign sigma1 \<le> skip_sign sigma2"
  by (simp add: skip_sign_def)

lemma body_sign_mono: "sigma1 \<le> sigma2 \<Longrightarrow> body_sign p sigma1 \<le> body_sign p sigma2"
  by (simp add: body_sign_def)

lemma event_sign_mono: "sigma1 \<le> sigma2 \<Longrightarrow> event_sign ev sigma1 \<le> event_sign ev sigma2"
  by (simp add: event_sign_def)

lemma return_sign_mono:
  "sigma1 \<le> sigma2 \<Longrightarrow> return_sign e p sigma1 \<le> return_sign e p sigma2"
  by (cases e) (simp_all add: return_sign_def le_fun_def)

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
    "(vname => bool) => tyenv => vname list => exp list =>
      sign abs_state => sign abs_state" where
  "enter_sign_for gs \<Gamma> = enter_D_typed gs STop \<Gamma> sign_cast aval_sign_t"

lemma enter_frame_sign_for_sound:
  assumes gs: "s \<in> \<lbrakk>\<sigma>\<rbrakk>"
  shows "enter_state cls s \<in> \<lbrakk>enter_frame_sign_for cls \<sigma>\<rbrakk>"
  unfolding enter_frame_sign_for_def
proof (rule enter_frame_D_sound[OF gs])
  show "gamma STop = UNIV" by simp
qed

lemma enter_sign_for_sound:
  assumes gs: "s \<in> \<lbrakk>\<sigma>\<rbrakk>"
  shows "bind_formals xs (map2 (\<lambda>x e. ik_norm (\<Gamma> x) (taval_syn \<Gamma> e s)) xs es) (enter_state cls s)
           \<in> \<lbrakk>enter_sign_for cls \<Gamma> xs es \<sigma>\<rbrakk>"
  unfolding enter_sign_for_def
proof (rule enter_D_typed_sound[OF gs])
  show "gamma STop = UNIV" by simp
next
  fix ik v a show "v \<in> gamma a \<Longrightarrow> ik_norm ik v \<in> gamma (sign_cast ik a)"
    by (simp add: gamma_abs_sign sign_cast_sound_sign)
next
  fix ik e' s' \<sigma>' show "(\<forall>x. s' x \<in> gamma (\<sigma>' x)) \<Longrightarrow>
                          taval \<Gamma> ik e' s' \<in> gamma (aval_sign_t (elaborate \<Gamma> ik e') \<sigma>')"
    by (simp add: gamma_abs_sign aval_sign_sound)
qed

definition sign_tf_for :: "(vname => bool) => tyenv => sign domain_transfer" where
  "sign_tf_for gs \<Gamma> = (| tf_assign  = assign_sign \<Gamma>,
                       tf_special = special_sign \<Gamma>,
                       tf_branch  = branch_sign \<Gamma>,
                       tf_skip    = skip_sign,
                       tf_body    = body_sign,
                       tf_return  = return_sign,
                       tf_enter   = enter_sign_for gs \<Gamma>,
                       tf_event   = event_sign,
                       tf_caller_cont = (\<lambda>_ \<sigma>. \<sigma>),
                       tf_combine_env = (\<lambda>_. combine_env_abs gs) |)"

text \<open>
  The branch obligation below is unresolved: @{thm [source] branch_sign_sound}
  requires \<open>styped \<Gamma> s\<close> and \<open>wt_exp \<Gamma> b (opk (esyn \<Gamma> b))\<close>, premises that
  \<open>sound_transfer_for\<close>'s \<open>tf_sound_branch_for\<close> obligation does not supply.
  Closing this needs a well-typedness invariant threaded through the whole
  \<open>sound_transfer_for\<close> soundness chain, not a local fix to this lemma.
\<close>
lemma sign_is_sound_transfer_for: "sound_transfer_for gs (sign_tf_for gs \<Gamma>) \<Gamma>"
  unfolding sign_tf_for_def
  apply unfold_locales
  subgoal by (simp add: assign_sign_sound)
  subgoal by (simp add: special_sign_sound)
  subgoal sorry
  subgoal by (simp add: skip_sign_sound)
  subgoal by (simp add: body_sign_sound)
  subgoal by (simp add: return_sign_sound)
  subgoal by (simp add: enter_sign_for_sound)
  subgoal by (simp add: event_sign_sound)
  subgoal by simp
  subgoal by (simp add: combine_env_sound)
  done

lemma enter_frame_sign_for_mono:
  assumes "s1 \<le> s2"
  shows "enter_frame_sign_for gs s1 \<le> enter_frame_sign_for gs s2"
  unfolding enter_frame_sign_for_def by (rule enter_frame_D_mono[OF assms])

lemma enter_sign_for_mono:
  assumes "s1 \<le> s2"
  shows "enter_sign_for gs \<Gamma> xs es s1 \<le> enter_sign_for gs \<Gamma> xs es s2"
  unfolding enter_sign_for_def
proof (rule enter_D_typed_mono[OF assms])
  show "\<And>ik a1 a2. a1 \<le> a2 \<Longrightarrow> sign_cast ik a1 \<le> sign_cast ik a2"
    by (rule sign_cast_mono)
next
  show "\<And>ik e' \<tau>1 \<tau>2. \<tau>1 \<le> \<tau>2 \<Longrightarrow>
          aval_sign_t (elaborate \<Gamma> ik e') \<tau>1 \<le> aval_sign_t (elaborate \<Gamma> ik e') \<tau>2"
    by (rule aval_sign_t_mono)
qed

lemma sign_tf_for_mono:
  "s1 \<le> s2 \<Longrightarrow>
   apply_tf (sign_tf_for gs \<Gamma>) a s1 \<le> apply_tf (sign_tf_for gs \<Gamma>) a s2"
  by (cases a)
     (auto simp: sign_tf_for_def assign_sign_mono special_sign_mono branch_sign_mono
                 skip_sign_mono body_sign_mono return_sign_mono enter_sign_for_mono
                 event_sign_mono)

end
