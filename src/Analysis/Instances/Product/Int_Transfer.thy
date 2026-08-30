theory Int_Transfer
  imports Int_Backward Int_Warrowing Sign_Special Parity_Special
    "Voblint_Core.Transfer_Interface" "Voblint_VIMP.VIMP_Globals"
begin

section \<open>Composite integer-domain transfer functions\<close>

text \<open>
  Registers the composite Sign/Interval/Parity/Congruence domain against the
  generic transfer-function interface (\<^locale>\<open>sound_transfer_for\<close>,
  \<^typ>\<open>'a domain_transfer\<close>), mirroring \<open>ivl_tf_for\<close>/\<open>sign_tf_for\<close>. Every
  refinement mode gets its own registered bundle rather than a single
  mode-parameterised one: \<open>Int_Backward\<close> already split \<open>Refine_Fixpoint\<close>
  onto the weaker \<^locale>\<open>backward_domain\<close> locale (no monotonicity theorem
  for \<open>refine_fix\<close>), and keeping that split visible at the
  transfer-registration layer -- three named bundles, three named soundness
  interpretations, a monotonicity bonus lemma for only two of them -- avoids
  hiding the asymmetry behind a single mode argument.
\<close>

subsection \<open>Guard refinement\<close>

text \<open>
  Guard refinement delegates to the generic \<open>bfilter\<close> proved sound per mode
  by \<^theory>\<open>Voblint_Analysis.Int_Backward\<close>'s three interpretations.
\<close>

lemma bfilter_int_dom_never_sound:
  "s \<in> \<lbrakk>\<sigma>\<rbrakk> \<Longrightarrow> truthy(aval b s) = res \<Longrightarrow> s \<in> \<lbrakk>bfilter_int_dom_never b res \<sigma>\<rbrakk>"
  using int_dom_backward_never.bfilter_sound by simp

lemma bfilter_int_dom_once_sound:
  "s \<in> \<lbrakk>\<sigma>\<rbrakk> \<Longrightarrow> truthy(aval b s) = res \<Longrightarrow> s \<in> \<lbrakk>bfilter_int_dom_once b res \<sigma>\<rbrakk>"
  using int_dom_backward_once.bfilter_sound by simp

lemma bfilter_int_dom_fixpoint_sound:
  "s \<in> \<lbrakk>\<sigma>\<rbrakk> \<Longrightarrow> truthy(aval b s) = res \<Longrightarrow> s \<in> \<lbrakk>bfilter_int_dom_fixpoint b res \<sigma>\<rbrakk>"
  using int_dom_backward_fixpoint.bfilter_sound by simp

text \<open>
  \<open>branch_int_dom_*\<close> is the composite domain's Goblint-aligned \<open>tf_branch\<close>
  instance per mode: a forward \<open>int_dom_tobool\<close> feasibility check ahead of
  \<open>bfilter_int_dom_*\<close>, proved once generically as
  @{thm [source] backward_domain.branch_sound}.
\<close>

lemma branch_int_dom_never_sound:
  "s \<in> \<lbrakk>\<sigma>\<rbrakk> \<Longrightarrow> truthy(aval b s) = res \<Longrightarrow> s \<in> \<lbrakk>branch_int_dom_never b res \<sigma>\<rbrakk>"
  using int_dom_backward_never.branch_sound by simp

lemma branch_int_dom_once_sound:
  "s \<in> \<lbrakk>\<sigma>\<rbrakk> \<Longrightarrow> truthy(aval b s) = res \<Longrightarrow> s \<in> \<lbrakk>branch_int_dom_once b res \<sigma>\<rbrakk>"
  using int_dom_backward_once.branch_sound by simp

lemma branch_int_dom_fixpoint_sound:
  "s \<in> \<lbrakk>\<sigma>\<rbrakk> \<Longrightarrow> truthy(aval b s) = res \<Longrightarrow> s \<in> \<lbrakk>branch_int_dom_fixpoint b res \<sigma>\<rbrakk>"
  using int_dom_backward_fixpoint.branch_sound by simp

subsection \<open>Abstract assignment\<close>

definition assign_int_dom ::
    "refine_mode => vname => exp => (vname => int_dom) => (vname => int_dom)"
where
  "assign_int_dom mode x a \<sigma> = \<sigma>(x := aval_int_dom mode a \<sigma>)"

lemma assign_int_dom_sound:
  "s \<in> \<lbrakk>\<sigma>\<rbrakk> \<Longrightarrow> s(x := aval a s) \<in> \<lbrakk>assign_int_dom mode x a \<sigma>\<rbrakk>"
  unfolding gamma_state_def assign_int_dom_def
  by (auto simp: aval_int_dom_sound)

lemma assign_int_dom_mono:
  assumes "mode ~= Refine_Fixpoint" and "sigma1 <= sigma2"
  shows "assign_int_dom mode x a sigma1 <= assign_int_dom mode x a sigma2"
  using assms
  by (simp add: assign_int_dom_def aval_int_dom_mono le_funD le_funI)

subsection \<open>Min/Max special-call primitives\<close>

text \<open>
  Sign, Interval, and Parity each already implement a real \<open>min\<close>/\<open>max\<close>
  primitive for the \<open>Nondet_Int\<close>/\<open>Min\<close>/\<open>Max\<close> special-call dispatch
  (\<open>sign_min\<close>/\<open>sign_max\<close>, \<open>ivl_min\<close>/\<open>ivl_max\<close>,
  \<open>parity_min\<close>/\<open>parity_max\<close>). Congruence has no such primitive: the
  congruence class of a \<open>min\<close>/\<open>max\<close> result is not determined by the
  operands' congruence classes in general, so the congruence component stays
  \<open>top\<close> -- conservative, matching Congruence's own choice for \<open>narrow\<close> in
  \<^theory>\<open>Voblint_Analysis.Congruence_Warrowing\<close>. Mode-aware refinement then
  applies to the raw combination exactly as it does for
  \<open>plus_int_dom\<close>/\<open>minus_int_dom\<close>/\<open>times_int_dom\<close>.
\<close>

definition int_dom_min_raw :: "int_dom => int_dom => int_dom" where
  "int_dom_min_raw a b =
     (top :: int_dom)\<lparr>
       int_sign := sign_min (int_sign a) (int_sign b),
       int_ivl := ivl_min (int_ivl a) (int_ivl b),
       int_parity := parity_min (int_parity a) (int_parity b)
     \<rparr>"

definition int_dom_max_raw :: "int_dom => int_dom => int_dom" where
  "int_dom_max_raw a b =
     (top :: int_dom)\<lparr>
       int_sign := sign_max (int_sign a) (int_sign b),
       int_ivl := ivl_max (int_ivl a) (int_ivl b),
       int_parity := parity_max (int_parity a) (int_parity b)
     \<rparr>"

lemma int_dom_min_raw_sound:
  assumes "i : gamma_int_dom a" and "j : gamma_int_dom b"
  shows "min i j : gamma_int_dom (int_dom_min_raw a b)"
  using assms
  by (auto simp: gamma_int_dom_def int_dom_min_raw_def top_int_dom_ext_def
        intro: sign_min_sound ivl_min_sound parity_min_sound)

lemma int_dom_max_raw_sound:
  assumes "i : gamma_int_dom a" and "j : gamma_int_dom b"
  shows "max i j : gamma_int_dom (int_dom_max_raw a b)"
  using assms
  by (auto simp: gamma_int_dom_def int_dom_max_raw_def top_int_dom_ext_def
        intro: sign_max_sound ivl_max_sound parity_max_sound)

lemma int_dom_min_raw_mono:
  assumes "a1 <= a2" and "b1 <= b2"
  shows "int_dom_min_raw a1 b1 <= int_dom_min_raw a2 b2"
  using assms
  by (auto simp: int_dom_min_raw_def less_eq_int_dom_ext_def
        intro: sign_min_combine_mono ivl_min_combine_mono parity_min_combine_mono)

lemma int_dom_max_raw_mono:
  assumes "a1 <= a2" and "b1 <= b2"
  shows "int_dom_max_raw a1 b1 <= int_dom_max_raw a2 b2"
  using assms
  by (auto simp: int_dom_max_raw_def less_eq_int_dom_ext_def
        intro: sign_max_combine_mono ivl_max_combine_mono parity_max_combine_mono)

definition int_dom_min :: "refine_mode => int_dom => int_dom => int_dom" where
  "int_dom_min mode a b = refine mode (int_dom_min_raw a b)"

definition int_dom_max :: "refine_mode => int_dom => int_dom => int_dom" where
  "int_dom_max mode a b = refine mode (int_dom_max_raw a b)"

lemma int_dom_min_sound:
  assumes "i : gamma_int_dom a" and "j : gamma_int_dom b"
  shows "min i j : gamma_int_dom (int_dom_min mode a b)"
proof -
  have "min i j : gamma_int_dom (int_dom_min_raw a b)"
    by (rule int_dom_min_raw_sound[OF assms])
  then show ?thesis
    unfolding int_dom_min_def using refine_exact by simp
qed

lemma int_dom_max_sound:
  assumes "i : gamma_int_dom a" and "j : gamma_int_dom b"
  shows "max i j : gamma_int_dom (int_dom_max mode a b)"
proof -
  have "max i j : gamma_int_dom (int_dom_max_raw a b)"
    by (rule int_dom_max_raw_sound[OF assms])
  then show ?thesis
    unfolding int_dom_max_def using refine_exact by simp
qed

lemma int_dom_min_mono:
  assumes "mode ~= Refine_Fixpoint" and "a1 <= a2" and "b1 <= b2"
  shows "int_dom_min mode a1 b1 <= int_dom_min mode a2 b2"
proof -
  have raw: "int_dom_min_raw a1 b1 <= int_dom_min_raw a2 b2"
    by (rule int_dom_min_raw_mono[OF assms(2,3)])
  show ?thesis
    unfolding int_dom_min_def
    by (rule monoD[OF refine_nonfixpoint_mono[OF assms(1)] raw])
qed

lemma int_dom_max_mono:
  assumes "mode ~= Refine_Fixpoint" and "a1 <= a2" and "b1 <= b2"
  shows "int_dom_max mode a1 b1 <= int_dom_max mode a2 b2"
proof -
  have raw: "int_dom_max_raw a1 b1 <= int_dom_max_raw a2 b2"
    by (rule int_dom_max_raw_mono[OF assms(2,3)])
  show ?thesis
    unfolding int_dom_max_def
    by (rule monoD[OF refine_nonfixpoint_mono[OF assms(1)] raw])
qed

subsection \<open>Special-call dispatch\<close>

fun special_int_dom ::
    "refine_mode => special_call => vname => (vname => int_dom) => (vname => int_dom)"
where
  "special_int_dom mode Nondet_Int x \<sigma> = \<sigma>(x := top)"
| "special_int_dom mode (Min a b) x \<sigma> =
     \<sigma>(x := int_dom_min mode (aval_int_dom mode a \<sigma>) (aval_int_dom mode b \<sigma>))"
| "special_int_dom mode (Max a b) x \<sigma> =
     \<sigma>(x := int_dom_max mode (aval_int_dom mode a \<sigma>) (aval_int_dom mode b \<sigma>))"

lemma gamma_int_dom_top: "gamma_int_dom (top :: int_dom) = UNIV"
  by (simp add: gamma_int_dom_def top_int_dom_ext_def top_ivl_def
        gamma_sign_top gamma_ivl_top gamma_parity_top)

lemma special_int_dom_sound:
  assumes gs: "s \<in> \<lbrakk>\<sigma>\<rbrakk>" and sr: "special_result sc s v"
  shows "s(x := v) \<in> \<lbrakk>special_int_dom mode sc x \<sigma>\<rbrakk>"
proof (cases sc)
  case Nondet_Int
  show ?thesis
    unfolding Nondet_Int gamma_state_def
    using gs unfolding gamma_state_def
    by (simp add: gamma_int_dom_top)
next
  case (Min a b)
  have V: "\<forall>y. s y \<in> gamma_int_dom (\<sigma> y)"
    using gs unfolding gamma_state_def by simp
  have Va: "aval a s : gamma_int_dom (aval_int_dom mode a \<sigma>)"
    by (rule aval_int_dom_sound[OF V])
  have Vb: "aval b s : gamma_int_dom (aval_int_dom mode b \<sigma>)"
    by (rule aval_int_dom_sound[OF V])
  have v: "v = min (aval a s) (aval b s)"
    using sr unfolding Min by simp
  have "v : gamma_int_dom (int_dom_min mode (aval_int_dom mode a \<sigma>) (aval_int_dom mode b \<sigma>))"
    unfolding v by (rule int_dom_min_sound[OF Va Vb])
  then show ?thesis
    unfolding Min gamma_state_def using V by (auto simp: gamma_int_dom_def)
next
  case (Max a b)
  have V: "\<forall>y. s y \<in> gamma_int_dom (\<sigma> y)"
    using gs unfolding gamma_state_def by simp
  have Va: "aval a s : gamma_int_dom (aval_int_dom mode a \<sigma>)"
    by (rule aval_int_dom_sound[OF V])
  have Vb: "aval b s : gamma_int_dom (aval_int_dom mode b \<sigma>)"
    by (rule aval_int_dom_sound[OF V])
  have v: "v = max (aval a s) (aval b s)"
    using sr unfolding Max by simp
  have "v : gamma_int_dom (int_dom_max mode (aval_int_dom mode a \<sigma>) (aval_int_dom mode b \<sigma>))"
    unfolding v by (rule int_dom_max_sound[OF Va Vb])
  then show ?thesis
    unfolding Max gamma_state_def using V by (auto simp: gamma_int_dom_def)
qed

lemma special_int_dom_mono:
  assumes mode: "mode ~= Refine_Fixpoint" and le: "sigma1 <= sigma2"
  shows "special_int_dom mode sc x sigma1 <= special_int_dom mode sc x sigma2"
proof (cases sc)
  case Nondet_Int
  then show ?thesis
    using le by (auto simp: le_fun_def)
next
  case (Min a b)
  have A: "aval_int_dom mode a sigma1 <= aval_int_dom mode a sigma2"
    using mode le by (rule aval_int_dom_mono)
  have B: "aval_int_dom mode b sigma1 <= aval_int_dom mode b sigma2"
    using mode le by (rule aval_int_dom_mono)
  have M: "int_dom_min mode (aval_int_dom mode a sigma1) (aval_int_dom mode b sigma1)
          <= int_dom_min mode (aval_int_dom mode a sigma2) (aval_int_dom mode b sigma2)"
    by (rule int_dom_min_mono[OF mode A B])
  show ?thesis
    unfolding Min using le M by (auto simp: le_fun_def)
next
  case (Max a b)
  have A: "aval_int_dom mode a sigma1 <= aval_int_dom mode a sigma2"
    using mode le by (rule aval_int_dom_mono)
  have B: "aval_int_dom mode b sigma1 <= aval_int_dom mode b sigma2"
    using mode le by (rule aval_int_dom_mono)
  have M: "int_dom_max mode (aval_int_dom mode a sigma1) (aval_int_dom mode b sigma1)
          <= int_dom_max mode (aval_int_dom mode a sigma2) (aval_int_dom mode b sigma2)"
    by (rule int_dom_max_mono[OF mode A B])
  show ?thesis
    unfolding Max using le M by (auto simp: le_fun_def)
qed

subsection \<open>Skip, body-entry, return, and event\<close>

text \<open>Composite \<open>int_dom\<close> has no lifecycle-specific abstract information,
  mirroring every other current domain: \<open>skip\<^sup>#\<close>/\<open>body\<^sup>#\<close>/\<open>event\<^sup>#\<close> are
  the identity, and \<open>return\<^sup>#\<close> reuses \<open>assign_int_dom\<close>.\<close>

definition skip_int_dom :: "(vname => int_dom) => (vname => int_dom)" where
  "skip_int_dom \<sigma> = \<sigma>"

definition body_int_dom :: "pname => (vname => int_dom) => (vname => int_dom)" where
  "body_int_dom p \<sigma> = \<sigma>"

definition event_int_dom :: "analysis_event => (vname => int_dom) => (vname => int_dom)" where
  "event_int_dom ev \<sigma> = \<sigma>"

definition return_int_dom ::
    "refine_mode => exp option => pname => (vname => int_dom) => (vname => int_dom)"
where
  "return_int_dom mode e p \<sigma> = (case e of None \<Rightarrow> \<sigma> | Some a \<Rightarrow> assign_int_dom mode ret_var a \<sigma>)"

lemma skip_int_dom_sound: "s \<in> \<lbrakk>\<sigma>\<rbrakk> \<Longrightarrow> s \<in> \<lbrakk>skip_int_dom \<sigma>\<rbrakk>"
  by (simp add: skip_int_dom_def)

lemma body_int_dom_sound: "s \<in> \<lbrakk>\<sigma>\<rbrakk> \<Longrightarrow> s \<in> \<lbrakk>body_int_dom p \<sigma>\<rbrakk>"
  by (simp add: body_int_dom_def)

lemma event_int_dom_sound: "s \<in> \<lbrakk>\<sigma>\<rbrakk> \<Longrightarrow> s \<in> \<lbrakk>event_int_dom ev \<sigma>\<rbrakk>"
  by (simp add: event_int_dom_def)

lemma return_int_dom_sound:
  assumes gs: "s \<in> \<lbrakk>\<sigma>\<rbrakk>"
  shows "s(ret_var := (case e of None \<Rightarrow> s ret_var | Some a \<Rightarrow> aval a s))
           \<in> \<lbrakk>return_int_dom mode e p \<sigma>\<rbrakk>"
  using assign_int_dom_sound[OF gs] gs
  by (cases e) (simp_all add: return_int_dom_def)

lemma skip_int_dom_mono: "sigma1 <= sigma2 \<Longrightarrow> skip_int_dom sigma1 <= skip_int_dom sigma2"
  by (simp add: skip_int_dom_def)

lemma body_int_dom_mono: "sigma1 <= sigma2 \<Longrightarrow> body_int_dom p sigma1 <= body_int_dom p sigma2"
  by (simp add: body_int_dom_def)

lemma event_int_dom_mono: "sigma1 <= sigma2 \<Longrightarrow> event_int_dom ev sigma1 <= event_int_dom ev sigma2"
  by (simp add: event_int_dom_def)

lemma return_int_dom_mono:
  assumes "mode ~= Refine_Fixpoint" and "sigma1 <= sigma2"
  shows "return_int_dom mode e p sigma1 <= return_int_dom mode e p sigma2"
  using assms
  by (cases e) (simp_all add: return_int_dom_def assign_int_dom_mono)

subsection \<open>Classifier-parametric procedure entry\<close>

definition enter_frame_int_dom_for ::
    "(vname => bool) => int_dom abs_state => int_dom abs_state" where
  "enter_frame_int_dom_for gs = enter_frame_D gs (top :: int_dom)"

definition enter_int_dom_for ::
    "refine_mode => (vname => bool) => vname list => exp list =>
      int_dom abs_state => int_dom abs_state" where
  "enter_int_dom_for mode gs = enter_D gs (top :: int_dom) (aval_int_dom mode)"

lemma enter_frame_int_dom_for_sound:
  assumes gs: "s \<in> \<lbrakk>\<sigma>\<rbrakk>"
  shows "enter_state cls s \<in> \<lbrakk>enter_frame_int_dom_for cls \<sigma>\<rbrakk>"
  unfolding enter_frame_int_dom_for_def
proof (rule enter_frame_D_sound[OF gs])
  show "gamma (top :: int_dom) = UNIV" by (simp add: gamma_int_dom_top)
qed

lemma enter_int_dom_for_sound:
  assumes gs: "s \<in> \<lbrakk>\<sigma>\<rbrakk>"
  shows "bind_formals xs (map (\<lambda>e. aval e s) es) (enter_state cls s)
           \<in> \<lbrakk>enter_int_dom_for mode cls xs es \<sigma>\<rbrakk>"
  unfolding enter_int_dom_for_def
proof (rule enter_D_sound[OF gs])
  show "gamma (top :: int_dom) = UNIV" by (simp add: gamma_int_dom_top)
next
  have V: "\<forall>y. s y \<in> gamma_int_dom (\<sigma> y)"
    using gs unfolding gamma_state_def by simp
  show "list_all2 (\<lambda>v a. v \<in> gamma a)
          (map (\<lambda>e. aval e s) es) (map (\<lambda>e. aval_int_dom mode e \<sigma>) es)"
    using V by (simp add: list_all2_conv_all_nth aval_int_dom_sound)
qed

lemma enter_frame_int_dom_for_mono:
  assumes "s1 <= s2"
  shows "enter_frame_int_dom_for gs s1 <= enter_frame_int_dom_for gs s2"
  unfolding enter_frame_int_dom_for_def by (rule enter_frame_D_mono[OF assms])

lemma enter_int_dom_for_mono:
  assumes "mode ~= Refine_Fixpoint" and "s1 <= s2"
  shows "enter_int_dom_for mode gs xs es s1 <= enter_int_dom_for mode gs xs es s2"
  unfolding enter_int_dom_for_def
proof (rule enter_D_mono[OF assms(2)])
  show "list_all2 (<=) (map (\<lambda>e. aval_int_dom mode e s1) es) (map (\<lambda>e. aval_int_dom mode e s2) es)"
    using assms by (simp add: list_all2_conv_all_nth aval_int_dom_mono)
qed

subsection \<open>Registered transfer bundles, one per refinement mode\<close>

definition int_tf_never_for :: "(vname => bool) => int_dom domain_transfer" where
  "int_tf_never_for gs = (| tf_assign  = assign_int_dom Refine_Never,
                            tf_special = special_int_dom Refine_Never,
                            tf_branch  = branch_int_dom_never,
                            tf_skip    = skip_int_dom,
                            tf_body    = body_int_dom,
                            tf_return  = return_int_dom Refine_Never,
                            tf_enter   = enter_int_dom_for Refine_Never gs,
                            tf_event   = event_int_dom,
                            tf_caller_cont = (\<lambda>_ \<sigma>. \<sigma>),
                            tf_combine_env = (\<lambda>_. combine_env gs) |)"

definition int_tf_once_for :: "(vname => bool) => int_dom domain_transfer" where
  "int_tf_once_for gs = (| tf_assign  = assign_int_dom Refine_Once,
                           tf_special = special_int_dom Refine_Once,
                           tf_branch  = branch_int_dom_once,
                           tf_skip    = skip_int_dom,
                           tf_body    = body_int_dom,
                           tf_return  = return_int_dom Refine_Once,
                           tf_enter   = enter_int_dom_for Refine_Once gs,
                           tf_event   = event_int_dom,
                           tf_caller_cont = (\<lambda>_ \<sigma>. \<sigma>),
                           tf_combine_env = (\<lambda>_. combine_env gs) |)"

definition int_tf_fixpoint_for :: "(vname => bool) => int_dom domain_transfer" where
  "int_tf_fixpoint_for gs = (| tf_assign  = assign_int_dom Refine_Fixpoint,
                               tf_special = special_int_dom Refine_Fixpoint,
                               tf_branch  = branch_int_dom_fixpoint,
                               tf_skip    = skip_int_dom,
                               tf_body    = body_int_dom,
                               tf_return  = return_int_dom Refine_Fixpoint,
                               tf_enter   = enter_int_dom_for Refine_Fixpoint gs,
                               tf_event   = event_int_dom,
                               tf_caller_cont = (\<lambda>_ \<sigma>. \<sigma>),
                               tf_combine_env = (\<lambda>_. combine_env gs) |)"

lemma int_never_is_sound_transfer_for: "sound_transfer_for gs (int_tf_never_for gs)"
  unfolding int_tf_never_for_def
  apply unfold_locales
  subgoal by (simp add: assign_int_dom_sound)
  subgoal by (simp add: special_int_dom_sound)
  subgoal by (simp add: branch_int_dom_never_sound)
  subgoal by (simp add: skip_int_dom_sound)
  subgoal by (simp add: body_int_dom_sound)
  subgoal by (simp add: return_int_dom_sound)
  subgoal by (simp add: enter_int_dom_for_sound)
  subgoal by (simp add: event_int_dom_sound)
  subgoal by simp
  subgoal by (simp add: combine_env_sound)
  done

lemma int_once_is_sound_transfer_for: "sound_transfer_for gs (int_tf_once_for gs)"
  unfolding int_tf_once_for_def
  apply unfold_locales
  subgoal by (simp add: assign_int_dom_sound)
  subgoal by (simp add: special_int_dom_sound)
  subgoal by (simp add: branch_int_dom_once_sound)
  subgoal by (simp add: skip_int_dom_sound)
  subgoal by (simp add: body_int_dom_sound)
  subgoal by (simp add: return_int_dom_sound)
  subgoal by (simp add: enter_int_dom_for_sound)
  subgoal by (simp add: event_int_dom_sound)
  subgoal by simp
  subgoal by (simp add: combine_env_sound)
  done

lemma int_fixpoint_is_sound_transfer_for: "sound_transfer_for gs (int_tf_fixpoint_for gs)"
  unfolding int_tf_fixpoint_for_def
  apply unfold_locales
  subgoal by (simp add: assign_int_dom_sound)
  subgoal by (simp add: special_int_dom_sound)
  subgoal by (simp add: branch_int_dom_fixpoint_sound)
  subgoal by (simp add: skip_int_dom_sound)
  subgoal by (simp add: body_int_dom_sound)
  subgoal by (simp add: return_int_dom_sound)
  subgoal by (simp add: enter_int_dom_for_sound)
  subgoal by (simp add: event_int_dom_sound)
  subgoal by simp
  subgoal by (simp add: combine_env_sound)
  done

text \<open>
  \<open>apply_tf\<close> monotonicity is available for \<open>Never\<close> and \<open>Once\<close>: every field
  behind them (\<open>assign_int_dom\<close>, \<open>special_int_dom\<close>, \<open>return_int_dom\<close>,
  \<open>enter_int_dom_for\<close>) is monotone once \<open>mode \<noteq> Refine_Fixpoint\<close>, and
  \<open>Int_Backward\<close>'s \<open>backward_domain_refined\<close> interpretation gives
  \<open>bfilter_int_dom_never\<close>/\<open>bfilter_int_dom_once\<close> their own monotonicity
  (\<open>bfilter_mono\<close>). \<open>bfilter_int_dom_fixpoint\<close> has no such theorem --
  \<open>Int_Backward\<close> interpreted \<open>Refine_Fixpoint\<close> against the weaker
  \<^locale>\<open>backward_domain\<close> locale precisely because \<open>refine_fix\<close> lacks one --
  so \<open>int_tf_fixpoint_for\<close> gets no matching monotonicity lemma here.
\<close>

lemma int_tf_never_for_mono:
  "s1 <= s2 \<Longrightarrow> apply_tf (int_tf_never_for gs) a s1 <= apply_tf (int_tf_never_for gs) a s2"
  by (cases a)
     (auto simp: int_tf_never_for_def assign_int_dom_mono special_int_dom_mono
                 int_dom_backward_never.branch_mono skip_int_dom_mono body_int_dom_mono
                 return_int_dom_mono enter_int_dom_for_mono event_int_dom_mono)

lemma int_tf_once_for_mono:
  "s1 <= s2 \<Longrightarrow> apply_tf (int_tf_once_for gs) a s1 <= apply_tf (int_tf_once_for gs) a s2"
  by (cases a)
     (auto simp: int_tf_once_for_def assign_int_dom_mono special_int_dom_mono
                 int_dom_backward_once.branch_mono skip_int_dom_mono body_int_dom_mono
                 return_int_dom_mono enter_int_dom_for_mono event_int_dom_mono)

end
