theory Int_Transfer
  imports Int_Backward Int_Warrowing Sign_Special Parity_Special
    "Voblint_Framework.DG_Local_State_Spec" "Voblint_VIMP.VIMP_Globals"
begin

section \<open>Composite integer-domain transfer functions\<close>

text \<open>
  Registers the composite Sign/Interval/Parity/Congruence domain against the
  framework's transfer contract (\<^locale>\<open>sound_transfer_for\<close>), mirroring
  Interval's and Sign's own registrations. One registration covers all three
  refinement modes, since every operation already takes \<open>mode\<close> as an argument
  and \<open>branch_int_dom_for\<close> dispatches the one whose name does not.

  What stays asymmetric is monotonicity: \<open>Int_Backward\<close> put
  \<open>Refine_Fixpoint\<close> on the weaker \<^locale>\<open>backward_domain\<close> locale (no
  monotonicity theorem for \<open>refine_fix\<close>), so only \<open>Never\<close> and \<open>Once\<close>
  get a monotonicity lemma below.
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
  \<open>branch_int_dom_*\<close> is the composite domain's Goblint-aligned branch
  operation per mode: a forward \<open>int_dom_tobool\<close> feasibility check ahead of
  \<open>bfilter_int_dom_*\<close>, proved once generically as
  @{thm [source] backward_domain.branch_sound}.
\<close>

lemma branch_int_dom_never_sound:
  "s \<in> \<lbrakk>\<sigma>\<rbrakk> \<Longrightarrow> truthy(aval b s) = res \<Longrightarrow> s \<in> \<lbrakk>branch_int_dom_never b res \<sigma>\<rbrakk>"
  using int_dom_backward_never.branch_sound by simp

lemma branch_int_dom_once_sound:
  "s \<in> \<lbrakk>\<sigma>\<rbrakk> \<Longrightarrow> truthy(aval b s) = res \<Longrightarrow> s \<in> \<lbrakk>branch_int_dom_once b res \<sigma>\<rbrakk>"
  using int_dom_backward_once.branch_sound by simp

text \<open>
  \<open>branch_int_dom_fixpoint\<close>'s own soundness (\<open>branch_int_dom_fixpoint_sound\<close>)
  is proved directly in \<open>Int_Backward.thy\<close>, next to its definition: unlike
  \<open>Never\<close>/\<open>Once\<close>, \<open>Refine_Fixpoint\<close> names an explicitly local raw
  feasible-gated-\<open>bfilter\<close> pair rather than the shared, pollution-fixed
  \<open>branch\<close>, so there is no generic \<open>backward_domain.branch_sound\<close> instance
  to reuse here.
\<close>

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
  "enter_frame_int_dom_for gs = enter_frame gs (top :: int_dom)"

definition enter_int_dom_for ::
    "refine_mode => (vname => bool) => vname list => exp list =>
      int_dom abs_state => int_dom abs_state" where
  "enter_int_dom_for mode gs = enter_binding gs (top :: int_dom) (aval_int_dom mode)"

lemma enter_frame_int_dom_for_sound:
  assumes gs: "s \<in> \<lbrakk>\<sigma>\<rbrakk>"
  shows "enter_state cls s \<in> \<lbrakk>enter_frame_int_dom_for cls \<sigma>\<rbrakk>"
  unfolding enter_frame_int_dom_for_def
proof (rule enter_frame_sound[OF gs])
  show "gamma (top :: int_dom) = UNIV" by (simp add: gamma_int_dom_top)
qed

lemma enter_int_dom_for_sound:
  assumes gs: "s \<in> \<lbrakk>\<sigma>\<rbrakk>"
  shows "bind_formals xs (map (\<lambda>e. aval e s) es) (enter_state cls s)
           \<in> \<lbrakk>enter_int_dom_for mode cls xs es \<sigma>\<rbrakk>"
  unfolding enter_int_dom_for_def enter_binding_concrete[symmetric]
proof (rule enter_binding_sound[OF gs])
  show "gamma (top :: int_dom) = UNIV" by (simp add: gamma_int_dom_top)
next
  fix e
  have V: "\<forall>y. s y \<in> gamma_int_dom (\<sigma> y)"
    using gs unfolding gamma_state_def by simp
  show "aval e s \<in> gamma (aval_int_dom mode e \<sigma>)"
    using V by (simp add: aval_int_dom_sound)
qed

lemma enter_frame_int_dom_for_mono:
  assumes "s1 <= s2"
  shows "enter_frame_int_dom_for gs s1 <= enter_frame_int_dom_for gs s2"
  unfolding enter_frame_int_dom_for_def by (rule enter_frame_mono[OF assms])

lemma enter_int_dom_for_mono:
  assumes "mode ~= Refine_Fixpoint" and "s1 <= s2"
  shows "enter_int_dom_for mode gs xs es s1 <= enter_int_dom_for mode gs xs es s2"
  unfolding enter_int_dom_for_def
proof (rule enter_binding_mono[OF assms(2)])
  fix e
  show "aval_int_dom mode e s1 <= aval_int_dom mode e s2"
    using assms by (simp add: aval_int_dom_mono)
qed

definition enter_int_dom_ci_for ::
    "refine_mode => (vname => bool) => call_info => int_dom abs_state => int_dom abs_state" where
  "enter_int_dom_ci_for mode gs ci = enter_int_dom_for mode gs (ci_formals ci) (ci_args ci)"

lemma enter_int_dom_ci_for_sound:
  assumes gs: "s \<in> \<lbrakk>\<sigma>\<rbrakk>"
  shows "bind_formals (ci_formals ci) (map (\<lambda>e. aval e s) (ci_args ci)) (enter_state cls s)
           \<in> \<lbrakk>enter_int_dom_ci_for mode cls ci \<sigma>\<rbrakk>"
  using enter_int_dom_for_sound[OF gs, where xs = "ci_formals ci" and es = "ci_args ci"
      and mode = mode]
  by (simp add: enter_int_dom_ci_for_def)

lemma enter_int_dom_ci_for_mono:
  assumes "mode ~= Refine_Fixpoint" and "s1 <= s2"
  shows "enter_int_dom_ci_for mode gs ci s1 <= enter_int_dom_ci_for mode gs ci s2"
  using enter_int_dom_for_mono[OF assms, of gs "ci_formals ci" "ci_args ci"]
  by (simp add: enter_int_dom_ci_for_def)

subsection \<open>Registered transfer operations, one set per refinement mode\<close>

text \<open>The branch operation is the only one whose name differs per mode, so it gets
  its own dispatcher; everything else already takes \<open>mode\<close> as an argument.\<close>

fun branch_int_dom_for ::
    "refine_mode => exp => bool => int_dom abs_state => int_dom abs_state" where
  "branch_int_dom_for Refine_Never = branch_int_dom_never"
| "branch_int_dom_for Refine_Once = branch_int_dom_once"
| "branch_int_dom_for Refine_Fixpoint = branch_int_dom_fixpoint"

lemma int_is_sound_transfer_for:
  "sound_transfer_for gs skip_int_dom (assign_int_dom mode) (special_int_dom mode)
     (branch_int_dom_for mode) body_int_dom (return_int_dom mode)
     (enter_int_dom_ci_for mode gs) event_int_dom"
  apply unfold_locales
  subgoal by (simp add: assign_int_dom_sound)
  subgoal by (simp add: special_int_dom_sound)
  subgoal by (cases mode)
       (simp_all add: branch_int_dom_never_sound branch_int_dom_once_sound
          branch_int_dom_fixpoint_sound)
  subgoal by (simp add: skip_int_dom_sound)
  subgoal by (simp add: body_int_dom_sound)
  subgoal by (simp add: return_int_dom_sound)
  subgoal by (simp add: enter_int_dom_ci_for_sound)
  subgoal by (simp add: event_int_dom_sound)
  done

definition int_tf_abs ::
    "refine_mode => edge_action => int_dom abs_state => int_dom abs_state" where
  "int_tf_abs mode = local_spec_step skip_int_dom (assign_int_dom mode) (special_int_dom mode)
     (branch_int_dom_for mode) body_int_dom (return_int_dom mode) event_int_dom"

lemma int_tf_abs_simps [simp]:
  "int_tf_abs mode EA_Nop = skip_int_dom"
  "int_tf_abs mode (EA_Assign x e) = assign_int_dom mode x e"
  "int_tf_abs mode (EA_Special sc y) = special_int_dom mode sc y"
  "int_tf_abs mode (EA_Assume b) = branch_int_dom_for mode b True"
  "int_tf_abs mode (EA_AssumeNot b) = branch_int_dom_for mode b False"
  "int_tf_abs mode (EA_Body p) = body_int_dom p"
  "int_tf_abs mode (EA_Ret eo p) = return_int_dom mode eo p"
  "int_tf_abs mode (EA_Check c) = event_int_dom (Check_Event c)"
  by (simp_all add: int_tf_abs_def)

text \<open>
  Monotonicity is available for \<open>Never\<close> and \<open>Once\<close>: every operation
  behind them (\<open>assign_int_dom\<close>, \<open>special_int_dom\<close>, \<open>return_int_dom\<close>,
  \<open>enter_int_dom_for\<close>) is monotone once \<open>mode \<noteq> Refine_Fixpoint\<close>, and
  \<open>Int_Backward\<close>'s \<open>backward_domain_refined\<close> interpretation gives
  \<open>bfilter_int_dom_never\<close>/\<open>bfilter_int_dom_once\<close> their own monotonicity
  (\<open>bfilter_mono\<close>). \<open>bfilter_int_dom_fixpoint\<close> has no such theorem --
  \<open>Int_Backward\<close> interpreted \<open>Refine_Fixpoint\<close> against the weaker
  \<^locale>\<open>backward_domain\<close> locale precisely because \<open>refine_fix\<close> lacks one --
  so \<open>Refine_Fixpoint\<close> gets no matching monotonicity lemma here. The same
  gap means \<open>Never\<close>/\<open>Once\<close> alone get the pollution-fixed, shared \<open>branch\<close>
  (\<open>branch_int_dom_never\<close>/\<open>_once\<close>, backed by
  \<^theory>\<open>Voblint_Analysis.Exec_Backward\<close>'s \<open>bfilter_st_lift_correct\<close>, itself
  only proved for \<^locale>\<open>backward_domain_refined\<close>): \<open>Refine_Fixpoint\<close>
  instead names its own, explicitly local \<open>branch_int_dom_fixpoint\<close>
  (\<open>Int_Backward.thy\<close>), since there is no executable correspondence theorem
  to route the shared one's dispatch through for this mode.
\<close>

lemma int_tf_abs_never_mono:
  "s1 <= s2 \<Longrightarrow> int_tf_abs Refine_Never a s1 <= int_tf_abs Refine_Never a s2"
  by (cases a)
     (auto simp: assign_int_dom_mono special_int_dom_mono
                 int_dom_backward_never.branch_mono skip_int_dom_mono
                 body_int_dom_mono return_int_dom_mono
                 event_int_dom_mono)

lemma int_tf_abs_once_mono:
  "s1 <= s2 \<Longrightarrow> int_tf_abs Refine_Once a s1 <= int_tf_abs Refine_Once a s2"
  by (cases a)
     (auto simp: assign_int_dom_mono special_int_dom_mono
                 int_dom_backward_once.branch_mono skip_int_dom_mono
                 body_int_dom_mono return_int_dom_mono
                 event_int_dom_mono)


end
