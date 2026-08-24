theory Int_Transfer
  imports Int_Backward Int_Warrowing Sign_Special Parity_Special
    Voblint_Core.Constraint_System "Voblint_VIMP.VIMP_Globals"
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
  "s \<in> \<lbrakk>\<sigma>\<rbrakk> \<Longrightarrow> truthy (taval_syn \<Gamma> b s) = res \<Longrightarrow> styped \<Gamma> s \<Longrightarrow>
   wt_exp \<Gamma> b (opk (esyn \<Gamma> b)) \<Longrightarrow> s \<in> \<lbrakk>bfilter_int_dom_never \<Gamma> b res \<sigma>\<rbrakk>"
  using int_dom_backward_never.bfilter_sound by simp

lemma bfilter_int_dom_once_sound:
  "s \<in> \<lbrakk>\<sigma>\<rbrakk> \<Longrightarrow> truthy (taval_syn \<Gamma> b s) = res \<Longrightarrow> styped \<Gamma> s \<Longrightarrow>
   wt_exp \<Gamma> b (opk (esyn \<Gamma> b)) \<Longrightarrow> s \<in> \<lbrakk>bfilter_int_dom_once \<Gamma> b res \<sigma>\<rbrakk>"
  using int_dom_backward_once.bfilter_sound by simp

lemma bfilter_int_dom_fixpoint_sound:
  "s \<in> \<lbrakk>\<sigma>\<rbrakk> \<Longrightarrow> truthy (taval_syn \<Gamma> b s) = res \<Longrightarrow> styped \<Gamma> s \<Longrightarrow>
   wt_exp \<Gamma> b (opk (esyn \<Gamma> b)) \<Longrightarrow> s \<in> \<lbrakk>bfilter_int_dom_fixpoint \<Gamma> b res \<sigma>\<rbrakk>"
  using int_dom_backward_fixpoint.bfilter_sound by simp

text \<open>
  \<open>branch_int_dom_*\<close> is the composite domain's Goblint-aligned \<open>tf_branch\<close>
  instance per mode: a forward \<open>int_dom_tobool\<close> feasibility check ahead of
  \<open>bfilter_int_dom_*\<close>, proved once generically as
  @{thm [source] backward_domain.branch_sound}.
\<close>

lemma branch_int_dom_never_sound:
  "s \<in> \<lbrakk>\<sigma>\<rbrakk> \<Longrightarrow> truthy (taval_syn \<Gamma> b s) = res \<Longrightarrow> styped \<Gamma> s \<Longrightarrow>
   wt_exp \<Gamma> b (opk (esyn \<Gamma> b)) \<Longrightarrow> s \<in> \<lbrakk>branch_int_dom_never \<Gamma> b res \<sigma>\<rbrakk>"
  using int_dom_backward_never.branch_sound by simp

lemma branch_int_dom_once_sound:
  "s \<in> \<lbrakk>\<sigma>\<rbrakk> \<Longrightarrow> truthy (taval_syn \<Gamma> b s) = res \<Longrightarrow> styped \<Gamma> s \<Longrightarrow>
   wt_exp \<Gamma> b (opk (esyn \<Gamma> b)) \<Longrightarrow> s \<in> \<lbrakk>branch_int_dom_once \<Gamma> b res \<sigma>\<rbrakk>"
  using int_dom_backward_once.branch_sound by simp

lemma branch_int_dom_fixpoint_sound:
  "s \<in> \<lbrakk>\<sigma>\<rbrakk> \<Longrightarrow> truthy (taval_syn \<Gamma> b s) = res \<Longrightarrow> styped \<Gamma> s \<Longrightarrow>
   wt_exp \<Gamma> b (opk (esyn \<Gamma> b)) \<Longrightarrow> s \<in> \<lbrakk>branch_int_dom_fixpoint \<Gamma> b res \<sigma>\<rbrakk>"
  using int_dom_backward_fixpoint.branch_sound by simp

subsection \<open>Abstract assignment\<close>

text \<open>
  \<open>assign_int_dom\<close> casts to the destination's own declared kind via
  \<^const>\<open>int_dom_cast\<close>, evaluating the right-hand side with
  \<^const>\<open>taval_int_dom\<close> at its synthesized kind -- the same double-cast
  shape \<open>assign_sign\<close>/\<open>assign_ivl\<close> use, needed to match
  \<open>sound_transfer_for\<close>'s \<open>tf_sound_assign_for\<close> obligation
  (\<open>ik_norm (\<Gamma> x) (taval_syn \<Gamma> a s)\<close>) rather than the untyped \<open>aval_int_dom\<close>.
\<close>
definition assign_int_dom ::
    "tyenv => refine_mode => vname => exp => (vname => int_dom) => (vname => int_dom)"
where
  "assign_int_dom \<Gamma> mode x a \<sigma> =
     \<sigma>(x := int_dom_cast (\<Gamma> x) (taval_int_dom \<Gamma> mode (opk (esyn \<Gamma> a)) a \<sigma>))"

lemma assign_int_dom_sound:
  assumes gs: "s \<in> \<lbrakk>\<sigma>\<rbrakk>"
  shows "s(x := ik_norm (\<Gamma> x) (taval_syn \<Gamma> a s)) \<in> \<lbrakk>assign_int_dom \<Gamma> mode x a \<sigma>\<rbrakk>"
  unfolding assign_int_dom_def gamma_state_def
proof safe
  fix y
  from gs have V: "\<forall>z. s z \<in> gamma_int_dom (\<sigma> z)"
    using gamma_stateD[OF gs] by simp
  have av: "taval \<Gamma> (opk (esyn \<Gamma> a)) a s \<in> gamma_int_dom (taval_int_dom \<Gamma> mode (opk (esyn \<Gamma> a)) a \<sigma>)"
    using taval_int_dom_sound[OF V] .
  show "(s(x := ik_norm (\<Gamma> x) (taval_syn \<Gamma> a s))) y
          \<in> gamma ((\<sigma>(x := int_dom_cast (\<Gamma> x) (taval_int_dom \<Gamma> mode (opk (esyn \<Gamma> a)) a \<sigma>))) y)"
  proof (cases "y = x")
    case True
    have "ik_norm (\<Gamma> x) (taval \<Gamma> (opk (esyn \<Gamma> a)) a s)
            \<in> gamma_int_dom (int_dom_cast (\<Gamma> x) (taval_int_dom \<Gamma> mode (opk (esyn \<Gamma> a)) a \<sigma>))"
      by (rule int_dom_cast_sound[OF av])
    with True show ?thesis by (simp add: taval_syn_def)
  next
    case False
    with V show ?thesis by simp
  qed
qed

lemma assign_int_dom_mono:
  assumes "mode ~= Refine_Fixpoint" and "sigma1 <= sigma2"
  shows "assign_int_dom \<Gamma> mode x a sigma1 <= assign_int_dom \<Gamma> mode x a sigma2"
  using assms
  by (simp add: assign_int_dom_def taval_int_dom_mono le_funD le_funI int_dom_cast_mono)

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

text \<open>
  \<open>special_int_dom\<close> evaluates \<open>Min\<close>/\<open>Max\<close>'s two operands with
  \<^const>\<open>taval_int_dom\<close> at their shared synthesized kind (mirroring
  \<^const>\<open>special_result\<close> and \<open>Special_Ops.special_transfer\<close> exactly), then casts
  the combined result to the destination \<open>x\<close>'s own declared kind via
  \<^const>\<open>int_dom_cast\<close> -- the same double-cast shape \<open>assign_int_dom\<close> uses.
\<close>
fun special_int_dom ::
    "tyenv => refine_mode => special_call => vname => (vname => int_dom) => (vname => int_dom)"
where
  "special_int_dom \<Gamma> mode Nondet_Int x \<sigma> = \<sigma>(x := top)"
| "special_int_dom \<Gamma> mode (Min a b) x \<sigma> =
     (let k = opk (kjoin (esyn \<Gamma> a) (esyn \<Gamma> b))
      in \<sigma>(x := int_dom_cast (\<Gamma> x)
             (int_dom_min mode (taval_int_dom \<Gamma> mode k a \<sigma>) (taval_int_dom \<Gamma> mode k b \<sigma>))))"
| "special_int_dom \<Gamma> mode (Max a b) x \<sigma> =
     (let k = opk (kjoin (esyn \<Gamma> a) (esyn \<Gamma> b))
      in \<sigma>(x := int_dom_cast (\<Gamma> x)
             (int_dom_max mode (taval_int_dom \<Gamma> mode k a \<sigma>) (taval_int_dom \<Gamma> mode k b \<sigma>))))"

lemma gamma_int_dom_top: "gamma_int_dom (top :: int_dom) = UNIV"
  by (simp add: gamma_int_dom_def top_int_dom_ext_def top_ivl_def
        gamma_sign_top gamma_ivl_top gamma_parity_top)

lemma special_int_dom_sound:
  assumes gs: "s \<in> \<lbrakk>\<sigma>\<rbrakk>" and sr: "special_result \<Gamma> sc s v"
  shows "s(x := ik_norm (\<Gamma> x) v) \<in> \<lbrakk>special_int_dom \<Gamma> mode sc x \<sigma>\<rbrakk>"
proof (cases sc)
  case Nondet_Int
  show ?thesis
    unfolding Nondet_Int gamma_state_def
    using gs unfolding gamma_state_def
    by (simp add: gamma_int_dom_top)
next
  case (Min a b)
  let ?k = "opk (kjoin (esyn \<Gamma> a) (esyn \<Gamma> b))"
  have V: "\<forall>y. s y \<in> gamma_int_dom (\<sigma> y)"
    using gs unfolding gamma_state_def by simp
  have Va: "taval \<Gamma> ?k a s : gamma_int_dom (taval_int_dom \<Gamma> mode ?k a \<sigma>)"
    by (rule taval_int_dom_sound[OF V])
  have Vb: "taval \<Gamma> ?k b s : gamma_int_dom (taval_int_dom \<Gamma> mode ?k b \<sigma>)"
    by (rule taval_int_dom_sound[OF V])
  have v: "v = min (taval \<Gamma> ?k a s) (taval \<Gamma> ?k b s)"
    using sr unfolding Min by (simp add: Let_def)
  have vmem: "v : gamma_int_dom (int_dom_min mode (taval_int_dom \<Gamma> mode ?k a \<sigma>) (taval_int_dom \<Gamma> mode ?k b \<sigma>))"
    unfolding v by (rule int_dom_min_sound[OF Va Vb])
  have "ik_norm (\<Gamma> x) v
          : gamma_int_dom (int_dom_cast (\<Gamma> x)
              (int_dom_min mode (taval_int_dom \<Gamma> mode ?k a \<sigma>) (taval_int_dom \<Gamma> mode ?k b \<sigma>)))"
    by (rule int_dom_cast_sound[OF vmem])
  then show ?thesis
    unfolding Min gamma_state_def using V by (auto simp: gamma_int_dom_def Let_def)
next
  case (Max a b)
  let ?k = "opk (kjoin (esyn \<Gamma> a) (esyn \<Gamma> b))"
  have V: "\<forall>y. s y \<in> gamma_int_dom (\<sigma> y)"
    using gs unfolding gamma_state_def by simp
  have Va: "taval \<Gamma> ?k a s : gamma_int_dom (taval_int_dom \<Gamma> mode ?k a \<sigma>)"
    by (rule taval_int_dom_sound[OF V])
  have Vb: "taval \<Gamma> ?k b s : gamma_int_dom (taval_int_dom \<Gamma> mode ?k b \<sigma>)"
    by (rule taval_int_dom_sound[OF V])
  have v: "v = max (taval \<Gamma> ?k a s) (taval \<Gamma> ?k b s)"
    using sr unfolding Max by (simp add: Let_def)
  have vmem: "v : gamma_int_dom (int_dom_max mode (taval_int_dom \<Gamma> mode ?k a \<sigma>) (taval_int_dom \<Gamma> mode ?k b \<sigma>))"
    unfolding v by (rule int_dom_max_sound[OF Va Vb])
  have "ik_norm (\<Gamma> x) v
          : gamma_int_dom (int_dom_cast (\<Gamma> x)
              (int_dom_max mode (taval_int_dom \<Gamma> mode ?k a \<sigma>) (taval_int_dom \<Gamma> mode ?k b \<sigma>)))"
    by (rule int_dom_cast_sound[OF vmem])
  then show ?thesis
    unfolding Max gamma_state_def using V by (auto simp: gamma_int_dom_def Let_def)
qed

lemma special_int_dom_mono:
  assumes mode: "mode ~= Refine_Fixpoint" and le: "sigma1 <= sigma2"
  shows "special_int_dom \<Gamma> mode sc x sigma1 <= special_int_dom \<Gamma> mode sc x sigma2"
proof (cases sc)
  case Nondet_Int
  then show ?thesis
    using le by (auto simp: le_fun_def)
next
  case (Min a b)
  let ?k = "opk (kjoin (esyn \<Gamma> a) (esyn \<Gamma> b))"
  have A: "taval_int_dom \<Gamma> mode ?k a sigma1 <= taval_int_dom \<Gamma> mode ?k a sigma2"
    using mode le by (rule taval_int_dom_mono)
  have B: "taval_int_dom \<Gamma> mode ?k b sigma1 <= taval_int_dom \<Gamma> mode ?k b sigma2"
    using mode le by (rule taval_int_dom_mono)
  have M: "int_dom_min mode (taval_int_dom \<Gamma> mode ?k a sigma1) (taval_int_dom \<Gamma> mode ?k b sigma1)
          <= int_dom_min mode (taval_int_dom \<Gamma> mode ?k a sigma2) (taval_int_dom \<Gamma> mode ?k b sigma2)"
    by (rule int_dom_min_mono[OF mode A B])
  have C: "int_dom_cast (\<Gamma> x)
             (int_dom_min mode (taval_int_dom \<Gamma> mode ?k a sigma1) (taval_int_dom \<Gamma> mode ?k b sigma1))
          <= int_dom_cast (\<Gamma> x)
             (int_dom_min mode (taval_int_dom \<Gamma> mode ?k a sigma2) (taval_int_dom \<Gamma> mode ?k b sigma2))"
    by (rule int_dom_cast_mono[OF M])
  show ?thesis
    unfolding Min using le C by (auto simp: le_fun_def Let_def)
next
  case (Max a b)
  let ?k = "opk (kjoin (esyn \<Gamma> a) (esyn \<Gamma> b))"
  have A: "taval_int_dom \<Gamma> mode ?k a sigma1 <= taval_int_dom \<Gamma> mode ?k a sigma2"
    using mode le by (rule taval_int_dom_mono)
  have B: "taval_int_dom \<Gamma> mode ?k b sigma1 <= taval_int_dom \<Gamma> mode ?k b sigma2"
    using mode le by (rule taval_int_dom_mono)
  have M: "int_dom_max mode (taval_int_dom \<Gamma> mode ?k a sigma1) (taval_int_dom \<Gamma> mode ?k b sigma1)
          <= int_dom_max mode (taval_int_dom \<Gamma> mode ?k a sigma2) (taval_int_dom \<Gamma> mode ?k b sigma2)"
    by (rule int_dom_max_mono[OF mode A B])
  have C: "int_dom_cast (\<Gamma> x)
             (int_dom_max mode (taval_int_dom \<Gamma> mode ?k a sigma1) (taval_int_dom \<Gamma> mode ?k b sigma1))
          <= int_dom_cast (\<Gamma> x)
             (int_dom_max mode (taval_int_dom \<Gamma> mode ?k a sigma2) (taval_int_dom \<Gamma> mode ?k b sigma2))"
    by (rule int_dom_cast_mono[OF M])
  show ?thesis
    unfolding Max using le C by (auto simp: le_fun_def Let_def)
qed

subsection \<open>Skip, body-entry, return, and event\<close>

text \<open>Composite \<open>int_dom\<close> has no lifecycle-specific abstract information,
  mirroring every other current domain: \<open>skip\<^sup>#\<close>/\<open>body\<^sup>#\<close>/\<open>event\<^sup>#\<close> are
  the identity. \<open>return\<^sup>#\<close> cannot reuse \<open>assign_int_dom\<close>:
  \<^const>\<open>apply_tf\<close>'s \<open>EA_Ret\<close> case does not pass the edge's own baked
  return kind \<open>rk\<close> through to \<open>tf_return\<close> at all (\<open>sound_transfer_for\<close>'s
  \<open>tf_sound_return_for\<close> quantifies over every \<open>rk\<close> universally), so
  \<open>return\<^sup>#\<close>'s single output must already be sound for whichever \<open>rk\<close> the
  compiled edge actually used -- unlike an ordinary assignment, there is no
  declared kind here to cast against, only an unknown one, so \<open>ret_var\<close>
  widens to the composite \<^const>\<open>top\<close> whenever the return carries a value.\<close>

definition skip_int_dom :: "(vname => int_dom) => (vname => int_dom)" where
  "skip_int_dom \<sigma> = \<sigma>"

definition body_int_dom :: "pname => (vname => int_dom) => (vname => int_dom)" where
  "body_int_dom p \<sigma> = \<sigma>"

definition event_int_dom :: "analysis_event => (vname => int_dom) => (vname => int_dom)" where
  "event_int_dom ev \<sigma> = \<sigma>"

definition return_int_dom ::
    "exp option => pname => (vname => int_dom) => (vname => int_dom)"
where
  "return_int_dom e p \<sigma> = (case e of None \<Rightarrow> \<sigma> | Some a \<Rightarrow> \<sigma>(ret_var := top))"

lemma skip_int_dom_sound: "s \<in> \<lbrakk>\<sigma>\<rbrakk> \<Longrightarrow> s \<in> \<lbrakk>skip_int_dom \<sigma>\<rbrakk>"
  by (simp add: skip_int_dom_def)

lemma body_int_dom_sound: "s \<in> \<lbrakk>\<sigma>\<rbrakk> \<Longrightarrow> s \<in> \<lbrakk>body_int_dom p \<sigma>\<rbrakk>"
  by (simp add: body_int_dom_def)

lemma event_int_dom_sound: "s \<in> \<lbrakk>\<sigma>\<rbrakk> \<Longrightarrow> s \<in> \<lbrakk>event_int_dom ev \<sigma>\<rbrakk>"
  by (simp add: event_int_dom_def)

lemma return_int_dom_sound:
  assumes gs: "s \<in> \<lbrakk>\<sigma>\<rbrakk>"
  shows "s(ret_var := (case e of None \<Rightarrow> s ret_var | Some a \<Rightarrow> ik_norm rk (taval_syn \<Gamma> a s)))
           \<in> \<lbrakk>return_int_dom e p \<sigma>\<rbrakk>"
  using gs unfolding gamma_state_def
  by (cases e) (auto simp: return_int_dom_def gamma_int_dom_top)

lemma skip_int_dom_mono: "sigma1 <= sigma2 \<Longrightarrow> skip_int_dom sigma1 <= skip_int_dom sigma2"
  by (simp add: skip_int_dom_def)

lemma body_int_dom_mono: "sigma1 <= sigma2 \<Longrightarrow> body_int_dom p sigma1 <= body_int_dom p sigma2"
  by (simp add: body_int_dom_def)

lemma event_int_dom_mono: "sigma1 <= sigma2 \<Longrightarrow> event_int_dom ev sigma1 <= event_int_dom ev sigma2"
  by (simp add: event_int_dom_def)

lemma return_int_dom_mono:
  "sigma1 <= sigma2 \<Longrightarrow> return_int_dom e p sigma1 <= return_int_dom e p sigma2"
  by (cases e) (simp_all add: return_int_dom_def le_fun_def)

subsection \<open>Texp-based evaluation\<close>

text \<open>
  \<open>aval_int_dom_t\<close> mirrors \<open>taval_int_dom\<close>'s own recursion exactly, node for
  node, over an already-elaborated \<^typ>\<open>texp\<close> rather than an \<open>exp\<close> paired
  with a separately-threaded \<open>ikind\<close> -- the same relationship \<open>aval_sign_t\<close>
  has to \<open>aval_sign\<close>. \<open>Numeric_Ops.numeric_ops\<close>'s \<open>n_aval\<close> field needs this
  texp-based shape for the executable mirror (\<open>Int_Exec\<close>), and
  \<^const>\<open>enter_D_typed\<close> needs it here for \<open>enter_int_dom_for\<close>, so it is
  proved sound and monotone once via the bridge to the already-proved
  \<open>taval_int_dom\<close> rather than by a second, independent induction.
\<close>
fun aval_int_dom_t :: "refine_mode => texp => (vname => int_dom) => int_dom" where
  "aval_int_dom_t mode (TN ik n) \<sigma> = int_dom_cast ik (int_dom_of_int n)"
| "aval_int_dom_t mode (TV ik x) \<sigma> = int_dom_cast ik (\<sigma> x)"
| "aval_int_dom_t mode (TPlus ik a b) \<sigma> =
     int_dom_cast ik (plus_int_dom mode (aval_int_dom_t mode a \<sigma>) (aval_int_dom_t mode b \<sigma>))"
| "aval_int_dom_t mode (TMinus ik a b) \<sigma> =
     int_dom_cast ik (minus_int_dom mode (aval_int_dom_t mode a \<sigma>) (aval_int_dom_t mode b \<sigma>))"
| "aval_int_dom_t mode (TTimes ik a b) \<sigma> =
     int_dom_cast ik (times_int_dom mode (aval_int_dom_t mode a \<sigma>) (aval_int_dom_t mode b \<sigma>))"
| "aval_int_dom_t mode (TLess a b) \<sigma> =
     (let x = aval_int_dom_t mode a \<sigma>; y = aval_int_dom_t mode b \<sigma>
      in if is_bot x \<or> is_bot y then bot else int_dom_of_bool_option (int_dom_lt x y))"
| "aval_int_dom_t mode (TEq a b) \<sigma> =
     (let x = aval_int_dom_t mode a \<sigma>; y = aval_int_dom_t mode b \<sigma>
      in if is_bot x \<or> is_bot y then bot else int_dom_of_bool_option (int_dom_eqb x y))"
| "aval_int_dom_t mode (TNot a) \<sigma> =
     (let x = aval_int_dom_t mode a \<sigma>
      in if is_bot x then bot
         else if int_dom_tobool x = Some True then int_dom_of_int 0
         else if int_dom_tobool x = Some False then int_dom_of_int 1
         else int_dom_bool_unknown)"
| "aval_int_dom_t mode (TAnd a b) \<sigma> =
     (let x = aval_int_dom_t mode a \<sigma>; y = aval_int_dom_t mode b \<sigma>
      in if is_bot x \<or> is_bot y then bot
         else if int_dom_tobool x = Some False \<or> int_dom_tobool y = Some False
         then int_dom_of_int 0
         else if int_dom_tobool x = Some True \<and> int_dom_tobool y = Some True
         then int_dom_of_int 1
         else int_dom_bool_unknown)"
| "aval_int_dom_t mode (TOr a b) \<sigma> =
     (let x = aval_int_dom_t mode a \<sigma>; y = aval_int_dom_t mode b \<sigma>
      in if is_bot x \<or> is_bot y then bot
         else if int_dom_tobool x = Some True \<or> int_dom_tobool y = Some True
         then int_dom_of_int 1
         else if int_dom_tobool x = Some False \<and> int_dom_tobool y = Some False
         then int_dom_of_int 0
         else int_dom_bool_unknown)"

lemma aval_int_dom_t_elaborate [simp]:
  "aval_int_dom_t mode (elaborate \<Gamma> ik e) \<sigma> = taval_int_dom \<Gamma> mode ik e \<sigma>"
  by (induction e arbitrary: ik) (simp_all add: Let_def)

lemma aval_int_dom_t_elaborate_syn [simp]:
  "aval_int_dom_t mode (elaborate_syn \<Gamma> e) \<sigma> = taval_int_dom \<Gamma> mode (opk (esyn \<Gamma> e)) e \<sigma>"
  by (simp add: elaborate_syn_def)

lemma aval_int_dom_t_sound:
  assumes "\<forall>x. s x \<in> gamma_int_dom (\<sigma> x)"
  shows "taval \<Gamma> ik e s \<in> gamma_int_dom (aval_int_dom_t mode (elaborate \<Gamma> ik e) \<sigma>)"
  unfolding aval_int_dom_t_elaborate using taval_int_dom_sound[OF assms] .

lemma aval_int_dom_t_mono:
  assumes "mode ~= Refine_Fixpoint" and "sigma1 <= sigma2"
  shows "aval_int_dom_t mode (elaborate \<Gamma> ik e) sigma1 <= aval_int_dom_t mode (elaborate \<Gamma> ik e) sigma2"
  unfolding aval_int_dom_t_elaborate using taval_int_dom_mono[OF assms] .

subsection \<open>Classifier-parametric procedure entry\<close>

definition enter_frame_int_dom_for ::
    "(vname => bool) => int_dom abs_state => int_dom abs_state" where
  "enter_frame_int_dom_for gs = enter_frame_D gs (top :: int_dom)"

definition enter_int_dom_for ::
    "refine_mode => (vname => bool) => tyenv => vname list => exp list =>
      int_dom abs_state => int_dom abs_state" where
  "enter_int_dom_for mode gs \<Gamma> =
     enter_D_typed gs (top :: int_dom) \<Gamma> int_dom_cast (aval_int_dom_t mode)"

lemma enter_frame_int_dom_for_sound:
  assumes gs: "s \<in> \<lbrakk>\<sigma>\<rbrakk>"
  shows "enter_state cls s \<in> \<lbrakk>enter_frame_int_dom_for cls \<sigma>\<rbrakk>"
  unfolding enter_frame_int_dom_for_def
proof (rule enter_frame_D_sound[OF gs])
  show "gamma (top :: int_dom) = UNIV" by (simp add: gamma_int_dom_top)
qed

lemma enter_int_dom_for_sound:
  assumes gs: "s \<in> \<lbrakk>\<sigma>\<rbrakk>"
  shows "bind_formals xs (map2 (\<lambda>x e. ik_norm (\<Gamma> x) (taval_syn \<Gamma> e s)) xs es) (enter_state cls s)
           \<in> \<lbrakk>enter_int_dom_for mode cls \<Gamma> xs es \<sigma>\<rbrakk>"
  unfolding enter_int_dom_for_def
proof (rule enter_D_typed_sound[OF gs])
  show "gamma (top :: int_dom) = UNIV" by (simp add: gamma_int_dom_top)
next
  fix ik v a show "v \<in> gamma a \<Longrightarrow> ik_norm ik v \<in> gamma (int_dom_cast ik a)"
    by (simp add: int_dom_cast_sound)
next
  fix ik e' s' \<sigma>' show "(\<forall>x. s' x \<in> gamma (\<sigma>' x)) \<Longrightarrow>
                          taval \<Gamma> ik e' s' \<in> gamma (aval_int_dom_t mode (elaborate \<Gamma> ik e') \<sigma>')"
    by (simp add: taval_int_dom_sound)
qed

lemma enter_frame_int_dom_for_mono:
  assumes "s1 <= s2"
  shows "enter_frame_int_dom_for gs s1 <= enter_frame_int_dom_for gs s2"
  unfolding enter_frame_int_dom_for_def by (rule enter_frame_D_mono[OF assms])

lemma enter_int_dom_for_mono:
  assumes "mode ~= Refine_Fixpoint" and "s1 <= s2"
  shows "enter_int_dom_for mode gs \<Gamma> xs es s1 <= enter_int_dom_for mode gs \<Gamma> xs es s2"
  unfolding enter_int_dom_for_def
proof (rule enter_D_typed_mono[OF assms(2)])
  show "\<And>ik a1 a2. a1 \<le> a2 \<Longrightarrow> int_dom_cast ik a1 \<le> int_dom_cast ik a2"
    by (rule int_dom_cast_mono)
next
  show "\<And>ik e' \<tau>1 \<tau>2. \<tau>1 \<le> \<tau>2 \<Longrightarrow>
          aval_int_dom_t mode (elaborate \<Gamma> ik e') \<tau>1 \<le> aval_int_dom_t mode (elaborate \<Gamma> ik e') \<tau>2"
    using assms(1) by (rule aval_int_dom_t_mono)
qed

subsection \<open>Registered transfer bundles, one per refinement mode\<close>

definition int_tf_never_for :: "(vname => bool) => tyenv => int_dom domain_transfer" where
  "int_tf_never_for gs \<Gamma> = (| tf_assign  = assign_int_dom \<Gamma> Refine_Never,
                            tf_special = special_int_dom \<Gamma> Refine_Never,
                            tf_branch  = branch_int_dom_never \<Gamma>,
                            tf_skip    = skip_int_dom,
                            tf_body    = body_int_dom,
                            tf_return  = return_int_dom,
                            tf_enter   = enter_int_dom_for Refine_Never gs \<Gamma>,
                            tf_event   = event_int_dom,
                            tf_caller_cont = (\<lambda>_ \<sigma>. \<sigma>),
                            tf_combine_env = (\<lambda>_. combine_env_abs gs) |)"

definition int_tf_once_for :: "(vname => bool) => tyenv => int_dom domain_transfer" where
  "int_tf_once_for gs \<Gamma> = (| tf_assign  = assign_int_dom \<Gamma> Refine_Once,
                           tf_special = special_int_dom \<Gamma> Refine_Once,
                           tf_branch  = branch_int_dom_once \<Gamma>,
                           tf_skip    = skip_int_dom,
                           tf_body    = body_int_dom,
                           tf_return  = return_int_dom,
                           tf_enter   = enter_int_dom_for Refine_Once gs \<Gamma>,
                           tf_event   = event_int_dom,
                           tf_caller_cont = (\<lambda>_ \<sigma>. \<sigma>),
                           tf_combine_env = (\<lambda>_. combine_env_abs gs) |)"

definition int_tf_fixpoint_for :: "(vname => bool) => tyenv => int_dom domain_transfer" where
  "int_tf_fixpoint_for gs \<Gamma> = (| tf_assign  = assign_int_dom \<Gamma> Refine_Fixpoint,
                               tf_special = special_int_dom \<Gamma> Refine_Fixpoint,
                               tf_branch  = branch_int_dom_fixpoint \<Gamma>,
                               tf_skip    = skip_int_dom,
                               tf_body    = body_int_dom,
                               tf_return  = return_int_dom,
                               tf_enter   = enter_int_dom_for Refine_Fixpoint gs \<Gamma>,
                               tf_event   = event_int_dom,
                               tf_caller_cont = (\<lambda>_ \<sigma>. \<sigma>),
                               tf_combine_env = (\<lambda>_. combine_env_abs gs) |)"

text \<open>
  The branch obligation below is unresolved: @{thm [source] branch_int_dom_never_sound}
  requires \<open>styped \<Gamma> s\<close> and \<open>wt_exp \<Gamma> b (opk (esyn \<Gamma> b))\<close>, premises that
  \<open>sound_transfer_for\<close>'s \<open>tf_sound_branch_for\<close> obligation does not supply.
  Closing this needs a well-typedness invariant threaded through the whole
  \<open>sound_transfer_for\<close> soundness chain, not a local fix to this lemma. This is
  the same gap \<open>sign_is_sound_transfer_for\<close> defers for Sign, here across all
  three refinement modes.
\<close>
lemma int_never_is_sound_transfer_for: "sound_transfer_for gs (int_tf_never_for gs \<Gamma>) \<Gamma>"
  unfolding int_tf_never_for_def
  apply unfold_locales
  subgoal by (simp add: assign_int_dom_sound)
  subgoal by (simp add: special_int_dom_sound)
  subgoal sorry
  subgoal by (simp add: skip_int_dom_sound)
  subgoal by (simp add: body_int_dom_sound)
  subgoal by (simp add: return_int_dom_sound)
  subgoal by (simp add: enter_int_dom_for_sound)
  subgoal by (simp add: event_int_dom_sound)
  subgoal by simp
  subgoal by (simp add: combine_env_sound)
  done

lemma int_once_is_sound_transfer_for: "sound_transfer_for gs (int_tf_once_for gs \<Gamma>) \<Gamma>"
  unfolding int_tf_once_for_def
  apply unfold_locales
  subgoal by (simp add: assign_int_dom_sound)
  subgoal by (simp add: special_int_dom_sound)
  subgoal sorry
  subgoal by (simp add: skip_int_dom_sound)
  subgoal by (simp add: body_int_dom_sound)
  subgoal by (simp add: return_int_dom_sound)
  subgoal by (simp add: enter_int_dom_for_sound)
  subgoal by (simp add: event_int_dom_sound)
  subgoal by simp
  subgoal by (simp add: combine_env_sound)
  done

lemma int_fixpoint_is_sound_transfer_for: "sound_transfer_for gs (int_tf_fixpoint_for gs \<Gamma>) \<Gamma>"
  unfolding int_tf_fixpoint_for_def
  apply unfold_locales
  subgoal by (simp add: assign_int_dom_sound)
  subgoal by (simp add: special_int_dom_sound)
  subgoal sorry
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
  "s1 <= s2 \<Longrightarrow>
   apply_tf (int_tf_never_for gs \<Gamma>) a s1 <= apply_tf (int_tf_never_for gs \<Gamma>) a s2"
  by (cases a)
     (auto simp: int_tf_never_for_def assign_int_dom_mono special_int_dom_mono
                 int_dom_backward_never.branch_mono skip_int_dom_mono body_int_dom_mono
                 return_int_dom_mono enter_int_dom_for_mono event_int_dom_mono)

lemma int_tf_once_for_mono:
  "s1 <= s2 \<Longrightarrow>
   apply_tf (int_tf_once_for gs \<Gamma>) a s1 <= apply_tf (int_tf_once_for gs \<Gamma>) a s2"
  by (cases a)
     (auto simp: int_tf_once_for_def assign_int_dom_mono special_int_dom_mono
                 int_dom_backward_once.branch_mono skip_int_dom_mono body_int_dom_mono
                 return_int_dom_mono enter_int_dom_for_mono event_int_dom_mono)

end
