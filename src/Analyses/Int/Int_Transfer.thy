theory Int_Transfer
  imports
    Int_Backward
    Int_Warrowing
    "Voblint_Analysis_Sign.Sign_Special"
    "Voblint_Analysis_Parity.Parity_Special"
    "Voblint_Nonrelational.Nonrelational_Transfer"
    "Voblint_VIMP.VIMP_Globals"
begin

section \<open>Composite integer-domain transfer functions\<close>

text \<open>
  The composite Sign/Interval/Parity/Congruence domain is one
  \<^type>\<open>nonrelational_ops\<close> bundle per refinement mode, \<open>int_dom_ops mode\<close>, and
  one interpretation of \<^locale>\<open>sound_nonrelational_ops\<close> parametric in the mode
  derives the filters, the branch, the check classifier and every transfer
  function from it. This theory states only what is Int's own: the \<open>min\<close>/\<open>max\<close>
  primitives, the special-call dispatch, and the certificates.

  What stays asymmetric is monotonicity: \<open>refine_fix\<close> has no monotonicity theorem,
  so the interpretation is the sound one, and \<open>int_dom_mono_ops\<close> certifies the
  monotone bundle for \<open>Refine_Never\<close> and \<open>Refine_Once\<close> only.
\<close>

subsection \<open>Min/Max special-call primitives\<close>

text \<open>
  Sign, Interval, and Parity each already implement a real \<open>min\<close>/\<open>max\<close>
  primitive for the \<open>Nondet_Int\<close>/\<open>Min\<close>/\<open>Max\<close> special-call dispatch
  (\<open>sign_min\<close>/\<open>sign_max\<close>, \<open>ivl_min\<close>/\<open>ivl_max\<close>,
  \<open>parity_min\<close>/\<open>parity_max\<close>). Congruence has no such primitive: the
  congruence class of a \<open>min\<close>/\<open>max\<close> result is not determined by the
  operands' congruence classes in general, so the congruence component stays
  \<open>top\<close> -- conservative, matching Congruence's own choice for \<open>narrow\<close> in
  \<^theory>\<open>Voblint_Analysis_Congruence.Congruence_Warrowing\<close>. Mode-aware refinement then
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

definition int_dom_special_ops :: "refine_mode \<Rightarrow> int_dom special_ops" where
  "int_dom_special_ops mode =
     \<lparr> special_min = int_dom_min mode, special_max = int_dom_max mode \<rparr>"

lemma int_dom_special_ops_simps [simp]:
  "special_min (int_dom_special_ops mode) = int_dom_min mode"
  "special_max (int_dom_special_ops mode) = int_dom_max mode"
  by (simp_all add: int_dom_special_ops_def)

lemma int_dom_sound_special_ops: "sound_minmax_ops (int_dom_special_ops mode) (aval_int_dom mode)"
  by (intro sound_minmax_ops.intro int_dom_sound_evaluator sound_minmax_ops_axioms.intro)
     (simp_all add: int_dom_min_sound int_dom_max_sound)

lemma int_dom_mono_special_ops:
  assumes "mode \<noteq> Refine_Fixpoint"
  shows "mono_minmax_ops (int_dom_special_ops mode) (aval_int_dom mode)"
  by (intro mono_minmax_ops.intro int_dom_sound_special_ops int_dom_mono_evaluator[OF assms]
        mono_minmax_ops_axioms.intro)
     (simp_all add: int_dom_min_mono int_dom_max_mono assms)

lemma special_int_dom_eq_transfer:
  "sound_minmax_ops.special_transfer (int_dom_special_ops mode) (aval_int_dom mode) sc x \<sigma>
     = special_int_dom mode sc x \<sigma>"
  by (cases sc)
     (simp_all add: sound_minmax_ops.special_transfer_def[OF int_dom_sound_special_ops])

subsection \<open>The bundle, per refinement mode, and its certificates\<close>

text \<open>
  One bundle parametric in the mode: the evaluator, the special calls and the
  refinement operations carry it, the queries and the whole-value element do
  not. Every mode is sound; only \<open>Refine_Never\<close> and \<open>Refine_Once\<close> are monotone,
  because \<open>refine_fix\<close> has no monotonicity theorem (\<open>Int_Refinement\<close>).
\<close>

definition int_dom_ops :: "refine_mode \<Rightarrow> int_dom nonrelational_ops" where
  "int_dom_ops mode =
     \<lparr> n_aval = aval_int_dom mode, n_query = \<lparr>q_less = int_less, q_eq = int_eq\<rparr>,
       n_refine = int_refine_ops mode, n_special = int_dom_special_ops mode \<rparr>"

lemma int_dom_ops_simps [simp]:
  "n_aval (int_dom_ops mode) = aval_int_dom mode"
  "q_less (n_query (int_dom_ops mode)) = int_less"
  "q_eq (n_query (int_dom_ops mode)) = int_eq"
  "n_refine (int_dom_ops mode) = int_refine_ops mode"
  "n_special (int_dom_ops mode) = int_dom_special_ops mode"
  by (simp_all add: int_dom_ops_def)

lemma int_check_domain:
  "sound_check_query int_less int_eq gamma_state (aval_int_dom mode)"
  by (intro sound_check_query.intro int_dom_numeric_queries.sound_numeric_queries_axioms
        int_dom_sound_evaluator)

lemma int_dom_sound_ops: "sound_nonrelational_ops (int_dom_ops mode)"
  by (rule sound_nonrelational_opsI; unfold int_dom_ops_simps int_refine_ops_simps)
     (rule int_dom_sound_special_ops int_backward_domain int_check_domain)+

lemma int_dom_mono_ops:
  assumes "mode \<noteq> Refine_Fixpoint"
  shows "mono_nonrelational_ops (int_dom_ops mode)"
  by (rule mono_nonrelational_opsI; unfold int_dom_ops_simps int_refine_ops_simps)
     (rule int_dom_mono_special_ops[OF assms] int_dom_backward_domain_mono[OF assms]
        int_check_domain)+

global_interpretation int_tf: sound_nonrelational_ops "int_dom_ops mode"
  rewrites "sound_minmax_ops.special_transfer (n_special (int_dom_ops mode)) (n_aval (int_dom_ops mode))
           = special_int_dom mode"
  defines assign_int_dom = int_tf.assign
    and skip_int_dom = int_tf.skip
    and body_int_dom = int_tf.body
    and event_int_dom = int_tf.event
    and return_int_dom = int_tf.ret
    and enter_frame_int_dom_for = int_tf.enter_frame_for
    and enter_int_dom_for = int_tf.enter_for
    and enter_int_dom_ci_for = int_tf.enter_ci_for
    and int_tf_abs = int_tf.tf_abs
    and afilter_int_dom = int_tf.backward.afilter
    and feasible_int_dom = int_tf.backward.feasible
    and bfilter_int_dom = int_tf.backward.bfilter
    and branch_int_dom_for = int_tf.backward.branch
    and bfilter_lifted_int_dom = int_tf.backward.bfilter_lifted
    and branch_lifted_int_dom = int_tf.backward.branch_lifted
    and int_truthy_query = int_tf.check.truthy_query
    and int_check_query = int_tf.check.check_query
    and int_classify_check = int_tf.check.classify_check
    and int_eval_answer = int_tf.check.eval_answer
    and int_checks_proven = int_tf.check.abstract_checks_proven
  by (rule int_dom_sound_ops) (simp_all add: special_int_dom_eq_transfer fun_eq_iff)


text \<open>
  The theorems stay under \<open>int_tf.\<close>: \<^const>\<open>skip_int_dom\<close>'s soundness is
  \<open>int_tf.skip_sound\<close>, the branch's is \<open>int_tf.backward.branch_sound\<close>, and the framework's
  transfer contract at every mode is \<open>int_tf.is_sound_nonrelational_transfer\<close>.
\<close>

end
