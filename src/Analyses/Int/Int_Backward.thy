theory Int_Backward
  imports
    Int_Arithmetic
    "Voblint_Analysis_Sign.Sign_Backward"
    "Voblint_Analysis_Interval.Interval_Backward"
    "Voblint_Analysis_Congruence.Congruence_Backward"
    "Voblint_Nonrelational.Exec_Backward"
begin

section \<open>Composite integer-domain backward filtering\<close>

text \<open>
  Composite backward inversion follows the same shape as composite forward
  arithmetic (\<open>Int_Arithmetic\<close>): a raw componentwise operator, reusing
  each component's own existing inverse where one exists, then a mode-aware
  wrapper that refines the returned candidates with \<open>refine mode\<close>.

  No component here invents a new inverse operator. Sign and Interval both
  already fall back to the shared identity \<open>inv_conservative\<close> for
  \<open>+\<close>/\<open>-\<close>/\<open>*\<close> in their own theories (\<open>Sign_Backward\<close>,
  \<open>Interval_Backward\<close>); this composite reuses that same choice rather
  than inventing per-component arithmetic inversion the domains themselves
  do not have. Parity has no backward-inversion theory in the codebase at
  all, so its raw \<open>+\<close>/\<open>-\<close>/\<open>*\<close>/\<open>less\<close> candidates are likewise
  \<open>inv_conservative\<close>; its equality candidate still narrows, through the
  composite \<open>intersect_int_dom\<close> on the true branch below. Congruence
  contributes the only real arithmetic inversion (\<open>inv_plus_congruence\<close>,
  \<open>inv_minus_congruence\<close>, \<open>inv_times_congruence\<close>), matching
  \<open>Congruence_Backward\<close>.

  Precision Sign/Interval/Parity cannot recover directly at inversion time
  is not lost: the mode-aware wrapper's \<open>refine mode\<close> step re-derives
  their bounds from the (possibly Congruence-tightened) returned operand,
  exactly as \<open>refine_interval\<close>/\<open>refine_congruence\<close> already do for
  forward arithmetic.
\<close>

subsection \<open>Composite semantic intersection\<close>

definition intersect_int_dom :: "int_dom => int_dom => int_dom" where
  "intersect_int_dom d1 d2 =
     d1\<lparr>
       int_sign := intersect_sign (int_sign d1) (int_sign d2),
       int_ivl := intersect_ivl (int_ivl d1) (int_ivl d2),
       int_parity := intersect_parity (int_parity d1) (int_parity d2),
       int_congruence := intersect_congruence (int_congruence d1) (int_congruence d2)
     \<rparr>"

text \<open>
  \<open>intersect_ivl\<close>'s defining equation is globally tagged \<open>[simp]\<close>
  (\<open>Interval_Lattice\<close>), so plain \<open>simp\<close>/\<open>auto\<close> unfolds it to
  \<open>normalize_ivl (meet_ivl a b)\<close> before \<open>gamma_intersect_ivl_exact\<close> or
  \<open>intersect_ivl_le1\<close>/\<open>intersect_ivl_le2\<close>/\<open>intersect_ivl_mono\<close> -- all
  stated in terms of the abstract \<open>intersect_ivl\<close> -- get a chance to match.
  \<open>del: intersect_ivl_def\<close> below keeps \<open>intersect_ivl\<close> opaque for exactly
  those calls, matching \<open>is_bottom_int_dom_correct\<close>'s own
  \<open>simp only: gamma_intersect_ivl_exact ...\<close> workaround in
  \<open>Int_Domain\<close>.
\<close>

lemma intersect_int_dom_sound:
  assumes "n \<in> gamma_int_dom a" and "n \<in> gamma_int_dom b"
  shows "n \<in> gamma_int_dom (intersect_int_dom a b)"
proof -
  have hn: "n \<in> gamma_sign (int_sign a)" "n \<in> gamma_ivl (int_ivl a)"
           "n \<in> gamma_parity (int_parity a)" "n \<in> gamma_congruence (int_congruence a)"
    using assms(1) by (simp_all add: gamma_int_dom_def)
  have hm: "n \<in> gamma_sign (int_sign b)" "n \<in> gamma_ivl (int_ivl b)"
           "n \<in> gamma_parity (int_parity b)" "n \<in> gamma_congruence (int_congruence b)"
    using assms(2) by (simp_all add: gamma_int_dom_def)
  have ivl_fact: "n \<in> gamma_ivl (intersect_ivl (int_ivl a) (int_ivl b))"
    unfolding intersect_ivl_def
    using meet_ivl_gamma[OF hn(2) hm(2)] normalize_ivl_gamma by simp
  have sign_fact: "n \<in> gamma_sign (intersect_sign (int_sign a) (int_sign b))"
    using hn(1) hm(1) by simp
  have parity_fact: "n \<in> gamma_parity (intersect_parity (int_parity a) (int_parity b))"
    using hn(3) hm(3) by simp
  have congruence_fact:
    "n \<in> gamma_congruence (intersect_congruence (int_congruence a) (int_congruence b))"
    using hn(4) hm(4) by simp
  show ?thesis
    unfolding gamma_int_dom_def intersect_int_dom_def
    using sign_fact ivl_fact parity_fact congruence_fact
    by (simp del: intersect_ivl_def)
qed

lemma intersect_int_dom_le1: "intersect_int_dom a b \<le> a"
  unfolding intersect_int_dom_def less_eq_int_dom_ext_def
  by (simp add: intersect_sign_le1 intersect_ivl_le1
        intersect_parity_le1 intersect_congruence_le1
      del: intersect_ivl_def)

lemma intersect_int_dom_le2: "intersect_int_dom a b \<le> b"
  unfolding intersect_int_dom_def less_eq_int_dom_ext_def
  by (simp add: intersect_sign_le2 intersect_ivl_le2
        intersect_parity_le2 intersect_congruence_le2
      del: intersect_ivl_def)

lemma intersect_int_dom_mono:
  assumes "a1 \<le> a2" and "b1 \<le> b2"
  shows "intersect_int_dom a1 b1 \<le> intersect_int_dom a2 b2"
proof -
  have s: "int_sign a1 \<le> int_sign a2" "int_ivl a1 \<le> int_ivl a2"
          "int_parity a1 \<le> int_parity a2" "int_congruence a1 \<le> int_congruence a2"
    using assms(1) by (simp_all add: less_eq_int_dom_ext_def)
  have t: "int_sign b1 \<le> int_sign b2" "int_ivl b1 \<le> int_ivl b2"
          "int_parity b1 \<le> int_parity b2" "int_congruence b1 \<le> int_congruence b2"
    using assms(2) by (simp_all add: less_eq_int_dom_ext_def)
  show ?thesis
    unfolding intersect_int_dom_def less_eq_int_dom_ext_def
    by (simp add: intersect_sign_mono[OF s(1) t(1)] intersect_ivl_mono[OF s(2) t(2)]
          intersect_parity_mono[OF s(3) t(3)] intersect_congruence_mono[OF s(4) t(4)]
        del: intersect_ivl_def)
qed

definition intersect_int_dom_mode ::
    "refine_mode => int_dom => int_dom => int_dom"
where
  "intersect_int_dom_mode mode a b = refine mode (intersect_int_dom a b)"

lemma intersect_int_dom_mode_sound:
  assumes "n \<in> gamma_int_dom a" and "n \<in> gamma_int_dom b"
  shows "n \<in> gamma_int_dom (intersect_int_dom_mode mode a b)"
  unfolding intersect_int_dom_mode_def
  using intersect_int_dom_sound[OF assms] refine_exact by simp

text \<open>
  \<open>refine mode\<close> is reductive/exact for every mode (\<open>Int_Refinement\<close>)
  but only monotone off \<open>Refine_Fixpoint\<close> (\<open>Int_Arithmetic\<close>'s
  \<open>refine_nonfixpoint_mono\<close>); these two helpers compose that fact with a
  reductive/monotone step once, for \<open>intersect_int_dom_mode\<close> and the
  mode-aware inverse operators below.
\<close>

lemma refine_mode_reductive_trans:
  assumes "a \<le> d"
  shows "refine mode a \<le> d"
  using refine_reductive[of mode a] assms by (rule order_trans)

lemma refine_mode_mono_trans:
  assumes "mode \<noteq> Refine_Fixpoint" and "a \<le> b"
  shows "refine mode a \<le> refine mode b"
  using monoD[OF refine_nonfixpoint_mono[OF assms(1)] assms(2)] .

lemma intersect_int_dom_mode_reductive1:
  "intersect_int_dom_mode mode a b \<le> a"
  unfolding intersect_int_dom_mode_def
  using refine_mode_reductive_trans[OF intersect_int_dom_le1] .

lemma intersect_int_dom_mode_reductive2:
  "intersect_int_dom_mode mode a b \<le> b"
  unfolding intersect_int_dom_mode_def
  using refine_mode_reductive_trans[OF intersect_int_dom_le2] .

lemma intersect_int_dom_mode_mono:
  assumes "mode \<noteq> Refine_Fixpoint" and "a1 \<le> a2" and "b1 \<le> b2"
  shows "intersect_int_dom_mode mode a1 b1 \<le> intersect_int_dom_mode mode a2 b2"
  unfolding intersect_int_dom_mode_def
  using refine_mode_mono_trans[OF assms(1) intersect_int_dom_mono[OF assms(2,3)]] .


subsection \<open>Raw componentwise inverse operators\<close>

definition inv_less_int_dom_raw ::
    "bool => int_dom => int_dom => int_dom * int_dom"
where
  "inv_less_int_dom_raw res d1 d2 =
     (let (s1, s2) = inv_less_sign res (int_sign d1) (int_sign d2);
          (i1, i2) = inv_less_ivl res (int_ivl d1) (int_ivl d2);
          (c1, c2) = inv_less_congruence res (int_congruence d1) (int_congruence d2)
      in
        (d1\<lparr>int_sign := s1, int_ivl := i1, int_congruence := c1\<rparr>,
         d2\<lparr>int_sign := s2, int_ivl := i2, int_congruence := c2\<rparr>))"

definition inv_eq_int_dom_raw ::
    "bool => int_dom => int_dom => int_dom * int_dom"
where
  "inv_eq_int_dom_raw res d1 d2 =
     (if res then (intersect_int_dom d1 d2, intersect_int_dom d1 d2)
      else
        (let (s1, s2) = inv_eq_sign False (int_sign d1) (int_sign d2);
             (i1, i2) = inv_eq_ivl False (int_ivl d1) (int_ivl d2);
             (c1, c2) = inv_eq_congruence False (int_congruence d1) (int_congruence d2)
         in
           (d1\<lparr>int_sign := s1, int_ivl := i1, int_congruence := c1\<rparr>,
            d2\<lparr>int_sign := s2, int_ivl := i2, int_congruence := c2\<rparr>)))"

definition inv_plus_int_dom_raw ::
    "int_dom => int_dom => int_dom => int_dom * int_dom"
where
  "inv_plus_int_dom_raw r d1 d2 =
     (let (s1, s2) = inv_conservative (int_sign r) (int_sign d1) (int_sign d2);
          (i1, i2) = inv_conservative (int_ivl r) (int_ivl d1) (int_ivl d2);
          (p1, p2) = inv_conservative (int_parity r) (int_parity d1) (int_parity d2);
          (c1, c2) =
            inv_plus_congruence (int_congruence r) (int_congruence d1) (int_congruence d2)
      in
        (d1\<lparr>int_sign := s1, int_ivl := i1, int_parity := p1, int_congruence := c1\<rparr>,
         d2\<lparr>int_sign := s2, int_ivl := i2, int_parity := p2, int_congruence := c2\<rparr>))"

definition inv_minus_int_dom_raw ::
    "int_dom => int_dom => int_dom => int_dom * int_dom"
where
  "inv_minus_int_dom_raw r d1 d2 =
     (let (s1, s2) = inv_conservative (int_sign r) (int_sign d1) (int_sign d2);
          (i1, i2) = inv_conservative (int_ivl r) (int_ivl d1) (int_ivl d2);
          (p1, p2) = inv_conservative (int_parity r) (int_parity d1) (int_parity d2);
          (c1, c2) =
            inv_minus_congruence (int_congruence r) (int_congruence d1) (int_congruence d2)
      in
        (d1\<lparr>int_sign := s1, int_ivl := i1, int_parity := p1, int_congruence := c1\<rparr>,
         d2\<lparr>int_sign := s2, int_ivl := i2, int_parity := p2, int_congruence := c2\<rparr>))"

definition inv_times_int_dom_raw ::
    "int_dom => int_dom => int_dom => int_dom * int_dom"
where
  "inv_times_int_dom_raw r d1 d2 =
     (let (s1, s2) = inv_conservative (int_sign r) (int_sign d1) (int_sign d2);
          (i1, i2) = inv_conservative (int_ivl r) (int_ivl d1) (int_ivl d2);
          (p1, p2) = inv_conservative (int_parity r) (int_parity d1) (int_parity d2);
          (c1, c2) =
            inv_times_congruence (int_congruence r) (int_congruence d1) (int_congruence d2)
      in
        (d1\<lparr>int_sign := s1, int_ivl := i1, int_parity := p1, int_congruence := c1\<rparr>,
         d2\<lparr>int_sign := s2, int_ivl := i2, int_parity := p2, int_congruence := c2\<rparr>))"


subsection \<open>Raw soundness\<close>

lemma inv_less_int_dom_raw_sound:
  assumes "x \<in> gamma_int_dom d1" and "y \<in> gamma_int_dom d2" and "(x < y) = res"
  shows
    "x \<in> gamma_int_dom (fst (inv_less_int_dom_raw res d1 d2)) \<and>
     y \<in> gamma_int_dom (snd (inv_less_int_dom_raw res d1 d2))"
  using assms(1,2) inv_less_sign_sound[OF _ _ assms(3)] inv_less_ivl_sound[OF _ _ assms(3)]
  by (simp add: inv_less_int_dom_raw_def Let_def case_prod_beta gamma_int_dom_def
      inv_less_congruence_def)

lemma inv_eq_int_dom_raw_sound:
  assumes "x \<in> gamma_int_dom d1" and "y \<in> gamma_int_dom d2" and "(x = y) = res"
  shows
    "x \<in> gamma_int_dom (fst (inv_eq_int_dom_raw res d1 d2)) \<and>
     y \<in> gamma_int_dom (snd (inv_eq_int_dom_raw res d1 d2))"
proof (cases res)
  case True
  then show ?thesis
    using assms intersect_int_dom_sound[OF assms(1), of d2] by (simp add: inv_eq_int_dom_raw_def)
next
  case False
  then show ?thesis
    using assms(1,2) inv_eq_sign_sound[OF _ _ assms(3)] inv_eq_ivl_sound[OF _ _ assms(3)]
      inv_eq_congruence_sound[OF _ _ assms(3)]
    by (simp add: inv_eq_int_dom_raw_def Let_def case_prod_beta gamma_int_dom_def
        del: inv_eq_sign.simps)
qed

lemma inv_plus_int_dom_raw_sound:
  assumes "x \<in> gamma_int_dom d1" and "y \<in> gamma_int_dom d2" and "x + y \<in> gamma_int_dom r"
  shows
    "x \<in> gamma_int_dom (fst (inv_plus_int_dom_raw r d1 d2)) \<and>
     y \<in> gamma_int_dom (snd (inv_plus_int_dom_raw r d1 d2))"
  using assms inv_plus_congruence_sound[of x _ y _ "int_congruence r"]
  by (simp add: inv_plus_int_dom_raw_def Let_def case_prod_beta gamma_int_dom_def
      inv_conservative_def)

lemma inv_minus_int_dom_raw_sound:
  assumes "x \<in> gamma_int_dom d1" and "y \<in> gamma_int_dom d2" and "x - y \<in> gamma_int_dom r"
  shows
    "x \<in> gamma_int_dom (fst (inv_minus_int_dom_raw r d1 d2)) \<and>
     y \<in> gamma_int_dom (snd (inv_minus_int_dom_raw r d1 d2))"
  using assms inv_minus_congruence_sound[of x _ y _ "int_congruence r"]
  by (simp add: inv_minus_int_dom_raw_def Let_def case_prod_beta gamma_int_dom_def
      inv_conservative_def)

lemma inv_times_int_dom_raw_sound:
  assumes "x \<in> gamma_int_dom d1" and "y \<in> gamma_int_dom d2" and "x * y \<in> gamma_int_dom r"
  shows
    "x \<in> gamma_int_dom (fst (inv_times_int_dom_raw r d1 d2)) \<and>
     y \<in> gamma_int_dom (snd (inv_times_int_dom_raw r d1 d2))"
  using assms inv_times_congruence_sound[of x _ y _ "int_congruence r"]
  by (simp add: inv_times_int_dom_raw_def Let_def case_prod_beta gamma_int_dom_def
      inv_conservative_def)


subsection \<open>Raw monotonicity\<close>

lemma inv_less_int_dom_raw_mono:
  assumes "d1 \<le> d2" and "e1 \<le> e2"
  shows "le_pair (inv_less_int_dom_raw res d1 e1) (inv_less_int_dom_raw res d2 e2)"
  using assms
  by (simp add: inv_less_int_dom_raw_def Let_def case_prod_beta less_eq_int_dom_ext_def
      inv_less_sign_mono inv_less_ivl_mono inv_less_congruence_def)

lemma inv_eq_int_dom_raw_mono:
  assumes "d1 \<le> d2" and "e1 \<le> e2"
  shows "le_pair (inv_eq_int_dom_raw res d1 e1) (inv_eq_int_dom_raw res d2 e2)"
proof (cases res)
  case True
  then show ?thesis
    using intersect_int_dom_mono[OF assms] by (simp add: inv_eq_int_dom_raw_def)
next
  case False
  then show ?thesis
    using assms
    by (simp add: inv_eq_int_dom_raw_def Let_def case_prod_beta less_eq_int_dom_ext_def
        inv_eq_sign_mono inv_eq_ivl_mono inv_eq_congruence_mono del: inv_eq_sign.simps)
qed

lemma inv_plus_int_dom_raw_mono:
  assumes "r1 \<le> r2" and "d1 \<le> d2" and "e1 \<le> e2"
  shows "le_pair (inv_plus_int_dom_raw r1 d1 e1) (inv_plus_int_dom_raw r2 d2 e2)"
  using assms
  by (simp add: inv_plus_int_dom_raw_def Let_def case_prod_beta less_eq_int_dom_ext_def
      inv_conservative_def inv_plus_congruence_mono)

lemma inv_minus_int_dom_raw_mono:
  assumes "r1 \<le> r2" and "d1 \<le> d2" and "e1 \<le> e2"
  shows "le_pair (inv_minus_int_dom_raw r1 d1 e1) (inv_minus_int_dom_raw r2 d2 e2)"
  using assms
  by (simp add: inv_minus_int_dom_raw_def Let_def case_prod_beta less_eq_int_dom_ext_def
      inv_conservative_def inv_minus_congruence_mono)

lemma inv_times_int_dom_raw_mono:
  assumes "r1 \<le> r2" and "d1 \<le> d2" and "e1 \<le> e2"
  shows "le_pair (inv_times_int_dom_raw r1 d1 e1) (inv_times_int_dom_raw r2 d2 e2)"
  using assms
  by (simp add: inv_times_int_dom_raw_def Let_def case_prod_beta less_eq_int_dom_ext_def
      inv_conservative_def inv_times_congruence_mono)


subsection \<open>Mode-aware wrappers\<close>

definition inv_less_int_dom ::
    "refine_mode => bool => int_dom => int_dom => int_dom * int_dom"
where
  "inv_less_int_dom mode res d1 d2 =
     (let (r1, r2) = inv_less_int_dom_raw res d1 d2
      in (refine mode r1, refine mode r2))"

definition inv_eq_int_dom ::
    "refine_mode => bool => int_dom => int_dom => int_dom * int_dom"
where
  "inv_eq_int_dom mode res d1 d2 =
     (let (r1, r2) = inv_eq_int_dom_raw res d1 d2
      in (refine mode r1, refine mode r2))"

definition inv_plus_int_dom ::
    "refine_mode => int_dom => int_dom => int_dom => int_dom * int_dom"
where
  "inv_plus_int_dom mode r d1 d2 =
     (let (r1, r2) = inv_plus_int_dom_raw r d1 d2
      in (refine mode r1, refine mode r2))"

definition inv_minus_int_dom ::
    "refine_mode => int_dom => int_dom => int_dom => int_dom * int_dom"
where
  "inv_minus_int_dom mode r d1 d2 =
     (let (r1, r2) = inv_minus_int_dom_raw r d1 d2
      in (refine mode r1, refine mode r2))"

definition inv_times_int_dom ::
    "refine_mode => int_dom => int_dom => int_dom => int_dom * int_dom"
where
  "inv_times_int_dom mode r d1 d2 =
     (let (r1, r2) = inv_times_int_dom_raw r d1 d2
      in (refine mode r1, refine mode r2))"


text \<open>
  Each wrapper refines both raw candidates, so its soundness and monotonicity
  reduce to the raw operator's through \<open>refine_exact\<close> and
  \<open>refine_nonfixpoint_mono\<close>.
\<close>

lemma inv_int_dom_map_prod:
  "inv_less_int_dom mode res d1 d2 =
     map_prod (refine mode) (refine mode) (inv_less_int_dom_raw res d1 d2)"
  "inv_eq_int_dom mode res d1 d2 =
     map_prod (refine mode) (refine mode) (inv_eq_int_dom_raw res d1 d2)"
  "inv_plus_int_dom mode r d1 d2 =
     map_prod (refine mode) (refine mode) (inv_plus_int_dom_raw r d1 d2)"
  "inv_minus_int_dom mode r d1 d2 =
     map_prod (refine mode) (refine mode) (inv_minus_int_dom_raw r d1 d2)"
  "inv_times_int_dom mode r d1 d2 =
     map_prod (refine mode) (refine mode) (inv_times_int_dom_raw r d1 d2)"
  by (simp_all add: inv_less_int_dom_def inv_eq_int_dom_def inv_plus_int_dom_def
      inv_minus_int_dom_def inv_times_int_dom_def map_prod_def case_prod_beta)


subsection \<open>Backward-domain interpretation\<close>

text \<open>
  Soundness and the reductiveness of \<open>intersect\<close> hold at every mode, so every
  mode interprets @{locale backward_domain_reductive} and shares the precise,
  dead-arm-eliminating \<open>branch\<close>/\<open>branch_st\<close>. Monotonicity needs
  \<open>mode \<noteq> Refine_Fixpoint\<close>: \<open>refine_fix\<close>'s total wrapper has no monotonicity
  theorem (\<open>Int_Refinement\<close>), a faithful transliteration of Goblint's
  \<open>fixpoint\<close> loop. So \<open>Refine_Never\<close> and \<open>Refine_Once\<close> interpret the full
  @{locale backward_domain_mono}, and \<open>Refine_Fixpoint\<close> stays out of reach of
  \<open>branch_mono\<close> and the rest of the monotonicity layer.
\<close>

lemma int_dom_backward_domain_reductive:
  "backward_domain_reductive (intersect_int_dom_mode mode) (aval_int_dom mode) int_dom_tobool
     (inv_less_int_dom mode) (inv_eq_int_dom mode)
     (inv_plus_int_dom mode) (inv_minus_int_dom mode) (inv_times_int_dom mode)"
proof (intro backward_domain_reductive.intro backward_domain.intro sound_intersection.intro
    int_dom_sound_evaluator mono_truth_test.axioms(1)[OF int_dom_truth_test]
    backward_ops.intro backward_ops_axioms.intro
    reductive_intersection.intro reductive_intersection_axioms.intro)
qed (simp_all add: inv_int_dom_map_prod refine_exact intersect_int_dom_mode_sound
       inv_less_int_dom_raw_sound inv_eq_int_dom_raw_sound inv_plus_int_dom_raw_sound
       inv_minus_int_dom_raw_sound inv_times_int_dom_raw_sound
       intersect_int_dom_mode_reductive1 intersect_int_dom_mode_reductive2)

lemma int_dom_backward_domain_mono:
  assumes "mode \<noteq> Refine_Fixpoint"
  shows
    "backward_domain_mono (intersect_int_dom_mode mode) (aval_int_dom mode) int_dom_tobool
       (inv_less_int_dom mode) (inv_eq_int_dom mode)
       (inv_plus_int_dom mode) (inv_minus_int_dom mode) (inv_times_int_dom mode)"
proof (intro backward_domain_mono.intro int_dom_backward_domain_reductive
    int_dom_mono_evaluator[OF assms] int_dom_truth_test backward_domain_mono_axioms.intro
    mono_intersection.intro mono_intersection_axioms.intro
    sound_intersection.intro)
qed (auto simp: assms inv_int_dom_map_prod refine_mode_mono_trans intersect_int_dom_mode_mono
       refine_exact intersect_int_dom_mode_sound
       inv_less_int_dom_raw_mono inv_eq_int_dom_raw_mono
       inv_plus_int_dom_raw_mono inv_minus_int_dom_raw_mono inv_times_int_dom_raw_mono)

abbreviation intersect_int_dom_never :: "int_dom => int_dom => int_dom" where
  "intersect_int_dom_never == intersect_int_dom_mode Refine_Never"

abbreviation aval_int_dom_never :: "exp => (vname => int_dom) => int_dom" where
  "aval_int_dom_never == aval_int_dom Refine_Never"

abbreviation tobool_int_dom_never :: "int_dom => bool option" where
  "tobool_int_dom_never == int_dom_tobool"

abbreviation inv_less_int_dom_never ::
    "bool => int_dom => int_dom => int_dom * int_dom"
where
  "inv_less_int_dom_never == inv_less_int_dom Refine_Never"

abbreviation inv_eq_int_dom_never ::
    "bool => int_dom => int_dom => int_dom * int_dom"
where
  "inv_eq_int_dom_never == inv_eq_int_dom Refine_Never"

abbreviation inv_plus_int_dom_never ::
    "int_dom => int_dom => int_dom => int_dom * int_dom"
where
  "inv_plus_int_dom_never == inv_plus_int_dom Refine_Never"

abbreviation inv_minus_int_dom_never ::
    "int_dom => int_dom => int_dom => int_dom * int_dom"
where
  "inv_minus_int_dom_never == inv_minus_int_dom Refine_Never"

abbreviation inv_times_int_dom_never ::
    "int_dom => int_dom => int_dom => int_dom * int_dom"
where
  "inv_times_int_dom_never == inv_times_int_dom Refine_Never"

global_interpretation int_dom_backward_never:
    backward_domain_mono
      intersect_int_dom_never aval_int_dom_never tobool_int_dom_never
      inv_less_int_dom_never inv_eq_int_dom_never
      inv_plus_int_dom_never inv_minus_int_dom_never inv_times_int_dom_never
  defines
    afilter_int_dom_never = int_dom_backward_never.afilter
    and feasible_int_dom_never = int_dom_backward_never.feasible
    and bfilter_int_dom_never = int_dom_backward_never.bfilter
    and branch_int_dom_never = int_dom_backward_never.branch
    and branch_lifted_int_dom_never = int_dom_backward_never.branch_lifted
    and afilter_int_dom_never_st = int_dom_backward_never.afilter_st
    and bfilter_int_dom_never_st = int_dom_backward_never.bfilter_st
    and branch_int_dom_never_st = int_dom_backward_never.branch_st
  by (rule int_dom_backward_domain_mono) simp

abbreviation intersect_int_dom_once :: "int_dom => int_dom => int_dom" where
  "intersect_int_dom_once == intersect_int_dom_mode Refine_Once"

abbreviation aval_int_dom_once :: "exp => (vname => int_dom) => int_dom" where
  "aval_int_dom_once == aval_int_dom Refine_Once"

abbreviation tobool_int_dom_once :: "int_dom => bool option" where
  "tobool_int_dom_once == int_dom_tobool"

abbreviation inv_less_int_dom_once ::
    "bool => int_dom => int_dom => int_dom * int_dom"
where
  "inv_less_int_dom_once == inv_less_int_dom Refine_Once"

abbreviation inv_eq_int_dom_once ::
    "bool => int_dom => int_dom => int_dom * int_dom"
where
  "inv_eq_int_dom_once == inv_eq_int_dom Refine_Once"

abbreviation inv_plus_int_dom_once ::
    "int_dom => int_dom => int_dom => int_dom * int_dom"
where
  "inv_plus_int_dom_once == inv_plus_int_dom Refine_Once"

abbreviation inv_minus_int_dom_once ::
    "int_dom => int_dom => int_dom => int_dom * int_dom"
where
  "inv_minus_int_dom_once == inv_minus_int_dom Refine_Once"

abbreviation inv_times_int_dom_once ::
    "int_dom => int_dom => int_dom => int_dom * int_dom"
where
  "inv_times_int_dom_once == inv_times_int_dom Refine_Once"

global_interpretation int_dom_backward_once:
    backward_domain_mono
      intersect_int_dom_once aval_int_dom_once tobool_int_dom_once
      inv_less_int_dom_once inv_eq_int_dom_once
      inv_plus_int_dom_once inv_minus_int_dom_once inv_times_int_dom_once
  defines
    afilter_int_dom_once = int_dom_backward_once.afilter
    and feasible_int_dom_once = int_dom_backward_once.feasible
    and bfilter_int_dom_once = int_dom_backward_once.bfilter
    and branch_int_dom_once = int_dom_backward_once.branch
    and branch_lifted_int_dom_once = int_dom_backward_once.branch_lifted
    and afilter_int_dom_once_st = int_dom_backward_once.afilter_st
    and bfilter_int_dom_once_st = int_dom_backward_once.bfilter_st
    and branch_int_dom_once_st = int_dom_backward_once.branch_st
  by (rule int_dom_backward_domain_mono) simp

abbreviation intersect_int_dom_fixpoint :: "int_dom => int_dom => int_dom" where
  "intersect_int_dom_fixpoint == intersect_int_dom_mode Refine_Fixpoint"

abbreviation aval_int_dom_fixpoint :: "exp => (vname => int_dom) => int_dom" where
  "aval_int_dom_fixpoint == aval_int_dom Refine_Fixpoint"

abbreviation tobool_int_dom_fixpoint :: "int_dom => bool option" where
  "tobool_int_dom_fixpoint == int_dom_tobool"

abbreviation inv_less_int_dom_fixpoint ::
    "bool => int_dom => int_dom => int_dom * int_dom"
where
  "inv_less_int_dom_fixpoint == inv_less_int_dom Refine_Fixpoint"

abbreviation inv_eq_int_dom_fixpoint ::
    "bool => int_dom => int_dom => int_dom * int_dom"
where
  "inv_eq_int_dom_fixpoint == inv_eq_int_dom Refine_Fixpoint"

abbreviation inv_plus_int_dom_fixpoint ::
    "int_dom => int_dom => int_dom => int_dom * int_dom"
where
  "inv_plus_int_dom_fixpoint == inv_plus_int_dom Refine_Fixpoint"

abbreviation inv_minus_int_dom_fixpoint ::
    "int_dom => int_dom => int_dom => int_dom * int_dom"
where
  "inv_minus_int_dom_fixpoint == inv_minus_int_dom Refine_Fixpoint"

abbreviation inv_times_int_dom_fixpoint ::
    "int_dom => int_dom => int_dom => int_dom * int_dom"
where
  "inv_times_int_dom_fixpoint == inv_times_int_dom Refine_Fixpoint"

global_interpretation int_dom_backward_fixpoint:
    backward_domain_reductive
      intersect_int_dom_fixpoint aval_int_dom_fixpoint tobool_int_dom_fixpoint
      inv_less_int_dom_fixpoint inv_eq_int_dom_fixpoint
      inv_plus_int_dom_fixpoint inv_minus_int_dom_fixpoint inv_times_int_dom_fixpoint
  defines
    afilter_int_dom_fixpoint = int_dom_backward_fixpoint.afilter
    and feasible_int_dom_fixpoint = int_dom_backward_fixpoint.feasible
    and bfilter_int_dom_fixpoint = int_dom_backward_fixpoint.bfilter
    and branch_lifted_int_dom_fixpoint = int_dom_backward_fixpoint.branch_lifted
    and branch_int_dom_fixpoint = int_dom_backward_fixpoint.branch
    and afilter_int_dom_fixpoint_st = int_dom_backward_fixpoint.afilter_st
    and bfilter_int_dom_fixpoint_st = int_dom_backward_fixpoint.bfilter_st
    and branch_int_dom_fixpoint_st = int_dom_backward_fixpoint.branch_st
  by (rule int_dom_backward_domain_reductive)

lemmas branch_int_dom_fixpoint_sound = int_dom_backward_fixpoint.branch_sound

end
