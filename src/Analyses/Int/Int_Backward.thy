theory Int_Backward
  imports
    Int_Arithmetic
    "Voblint_Analysis_Sign.Sign_Numeric_Queries"
    "Voblint_Analysis_Parity.Parity_Backward"
    "Voblint_Analysis_Parity.Parity_Numeric_Queries"
    "Voblint_Analysis_Congruence.Congruence_Backward"
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
  do not have. Parity and Congruence invert arithmetic in their own theories,
  and the composite reuses both: \<open>inv_plus_parity\<close>, \<open>inv_minus_parity\<close>,
  \<open>inv_times_parity\<close> (\<open>Parity_Backward\<close>) and \<open>inv_plus_congruence\<close>,
  \<open>inv_minus_congruence\<close>, \<open>inv_times_congruence\<close> (\<open>Congruence_Backward\<close>).
  A comparison leaves the Parity component unchanged, as Parity's own \<open>less\<close>
  inverse does; an equality narrows it through the composite
  \<open>intersect_int_dom\<close> on the true branch below.

  Precision Sign and Interval cannot recover directly at inversion time
  is not lost: the mode-aware wrapper's \<open>refine mode\<close> step re-derives
  their bounds from the (possibly Congruence-tightened) returned operand,
  exactly as \<open>refine_interval\<close>/\<open>refine_congruence\<close> already do for
  forward arithmetic.
\<close>

subsection \<open>Composite semantic intersection\<close>

definition intersect_int_dom :: "int_dom => int_dom => int_dom" where
  "intersect_int_dom d1 d2 =
     d1\<lparr>
       int_sign := int_sign d1 \<sqinter> int_sign d2,
       int_ivl := intersect_ivl (int_ivl d1) (int_ivl d2),
       int_parity := int_parity d1 \<sqinter> int_parity d2,
       int_congruence := int_congruence d1 \<sqinter> int_congruence d2
     \<rparr>"

text \<open>
  \<open>intersect_ivl\<close>'s defining equation is globally tagged \<open>[simp]\<close>
  (\<open>Interval_Lattice\<close>), so plain \<open>simp\<close>/\<open>auto\<close> unfolds it to
  \<open>normalize_ivl (a \<sqinter> b)\<close> before \<open>gamma_intersect_ivl_exact\<close> or
  \<open>intersect_ivl_le1\<close>/\<open>intersect_ivl_le2\<close>/\<open>intersect_ivl_mono\<close> -- all
  stated in terms of the abstract \<open>intersect_ivl\<close> -- get a chance to match.
  \<open>del: intersect_ivl_def\<close> below keeps \<open>intersect_ivl\<close> opaque for exactly
  those calls, matching \<open>is_bottom_int_dom_correct\<close>'s own
  \<open>simp only: gamma_intersect_ivl_exact ...\<close> workaround in
  \<open>Int_Lattice\<close>.
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
  have sign_fact: "n \<in> gamma_sign (int_sign a \<sqinter> int_sign b)"
    using hn(1) hm(1) by simp
  have parity_fact: "n \<in> gamma_parity (int_parity a \<sqinter> int_parity b)"
    using hn(3) hm(3) by simp
  have congruence_fact:
    "n \<in> gamma_congruence (int_congruence a \<sqinter> int_congruence b)"
    using hn(4) hm(4) by simp
  show ?thesis
    unfolding gamma_int_dom_def intersect_int_dom_def
    using sign_fact ivl_fact parity_fact congruence_fact
    by (simp del: intersect_ivl_def)
qed

lemma intersect_int_dom_le1: "intersect_int_dom a b \<le> a"
  unfolding intersect_int_dom_def less_eq_int_dom_ext_def
  by (simp add: inf_le1 intersect_ivl_le1
      del: intersect_ivl_def)

lemma intersect_int_dom_le2: "intersect_int_dom a b \<le> b"
  unfolding intersect_int_dom_def less_eq_int_dom_ext_def
  by (simp add: inf_le2 intersect_ivl_le2
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
    using s t
    by (simp add: intersect_ivl_mono[OF s(2) t(2)] le_infI1 le_infI2
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

text \<open>
  The raw inverses run each component's backward operator on its own field and
  reassemble the record. A component with no useful inverse goes through
  \<open>inv_conservative\<close>, and a true equality intersects both operands with
  \<open>intersect_int_dom\<close>.
\<close>

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
          (p1, p2) = inv_plus_parity (int_parity r) (int_parity d1) (int_parity d2);
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
          (p1, p2) = inv_minus_parity (int_parity r) (int_parity d1) (int_parity d2);
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
          (p1, p2) = inv_times_parity (int_parity r) (int_parity d1) (int_parity d2);
          (c1, c2) =
            inv_times_congruence (int_congruence r) (int_congruence d1) (int_congruence d2)
      in
        (d1\<lparr>int_sign := s1, int_ivl := i1, int_parity := p1, int_congruence := c1\<rparr>,
         d2\<lparr>int_sign := s2, int_ivl := i2, int_parity := p2, int_congruence := c2\<rparr>))"


subsection \<open>Raw soundness\<close>

text \<open>
  A raw inverse keeps every concrete operand pair consistent with the observed
  outcome: if \<open>x\<close> and \<open>y\<close> lie in the inputs and produce the comparison result or
  the value in \<open>r\<close>, they lie in the refined pair. Each proof cites the component
  soundness lemmas.
\<close>

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
    inv_plus_parity_sound[of x _ y _ "int_parity r"]
  by (simp add: inv_plus_int_dom_raw_def Let_def case_prod_beta gamma_int_dom_def
      inv_conservative_def)

lemma inv_minus_int_dom_raw_sound:
  assumes "x \<in> gamma_int_dom d1" and "y \<in> gamma_int_dom d2" and "x - y \<in> gamma_int_dom r"
  shows
    "x \<in> gamma_int_dom (fst (inv_minus_int_dom_raw r d1 d2)) \<and>
     y \<in> gamma_int_dom (snd (inv_minus_int_dom_raw r d1 d2))"
  using assms inv_minus_congruence_sound[of x _ y _ "int_congruence r"]
    inv_minus_parity_sound[of x _ y _ "int_parity r"]
  by (simp add: inv_minus_int_dom_raw_def Let_def case_prod_beta gamma_int_dom_def
      inv_conservative_def)

lemma inv_times_int_dom_raw_sound:
  assumes "x \<in> gamma_int_dom d1" and "y \<in> gamma_int_dom d2" and "x * y \<in> gamma_int_dom r"
  shows
    "x \<in> gamma_int_dom (fst (inv_times_int_dom_raw r d1 d2)) \<and>
     y \<in> gamma_int_dom (snd (inv_times_int_dom_raw r d1 d2))"
  using assms inv_times_congruence_sound[of x _ y _ "int_congruence r"]
    inv_times_parity_sound[of x _ y _ "int_parity r"]
  by (simp add: inv_times_int_dom_raw_def Let_def case_prod_beta gamma_int_dom_def
      inv_conservative_def)


subsection \<open>Raw monotonicity\<close>

text \<open>
  The raw inverses are monotone in every argument, stated as \<open>le_pair\<close> on the
  refined pair and proved from the componentwise monotonicity lemmas.
\<close>

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
      inv_conservative_def inv_plus_congruence_mono inv_plus_parity_mono)

lemma inv_minus_int_dom_raw_mono:
  assumes "r1 \<le> r2" and "d1 \<le> d2" and "e1 \<le> e2"
  shows "le_pair (inv_minus_int_dom_raw r1 d1 e1) (inv_minus_int_dom_raw r2 d2 e2)"
  using assms
  by (simp add: inv_minus_int_dom_raw_def Let_def case_prod_beta less_eq_int_dom_ext_def
      inv_conservative_def inv_minus_congruence_mono inv_minus_parity_mono)

lemma inv_times_int_dom_raw_mono:
  assumes "r1 \<le> r2" and "d1 \<le> d2" and "e1 \<le> e2"
  shows "le_pair (inv_times_int_dom_raw r1 d1 e1) (inv_times_int_dom_raw r2 d2 e2)"
  using assms
  by (simp add: inv_times_int_dom_raw_def Let_def case_prod_beta less_eq_int_dom_ext_def
      inv_conservative_def inv_times_congruence_mono inv_times_parity_mono)


subsection \<open>Mode-aware wrappers\<close>

text \<open>
  \<open>inv_less_int_dom\<close> and its siblings apply \<open>refine mode\<close> to both halves of the
  raw result, so backward filtering follows the same refinement policy as the
  forward arithmetic.
\<close>

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
  mode interprets @{locale sound_refinement} and shares the precise,
  dead-arm-eliminating \<open>branch\<close>/\<open>branch_st\<close>. Monotonicity needs
  \<open>mode \<noteq> Refine_Fixpoint\<close>: \<open>refine_fix\<close>'s total wrapper has no monotonicity
  theorem (\<open>Int_Refinement\<close>), a faithful transliteration of Goblint's
  \<open>fixpoint\<close> loop. So \<open>Refine_Never\<close> and \<open>Refine_Once\<close> interpret the full
  @{locale mono_refinement}, and \<open>Refine_Fixpoint\<close> stays out of reach of
  \<open>branch_mono\<close> and the rest of the monotonicity layer.
\<close>

lemma int_backward_domain:
  "sound_refinement (intersect_int_dom_mode mode) (aval_int_dom mode) int_dom_tobool
     (inv_less_int_dom mode) (inv_eq_int_dom mode)
     (inv_plus_int_dom mode) (inv_minus_int_dom mode) (inv_times_int_dom mode)"
proof (intro sound_refinement.intro sound_intersection.intro
    int_dom_sound_evaluator mono_truth_test.axioms(1)[OF int_dom_truth_test]
    sound_inverse_ops.intro sound_inverse_ops_axioms.intro)
qed (simp_all add: inv_int_dom_map_prod refine_exact intersect_int_dom_mode_sound
       inv_less_int_dom_raw_sound inv_eq_int_dom_raw_sound inv_plus_int_dom_raw_sound
       inv_minus_int_dom_raw_sound inv_times_int_dom_raw_sound
       intersect_int_dom_mode_reductive1 intersect_int_dom_mode_reductive2)

lemma int_dom_backward_domain_mono:
  assumes "mode \<noteq> Refine_Fixpoint"
  shows
    "mono_refinement (intersect_int_dom_mode mode) (aval_int_dom mode) int_dom_tobool
       (inv_less_int_dom mode) (inv_eq_int_dom mode)
       (inv_plus_int_dom mode) (inv_minus_int_dom mode) (inv_times_int_dom mode)"
proof (intro mono_refinement.intro int_backward_domain
    int_dom_mono_evaluator[OF assms] int_dom_truth_test mono_refinement_axioms.intro
    mono_intersection.intro mono_intersection_axioms.intro
    sound_intersection.intro)
qed (auto simp: assms inv_int_dom_map_prod refine_mode_mono_trans intersect_int_dom_mode_mono
       refine_exact intersect_int_dom_mode_sound
       intersect_int_dom_mode_reductive1 intersect_int_dom_mode_reductive2
       inv_less_int_dom_raw_mono inv_eq_int_dom_raw_mono
       inv_plus_int_dom_raw_mono inv_minus_int_dom_raw_mono inv_times_int_dom_raw_mono)

subsection \<open>The refinement operations, per mode\<close>

text \<open>
  The three refinement modes differ only in how often the four components are
  reduced against each other, so one record parametric in the mode carries all
  three. The guard filters and the branch are derived from it in \<open>Int_Transfer\<close>.
\<close>

definition int_refine_ops :: "refine_mode \<Rightarrow> int_dom refine_ops" where
  "int_refine_ops mode =
     \<lparr>r_tobool = int_dom_tobool, r_inv_less = inv_less_int_dom mode,
      r_inv_eq = inv_eq_int_dom mode, r_inv_plus = inv_plus_int_dom mode,
      r_inv_minus = inv_minus_int_dom mode, r_inv_times = inv_times_int_dom mode,
      r_intersect = intersect_int_dom_mode mode\<rparr>"

lemma int_refine_ops_simps [simp]:
  "r_tobool (int_refine_ops mode) = int_dom_tobool"
  "r_inv_less (int_refine_ops mode) = inv_less_int_dom mode"
  "r_inv_eq (int_refine_ops mode) = inv_eq_int_dom mode"
  "r_inv_plus (int_refine_ops mode) = inv_plus_int_dom mode"
  "r_inv_minus (int_refine_ops mode) = inv_minus_int_dom mode"
  "r_inv_times (int_refine_ops mode) = inv_times_int_dom mode"
  "r_intersect (int_refine_ops mode) = intersect_int_dom_mode mode"
  by (simp_all add: int_refine_ops_def)

subsection \<open>Comparison queries\<close>

text \<open>
  A comparison is answered component by component, as Goblint's
  \<open>IntDomTuple\<close> answers \<open>lt\<close> and \<open>eq\<close>: it is decided when some component
  decides it on its own value, and no step here combines the components. The
  refinement mode therefore reaches a comparison only through its operands,
  which \<^const>\<open>aval_int_dom\<close> reduces as the mode says; under
  \<^const>\<open>Refine_Never\<close> a fact that only the reduced product knows is not
  available to a check.
\<close>

definition int_less_true :: "int_dom \<Rightarrow> int_dom \<Rightarrow> bool" where
  "int_less_true a b \<longleftrightarrow>
     sign_less_true (int_sign a) (int_sign b)
     \<or> interval_less_true (int_ivl a) (int_ivl b)
     \<or> parity_less_true (int_parity a) (int_parity b)
     \<or> congruence_lt (int_congruence a) (int_congruence b) = Some True"

definition int_less_false :: "int_dom \<Rightarrow> int_dom \<Rightarrow> bool" where
  "int_less_false a b \<longleftrightarrow>
     sign_less_false (int_sign a) (int_sign b)
     \<or> interval_less_false (int_ivl a) (int_ivl b)
     \<or> parity_less_false (int_parity a) (int_parity b)
     \<or> congruence_lt (int_congruence a) (int_congruence b) = Some False"

definition int_eq_true :: "int_dom \<Rightarrow> int_dom \<Rightarrow> bool" where
  "int_eq_true a b \<longleftrightarrow>
     sign_eq_true (int_sign a) (int_sign b)
     \<or> interval_eq_true (int_ivl a) (int_ivl b)
     \<or> parity_eq_true (int_parity a) (int_parity b)
     \<or> congruence_eqb (int_congruence a) (int_congruence b) = Some True"

definition int_eq_false :: "int_dom \<Rightarrow> int_dom \<Rightarrow> bool" where
  "int_eq_false a b \<longleftrightarrow>
     sign_eq_false (int_sign a) (int_sign b)
     \<or> interval_eq_false (int_ivl a) (int_ivl b)
     \<or> parity_eq_false (int_parity a) (int_parity b)
     \<or> congruence_eqb (int_congruence a) (int_congruence b) = Some False"

lemma gamma_int_dom_components:
  assumes "i \<in> \<gamma> (a :: int_dom)"
  shows "i \<in> gamma_sign (int_sign a)" "i \<in> gamma_ivl (int_ivl a)"
    "i \<in> gamma_parity (int_parity a)" "i \<in> gamma_congruence (int_congruence a)"
  using assms by (simp_all add: gamma_int_dom_def)

lemma int_less_true_sound:
  assumes "int_less_true a b" and "i \<in> \<gamma> a" and "j \<in> \<gamma> b"
  shows "i < j"
  using assms(1) gamma_int_dom_components[OF assms(2)] gamma_int_dom_components[OF assms(3)]
  unfolding int_less_true_def
  by (auto dest: sign_less_true_sound interval_less_true_sound parity_less_true_sound
      congruence_lt_sound)

lemma int_less_false_sound:
  assumes "int_less_false a b" and "i \<in> \<gamma> a" and "j \<in> \<gamma> b"
  shows "\<not> i < j"
  using assms(1) gamma_int_dom_components[OF assms(2)] gamma_int_dom_components[OF assms(3)]
  unfolding int_less_false_def
  by (auto dest: sign_less_false_sound interval_less_false_sound parity_less_false_sound
      congruence_lt_sound)

lemma int_eq_true_sound:
  assumes "int_eq_true a b" and "i \<in> \<gamma> a" and "j \<in> \<gamma> b"
  shows "i = j"
  using assms(1) gamma_int_dom_components[OF assms(2)] gamma_int_dom_components[OF assms(3)]
  unfolding int_eq_true_def
  by (auto dest: sign_eq_true_sound interval_eq_true_sound parity_eq_true_sound
      congruence_eqb_sound)

lemma int_eq_false_sound:
  assumes "int_eq_false a b" and "i \<in> \<gamma> a" and "j \<in> \<gamma> b"
  shows "i \<noteq> j"
  using assms(1) gamma_int_dom_components[OF assms(2)] gamma_int_dom_components[OF assms(3)]
  unfolding int_eq_false_def
  by (auto dest: sign_eq_false_sound interval_eq_false_sound parity_eq_false_sound
      congruence_eqb_sound)

global_interpretation int_dom_numeric_queries:
  numeric_query_judgments int_less_true int_less_false int_eq_true int_eq_false
  defines int_less = int_dom_numeric_queries.query_less
    and int_eq = int_dom_numeric_queries.query_eq
  by unfold_locales
     (fact int_less_true_sound, fact int_less_false_sound,
      fact int_eq_true_sound, fact int_eq_false_sound)

end
