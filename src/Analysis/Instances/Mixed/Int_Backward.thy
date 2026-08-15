theory Int_Backward
  imports
    Int_Arithmetic
    Sign_Backward
    Interval_Backward
    Congruence_Backward
    Voblint_Core.Exec_Backward
begin

section \<open>Composite integer-domain backward filtering\<close>

text \<open>
  Composite backward inversion follows the same shape as composite forward
  arithmetic (\<open>Int_Arithmetic.thy\<close>): a raw componentwise operator, reusing
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
  (\<open>Interval_Lattice.thy\<close>), so plain \<open>simp\<close>/\<open>auto\<close> unfolds it to
  \<open>normalize_ivl (meet_ivl a b)\<close> before \<open>gamma_intersect_ivl_exact\<close> or
  \<open>intersect_ivl_le1\<close>/\<open>intersect_ivl_le2\<close>/\<open>intersect_ivl_mono\<close> -- all
  stated in terms of the abstract \<open>intersect_ivl\<close> -- get a chance to match.
  \<open>del: intersect_ivl_def\<close> below keeps \<open>intersect_ivl\<close> opaque for exactly
  those calls, matching \<open>is_bottom_int_dom_correct\<close>'s own
  \<open>simp only: gamma_intersect_ivl_exact ...\<close> workaround in
  \<open>Int_Domain.thy\<close>.
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
  \<open>refine mode\<close> is reductive/exact for every mode (\<open>Int_Refinement.thy\<close>)
  but only monotone off \<open>Refine_Fixpoint\<close> (\<open>Int_Arithmetic.thy\<close>'s
  \<open>refine_nonfixpoint_mono\<close>); these two helpers compose that fact with an
  arbitrary reductive/monotone raw step once, instead of re-deriving the
  transitivity argument at each of the ten raw operators below.
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
proof -
  have hx: "x \<in> gamma_sign (int_sign d1)" "x \<in> gamma_ivl (int_ivl d1)"
           "x \<in> gamma_parity (int_parity d1)" "x \<in> gamma_congruence (int_congruence d1)"
    using assms(1) by (simp_all add: gamma_int_dom_def)
  have hy: "y \<in> gamma_sign (int_sign d2)" "y \<in> gamma_ivl (int_ivl d2)"
           "y \<in> gamma_parity (int_parity d2)" "y \<in> gamma_congruence (int_congruence d2)"
    using assms(2) by (simp_all add: gamma_int_dom_def)
  have s: "x \<in> gamma_sign (fst (inv_less_sign res (int_sign d1) (int_sign d2))) \<and>
           y \<in> gamma_sign (snd (inv_less_sign res (int_sign d1) (int_sign d2)))"
    by (rule inv_less_sign_sound[OF hx(1) hy(1) assms(3)])
  have i: "x \<in> gamma_ivl (fst (inv_less_ivl res (int_ivl d1) (int_ivl d2))) \<and>
           y \<in> gamma_ivl (snd (inv_less_ivl res (int_ivl d1) (int_ivl d2)))"
    by (rule inv_less_ivl_sound[OF hx(2) hy(2) assms(3)])
  have c:
    "x \<in> gamma_congruence
            (fst (inv_less_congruence res (int_congruence d1) (int_congruence d2))) \<and>
     y \<in> gamma_congruence
            (snd (inv_less_congruence res (int_congruence d1) (int_congruence d2)))"
    using hx(4) hy(4) by (simp add: inv_less_congruence_def)
  show ?thesis
    unfolding inv_less_int_dom_raw_def Let_def case_prod_beta gamma_int_dom_def
    using s i c hx(3) hy(3) by simp
qed

lemma inv_eq_int_dom_raw_sound:
  assumes "x \<in> gamma_int_dom d1" and "y \<in> gamma_int_dom d2" and "(x = y) = res"
  shows
    "x \<in> gamma_int_dom (fst (inv_eq_int_dom_raw res d1 d2)) \<and>
     y \<in> gamma_int_dom (snd (inv_eq_int_dom_raw res d1 d2))"
proof (cases res)
  case True
  have xy: "x = y" using assms(3) True by simp
  have x_in_d2: "x \<in> gamma_int_dom d2"
    using assms(2) xy by simp
  have result: "x \<in> gamma_int_dom (intersect_int_dom d1 d2)"
    by (rule intersect_int_dom_sound[OF assms(1) x_in_d2])
  show ?thesis
    unfolding inv_eq_int_dom_raw_def
    using True result xy by simp
next
  case False
  have hx: "x \<in> gamma_sign (int_sign d1)" "x \<in> gamma_ivl (int_ivl d1)"
           "x \<in> gamma_parity (int_parity d1)" "x \<in> gamma_congruence (int_congruence d1)"
    using assms(1) by (simp_all add: gamma_int_dom_def)
  have hy: "y \<in> gamma_sign (int_sign d2)" "y \<in> gamma_ivl (int_ivl d2)"
           "y \<in> gamma_parity (int_parity d2)" "y \<in> gamma_congruence (int_congruence d2)"
    using assms(2) by (simp_all add: gamma_int_dom_def)
  have hne: "(x = y) = False"
    using assms(3) False by simp
  have s: "x \<in> gamma_sign (fst (inv_eq_sign False (int_sign d1) (int_sign d2))) \<and>
           y \<in> gamma_sign (snd (inv_eq_sign False (int_sign d1) (int_sign d2)))"
    by (rule inv_eq_sign_sound[OF hx(1) hy(1) hne])
  have i: "x \<in> gamma_ivl (fst (inv_eq_ivl False (int_ivl d1) (int_ivl d2))) \<and>
           y \<in> gamma_ivl (snd (inv_eq_ivl False (int_ivl d1) (int_ivl d2)))"
    by (rule inv_eq_ivl_sound[OF hx(2) hy(2) hne])
  have c:
    "x \<in> gamma_congruence
            (fst (inv_eq_congruence False (int_congruence d1) (int_congruence d2))) \<and>
     y \<in> gamma_congruence
            (snd (inv_eq_congruence False (int_congruence d1) (int_congruence d2)))"
    by (rule inv_eq_congruence_sound[OF hx(4) hy(4) hne])
  show ?thesis
    unfolding inv_eq_int_dom_raw_def Let_def case_prod_beta gamma_int_dom_def
    using False s i c hx(3) hy(3) by simp
qed

lemma inv_plus_int_dom_raw_sound:
  assumes "x \<in> gamma_int_dom d1" and "y \<in> gamma_int_dom d2" and "x + y \<in> gamma_int_dom r"
  shows
    "x \<in> gamma_int_dom (fst (inv_plus_int_dom_raw r d1 d2)) \<and>
     y \<in> gamma_int_dom (snd (inv_plus_int_dom_raw r d1 d2))"
proof -
  have hx: "x \<in> gamma_sign (int_sign d1)" "x \<in> gamma_ivl (int_ivl d1)"
           "x \<in> gamma_parity (int_parity d1)" "x \<in> gamma_congruence (int_congruence d1)"
    using assms(1) by (simp_all add: gamma_int_dom_def)
  have hy: "y \<in> gamma_sign (int_sign d2)" "y \<in> gamma_ivl (int_ivl d2)"
           "y \<in> gamma_parity (int_parity d2)" "y \<in> gamma_congruence (int_congruence d2)"
    using assms(2) by (simp_all add: gamma_int_dom_def)
  have hr: "x + y \<in> gamma_congruence (int_congruence r)"
    using assms(3) by (simp add: gamma_int_dom_def)
  have s: "x \<in> gamma_sign (fst (inv_conservative (int_sign r) (int_sign d1) (int_sign d2))) \<and>
           y \<in> gamma_sign (snd (inv_conservative (int_sign r) (int_sign d1) (int_sign d2)))"
    using hx(1) hy(1) by (simp add: inv_conservative_def)
  have i: "x \<in> gamma_ivl (fst (inv_conservative (int_ivl r) (int_ivl d1) (int_ivl d2))) \<and>
           y \<in> gamma_ivl (snd (inv_conservative (int_ivl r) (int_ivl d1) (int_ivl d2)))"
    using hx(2) hy(2) by (simp add: inv_conservative_def)
  have p:
    "x \<in> gamma_parity
            (fst (inv_conservative (int_parity r) (int_parity d1) (int_parity d2))) \<and>
     y \<in> gamma_parity
            (snd (inv_conservative (int_parity r) (int_parity d1) (int_parity d2)))"
    using hx(3) hy(3) by (simp add: inv_conservative_def)
  have c:
    "x \<in> gamma_congruence
            (fst (inv_plus_congruence
                    (int_congruence r) (int_congruence d1) (int_congruence d2))) \<and>
     y \<in> gamma_congruence
            (snd (inv_plus_congruence
                    (int_congruence r) (int_congruence d1) (int_congruence d2)))"
    by (rule inv_plus_congruence_sound[OF hx(4) hy(4) hr])
  show ?thesis
    unfolding inv_plus_int_dom_raw_def Let_def case_prod_beta gamma_int_dom_def
    using s i p c by simp
qed

lemma inv_minus_int_dom_raw_sound:
  assumes "x \<in> gamma_int_dom d1" and "y \<in> gamma_int_dom d2" and "x - y \<in> gamma_int_dom r"
  shows
    "x \<in> gamma_int_dom (fst (inv_minus_int_dom_raw r d1 d2)) \<and>
     y \<in> gamma_int_dom (snd (inv_minus_int_dom_raw r d1 d2))"
proof -
  have hx: "x \<in> gamma_sign (int_sign d1)" "x \<in> gamma_ivl (int_ivl d1)"
           "x \<in> gamma_parity (int_parity d1)" "x \<in> gamma_congruence (int_congruence d1)"
    using assms(1) by (simp_all add: gamma_int_dom_def)
  have hy: "y \<in> gamma_sign (int_sign d2)" "y \<in> gamma_ivl (int_ivl d2)"
           "y \<in> gamma_parity (int_parity d2)" "y \<in> gamma_congruence (int_congruence d2)"
    using assms(2) by (simp_all add: gamma_int_dom_def)
  have hr: "x - y \<in> gamma_congruence (int_congruence r)"
    using assms(3) by (simp add: gamma_int_dom_def)
  have s: "x \<in> gamma_sign (fst (inv_conservative (int_sign r) (int_sign d1) (int_sign d2))) \<and>
           y \<in> gamma_sign (snd (inv_conservative (int_sign r) (int_sign d1) (int_sign d2)))"
    using hx(1) hy(1) by (simp add: inv_conservative_def)
  have i: "x \<in> gamma_ivl (fst (inv_conservative (int_ivl r) (int_ivl d1) (int_ivl d2))) \<and>
           y \<in> gamma_ivl (snd (inv_conservative (int_ivl r) (int_ivl d1) (int_ivl d2)))"
    using hx(2) hy(2) by (simp add: inv_conservative_def)
  have p:
    "x \<in> gamma_parity
            (fst (inv_conservative (int_parity r) (int_parity d1) (int_parity d2))) \<and>
     y \<in> gamma_parity
            (snd (inv_conservative (int_parity r) (int_parity d1) (int_parity d2)))"
    using hx(3) hy(3) by (simp add: inv_conservative_def)
  have c:
    "x \<in> gamma_congruence
            (fst (inv_minus_congruence
                    (int_congruence r) (int_congruence d1) (int_congruence d2))) \<and>
     y \<in> gamma_congruence
            (snd (inv_minus_congruence
                    (int_congruence r) (int_congruence d1) (int_congruence d2)))"
    by (rule inv_minus_congruence_sound[OF hx(4) hy(4) hr])
  show ?thesis
    unfolding inv_minus_int_dom_raw_def Let_def case_prod_beta gamma_int_dom_def
    using s i p c by simp
qed

lemma inv_times_int_dom_raw_sound:
  assumes "x \<in> gamma_int_dom d1" and "y \<in> gamma_int_dom d2" and "x * y \<in> gamma_int_dom r"
  shows
    "x \<in> gamma_int_dom (fst (inv_times_int_dom_raw r d1 d2)) \<and>
     y \<in> gamma_int_dom (snd (inv_times_int_dom_raw r d1 d2))"
proof -
  have hx: "x \<in> gamma_sign (int_sign d1)" "x \<in> gamma_ivl (int_ivl d1)"
           "x \<in> gamma_parity (int_parity d1)" "x \<in> gamma_congruence (int_congruence d1)"
    using assms(1) by (simp_all add: gamma_int_dom_def)
  have hy: "y \<in> gamma_sign (int_sign d2)" "y \<in> gamma_ivl (int_ivl d2)"
           "y \<in> gamma_parity (int_parity d2)" "y \<in> gamma_congruence (int_congruence d2)"
    using assms(2) by (simp_all add: gamma_int_dom_def)
  have hr: "x * y \<in> gamma_congruence (int_congruence r)"
    using assms(3) by (simp add: gamma_int_dom_def)
  have s: "x \<in> gamma_sign (fst (inv_conservative (int_sign r) (int_sign d1) (int_sign d2))) \<and>
           y \<in> gamma_sign (snd (inv_conservative (int_sign r) (int_sign d1) (int_sign d2)))"
    using hx(1) hy(1) by (simp add: inv_conservative_def)
  have i: "x \<in> gamma_ivl (fst (inv_conservative (int_ivl r) (int_ivl d1) (int_ivl d2))) \<and>
           y \<in> gamma_ivl (snd (inv_conservative (int_ivl r) (int_ivl d1) (int_ivl d2)))"
    using hx(2) hy(2) by (simp add: inv_conservative_def)
  have p:
    "x \<in> gamma_parity
            (fst (inv_conservative (int_parity r) (int_parity d1) (int_parity d2))) \<and>
     y \<in> gamma_parity
            (snd (inv_conservative (int_parity r) (int_parity d1) (int_parity d2)))"
    using hx(3) hy(3) by (simp add: inv_conservative_def)
  have c:
    "x \<in> gamma_congruence
            (fst (inv_times_congruence
                    (int_congruence r) (int_congruence d1) (int_congruence d2))) \<and>
     y \<in> gamma_congruence
            (snd (inv_times_congruence
                    (int_congruence r) (int_congruence d1) (int_congruence d2)))"
    by (rule inv_times_congruence_sound[OF hx(4) hy(4) hr])
  show ?thesis
    unfolding inv_times_int_dom_raw_def Let_def case_prod_beta gamma_int_dom_def
    using s i p c by simp
qed


subsection \<open>Raw reductiveness\<close>

lemma inv_less_int_dom_raw_reductive1:
  "fst (inv_less_int_dom_raw res d1 d2) \<le> d1"
  unfolding inv_less_int_dom_raw_def Let_def case_prod_beta less_eq_int_dom_ext_def
  by (simp add: inv_less_sign_reductive1 inv_less_ivl_reductive1 inv_less_congruence_def
        del: intersect_ivl_def)

lemma inv_less_int_dom_raw_reductive2:
  "snd (inv_less_int_dom_raw res d1 d2) \<le> d2"
  unfolding inv_less_int_dom_raw_def Let_def case_prod_beta less_eq_int_dom_ext_def
  by (simp add: inv_less_sign_reductive2 inv_less_ivl_reductive2 inv_less_congruence_def
        del: intersect_ivl_def)

lemma inv_eq_int_dom_raw_reductive1:
  "fst (inv_eq_int_dom_raw res d1 d2) \<le> d1"
proof (cases res)
  case True
  then show ?thesis
    unfolding inv_eq_int_dom_raw_def
    using intersect_int_dom_le1 by simp
next
  case False
  then show ?thesis
    unfolding inv_eq_int_dom_raw_def Let_def case_prod_beta less_eq_int_dom_ext_def
    by (simp add: inv_eq_sign_reductive1 inv_eq_ivl_reductive1
          del: intersect_ivl_def inv_eq_sign.simps)
qed

lemma inv_eq_int_dom_raw_reductive2:
  "snd (inv_eq_int_dom_raw res d1 d2) \<le> d2"
proof (cases res)
  case True
  then show ?thesis
    unfolding inv_eq_int_dom_raw_def
    using intersect_int_dom_le2 by simp
next
  case False
  then show ?thesis
    unfolding inv_eq_int_dom_raw_def Let_def case_prod_beta less_eq_int_dom_ext_def
    by (simp add: inv_eq_sign_reductive2 inv_eq_ivl_reductive2
          del: intersect_ivl_def inv_eq_sign.simps)
qed

lemma inv_plus_int_dom_raw_reductive1:
  "fst (inv_plus_int_dom_raw r d1 d2) \<le> d1"
proof -
  have s: "fst (inv_conservative (int_sign r) (int_sign d1) (int_sign d2)) \<le> int_sign d1"
    by (rule inv_conservative_reductive1)
  have i: "fst (inv_conservative (int_ivl r) (int_ivl d1) (int_ivl d2)) \<le> int_ivl d1"
    by (rule inv_conservative_reductive1)
  have p:
    "fst (inv_conservative (int_parity r) (int_parity d1) (int_parity d2)) \<le> int_parity d1"
    by (rule inv_conservative_reductive1)
  have c:
    "fst (inv_plus_congruence (int_congruence r) (int_congruence d1) (int_congruence d2)) \<le>
     int_congruence d1"
    using le_pair_fst[OF inv_plus_congruence_reductive] by simp
  show ?thesis
    unfolding inv_plus_int_dom_raw_def Let_def case_prod_beta less_eq_int_dom_ext_def
    using s i p c by simp
qed

lemma inv_plus_int_dom_raw_reductive2:
  "snd (inv_plus_int_dom_raw r d1 d2) \<le> d2"
proof -
  have s: "snd (inv_conservative (int_sign r) (int_sign d1) (int_sign d2)) \<le> int_sign d2"
    by (rule inv_conservative_reductive2)
  have i: "snd (inv_conservative (int_ivl r) (int_ivl d1) (int_ivl d2)) \<le> int_ivl d2"
    by (rule inv_conservative_reductive2)
  have p:
    "snd (inv_conservative (int_parity r) (int_parity d1) (int_parity d2)) \<le> int_parity d2"
    by (rule inv_conservative_reductive2)
  have c:
    "snd (inv_plus_congruence (int_congruence r) (int_congruence d1) (int_congruence d2)) \<le>
     int_congruence d2"
    using le_pair_snd[OF inv_plus_congruence_reductive] by simp
  show ?thesis
    unfolding inv_plus_int_dom_raw_def Let_def case_prod_beta less_eq_int_dom_ext_def
    using s i p c by simp
qed

lemma inv_minus_int_dom_raw_reductive1:
  "fst (inv_minus_int_dom_raw r d1 d2) \<le> d1"
proof -
  have s: "fst (inv_conservative (int_sign r) (int_sign d1) (int_sign d2)) \<le> int_sign d1"
    by (rule inv_conservative_reductive1)
  have i: "fst (inv_conservative (int_ivl r) (int_ivl d1) (int_ivl d2)) \<le> int_ivl d1"
    by (rule inv_conservative_reductive1)
  have p:
    "fst (inv_conservative (int_parity r) (int_parity d1) (int_parity d2)) \<le> int_parity d1"
    by (rule inv_conservative_reductive1)
  have c:
    "fst (inv_minus_congruence (int_congruence r) (int_congruence d1) (int_congruence d2)) \<le>
     int_congruence d1"
    using le_pair_fst[OF inv_minus_congruence_reductive] by simp
  show ?thesis
    unfolding inv_minus_int_dom_raw_def Let_def case_prod_beta less_eq_int_dom_ext_def
    using s i p c by simp
qed

lemma inv_minus_int_dom_raw_reductive2:
  "snd (inv_minus_int_dom_raw r d1 d2) \<le> d2"
proof -
  have s: "snd (inv_conservative (int_sign r) (int_sign d1) (int_sign d2)) \<le> int_sign d2"
    by (rule inv_conservative_reductive2)
  have i: "snd (inv_conservative (int_ivl r) (int_ivl d1) (int_ivl d2)) \<le> int_ivl d2"
    by (rule inv_conservative_reductive2)
  have p:
    "snd (inv_conservative (int_parity r) (int_parity d1) (int_parity d2)) \<le> int_parity d2"
    by (rule inv_conservative_reductive2)
  have c:
    "snd (inv_minus_congruence (int_congruence r) (int_congruence d1) (int_congruence d2)) \<le>
     int_congruence d2"
    using le_pair_snd[OF inv_minus_congruence_reductive] by simp
  show ?thesis
    unfolding inv_minus_int_dom_raw_def Let_def case_prod_beta less_eq_int_dom_ext_def
    using s i p c by simp
qed

lemma inv_times_int_dom_raw_reductive1:
  "fst (inv_times_int_dom_raw r d1 d2) \<le> d1"
proof -
  have s: "fst (inv_conservative (int_sign r) (int_sign d1) (int_sign d2)) \<le> int_sign d1"
    by (rule inv_conservative_reductive1)
  have i: "fst (inv_conservative (int_ivl r) (int_ivl d1) (int_ivl d2)) \<le> int_ivl d1"
    by (rule inv_conservative_reductive1)
  have p:
    "fst (inv_conservative (int_parity r) (int_parity d1) (int_parity d2)) \<le> int_parity d1"
    by (rule inv_conservative_reductive1)
  have c:
    "fst (inv_times_congruence (int_congruence r) (int_congruence d1) (int_congruence d2)) \<le>
     int_congruence d1"
    using le_pair_fst[OF inv_times_congruence_reductive] by simp
  show ?thesis
    unfolding inv_times_int_dom_raw_def Let_def case_prod_beta less_eq_int_dom_ext_def
    using s i p c by simp
qed

lemma inv_times_int_dom_raw_reductive2:
  "snd (inv_times_int_dom_raw r d1 d2) \<le> d2"
proof -
  have s: "snd (inv_conservative (int_sign r) (int_sign d1) (int_sign d2)) \<le> int_sign d2"
    by (rule inv_conservative_reductive2)
  have i: "snd (inv_conservative (int_ivl r) (int_ivl d1) (int_ivl d2)) \<le> int_ivl d2"
    by (rule inv_conservative_reductive2)
  have p:
    "snd (inv_conservative (int_parity r) (int_parity d1) (int_parity d2)) \<le> int_parity d2"
    by (rule inv_conservative_reductive2)
  have c:
    "snd (inv_times_congruence (int_congruence r) (int_congruence d1) (int_congruence d2)) \<le>
     int_congruence d2"
    using le_pair_snd[OF inv_times_congruence_reductive] by simp
  show ?thesis
    unfolding inv_times_int_dom_raw_def Let_def case_prod_beta less_eq_int_dom_ext_def
    using s i p c by simp
qed


subsection \<open>Raw monotonicity\<close>

lemma inv_less_int_dom_raw_mono:
  assumes "d1 \<le> d2" and "e1 \<le> e2"
  shows
    "fst (inv_less_int_dom_raw res d1 e1) \<le> fst (inv_less_int_dom_raw res d2 e2) \<and>
     snd (inv_less_int_dom_raw res d1 e1) \<le> snd (inv_less_int_dom_raw res d2 e2)"
proof -
  have hd: "int_sign d1 \<le> int_sign d2" "int_ivl d1 \<le> int_ivl d2"
           "int_parity d1 \<le> int_parity d2" "int_congruence d1 \<le> int_congruence d2"
    using assms(1) by (simp_all add: less_eq_int_dom_ext_def)
  have he: "int_sign e1 \<le> int_sign e2" "int_ivl e1 \<le> int_ivl e2"
           "int_parity e1 \<le> int_parity e2" "int_congruence e1 \<le> int_congruence e2"
    using assms(2) by (simp_all add: less_eq_int_dom_ext_def)
  have s:
    "fst (inv_less_sign res (int_sign d1) (int_sign e1)) \<le>
     fst (inv_less_sign res (int_sign d2) (int_sign e2)) \<and>
     snd (inv_less_sign res (int_sign d1) (int_sign e1)) \<le>
     snd (inv_less_sign res (int_sign d2) (int_sign e2))"
    by (rule inv_less_sign_mono[OF hd(1) he(1)])
  have i:
    "fst (inv_less_ivl res (int_ivl d1) (int_ivl e1)) \<le>
     fst (inv_less_ivl res (int_ivl d2) (int_ivl e2)) \<and>
     snd (inv_less_ivl res (int_ivl d1) (int_ivl e1)) \<le>
     snd (inv_less_ivl res (int_ivl d2) (int_ivl e2))"
    by (rule inv_less_ivl_mono[OF hd(2) he(2)])
  have c:
    "fst (inv_less_congruence res (int_congruence d1) (int_congruence e1)) \<le>
     fst (inv_less_congruence res (int_congruence d2) (int_congruence e2)) \<and>
     snd (inv_less_congruence res (int_congruence d1) (int_congruence e1)) \<le>
     snd (inv_less_congruence res (int_congruence d2) (int_congruence e2))"
    using hd(4) he(4) by (simp add: inv_less_congruence_def)
  show ?thesis
    unfolding inv_less_int_dom_raw_def Let_def case_prod_beta less_eq_int_dom_ext_def
    using s i c hd(3) he(3) by simp
qed

lemma inv_eq_int_dom_raw_mono:
  assumes "d1 \<le> d2" and "e1 \<le> e2"
  shows
    "fst (inv_eq_int_dom_raw res d1 e1) \<le> fst (inv_eq_int_dom_raw res d2 e2) \<and>
     snd (inv_eq_int_dom_raw res d1 e1) \<le> snd (inv_eq_int_dom_raw res d2 e2)"
proof (cases res)
  case True
  then show ?thesis
    unfolding inv_eq_int_dom_raw_def
    using intersect_int_dom_mono[OF assms(1) assms(2)] by simp
next
  case False
  have hd: "int_sign d1 \<le> int_sign d2" "int_ivl d1 \<le> int_ivl d2"
           "int_parity d1 \<le> int_parity d2" "int_congruence d1 \<le> int_congruence d2"
    using assms(1) by (simp_all add: less_eq_int_dom_ext_def)
  have he: "int_sign e1 \<le> int_sign e2" "int_ivl e1 \<le> int_ivl e2"
           "int_parity e1 \<le> int_parity e2" "int_congruence e1 \<le> int_congruence e2"
    using assms(2) by (simp_all add: less_eq_int_dom_ext_def)
  have s:
    "fst (inv_eq_sign False (int_sign d1) (int_sign e1)) \<le>
     fst (inv_eq_sign False (int_sign d2) (int_sign e2)) \<and>
     snd (inv_eq_sign False (int_sign d1) (int_sign e1)) \<le>
     snd (inv_eq_sign False (int_sign d2) (int_sign e2))"
    by (rule inv_eq_sign_mono[OF hd(1) he(1)])
  have i:
    "fst (inv_eq_ivl False (int_ivl d1) (int_ivl e1)) \<le>
     fst (inv_eq_ivl False (int_ivl d2) (int_ivl e2)) \<and>
     snd (inv_eq_ivl False (int_ivl d1) (int_ivl e1)) \<le>
     snd (inv_eq_ivl False (int_ivl d2) (int_ivl e2))"
    by (rule inv_eq_ivl_mono[OF hd(2) he(2)])
  have c:
    "fst (inv_eq_congruence False (int_congruence d1) (int_congruence e1)) \<le>
     fst (inv_eq_congruence False (int_congruence d2) (int_congruence e2)) \<and>
     snd (inv_eq_congruence False (int_congruence d1) (int_congruence e1)) \<le>
     snd (inv_eq_congruence False (int_congruence d2) (int_congruence e2))"
    using inv_eq_congruence_mono[OF hd(4) he(4), where result=False]
    by (simp add: le_pair_def)
  show ?thesis
    unfolding inv_eq_int_dom_raw_def Let_def case_prod_beta less_eq_int_dom_ext_def
    using False s i c hd(3) he(3) by (simp del: inv_eq_sign.simps)
qed

lemma inv_plus_int_dom_raw_mono:
  assumes "r1 \<le> r2" and "d1 \<le> d2" and "e1 \<le> e2"
  shows
    "fst (inv_plus_int_dom_raw r1 d1 e1) \<le> fst (inv_plus_int_dom_raw r2 d2 e2) \<and>
     snd (inv_plus_int_dom_raw r1 d1 e1) \<le> snd (inv_plus_int_dom_raw r2 d2 e2)"
proof -
  have hr: "int_congruence r1 \<le> int_congruence r2"
    using assms(1) by (simp add: less_eq_int_dom_ext_def)
  have hd: "int_sign d1 \<le> int_sign d2" "int_ivl d1 \<le> int_ivl d2"
           "int_parity d1 \<le> int_parity d2" "int_congruence d1 \<le> int_congruence d2"
    using assms(2) by (simp_all add: less_eq_int_dom_ext_def)
  have he: "int_sign e1 \<le> int_sign e2" "int_ivl e1 \<le> int_ivl e2"
           "int_parity e1 \<le> int_parity e2" "int_congruence e1 \<le> int_congruence e2"
    using assms(3) by (simp_all add: less_eq_int_dom_ext_def)
  have s:
    "fst (inv_conservative (int_sign r1) (int_sign d1) (int_sign e1)) \<le>
     fst (inv_conservative (int_sign r2) (int_sign d2) (int_sign e2)) \<and>
     snd (inv_conservative (int_sign r1) (int_sign d1) (int_sign e1)) \<le>
     snd (inv_conservative (int_sign r2) (int_sign d2) (int_sign e2))"
    using hd(1) he(1) by (simp add: inv_conservative_def)
  have i:
    "fst (inv_conservative (int_ivl r1) (int_ivl d1) (int_ivl e1)) \<le>
     fst (inv_conservative (int_ivl r2) (int_ivl d2) (int_ivl e2)) \<and>
     snd (inv_conservative (int_ivl r1) (int_ivl d1) (int_ivl e1)) \<le>
     snd (inv_conservative (int_ivl r2) (int_ivl d2) (int_ivl e2))"
    using hd(2) he(2) by (simp add: inv_conservative_def)
  have p:
    "fst (inv_conservative (int_parity r1) (int_parity d1) (int_parity e1)) \<le>
     fst (inv_conservative (int_parity r2) (int_parity d2) (int_parity e2)) \<and>
     snd (inv_conservative (int_parity r1) (int_parity d1) (int_parity e1)) \<le>
     snd (inv_conservative (int_parity r2) (int_parity d2) (int_parity e2))"
    using hd(3) he(3) by (simp add: inv_conservative_def)
  have c:
    "fst (inv_plus_congruence (int_congruence r1) (int_congruence d1) (int_congruence e1)) \<le>
     fst (inv_plus_congruence (int_congruence r2) (int_congruence d2) (int_congruence e2)) \<and>
     snd (inv_plus_congruence (int_congruence r1) (int_congruence d1) (int_congruence e1)) \<le>
     snd (inv_plus_congruence (int_congruence r2) (int_congruence d2) (int_congruence e2))"
    using inv_plus_congruence_mono[OF hr hd(4) he(4)] by (simp add: le_pair_def)
  show ?thesis
    unfolding inv_plus_int_dom_raw_def Let_def case_prod_beta less_eq_int_dom_ext_def
    using s i p c by simp
qed

lemma inv_minus_int_dom_raw_mono:
  assumes "r1 \<le> r2" and "d1 \<le> d2" and "e1 \<le> e2"
  shows
    "fst (inv_minus_int_dom_raw r1 d1 e1) \<le> fst (inv_minus_int_dom_raw r2 d2 e2) \<and>
     snd (inv_minus_int_dom_raw r1 d1 e1) \<le> snd (inv_minus_int_dom_raw r2 d2 e2)"
proof -
  have hr: "int_congruence r1 \<le> int_congruence r2"
    using assms(1) by (simp add: less_eq_int_dom_ext_def)
  have hd: "int_sign d1 \<le> int_sign d2" "int_ivl d1 \<le> int_ivl d2"
           "int_parity d1 \<le> int_parity d2" "int_congruence d1 \<le> int_congruence d2"
    using assms(2) by (simp_all add: less_eq_int_dom_ext_def)
  have he: "int_sign e1 \<le> int_sign e2" "int_ivl e1 \<le> int_ivl e2"
           "int_parity e1 \<le> int_parity e2" "int_congruence e1 \<le> int_congruence e2"
    using assms(3) by (simp_all add: less_eq_int_dom_ext_def)
  have s:
    "fst (inv_conservative (int_sign r1) (int_sign d1) (int_sign e1)) \<le>
     fst (inv_conservative (int_sign r2) (int_sign d2) (int_sign e2)) \<and>
     snd (inv_conservative (int_sign r1) (int_sign d1) (int_sign e1)) \<le>
     snd (inv_conservative (int_sign r2) (int_sign d2) (int_sign e2))"
    using hd(1) he(1) by (simp add: inv_conservative_def)
  have i:
    "fst (inv_conservative (int_ivl r1) (int_ivl d1) (int_ivl e1)) \<le>
     fst (inv_conservative (int_ivl r2) (int_ivl d2) (int_ivl e2)) \<and>
     snd (inv_conservative (int_ivl r1) (int_ivl d1) (int_ivl e1)) \<le>
     snd (inv_conservative (int_ivl r2) (int_ivl d2) (int_ivl e2))"
    using hd(2) he(2) by (simp add: inv_conservative_def)
  have p:
    "fst (inv_conservative (int_parity r1) (int_parity d1) (int_parity e1)) \<le>
     fst (inv_conservative (int_parity r2) (int_parity d2) (int_parity e2)) \<and>
     snd (inv_conservative (int_parity r1) (int_parity d1) (int_parity e1)) \<le>
     snd (inv_conservative (int_parity r2) (int_parity d2) (int_parity e2))"
    using hd(3) he(3) by (simp add: inv_conservative_def)
  have c:
    "fst (inv_minus_congruence (int_congruence r1) (int_congruence d1) (int_congruence e1)) \<le>
     fst (inv_minus_congruence (int_congruence r2) (int_congruence d2) (int_congruence e2)) \<and>
     snd (inv_minus_congruence (int_congruence r1) (int_congruence d1) (int_congruence e1)) \<le>
     snd (inv_minus_congruence (int_congruence r2) (int_congruence d2) (int_congruence e2))"
    using inv_minus_congruence_mono[OF hr hd(4) he(4)] by (simp add: le_pair_def)
  show ?thesis
    unfolding inv_minus_int_dom_raw_def Let_def case_prod_beta less_eq_int_dom_ext_def
    using s i p c by simp
qed

lemma inv_times_int_dom_raw_mono:
  assumes "r1 \<le> r2" and "d1 \<le> d2" and "e1 \<le> e2"
  shows
    "fst (inv_times_int_dom_raw r1 d1 e1) \<le> fst (inv_times_int_dom_raw r2 d2 e2) \<and>
     snd (inv_times_int_dom_raw r1 d1 e1) \<le> snd (inv_times_int_dom_raw r2 d2 e2)"
proof -
  have hr: "int_congruence r1 \<le> int_congruence r2"
    using assms(1) by (simp add: less_eq_int_dom_ext_def)
  have hd: "int_sign d1 \<le> int_sign d2" "int_ivl d1 \<le> int_ivl d2"
           "int_parity d1 \<le> int_parity d2" "int_congruence d1 \<le> int_congruence d2"
    using assms(2) by (simp_all add: less_eq_int_dom_ext_def)
  have he: "int_sign e1 \<le> int_sign e2" "int_ivl e1 \<le> int_ivl e2"
           "int_parity e1 \<le> int_parity e2" "int_congruence e1 \<le> int_congruence e2"
    using assms(3) by (simp_all add: less_eq_int_dom_ext_def)
  have s:
    "fst (inv_conservative (int_sign r1) (int_sign d1) (int_sign e1)) \<le>
     fst (inv_conservative (int_sign r2) (int_sign d2) (int_sign e2)) \<and>
     snd (inv_conservative (int_sign r1) (int_sign d1) (int_sign e1)) \<le>
     snd (inv_conservative (int_sign r2) (int_sign d2) (int_sign e2))"
    using hd(1) he(1) by (simp add: inv_conservative_def)
  have i:
    "fst (inv_conservative (int_ivl r1) (int_ivl d1) (int_ivl e1)) \<le>
     fst (inv_conservative (int_ivl r2) (int_ivl d2) (int_ivl e2)) \<and>
     snd (inv_conservative (int_ivl r1) (int_ivl d1) (int_ivl e1)) \<le>
     snd (inv_conservative (int_ivl r2) (int_ivl d2) (int_ivl e2))"
    using hd(2) he(2) by (simp add: inv_conservative_def)
  have p:
    "fst (inv_conservative (int_parity r1) (int_parity d1) (int_parity e1)) \<le>
     fst (inv_conservative (int_parity r2) (int_parity d2) (int_parity e2)) \<and>
     snd (inv_conservative (int_parity r1) (int_parity d1) (int_parity e1)) \<le>
     snd (inv_conservative (int_parity r2) (int_parity d2) (int_parity e2))"
    using hd(3) he(3) by (simp add: inv_conservative_def)
  have c:
    "fst (inv_times_congruence (int_congruence r1) (int_congruence d1) (int_congruence e1)) \<le>
     fst (inv_times_congruence (int_congruence r2) (int_congruence d2) (int_congruence e2)) \<and>
     snd (inv_times_congruence (int_congruence r1) (int_congruence d1) (int_congruence e1)) \<le>
     snd (inv_times_congruence (int_congruence r2) (int_congruence d2) (int_congruence e2))"
    using inv_times_congruence_mono[OF hr hd(4) he(4)] by (simp add: le_pair_def)
  show ?thesis
    unfolding inv_times_int_dom_raw_def Let_def case_prod_beta less_eq_int_dom_ext_def
    using s i p c by simp
qed


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


subsection \<open>Mode-aware soundness\<close>

lemma inv_less_int_dom_sound:
  assumes "x \<in> gamma_int_dom d1" and "y \<in> gamma_int_dom d2" and "(x < y) = res"
  shows
    "x \<in> gamma_int_dom (fst (inv_less_int_dom mode res d1 d2)) \<and>
     y \<in> gamma_int_dom (snd (inv_less_int_dom mode res d1 d2))"
  unfolding inv_less_int_dom_def Let_def case_prod_beta
  using inv_less_int_dom_raw_sound[OF assms] refine_exact by simp

lemma inv_eq_int_dom_sound:
  assumes "x \<in> gamma_int_dom d1" and "y \<in> gamma_int_dom d2" and "(x = y) = res"
  shows
    "x \<in> gamma_int_dom (fst (inv_eq_int_dom mode res d1 d2)) \<and>
     y \<in> gamma_int_dom (snd (inv_eq_int_dom mode res d1 d2))"
  unfolding inv_eq_int_dom_def Let_def case_prod_beta
  using inv_eq_int_dom_raw_sound[OF assms] refine_exact by simp

lemma inv_plus_int_dom_sound:
  assumes "x \<in> gamma_int_dom d1" and "y \<in> gamma_int_dom d2" and "x + y \<in> gamma_int_dom r"
  shows
    "x \<in> gamma_int_dom (fst (inv_plus_int_dom mode r d1 d2)) \<and>
     y \<in> gamma_int_dom (snd (inv_plus_int_dom mode r d1 d2))"
  unfolding inv_plus_int_dom_def Let_def case_prod_beta
  using inv_plus_int_dom_raw_sound[OF assms] refine_exact by simp

lemma inv_minus_int_dom_sound:
  assumes "x \<in> gamma_int_dom d1" and "y \<in> gamma_int_dom d2" and "x - y \<in> gamma_int_dom r"
  shows
    "x \<in> gamma_int_dom (fst (inv_minus_int_dom mode r d1 d2)) \<and>
     y \<in> gamma_int_dom (snd (inv_minus_int_dom mode r d1 d2))"
  unfolding inv_minus_int_dom_def Let_def case_prod_beta
  using inv_minus_int_dom_raw_sound[OF assms] refine_exact by simp

lemma inv_times_int_dom_sound:
  assumes "x \<in> gamma_int_dom d1" and "y \<in> gamma_int_dom d2" and "x * y \<in> gamma_int_dom r"
  shows
    "x \<in> gamma_int_dom (fst (inv_times_int_dom mode r d1 d2)) \<and>
     y \<in> gamma_int_dom (snd (inv_times_int_dom mode r d1 d2))"
  unfolding inv_times_int_dom_def Let_def case_prod_beta
  using inv_times_int_dom_raw_sound[OF assms] refine_exact by simp


subsection \<open>Mode-aware reductiveness\<close>

lemma inv_less_int_dom_reductive1:
  "fst (inv_less_int_dom mode res d1 d2) \<le> d1"
  unfolding inv_less_int_dom_def Let_def case_prod_beta
  using refine_mode_reductive_trans[OF inv_less_int_dom_raw_reductive1] by simp

lemma inv_less_int_dom_reductive2:
  "snd (inv_less_int_dom mode res d1 d2) \<le> d2"
  unfolding inv_less_int_dom_def Let_def case_prod_beta
  using refine_mode_reductive_trans[OF inv_less_int_dom_raw_reductive2] by simp

lemma inv_eq_int_dom_reductive1:
  "fst (inv_eq_int_dom mode res d1 d2) \<le> d1"
  unfolding inv_eq_int_dom_def Let_def case_prod_beta
  using refine_mode_reductive_trans[OF inv_eq_int_dom_raw_reductive1] by simp

lemma inv_eq_int_dom_reductive2:
  "snd (inv_eq_int_dom mode res d1 d2) \<le> d2"
  unfolding inv_eq_int_dom_def Let_def case_prod_beta
  using refine_mode_reductive_trans[OF inv_eq_int_dom_raw_reductive2] by simp

lemma inv_plus_int_dom_reductive1:
  "fst (inv_plus_int_dom mode r d1 d2) \<le> d1"
  unfolding inv_plus_int_dom_def Let_def case_prod_beta
  using refine_mode_reductive_trans[OF inv_plus_int_dom_raw_reductive1] by simp

lemma inv_plus_int_dom_reductive2:
  "snd (inv_plus_int_dom mode r d1 d2) \<le> d2"
  unfolding inv_plus_int_dom_def Let_def case_prod_beta
  using refine_mode_reductive_trans[OF inv_plus_int_dom_raw_reductive2] by simp

lemma inv_minus_int_dom_reductive1:
  "fst (inv_minus_int_dom mode r d1 d2) \<le> d1"
  unfolding inv_minus_int_dom_def Let_def case_prod_beta
  using refine_mode_reductive_trans[OF inv_minus_int_dom_raw_reductive1] by simp

lemma inv_minus_int_dom_reductive2:
  "snd (inv_minus_int_dom mode r d1 d2) \<le> d2"
  unfolding inv_minus_int_dom_def Let_def case_prod_beta
  using refine_mode_reductive_trans[OF inv_minus_int_dom_raw_reductive2] by simp

lemma inv_times_int_dom_reductive1:
  "fst (inv_times_int_dom mode r d1 d2) \<le> d1"
  unfolding inv_times_int_dom_def Let_def case_prod_beta
  using refine_mode_reductive_trans[OF inv_times_int_dom_raw_reductive1] by simp

lemma inv_times_int_dom_reductive2:
  "snd (inv_times_int_dom mode r d1 d2) \<le> d2"
  unfolding inv_times_int_dom_def Let_def case_prod_beta
  using refine_mode_reductive_trans[OF inv_times_int_dom_raw_reductive2] by simp


subsection \<open>Mode-aware monotonicity (Never/Once only)\<close>

lemma inv_less_int_dom_mono:
  assumes "mode \<noteq> Refine_Fixpoint" and "d1 \<le> d2" and "e1 \<le> e2"
  shows
    "fst (inv_less_int_dom mode res d1 e1) \<le> fst (inv_less_int_dom mode res d2 e2) \<and>
     snd (inv_less_int_dom mode res d1 e1) \<le> snd (inv_less_int_dom mode res d2 e2)"
proof -
  have raw:
    "fst (inv_less_int_dom_raw res d1 e1) \<le> fst (inv_less_int_dom_raw res d2 e2) \<and>
     snd (inv_less_int_dom_raw res d1 e1) \<le> snd (inv_less_int_dom_raw res d2 e2)"
    by (rule inv_less_int_dom_raw_mono[OF assms(2,3)])
  show ?thesis
    unfolding inv_less_int_dom_def Let_def case_prod_beta
    using refine_mode_mono_trans[OF assms(1) raw[THEN conjunct1]]
          refine_mode_mono_trans[OF assms(1) raw[THEN conjunct2]]
    by simp
qed

lemma inv_eq_int_dom_mono:
  assumes "mode \<noteq> Refine_Fixpoint" and "d1 \<le> d2" and "e1 \<le> e2"
  shows
    "fst (inv_eq_int_dom mode res d1 e1) \<le> fst (inv_eq_int_dom mode res d2 e2) \<and>
     snd (inv_eq_int_dom mode res d1 e1) \<le> snd (inv_eq_int_dom mode res d2 e2)"
proof -
  have raw:
    "fst (inv_eq_int_dom_raw res d1 e1) \<le> fst (inv_eq_int_dom_raw res d2 e2) \<and>
     snd (inv_eq_int_dom_raw res d1 e1) \<le> snd (inv_eq_int_dom_raw res d2 e2)"
    by (rule inv_eq_int_dom_raw_mono[OF assms(2,3)])
  show ?thesis
    unfolding inv_eq_int_dom_def Let_def case_prod_beta
    using refine_mode_mono_trans[OF assms(1) raw[THEN conjunct1]]
          refine_mode_mono_trans[OF assms(1) raw[THEN conjunct2]]
    by simp
qed

lemma inv_plus_int_dom_mono:
  assumes "mode \<noteq> Refine_Fixpoint" and "r1 \<le> r2" and "d1 \<le> d2" and "e1 \<le> e2"
  shows
    "fst (inv_plus_int_dom mode r1 d1 e1) \<le> fst (inv_plus_int_dom mode r2 d2 e2) \<and>
     snd (inv_plus_int_dom mode r1 d1 e1) \<le> snd (inv_plus_int_dom mode r2 d2 e2)"
proof -
  have raw:
    "fst (inv_plus_int_dom_raw r1 d1 e1) \<le> fst (inv_plus_int_dom_raw r2 d2 e2) \<and>
     snd (inv_plus_int_dom_raw r1 d1 e1) \<le> snd (inv_plus_int_dom_raw r2 d2 e2)"
    by (rule inv_plus_int_dom_raw_mono[OF assms(2,3,4)])
  show ?thesis
    unfolding inv_plus_int_dom_def Let_def case_prod_beta
    using refine_mode_mono_trans[OF assms(1) raw[THEN conjunct1]]
          refine_mode_mono_trans[OF assms(1) raw[THEN conjunct2]]
    by simp
qed

lemma inv_minus_int_dom_mono:
  assumes "mode \<noteq> Refine_Fixpoint" and "r1 \<le> r2" and "d1 \<le> d2" and "e1 \<le> e2"
  shows
    "fst (inv_minus_int_dom mode r1 d1 e1) \<le> fst (inv_minus_int_dom mode r2 d2 e2) \<and>
     snd (inv_minus_int_dom mode r1 d1 e1) \<le> snd (inv_minus_int_dom mode r2 d2 e2)"
proof -
  have raw:
    "fst (inv_minus_int_dom_raw r1 d1 e1) \<le> fst (inv_minus_int_dom_raw r2 d2 e2) \<and>
     snd (inv_minus_int_dom_raw r1 d1 e1) \<le> snd (inv_minus_int_dom_raw r2 d2 e2)"
    by (rule inv_minus_int_dom_raw_mono[OF assms(2,3,4)])
  show ?thesis
    unfolding inv_minus_int_dom_def Let_def case_prod_beta
    using refine_mode_mono_trans[OF assms(1) raw[THEN conjunct1]]
          refine_mode_mono_trans[OF assms(1) raw[THEN conjunct2]]
    by simp
qed

lemma inv_times_int_dom_mono:
  assumes "mode \<noteq> Refine_Fixpoint" and "r1 \<le> r2" and "d1 \<le> d2" and "e1 \<le> e2"
  shows
    "fst (inv_times_int_dom mode r1 d1 e1) \<le> fst (inv_times_int_dom mode r2 d2 e2) \<and>
     snd (inv_times_int_dom mode r1 d1 e1) \<le> snd (inv_times_int_dom mode r2 d2 e2)"
proof -
  have raw:
    "fst (inv_times_int_dom_raw r1 d1 e1) \<le> fst (inv_times_int_dom_raw r2 d2 e2) \<and>
     snd (inv_times_int_dom_raw r1 d1 e1) \<le> snd (inv_times_int_dom_raw r2 d2 e2)"
    by (rule inv_times_int_dom_raw_mono[OF assms(2,3,4)])
  show ?thesis
    unfolding inv_times_int_dom_def Let_def case_prod_beta
    using refine_mode_mono_trans[OF assms(1) raw[THEN conjunct1]]
          refine_mode_mono_trans[OF assms(1) raw[THEN conjunct2]]
    by simp
qed


subsection \<open>Backward-domain interpretation\<close>

text \<open>
  Refine_Never and Refine_Once each get the full backward_domain_refined
  interpretation: soundness, reductiveness, and monotonicity, all proved
  above uniformly in \<open>mode\<close> (soundness/reductiveness) or restricted to
  \<open>mode \<noteq> Refine_Fixpoint\<close> (monotonicity). Refine_Fixpoint gets only the
  weaker backward_domain interpretation -- soundness alone -- since
  \<open>refine_fix\<close>'s total wrapper has no monotonicity theorem
  (\<open>Int_Refinement.thy\<close>): a faithful transliteration of Goblint's
  \<open>fixpoint\<close> loop, not an oversight.
\<close>

abbreviation intersect_int_dom_never :: "int_dom => int_dom => int_dom" where
  "intersect_int_dom_never == intersect_int_dom_mode Refine_Never"

abbreviation aval_int_dom_never :: "exp => (vname => int_dom) => int_dom" where
  "aval_int_dom_never == aval_int_dom Refine_Never"

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
    backward_domain_refined
      intersect_int_dom_never aval_int_dom_never
      inv_less_int_dom_never inv_eq_int_dom_never
      inv_plus_int_dom_never inv_minus_int_dom_never inv_times_int_dom_never
  defines
    afilter_int_dom_never = int_dom_backward_never.afilter
    and bfilter_int_dom_never = int_dom_backward_never.bfilter
    and afilter_int_dom_never_st = int_dom_backward_never.afilter_st
    and bfilter_int_dom_never_st = int_dom_backward_never.bfilter_st
proof unfold_locales
  fix n :: int and a b :: int_dom
  assume "n \<in> gamma a" and "n \<in> gamma b"
  then show "n \<in> gamma (intersect_int_dom_mode Refine_Never a b)"
    using intersect_int_dom_mode_sound by simp
next
  fix s :: store and e :: exp and sigma :: "vname => int_dom"
  assume "\<forall>x. s x \<in> gamma (sigma x)"
  then show "aval e s \<in> gamma (aval_int_dom Refine_Never e sigma)"
    using aval_int_dom_sound by simp
next
  fix n1 n2 :: int and a1 a2 :: int_dom and res :: bool
  assume "n1 \<in> gamma a1" and "n2 \<in> gamma a2" and "(n1 < n2) = res"
  then show
    "n1 \<in> gamma (fst (inv_less_int_dom Refine_Never res a1 a2)) \<and>
     n2 \<in> gamma (snd (inv_less_int_dom Refine_Never res a1 a2))"
    using inv_less_int_dom_sound by simp
next
  fix n1 n2 :: int and a1 a2 :: int_dom and res :: bool
  assume "n1 \<in> gamma a1" and "n2 \<in> gamma a2" and "(n1 = n2) = res"
  then show
    "n1 \<in> gamma (fst (inv_eq_int_dom Refine_Never res a1 a2)) \<and>
     n2 \<in> gamma (snd (inv_eq_int_dom Refine_Never res a1 a2))"
    using inv_eq_int_dom_sound by simp
next
  fix n1 n2 :: int and a1 a2 r :: int_dom
  assume "n1 \<in> gamma a1" and "n2 \<in> gamma a2" and "n1 + n2 \<in> gamma r"
  then show
    "n1 \<in> gamma (fst (inv_plus_int_dom Refine_Never r a1 a2)) \<and>
     n2 \<in> gamma (snd (inv_plus_int_dom Refine_Never r a1 a2))"
    using inv_plus_int_dom_sound by simp
next
  fix n1 n2 :: int and a1 a2 r :: int_dom
  assume "n1 \<in> gamma a1" and "n2 \<in> gamma a2" and "n1 - n2 \<in> gamma r"
  then show
    "n1 \<in> gamma (fst (inv_minus_int_dom Refine_Never r a1 a2)) \<and>
     n2 \<in> gamma (snd (inv_minus_int_dom Refine_Never r a1 a2))"
    using inv_minus_int_dom_sound by simp
next
  fix n1 n2 :: int and a1 a2 r :: int_dom
  assume "n1 \<in> gamma a1" and "n2 \<in> gamma a2" and "n1 * n2 \<in> gamma r"
  then show
    "n1 \<in> gamma (fst (inv_times_int_dom Refine_Never r a1 a2)) \<and>
     n2 \<in> gamma (snd (inv_times_int_dom Refine_Never r a1 a2))"
    using inv_times_int_dom_sound by simp
next
  fix a1 a2 b1 b2 :: int_dom
  assume A: "a1 \<le> a2" and B: "b1 \<le> b2"
  have ne: "Refine_Never \<noteq> Refine_Fixpoint" by simp
  show
    "intersect_int_dom_mode Refine_Never a1 b1 \<le>
     intersect_int_dom_mode Refine_Never a2 b2"
    using intersect_int_dom_mode_mono[OF ne A B] .
next
  fix e :: exp and sigma1 sigma2 :: "vname => int_dom"
  assume S: "sigma1 \<le> sigma2"
  have ne: "Refine_Never \<noteq> Refine_Fixpoint" by simp
  show "aval_int_dom Refine_Never e sigma1 \<le> aval_int_dom Refine_Never e sigma2"
    using aval_int_dom_mono[OF ne S] .
next
  fix x1 x2 y1 y2 :: int_dom and res :: bool
  assume A: "x1 \<le> x2" and B: "y1 \<le> y2"
  have ne: "Refine_Never \<noteq> Refine_Fixpoint" by simp
  show
    "le_pair (inv_less_int_dom Refine_Never res x1 y1)
       (inv_less_int_dom Refine_Never res x2 y2)"
    using inv_less_int_dom_mono[OF ne A B] by (simp add: le_pair_def)
next
  fix x1 x2 y1 y2 :: int_dom and res :: bool
  assume A: "x1 \<le> x2" and B: "y1 \<le> y2"
  have ne: "Refine_Never \<noteq> Refine_Fixpoint" by simp
  show
    "le_pair (inv_eq_int_dom Refine_Never res x1 y1)
       (inv_eq_int_dom Refine_Never res x2 y2)"
    using inv_eq_int_dom_mono[OF ne A B] by (simp add: le_pair_def)
next
  fix r1 r2 x1 x2 y1 y2 :: int_dom
  assume RR: "r1 \<le> r2" and A: "x1 \<le> x2" and B: "y1 \<le> y2"
  have ne: "Refine_Never \<noteq> Refine_Fixpoint" by simp
  show
    "le_pair (inv_plus_int_dom Refine_Never r1 x1 y1)
       (inv_plus_int_dom Refine_Never r2 x2 y2)"
    using inv_plus_int_dom_mono[OF ne RR A B] by (simp add: le_pair_def)
next
  fix r1 r2 x1 x2 y1 y2 :: int_dom
  assume RR: "r1 \<le> r2" and A: "x1 \<le> x2" and B: "y1 \<le> y2"
  have ne: "Refine_Never \<noteq> Refine_Fixpoint" by simp
  show
    "le_pair (inv_minus_int_dom Refine_Never r1 x1 y1)
       (inv_minus_int_dom Refine_Never r2 x2 y2)"
    using inv_minus_int_dom_mono[OF ne RR A B] by (simp add: le_pair_def)
next
  fix r1 r2 x1 x2 y1 y2 :: int_dom
  assume RR: "r1 \<le> r2" and A: "x1 \<le> x2" and B: "y1 \<le> y2"
  have ne: "Refine_Never \<noteq> Refine_Fixpoint" by simp
  show
    "le_pair (inv_times_int_dom Refine_Never r1 x1 y1)
       (inv_times_int_dom Refine_Never r2 x2 y2)"
    using inv_times_int_dom_mono[OF ne RR A B] by (simp add: le_pair_def)
next
  fix a b :: int_dom
  show "intersect_int_dom_mode Refine_Never a b \<le> a"
    by (rule intersect_int_dom_mode_reductive1)
next
  fix a b :: int_dom
  show "intersect_int_dom_mode Refine_Never a b \<le> b"
    by (rule intersect_int_dom_mode_reductive2)
next
  fix res :: bool and a1 a2 :: int_dom
  show "le_pair (inv_less_int_dom Refine_Never res a1 a2) (a1, a2)"
    using inv_less_int_dom_reductive1 inv_less_int_dom_reductive2
    by (simp add: le_pair_def)
next
  fix res :: bool and a1 a2 :: int_dom
  show "le_pair (inv_eq_int_dom Refine_Never res a1 a2) (a1, a2)"
    using inv_eq_int_dom_reductive1 inv_eq_int_dom_reductive2
    by (simp add: le_pair_def)
next
  fix r a1 a2 :: int_dom
  show "le_pair (inv_plus_int_dom Refine_Never r a1 a2) (a1, a2)"
    using inv_plus_int_dom_reductive1 inv_plus_int_dom_reductive2
    by (simp add: le_pair_def)
next
  fix r a1 a2 :: int_dom
  show "le_pair (inv_minus_int_dom Refine_Never r a1 a2) (a1, a2)"
    using inv_minus_int_dom_reductive1 inv_minus_int_dom_reductive2
    by (simp add: le_pair_def)
next
  fix r a1 a2 :: int_dom
  show "le_pair (inv_times_int_dom Refine_Never r a1 a2) (a1, a2)"
    using inv_times_int_dom_reductive1 inv_times_int_dom_reductive2
    by (simp add: le_pair_def)
qed

abbreviation intersect_int_dom_once :: "int_dom => int_dom => int_dom" where
  "intersect_int_dom_once == intersect_int_dom_mode Refine_Once"

abbreviation aval_int_dom_once :: "exp => (vname => int_dom) => int_dom" where
  "aval_int_dom_once == aval_int_dom Refine_Once"

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
    backward_domain_refined
      intersect_int_dom_once aval_int_dom_once
      inv_less_int_dom_once inv_eq_int_dom_once
      inv_plus_int_dom_once inv_minus_int_dom_once inv_times_int_dom_once
  defines
    afilter_int_dom_once = int_dom_backward_once.afilter
    and bfilter_int_dom_once = int_dom_backward_once.bfilter
    and afilter_int_dom_once_st = int_dom_backward_once.afilter_st
    and bfilter_int_dom_once_st = int_dom_backward_once.bfilter_st
proof unfold_locales
  fix n :: int and a b :: int_dom
  assume "n \<in> gamma a" and "n \<in> gamma b"
  then show "n \<in> gamma (intersect_int_dom_mode Refine_Once a b)"
    using intersect_int_dom_mode_sound by simp
next
  fix s :: store and e :: exp and sigma :: "vname => int_dom"
  assume "\<forall>x. s x \<in> gamma (sigma x)"
  then show "aval e s \<in> gamma (aval_int_dom Refine_Once e sigma)"
    using aval_int_dom_sound by simp
next
  fix n1 n2 :: int and a1 a2 :: int_dom and res :: bool
  assume "n1 \<in> gamma a1" and "n2 \<in> gamma a2" and "(n1 < n2) = res"
  then show
    "n1 \<in> gamma (fst (inv_less_int_dom Refine_Once res a1 a2)) \<and>
     n2 \<in> gamma (snd (inv_less_int_dom Refine_Once res a1 a2))"
    using inv_less_int_dom_sound by simp
next
  fix n1 n2 :: int and a1 a2 :: int_dom and res :: bool
  assume "n1 \<in> gamma a1" and "n2 \<in> gamma a2" and "(n1 = n2) = res"
  then show
    "n1 \<in> gamma (fst (inv_eq_int_dom Refine_Once res a1 a2)) \<and>
     n2 \<in> gamma (snd (inv_eq_int_dom Refine_Once res a1 a2))"
    using inv_eq_int_dom_sound by simp
next
  fix n1 n2 :: int and a1 a2 r :: int_dom
  assume "n1 \<in> gamma a1" and "n2 \<in> gamma a2" and "n1 + n2 \<in> gamma r"
  then show
    "n1 \<in> gamma (fst (inv_plus_int_dom Refine_Once r a1 a2)) \<and>
     n2 \<in> gamma (snd (inv_plus_int_dom Refine_Once r a1 a2))"
    using inv_plus_int_dom_sound by simp
next
  fix n1 n2 :: int and a1 a2 r :: int_dom
  assume "n1 \<in> gamma a1" and "n2 \<in> gamma a2" and "n1 - n2 \<in> gamma r"
  then show
    "n1 \<in> gamma (fst (inv_minus_int_dom Refine_Once r a1 a2)) \<and>
     n2 \<in> gamma (snd (inv_minus_int_dom Refine_Once r a1 a2))"
    using inv_minus_int_dom_sound by simp
next
  fix n1 n2 :: int and a1 a2 r :: int_dom
  assume "n1 \<in> gamma a1" and "n2 \<in> gamma a2" and "n1 * n2 \<in> gamma r"
  then show
    "n1 \<in> gamma (fst (inv_times_int_dom Refine_Once r a1 a2)) \<and>
     n2 \<in> gamma (snd (inv_times_int_dom Refine_Once r a1 a2))"
    using inv_times_int_dom_sound by simp
next
  fix a1 a2 b1 b2 :: int_dom
  assume A: "a1 \<le> a2" and B: "b1 \<le> b2"
  have ne: "Refine_Once \<noteq> Refine_Fixpoint" by simp
  show
    "intersect_int_dom_mode Refine_Once a1 b1 \<le>
     intersect_int_dom_mode Refine_Once a2 b2"
    using intersect_int_dom_mode_mono[OF ne A B] .
next
  fix e :: exp and sigma1 sigma2 :: "vname => int_dom"
  assume S: "sigma1 \<le> sigma2"
  have ne: "Refine_Once \<noteq> Refine_Fixpoint" by simp
  show "aval_int_dom Refine_Once e sigma1 \<le> aval_int_dom Refine_Once e sigma2"
    using aval_int_dom_mono[OF ne S] .
next
  fix x1 x2 y1 y2 :: int_dom and res :: bool
  assume A: "x1 \<le> x2" and B: "y1 \<le> y2"
  have ne: "Refine_Once \<noteq> Refine_Fixpoint" by simp
  show
    "le_pair (inv_less_int_dom Refine_Once res x1 y1)
       (inv_less_int_dom Refine_Once res x2 y2)"
    using inv_less_int_dom_mono[OF ne A B] by (simp add: le_pair_def)
next
  fix x1 x2 y1 y2 :: int_dom and res :: bool
  assume A: "x1 \<le> x2" and B: "y1 \<le> y2"
  have ne: "Refine_Once \<noteq> Refine_Fixpoint" by simp
  show
    "le_pair (inv_eq_int_dom Refine_Once res x1 y1)
       (inv_eq_int_dom Refine_Once res x2 y2)"
    using inv_eq_int_dom_mono[OF ne A B] by (simp add: le_pair_def)
next
  fix r1 r2 x1 x2 y1 y2 :: int_dom
  assume RR: "r1 \<le> r2" and A: "x1 \<le> x2" and B: "y1 \<le> y2"
  have ne: "Refine_Once \<noteq> Refine_Fixpoint" by simp
  show
    "le_pair (inv_plus_int_dom Refine_Once r1 x1 y1)
       (inv_plus_int_dom Refine_Once r2 x2 y2)"
    using inv_plus_int_dom_mono[OF ne RR A B] by (simp add: le_pair_def)
next
  fix r1 r2 x1 x2 y1 y2 :: int_dom
  assume RR: "r1 \<le> r2" and A: "x1 \<le> x2" and B: "y1 \<le> y2"
  have ne: "Refine_Once \<noteq> Refine_Fixpoint" by simp
  show
    "le_pair (inv_minus_int_dom Refine_Once r1 x1 y1)
       (inv_minus_int_dom Refine_Once r2 x2 y2)"
    using inv_minus_int_dom_mono[OF ne RR A B] by (simp add: le_pair_def)
next
  fix r1 r2 x1 x2 y1 y2 :: int_dom
  assume RR: "r1 \<le> r2" and A: "x1 \<le> x2" and B: "y1 \<le> y2"
  have ne: "Refine_Once \<noteq> Refine_Fixpoint" by simp
  show
    "le_pair (inv_times_int_dom Refine_Once r1 x1 y1)
       (inv_times_int_dom Refine_Once r2 x2 y2)"
    using inv_times_int_dom_mono[OF ne RR A B] by (simp add: le_pair_def)
next
  fix a b :: int_dom
  show "intersect_int_dom_mode Refine_Once a b \<le> a"
    by (rule intersect_int_dom_mode_reductive1)
next
  fix a b :: int_dom
  show "intersect_int_dom_mode Refine_Once a b \<le> b"
    by (rule intersect_int_dom_mode_reductive2)
next
  fix res :: bool and a1 a2 :: int_dom
  show "le_pair (inv_less_int_dom Refine_Once res a1 a2) (a1, a2)"
    using inv_less_int_dom_reductive1 inv_less_int_dom_reductive2
    by (simp add: le_pair_def)
next
  fix res :: bool and a1 a2 :: int_dom
  show "le_pair (inv_eq_int_dom Refine_Once res a1 a2) (a1, a2)"
    using inv_eq_int_dom_reductive1 inv_eq_int_dom_reductive2
    by (simp add: le_pair_def)
next
  fix r a1 a2 :: int_dom
  show "le_pair (inv_plus_int_dom Refine_Once r a1 a2) (a1, a2)"
    using inv_plus_int_dom_reductive1 inv_plus_int_dom_reductive2
    by (simp add: le_pair_def)
next
  fix r a1 a2 :: int_dom
  show "le_pair (inv_minus_int_dom Refine_Once r a1 a2) (a1, a2)"
    using inv_minus_int_dom_reductive1 inv_minus_int_dom_reductive2
    by (simp add: le_pair_def)
next
  fix r a1 a2 :: int_dom
  show "le_pair (inv_times_int_dom Refine_Once r a1 a2) (a1, a2)"
    using inv_times_int_dom_reductive1 inv_times_int_dom_reductive2
    by (simp add: le_pair_def)
qed

abbreviation intersect_int_dom_fixpoint :: "int_dom => int_dom => int_dom" where
  "intersect_int_dom_fixpoint == intersect_int_dom_mode Refine_Fixpoint"

abbreviation aval_int_dom_fixpoint :: "exp => (vname => int_dom) => int_dom" where
  "aval_int_dom_fixpoint == aval_int_dom Refine_Fixpoint"

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
    backward_domain
      intersect_int_dom_fixpoint aval_int_dom_fixpoint
      inv_less_int_dom_fixpoint inv_eq_int_dom_fixpoint
      inv_plus_int_dom_fixpoint inv_minus_int_dom_fixpoint inv_times_int_dom_fixpoint
  defines
    afilter_int_dom_fixpoint = int_dom_backward_fixpoint.afilter
    and bfilter_int_dom_fixpoint = int_dom_backward_fixpoint.bfilter
    and afilter_int_dom_fixpoint_st = int_dom_backward_fixpoint.afilter_st
    and bfilter_int_dom_fixpoint_st = int_dom_backward_fixpoint.bfilter_st
proof unfold_locales
  fix n :: int and a b :: int_dom
  assume "n \<in> gamma a" and "n \<in> gamma b"
  then show "n \<in> gamma (intersect_int_dom_mode Refine_Fixpoint a b)"
    using intersect_int_dom_mode_sound by simp
next
  fix s :: store and e :: exp and sigma :: "vname => int_dom"
  assume "\<forall>x. s x \<in> gamma (sigma x)"
  then show "aval e s \<in> gamma (aval_int_dom Refine_Fixpoint e sigma)"
    using aval_int_dom_sound by simp
next
  fix n1 n2 :: int and a1 a2 :: int_dom and res :: bool
  assume "n1 \<in> gamma a1" and "n2 \<in> gamma a2" and "(n1 < n2) = res"
  then show
    "n1 \<in> gamma (fst (inv_less_int_dom Refine_Fixpoint res a1 a2)) \<and>
     n2 \<in> gamma (snd (inv_less_int_dom Refine_Fixpoint res a1 a2))"
    using inv_less_int_dom_sound by simp
next
  fix n1 n2 :: int and a1 a2 :: int_dom and res :: bool
  assume "n1 \<in> gamma a1" and "n2 \<in> gamma a2" and "(n1 = n2) = res"
  then show
    "n1 \<in> gamma (fst (inv_eq_int_dom Refine_Fixpoint res a1 a2)) \<and>
     n2 \<in> gamma (snd (inv_eq_int_dom Refine_Fixpoint res a1 a2))"
    using inv_eq_int_dom_sound by simp
next
  fix n1 n2 :: int and a1 a2 r :: int_dom
  assume "n1 \<in> gamma a1" and "n2 \<in> gamma a2" and "n1 + n2 \<in> gamma r"
  then show
    "n1 \<in> gamma (fst (inv_plus_int_dom Refine_Fixpoint r a1 a2)) \<and>
     n2 \<in> gamma (snd (inv_plus_int_dom Refine_Fixpoint r a1 a2))"
    using inv_plus_int_dom_sound by simp
next
  fix n1 n2 :: int and a1 a2 r :: int_dom
  assume "n1 \<in> gamma a1" and "n2 \<in> gamma a2" and "n1 - n2 \<in> gamma r"
  then show
    "n1 \<in> gamma (fst (inv_minus_int_dom Refine_Fixpoint r a1 a2)) \<and>
     n2 \<in> gamma (snd (inv_minus_int_dom Refine_Fixpoint r a1 a2))"
    using inv_minus_int_dom_sound by simp
next
  fix n1 n2 :: int and a1 a2 r :: int_dom
  assume "n1 \<in> gamma a1" and "n2 \<in> gamma a2" and "n1 * n2 \<in> gamma r"
  then show
    "n1 \<in> gamma (fst (inv_times_int_dom Refine_Fixpoint r a1 a2)) \<and>
     n2 \<in> gamma (snd (inv_times_int_dom Refine_Fixpoint r a1 a2))"
    using inv_times_int_dom_sound by simp
qed

end
