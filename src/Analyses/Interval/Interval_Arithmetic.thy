theory Interval_Arithmetic
  imports Interval_Lattice
begin

section \<open>Adding, subtracting and multiplying whole ranges\<close>

text \<open>
  Addition and subtraction of intervals move the two endpoints independently:
  the sum of \<open>[a, b]\<close> and \<open>[c, d]\<close> runs from \<open>a + c\<close> to \<open>b + d\<close>. Multiplication
  cannot, because a negative factor swaps which endpoint is larger, so
  \<open>ivl_times_core\<close> multiplies all four corner pairs and keeps their minimum and
  maximum. Every operation first \<open>normalize_ivl\<close>s its arguments --- an interval
  whose lower bound exceeds its upper one denotes no number at all and collapses
  to \<open>bot\<close> --- which is what keeps an unreachable operand from producing a
  spurious range.

  Each operation is proved sound (concrete values drawn from the operands land
  in the computed interval) and monotone (widening either operand widens the
  result). Those two facts are what \<open>Interval_Backward\<close> later needs to
  interpret the shared \<open>expression_domain_sound\<close> locale at Interval.
\<close>

instantiation ivl :: plus begin
fun plus_ivl :: "ivl => ivl => ivl" where
    "plus_ivl (Ivl l1 u1) (Ivl l2 u2) =
       (case (normalize_ivl (Ivl l1 u1), normalize_ivl (Ivl l2 u2)) of
          (Ivl a b, Ivl c d) \<Rightarrow> normalize_ivl (Ivl (a + c) (b + d)))"
instance ..
end

instantiation ivl :: minus begin
fun minus_ivl :: "ivl => ivl => ivl" where
    "minus_ivl (Ivl l1 u1) (Ivl l2 u2) =
       (case (normalize_ivl (Ivl l1 u1), normalize_ivl (Ivl l2 u2)) of
          (Ivl a b, Ivl c d) \<Rightarrow> normalize_ivl (Ivl (a - d) (b - c)))"
instance ..
end

text \<open>
  \<open>ivl_min\<close>/\<open>ivl_max\<close> abstract the two-argument \<open>Min\<close>/\<open>Max\<close> special calls:
  componentwise \<open>min\<close>/\<open>max\<close> of the bounds, exact whenever both operands are
  non-empty (\<open>min\<close>/\<open>max\<close> of two non-empty ranges is again non-empty, unlike
  multiplication's corner case), normalized like \<open>plus_ivl\<close>/\<open>minus_ivl\<close> so an
  empty operand still collapses to the canonical @{const bot}.
\<close>
fun ivl_min :: "ivl => ivl => ivl" where
    "ivl_min (Ivl l1 u1) (Ivl l2 u2) = normalize_ivl (Ivl (min l1 l2) (min u1 u2))"

fun ivl_max :: "ivl => ivl => ivl" where
    "ivl_max (Ivl l1 u1) (Ivl l2 u2) = normalize_ivl (Ivl (max l1 l2) (max u1 u2))"

lemma ivl_min_sound:
  assumes "i \<in> gamma_ivl a" "j \<in> gamma_ivl b"
  shows "min i j \<in> gamma_ivl (ivl_min a b)"
  using assms
  by (cases a; cases b)
     (auto simp: normalize_ivl_gamma Fin_min intro: eint_min_mono)

lemma ivl_max_sound:
  assumes "i \<in> gamma_ivl a" "j \<in> gamma_ivl b"
  shows "max i j \<in> gamma_ivl (ivl_max a b)"
  using assms
  by (cases a; cases b)
     (auto simp: normalize_ivl_gamma Fin_max intro: eint_max_mono)

lemma ivl_min_mono1: "a1 \<le> a2 \<Longrightarrow> ivl_min a1 b \<le> ivl_min a2 (b::ivl)"
proof -
  assume le: "a1 \<le> a2"
  obtain x1 x2 where a1: "a1 = Ivl x1 x2" by (rule ivl_exhaustE)
  obtain x1a x2a where a2: "a2 = Ivl x1a x2a" by (rule ivl_exhaustE)
  obtain x1b x2b where b: "b = Ivl x1b x2b" by (rule ivl_exhaustE)
  from le a1 a2 have h: "eint_le x1a x1" "eint_le x2 x2a"
    by (simp_all add: less_eq_ivl_def)
  have "Ivl (min x1 x1b) (min x2 x2b) \<le> Ivl (min x1a x1b) (min x2a x2b)"
    unfolding less_eq_ivl_def using h by (auto intro: eint_min_mono)
  then show ?thesis unfolding a1 a2 b ivl_min.simps by (rule normalize_ivl_mono)
qed

lemma ivl_min_mono2: "b1 \<le> b2 \<Longrightarrow> ivl_min a b1 \<le> ivl_min a (b2::ivl)"
proof -
  assume le: "b1 \<le> b2"
  obtain x1 x2 where a: "a = Ivl x1 x2" by (rule ivl_exhaustE)
  obtain x1a x2a where b1: "b1 = Ivl x1a x2a" by (rule ivl_exhaustE)
  obtain x1b x2b where b2: "b2 = Ivl x1b x2b" by (rule ivl_exhaustE)
  from le b1 b2 have h: "eint_le x1b x1a" "eint_le x2a x2b"
    by (simp_all add: less_eq_ivl_def)
  have "Ivl (min x1 x1a) (min x2 x2a) \<le> Ivl (min x1 x1b) (min x2 x2b)"
    unfolding less_eq_ivl_def using h by (auto intro: eint_min_mono)
  then show ?thesis unfolding a b1 b2 ivl_min.simps by (rule normalize_ivl_mono)
qed

lemma ivl_min_combine_mono:
  "\<lbrakk>a1 \<le> a2; b1 \<le> b2\<rbrakk> \<Longrightarrow> ivl_min a1 b1 \<le> ivl_min a2 (b2::ivl)"
  by (meson order.trans ivl_min_mono1 ivl_min_mono2)

lemma ivl_max_mono1: "a1 \<le> a2 \<Longrightarrow> ivl_max a1 b \<le> ivl_max a2 (b::ivl)"
proof -
  assume le: "a1 \<le> a2"
  obtain x1 x2 where a1: "a1 = Ivl x1 x2" by (rule ivl_exhaustE)
  obtain x1a x2a where a2: "a2 = Ivl x1a x2a" by (rule ivl_exhaustE)
  obtain x1b x2b where b: "b = Ivl x1b x2b" by (rule ivl_exhaustE)
  from le a1 a2 have h: "eint_le x1a x1" "eint_le x2 x2a"
    by (simp_all add: less_eq_ivl_def)
  have "Ivl (max x1 x1b) (max x2 x2b) \<le> Ivl (max x1a x1b) (max x2a x2b)"
    unfolding less_eq_ivl_def using h by (auto intro: eint_max_mono)
  then show ?thesis unfolding a1 a2 b ivl_max.simps by (rule normalize_ivl_mono)
qed

lemma ivl_max_mono2: "b1 \<le> b2 \<Longrightarrow> ivl_max a b1 \<le> ivl_max a (b2::ivl)"
proof -
  assume le: "b1 \<le> b2"
  obtain x1 x2 where a: "a = Ivl x1 x2" by (rule ivl_exhaustE)
  obtain x1a x2a where b1: "b1 = Ivl x1a x2a" by (rule ivl_exhaustE)
  obtain x1b x2b where b2: "b2 = Ivl x1b x2b" by (rule ivl_exhaustE)
  from le b1 b2 have h: "eint_le x1b x1a" "eint_le x2a x2b"
    by (simp_all add: less_eq_ivl_def)
  have "Ivl (max x1 x1a) (max x2 x2a) \<le> Ivl (max x1 x1b) (max x2 x2b)"
    unfolding less_eq_ivl_def using h by (auto intro: eint_max_mono)
  then show ?thesis unfolding a b1 b2 ivl_max.simps by (rule normalize_ivl_mono)
qed

lemma ivl_max_combine_mono:
  "\<lbrakk>a1 \<le> a2; b1 \<le> b2\<rbrakk> \<Longrightarrow> ivl_max a1 b1 \<le> ivl_max a2 (b2::ivl)"
  by (meson order.trans ivl_max_mono1 ivl_max_mono2)

lemma int_mult_in_corners_lo:
  fixes l1 u1 l2 u2 i j :: int
  assumes "l1 \<le> i" "i \<le> u1" "l2 \<le> j" "j \<le> u2"
  shows "min (l1*l2) (min (l1*u2) (min (u1*l2) (u1*u2))) \<le> i*j"
proof -
  consider (A) "0 \<le> i" "0 \<le> l2"
    | (B) "0 \<le> i" "l2 < 0"
    | (C) "i < 0" "0 \<le> u2"
    | (D) "i < 0" "u2 < 0"
    by linarith
  then show ?thesis
  proof cases
    case A
    have "l1*l2 \<le> i*l2"
      using assms(1) A(2)
      by (simp add: mult_right_mono)
    also have "\<dots> \<le> i*j"
      by (simp add: A(1) assms(3) mult_left_mono)
    finally show ?thesis by simp
  next
    case B
    have "u1*l2 \<le> i*l2"
      using assms(2) B(2) by simp
    also have "\<dots> \<le> i*j"
      using assms(3) B(1) by (rule mult_left_mono)
    finally show ?thesis by simp
  next
    case C
    have "l1*u2 \<le> i*u2"
      using assms(1) C(2) by (rule mult_right_mono)
    also have "\<dots> \<le> i*j"
      using assms(4) C(1) by simp
    finally show ?thesis by simp
  next
    case D
    have "u1*u2 \<le> i*u2"
      using assms(2) D(2) by simp
    also have "\<dots> \<le> i*j"
      using assms(4) D(1) by simp
    finally show ?thesis by simp
  qed
qed

lemma int_mult_in_corners_hi:
  fixes l1 u1 l2 u2 i j :: int
  assumes "l1 \<le> i" "i \<le> u1" "l2 \<le> j" "j \<le> u2"
  shows "i * j \<le> max (l1*l2) (max (l1*u2) (max (u1*l2) (u1*u2)))"
proof -
  have negated:
    "min ((-u1)*l2) (min ((-u1)*u2) (min ((-l1)*l2) ((-l1)*u2)))
       \<le> (-i)*j"
    by (rule int_mult_in_corners_lo) (use assms in simp_all)
  from negated show ?thesis
    by (simp add: min_def max_def; linarith)
qed

text \<open>
  Precise multiplication on non-empty intervals.  For all-finite operands the
  product range is the min / max over the four corner products (the box product
  attains its extrema at the corners); any infinite bound falls back to
  @{const ivl_top}.  An empty operand yields @{term bot} -- the proper bottom
  handling that keeps the operator monotone (mapping empties to @{const ivl_top}
  would destroy the ordering).
\<close>
fun ivl_times_core :: "ivl => ivl => ivl" where
    "ivl_times_core (Ivl (Fin l1) (Fin u1)) (Ivl (Fin l2) (Fin u2)) =
       Ivl (Fin (min (l1*l2) (min (l1*u2) (min (u1*l2) (u1*u2)))))
           (Fin (max (l1*l2) (max (l1*u2) (max (u1*l2) (u1*u2)))))"
  | "ivl_times_core _ _ = ivl_top"

instantiation ivl :: times begin
definition times_ivl :: "ivl => ivl => ivl" where
  "times_ivl a b = (if ivl_nonempty a \<and> ivl_nonempty b then ivl_times_core a b else bot)"
instance ..
end

text \<open>
  \<open>times_ivl_def\<close> is deliberately not \<open>[simp]\<close>: its conditional body would make
  \<open>simp\<close> split on \<open>ivl_nonempty\<close> before \<open>ivl_times_sound\<close> or \<open>ivl_times_mono\<close>
  can fire. A proof that must unfold \<open>*\<close> directly adds it explicitly.
\<close>

lemma ivl_plus_sound:
  assumes "i \<in> gamma_ivl a" "j \<in> gamma_ivl b"
  shows "i + j \<in> gamma_ivl (a + b)"
proof (cases a; cases b)
  fix l1 u1 l2 u2 :: eint
  assume "a = Ivl l1 u1" "b = Ivl l2 u2"
  with assms have bnds:
    "eint_le l1 (Fin i)" "eint_le (Fin i) u1"
    "eint_le l2 (Fin j)" "eint_le (Fin j) u2"
    by auto
  show "i + j \<in> gamma_ivl (a + b)"
    unfolding \<open>a = Ivl l1 u1\<close> \<open>b = Ivl l2 u2\<close>
    using bnds normalize_ivl_def
    by (cases l1; cases l2; cases u1; cases u2) auto
qed

lemma ivl_minus_sound:
  assumes "i \<in> gamma_ivl a" "j \<in> gamma_ivl b"
  shows "i - j \<in> gamma_ivl (a - b)"
proof (cases a; cases b)
  fix l1 u1 l2 u2 :: eint
  assume "a = Ivl l1 u1" "b = Ivl l2 u2"
  with assms have bnds:
    "eint_le l1 (Fin i)" "eint_le (Fin i) u1"
    "eint_le l2 (Fin j)" "eint_le (Fin j) u2"
    by auto
  show "i - j \<in> gamma_ivl (a - b)"
    unfolding \<open>a = Ivl l1 u1\<close> \<open>b = Ivl l2 u2\<close>
    using bnds normalize_ivl_def
    by (cases l1; cases l2; cases u1; cases u2) auto
qed

lemma ivl_times_sound:
  assumes "i \<in> gamma_ivl a" "j \<in> gamma_ivl b"
  shows "i * j \<in> gamma_ivl (a * b)"
proof -
  from assms have ne: "ivl_nonempty a" "ivl_nonempty b"
    by (auto intro: gamma_ivl_nonempty)
  hence eq: "a * b = ivl_times_core a b" by (simp add: times_ivl_def)
  show ?thesis
  proof (cases a; cases b)
    fix l1 u1 l2 u2 assume ab: "a = Ivl l1 u1" "b = Ivl l2 u2"
    show ?thesis
    proof (cases l1; cases u1; cases l2; cases u2)
      fix n1 m1 n2 m2 assume fin: "l1 = Fin n1" "u1 = Fin m1" "l2 = Fin n2" "u2 = Fin m2"
      from assms ab fin have bnds: "n1 \<le> i" "i \<le> m1" "n2 \<le> j" "j \<le> m2" by auto
      show ?thesis using eq ab fin
        int_mult_in_corners_lo[OF bnds] int_mult_in_corners_hi[OF bnds] by simp
    qed (use eq ab ne(1) ne(2) in \<open>simp_all add: ivl_top_def\<close>)
  qed
qed

text \<open>Both operators route their operands through \<^const>\<open>normalize_ivl\<close>; these rewrites
  expose that shape without the constructor-pattern gate, so monotonicity factors through
  \<^const>\<open>normalize_ivl\<close>'s monotonicity and the pointwise \<^typ>\<open>eint\<close> bounds.\<close>
lemma plus_ivl_norm:
  "a + b = (case (normalize_ivl a, normalize_ivl b) of
              (Ivl l1 u1, Ivl l2 u2) \<Rightarrow> normalize_ivl (Ivl (l1 + l2) (u1 + u2)))"
  by (cases a; cases b) simp

lemma minus_ivl_norm:
  "a - b = (case (normalize_ivl a, normalize_ivl b) of
              (Ivl l1 u1, Ivl l2 u2) \<Rightarrow> normalize_ivl (Ivl (l1 - u2) (u1 - l2)))"
  by (cases a; cases b) simp

lemma ivl_plus_mono:
  assumes "a1 \<le> a2" "b1 \<le> b2" shows "a1 + b1 \<le> a2 + (b2::ivl)"
proof -
  obtain pa qa where na1: "normalize_ivl a1 = Ivl pa qa" by (rule ivl_exhaustE)
  obtain ra sa where na2: "normalize_ivl a2 = Ivl ra sa" by (rule ivl_exhaustE)
  obtain pb qb where nb1: "normalize_ivl b1 = Ivl pb qb" by (rule ivl_exhaustE)
  obtain rb sb where nb2: "normalize_ivl b2 = Ivl rb sb" by (rule ivl_exhaustE)
  from normalize_ivl_mono[OF assms(1)] na1 na2 have A: "Ivl pa qa \<le> Ivl ra sa" by simp
  from normalize_ivl_mono[OF assms(2)] nb1 nb2 have B: "Ivl pb qb \<le> Ivl rb sb" by simp
  have "Ivl (pa + pb) (qa + qb) \<le> Ivl (ra + rb) (sa + sb)"
    using A B by (auto simp: less_eq_ivl_def eint_plus_mono)
  moreover have "a1 + b1 = normalize_ivl (Ivl (pa + pb) (qa + qb))"
    by (simp add: plus_ivl_norm na1 nb1)
  moreover have "a2 + b2 = normalize_ivl (Ivl (ra + rb) (sa + sb))"
    by (simp add: plus_ivl_norm na2 nb2)
  ultimately show ?thesis by (metis normalize_ivl_mono)
qed

lemma ivl_minus_mono:
  assumes "a1 \<le> a2" "b1 \<le> b2" shows "a1 - b1 \<le> a2 - (b2::ivl)"
proof -
  obtain pa qa where na1: "normalize_ivl a1 = Ivl pa qa" by (rule ivl_exhaustE)
  obtain ra sa where na2: "normalize_ivl a2 = Ivl ra sa" by (rule ivl_exhaustE)
  obtain pb qb where nb1: "normalize_ivl b1 = Ivl pb qb" by (rule ivl_exhaustE)
  obtain rb sb where nb2: "normalize_ivl b2 = Ivl rb sb" by (rule ivl_exhaustE)
  from normalize_ivl_mono[OF assms(1)] na1 na2 have A: "Ivl pa qa \<le> Ivl ra sa" by simp
  from normalize_ivl_mono[OF assms(2)] nb1 nb2 have B: "Ivl pb qb \<le> Ivl rb sb" by simp
  have "Ivl (pa - qb) (qa - pb) \<le> Ivl (ra - sb) (sa - rb)"
    using A B by (auto simp: less_eq_ivl_def eint_minus_mono)
  moreover have "a1 - b1 = normalize_ivl (Ivl (pa - qb) (qa - pb))"
    by (simp add: minus_ivl_norm na1 nb1)
  moreover have "a2 - b2 = normalize_ivl (Ivl (ra - sb) (sa - rb))"
    by (simp add: minus_ivl_norm na2 nb2)
  ultimately show ?thesis by (metis normalize_ivl_mono)
qed

text \<open>
  Monotonicity of the precise corner product.  Over a larger box the corner
  minimum can only drop and the corner maximum can only rise (each old corner is
  a point of the new box), so widening either operand widens the product.
\<close>

lemma corner_min_mono:
  fixes a1 b1 c1 d1 a2 b2 c2 d2 :: int
  assumes "a2 \<le> a1" "b1 \<le> b2" "c2 \<le> c1" "d1 \<le> d2" "a1 \<le> b1" "c1 \<le> d1"
  shows "min (a2*c2) (min (a2*d2) (min (b2*c2) (b2*d2)))
       \<le> min (a1*c1) (min (a1*d1) (min (b1*c1) (b1*d1)))"
proof -
  let ?M = "min (a2*c2) (min (a2*d2) (min (b2*c2) (b2*d2)))"
  have d1: "a1 \<le> b2" "c1 \<le> d2" "a2 \<le> b1" "c2 \<le> d1" using assms by auto
  have "?M \<le> a1*c1" by (rule int_mult_in_corners_lo[OF assms(1) d1(1) assms(3) d1(2)])
  moreover have "?M \<le> a1*d1" by (rule int_mult_in_corners_lo[OF assms(1) d1(1) d1(4) assms(4)])
  moreover have "?M \<le> b1*c1" by (rule int_mult_in_corners_lo[OF d1(3) assms(2) assms(3) d1(2)])
  moreover have "?M \<le> b1*d1" by (rule int_mult_in_corners_lo[OF d1(3) assms(2) d1(4) assms(4)])
  ultimately show ?thesis by simp
qed

lemma corner_max_mono:
  fixes a1 b1 c1 d1 a2 b2 c2 d2 :: int
  assumes "a2 \<le> a1" "b1 \<le> b2" "c2 \<le> c1" "d1 \<le> d2" "a1 \<le> b1" "c1 \<le> d1"
  shows "max (a1*c1) (max (a1*d1) (max (b1*c1) (b1*d1)))
       \<le> max (a2*c2) (max (a2*d2) (max (b2*c2) (b2*d2)))"
proof -
  let ?M = "max (a2*c2) (max (a2*d2) (max (b2*c2) (b2*d2)))"
  have d1: "a1 \<le> b2" "c1 \<le> d2" "a2 \<le> b1" "c2 \<le> d1" using assms by auto
  have "a1*c1 \<le> ?M" by (rule int_mult_in_corners_hi[OF assms(1) d1(1) assms(3) d1(2)])
  moreover have "a1*d1 \<le> ?M" by (rule int_mult_in_corners_hi[OF assms(1) d1(1) d1(4) assms(4)])
  moreover have "b1*c1 \<le> ?M" by (rule int_mult_in_corners_hi[OF d1(3) assms(2) assms(3) d1(2)])
  moreover have "b1*d1 \<le> ?M" by (rule int_mult_in_corners_hi[OF d1(3) assms(2) d1(4) assms(4)])
  ultimately show ?thesis by simp
qed

lemma ivl_times_core_top:
  "\<not> (\<exists>la ua lb ub. a = Ivl (Fin la) (Fin ua) \<and> b = Ivl (Fin lb) (Fin ub))
   \<Longrightarrow> ivl_times_core a b = ivl_top"
  by (cases "(a,b)" rule: ivl_times_core.cases) auto

lemma ivl_nonempty_le_fin:
  assumes "ivl_nonempty a" "a \<le> Ivl (Fin l2) (Fin u2)"
  shows "\<exists>l1 u1. a = Ivl (Fin l1) (Fin u1)"
proof (cases a)
  case (Ivl l u)
  with assms show ?thesis by (cases l; cases u; auto simp: less_eq_ivl_def)
qed

lemma ivl_times_core_mono:
  assumes ne: "ivl_nonempty a1" "ivl_nonempty b1"
      and le: "a1 \<le> a2" "b1 \<le> b2"
  shows "ivl_times_core a1 b1 \<le> ivl_times_core a2 b2"
proof (cases "\<exists>la ua lb ub. a2 = Ivl (Fin la) (Fin ua) \<and> b2 = Ivl (Fin lb) (Fin ub)")
  case False
  then have "ivl_times_core a2 b2 = ivl_top" by (rule ivl_times_core_top)
  thus ?thesis by (simp add: ivl_le_top)
next
  case True
  then obtain la2 ua2 lb2 ub2 where
    a2: "a2 = Ivl (Fin la2) (Fin ua2)" and b2: "b2 = Ivl (Fin lb2) (Fin ub2)" by blast
  from ivl_nonempty_le_fin[OF ne(1)] le(1) a2 obtain la1 ua1 where
    a1: "a1 = Ivl (Fin la1) (Fin ua1)" by metis
  from ivl_nonempty_le_fin[OF ne(2)] le(2) b2 obtain lb1 ub1 where
    b1: "b1 = Ivl (Fin lb1) (Fin ub1)" by metis
  from le a1 a2 b1 b2 have ord:
    "la2 \<le> la1" "ua1 \<le> ua2" "lb2 \<le> lb1" "ub1 \<le> ub2"
    by (auto simp: less_eq_ivl_def)
  from ne a1 b1 have nemp: "la1 \<le> ua1" "lb1 \<le> ub1" by auto
  show ?thesis
    unfolding a1 a2 b1 b2 ivl_times_core.simps less_eq_ivl_def
    using corner_min_mono[OF ord(1) ord(2) ord(3) ord(4) nemp(1) nemp(2)]
          corner_max_mono[OF ord(1) ord(2) ord(3) ord(4) nemp(1) nemp(2)]
    by simp
qed

lemma ivl_times_mono:
  assumes "a1 \<le> a2" "b1 \<le> b2"
  shows "a1 * b1 \<le> a2 * (b2::ivl)"
proof (cases "ivl_nonempty a1 \<and> ivl_nonempty b1")
  case False
  then have "a1 * b1 = bot" by (auto simp add: times_ivl_def)
  thus ?thesis by simp
next
  case True
  hence ne2: "ivl_nonempty a2" "ivl_nonempty b2"
    using assms ivl_nonempty_mono by blast+
  have "a1 * b1 = ivl_times_core a1 b1"
    using True by (simp add: times_ivl_def)
  moreover have "a2 * b2 = ivl_times_core a2 b2"
    using ne2 by (simp add: times_ivl_def)
  ultimately show ?thesis
    using ivl_times_core_mono[OF _ _ assms] True by simp
qed


subsection \<open>Truncating division\<close>

lemma c_mod_modulus_bound:
  assumes "b \<noteq> 0"
  shows "abs (c_mod a b) < abs b"
proof -
  have "0 \<le> abs a mod abs b" "abs a mod abs b < abs b"
    using assms by (auto intro: pos_mod_sign pos_mod_bound)
  then show ?thesis unfolding c_mod_abs
    by (auto simp: sgn_if abs_mult)
qed


lemma c_mod_dividend_bound:
  "abs (c_mod a b) \<le> abs a"
  unfolding c_mod_abs
  using zmod_le_nonneg_dividend[of "abs a" "abs b"]
  by (cases "b = 0") (auto simp: sgn_if abs_mult intro: pos_mod_sign)


lemma c_div_nonneg_divisor:
  assumes "0 < b"
  shows "c_div a b = (if a < 0 then - ((-a) div b) else a div b)"
  using assms by (auto simp: c_div_def sgn_if)


lemma c_div_mono_dividend:
  assumes "a1 \<le> a2" "0 < b"
  shows "c_div a1 b \<le> c_div a2 b"
proof (cases "a1 < 0 \<and> 0 \<le> a2")
  case True
  have "c_div a1 b \<le> 0" "0 \<le> c_div a2 b"
    using True assms c_div_nonpos(1) c_div_nonneg(1) by auto
  then show ?thesis by linarith
next
  case False
  show ?thesis unfolding c_div_nonneg_divisor[OF assms(2)]
    using False assms
    by (auto split: if_splits intro: zdiv_mono1)
qed


lemma c_div_antimono_divisor:
  assumes "0 \<le> a" "0 < b1" "b1 \<le> b2"
  shows "c_div a b2 \<le> c_div a b1"
  using assms
  by (simp add: c_div_nonneg_divisor zdiv_mono2)



lemma c_div_positive_divisor_bounds:
  assumes "0 < l" "l \<le> b" "b \<le> u"
  shows "min (c_div a l) (c_div a u) \<le> c_div a b \<and>
    c_div a b \<le> max (c_div a l) (c_div a u)"
proof (cases "0 \<le> a")
  case True
  have "c_div a u \<le> c_div a b" "c_div a b \<le> c_div a l"
    using assms True by (auto intro: c_div_antimono_divisor)
  then show ?thesis by auto
next
  case False
  have "c_div (-a) u \<le> c_div (-a) b" "c_div (-a) b \<le> c_div (-a) l"
    using assms False by (auto intro: c_div_antimono_divisor)
  then show ?thesis
    by (simp_all add: c_div_neg_dividend min_le_iff_disj le_max_iff_disj)
qed


lemma c_div_positive_corners:
  assumes "l \<le> i" "i \<le> u" "0 < c" "c \<le> j" "j \<le> d"
  shows "min (c_div l c) (c_div l d) \<le> c_div i j"
    and "c_div i j \<le> max (c_div u c) (c_div u d)"
proof -
  have "min (c_div l c) (c_div l d) \<le> c_div l j"
    using c_div_positive_divisor_bounds[OF assms(3-5), THEN conjunct1] .
  also have "c_div l j \<le> c_div i j"
    using assms by (auto intro: c_div_mono_dividend)
  finally show "min (c_div l c) (c_div l d) \<le> c_div i j" .
  have "c_div i j \<le> c_div u j"
    using assms by (auto intro: c_div_mono_dividend)
  also have "c_div u j \<le> max (c_div u c) (c_div u d)"
    using c_div_positive_divisor_bounds[OF assms(3-5), THEN conjunct2] .
  finally show "c_div i j \<le> max (c_div u c) (c_div u d)" .
qed


fun ivl_div_positive_core :: "ivl \<Rightarrow> ivl \<Rightarrow> ivl" where
  "ivl_div_positive_core (Ivl (Fin l) (Fin u)) (Ivl (Fin c) (Fin d)) =
    (if 0 < c then
      Ivl (Fin (min (c_div l c) (c_div l d))) (Fin (max (c_div u c) (c_div u d)))
     else ivl_top)"
| "ivl_div_positive_core a b = (if b = Ivl (Fin 1) (Fin 1) then a else ivl_top)"

definition ivl_div_positive :: "ivl \<Rightarrow> ivl \<Rightarrow> ivl" where
  "ivl_div_positive a b =
    (if ivl_nonempty a \<and> ivl_nonempty b
     then normalize_ivl (ivl_div_positive_core a b) else bot)"

lemma ivl_div_positive_core_sound:
  assumes "i \<in> gamma_ivl a" "j \<in> gamma_ivl b"
  shows "c_div i j \<in> gamma_ivl (ivl_div_positive_core a b)"
  using assms
  by (cases "(a, b)" rule: ivl_div_positive_core.cases)
     (auto simp: gamma_ivl_top intro: c_div_positive_corners)

lemma ivl_div_positive_sound:
  "i \<in> gamma_ivl a \<Longrightarrow> j \<in> gamma_ivl b \<Longrightarrow>
    c_div i j \<in> gamma_ivl (ivl_div_positive a b)"
  unfolding ivl_div_positive_def
  by (auto simp: normalize_ivl_gamma
      intro: ivl_div_positive_core_sound dest: gamma_ivl_nonempty)

lemma ivl_div_positive_core_one:
  "ivl_div_positive_core a (Ivl (Fin 1) (Fin 1)) = a"
  by (cases "(a, Ivl (Fin 1) (Fin 1))" rule: ivl_div_positive_core.cases) auto

lemma ivl_div_positive_core_top:
  "\<not> (\<exists>l u c d. a = Ivl (Fin l) (Fin u) \<and> b = Ivl (Fin c) (Fin d) \<and> 0 < c)
    \<Longrightarrow> b \<noteq> Ivl (Fin 1) (Fin 1) \<Longrightarrow> ivl_div_positive_core a b = ivl_top"
  by (cases "(a, b)" rule: ivl_div_positive_core.cases) auto

lemma ivl_div_positive_core_mono:
  assumes ne: "ivl_nonempty a1" "ivl_nonempty b1"
    and le: "a1 \<le> a2" "b1 \<le> b2"
  shows "ivl_div_positive_core a1 b1 \<le> ivl_div_positive_core a2 b2"
proof (cases "b2 = Ivl (Fin 1) (Fin 1)")
  case True
  have b1: "b1 = Ivl (Fin 1) (Fin 1)"
    using ivl_nonempty_le_fin[OF ne(2) le(2)[unfolded True]] le(2) ne(2)
    by (auto simp: True less_eq_ivl_def)
  show ?thesis using le(1) by (simp add: True b1 ivl_div_positive_core_one)
next
  case not_one: False
  show ?thesis
  proof (cases "\<exists>l u c d. a2 = Ivl (Fin l) (Fin u) \<and> b2 = Ivl (Fin c) (Fin d) \<and> 0 < c")
    case False
    then show ?thesis using not_one by (simp add: ivl_div_positive_core_top ivl_le_top)
  next
    case True
    then obtain l2 u2 c2 d2 where
      a2: "a2 = Ivl (Fin l2) (Fin u2)" and b2: "b2 = Ivl (Fin c2) (Fin d2)"
      and pos: "0 < c2" by blast
    obtain l1 u1 where a1: "a1 = Ivl (Fin l1) (Fin u1)"
      using ivl_nonempty_le_fin[OF ne(1) le(1)[unfolded a2]] by blast
    obtain c1 d1 where b1: "b1 = Ivl (Fin c1) (Fin d1)"
      using ivl_nonempty_le_fin[OF ne(2) le(2)[unfolded b2]] by blast
    have bounds: "l2 \<le> l1" "u1 \<le> u2" "c2 \<le> c1" "d1 \<le> d2" "l1 \<le> u1" "c1 \<le> d1"
      using le ne unfolding a1 a2 b1 b2 by (auto simp: less_eq_ivl_def)
    have lo:
      "min (c_div l2 c2) (c_div l2 d2) \<le> c_div l1 c1"
      "min (c_div l2 c2) (c_div l2 d2) \<le> c_div l1 d1"
      using bounds pos by (auto intro: c_div_positive_corners(1))
    have hi:
      "c_div u1 c1 \<le> max (c_div u2 c2) (c_div u2 d2)"
      "c_div u1 d1 \<le> max (c_div u2 c2) (c_div u2 d2)"
      using bounds pos by (auto intro: c_div_positive_corners(2))
    show ?thesis unfolding a1 a2 b1 b2
      using lo hi pos bounds by (simp add: less_eq_ivl_def)
  qed
qed


lemma ivl_div_positive_mono:
  assumes "a1 \<le> a2" "b1 \<le> b2"
  shows "ivl_div_positive a1 b1 \<le> ivl_div_positive a2 b2"
  using assms
  unfolding ivl_div_positive_def
  by (auto intro: normalize_ivl_mono ivl_div_positive_core_mono
      dest: ivl_nonempty_mono)

definition ivl_positive_part :: "ivl \<Rightarrow> ivl" where
  "ivl_positive_part a = intersect_ivl a (Ivl (Fin 1) PlusInf)"

definition ivl_zero_part :: "ivl \<Rightarrow> ivl" where
  "ivl_zero_part a = intersect_ivl a (Ivl (Fin 0) (Fin 0))"

definition ivl_div :: "ivl \<Rightarrow> ivl \<Rightarrow> ivl" where
  "ivl_div a b =
    (if ivl_nonempty a \<and> ivl_nonempty b then
      ivl_div_positive a (ivl_positive_part b) \<squnion>
      ivl_div_positive (Ivl (Fin 0) (Fin 0) - a)
        (ivl_positive_part (Ivl (Fin 0) (Fin 0) - b)) \<squnion> ivl_zero_part b
     else bot)"


lemma ivl_div_join_left:
  "x \<in> gamma_ivl a \<Longrightarrow> x \<in> gamma_ivl (a \<squnion> b)"
  using gamma_ivl_mono[OF le_supI1] by blast

lemma ivl_div_join_right:
  "x \<in> gamma_ivl b \<Longrightarrow> x \<in> gamma_ivl (a \<squnion> b)"
  using gamma_ivl_mono[OF le_supI2] by blast

lemma ivl_div_sound:
  assumes "i \<in> gamma_ivl a" "j \<in> gamma_ivl b"
  shows "c_div i j \<in> gamma_ivl (ivl_div a b)"
proof -
  have ne: "ivl_nonempty a" "ivl_nonempty b"
    using assms by (auto dest: gamma_ivl_nonempty)
  show ?thesis
  proof (cases "j = 0")
    case True
    then have "c_div i j \<in> gamma_ivl (ivl_zero_part b)"
      unfolding ivl_zero_part_def using assms True
      by (intro intersect_ivl_gamma) auto
    then show ?thesis unfolding ivl_div_def using ne
      by (auto intro: ivl_div_join_right)
  next
    case nz: False
    show ?thesis
    proof (cases "0 < j")
      case True
      have "j \<in> gamma_ivl (ivl_positive_part b)"
        unfolding ivl_positive_part_def using assms True
        by (intro intersect_ivl_gamma) auto
      then have "c_div i j \<in> gamma_ivl (ivl_div_positive a (ivl_positive_part b))"
        using assms(1) by (auto intro: ivl_div_positive_sound)
      then show ?thesis unfolding ivl_div_def using ne
        by (auto intro: ivl_div_join_left)
    next
      case False
      have ni: "-i \<in> gamma_ivl (Ivl (Fin 0) (Fin 0) - a)"
        using ivl_minus_sound[of 0 _ i a] assms(1) by simp
      have nj: "-j \<in> gamma_ivl (ivl_positive_part (Ivl (Fin 0) (Fin 0) - b))"
        unfolding ivl_positive_part_def
        apply (rule intersect_ivl_gamma)
         apply (use ivl_minus_sound[of 0 "Ivl (Fin 0) (Fin 0)" j b] assms(2) in simp)
        using False nz by auto
      have "c_div i j \<in> gamma_ivl
        (ivl_div_positive (Ivl (Fin 0) (Fin 0) - a)
          (ivl_positive_part (Ivl (Fin 0) (Fin 0) - b)))"
        using ivl_div_positive_sound[OF ni nj]
        by (simp add: c_div_neg_dividend c_div_neg_divisor)
      then show ?thesis unfolding ivl_div_def using ne
        by (auto intro: ivl_div_join_left
            ivl_div_join_right)
    qed
  qed
qed

lemma ivl_div_mono:
  assumes "a1 \<le> a2" "b1 \<le> b2"
  shows "ivl_div a1 b1 \<le> ivl_div a2 b2"
proof -
  have pos: "ivl_positive_part b1 \<le> ivl_positive_part b2"
    unfolding ivl_positive_part_def
    by (intro intersect_ivl_mono assms order_refl)
  have neg_a: "Ivl (Fin 0) (Fin 0) - a1 \<le> Ivl (Fin 0) (Fin 0) - a2"
    by (intro ivl_minus_mono assms order_refl)
  have neg_b: "ivl_positive_part (Ivl (Fin 0) (Fin 0) - b1) \<le>
    ivl_positive_part (Ivl (Fin 0) (Fin 0) - b2)"
    unfolding ivl_positive_part_def
    by (intro intersect_ivl_mono ivl_minus_mono assms order_refl)
  have zero: "ivl_zero_part b1 \<le> ivl_zero_part b2"
    unfolding ivl_zero_part_def
    by (intro intersect_ivl_mono assms order_refl)
  have joined:
    "ivl_div_positive a1 (ivl_positive_part b1) \<squnion>
      ivl_div_positive (Ivl (Fin 0) (Fin 0) - a1)
        (ivl_positive_part (Ivl (Fin 0) (Fin 0) - b1)) \<squnion> ivl_zero_part b1 \<le>
     ivl_div_positive a2 (ivl_positive_part b2) \<squnion>
      ivl_div_positive (Ivl (Fin 0) (Fin 0) - a2)
        (ivl_positive_part (Ivl (Fin 0) (Fin 0) - b2)) \<squnion> ivl_zero_part b2"
    by (intro sup_mono ivl_div_positive_mono assms pos neg_a neg_b zero)
  show ?thesis unfolding ivl_div_def
    using joined ivl_nonempty_mono assms by auto
qed


subsection \<open>Remainder bounds\<close>

fun ivl_mod_bound :: "ivl \<Rightarrow> ivl" where
  "ivl_mod_bound (Ivl (Fin l) (Fin u)) =
    (if 0 < l \<or> u < 0 then
      Ivl (Fin (1 - max (abs l) (abs u))) (Fin (max (abs l) (abs u) - 1))
     else ivl_top)"
| "ivl_mod_bound _ = ivl_top"

lemma abs_between_bounds:
  fixes l i u :: int
  assumes "l \<le> i" "i \<le> u"
  shows "abs i \<le> max (abs l) (abs u)"
  using assms by (auto simp: abs_if)

lemma ivl_mod_bound_sound:
  assumes "j \<in> gamma_ivl b"
  shows "c_mod i j \<in> gamma_ivl (ivl_mod_bound b)"
proof (cases b rule: ivl_mod_bound.cases)
  case (1 l u)
  with assms have bounds: "l \<le> j" "j \<le> u" by simp_all
  have magnitude: "abs j \<le> max (abs l) (abs u)"
    by (rule abs_between_bounds[OF bounds])
  show ?thesis unfolding 1 ivl_mod_bound.simps
    using bounds magnitude c_mod_modulus_bound[of j i]
    by (auto simp: gamma_ivl_top; linarith)
qed (simp_all add: gamma_ivl_top)

lemma ivl_mod_bound_mono:
  assumes "ivl_nonempty b1" "b1 \<le> b2"
  shows "ivl_mod_bound b1 \<le> ivl_mod_bound b2"
proof (cases b2 rule: ivl_mod_bound.cases)
  case (1 l2 u2)
  obtain l1 u1 where b1: "b1 = Ivl (Fin l1) (Fin u1)"
    using ivl_nonempty_le_fin[OF assms(1) assms(2)[unfolded 1]] by blast
  have bounds: "l2 \<le> l1" "u1 \<le> u2" "l1 \<le> u1"
    using assms unfolding 1 b1 by (auto simp: less_eq_ivl_def)
  have "max (abs l1) (abs u1) \<le> max (abs l2) (abs u2)"
    using abs_between_bounds[of l2 l1 u2] abs_between_bounds[of l2 u1 u2] bounds by auto
  then show ?thesis unfolding 1 b1 ivl_mod_bound.simps
    using bounds by (auto simp: less_eq_ivl_def ivl_top_def)
qed (simp_all add: ivl_le_top)

lemma ivl_mod_dividend_sound:
  assumes "i \<in> gamma_ivl a"
  shows "c_mod i j \<in> gamma_ivl (a \<squnion> Ivl (Fin 0) (Fin 0))"
proof -
  have range: "min 0 i \<le> c_mod i j \<and> c_mod i j \<le> max 0 i"
    using c_mod_dividend_bound[of i j] c_mod_nonneg[of i j] c_mod_nonpos[of i j]
    by (auto simp: abs_if min_def max_def split: if_splits; linarith)
  obtain l u where a: "a = Ivl l u" by (cases a)
  show ?thesis using assms range
    unfolding a sup_ivl_def
    by (cases l; cases u; auto simp: min_def max_def split: if_splits)
qed

definition ivl_mod :: "ivl \<Rightarrow> ivl \<Rightarrow> ivl" where
  "ivl_mod a b =
    (if ivl_nonempty a \<and> ivl_nonempty b then
      intersect_ivl (a - ivl_div a b * b)
        (intersect_ivl (a \<squnion> Ivl (Fin 0) (Fin 0)) (ivl_mod_bound b))
     else bot)"

lemma ivl_mod_sound:
  assumes "i \<in> gamma_ivl a" "j \<in> gamma_ivl b"
  shows "c_mod i j \<in> gamma_ivl (ivl_mod a b)"
proof -
  have ne: "ivl_nonempty a" "ivl_nonempty b"
    using assms by (auto dest: gamma_ivl_nonempty)
  have residual: "i - c_div i j * j \<in> gamma_ivl (a - ivl_div a b * b)"
    by (intro ivl_minus_sound ivl_times_sound ivl_div_sound assms)
  have "c_mod i j \<in> gamma_ivl (a - ivl_div a b * b)"
    using residual by (cases "j = 0") (simp_all add: c_mod_def)
  then show ?thesis unfolding ivl_mod_def
    using assms(1,2) intersect_ivl_gamma ivl_mod_bound_sound ivl_mod_dividend_sound ne(1,2)
    by presburger
qed

lemma ivl_mod_mono:
  assumes "a1 \<le> a2" "b1 \<le> b2"
  shows "ivl_mod a1 b1 \<le> ivl_mod a2 b2"
proof (cases "ivl_nonempty a1 \<and> ivl_nonempty b1")
  case False
  then show ?thesis unfolding ivl_mod_def by (simp only: False if_False bot_least)
next
  case True
  have ne: "ivl_nonempty a2" "ivl_nonempty b2"
    using True assms ivl_nonempty_mono by blast+
  show ?thesis unfolding ivl_mod_def
    apply (simp only: True ne simp_thms if_True)
    by (intro intersect_ivl_mono ivl_minus_mono ivl_times_mono ivl_div_mono
        sup_mono ivl_mod_bound_mono assms order_refl) (use True in auto)
qed

subsection \<open>Results are canonical\<close>

text \<open>
  Every public interval operation returns a canonical representative: a non-empty
  interval, or \<^const>\<open>bot\<close> itself.  No operation manufactures a fresh inverted
  bound pair such as \<^term>\<open>Ivl (Fin 2) (Fin 1)\<close>, so structural equality on
  results distinguishes exactly the abstract values they denote.
\<close>

lemma normalize_ivl_plus [simp]: "normalize_ivl (a + b) = a + b"
  by (simp add: plus_ivl_norm split: ivl.splits prod.splits)

lemma normalize_ivl_minus [simp]: "normalize_ivl (a - b) = a - b"
  by (simp add: minus_ivl_norm split: ivl.splits prod.splits)

lemma normalize_ivl_ivl_min [simp]: "normalize_ivl (ivl_min a b) = ivl_min a b"
  by (cases a; cases b) simp

lemma normalize_ivl_ivl_max [simp]: "normalize_ivl (ivl_max a b) = ivl_max a b"
  by (cases a; cases b) simp

lemma is_bottom_ivl_times_core [simp]:
  "\<not> is_bottom_ivl (ivl_times_core x y)"
proof (induction x y rule: ivl_times_core.induct)
  case (1 l1 u1 l2 u2)
  show ?case
    by (auto simp: is_bottom_ivl_def min_le_iff_disj le_max_iff_disj)
qed (simp_all add: is_bottom_ivl_def ivl_top_def)

lemma normalize_ivl_times [simp]: "normalize_ivl (a * b) = a * b"
  by (cases "ivl_nonempty a \<and> ivl_nonempty b") (auto simp: times_ivl_def)

end
