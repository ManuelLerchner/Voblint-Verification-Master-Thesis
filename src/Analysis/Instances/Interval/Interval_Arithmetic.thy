theory Interval_Arithmetic
  imports Interval_Lattice
begin

section \<open>Interval arithmetic\<close>

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
  shows "min (l1*l2) (min (l1*u2) (min (u1*l2) (u1*u2))) \<le> i * j"
  using assms
  by (smt (verit) mult_left_mono mult_right_mono mult_left_mono_neg mult_right_mono_neg min_def)

lemma int_mult_in_corners_hi:
  fixes l1 u1 l2 u2 i j :: int
  assumes "l1 \<le> i" "i \<le> u1" "l2 \<le> j" "j \<le> u2"
  shows "i * j \<le> max (l1*l2) (max (l1*u2) (max (u1*l2) (u1*u2)))"
  using assms
  by (smt (verit) mult_left_mono mult_right_mono mult_left_mono_neg mult_right_mono_neg max_def)

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

(* times_ivl_def is NOT declared [simp]: the conditional body would
   cause simp to split on ivl_nonempty before ivl_times_sound / ivl_times_mono
   can fire. Add it explicitly in proofs that must unfold * directly. *)

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

end
