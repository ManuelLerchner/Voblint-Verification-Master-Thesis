theory Congruence_Arithmetic
  imports Congruence_Lattice "Voblint_VIMP.VIMP_Expr"
    "Voblint_Nonrelational.Abstract_Arithmetic"
begin

section \<open>Congruence arithmetic\<close>

text \<open>
  Arithmetic follows the unbounded-integer fragment of Goblint's congruence
  domain. Every public result passes through the normalized carrier. Goblint
  raises when exactly one operand is bottom; the total HOL operations instead
  return bottom because no concrete arithmetic result exists for an empty
  operand.
\<close>

fun plus_congruence_rep ::
    "congruence_rep => congruence_rep => congruence_rep"
where
  "plus_congruence_rep None _ = None"
| "plus_congruence_rep _ None = None"
| "plus_congruence_rep (Some (c1, m1)) (Some (c2, m2)) =
     normalize_congruence_rep (Some (c1 + c2, gcd m1 m2))"

fun minus_congruence_rep ::
    "congruence_rep => congruence_rep => congruence_rep"
where
  "minus_congruence_rep None _ = None"
| "minus_congruence_rep _ None = None"
| "minus_congruence_rep (Some (c1, m1)) (Some (c2, m2)) =
     normalize_congruence_rep (Some (c1 - c2, gcd m1 m2))"

text \<open>
  Multiplication expands two classes into a constant plus three variable
  terms. The gcd of their coefficients contains every concrete product while
  retaining all congruence information justified by that expansion. The
  resulting class is a sound over-approximation; no exactness claim is needed.
\<close>

fun times_congruence_rep ::
    "congruence_rep => congruence_rep => congruence_rep"
where
  "times_congruence_rep None _ = None"
| "times_congruence_rep _ None = None"
| "times_congruence_rep (Some (c1, m1)) (Some (c2, m2)) =
     normalize_congruence_rep
       (Some
         (c1 * c2,
          gcd (c1 * m2)
            (gcd (m1 * c2) (m1 * m2))))"

lemma normalized_plus_congruence_rep [simp]:
  "normalized_congruence_rep (plus_congruence_rep a b)"
  by (cases a; cases b;
      auto simp only: plus_congruence_rep.simps
        normalized_congruence_rep.simps
        normalized_normalize_congruence_rep
        split: prod.splits)

lemma normalized_minus_congruence_rep [simp]:
  "normalized_congruence_rep (minus_congruence_rep a b)"
  by (cases a; cases b;
      auto simp only: minus_congruence_rep.simps
        normalized_congruence_rep.simps
        normalized_normalize_congruence_rep
        split: prod.splits)

lemma normalized_times_congruence_rep [simp]:
  "normalized_congruence_rep (times_congruence_rep a b)"
  by (cases a; cases b;
      auto simp only: times_congruence_rep.simps
        normalized_congruence_rep.simps
        normalized_normalize_congruence_rep
        split: prod.splits)

instantiation congruence :: plus
begin

lift_definition plus_congruence ::
    "congruence => congruence => congruence"
  is plus_congruence_rep
  by simp

instance ..

end

instantiation congruence :: minus
begin

lift_definition minus_congruence ::
    "congruence => congruence => congruence"
  is minus_congruence_rep
  by simp

instance ..

end

instantiation congruence :: times
begin

lift_definition times_congruence ::
    "congruence => congruence => congruence"
  is times_congruence_rep
  by simp

instance ..

end

definition congruence_of_int :: "int => congruence" where
  "congruence_of_int n = mk_congruence n 0"

lemma congruence_of_int_gamma [simp]:
  "n \<in> gamma_congruence (congruence_of_int n)"
  unfolding congruence_of_int_def by simp

subsection \<open>Semantic soundness\<close>

text \<open>
  Each operation's soundness reduces to one divisibility fact about the two
  operand classes; \<open>congruence_binop_sound\<close> discharges the bottom operands
  and the representation plumbing once.
\<close>

lemma congruence_binop_sound:
  assumes "i \<in> gamma_congruence a" and "j \<in> gamma_congruence b"
    and "\<And>c1 m1 c2 m2. Rep_congruence a = Some (c1, m1) \<Longrightarrow>
           Rep_congruence b = Some (c2, m2) \<Longrightarrow> m1 dvd i - c1 \<Longrightarrow> m2 dvd j - c2 \<Longrightarrow>
           k \<in> gamma_congruence r"
  shows "k \<in> gamma_congruence r"
  using assms unfolding gamma_congruence_def
  by (cases rule: congruence_rep_cases[of a]; cases rule: congruence_rep_cases[of b]) auto

lemma congruence_plus_sound:
  assumes "i \<in> gamma_congruence a" and "j \<in> gamma_congruence b"
  shows "i + j \<in> gamma_congruence (a + b)"
  using assms
proof (rule congruence_binop_sound)
  fix c1 m1 c2 m2
  assume a: "Rep_congruence a = Some (c1, m1)" and b: "Rep_congruence b = Some (c2, m2)"
    and mi: "m1 dvd i - c1" and mj: "m2 dvd j - c2"
  have "gcd m1 m2 dvd (i - c1) + (j - c2)"
    by (rule dvd_add[OF dvd_trans[OF gcd_dvd1 mi] dvd_trans[OF gcd_dvd2 mj]])
  then have "gcd m1 m2 dvd (i + j) - (c1 + c2)" by (simp add: algebra_simps)
  then show "i + j \<in> gamma_congruence (a + b)"
    unfolding gamma_congruence_def plus_congruence.rep_eq a b
    by (simp only: plus_congruence_rep.simps gamma_normalize_congruence_rep
        gamma_congruence_rep.simps mem_Collect_eq)
qed

lemma congruence_minus_sound:
  assumes "i \<in> gamma_congruence a" and "j \<in> gamma_congruence b"
  shows "i - j \<in> gamma_congruence (a - b)"
  using assms
proof (rule congruence_binop_sound)
  fix c1 m1 c2 m2
  assume a: "Rep_congruence a = Some (c1, m1)" and b: "Rep_congruence b = Some (c2, m2)"
    and mi: "m1 dvd i - c1" and mj: "m2 dvd j - c2"
  have "gcd m1 m2 dvd (i - c1) - (j - c2)"
    by (rule dvd_diff[OF dvd_trans[OF gcd_dvd1 mi] dvd_trans[OF gcd_dvd2 mj]])
  then have "gcd m1 m2 dvd (i - j) - (c1 - c2)" by (simp add: algebra_simps)
  then show "i - j \<in> gamma_congruence (a - b)"
    unfolding gamma_congruence_def minus_congruence.rep_eq a b
    by (simp only: minus_congruence_rep.simps gamma_normalize_congruence_rep
        gamma_congruence_rep.simps mem_Collect_eq)
qed

lemma congruence_product_divisible:
  fixes c1 c2 m1 m2 i j :: int
  assumes mi: "m1 dvd i - c1"
      and mj: "m2 dvd j - c2"
  shows
    "gcd (c1 * m2) (gcd (m1 * c2) (m1 * m2))
       dvd i * j - c1 * c2"
proof -
  obtain ki where ki: "i - c1 = m1 * ki"
    using mi unfolding dvd_def by blast
  obtain kj where kj: "j - c2 = m2 * kj"
    using mj unfolding dvd_def by blast
  let ?g =
    "gcd (c1 * m2) (gcd (m1 * c2) (m1 * m2))"
  have d1: "?g dvd c1 * m2"
    by (rule gcd_dvd1)
  have outer:
    "?g dvd gcd (m1 * c2) (m1 * m2)"
    by (rule gcd_dvd2)
  have d2: "?g dvd m1 * c2"
    by (rule dvd_trans[OF outer gcd_dvd1])
  have d3: "?g dvd m1 * m2"
    by (rule dvd_trans[OF outer gcd_dvd2])
  have t1: "?g dvd c1 * (j - c2)"
    using dvd_mult2[OF d1, of kj] unfolding kj by (simp add: algebra_simps)
  have t2: "?g dvd c2 * (i - c1)"
    using dvd_mult2[OF d2, of ki] unfolding ki by (simp add: algebra_simps)
  have t3: "?g dvd (i - c1) * (j - c2)"
    using dvd_mult2[OF d3, of "ki * kj"]
    unfolding ki kj by (simp add: algebra_simps)
  have combined:
    "?g dvd c1 * (j - c2) + c2 * (i - c1) +
      (i - c1) * (j - c2)"
    by (rule dvd_add[OF dvd_add[OF t1 t2] t3])
  have product:
    "c1 * (j - c2) + c2 * (i - c1) +
       (i - c1) * (j - c2) =
     i * j - c1 * c2"
    by (simp add: algebra_simps)
  show ?thesis using combined unfolding product .
qed

lemma congruence_times_sound:
  assumes "i \<in> gamma_congruence a" and "j \<in> gamma_congruence b"
  shows "i * j \<in> gamma_congruence (a * b)"
  using assms
proof (rule congruence_binop_sound)
  fix c1 m1 c2 m2
  assume a: "Rep_congruence a = Some (c1, m1)" and b: "Rep_congruence b = Some (c2, m2)"
    and mi: "m1 dvd i - c1" and mj: "m2 dvd j - c2"
  from congruence_product_divisible[OF mi mj]
  show "i * j \<in> gamma_congruence (a * b)"
    unfolding gamma_congruence_def times_congruence.rep_eq a b
    by (simp only: times_congruence_rep.simps gamma_normalize_congruence_rep
        gamma_congruence_rep.simps mem_Collect_eq)
qed

subsection \<open>Monotonicity\<close>

lemma plus_congruence_rep_mono_nonbottom:
  fixes c1 m1 c2 m2 d1 n1 d2 n2 :: int
  assumes m: "m2 dvd m1" "m2 dvd c1 - c2"
      and n: "n2 dvd n1" "n2 dvd d1 - d2"
  shows
    "congruence_le_rep
       (plus_congruence_rep (Some (c1, m1)) (Some (d1, n1)))
       (plus_congruence_rep (Some (c2, m2)) (Some (d2, n2)))"
  unfolding congruence_le_rep_iff
  by (simp only: plus_congruence_rep.simps gamma_normalize_congruence_rep
        gamma_congruence_rep.simps congruence_class_subset_iff)
     (use gcd_mono[OF m(1) n(1)]
        dvd_add[OF dvd_trans[OF gcd_dvd1 m(2)] dvd_trans[OF gcd_dvd2 n(2)]]
      in \<open>simp add: algebra_simps\<close>)

lemma plus_congruence_rep_mono:
  assumes "congruence_le_rep a1 a2"
      and "congruence_le_rep b1 b2"
  shows
    "congruence_le_rep
       (plus_congruence_rep a1 b1)
       (plus_congruence_rep a2 b2)"
  using assms
  by (cases a1; cases a2; cases b1; cases b2;
      auto split: prod.splits
        intro: plus_congruence_rep_mono_nonbottom)

lemma congruence_plus_mono:
  assumes "a1 <= a2" and "b1 <= b2"
  shows "a1 + b1 <= a2 + (b2 :: congruence)"
  unfolding less_eq_congruence_def congruence_le_def
  apply (simp only: plus_congruence.rep_eq)
  by (rule plus_congruence_rep_mono)
     (use assms in
       \<open>simp_all add: less_eq_congruence_def congruence_le_def\<close>)

lemma minus_congruence_rep_mono_nonbottom:
  fixes c1 m1 c2 m2 d1 n1 d2 n2 :: int
  assumes m: "m2 dvd m1" "m2 dvd c1 - c2"
      and n: "n2 dvd n1" "n2 dvd d1 - d2"
  shows
    "congruence_le_rep
       (minus_congruence_rep (Some (c1, m1)) (Some (d1, n1)))
       (minus_congruence_rep (Some (c2, m2)) (Some (d2, n2)))"
  unfolding congruence_le_rep_iff
  by (simp only: minus_congruence_rep.simps gamma_normalize_congruence_rep
        gamma_congruence_rep.simps congruence_class_subset_iff)
     (use gcd_mono[OF m(1) n(1)]
        dvd_diff[OF dvd_trans[OF gcd_dvd1 m(2)] dvd_trans[OF gcd_dvd2 n(2)]]
      in \<open>simp add: algebra_simps\<close>)

lemma minus_congruence_rep_mono:
  assumes "congruence_le_rep a1 a2"
      and "congruence_le_rep b1 b2"
  shows
    "congruence_le_rep
       (minus_congruence_rep a1 b1)
       (minus_congruence_rep a2 b2)"
  using assms
  by (cases a1; cases a2; cases b1; cases b2;
      auto split: prod.splits
        intro: minus_congruence_rep_mono_nonbottom)

lemma congruence_minus_mono:
  assumes "a1 <= a2" and "b1 <= b2"
  shows "a1 - b1 <= a2 - (b2 :: congruence)"
  unfolding less_eq_congruence_def congruence_le_def
  apply (simp only: minus_congruence.rep_eq)
  by (rule minus_congruence_rep_mono)
     (use assms in
       \<open>simp_all add: less_eq_congruence_def congruence_le_def\<close>)

lemma times_congruence_rep_mono_nonbottom:
  fixes c1 m1 c2 m2 d1 n1 d2 n2 :: int
  assumes m: "m2 dvd m1" "m2 dvd c1 - c2"
      and n: "n2 dvd n1" "n2 dvd d1 - d2"
  shows
    "congruence_le_rep
       (times_congruence_rep (Some (c1, m1)) (Some (d1, n1)))
       (times_congruence_rep (Some (c2, m2)) (Some (d2, n2)))"
proof -
  obtain km where m1: "m1 = m2 * km"
    using m(1) unfolding dvd_def by blast
  obtain kc where c1: "c1 = c2 + m2 * kc"
  proof -
    obtain kc where "c1 - c2 = m2 * kc"
      using m(2) unfolding dvd_def by blast
    then have "c1 = c2 + m2 * kc" by simp
    then show thesis by (rule that)
  qed
  obtain kn where n1: "n1 = n2 * kn"
    using n(1) unfolding dvd_def by blast
  obtain kd where d1: "d1 = d2 + n2 * kd"
  proof -
    obtain kd where "d1 - d2 = n2 * kd"
      using n(2) unfolding dvd_def by blast
    then have "d1 = d2 + n2 * kd" by simp
    then show thesis by (rule that)
  qed
  let ?coarse =
    "gcd (c2 * n2) (gcd (m2 * d2) (m2 * n2))"
  have coarse_c: "?coarse dvd c2 * n2"
    by (rule gcd_dvd1)
  have coarse_tail:
    "?coarse dvd gcd (m2 * d2) (m2 * n2)"
    by (rule gcd_dvd2)
  have coarse_d: "?coarse dvd m2 * d2"
    by (rule dvd_trans[OF coarse_tail gcd_dvd1])
  have coarse_mn: "?coarse dvd m2 * n2"
    by (rule dvd_trans[OF coarse_tail gcd_dvd2])
  have generator1: "?coarse dvd c1 * n1"
  proof -
    have first: "?coarse dvd (c2 * n2) * kn"
      by (rule dvd_mult2[OF coarse_c])
    have second: "?coarse dvd (m2 * n2) * (kc * kn)"
      by (rule dvd_mult2[OF coarse_mn])
    have sum:
      "?coarse dvd (c2 * n2) * kn +
        (m2 * n2) * (kc * kn)"
      by (rule dvd_add[OF first second])
    show ?thesis
      using sum unfolding c1 n1 by (simp add: algebra_simps)
  qed
  have generator2: "?coarse dvd m1 * d1"
  proof -
    have first: "?coarse dvd (m2 * d2) * km"
      by (rule dvd_mult2[OF coarse_d])
    have second: "?coarse dvd (m2 * n2) * (km * kd)"
      by (rule dvd_mult2[OF coarse_mn])
    have sum:
      "?coarse dvd (m2 * d2) * km +
        (m2 * n2) * (km * kd)"
      by (rule dvd_add[OF first second])
    show ?thesis
      using sum unfolding m1 d1 by (simp add: algebra_simps)
  qed
  have generator3: "?coarse dvd m1 * n1"
  proof -
    have "?coarse dvd (m2 * n2) * (km * kn)"
      by (rule dvd_mult2[OF coarse_mn])
    then show ?thesis
      unfolding m1 n1 by (simp add: algebra_simps)
  qed
  have modulus:
    "?coarse dvd
      gcd (c1 * n1) (gcd (m1 * d1) (m1 * n1))"
  proof (rule gcd_greatest)
    show "?coarse dvd c1 * n1" by (rule generator1)
    show "?coarse dvd gcd (m1 * d1) (m1 * n1)"
      by (rule gcd_greatest[OF generator2 generator3])
  qed
  have offset: "?coarse dvd c1 * d1 - c2 * d2"
    by (rule congruence_product_divisible[OF m(2) n(2)])
  show ?thesis
    unfolding congruence_le_rep_iff
    using modulus offset
    by (simp only: times_congruence_rep.simps
        gamma_normalize_congruence_rep
        gamma_congruence_rep.simps congruence_class_subset_iff)
qed

lemma times_congruence_rep_mono:
  assumes "congruence_le_rep a1 a2"
      and "congruence_le_rep b1 b2"
  shows
    "congruence_le_rep
       (times_congruence_rep a1 b1)
       (times_congruence_rep a2 b2)"
  using assms
  by (cases a1; cases a2; cases b1; cases b2;
      auto split: prod.splits
        intro: times_congruence_rep_mono_nonbottom)

lemma congruence_times_mono:
  assumes "a1 <= a2" and "b1 <= b2"
  shows "a1 * b1 <= a2 * (b2 :: congruence)"
  unfolding less_eq_congruence_def congruence_le_def
  apply (simp only: times_congruence.rep_eq)
  by (rule times_congruence_rep_mono)
     (use assms in
       \<open>simp_all add: less_eq_congruence_def congruence_le_def\<close>)

subsection \<open>Comparison and truthiness queries\<close>

text \<open>
  Congruence classes carry no ordering information, so \<open>congruence_lt\<close> is
  always \<open>None\<close>. Equality and truthiness are decidable exactly when both
  sides are singleton classes (modulus \<open>0\<close>): \<open>congruence_singleton\<close> reads
  that singleton constant off the normalized representation.
\<close>

definition congruence_singleton :: "congruence => int option" where
  "congruence_singleton a =
     (case Rep_congruence a of
        Some (c, m) => (if m = 0 then Some c else None)
      | None => None)"

lemma congruence_singleton_sound:
  assumes "congruence_singleton a = Some c" and "n \<in> gamma_congruence a"
  shows "n = c"
  using assms
  unfolding congruence_singleton_def gamma_congruence_def
  by (cases "Rep_congruence a" rule: option.exhaust) (auto split: if_splits)

lemma congruence_singleton_le:
  assumes "\<not> is_empty (a1::congruence)" and "a1 \<le> a2"
      and "congruence_singleton a2 = Some c"
  shows "congruence_singleton a1 = Some c"
proof -
  have rep2: "Rep_congruence a2 = Some (c, 0)"
    using assms(3) unfolding congruence_singleton_def
    by (auto split: option.splits if_splits)
  have le: "congruence_le_rep (Rep_congruence a1) (Rep_congruence a2)"
    using assms(2) unfolding less_eq_congruence_def congruence_le_def .
  show ?thesis
  proof (cases "Rep_congruence a1")
    case None
    then have "a1 = bottom_congruence"
      by (simp only: Rep_congruence_inject[symmetric] Rep_bottom_congruence)
    with assms(1) show ?thesis
      by (simp add: is_bottom_congruence_def bot_congruence_def)
  next
    case (Some p)
    obtain c1 m1 where p: "p = (c1, m1)" by (cases p)
    with le Some rep2 have "m1 = 0 \<and> c1 = c" by simp
    with Some p show ?thesis unfolding congruence_singleton_def by simp
  qed
qed

definition congruence_lt :: "congruence => congruence => bool option" where
  "congruence_lt a b =
     (case (congruence_singleton a, congruence_singleton b) of
        (Some c1, Some c2) => Some (c1 < c2)
      | _ => None)"

definition congruence_eqb :: "congruence => congruence => bool option" where
  "congruence_eqb a b =
     (case (congruence_singleton a, congruence_singleton b) of
        (Some c1, Some c2) => Some (c1 = c2)
      | _ => None)"

definition congruence_tobool :: "congruence => bool option" where
  "congruence_tobool a =
     (case congruence_singleton a of Some c => Some (c \<noteq> 0) | None => None)"

lemma congruence_lt_sound:
  assumes "congruence_lt a b = Some c" and "i \<in> gamma_congruence a" and "j \<in> gamma_congruence b"
  shows "(i < j) = c"
proof -
  obtain c1 c2 where s1: "congruence_singleton a = Some c1" and s2: "congruence_singleton b = Some c2"
      and c_def: "c = (c1 < c2)"
    using assms(1) unfolding congruence_lt_def by (auto split: option.splits)
  have "i = c1" using congruence_singleton_sound[OF s1 assms(2)] .
  moreover have "j = c2" using congruence_singleton_sound[OF s2 assms(3)] .
  ultimately show ?thesis using c_def by simp
qed

lemma congruence_eqb_sound:
  assumes "congruence_eqb a b = Some c" and "i \<in> gamma_congruence a" and "j \<in> gamma_congruence b"
  shows "(i = j) = c"
proof -
  obtain c1 c2 where s1: "congruence_singleton a = Some c1" and s2: "congruence_singleton b = Some c2"
      and c_def: "c = (c1 = c2)"
    using assms(1) unfolding congruence_eqb_def by (auto split: option.splits)
  have "i = c1" using congruence_singleton_sound[OF s1 assms(2)] .
  moreover have "j = c2" using congruence_singleton_sound[OF s2 assms(3)] .
  ultimately show ?thesis using c_def by simp
qed

lemma congruence_tobool_sound:
  assumes "congruence_tobool a = Some c" and "i \<in> gamma_congruence a"
  shows "(i \<noteq> 0) = c"
proof -
  obtain c1 where s1: "congruence_singleton a = Some c1" and c_def: "c = (c1 \<noteq> 0)"
    using assms(1) unfolding congruence_tobool_def by (auto split: option.splits)
  have "i = c1" using congruence_singleton_sound[OF s1 assms(2)] .
  then show ?thesis using c_def by simp
qed

lemma congruence_lt_mono:
  assumes "\<not> is_empty (a1::congruence)" and "\<not> is_empty b1" and "a1 \<le> a2" and "b1 \<le> b2"
      and "congruence_lt a2 b2 = Some c"
  shows "congruence_lt a1 b1 = Some c"
proof -
  obtain c1 c2 where s1: "congruence_singleton a2 = Some c1" and s2: "congruence_singleton b2 = Some c2"
      and c_def: "c = (c1 < c2)"
    using assms(5) unfolding congruence_lt_def by (auto split: option.splits)
  have "congruence_singleton a1 = Some c1"
    using congruence_singleton_le[OF assms(1,3) s1] .
  moreover have "congruence_singleton b1 = Some c2"
    using congruence_singleton_le[OF assms(2,4) s2] .
  ultimately show ?thesis unfolding congruence_lt_def using c_def by simp
qed

lemma congruence_eqb_mono:
  assumes "\<not> is_empty (a1::congruence)" and "\<not> is_empty b1" and "a1 \<le> a2" and "b1 \<le> b2"
      and "congruence_eqb a2 b2 = Some c"
  shows "congruence_eqb a1 b1 = Some c"
proof -
  obtain c1 c2 where s1: "congruence_singleton a2 = Some c1" and s2: "congruence_singleton b2 = Some c2"
      and c_def: "c = (c1 = c2)"
    using assms(5) unfolding congruence_eqb_def by (auto split: option.splits)
  have "congruence_singleton a1 = Some c1"
    using congruence_singleton_le[OF assms(1,3) s1] .
  moreover have "congruence_singleton b1 = Some c2"
    using congruence_singleton_le[OF assms(2,4) s2] .
  ultimately show ?thesis unfolding congruence_eqb_def using c_def by simp
qed

lemma congruence_tobool_mono:
  assumes "\<not> is_empty (a1::congruence)" and "a1 \<le> a2" and "congruence_tobool a2 = Some c"
  shows "congruence_tobool a1 = Some c"
proof -
  obtain c1 where s1: "congruence_singleton a2 = Some c1" and c_def: "c = (c1 \<noteq> 0)"
    using assms(3) unfolding congruence_tobool_def by (auto split: option.splits)
  have "congruence_singleton a1 = Some c1"
    using congruence_singleton_le[OF assms(1,2) s1] .
  then show ?thesis unfolding congruence_tobool_def using c_def by simp
qed


definition congruence_exact_binop ::
    "(int \<Rightarrow> int \<Rightarrow> int) \<Rightarrow> (congruence \<Rightarrow> congruence \<Rightarrow> congruence) \<Rightarrow>
      congruence \<Rightarrow> congruence \<Rightarrow> congruence" where
  "congruence_exact_binop f fallback a b =
    (if is_empty a \<or> is_empty b then bot
     else case (congruence_singleton a, congruence_singleton b) of
       (Some x, Some y) \<Rightarrow> congruence_of_int (f x y)
     | _ \<Rightarrow> fallback a b)"

lemma congruence_exact_binop_sound:
  assumes "i \<in> gamma_congruence a" "j \<in> gamma_congruence b"
    and sound: "\<And>a b i j. i \<in> gamma_congruence a \<Longrightarrow> j \<in> gamma_congruence b \<Longrightarrow>
      f i j \<in> gamma_congruence (fallback a b)"
  shows "f i j \<in> gamma_congruence (congruence_exact_binop f fallback a b)"
  using assms congruence_singleton_sound
  unfolding congruence_exact_binop_def
  by (auto simp: is_bottom_congruence_correct congruence_of_int_def
      split: option.splits dest: congruence_singleton_sound)

lemma congruence_exact_binop_mono:
  assumes "a1 \<le> a2" "b1 \<le> b2"
    and sound: "\<And>a b i j. i \<in> gamma_congruence a \<Longrightarrow> j \<in> gamma_congruence b \<Longrightarrow>
      f i j \<in> gamma_congruence (fallback a b)"
    and mono: "\<And>a1 a2 b1 b2. a1 \<le> a2 \<Longrightarrow> b1 \<le> b2 \<Longrightarrow>
      fallback a1 b1 \<le> fallback a2 b2"
  shows "congruence_exact_binop f fallback a1 b1 \<le>
    congruence_exact_binop f fallback a2 b2"
proof (cases "is_empty a1 \<or> is_empty b1")
  case True
  then show ?thesis by (simp add: congruence_exact_binop_def)
next
  case False
  have ne: "\<not> is_empty a1" "\<not> is_empty b1" "\<not> is_empty a2" "\<not> is_empty b2"
    using False is_empty_antimono assms(1,2) by blast+
  have singleton_le:
    "\<And>a x. congruence_singleton a = Some x \<Longrightarrow>
      gamma_congruence a = {x}"
    unfolding congruence_singleton_def gamma_congruence_def
    by (auto split: option.splits if_splits)
  show ?thesis
    unfolding congruence_exact_binop_def
    using ne congruence_singleton_le[OF ne(1) assms(1)]
      congruence_singleton_le[OF ne(2) assms(2)]
      assms(1,2) mono[OF assms(1,2)] sound singleton_le
    by (auto simp: less_eq_congruence_iff_gamma congruence_of_int_def
        split: option.splits)
qed


lemma gamma_congruence_exact_division:
  assumes nz: "d \<noteq> 0" and dc: "d dvd c" and dm: "d dvd m"
  shows "gamma_congruence (mk_congruence (c div d) (m div d)) =
    (\<lambda>n. c_div n d) ` {n. m dvd n - c}"
proof -
  obtain c' m' where c: "c = d * c'" and m: "m = d * m'"
    using dc dm by (auto simp: dvd_def)
  have cancel: "\<And>k. c_div (d * k) d = k"
    using nz by (simp add: c_div_exact)
  have quotients: "c div d = c'" "m div d = m'"
    using nz by (simp_all add: c m)
  show ?thesis
  proof (rule set_eqI, rule iffI)
    fix q
    assume "q \<in> gamma_congruence (mk_congruence (c div d) (m div d))"
    then obtain k where q: "q - c' = m' * k"
      unfolding quotients by (auto simp: dvd_def)
    have member: "d * q \<in> {n. m dvd n - c}"
      unfolding c m using q by (auto simp: dvd_def algebra_simps)
    show "q \<in> (\<lambda>n. c_div n d) ` {n. m dvd n - c}"
      using imageI[OF member, of "\<lambda>n. c_div n d"] by (simp add: cancel)
  next
    fix q
    assume "q \<in> (\<lambda>n. c_div n d) ` {n. m dvd n - c}"
    then obtain n k where q: "q = c_div n d" and n: "n - c = m * k"
      by (auto simp: dvd_def)
    have n_eq: "n = d * (c' + m' * k)"
      using n unfolding c m by (simp add: algebra_simps)
    show "q \<in> gamma_congruence (mk_congruence (c div d) (m div d))"
      unfolding quotients q n_eq by (simp add: cancel)
  qed
qed

definition congruence_divides :: "int \<Rightarrow> congruence \<Rightarrow> bool" where
  "congruence_divides d a =
    (case Rep_congruence a of None \<Rightarrow> True | Some (c, m) \<Rightarrow> d dvd c \<and> d dvd m)"

lemma congruence_divides_iff:
  "congruence_divides d a \<longleftrightarrow> (\<forall>n \<in> gamma_congruence a. d dvd n)"
proof -
  have classes: "\<And>c m. (\<forall>n. m dvd n - c \<longrightarrow> d dvd n) \<longleftrightarrow> d dvd c \<and> d dvd m"
    using congruence_class_subset_iff[of _ _ d 0]
    by (auto simp: subset_iff)
  show ?thesis
    unfolding congruence_divides_def gamma_congruence_def
    by (auto simp: classes split: option.splits)
qed

definition congruence_div_const :: "congruence \<Rightarrow> int \<Rightarrow> congruence" where
  "congruence_div_const a d =
    (case Rep_congruence a of None \<Rightarrow> bot
     | Some (c, m) \<Rightarrow>
       if d = 0 then congruence_of_int 0
       else if congruence_divides d a then mk_congruence (c div d) (m div d)
       else top)"

lemma gamma_congruence_div_const:
  assumes "d \<noteq> 0" "congruence_divides d a"
  shows "gamma_congruence (congruence_div_const a d) =
    (\<lambda>n. c_div n d) ` gamma_congruence a"
proof (cases "Rep_congruence a")
  case None
  then have "gamma_congruence a = {}" by (simp add: gamma_congruence_def)
  then show ?thesis by (simp add: congruence_div_const_def None bot_congruence_def)
next
  case (Some p)
  obtain c m where p: "p = (c, m)" by (cases p)
  have divisibility: "d dvd c" "d dvd m"
    using assms(2) unfolding congruence_divides_def Some p by simp_all
  have gamma: "gamma_congruence a = {n. m dvd n - c}"
    by (simp add: gamma_congruence_def Some p)
  show ?thesis
    using gamma_congruence_exact_division[OF assms(1) divisibility]
    by (simp add: congruence_div_const_def Some p assms gamma)
qed

lemma gamma_congruence_div_const_cases:
  "gamma_congruence (congruence_div_const a d) =
    (if is_empty a then {}
     else if d = 0 then {0}
     else if congruence_divides d a then (\<lambda>n. c_div n d) ` gamma_congruence a
     else UNIV)"
proof (cases "is_empty a")
  case True
  then have rep: "Rep_congruence a = None"
    by (simp add: is_bottom_congruence_def bot_congruence_def)
  show ?thesis using True
    by (simp add: congruence_div_const_def rep bot_congruence_def
        is_bottom_congruence_correct gamma_congruence_def)
next
  case False
  then obtain c m where rep: "Rep_congruence a = Some (c, m)"
    by (cases "Rep_congruence a") (auto simp: is_bottom_congruence_correct gamma_congruence_def)
  show ?thesis
    using gamma_congruence_div_const[of d a]
    by (cases "d = 0"; cases "congruence_divides d a")
       (use False in \<open>simp_all add: congruence_div_const_def rep congruence_of_int_def\<close>)
qed

lemma congruence_div_const_sound:
  assumes "i \<in> gamma_congruence a"
  shows "c_div i d \<in> gamma_congruence (congruence_div_const a d)"
  using assms
  by (auto simp: gamma_congruence_div_const_cases is_bottom_congruence_correct)

lemma congruence_div_const_mono:
  assumes "a1 \<le> a2"
  shows "congruence_div_const a1 d \<le> congruence_div_const a2 d"
  using assms
  by (auto simp: less_eq_congruence_iff_gamma gamma_congruence_div_const_cases
      is_bottom_congruence_correct congruence_divides_iff)

definition congruence_div_fallback :: "congruence \<Rightarrow> congruence \<Rightarrow> congruence" where
  "congruence_div_fallback a b =
    (if is_empty a \<or> is_empty b then bot
     else case congruence_singleton b of
       Some c \<Rightarrow> congruence_div_const a c
     | None \<Rightarrow> top)"

lemma congruence_div_fallback_sound:
  assumes "i \<in> gamma_congruence a" "j \<in> gamma_congruence b"
  shows "c_div i j \<in> gamma_congruence (congruence_div_fallback a b)"
  using assms congruence_singleton_sound[OF _ assms(2)]

  unfolding congruence_div_fallback_def
  by (auto simp: is_bottom_congruence_correct split: option.splits
      intro: congruence_div_const_sound)

lemma congruence_div_fallback_mono:
  assumes "a1 \<le> a2" "b1 \<le> b2"
  shows "congruence_div_fallback a1 b1 \<le> congruence_div_fallback a2 b2"
proof (cases "is_empty a1 \<or> is_empty b1")
  case True
  then show ?thesis by (simp add: congruence_div_fallback_def)
next
  case False
  have ne: "\<not> is_empty a1" "\<not> is_empty b1" "\<not> is_empty a2" "\<not> is_empty b2"
    using False is_empty_antimono assms by blast+
  show ?thesis unfolding congruence_div_fallback_def
    using ne assms congruence_singleton_le[OF ne(2) assms(2)]
    by (auto split: option.splits intro: congruence_div_const_mono)
qed

definition congruence_div :: "congruence \<Rightarrow> congruence \<Rightarrow> congruence" where
  "congruence_div = congruence_exact_binop c_div congruence_div_fallback"

definition congruence_mod :: "congruence \<Rightarrow> congruence \<Rightarrow> congruence" where
  "congruence_mod = congruence_exact_binop c_mod (\<lambda>a b. a - top * b)"

lemma congruence_mod_fallback_sound:
  assumes "i \<in> gamma_congruence a" "j \<in> gamma_congruence b"
  shows "c_mod i j \<in> gamma_congruence (a - top * b)"
proof -
  have "i - c_div i j * j \<in> gamma_congruence (a - top * b)"
    by (intro congruence_minus_sound assms congruence_times_sound) simp_all
  then show ?thesis by (cases "j = 0") (simp_all add: c_mod_def)
qed

lemma congruence_div_sound:
  "i \<in> gamma_congruence a \<Longrightarrow> j \<in> gamma_congruence b \<Longrightarrow>
    c_div i j \<in> gamma_congruence (congruence_div a b)"
  unfolding congruence_div_def
  by (rule congruence_exact_binop_sound) (auto intro: congruence_div_fallback_sound)

lemma congruence_mod_sound:
  "i \<in> gamma_congruence a \<Longrightarrow> j \<in> gamma_congruence b \<Longrightarrow>
    c_mod i j \<in> gamma_congruence (congruence_mod a b)"
  unfolding congruence_mod_def
  by (rule congruence_exact_binop_sound) (auto intro: congruence_mod_fallback_sound)

lemma congruence_div_mono:
  "a1 \<le> a2 \<Longrightarrow> b1 \<le> b2 \<Longrightarrow> congruence_div a1 b1 \<le> congruence_div a2 b2"
  unfolding congruence_div_def
  by (rule congruence_exact_binop_mono)
     (auto intro: congruence_div_fallback_sound congruence_div_fallback_mono)

lemma congruence_mod_mono:
  "a1 \<le> a2 \<Longrightarrow> b1 \<le> b2 \<Longrightarrow> congruence_mod a1 b1 \<le> congruence_mod a2 b2"
  unfolding congruence_mod_def
  by (rule congruence_exact_binop_mono)
     (auto intro: congruence_mod_fallback_sound congruence_minus_mono congruence_times_mono)

subsection \<open>Abstract expression evaluation\<close>

fun aval_congruence ::
    "exp => (vname => congruence) => congruence"
where
  "aval_congruence (N n) sigma = congruence_of_int n"
| "aval_congruence (V x) sigma = sigma x"
| "aval_congruence (Plus e1 e2) sigma =
     aval_congruence e1 sigma + aval_congruence e2 sigma"
| "aval_congruence (Minus e1 e2) sigma =
     aval_congruence e1 sigma - aval_congruence e2 sigma"
| "aval_congruence (Times e1 e2) sigma =
     aval_congruence e1 sigma * aval_congruence e2 sigma"
  | "aval_congruence (Div e1 e2) sigma = congruence_div (aval_congruence e1 sigma) (aval_congruence e2 sigma)"
  | "aval_congruence (Mod e1 e2) sigma = congruence_mod (aval_congruence e1 sigma) (aval_congruence e2 sigma)"
| "aval_congruence (Less e1 e2) sigma =
     (if is_empty (aval_congruence e1 sigma) \<or> is_empty (aval_congruence e2 sigma) then bot
      else if congruence_lt (aval_congruence e1 sigma) (aval_congruence e2 sigma) = Some True
      then congruence_of_int 1
      else if congruence_lt (aval_congruence e1 sigma) (aval_congruence e2 sigma) = Some False
      then congruence_of_int 0
      else congruence_of_int 0 \<squnion> congruence_of_int 1)"
| "aval_congruence (LessEq e1 e2) sigma =
     (if is_empty (aval_congruence e2 sigma) \<or> is_empty (aval_congruence e1 sigma) then bot
      else if congruence_lt (aval_congruence e2 sigma) (aval_congruence e1 sigma) = Some False
      then congruence_of_int 1
      else if congruence_lt (aval_congruence e2 sigma) (aval_congruence e1 sigma) = Some True
      then congruence_of_int 0
      else congruence_of_int 0 \<squnion> congruence_of_int 1)"
| "aval_congruence (Greater e1 e2) sigma =
     (if is_empty (aval_congruence e2 sigma) \<or> is_empty (aval_congruence e1 sigma) then bot
      else if congruence_lt (aval_congruence e2 sigma) (aval_congruence e1 sigma) = Some True
      then congruence_of_int 1
      else if congruence_lt (aval_congruence e2 sigma) (aval_congruence e1 sigma) = Some False
      then congruence_of_int 0
      else congruence_of_int 0 \<squnion> congruence_of_int 1)"
| "aval_congruence (GreaterEq e1 e2) sigma =
     (if is_empty (aval_congruence e1 sigma) \<or> is_empty (aval_congruence e2 sigma) then bot
      else if congruence_lt (aval_congruence e1 sigma) (aval_congruence e2 sigma) = Some False
      then congruence_of_int 1
      else if congruence_lt (aval_congruence e1 sigma) (aval_congruence e2 sigma) = Some True
      then congruence_of_int 0
      else congruence_of_int 0 \<squnion> congruence_of_int 1)"
| "aval_congruence (NotEq e1 e2) sigma =
     (if is_empty (aval_congruence e1 sigma) \<or> is_empty (aval_congruence e2 sigma) then bot
      else if congruence_eqb (aval_congruence e1 sigma) (aval_congruence e2 sigma) = Some False
      then congruence_of_int 1
      else if congruence_eqb (aval_congruence e1 sigma) (aval_congruence e2 sigma) = Some True
      then congruence_of_int 0
      else congruence_of_int 0 \<squnion> congruence_of_int 1)"
| "aval_congruence (exp.Eq e1 e2) sigma =
     (if is_empty (aval_congruence e1 sigma) \<or> is_empty (aval_congruence e2 sigma) then bot
      else if congruence_eqb (aval_congruence e1 sigma) (aval_congruence e2 sigma) = Some True
      then congruence_of_int 1
      else if congruence_eqb (aval_congruence e1 sigma) (aval_congruence e2 sigma) = Some False
      then congruence_of_int 0
      else congruence_of_int 0 \<squnion> congruence_of_int 1)"
| "aval_congruence (exp.Not e) sigma =
     (if is_empty (aval_congruence e sigma) then bot
      else if congruence_tobool (aval_congruence e sigma) = Some True then congruence_of_int 0
      else if congruence_tobool (aval_congruence e sigma) = Some False then congruence_of_int 1
      else congruence_of_int 0 \<squnion> congruence_of_int 1)"
| "aval_congruence (And e1 e2) sigma =
     (if is_empty (aval_congruence e1 sigma) \<or> is_empty (aval_congruence e2 sigma) then bot
      else if congruence_tobool (aval_congruence e1 sigma) = Some False
           \<or> congruence_tobool (aval_congruence e2 sigma) = Some False
      then congruence_of_int 0
      else if congruence_tobool (aval_congruence e1 sigma) = Some True
           \<and> congruence_tobool (aval_congruence e2 sigma) = Some True
      then congruence_of_int 1
      else congruence_of_int 0 \<squnion> congruence_of_int 1)"
| "aval_congruence (Or e1 e2) sigma =
     (if is_empty (aval_congruence e1 sigma) \<or> is_empty (aval_congruence e2 sigma) then bot
      else if congruence_tobool (aval_congruence e1 sigma) = Some True
           \<or> congruence_tobool (aval_congruence e2 sigma) = Some True
      then congruence_of_int 1
      else if congruence_tobool (aval_congruence e1 sigma) = Some False
           \<and> congruence_tobool (aval_congruence e2 sigma) = Some False
      then congruence_of_int 0
      else congruence_of_int 0 \<squnion> congruence_of_int 1)"

interpretation congruence_arith: expression_domain_mono
    aval_congruence congruence_of_int "(+)" "(-)" "(*)" congruence_div congruence_mod
    congruence_lt congruence_eqb congruence_tobool
  apply unfold_locales
  apply (simp_all add: congruence_plus_sound congruence_minus_sound congruence_times_sound congruence_div_sound congruence_mod_sound
                        congruence_plus_mono congruence_minus_mono congruence_times_mono congruence_div_mono congruence_mod_mono
                        congruence_lt_sound congruence_eqb_sound
                        congruence_tobool_sound[unfolded truthy_def])
  apply (blast intro: congruence_lt_mono[unfolded is_empty_congruence])
  apply (blast intro: congruence_eqb_mono[unfolded is_empty_congruence])
  apply (blast intro: congruence_tobool_mono[unfolded is_empty_congruence])
  done

end
