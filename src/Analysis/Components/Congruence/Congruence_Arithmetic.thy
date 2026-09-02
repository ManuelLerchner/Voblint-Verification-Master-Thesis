theory Congruence_Arithmetic
  imports Congruence_Lattice "Voblint_VIMP.VIMP_Expr"
    Abstract_Arithmetic
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

lemma congruence_plus_sound:
  assumes "i \<in> gamma_congruence a"
      and "j \<in> gamma_congruence b"
  shows "i + j \<in> gamma_congruence (a + b)"
proof -
  have ai:
    "i \<in> gamma_congruence_rep (Rep_congruence a)"
    using assms(1) unfolding gamma_congruence_def .
  have bj:
    "j \<in> gamma_congruence_rep (Rep_congruence b)"
    using assms(2) unfolding gamma_congruence_def .
  show ?thesis
  proof (cases "Rep_congruence a")
    case None
    with ai show ?thesis by simp
  next
    case (Some p1)
    obtain c1 m1 where p1: "p1 = (c1, m1)"
      by (cases p1)
    show ?thesis
    proof (cases "Rep_congruence b")
      case None
      with bj show ?thesis by simp
    next
      case (Some p2)
      obtain c2 m2 where p2: "p2 = (c2, m2)"
        by (cases p2)
      have mi: "m1 dvd i - c1"
        using ai unfolding \<open>Rep_congruence a = Some p1\<close> p1 by simp
      have mj: "m2 dvd j - c2"
        using bj unfolding Some p2 by simp
      have gi: "gcd m1 m2 dvd i - c1"
        by (rule dvd_trans[OF gcd_dvd1 mi])
      have gj: "gcd m1 m2 dvd j - c2"
        by (rule dvd_trans[OF gcd_dvd2 mj])
      have sum_eq:
        "(i - c1) + (j - c2) = (i + j) - (c1 + c2)"
        by simp
      have "gcd m1 m2 dvd (i + j) - (c1 + c2)"
        using dvd_add[OF gi gj] unfolding sum_eq .
      then show ?thesis
        unfolding gamma_congruence_def
          plus_congruence.rep_eq
          \<open>Rep_congruence a = Some p1\<close> Some p1 p2
        by (simp only: plus_congruence_rep.simps
            gamma_normalize_congruence_rep
            gamma_congruence_rep.simps Set.mem_Collect_eq)
    qed
  qed
qed

lemma congruence_minus_sound:
  assumes "i \<in> gamma_congruence a"
      and "j \<in> gamma_congruence b"
  shows "i - j \<in> gamma_congruence (a - b)"
proof -
  have ai:
    "i \<in> gamma_congruence_rep (Rep_congruence a)"
    using assms(1) unfolding gamma_congruence_def .
  have bj:
    "j \<in> gamma_congruence_rep (Rep_congruence b)"
    using assms(2) unfolding gamma_congruence_def .
  show ?thesis
  proof (cases "Rep_congruence a")
    case None
    with ai show ?thesis by simp
  next
    case (Some p1)
    obtain c1 m1 where p1: "p1 = (c1, m1)"
      by (cases p1)
    show ?thesis
    proof (cases "Rep_congruence b")
      case None
      with bj show ?thesis by simp
    next
      case (Some p2)
      obtain c2 m2 where p2: "p2 = (c2, m2)"
        by (cases p2)
      have mi: "m1 dvd i - c1"
        using ai unfolding \<open>Rep_congruence a = Some p1\<close> p1 by simp
      have mj: "m2 dvd j - c2"
        using bj unfolding Some p2 by simp
      have gi: "gcd m1 m2 dvd i - c1"
        by (rule dvd_trans[OF gcd_dvd1 mi])
      have gj: "gcd m1 m2 dvd j - c2"
        by (rule dvd_trans[OF gcd_dvd2 mj])
      have diff_eq:
        "(i - c1) - (j - c2) = (i - j) - (c1 - c2)"
        by simp
      have "gcd m1 m2 dvd (i - j) - (c1 - c2)"
        using dvd_diff[OF gi gj] unfolding diff_eq .
      then show ?thesis
        unfolding gamma_congruence_def
          minus_congruence.rep_eq
          \<open>Rep_congruence a = Some p1\<close> Some p1 p2
        by (simp only: minus_congruence_rep.simps
            gamma_normalize_congruence_rep
            gamma_congruence_rep.simps Set.mem_Collect_eq)
    qed
  qed
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
  assumes "i \<in> gamma_congruence a"
      and "j \<in> gamma_congruence b"
  shows "i * j \<in> gamma_congruence (a * b)"
proof -
  have ai:
    "i \<in> gamma_congruence_rep (Rep_congruence a)"
    using assms(1) unfolding gamma_congruence_def .
  have bj:
    "j \<in> gamma_congruence_rep (Rep_congruence b)"
    using assms(2) unfolding gamma_congruence_def .
  show ?thesis
  proof (cases "Rep_congruence a")
    case None
    with ai show ?thesis by simp
  next
    case (Some p1)
    obtain c1 m1 where p1: "p1 = (c1, m1)"
      by (cases p1)
    show ?thesis
    proof (cases "Rep_congruence b")
      case None
      with bj show ?thesis by simp
    next
      case (Some p2)
      obtain c2 m2 where p2: "p2 = (c2, m2)"
        by (cases p2)
      have mi: "m1 dvd i - c1"
        using ai unfolding \<open>Rep_congruence a = Some p1\<close> p1 by simp
      have mj: "m2 dvd j - c2"
        using bj unfolding Some p2 by simp
      have
        "gcd (c1 * m2) (gcd (m1 * c2) (m1 * m2))
           dvd i * j - c1 * c2"
        by (rule congruence_product_divisible[OF mi mj])
      then show ?thesis
        unfolding gamma_congruence_def
          times_congruence.rep_eq
          \<open>Rep_congruence a = Some p1\<close> Some p1 p2
        by (simp only: times_congruence_rep.simps
            gamma_normalize_congruence_rep
            gamma_congruence_rep.simps Set.mem_Collect_eq)
    qed
  qed
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
proof -
  have modulus: "gcd m2 n2 dvd gcd m1 n1"
    by (rule gcd_mono[OF m(1) n(1)])
  have first: "gcd m2 n2 dvd c1 - c2"
    by (rule dvd_trans[OF gcd_dvd1 m(2)])
  have second: "gcd m2 n2 dvd d1 - d2"
    by (rule dvd_trans[OF gcd_dvd2 n(2)])
  have offset:
    "gcd m2 n2 dvd (c1 + d1) - (c2 + d2)"
  proof -
    have sum_eq:
      "(c1 - c2) + (d1 - d2) =
       (c1 + d1) - (c2 + d2)"
      by simp
    show ?thesis using dvd_add[OF first second] unfolding sum_eq .
  qed
  show ?thesis
    unfolding congruence_le_rep_iff
    using modulus offset
    by (simp only: plus_congruence_rep.simps
        gamma_normalize_congruence_rep
        gamma_congruence_rep.simps congruence_class_subset_iff)
qed

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
proof -
  have modulus: "gcd m2 n2 dvd gcd m1 n1"
    by (rule gcd_mono[OF m(1) n(1)])
  have first: "gcd m2 n2 dvd c1 - c2"
    by (rule dvd_trans[OF gcd_dvd1 m(2)])
  have second: "gcd m2 n2 dvd d1 - d2"
    by (rule dvd_trans[OF gcd_dvd2 n(2)])
  have offset:
    "gcd m2 n2 dvd (c1 - d1) - (c2 - d2)"
  proof -
    have diff_eq:
      "(c1 - c2) - (d1 - d2) =
       (c1 - d1) - (c2 - d2)"
      by simp
    show ?thesis using dvd_diff[OF first second] unfolding diff_eq .
  qed
  show ?thesis
    unfolding congruence_le_rep_iff
    using modulus offset
    by (simp only: minus_congruence_rep.simps
        gamma_normalize_congruence_rep
        gamma_congruence_rep.simps congruence_class_subset_iff)
qed

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
      by (simp add: is_empty_congruence is_bottom_congruence_def bot_congruence_def)
  next
    case (Some p)
    obtain c1 m1 where p: "p = (c1, m1)" by (cases p)
    with le Some rep2 have "m1 = 0 \<and> c1 = c" by simp
    with Some p show ?thesis unfolding congruence_singleton_def by simp
  qed
qed

fun congruence_lt :: "congruence => congruence => bool option" where
  "congruence_lt _ _ = None"

definition congruence_eqb :: "congruence => congruence => bool option" where
  "congruence_eqb a b =
     (case (congruence_singleton a, congruence_singleton b) of
        (Some c1, Some c2) => Some (c1 = c2)
      | _ => None)"

definition congruence_tobool :: "congruence => bool option" where
  "congruence_tobool a =
     (case congruence_singleton a of Some c => Some (c \<noteq> 0) | None => None)"

lemma congruence_lt_sound:
  "congruence_lt a b = Some c \<Longrightarrow> i \<in> gamma_congruence a \<Longrightarrow> j \<in> gamma_congruence b \<Longrightarrow> (i < j) = c"
  by simp

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
  "\<not> is_empty (a1::congruence) \<Longrightarrow> \<not> is_empty b1 \<Longrightarrow> a1 \<le> a2 \<Longrightarrow> b1 \<le> b2 \<Longrightarrow>
   congruence_lt a2 b2 = Some c \<Longrightarrow> congruence_lt a1 b1 = Some c"
  by simp

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
| "aval_congruence (Less e1 e2) sigma =
     (if is_empty (aval_congruence e1 sigma) \<or> is_empty (aval_congruence e2 sigma) then bot
      else if congruence_lt (aval_congruence e1 sigma) (aval_congruence e2 sigma) = Some True
      then congruence_of_int 1
      else if congruence_lt (aval_congruence e1 sigma) (aval_congruence e2 sigma) = Some False
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

interpretation congruence_arith: expression_domain_sound
    aval_congruence congruence_of_int congruence_lt congruence_eqb congruence_tobool
  apply unfold_locales
  apply (simp_all add: congruence_plus_sound congruence_minus_sound congruence_times_sound
                        congruence_plus_mono congruence_minus_mono congruence_times_mono
                        congruence_lt_sound congruence_eqb_sound
                        congruence_tobool_sound[unfolded truthy_def]
                    del: congruence_lt.simps)
  apply (blast intro: congruence_lt_mono[unfolded is_empty_congruence])
  apply (blast intro: congruence_eqb_mono[unfolded is_empty_congruence])
  apply (blast intro: congruence_tobool_mono[unfolded is_empty_congruence])
  done

lemmas aval_congruence_sound = congruence_arith.aval_dom_sound
lemmas aval_congruence_mono = congruence_arith.aval_dom_mono

end
