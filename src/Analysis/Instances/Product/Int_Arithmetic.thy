theory Int_Arithmetic
  imports
    Int_Refinement
    Sign_Arithmetic
    Interval_Backward
    Parity_Domain
    Congruence_Arithmetic
begin

section \<open>Composite integer arithmetic\<close>

text \<open>
  Raw operations preserve the independent component results. Refinement is an
  explicit policy at the composite operation boundary, so the same arithmetic
  evaluator can expose the unreduced product or apply one or repeated
  progressive reduction rounds.
\<close>

definition plus_int_dom_raw :: "int_dom => int_dom => int_dom" where
  "plus_int_dom_raw a b =
     (top :: int_dom)\<lparr>
       int_sign := int_sign a + int_sign b,
       int_ivl := int_ivl a + int_ivl b,
       int_parity := int_parity a + int_parity b,
       int_congruence := int_congruence a + int_congruence b
     \<rparr>"

definition minus_int_dom_raw :: "int_dom => int_dom => int_dom" where
  "minus_int_dom_raw a b =
     (top :: int_dom)\<lparr>
       int_sign := int_sign a - int_sign b,
       int_ivl := int_ivl a - int_ivl b,
       int_parity := int_parity a - int_parity b,
       int_congruence := int_congruence a - int_congruence b
     \<rparr>"

definition times_int_dom_raw :: "int_dom => int_dom => int_dom" where
  "times_int_dom_raw a b =
     (top :: int_dom)\<lparr>
       int_sign := int_sign a * int_sign b,
       int_ivl := int_ivl a * int_ivl b,
       int_parity := int_parity a * int_parity b,
       int_congruence := int_congruence a * int_congruence b
     \<rparr>"

definition plus_int_dom ::
    "refine_mode => int_dom => int_dom => int_dom"
where
  "plus_int_dom mode a b =
     refine mode (plus_int_dom_raw a b)"

definition minus_int_dom ::
    "refine_mode => int_dom => int_dom => int_dom"
where
  "minus_int_dom mode a b =
     refine mode (minus_int_dom_raw a b)"

definition times_int_dom ::
    "refine_mode => int_dom => int_dom => int_dom"
where
  "times_int_dom mode a b =
     refine mode (times_int_dom_raw a b)"


subsection \<open>Literal embedding\<close>

definition int_dom_of_int :: "int => int_dom" where
  "int_dom_of_int n =
     (top :: int_dom)\<lparr>
       int_sign := sign_of_int n,
       int_ivl := Ivl (Fin n) (Fin n),
       int_parity := parity_of_int n,
       int_congruence := congruence_of_int n
     \<rparr>"

lemma gamma_int_dom_of_int [simp]:
  "gamma_int_dom (int_dom_of_int n) = {n}"
  by (auto simp: int_dom_of_int_def gamma_int_dom_def
        sign_of_int_gamma parity_of_int_gamma)


subsection \<open>Raw operation laws\<close>

lemma plus_int_dom_raw_sound:
  assumes "x : gamma_int_dom a"
      and "y : gamma_int_dom b"
  shows "x + y : gamma_int_dom (plus_int_dom_raw a b)"
  using assms
  by (auto simp: gamma_int_dom_def plus_int_dom_raw_def
        intro: sign_plus_sound ivl_plus_sound
          parity_plus_sound congruence_plus_sound)

lemma minus_int_dom_raw_sound:
  assumes "x : gamma_int_dom a"
      and "y : gamma_int_dom b"
  shows "x - y : gamma_int_dom (minus_int_dom_raw a b)"
  using assms
  by (auto simp: gamma_int_dom_def minus_int_dom_raw_def
        intro: sign_minus_sound ivl_minus_sound
          parity_minus_sound congruence_minus_sound)

lemma times_int_dom_raw_sound:
  assumes "x : gamma_int_dom a"
      and "y : gamma_int_dom b"
  shows "x * y : gamma_int_dom (times_int_dom_raw a b)"
  using assms
  by (auto simp: gamma_int_dom_def times_int_dom_raw_def
        intro: sign_times_sound ivl_times_sound
          parity_times_sound congruence_times_sound)

lemma plus_int_dom_raw_mono:
  assumes "a1 <= a2" and "b1 <= b2"
  shows "plus_int_dom_raw a1 b1 <= plus_int_dom_raw a2 b2"
  using assms
  by (auto simp: plus_int_dom_raw_def less_eq_int_dom_ext_def
        intro: sign_plus_combine_mono ivl_plus_mono
          parity_plus_combine_mono congruence_plus_mono)

lemma minus_int_dom_raw_mono:
  assumes "a1 <= a2" and "b1 <= b2"
  shows "minus_int_dom_raw a1 b1 <= minus_int_dom_raw a2 b2"
  using assms
  by (auto simp: minus_int_dom_raw_def less_eq_int_dom_ext_def
        intro: sign_minus_combine_mono ivl_minus_mono
          parity_minus_combine_mono congruence_minus_mono)

lemma times_int_dom_raw_mono:
  assumes "a1 <= a2" and "b1 <= b2"
  shows "times_int_dom_raw a1 b1 <= times_int_dom_raw a2 b2"
  using assms
  by (auto simp: times_int_dom_raw_def less_eq_int_dom_ext_def
        intro: sign_times_combine_mono ivl_times_mono
          parity_times_combine_mono congruence_times_mono)


subsection \<open>Mode-aware operation laws\<close>

lemma plus_int_dom_sound:
  assumes "x : gamma_int_dom a"
      and "y : gamma_int_dom b"
  shows "x + y : gamma_int_dom (plus_int_dom mode a b)"
proof -
  have "x + y : gamma_int_dom (plus_int_dom_raw a b)"
    by (rule plus_int_dom_raw_sound[OF assms])
  then show ?thesis
    unfolding plus_int_dom_def
    using refine_exact by simp
qed

lemma minus_int_dom_sound:
  assumes "x : gamma_int_dom a"
      and "y : gamma_int_dom b"
  shows "x - y : gamma_int_dom (minus_int_dom mode a b)"
proof -
  have "x - y : gamma_int_dom (minus_int_dom_raw a b)"
    by (rule minus_int_dom_raw_sound[OF assms])
  then show ?thesis
    unfolding minus_int_dom_def
    using refine_exact by simp
qed

lemma times_int_dom_sound:
  assumes "x : gamma_int_dom a"
      and "y : gamma_int_dom b"
  shows "x * y : gamma_int_dom (times_int_dom mode a b)"
proof -
  have "x * y : gamma_int_dom (times_int_dom_raw a b)"
    by (rule times_int_dom_raw_sound[OF assms])
  then show ?thesis
    unfolding times_int_dom_def
    using refine_exact by simp
qed

text \<open>
  The total logical Fixpoint wrapper returns its input when the structural loop
  has no result. Without a termination theorem this fallback does not support
  unconditional order monotonicity. Never and Once inherit monotonicity
  directly from the identity and the verified reduction round.
\<close>

lemma refine_nonfixpoint_mono:
  assumes "mode ~= Refine_Fixpoint"
  shows "mono (refine mode)"
proof (cases mode)
  case Refine_Never
  then show ?thesis by (simp add: mono_def)
next
  case Refine_Once
  then show ?thesis using refine_once_mono by simp
next
  case Refine_Fixpoint
  with assms show ?thesis by simp
qed

lemma plus_int_dom_mono:
  assumes "mode ~= Refine_Fixpoint"
      and "a1 <= a2" and "b1 <= b2"
  shows "plus_int_dom mode a1 b1 <= plus_int_dom mode a2 b2"
proof -
  have raw:
    "plus_int_dom_raw a1 b1 <= plus_int_dom_raw a2 b2"
    by (rule plus_int_dom_raw_mono[OF assms(2,3)])
  show ?thesis
    unfolding plus_int_dom_def
    by (rule monoD[OF refine_nonfixpoint_mono[OF assms(1)] raw])
qed

lemma minus_int_dom_mono:
  assumes "mode ~= Refine_Fixpoint"
      and "a1 <= a2" and "b1 <= b2"
  shows "minus_int_dom mode a1 b1 <= minus_int_dom mode a2 b2"
proof -
  have raw:
    "minus_int_dom_raw a1 b1 <= minus_int_dom_raw a2 b2"
    by (rule minus_int_dom_raw_mono[OF assms(2,3)])
  show ?thesis
    unfolding minus_int_dom_def
    by (rule monoD[OF refine_nonfixpoint_mono[OF assms(1)] raw])
qed

lemma times_int_dom_mono:
  assumes "mode ~= Refine_Fixpoint"
      and "a1 <= a2" and "b1 <= b2"
  shows "times_int_dom mode a1 b1 <= times_int_dom mode a2 b2"
proof -
  have raw:
    "times_int_dom_raw a1 b1 <= times_int_dom_raw a2 b2"
    by (rule times_int_dom_raw_mono[OF assms(2,3)])
  show ?thesis
    unfolding times_int_dom_def
    by (rule monoD[OF refine_nonfixpoint_mono[OF assms(1)] raw])
qed


subsection \<open>Comparison and truthiness queries\<close>

text \<open>
  \<open>int_dom\<close> has no fixed \<open>plus\<close>/\<open>minus\<close>/\<open>times\<close> class instance -- its
  arithmetic is parameterized by \<open>refine_mode\<close> (\<open>plus_int_dom
  Refine_Never\<close> and \<open>plus_int_dom Refine_Fixpoint\<close> are genuinely
  different operations) -- so \<open>int_dom\<close> cannot literally interpret
  \<open>Voblint_Analysis.Abstract_Arithmetic\<close>'s \<open>expression_domain_sound\<close> locale,
  which fixes those as type-class operations. \<open>int_dom_lt\<close>/\<open>int_dom_eqb\<close>/
  \<open>int_dom_tobool\<close> below still follow that locale's query shape exactly
  (\<open>bool option\<close>, \<open>Some True\<close>/\<open>Some False\<close>/\<open>None\<close>), and \<open>aval_int_dom\<close>'s
  \<open>Less\<close>/\<open>Eq\<close>/\<open>Not\<close>/\<open>And\<close>/\<open>Or\<close> cases below reuse that same shape by hand;
  only the generic locale interpretation itself does not transfer.

  Each query consults the composite's own four components in turn --
  Interval and Sign first, since they carry ordering information Parity and
  Congruence lack -- taking the first that decides. This treats \<open>int_dom\<close>
  as one reduced value with one query per comparison, not as four
  independent per-component evaluations mechanically joined.
\<close>

text \<open>
  \<open>first_deciding\<close>/\<open>first_deciding2\<close> are the shared "ask components in
  priority order, stop at the first that decides" policy, factored out once
  so \<open>int_dom_lt\<close>/\<open>int_dom_eqb\<close>/\<open>int_dom_tobool\<close> below are plain
  registries rather than repeating the same nested-\<open>case\<close> pattern three
  times. The query LIST holds functions, not pre-evaluated \<open>bool option\<close>
  results: generated ML is strict, so passing already-evaluated results
  would force all four component queries every time, discarding the
  short-circuit that a hand-written nested \<open>case\<close> gets for free.
\<close>

fun first_deciding :: "('a => 'b option) list => 'a => 'b option" where
  "first_deciding [] x = None"
| "first_deciding (q # qs) x = (case q x of Some y => Some y | None => first_deciding qs x)"

fun first_deciding2 :: "('a => 'a => 'b option) list => 'a => 'a => 'b option" where
  "first_deciding2 [] x y = None"
| "first_deciding2 (q # qs) x y = (case q x y of Some z => Some z | None => first_deciding2 qs x y)"

lemma first_deciding_SomeE:
  assumes "first_deciding qs x = Some y"
  obtains q where "q \<in> set qs" and "q x = Some y"
  using assms by (induction qs) (auto split: option.splits)

lemma first_deciding_not_none_of_component:
  assumes "q \<in> set qs" and "q x = Some y"
  shows "first_deciding qs x \<noteq> None"
  using assms by (induction qs) (auto split: option.splits)

lemma first_deciding2_SomeE:
  assumes "first_deciding2 qs x y = Some z"
  obtains q where "q \<in> set qs" and "q x y = Some z"
  using assms by (induction qs) (auto split: option.splits)

lemma first_deciding2_not_none_of_component:
  assumes "q \<in> set qs" and "q x y = Some z"
  shows "first_deciding2 qs x y \<noteq> None"
  using assms by (induction qs) (auto split: option.splits)

definition int_dom_lt :: "int_dom => int_dom => bool option" where
  "int_dom_lt d1 d2 =
     first_deciding2
       [\<lambda>a b. interval_lt (int_ivl a) (int_ivl b),
        \<lambda>a b. sign_lt (int_sign a) (int_sign b),
        \<lambda>a b. parity_lt (int_parity a) (int_parity b),
        \<lambda>a b. congruence_lt (int_congruence a) (int_congruence b)]
       d1 d2"

definition int_dom_eqb :: "int_dom => int_dom => bool option" where
  "int_dom_eqb d1 d2 =
     first_deciding2
       [\<lambda>a b. interval_eqb (int_ivl a) (int_ivl b),
        \<lambda>a b. sign_eqb (int_sign a) (int_sign b),
        \<lambda>a b. parity_eqb (int_parity a) (int_parity b),
        \<lambda>a b. congruence_eqb (int_congruence a) (int_congruence b)]
       d1 d2"

definition int_dom_tobool :: "int_dom => bool option" where
  "int_dom_tobool d =
     first_deciding
       [\<lambda>a. interval_tobool (int_ivl a),
        \<lambda>a. sign_tobool (int_sign a),
        \<lambda>a. parity_tobool (int_parity a),
        \<lambda>a. congruence_tobool (int_congruence a)]
       d"

lemma gamma_int_dom_sup_ub1: "gamma_int_dom a \<subseteq> gamma_int_dom (a \<squnion> b)"
  using gamma_sup_ub1[of a b] by simp

lemma gamma_int_dom_sup_ub2: "gamma_int_dom b \<subseteq> gamma_int_dom (a \<squnion> b)"
  using gamma_sup_ub2[of b a] by simp

lemma int_dom_not_bot_componentsE:
  assumes "\<not> is_empty (d::int_dom)"
  obtains n where "n \<in> gamma_sign (int_sign d)" "n \<in> gamma_ivl (int_ivl d)"
    "n \<in> gamma_parity (int_parity d)" "n \<in> gamma_congruence (int_congruence d)"
proof -
  have "gamma_int_dom d \<noteq> {}"
    using assms by (simp add: is_bottom_int_dom_correct)
  then obtain n where "n \<in> gamma_int_dom d" by blast
  then have "n \<in> gamma_sign (int_sign d) \<and> n \<in> gamma_ivl (int_ivl d) \<and>
             n \<in> gamma_parity (int_parity d) \<and> n \<in> gamma_congruence (int_congruence d)"
    by (simp add: gamma_int_dom_def)
  then show ?thesis using that by blast
qed

lemma int_dom_lt_sound:
  assumes "int_dom_lt d1 d2 = Some c" and "x \<in> gamma_int_dom d1" and "y \<in> gamma_int_dom d2"
  shows "(x < y) = c"
proof -
  have hx: "x \<in> gamma_sign (int_sign d1)" "x \<in> gamma_ivl (int_ivl d1)"
           "x \<in> gamma_parity (int_parity d1)" "x \<in> gamma_congruence (int_congruence d1)"
    using assms(2) by (simp_all add: gamma_int_dom_def)
  have hy: "y \<in> gamma_sign (int_sign d2)" "y \<in> gamma_ivl (int_ivl d2)"
           "y \<in> gamma_parity (int_parity d2)" "y \<in> gamma_congruence (int_congruence d2)"
    using assms(3) by (simp_all add: gamma_int_dom_def)
  show ?thesis
  proof (cases "interval_lt (int_ivl d1) (int_ivl d2)")
    case (Some b)
    with assms(1) have "c = b" unfolding int_dom_lt_def by simp
    then show ?thesis using interval_lt_sound[OF Some hx(2) hy(2)] by simp
  next
    case ivl_none: None
    show ?thesis
    proof (cases "sign_lt (int_sign d1) (int_sign d2)")
      case (Some b)
      with assms(1) ivl_none have "c = b" unfolding int_dom_lt_def by simp
      then show ?thesis using sign_lt_sound[OF Some hx(1) hy(1)] by simp
    next
      case sign_none: None
      show ?thesis
      proof (cases "parity_lt (int_parity d1) (int_parity d2)")
        case (Some b)
        with assms(1) ivl_none sign_none have "c = b" unfolding int_dom_lt_def by simp
        then show ?thesis using parity_lt_sound[OF Some hx(3) hy(3)] by simp
      next
        case None
        with assms(1) ivl_none sign_none have "congruence_lt (int_congruence d1) (int_congruence d2) = Some c"
          unfolding int_dom_lt_def by simp
        then show ?thesis using congruence_lt_sound[OF _ hx(4) hy(4)] by simp
      qed
    qed
  qed
qed

lemma int_dom_eqb_sound:
  assumes "int_dom_eqb d1 d2 = Some c" and "x \<in> gamma_int_dom d1" and "y \<in> gamma_int_dom d2"
  shows "(x = y) = c"
proof -
  have hx: "x \<in> gamma_sign (int_sign d1)" "x \<in> gamma_ivl (int_ivl d1)"
           "x \<in> gamma_parity (int_parity d1)" "x \<in> gamma_congruence (int_congruence d1)"
    using assms(2) by (simp_all add: gamma_int_dom_def)
  have hy: "y \<in> gamma_sign (int_sign d2)" "y \<in> gamma_ivl (int_ivl d2)"
           "y \<in> gamma_parity (int_parity d2)" "y \<in> gamma_congruence (int_congruence d2)"
    using assms(3) by (simp_all add: gamma_int_dom_def)
  show ?thesis
  proof (cases "interval_eqb (int_ivl d1) (int_ivl d2)")
    case (Some b)
    with assms(1) have "c = b" unfolding int_dom_eqb_def by simp
    then show ?thesis using interval_eqb_sound[OF Some hx(2) hy(2)] by simp
  next
    case ivl_none: None
    show ?thesis
    proof (cases "sign_eqb (int_sign d1) (int_sign d2)")
      case (Some b)
      with assms(1) ivl_none have "c = b" unfolding int_dom_eqb_def by simp
      then show ?thesis using sign_eqb_sound[OF Some hx(1) hy(1)] by simp
    next
      case sign_none: None
      show ?thesis
      proof (cases "parity_eqb (int_parity d1) (int_parity d2)")
        case (Some b)
        with assms(1) ivl_none sign_none have "c = b" unfolding int_dom_eqb_def by simp
        then show ?thesis using parity_eqb_sound[OF Some hx(3) hy(3)] by simp
      next
        case None
        with assms(1) ivl_none sign_none have "congruence_eqb (int_congruence d1) (int_congruence d2) = Some c"
          unfolding int_dom_eqb_def by (auto split: option.splits)
        then show ?thesis using congruence_eqb_sound[OF _ hx(4) hy(4)] by simp
      qed
    qed
  qed
qed

lemma int_dom_tobool_sound:
  assumes "int_dom_tobool d = Some c" and "x \<in> gamma_int_dom d"
  shows "(x \<noteq> 0) = c"
proof -
  have hx: "x \<in> gamma_sign (int_sign d)" "x \<in> gamma_ivl (int_ivl d)"
           "x \<in> gamma_parity (int_parity d)" "x \<in> gamma_congruence (int_congruence d)"
    using assms(2) by (simp_all add: gamma_int_dom_def)
  show ?thesis
  proof (cases "interval_tobool (int_ivl d)")
    case (Some b)
    with assms(1) have "c = b" unfolding int_dom_tobool_def by simp
    then show ?thesis using interval_tobool_sound[OF Some hx(2)] by simp
  next
    case ivl_none: None
    show ?thesis
    proof (cases "sign_tobool (int_sign d)")
      case (Some b)
      with assms(1) ivl_none have "c = b" unfolding int_dom_tobool_def by simp
      then show ?thesis using sign_tobool_sound[OF Some hx(1)] by simp
    next
      case sign_none: None
      show ?thesis
      proof (cases "parity_tobool (int_parity d)")
        case (Some b)
        with assms(1) ivl_none sign_none have "c = b" unfolding int_dom_tobool_def by simp
        then show ?thesis using parity_tobool_sound[OF Some hx(3)] by simp
      next
        case None
        with assms(1) ivl_none sign_none have "congruence_tobool (int_congruence d) = Some c"
          unfolding int_dom_tobool_def by (auto split: option.splits)
        then show ?thesis using congruence_tobool_sound[OF _ hx(4)] by simp
      qed
    qed
  qed
qed

lemma int_dom_lt_mono:
  assumes h1: "\<not> is_empty (d1::int_dom)" and h2: "\<not> is_empty e1"
      and hd: "d1 \<le> d2" and he: "e1 \<le> e2"
      and hwide: "int_dom_lt d2 e2 = Some c"
  shows "int_dom_lt d1 e1 = Some c"
proof -
  obtain n where hn: "n \<in> gamma_sign (int_sign d1)" "n \<in> gamma_ivl (int_ivl d1)"
      "n \<in> gamma_parity (int_parity d1)" "n \<in> gamma_congruence (int_congruence d1)"
    using int_dom_not_bot_componentsE[OF h1] .
  obtain m where hm: "m \<in> gamma_sign (int_sign e1)" "m \<in> gamma_ivl (int_ivl e1)"
      "m \<in> gamma_parity (int_parity e1)" "m \<in> gamma_congruence (int_congruence e1)"
    using int_dom_not_bot_componentsE[OF h2] .
  have le1: "int_sign d1 \<le> int_sign d2" "int_ivl d1 \<le> int_ivl d2"
            "int_parity d1 \<le> int_parity d2" "int_congruence d1 \<le> int_congruence d2"
    using hd by (simp_all add: less_eq_int_dom_ext_def)
  have le2: "int_sign e1 \<le> int_sign e2" "int_ivl e1 \<le> int_ivl e2"
            "int_parity e1 \<le> int_parity e2" "int_congruence e1 \<le> int_congruence e2"
    using he by (simp_all add: less_eq_int_dom_ext_def)
  have nb1_sign: "\<not> is_empty (int_sign d1)" using hn(1) by (auto simp: is_bottom_sign_correct)
  have nb1_ivl: "\<not> is_empty (int_ivl d1)" using hn(2) by (auto simp: is_bottom_ivl_correct)
  have nb1_parity: "\<not> is_empty (int_parity d1)" using hn(3) by (auto simp: is_bottom_parity_correct)
  have nb1_cong: "\<not> is_empty (int_congruence d1)" using hn(4) by (auto simp: is_bottom_congruence_correct)
  have nb2_sign: "\<not> is_empty (int_sign e1)" using hm(1) by (auto simp: is_bottom_sign_correct)
  have nb2_ivl: "\<not> is_empty (int_ivl e1)" using hm(2) by (auto simp: is_bottom_ivl_correct)
  have nb2_parity: "\<not> is_empty (int_parity e1)" using hm(3) by (auto simp: is_bottom_parity_correct)
  have nb2_cong: "\<not> is_empty (int_congruence e1)" using hm(4) by (auto simp: is_bottom_congruence_correct)
  have m_ivl: "interval_lt (int_ivl d2) (int_ivl e2) = Some c \<Longrightarrow>
               interval_lt (int_ivl d1) (int_ivl e1) = Some c"
    by (rule interval_lt_mono[OF nb1_ivl nb2_ivl le1(2) le2(2)])
  have m_sign: "sign_lt (int_sign d2) (int_sign e2) = Some c \<Longrightarrow>
                sign_lt (int_sign d1) (int_sign e1) = Some c"
    by (rule sign_lt_mono[OF nb1_sign nb2_sign le1(1) le2(1)])
  have m_parity: "parity_lt (int_parity d2) (int_parity e2) = Some c \<Longrightarrow>
                  parity_lt (int_parity d1) (int_parity e1) = Some c"
    by (rule parity_lt_mono[OF nb1_parity nb2_parity le1(3) le2(3)])
  have m_cong: "congruence_lt (int_congruence d2) (int_congruence e2) = Some c \<Longrightarrow>
                congruence_lt (int_congruence d1) (int_congruence e1) = Some c"
    by (rule congruence_lt_mono[OF nb1_cong nb2_cong le1(4) le2(4)])
  have n_d1: "n \<in> gamma_int_dom d1" using hn by (simp add: gamma_int_dom_def)
  have m_e1: "m \<in> gamma_int_dom e1" using hm by (simp add: gamma_int_dom_def)
  have n_d2: "n \<in> gamma_int_dom d2" using n_d1 gamma_mono[OF hd] by auto
  have m_e2: "m \<in> gamma_int_dom e2" using m_e1 gamma_mono[OF he] by auto
  have not_none: "int_dom_lt d1 e1 \<noteq> None"
  proof (cases "interval_lt (int_ivl d2) (int_ivl e2)")
    case (Some b)
    with hwide have "c = b" unfolding int_dom_lt_def by simp
    with Some m_ivl have "interval_lt (int_ivl d1) (int_ivl e1) = Some c" by simp
    then show ?thesis unfolding int_dom_lt_def by simp
  next
    case ivl_none: None
    show ?thesis
    proof (cases "sign_lt (int_sign d2) (int_sign e2)")
      case (Some b)
      with hwide ivl_none have "c = b" unfolding int_dom_lt_def by simp
      with Some m_sign have "sign_lt (int_sign d1) (int_sign e1) = Some c" by simp
      then show ?thesis
        unfolding int_dom_lt_def by (cases "interval_lt (int_ivl d1) (int_ivl e1)") simp_all
    next
      case sign_none: None
      show ?thesis
      proof (cases "parity_lt (int_parity d2) (int_parity e2)")
        case (Some b)
        with hwide ivl_none sign_none have "c = b" unfolding int_dom_lt_def by simp
        with Some m_parity have "parity_lt (int_parity d1) (int_parity e1) = Some c" by simp
        then show ?thesis
          unfolding int_dom_lt_def
          by (cases "interval_lt (int_ivl d1) (int_ivl e1)";
              cases "sign_lt (int_sign d1) (int_sign e1)") simp_all
      next
        case None
        with hwide ivl_none sign_none
          have "congruence_lt (int_congruence d2) (int_congruence e2) = Some c"
          unfolding int_dom_lt_def by simp
        with m_cong have "congruence_lt (int_congruence d1) (int_congruence e1) = Some c" by simp
        then show ?thesis
          unfolding int_dom_lt_def
          by (cases "interval_lt (int_ivl d1) (int_ivl e1)";
              cases "sign_lt (int_sign d1) (int_sign e1)";
              cases "parity_lt (int_parity d1) (int_parity e1)") simp_all
      qed
    qed
  qed
  then obtain x where hx: "int_dom_lt d1 e1 = Some x" by auto
  have "(n < m) = c" using int_dom_lt_sound[OF hwide n_d2 m_e2] .
  moreover have "(n < m) = x" using int_dom_lt_sound[OF hx n_d1 m_e1] .
  ultimately have "x = c" by simp
  with hx show ?thesis by simp
qed

lemma int_dom_eqb_mono:
  assumes h1: "\<not> is_empty (d1::int_dom)" and h2: "\<not> is_empty e1"
      and hd: "d1 \<le> d2" and he: "e1 \<le> e2"
      and hwide: "int_dom_eqb d2 e2 = Some c"
  shows "int_dom_eqb d1 e1 = Some c"
proof -
  obtain n where hn: "n \<in> gamma_sign (int_sign d1)" "n \<in> gamma_ivl (int_ivl d1)"
      "n \<in> gamma_parity (int_parity d1)" "n \<in> gamma_congruence (int_congruence d1)"
    using int_dom_not_bot_componentsE[OF h1] .
  obtain m where hm: "m \<in> gamma_sign (int_sign e1)" "m \<in> gamma_ivl (int_ivl e1)"
      "m \<in> gamma_parity (int_parity e1)" "m \<in> gamma_congruence (int_congruence e1)"
    using int_dom_not_bot_componentsE[OF h2] .
  have le1: "int_sign d1 \<le> int_sign d2" "int_ivl d1 \<le> int_ivl d2"
            "int_parity d1 \<le> int_parity d2" "int_congruence d1 \<le> int_congruence d2"
    using hd by (simp_all add: less_eq_int_dom_ext_def)
  have le2: "int_sign e1 \<le> int_sign e2" "int_ivl e1 \<le> int_ivl e2"
            "int_parity e1 \<le> int_parity e2" "int_congruence e1 \<le> int_congruence e2"
    using he by (simp_all add: less_eq_int_dom_ext_def)
  have nb1_sign: "\<not> is_empty (int_sign d1)" using hn(1) by (auto simp: is_bottom_sign_correct)
  have nb1_ivl: "\<not> is_empty (int_ivl d1)" using hn(2) by (auto simp: is_bottom_ivl_correct)
  have nb1_parity: "\<not> is_empty (int_parity d1)" using hn(3) by (auto simp: is_bottom_parity_correct)
  have nb1_cong: "\<not> is_empty (int_congruence d1)" using hn(4) by (auto simp: is_bottom_congruence_correct)
  have nb2_sign: "\<not> is_empty (int_sign e1)" using hm(1) by (auto simp: is_bottom_sign_correct)
  have nb2_ivl: "\<not> is_empty (int_ivl e1)" using hm(2) by (auto simp: is_bottom_ivl_correct)
  have nb2_parity: "\<not> is_empty (int_parity e1)" using hm(3) by (auto simp: is_bottom_parity_correct)
  have nb2_cong: "\<not> is_empty (int_congruence e1)" using hm(4) by (auto simp: is_bottom_congruence_correct)
  have m_ivl: "interval_eqb (int_ivl d2) (int_ivl e2) = Some c \<Longrightarrow>
               interval_eqb (int_ivl d1) (int_ivl e1) = Some c"
    by (rule interval_eqb_mono[OF nb1_ivl nb2_ivl le1(2) le2(2)])
  have m_sign: "sign_eqb (int_sign d2) (int_sign e2) = Some c \<Longrightarrow>
                sign_eqb (int_sign d1) (int_sign e1) = Some c"
    by (rule sign_eqb_mono[OF nb1_sign nb2_sign le1(1) le2(1)])
  have m_parity: "parity_eqb (int_parity d2) (int_parity e2) = Some c \<Longrightarrow>
                  parity_eqb (int_parity d1) (int_parity e1) = Some c"
    by (rule parity_eqb_mono[OF nb1_parity nb2_parity le1(3) le2(3)])
  have m_cong: "congruence_eqb (int_congruence d2) (int_congruence e2) = Some c \<Longrightarrow>
                congruence_eqb (int_congruence d1) (int_congruence e1) = Some c"
    by (rule congruence_eqb_mono[OF nb1_cong nb2_cong le1(4) le2(4)])
  have n_d1: "n \<in> gamma_int_dom d1" using hn by (simp add: gamma_int_dom_def)
  have m_e1: "m \<in> gamma_int_dom e1" using hm by (simp add: gamma_int_dom_def)
  have n_d2: "n \<in> gamma_int_dom d2" using n_d1 gamma_mono[OF hd] by auto
  have m_e2: "m \<in> gamma_int_dom e2" using m_e1 gamma_mono[OF he] by auto
  have not_none: "int_dom_eqb d1 e1 \<noteq> None"
  proof (cases "interval_eqb (int_ivl d2) (int_ivl e2)")
    case (Some b)
    with hwide have "c = b" unfolding int_dom_eqb_def by simp
    with Some m_ivl have "interval_eqb (int_ivl d1) (int_ivl e1) = Some c" by simp
    then show ?thesis unfolding int_dom_eqb_def by simp
  next
    case ivl_none: None
    show ?thesis
    proof (cases "sign_eqb (int_sign d2) (int_sign e2)")
      case (Some b)
      with hwide ivl_none have "c = b" unfolding int_dom_eqb_def by simp
      with Some m_sign have "sign_eqb (int_sign d1) (int_sign e1) = Some c" by simp
      then show ?thesis
        unfolding int_dom_eqb_def by (cases "interval_eqb (int_ivl d1) (int_ivl e1)") simp_all
    next
      case sign_none: None
      show ?thesis
      proof (cases "parity_eqb (int_parity d2) (int_parity e2)")
        case (Some b)
        with hwide ivl_none sign_none have "c = b" unfolding int_dom_eqb_def by simp
        with Some m_parity have "parity_eqb (int_parity d1) (int_parity e1) = Some c" by simp
        then show ?thesis
          unfolding int_dom_eqb_def
          by (cases "interval_eqb (int_ivl d1) (int_ivl e1)";
              cases "sign_eqb (int_sign d1) (int_sign e1)") simp_all
      next
        case None
        with hwide ivl_none sign_none
          have "congruence_eqb (int_congruence d2) (int_congruence e2) = Some c"
          unfolding int_dom_eqb_def by (auto split: option.splits)
        with m_cong have "congruence_eqb (int_congruence d1) (int_congruence e1) = Some c" by simp
        then show ?thesis
          unfolding int_dom_eqb_def
          by (cases "interval_eqb (int_ivl d1) (int_ivl e1)";
              cases "sign_eqb (int_sign d1) (int_sign e1)";
              cases "parity_eqb (int_parity d1) (int_parity e1)") simp_all
      qed
    qed
  qed
  then obtain x where hx: "int_dom_eqb d1 e1 = Some x" by auto
  have "(n = m) = c" using int_dom_eqb_sound[OF hwide n_d2 m_e2] .
  moreover have "(n = m) = x" using int_dom_eqb_sound[OF hx n_d1 m_e1] .
  ultimately have "x = c" by simp
  with hx show ?thesis by simp
qed

lemma int_dom_tobool_mono:
  assumes h1: "\<not> is_empty (d1::int_dom)" and hd: "d1 \<le> d2"
      and hwide: "int_dom_tobool d2 = Some c"
  shows "int_dom_tobool d1 = Some c"
proof -
  obtain n where hn: "n \<in> gamma_sign (int_sign d1)" "n \<in> gamma_ivl (int_ivl d1)"
      "n \<in> gamma_parity (int_parity d1)" "n \<in> gamma_congruence (int_congruence d1)"
    using int_dom_not_bot_componentsE[OF h1] .
  have le1: "int_sign d1 \<le> int_sign d2" "int_ivl d1 \<le> int_ivl d2"
            "int_parity d1 \<le> int_parity d2" "int_congruence d1 \<le> int_congruence d2"
    using hd by (simp_all add: less_eq_int_dom_ext_def)
  have nb1_sign: "\<not> is_empty (int_sign d1)" using hn(1) by (auto simp: is_bottom_sign_correct)
  have nb1_ivl: "\<not> is_empty (int_ivl d1)" using hn(2) by (auto simp: is_bottom_ivl_correct)
  have nb1_parity: "\<not> is_empty (int_parity d1)" using hn(3) by (auto simp: is_bottom_parity_correct)
  have nb1_cong: "\<not> is_empty (int_congruence d1)" using hn(4) by (auto simp: is_bottom_congruence_correct)
  have m_ivl: "interval_tobool (int_ivl d2) = Some c \<Longrightarrow> interval_tobool (int_ivl d1) = Some c"
    by (rule interval_tobool_mono[OF nb1_ivl le1(2)])
  have m_sign: "sign_tobool (int_sign d2) = Some c \<Longrightarrow> sign_tobool (int_sign d1) = Some c"
    by (rule sign_tobool_mono[OF nb1_sign le1(1)])
  have m_parity: "parity_tobool (int_parity d2) = Some c \<Longrightarrow> parity_tobool (int_parity d1) = Some c"
    by (rule parity_tobool_mono[OF nb1_parity le1(3)])
  have m_cong: "congruence_tobool (int_congruence d2) = Some c \<Longrightarrow>
                congruence_tobool (int_congruence d1) = Some c"
    by (rule congruence_tobool_mono[OF nb1_cong le1(4)])
  have n_d1: "n \<in> gamma_int_dom d1" using hn by (simp add: gamma_int_dom_def)
  have n_d2: "n \<in> gamma_int_dom d2" using n_d1 gamma_mono[OF hd] by auto
  have not_none: "int_dom_tobool d1 \<noteq> None"
  proof (cases "interval_tobool (int_ivl d2)")
    case (Some b)
    with hwide have "c = b" unfolding int_dom_tobool_def by simp
    with Some m_ivl have "interval_tobool (int_ivl d1) = Some c" by simp
    then show ?thesis unfolding int_dom_tobool_def by simp
  next
    case ivl_none: None
    show ?thesis
    proof (cases "sign_tobool (int_sign d2)")
      case (Some b)
      with hwide ivl_none have "c = b" unfolding int_dom_tobool_def by simp
      with Some m_sign have "sign_tobool (int_sign d1) = Some c" by simp
      then show ?thesis
        unfolding int_dom_tobool_def by (cases "interval_tobool (int_ivl d1)") simp_all
    next
      case sign_none: None
      show ?thesis
      proof (cases "parity_tobool (int_parity d2)")
        case (Some b)
        with hwide ivl_none sign_none have "c = b" unfolding int_dom_tobool_def by simp
        with Some m_parity have "parity_tobool (int_parity d1) = Some c" by simp
        then show ?thesis
          unfolding int_dom_tobool_def
          by (cases "interval_tobool (int_ivl d1)"; cases "sign_tobool (int_sign d1)") simp_all
      next
        case None
        with hwide ivl_none sign_none have "congruence_tobool (int_congruence d2) = Some c"
          unfolding int_dom_tobool_def by (auto split: option.splits)
        with m_cong have "congruence_tobool (int_congruence d1) = Some c" by simp
        then show ?thesis
          unfolding int_dom_tobool_def
          by (cases "interval_tobool (int_ivl d1)"; cases "sign_tobool (int_sign d1)";
              cases "parity_tobool (int_parity d1)") simp_all
      qed
    qed
  qed
  then obtain x where hx: "int_dom_tobool d1 = Some x" by auto
  have "(n \<noteq> 0) = c" using int_dom_tobool_sound[OF hwide n_d2] .
  moreover have "(n \<noteq> 0) = x" using int_dom_tobool_sound[OF hx n_d1] .
  ultimately have "x = c" by simp
  with hx show ?thesis by simp
qed

subsection \<open>Arithmetic-expression evaluation\<close>

text \<open>
  \<open>Less\<close>/\<open>Eq\<close>/\<open>Not\<close>/\<open>And\<close>/\<open>Or\<close> mirror the shape
  \<open>Voblint_Analysis.Abstract_Arithmetic.expression_domain_sound\<close> would assume
  were \<open>int_dom\<close> able to interpret it (see the comment above
  \<open>int_dom_lt\<close>): each operand is recursively evaluated to a whole
  \<open>int_dom\<close> value first, and only the composite-level \<open>int_dom_lt\<close>/
  \<open>int_dom_eqb\<close>/\<open>int_dom_tobool\<close> query decides the result -- never a
  separate per-component recursive walk.
\<close>

definition int_dom_bool_unknown :: int_dom where
  [simp]: "int_dom_bool_unknown = int_dom_of_int 0 \<squnion> int_dom_of_int 1"

fun int_dom_of_bool_option :: "bool option => int_dom" where
  "int_dom_of_bool_option (Some True) = int_dom_of_int 1"
| "int_dom_of_bool_option (Some False) = int_dom_of_int 0"
| "int_dom_of_bool_option None = int_dom_bool_unknown"

lemma int_dom_of_bool_option_unfold [simp]:
  "int_dom_of_bool_option r = (if r = Some True then int_dom_of_int 1
                                else if r = Some False then int_dom_of_int 0
                                else int_dom_bool_unknown)"
  by (cases r rule: int_dom_of_bool_option.cases) simp_all

fun aval_int_dom ::
    "refine_mode => exp => (vname => int_dom) => int_dom"
where
  "aval_int_dom mode (N n) sigma = int_dom_of_int n"
| "aval_int_dom mode (V x) sigma = sigma x"
| "aval_int_dom mode (Plus e1 e2) sigma =
     plus_int_dom mode
       (aval_int_dom mode e1 sigma)
       (aval_int_dom mode e2 sigma)"
| "aval_int_dom mode (Minus e1 e2) sigma =
     minus_int_dom mode
       (aval_int_dom mode e1 sigma)
       (aval_int_dom mode e2 sigma)"
| "aval_int_dom mode (Times e1 e2) sigma =
     times_int_dom mode
       (aval_int_dom mode e1 sigma)
       (aval_int_dom mode e2 sigma)"
| "aval_int_dom mode (Less e1 e2) sigma =
     (let a = aval_int_dom mode e1 sigma; b = aval_int_dom mode e2 sigma
      in if is_empty a \<or> is_empty b then bot else int_dom_of_bool_option (int_dom_lt a b))"
| "aval_int_dom mode (exp.Eq e1 e2) sigma =
     (let a = aval_int_dom mode e1 sigma; b = aval_int_dom mode e2 sigma
      in if is_empty a \<or> is_empty b then bot else int_dom_of_bool_option (int_dom_eqb a b))"
| "aval_int_dom mode (exp.Not e) sigma =
     (let a = aval_int_dom mode e sigma
      in if is_empty a then bot
         else if int_dom_tobool a = Some True then int_dom_of_int 0
         else if int_dom_tobool a = Some False then int_dom_of_int 1
         else int_dom_bool_unknown)"
| "aval_int_dom mode (And e1 e2) sigma =
     (let a = aval_int_dom mode e1 sigma; b = aval_int_dom mode e2 sigma
      in if is_empty a \<or> is_empty b then bot
         else if int_dom_tobool a = Some False \<or> int_dom_tobool b = Some False
         then int_dom_of_int 0
         else if int_dom_tobool a = Some True \<and> int_dom_tobool b = Some True
         then int_dom_of_int 1
         else int_dom_bool_unknown)"
| "aval_int_dom mode (Or e1 e2) sigma =
     (let a = aval_int_dom mode e1 sigma; b = aval_int_dom mode e2 sigma
      in if is_empty a \<or> is_empty b then bot
         else if int_dom_tobool a = Some True \<or> int_dom_tobool b = Some True
         then int_dom_of_int 1
         else if int_dom_tobool a = Some False \<and> int_dom_tobool b = Some False
         then int_dom_of_int 0
         else int_dom_bool_unknown)"

lemma aval_int_dom_sound:
  assumes "\<forall>x. s x : gamma_int_dom (sigma x)"
  shows "aval e s : gamma_int_dom (aval_int_dom mode e sigma)"
  using assms
proof (induction e arbitrary: s sigma)
  case (Less e1 e2)
  have h1: "aval e1 s \<in> gamma_int_dom (aval_int_dom mode e1 sigma)" using Less.IH(1) Less.prems by simp
  have h2: "aval e2 s \<in> gamma_int_dom (aval_int_dom mode e2 sigma)" using Less.IH(2) Less.prems by simp
  have nb1: "\<not> is_empty (aval_int_dom mode e1 sigma)" using h1 by (auto simp: is_bottom_int_dom_correct)
  have nb2: "\<not> is_empty (aval_int_dom mode e2 sigma)" using h2 by (auto simp: is_bottom_int_dom_correct)
  show ?case
  proof (cases "int_dom_lt (aval_int_dom mode e1 sigma) (aval_int_dom mode e2 sigma) = Some True")
    case True
    with int_dom_lt_sound[OF True h1 h2] nb1 nb2 show ?thesis by simp
  next
    case False
    show ?thesis
    proof (cases "int_dom_lt (aval_int_dom mode e1 sigma) (aval_int_dom mode e2 sigma) = Some False")
      case True
      with int_dom_lt_sound[OF True h1 h2] nb1 nb2 False show ?thesis by simp
    next
      case False
      with \<open>\<not> (int_dom_lt (aval_int_dom mode e1 sigma) (aval_int_dom mode e2 sigma) = Some True)\<close>
        nb1 nb2
      show ?thesis
        by (auto intro: gamma_int_dom_sup_ub1[THEN subsetD] gamma_int_dom_sup_ub2[THEN subsetD])
    qed
  qed
next
  case (Eq e1 e2)
  have h1: "aval e1 s \<in> gamma_int_dom (aval_int_dom mode e1 sigma)" using Eq.IH(1) Eq.prems by simp
  have h2: "aval e2 s \<in> gamma_int_dom (aval_int_dom mode e2 sigma)" using Eq.IH(2) Eq.prems by simp
  have nb1: "\<not> is_empty (aval_int_dom mode e1 sigma)" using h1 by (auto simp: is_bottom_int_dom_correct)
  have nb2: "\<not> is_empty (aval_int_dom mode e2 sigma)" using h2 by (auto simp: is_bottom_int_dom_correct)
  show ?case
  proof (cases "int_dom_eqb (aval_int_dom mode e1 sigma) (aval_int_dom mode e2 sigma) = Some True")
    case True
    with int_dom_eqb_sound[OF True h1 h2] nb1 nb2 show ?thesis by simp
  next
    case False
    show ?thesis
    proof (cases "int_dom_eqb (aval_int_dom mode e1 sigma) (aval_int_dom mode e2 sigma) = Some False")
      case True
      with int_dom_eqb_sound[OF True h1 h2] nb1 nb2 False show ?thesis by simp
    next
      case False
      with \<open>\<not> (int_dom_eqb (aval_int_dom mode e1 sigma) (aval_int_dom mode e2 sigma) = Some True)\<close>
        nb1 nb2
      show ?thesis
        by (auto intro: gamma_int_dom_sup_ub1[THEN subsetD] gamma_int_dom_sup_ub2[THEN subsetD])
    qed
  qed
next
  case (Not e)
  have h: "aval e s \<in> gamma_int_dom (aval_int_dom mode e sigma)" using Not.IH Not.prems by simp
  have nb: "\<not> is_empty (aval_int_dom mode e sigma)" using h by (auto simp: is_bottom_int_dom_correct)
  show ?case
  proof (cases "int_dom_tobool (aval_int_dom mode e sigma) = Some True")
    case True
    with int_dom_tobool_sound[OF True h] nb show ?thesis by simp
  next
    case False
    show ?thesis
    proof (cases "int_dom_tobool (aval_int_dom mode e sigma) = Some False")
      case True
      with int_dom_tobool_sound[OF True h] nb False show ?thesis by simp
    next
      case False
      with \<open>\<not> (int_dom_tobool (aval_int_dom mode e sigma) = Some True)\<close> nb
      show ?thesis
        by (auto intro: gamma_int_dom_sup_ub1[THEN subsetD] gamma_int_dom_sup_ub2[THEN subsetD])
    qed
  qed
next
  case (And e1 e2)
  have h1: "aval e1 s \<in> gamma_int_dom (aval_int_dom mode e1 sigma)" using And.IH(1) And.prems by simp
  have h2: "aval e2 s \<in> gamma_int_dom (aval_int_dom mode e2 sigma)" using And.IH(2) And.prems by simp
  have nb1: "\<not> is_empty (aval_int_dom mode e1 sigma)" using h1 by (auto simp: is_bottom_int_dom_correct)
  have nb2: "\<not> is_empty (aval_int_dom mode e2 sigma)" using h2 by (auto simp: is_bottom_int_dom_correct)
  show ?case
  proof (cases "int_dom_tobool (aval_int_dom mode e1 sigma) = Some False
              \<or> int_dom_tobool (aval_int_dom mode e2 sigma) = Some False")
    case True
    then have "\<not> truthy (aval e1 s) \<or> \<not> truthy (aval e2 s)"
      using int_dom_tobool_sound h1 h2 by fastforce
    with True nb1 nb2 show ?thesis by (auto simp: truthy_def)
  next
    case False
    show ?thesis
    proof (cases "int_dom_tobool (aval_int_dom mode e1 sigma) = Some True
                \<and> int_dom_tobool (aval_int_dom mode e2 sigma) = Some True")
      case True
      then have "truthy (aval e1 s) \<and> truthy (aval e2 s)"
        using int_dom_tobool_sound h1 h2 by auto
      with True False nb1 nb2 show ?thesis by (simp add: truthy_def)
    next
      case False
      with \<open>\<not> (int_dom_tobool (aval_int_dom mode e1 sigma) = Some False
              \<or> int_dom_tobool (aval_int_dom mode e2 sigma) = Some False)\<close>
        nb1 nb2
      show ?thesis
        by (auto intro: gamma_int_dom_sup_ub1[THEN subsetD] gamma_int_dom_sup_ub2[THEN subsetD])
    qed
  qed
next
  case (Or e1 e2)
  have h1: "aval e1 s \<in> gamma_int_dom (aval_int_dom mode e1 sigma)" using Or.IH(1) Or.prems by simp
  have h2: "aval e2 s \<in> gamma_int_dom (aval_int_dom mode e2 sigma)" using Or.IH(2) Or.prems by simp
  have nb1: "\<not> is_empty (aval_int_dom mode e1 sigma)" using h1 by (auto simp: is_bottom_int_dom_correct)
  have nb2: "\<not> is_empty (aval_int_dom mode e2 sigma)" using h2 by (auto simp: is_bottom_int_dom_correct)
  show ?case
  proof (cases "int_dom_tobool (aval_int_dom mode e1 sigma) = Some True
              \<or> int_dom_tobool (aval_int_dom mode e2 sigma) = Some True")
    case True
    then have "truthy (aval e1 s) \<or> truthy (aval e2 s)"
      using int_dom_tobool_sound h1 h2 by fastforce
    with True nb1 nb2 show ?thesis by (auto simp: truthy_def)
  next
    case False
    show ?thesis
    proof (cases "int_dom_tobool (aval_int_dom mode e1 sigma) = Some False
                \<and> int_dom_tobool (aval_int_dom mode e2 sigma) = Some False")
      case True
      then have "\<not> truthy (aval e1 s) \<and> \<not> truthy (aval e2 s)"
        using int_dom_tobool_sound h1 h2 by auto
      with True False nb1 nb2 show ?thesis by (simp add: truthy_def)
    next
      case False
      with \<open>\<not> (int_dom_tobool (aval_int_dom mode e1 sigma) = Some True
              \<or> int_dom_tobool (aval_int_dom mode e2 sigma) = Some True)\<close>
        nb1 nb2
      show ?thesis
        by (auto intro: gamma_int_dom_sup_ub1[THEN subsetD] gamma_int_dom_sup_ub2[THEN subsetD])
    qed
  qed
qed (auto intro: plus_int_dom_sound minus_int_dom_sound times_int_dom_sound)

lemma aval_int_dom_mono:
  assumes "mode ~= Refine_Fixpoint"
      and "sigma1 <= sigma2"
  shows "aval_int_dom mode e sigma1 <= aval_int_dom mode e sigma2"
  using assms
proof (induction e)
  case (Less e1 e2)
  have p_mono: "aval_int_dom mode e1 sigma1 \<le> aval_int_dom mode e1 sigma2"
    using Less.IH(1) Less.prems by simp
  have q_mono: "aval_int_dom mode e2 sigma1 \<le> aval_int_dom mode e2 sigma2"
    using Less.IH(2) Less.prems by simp
  show ?case
  proof (cases "is_empty (aval_int_dom mode e1 sigma1) \<or> is_empty (aval_int_dom mode e2 sigma1)")
    case True
    then show ?thesis by (simp add: bot_least)
  next
    case False
    then have nb1: "\<not> is_empty (aval_int_dom mode e1 sigma1)"
      and nb2: "\<not> is_empty (aval_int_dom mode e2 sigma1)" by auto
    have nb1': "\<not> is_empty (aval_int_dom mode e1 sigma2)" using nb1 p_mono is_empty_antimono by blast
    have nb2': "\<not> is_empty (aval_int_dom mode e2 sigma2)" using nb2 q_mono is_empty_antimono by blast
    show ?thesis
    proof (cases "int_dom_lt (aval_int_dom mode e1 sigma2) (aval_int_dom mode e2 sigma2)")
      case (Some b)
      then have "int_dom_lt (aval_int_dom mode e1 sigma1) (aval_int_dom mode e2 sigma1) = Some b"
        using int_dom_lt_mono[OF nb1 nb2 p_mono q_mono] by simp
      then show ?thesis using Some nb1 nb2 nb1' nb2' by (cases b) simp_all
    next
      case None
      then show ?thesis using nb1 nb2 nb1' nb2' sup_ge1 sup_ge2
        by (cases "int_dom_lt (aval_int_dom mode e1 sigma1) (aval_int_dom mode e2 sigma1) = Some True";
            cases "int_dom_lt (aval_int_dom mode e1 sigma1) (aval_int_dom mode e2 sigma1) = Some False")
           auto
    qed
  qed
next
  case (Eq e1 e2)
  have p_mono: "aval_int_dom mode e1 sigma1 \<le> aval_int_dom mode e1 sigma2"
    using Eq.IH(1) Eq.prems by simp
  have q_mono: "aval_int_dom mode e2 sigma1 \<le> aval_int_dom mode e2 sigma2"
    using Eq.IH(2) Eq.prems by simp
  show ?case
  proof (cases "is_empty (aval_int_dom mode e1 sigma1) \<or> is_empty (aval_int_dom mode e2 sigma1)")
    case True
    then show ?thesis by (simp add: bot_least)
  next
    case False
    then have nb1: "\<not> is_empty (aval_int_dom mode e1 sigma1)"
      and nb2: "\<not> is_empty (aval_int_dom mode e2 sigma1)" by auto
    have nb1': "\<not> is_empty (aval_int_dom mode e1 sigma2)" using nb1 p_mono is_empty_antimono by blast
    have nb2': "\<not> is_empty (aval_int_dom mode e2 sigma2)" using nb2 q_mono is_empty_antimono by blast
    show ?thesis
    proof (cases "int_dom_eqb (aval_int_dom mode e1 sigma2) (aval_int_dom mode e2 sigma2)")
      case (Some b)
      then have "int_dom_eqb (aval_int_dom mode e1 sigma1) (aval_int_dom mode e2 sigma1) = Some b"
        using int_dom_eqb_mono[OF nb1 nb2 p_mono q_mono] by simp
      then show ?thesis using Some nb1 nb2 nb1' nb2' by (cases b) simp_all
    next
      case None
      then show ?thesis using nb1 nb2 nb1' nb2' sup_ge1 sup_ge2
        by (cases "int_dom_eqb (aval_int_dom mode e1 sigma1) (aval_int_dom mode e2 sigma1) = Some True";
            cases "int_dom_eqb (aval_int_dom mode e1 sigma1) (aval_int_dom mode e2 sigma1) = Some False")
           auto
    qed
  qed
next
  case (Not e)
  have p_mono: "aval_int_dom mode e sigma1 \<le> aval_int_dom mode e sigma2"
    using Not.IH Not.prems by simp
  show ?case
  proof (cases "is_empty (aval_int_dom mode e sigma1)")
    case True
    then show ?thesis by (simp add: bot_least)
  next
    case False
    then have nb: "\<not> is_empty (aval_int_dom mode e sigma1)" by auto
    have nb': "\<not> is_empty (aval_int_dom mode e sigma2)" using nb p_mono is_empty_antimono by blast
    show ?thesis
    proof (cases "int_dom_tobool (aval_int_dom mode e sigma2)")
      case (Some b)
      then have "int_dom_tobool (aval_int_dom mode e sigma1) = Some b"
        using int_dom_tobool_mono[OF nb p_mono] by simp
      then show ?thesis using Some nb nb' by (cases b) simp_all
    next
      case None
      then show ?thesis using nb nb' sup_ge1 sup_ge2
        by (cases "int_dom_tobool (aval_int_dom mode e sigma1) = Some True";
            cases "int_dom_tobool (aval_int_dom mode e sigma1) = Some False") auto
    qed
  qed
next
  case (And e1 e2)
  have p_mono: "aval_int_dom mode e1 sigma1 \<le> aval_int_dom mode e1 sigma2"
    using And.IH(1) And.prems by simp
  have q_mono: "aval_int_dom mode e2 sigma1 \<le> aval_int_dom mode e2 sigma2"
    using And.IH(2) And.prems by simp
  show ?case
  proof (cases "is_empty (aval_int_dom mode e1 sigma1) \<or> is_empty (aval_int_dom mode e2 sigma1)")
    case True
    then show ?thesis by (simp add: bot_least)
  next
    case False
    then have nb1: "\<not> is_empty (aval_int_dom mode e1 sigma1)"
      and nb2: "\<not> is_empty (aval_int_dom mode e2 sigma1)" by auto
    have nb1': "\<not> is_empty (aval_int_dom mode e1 sigma2)" using nb1 p_mono is_empty_antimono by blast
    have nb2': "\<not> is_empty (aval_int_dom mode e2 sigma2)" using nb2 q_mono is_empty_antimono by blast
    show ?thesis
    proof (cases "int_dom_tobool (aval_int_dom mode e1 sigma2) = Some False
                \<or> int_dom_tobool (aval_int_dom mode e2 sigma2) = Some False")
      case True
      then have "int_dom_tobool (aval_int_dom mode e1 sigma1) = Some False
               \<or> int_dom_tobool (aval_int_dom mode e2 sigma1) = Some False"
        using int_dom_tobool_mono[OF nb1 p_mono] int_dom_tobool_mono[OF nb2 q_mono] by auto
      with True nb1 nb2 nb1' nb2' show ?thesis by simp
    next
      case False
      show ?thesis
      proof (cases "int_dom_tobool (aval_int_dom mode e1 sigma2) = Some True
                  \<and> int_dom_tobool (aval_int_dom mode e2 sigma2) = Some True")
        case True
        then have "int_dom_tobool (aval_int_dom mode e1 sigma1) = Some True"
          and "int_dom_tobool (aval_int_dom mode e2 sigma1) = Some True"
          using int_dom_tobool_mono[OF nb1 p_mono] int_dom_tobool_mono[OF nb2 q_mono] by auto
        with True False nb1 nb2 nb1' nb2' show ?thesis by simp
      next
        case False
        with \<open>\<not> (int_dom_tobool (aval_int_dom mode e1 sigma2) = Some False
                \<or> int_dom_tobool (aval_int_dom mode e2 sigma2) = Some False)\<close>
          nb1 nb2 nb1' nb2' sup_ge1 sup_ge2
        show ?thesis
          by (cases "int_dom_tobool (aval_int_dom mode e1 sigma1) = Some False
                   \<or> int_dom_tobool (aval_int_dom mode e2 sigma1) = Some False";
              cases "int_dom_tobool (aval_int_dom mode e1 sigma1) = Some True
                   \<and> int_dom_tobool (aval_int_dom mode e2 sigma1) = Some True") auto
      qed
    qed
  qed
next
  case (Or e1 e2)
  have p_mono: "aval_int_dom mode e1 sigma1 \<le> aval_int_dom mode e1 sigma2"
    using Or.IH(1) Or.prems by simp
  have q_mono: "aval_int_dom mode e2 sigma1 \<le> aval_int_dom mode e2 sigma2"
    using Or.IH(2) Or.prems by simp
  show ?case
  proof (cases "is_empty (aval_int_dom mode e1 sigma1) \<or> is_empty (aval_int_dom mode e2 sigma1)")
    case True
    then show ?thesis by (simp add: bot_least)
  next
    case False
    then have nb1: "\<not> is_empty (aval_int_dom mode e1 sigma1)"
      and nb2: "\<not> is_empty (aval_int_dom mode e2 sigma1)" by auto
    have nb1': "\<not> is_empty (aval_int_dom mode e1 sigma2)" using nb1 p_mono is_empty_antimono by blast
    have nb2': "\<not> is_empty (aval_int_dom mode e2 sigma2)" using nb2 q_mono is_empty_antimono by blast
    show ?thesis
    proof (cases "int_dom_tobool (aval_int_dom mode e1 sigma2) = Some True
                \<or> int_dom_tobool (aval_int_dom mode e2 sigma2) = Some True")
      case True
      then have "int_dom_tobool (aval_int_dom mode e1 sigma1) = Some True
               \<or> int_dom_tobool (aval_int_dom mode e2 sigma1) = Some True"
        using int_dom_tobool_mono[OF nb1 p_mono] int_dom_tobool_mono[OF nb2 q_mono] by auto
      with True nb1 nb2 nb1' nb2' show ?thesis by simp
    next
      case False
      show ?thesis
      proof (cases "int_dom_tobool (aval_int_dom mode e1 sigma2) = Some False
                  \<and> int_dom_tobool (aval_int_dom mode e2 sigma2) = Some False")
        case True
        then have "int_dom_tobool (aval_int_dom mode e1 sigma1) = Some False"
          and "int_dom_tobool (aval_int_dom mode e2 sigma1) = Some False"
          using int_dom_tobool_mono[OF nb1 p_mono] int_dom_tobool_mono[OF nb2 q_mono] by auto
        with True False nb1 nb2 nb1' nb2' show ?thesis by simp
      next
        case False
        with \<open>\<not> (int_dom_tobool (aval_int_dom mode e1 sigma2) = Some True
                \<or> int_dom_tobool (aval_int_dom mode e2 sigma2) = Some True)\<close>
          nb1 nb2 nb1' nb2' sup_ge1 sup_ge2
        show ?thesis
          by (cases "int_dom_tobool (aval_int_dom mode e1 sigma1) = Some True
                   \<or> int_dom_tobool (aval_int_dom mode e2 sigma1) = Some True";
              cases "int_dom_tobool (aval_int_dom mode e1 sigma1) = Some False
                   \<and> int_dom_tobool (aval_int_dom mode e2 sigma1) = Some False") auto
      qed
    qed
  qed
qed (auto simp: le_funD intro: plus_int_dom_mono minus_int_dom_mono times_int_dom_mono)

end
