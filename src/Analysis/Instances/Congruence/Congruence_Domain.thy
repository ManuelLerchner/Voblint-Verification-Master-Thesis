theory Congruence_Domain
  imports Voblint_Core.Abstract_Domain
begin

section \<open>Normalized congruence carrier\<close>

text \<open>
  The representation follows Goblint's congruence domain: bottom is @{term None}
  and @{term "Some (c, m)"} denotes the class of integers congruent to @{term c}
  modulo @{term m}. Modulus zero denotes the singleton @{term "{c}"}.

  Isabelle's order laws quantify over every carrier value, so the public type is
  the subtype of normalized representations. Public construction applies the
  same normalization discipline as Goblint: a nonzero modulus becomes positive
  and its residue lies in the half-open range from zero to the modulus.
\<close>

type_synonym congruence_rep = "(int * int) option"

fun normalized_congruence_rep :: "congruence_rep => bool" where
  "normalized_congruence_rep None = True"
| "normalized_congruence_rep (Some (c, m)) =
     (m = 0 \<or> (0 <= c \<and> c < m))"

fun normalize_congruence_rep :: "congruence_rep => congruence_rep" where
  "normalize_congruence_rep None = None"
| "normalize_congruence_rep (Some (c, m)) =
     (if m = 0 then Some (c, 0)
      else
        let p = abs m;
            r = c mod p
        in Some (r, p))"

lemma normalized_normalize_congruence_rep [simp]:
  "normalized_congruence_rep (normalize_congruence_rep x)"
proof (cases x)
  case None
  then show ?thesis by simp
next
  case (Some p)
  obtain c m where p: "p = (c, m)"
    by (cases p)
  show ?thesis
  proof (cases "m = 0")
    case True
    then show ?thesis unfolding Some p by simp
  next
    case False
    then have positive: "0 < abs m" by simp
    have nonnegative: "0 <= c mod abs m"
      using positive by simp
    have less: "c mod abs m < abs m"
      by (rule pos_mod_bound[OF positive])
    show ?thesis
      unfolding Some p
      using False nonnegative less
      by (simp add: Let_def)
  qed
qed

lemma normalize_congruence_rep_fixed:
  assumes "normalized_congruence_rep x"
  shows "normalize_congruence_rep x = x"
proof (cases x)
  case None
  then show ?thesis by simp
next
  case (Some p)
  obtain c m where p: "p = (c, m)"
    by (cases p)
  show ?thesis
  proof (cases "m = 0")
    case True
    then show ?thesis unfolding Some p by simp
  next
    case False
    with assms have bounds: "0 <= c" "c < m"
      unfolding Some p by simp_all
    then have positive: "0 < m" by linarith
    have "c mod m = c"
      by (rule mod_pos_pos_trivial[OF bounds])
    with positive False show ?thesis
      unfolding Some p by (simp add: Let_def abs_of_pos)
  qed
qed

lemma normalize_congruence_rep_idem [simp]:
  "normalize_congruence_rep (normalize_congruence_rep x) =
   normalize_congruence_rep x"
  by (rule normalize_congruence_rep_fixed) simp

lemma normalized_congruence_rep_modulus_nonnegative:
  assumes "normalized_congruence_rep (Some (c, m))"
  shows "0 <= m"
  using assms by auto

lemma normalized_congruence_rep_nonzero:
  assumes "normalized_congruence_rep (Some (c, m))"
      and "m \<noteq> 0"
  shows "0 <= c" and "c < m" and "0 < m"
  using assms by auto
typedef congruence =
  "{x :: congruence_rep. normalized_congruence_rep x}"
  morphisms Rep_congruence Abs_congruence
  by (rule exI[of _ None]) simp

setup_lifting type_definition_congruence

instantiation congruence :: equal
begin

definition equal_congruence :: "congruence => congruence => bool" where
  "equal_congruence a b = (Rep_congruence a = Rep_congruence b)"

instance
proof
  fix a b :: congruence
  show "HOL.equal a b \<longleftrightarrow> a = b"
    unfolding equal_congruence_def
    by (simp only: Rep_congruence_inject)
qed

end

lift_definition mk_congruence :: "int => int => congruence"
  is "\<lambda>c m. normalize_congruence_rep (Some (c, m))"
  by (rule normalized_normalize_congruence_rep)

lift_definition bottom_congruence :: congruence
  is None
  by simp

lemma Rep_mk_congruence [simp]:
  "Rep_congruence (mk_congruence c m) =
   normalize_congruence_rep (Some (c, m))"
  by (rule mk_congruence.rep_eq)

lemma Rep_bottom_congruence [simp]:
  "Rep_congruence bottom_congruence = None"
  by (rule bottom_congruence.rep_eq)

lemma congruence_cases [cases type: congruence]:
  obtains "a = bottom_congruence"
    | c m where "a = mk_congruence c m"
proof (cases "Rep_congruence a")
  case None
  have "Rep_congruence a = Rep_congruence bottom_congruence"
    using None by simp
  then have "a = bottom_congruence"
    by (simp only: Rep_congruence_inject)
  then show thesis by (rule that)
next
  case (Some p)
  obtain c m where p: "p = (c, m)"
    by (cases p)
  have normalized: "normalized_congruence_rep (Some (c, m))"
    using Rep_congruence[of a] unfolding Some p by simp
  then have fixed:
    "normalize_congruence_rep (Some (c, m)) = Some (c, m)"
    by (rule normalize_congruence_rep_fixed)
  have reps: "Rep_congruence a = Rep_congruence (mk_congruence c m)"
  proof -
    have "Rep_congruence a = Some (c, m)"
      using Some p by simp
    also have "... = Rep_congruence (mk_congruence c m)"
      using fixed by simp
    finally show ?thesis .
  qed
  then have "a = mk_congruence c m"
    by (simp only: Rep_congruence_inject)
  then show thesis by (rule that)
qed

fun gamma_congruence_rep :: "congruence_rep => int set" where
  "gamma_congruence_rep None = {}"
| "gamma_congruence_rep (Some (c, m)) = {n. m dvd n - c}"

definition gamma_congruence :: "congruence => int set" where
  "gamma_congruence a = gamma_congruence_rep (Rep_congruence a)"

lemma congruence_class_subset_iff:
  fixes m1 m2 c1 c2 :: int
  shows
    "{n. m1 dvd n - c1} \<subseteq> {n. m2 dvd n - c2} \<longleftrightarrow>
     m2 dvd m1 \<and> m2 dvd c1 - c2"
proof
  assume subset:
    "{n. m1 dvd n - c1} \<subseteq> {n. m2 dvd n - c2}"
  have offset: "m2 dvd c1 - c2"
    using subsetD[OF subset, of c1] by simp
  have shifted: "m2 dvd (c1 + m1) - c2"
    using subsetD[OF subset, of "c1 + m1"] by simp
  have "m2 dvd ((c1 + m1) - c2) - (c1 - c2)"
    by (rule dvd_diff[OF shifted offset])
  then have "m2 dvd m1" by simp
  with offset show "m2 dvd m1 \<and> m2 dvd c1 - c2" by blast
next
  assume divisibility: "m2 dvd m1 \<and> m2 dvd c1 - c2"
  show "{n. m1 dvd n - c1} \<subseteq> {n. m2 dvd n - c2}"
  proof
    fix n
    assume "n \<in> {n. m1 dvd n - c1}"
    then have n: "m1 dvd n - c1" by simp
    have first: "m2 dvd n - c1"
      by (rule dvd_trans[OF divisibility[THEN conjunct1] n])
    have "m2 dvd (n - c1) + (c1 - c2)"
      by (rule dvd_add[OF first divisibility[THEN conjunct2]])
    then show "n \<in> {n. m2 dvd n - c2}" by simp
  qed
qed

lemma gamma_normalize_congruence_rep [simp]:
  "gamma_congruence_rep (normalize_congruence_rep x) =
   gamma_congruence_rep x"
proof (cases x)
  case None
  then show ?thesis by simp
next
  case (Some p)
  obtain c m where p: "p = (c, m)"
    by (cases p)
  show ?thesis
  proof (cases "m = 0")
    case True
    then show ?thesis unfolding Some p by simp
  next
    case False
    let ?modulus = "abs m"
    let ?residue = "c mod ?modulus"
    have modulus1: "m dvd ?modulus" by simp
    have modulus2: "?modulus dvd m" by simp
    have offset2: "?modulus dvd c - ?residue"
      by (rule dvd_minus_mod)
    have offset1: "m dvd c - ?residue"
      using offset2 by (simp only: abs_dvd_iff)
    have negated_offset: "m dvd -(c - ?residue)"
      using offset1 by (simp only: dvd_minus_iff)
    have offset1_reverse: "m dvd ?residue - c"
      using negated_offset by simp
    have classes:
      "{n. ?modulus dvd n - ?residue} = {n. m dvd n - c}"
    proof (rule Set.subset_antisym)
      show "{n. ?modulus dvd n - ?residue} \<subseteq>
        {n. m dvd n - c}"
        unfolding congruence_class_subset_iff
        using modulus1 offset1_reverse by blast
      show "{n. m dvd n - c} \<subseteq>
        {n. ?modulus dvd n - ?residue}"
        unfolding congruence_class_subset_iff
        using modulus2 offset2 by blast
    qed
    show ?thesis
      unfolding Some p
      using False classes by (simp add: Let_def)
  qed
qed

lemma gamma_congruence_rep_inject:
  assumes normalized_x: "normalized_congruence_rep x"
      and normalized_y: "normalized_congruence_rep y"
      and gamma_eq: "gamma_congruence_rep x = gamma_congruence_rep y"
  shows "x = y"
proof (cases x)
  case None
  show ?thesis
  proof (cases y)
    case None
    with `x = None` show ?thesis by simp
  next
    case (Some p)
    obtain c m where p: "p = (c, m)"
      by (cases p)
    have "c \<in> gamma_congruence_rep y"
      unfolding Some p by simp
    moreover have "gamma_congruence_rep y = {}"
      using gamma_eq `x = None` by simp
    ultimately show ?thesis by simp
  qed
next
  case (Some p1)
  obtain c1 m1 where p1: "p1 = (c1, m1)"
    by (cases p1)
  show ?thesis
  proof (cases y)
    case None
    have "c1 \<in> gamma_congruence_rep x"
      unfolding Some p1 by simp
    moreover have "gamma_congruence_rep x = {}"
      using gamma_eq None by simp
    ultimately show ?thesis by simp
  next
    case (Some p2)
    obtain c2 m2 where p2: "p2 = (c2, m2)"
      by (cases p2)
    have subset12:
      "{n. m1 dvd n - c1} \<subseteq> {n. m2 dvd n - c2}"
      using gamma_eq unfolding `x = Some p1` Some p1 p2 by auto
    have subset21:
      "{n. m2 dvd n - c2} \<subseteq> {n. m1 dvd n - c1}"
      using gamma_eq unfolding `x = Some p1` Some p1 p2 by auto
    have divisibility12: "m2 dvd m1 \<and> m2 dvd c1 - c2"
      using subset12 unfolding congruence_class_subset_iff .
    have divisibility21: "m1 dvd m2 \<and> m1 dvd c2 - c1"
      using subset21 unfolding congruence_class_subset_iff .
    have nonnegative1: "0 <= m1"
      using normalized_x unfolding `x = Some p1` p1
      by (rule normalized_congruence_rep_modulus_nonnegative)
    have nonnegative2: "0 <= m2"
      using normalized_y unfolding Some p2
      by (rule normalized_congruence_rep_modulus_nonnegative)
    have moduli: "m1 = m2"
      by (rule Int.zdvd_antisym_nonneg[OF nonnegative1 nonnegative2
            divisibility21[THEN conjunct1] divisibility12[THEN conjunct1]])
    have residues: "c1 = c2"
    proof (cases "m1 = 0")
      case True
      with moduli divisibility12 show ?thesis by simp
    next
      case False
      have bounds1: "0 <= c1" "c1 < m1" "0 < m1"
        using normalized_x False unfolding `x = Some p1` p1
        by (rule normalized_congruence_rep_nonzero)+
      have bounds2: "0 <= c2" "c2 < m1"
        using normalized_y False moduli unfolding Some p2
        by auto
      have mod_eq: "c1 mod m1 = c2 mod m1"
        using divisibility12 moduli
        by (simp only: Euclidean_Rings.euclidean_ring_cancel_class.mod_eq_dvd_iff)
      have left: "c1 mod m1 = c1"
        by (rule mod_pos_pos_trivial[OF bounds1(1) bounds1(2)])
      have right: "c2 mod m1 = c2"
        by (rule mod_pos_pos_trivial[OF bounds2])
      show ?thesis using mod_eq left right by simp
    qed
    show ?thesis
      unfolding `x = Some p1` Some p1 p2 moduli residues by simp
  qed
qed

lemma gamma_mk_congruence [simp]:
  "gamma_congruence (mk_congruence c m) = {n. m dvd n - c}"
  unfolding gamma_congruence_def
  by (simp only: Rep_mk_congruence gamma_normalize_congruence_rep
      gamma_congruence_rep.simps)

lemma mk_congruence_member [simp]:
  "c \<in> gamma_congruence (mk_congruence c m)"
  by simp

lemma gamma_bottom_congruence [simp]:
  "gamma_congruence bottom_congruence = {}"
  unfolding gamma_congruence_def by simp

lemma gamma_congruence_empty_iff [simp]:
  "gamma_congruence a = {} \<longleftrightarrow> a = bottom_congruence"
proof (cases "Rep_congruence a")
  case None
  have "Rep_congruence a = Rep_congruence bottom_congruence"
    using None by simp
  then have "a = bottom_congruence"
    by (simp only: Rep_congruence_inject)
  with None show ?thesis
    unfolding gamma_congruence_def by simp
next
  case (Some p)
  obtain c m where p: "p = (c, m)"
    by (cases p)
  have member: "c \<in> gamma_congruence a"
    unfolding gamma_congruence_def Some p by simp
  have "a \<noteq> bottom_congruence"
  proof
    assume "a = bottom_congruence"
    with Some show False by simp
  qed
  with member show ?thesis by blast
qed

lemma gamma_congruence_inject:
  assumes "gamma_congruence a = gamma_congruence b"
  shows "a = b"
proof -
  have reps: "Rep_congruence a = Rep_congruence b"
  proof (rule gamma_congruence_rep_inject)
    show "normalized_congruence_rep (Rep_congruence a)"
      using Rep_congruence[of a] by simp
    show "normalized_congruence_rep (Rep_congruence b)"
      using Rep_congruence[of b] by simp
    show "gamma_congruence_rep (Rep_congruence a) =
      gamma_congruence_rep (Rep_congruence b)"
      using assms unfolding gamma_congruence_def .
  qed
  from reps show ?thesis
    by (simp only: Rep_congruence_inject)
qed

lemma mk_congruence_normalized:
  assumes "m = 0 \<or> (0 <= c \<and> c < m)"
  shows "Rep_congruence (mk_congruence c m) = Some (c, m)"
proof -
  from assms have normalized:
    "normalized_congruence_rep (Some (c, m))"
    by simp
  then have fixed:
    "normalize_congruence_rep (Some (c, m)) = Some (c, m)"
    by (rule normalize_congruence_rep_fixed)
  then show ?thesis by simp
qed

lemma mk_congruence_negative_modulus [simp]:
  "mk_congruence 5 (-4) = mk_congruence 1 4"
  by (rule Rep_congruence_inject[THEN iffD1])
     (simp add: Let_def)

lemma mk_congruence_constant_distinct:
  "mk_congruence c 0 = mk_congruence d 0 \<longleftrightarrow> c = d"
  by (simp add: Rep_congruence_inject[symmetric])

end
