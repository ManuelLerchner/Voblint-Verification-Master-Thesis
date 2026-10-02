theory Congruence_Lattice
  imports "Voblint_Domain.Abstract_Domain" "HOL-Computational_Algebra.Euclidean_Algorithm"
begin

section \<open>Congruence lattice\<close>

text \<open>
  Goblint's congruence domain as a normalized subtype of \<open>(int * int) option\<close>,
  with concretization \<open>gamma_congruence\<close>, the lattice order, join
  and the executable tests the \<open>numeric_domain\<close> instance needs.
\<close>

subsection \<open>Carrier and concretization\<close>

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

lemma normalized_Rep_congruence [simp]:
  "normalized_congruence_rep (Rep_congruence a)"
  using Rep_congruence[of a] by simp

lemma congruence_rep_cases [case_names Bot Class]:
  obtains (Bot) "Rep_congruence a = None"
    | (Class) c m where "Rep_congruence a = Some (c, m)"
proof (cases "Rep_congruence a")
  case (Some p)
  then show thesis by (cases p) (auto intro: Class)
qed (rule Bot)
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

declare mk_congruence.rep_eq [simp] bottom_congruence.rep_eq [simp]

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
    using normalized_Rep_congruence[of a] unfolding Some p by simp
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
  by (simp only: mk_congruence.rep_eq gamma_normalize_congruence_rep
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
      by simp
    show "normalized_congruence_rep (Rep_congruence b)"
      by simp
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


definition congruence_of_int :: "int => congruence" where
  "congruence_of_int n = mk_congruence n 0"

lemma congruence_of_int_gamma [simp]:
  "n \<in> gamma_congruence (congruence_of_int n)"
  unfolding congruence_of_int_def by simp

subsection \<open>Order\<close>

text \<open>
  A congruence value denotes a set of integers: \<open>None\<close> denotes none at all and
  \<open>Some (c, m)\<close> the numbers congruent to \<open>c\<close> modulo \<open>m\<close>, with \<open>m = 0\<close> meaning
  the single number \<open>c\<close>. Containment between two such sets is decidable
  arithmetic: \<open>Some (c1, m1)\<close> sits inside \<open>Some (c2, m2)\<close> exactly when the
  coarser modulus \<open>m2\<close> divides both \<open>m1\<close> and the offset \<open>c1 - c2\<close>. That test is
  \<open>congruence_le_rep\<close> just below, and it is what everything else here is
  built on.

  From it come the order instance on the normalized type \<open>congruence\<close>, its
  bottom (the empty class) and top (every integer, \<open>Some (0, 1)\<close>), the join ---
  the coarsest class containing both arguments, computed through the gcd of the
  moduli and the difference of the residues --- and the executable emptiness and
  printing operations the abstract-domain interface asks for.
\<close>

fun congruence_le_rep :: "congruence_rep => congruence_rep => bool" where
  "congruence_le_rep None _ = True"
| "congruence_le_rep (Some _) None = False"
| "congruence_le_rep (Some (c1, m1)) (Some (c2, m2)) =
     (m2 dvd m1 \<and> m2 dvd c1 - c2)"

lemma congruence_le_rep_iff:
  "congruence_le_rep x y \<longleftrightarrow>
   gamma_congruence_rep x \<subseteq> gamma_congruence_rep y"
proof (cases x)
  case None
  then show ?thesis by simp
next
  case (Some p1)
  obtain c1 m1 where p1: "p1 = (c1, m1)"
    by (cases p1)
  have x_rep: "x = Some (c1, m1)"
    using Some p1 by simp
  show ?thesis
  proof (cases y)
    case None
    have member: "c1 \<in> gamma_congruence_rep x"
      unfolding x_rep by simp
    have not_subset:
      "\<not> gamma_congruence_rep x \<subseteq> gamma_congruence_rep y"
    proof
      assume subset: "gamma_congruence_rep x \<subseteq> gamma_congruence_rep y"
      have "c1 \<in> gamma_congruence_rep y"
        by (rule subsetD[OF subset member])
      with None show False by simp
    qed
    with None show ?thesis unfolding x_rep by simp
  next
    case (Some p2)
    obtain c2 m2 where p2: "p2 = (c2, m2)"
      by (cases p2)
    have y_rep: "y = Some (c2, m2)"
      using Some p2 by simp
    show ?thesis
      unfolding x_rep y_rep
      by (simp only: congruence_le_rep.simps gamma_congruence_rep.simps
          congruence_class_subset_iff)
  qed
qed

definition congruence_le :: "congruence => congruence => bool" where
  "congruence_le a b =
     congruence_le_rep (Rep_congruence a) (Rep_congruence b)"

lemma congruence_le_iff_gamma:
  "congruence_le a b \<longleftrightarrow>
   gamma_congruence a \<subseteq> gamma_congruence b"
  unfolding congruence_le_def gamma_congruence_def
  by (rule congruence_le_rep_iff)

instantiation congruence :: ord
begin

definition less_eq_congruence :: "congruence => congruence => bool" where
  "(a :: congruence) <= b = congruence_le a b"

definition less_congruence :: "congruence => congruence => bool" where
  "(a :: congruence) < b = (a <= b \<and> \<not> b <= a)"

instance ..

end

lemma less_eq_congruence_iff_gamma:
  "a \<le> b \<longleftrightarrow> gamma_congruence a \<subseteq> gamma_congruence b"
  for a b :: congruence
  unfolding less_eq_congruence_def by (rule congruence_le_iff_gamma)

instance congruence :: order
proof intro_classes
  fix a b c :: congruence
  show "(a < b) = (a <= b \<and> \<not> b <= a)"
    unfolding less_congruence_def ..
  show "a <= a"
    unfolding less_eq_congruence_iff_gamma by simp
  assume ab: "a <= b" and bc: "b <= c"
  show "a <= c"
    using ab bc
    unfolding less_eq_congruence_iff_gamma
    by blast
next
  fix a b :: congruence
  assume ab: "a <= b" and ba: "b <= a"
  have gamma_eq: "gamma_congruence a = gamma_congruence b"
    using ab ba
    unfolding less_eq_congruence_iff_gamma
    by blast
  show "a = b"
    by (rule gamma_congruence_inject[OF gamma_eq])
qed

instantiation congruence :: bot
begin

definition bot_congruence :: congruence where
  "bot_congruence = bottom_congruence"

instance ..

end

instance congruence :: order_bot
proof intro_classes
  fix a :: congruence
  show "bot <= a"
    unfolding less_eq_congruence_iff_gamma bot_congruence_def
    by simp
qed

instantiation congruence :: top
begin

definition top_congruence :: congruence where
  "top_congruence = mk_congruence 0 1"

instance ..

end

lemma gamma_top_congruence [simp]:
  "gamma_congruence (top :: congruence) = UNIV"
  unfolding top_congruence_def by auto

lemma mk_congruence_mod_one [simp]:
  "mk_congruence c 1 = (top :: congruence)"
proof (rule gamma_congruence_inject)
  show "gamma_congruence (mk_congruence c 1) =
    gamma_congruence (top :: congruence)"
    by auto
qed

instance congruence :: order_top
proof intro_classes
  fix a :: congruence
  show "a <= top"
    unfolding less_eq_congruence_iff_gamma
    by simp
qed


subsection \<open>Join\<close>

text \<open>
  Two classes join to the class modulo the gcd of both moduli and the residue
  difference, renormalized. The lemmas show the join is an upper bound in
  \<open>gamma_congruence\<close> and the least one in the order.
\<close>

fun join_congruence_rep :: "congruence_rep => congruence_rep => congruence_rep" where
  "join_congruence_rep None y = y"
| "join_congruence_rep x None = x"
| "join_congruence_rep (Some (c1, m1)) (Some (c2, m2)) =
     Some (c1, gcd m1 (gcd m2 (c1 - c2)))"

lift_definition join_congruence :: "congruence => congruence => congruence"
  is "\<lambda>x y. normalize_congruence_rep (join_congruence_rep x y)"
  by (rule normalized_normalize_congruence_rep)

declare join_congruence.rep_eq [simp]

lemma gamma_join_congruence [simp]:
  "gamma_congruence (join_congruence a b) =
   gamma_congruence_rep
     (join_congruence_rep (Rep_congruence a) (Rep_congruence b))"
  unfolding gamma_congruence_def by simp

lemma gamma_join_congruence_rep_ub1:
  "gamma_congruence_rep x \<subseteq>
   gamma_congruence_rep (join_congruence_rep x y)"
proof (cases x)
  case None
  then show ?thesis by simp
next
  case (Some p1)
  obtain c1 m1 where p1: "p1 = (c1, m1)"
    by (cases p1)
  have x_rep: "x = Some (c1, m1)"
    using Some p1 by simp
  show ?thesis
  proof (cases y)
    case None
    with x_rep show ?thesis by simp
  next
    case (Some p2)
    obtain c2 m2 where p2: "p2 = (c2, m2)"
      by (cases p2)
    have y_rep: "y = Some (c2, m2)"
      using Some p2 by simp
    have modulus:
      "gcd m1 (gcd m2 (c1 - c2)) dvd m1"
      by (rule gcd_dvd1)
    show ?thesis
      unfolding x_rep y_rep
      apply (simp only: join_congruence_rep.simps gamma_congruence_rep.simps)
      apply (subst congruence_class_subset_iff)
      using modulus by simp
  qed
qed

lemma gamma_join_congruence_rep_ub2:
  "gamma_congruence_rep y \<subseteq>
   gamma_congruence_rep (join_congruence_rep x y)"
proof (cases x)
  case None
  then show ?thesis by simp
next
  case (Some p1)
  obtain c1 m1 where p1: "p1 = (c1, m1)"
    by (cases p1)
  have x_rep: "x = Some (c1, m1)"
    using Some p1 by simp
  show ?thesis
  proof (cases y)
    case None
    with x_rep show ?thesis by simp
  next
    case (Some p2)
    obtain c2 m2 where p2: "p2 = (c2, m2)"
      by (cases p2)
    have y_rep: "y = Some (c2, m2)"
      using Some p2 by simp
    let ?g = "gcd m1 (gcd m2 (c1 - c2))"
    have modulus: "?g dvd m2"
      by (rule dvd_trans[OF gcd_dvd2 gcd_dvd1])
    have offset_forward: "?g dvd c1 - c2"
      by (rule dvd_trans[OF gcd_dvd2 gcd_dvd2])
    have offset: "?g dvd c2 - c1"
      by (subst dvd_diff_commute) (rule offset_forward)
    show ?thesis
      unfolding x_rep y_rep
      apply (simp only: join_congruence_rep.simps gamma_congruence_rep.simps)
      apply (subst congruence_class_subset_iff)
      using modulus offset by simp
  qed
qed

lemma gamma_join_congruence_rep_least:
  assumes xz:
    "gamma_congruence_rep x \<subseteq> gamma_congruence_rep z"
      and yz:
    "gamma_congruence_rep y \<subseteq> gamma_congruence_rep z"
  shows
    "gamma_congruence_rep (join_congruence_rep x y) \<subseteq>
     gamma_congruence_rep z"
proof (cases x)
  case None
  with yz show ?thesis by simp
next
  case (Some p1)
  obtain c1 m1 where p1: "p1 = (c1, m1)"
    by (cases p1)
  have x_rep: "x = Some (c1, m1)"
    using Some p1 by simp
  show ?thesis
  proof (cases y)
    case None
    with x_rep xz show ?thesis by simp
  next
    case (Some p2)
    obtain c2 m2 where p2: "p2 = (c2, m2)"
      by (cases p2)
    have y_rep: "y = Some (c2, m2)"
      using Some p2 by simp
    show ?thesis
    proof (cases z)
      case None
      have member: "c1 \<in> gamma_congruence_rep x"
        unfolding x_rep by simp
      have "c1 \<in> gamma_congruence_rep z"
        by (rule subsetD[OF xz member])
      with None show ?thesis by simp
    next
      case (Some p3)
      obtain c3 m3 where p3: "p3 = (c3, m3)"
        by (cases p3)
      have z_rep: "z = Some (c3, m3)"
        using Some p3 by simp
      have x_divisibility:
        "m3 dvd m1 \<and> m3 dvd c1 - c3"
        using xz
        unfolding x_rep z_rep
        by (simp only: gamma_congruence_rep.simps
            congruence_class_subset_iff)
      have y_divisibility:
        "m3 dvd m2 \<and> m3 dvd c2 - c3"
        using yz
        unfolding y_rep z_rep
        by (simp only: gamma_congruence_rep.simps
            congruence_class_subset_iff)
      have offset: "m3 dvd c1 - c2"
      proof -
        have "m3 dvd (c1 - c3) - (c2 - c3)"
          by (rule dvd_diff[OF x_divisibility[THEN conjunct2]
                y_divisibility[THEN conjunct2]])
        then show ?thesis by simp
      qed
      have inner: "m3 dvd gcd m2 (c1 - c2)"
        by (rule gcd_greatest[OF y_divisibility[THEN conjunct1] offset])
      have modulus:
        "m3 dvd gcd m1 (gcd m2 (c1 - c2))"
        by (rule gcd_greatest[OF x_divisibility[THEN conjunct1] inner])
      show ?thesis
        unfolding x_rep y_rep z_rep
        apply (simp only: join_congruence_rep.simps gamma_congruence_rep.simps)
        apply (subst congruence_class_subset_iff)
        using modulus x_divisibility by simp
    qed
  qed
qed

lemma join_congruence_ub1:
  "a <= join_congruence a b"
  unfolding less_eq_congruence_iff_gamma
    gamma_congruence_def
  apply (simp only: join_congruence.rep_eq gamma_normalize_congruence_rep)
  by (rule gamma_join_congruence_rep_ub1)

lemma join_congruence_ub2:
  "b <= join_congruence a b"
  unfolding less_eq_congruence_iff_gamma
    gamma_congruence_def
  apply (simp only: join_congruence.rep_eq gamma_normalize_congruence_rep)
  by (rule gamma_join_congruence_rep_ub2)

lemma join_congruence_least:
  assumes "a <= c" and "b <= c"
  shows "join_congruence a b <= c"
  using assms
  unfolding less_eq_congruence_iff_gamma
    gamma_congruence_def
  apply (simp only: join_congruence.rep_eq gamma_normalize_congruence_rep)
  by (rule gamma_join_congruence_rep_least)

instantiation congruence :: sup
begin

definition sup_congruence :: "congruence => congruence => congruence" where
  "sup_congruence = join_congruence"

instance ..

end

instance congruence :: semilattice_sup
proof intro_classes
  fix a b c :: congruence
  show "a <= a \<squnion> b"
    unfolding sup_congruence_def by (rule join_congruence_ub1)
  show "b <= a \<squnion> b"
    unfolding sup_congruence_def by (rule join_congruence_ub2)
  show "b <= a \<Longrightarrow> c <= a \<Longrightarrow> b \<squnion> c <= a"
    unfolding sup_congruence_def by (rule join_congruence_least)
qed

instance congruence :: bounded_semilattice_sup_bot ..

lemma join_congruence_same_modulus_regression:
  "mk_congruence 1 4 \<squnion> mk_congruence 3 4 =
   mk_congruence 1 2"
  by eval

subsection \<open>Meet\<close>

text \<open>
  Intersecting two non-singleton congruence classes is the executable Chinese
  remainder construction. The Bezout coefficient computes one shared residue;
  the least common multiple is the period of every shared solution.
\<close>

fun intersect_congruence_rep ::
    "congruence_rep => congruence_rep => congruence_rep"
where
  "intersect_congruence_rep None y = None"
| "intersect_congruence_rep x None = None"
| "intersect_congruence_rep (Some (c1, m1)) (Some (c2, m2)) =
     normalize_congruence_rep
       (if m1 = 0 then
          if m2 dvd c1 - c2 then Some (c1, 0) else None
        else if m2 = 0 then
          if m1 dvd c2 - c1 then Some (c2, 0) else None
        else
          let g = gcd m1 m2
          in if g dvd c2 - c1 then
               let s = fst (bezout_coefficients m1 m2);
                   q = (c2 - c1) div g
               in Some (c1 + m1 * (q * s), lcm m1 m2)
             else None)"

lemma normalized_intersect_congruence_rep [simp]:
  "normalized_congruence_rep (intersect_congruence_rep x y)"
  by (cases x; cases y)
     (auto simp: split_def split: if_splits prod.splits)

instantiation congruence :: inf
begin

lift_definition inf_congruence ::
    "congruence => congruence => congruence"
  is intersect_congruence_rep
  by simp

instance ..

end

lemma bezout_shared_residue:
  assumes compatible: "gcd m1 m2 dvd c2 - c1"
  defines
    "q == (c2 - c1) div gcd m1 m2"
  shows
    "m1 dvd
       (c1 + m1 * (q * fst (bezout_coefficients m1 m2))) - c1 \<and>
     m2 dvd
       (c1 + m1 * (q * fst (bezout_coefficients m1 m2))) - c2"
proof (intro conjI)
  show
    "m1 dvd
      c1 + m1 * (q * fst (bezout_coefficients m1 m2)) - c1"
    by simp
  have bezout:
    "fst (bezout_coefficients m1 m2) * m1 +
     snd (bezout_coefficients m1 m2) * m2 =
     gcd m1 m2"
    by (rule bezout_coefficients_fst_snd)
  have quotient:
    "q * gcd m1 m2 = c2 - c1"
    unfolding q_def
    using dvd_mult_div_cancel[OF compatible]
    by (simp add: mult.commute)
  have scaled0:
    "q * (fst (bezout_coefficients m1 m2) * m1 +
       snd (bezout_coefficients m1 m2) * m2) =
     q * gcd m1 m2"
    by (rule arg_cong[OF bezout])
  have scaled:
    "m1 * (q * fst (bezout_coefficients m1 m2)) +
     m2 * (q * snd (bezout_coefficients m1 m2)) =
     q * gcd m1 m2"
    using scaled0 by (simp add: algebra_simps)
  show
    "m2 dvd
      c1 + m1 * (q * fst (bezout_coefficients m1 m2)) - c2"
    unfolding dvd_def
  proof (rule exI[of _ "- q * snd (bezout_coefficients m1 m2)"])
    show
      "c1 + m1 * (q * fst (bezout_coefficients m1 m2)) - c2 =
       m2 * (- q * snd (bezout_coefficients m1 m2))"
      using scaled quotient by (simp add: algebra_simps)
  qed
qed


lemma gamma_intersect_congruence_rep:
  assumes normalized_x: "normalized_congruence_rep x"
      and normalized_y: "normalized_congruence_rep y"
  shows
    "gamma_congruence_rep (intersect_congruence_rep x y) =
     gamma_congruence_rep x \<inter> gamma_congruence_rep y"
proof (cases x)
  case None
  then show ?thesis by simp
next
  case (Some cm1)
  note x_some = Some
  obtain c1 m1 where cm1: "cm1 = (c1, m1)"
    by (cases cm1)
  show ?thesis
  proof (cases y)
    case None
    with x_some show ?thesis by simp
  next
    case (Some cm2)
    note y_some = Some
    obtain c2 m2 where cm2: "cm2 = (c2, m2)"
      by (cases cm2)
    show ?thesis
    proof (cases "m1 = 0")
      case True
      with x_some y_some cm1 cm2 show ?thesis
        by auto
    next
      case m1_nonzero: False
      show ?thesis
      proof (cases "m2 = 0")
        case True
        with x_some y_some cm1 cm2 show ?thesis
          by auto
      next
        case m2_nonzero: False
        let ?g = "gcd m1 m2"
        let ?q = "(c2 - c1) div ?g"
        let ?s = "fst (bezout_coefficients m1 m2)"
        let ?z = "c1 + m1 * (?q * ?s)"
        show ?thesis
        proof (cases "?g dvd c2 - c1")
          case incompatible: False
          have empty:
            "{n. m1 dvd n - c1} \<inter>
             {n. m2 dvd n - c2} = {}"
          proof (rule ccontr)
            assume
              "{n. m1 dvd n - c1} \<inter>
               {n. m2 dvd n - c2} ~= {}"
            then obtain n where
              n1: "m1 dvd n - c1" and
              n2: "m2 dvd n - c2"
              by blast
            have g1: "?g dvd n - c1"
              using gcd_dvd1 n1 by (rule dvd_trans)
            have g2: "?g dvd n - c2"
              using gcd_dvd2 n2 by (rule dvd_trans)
            have "?g dvd (n - c1) - (n - c2)"
              by (rule dvd_diff[OF g1 g2])
            then have "?g dvd c2 - c1"
              by simp
            with incompatible show False by contradiction
          qed
          with x_some y_some cm1 cm2 m1_nonzero m2_nonzero
            incompatible
          show ?thesis by simp
        next
          case compatible: True
          have shared:
            "m1 dvd ?z - c1 \<and> m2 dvd ?z - c2"
            by (rule bezout_shared_residue[OF compatible])
          have classes:
            "{n. lcm m1 m2 dvd n - ?z} =
             {n. m1 dvd n - c1} \<inter>
             {n. m2 dvd n - c2}"
          proof -
            have "m1 dvd n - ?z \<longleftrightarrow> m1 dvd n - c1" "m2 dvd n - ?z \<longleftrightarrow> m2 dvd n - c2" for n
              using shared dvd_add_left_iff[of m1 "?z - c1" "n - ?z"]
                dvd_add_left_iff[of m2 "?z - c2" "n - ?z"]
              by simp_all
            then show ?thesis by auto
          qed
          have normalized_gamma:
            "gamma_congruence_rep
               (normalize_congruence_rep
                 (Some (?z, lcm m1 m2))) =
             {n. lcm m1 m2 dvd n - ?z}"
            by (simp only: gamma_normalize_congruence_rep
                gamma_congruence_rep.simps)
          from x_some y_some cm1 cm2 m1_nonzero m2_nonzero
            compatible normalized_gamma classes
          show ?thesis
            by (simp only: intersect_congruence_rep.simps if_False
                if_True Let_def gamma_congruence_rep.simps)
        qed
      qed
    qed
  qed
qed

lemma gamma_inf_congruence [simp]:
  "gamma_congruence (a \<sqinter> b) =
   gamma_congruence a \<inter> gamma_congruence b"
proof -
  have norm_a: "normalized_congruence_rep (Rep_congruence a)"
    by simp
  have norm_b: "normalized_congruence_rep (Rep_congruence b)"
    by simp
  show ?thesis
    using gamma_intersect_congruence_rep[OF norm_a norm_b]
    by (simp add: gamma_congruence_def inf_congruence.rep_eq)
qed

instance congruence :: semilattice_inf
  by standard (auto simp: less_eq_congruence_iff_gamma)

instance congruence :: lattice ..
instance congruence :: bounded_lattice_bot ..


subsection \<open>Executable interface\<close>

text \<open>
  Executable bottom and top tests, each proved against \<open>gamma_congruence\<close>
  and checked by \<open>eval\<close> on small regression values.
\<close>

definition is_bottom_congruence :: "congruence => bool" where
  "is_bottom_congruence a = (a = bot)"

lemma is_bottom_congruence_regression:
  "is_bottom_congruence bottom_congruence \<and>
   \<not> is_bottom_congruence (mk_congruence 0 0)"
  by eval

lemma is_bottom_congruence_correct:
  "is_bottom_congruence a \<longleftrightarrow> gamma_congruence a = {}"
  unfolding is_bottom_congruence_def bot_congruence_def
  by simp

definition is_top_congruence :: "congruence => bool" where
  "is_top_congruence a = (a = top)"

lemma is_top_congruence_regression:
  "is_top_congruence (top :: congruence) \<and>
   \<not> is_top_congruence (mk_congruence 0 2)"
  by eval

lemma is_top_congruence_correct_gamma:
  "is_top_congruence a \<longleftrightarrow> gamma_congruence a = UNIV"
  unfolding is_top_congruence_def
  by (metis gamma_congruence_inject gamma_top_congruence)

text \<open>
  Goblint's congruence notation: a constant prints as itself, the class of \<open>r\<close>
  modulo \<open>m\<close> as \<open>r+m\<int>\<close>, with a zero residue and a unit modulus left out, so
  \<open>3\<int>\<close>, \<open>1+3\<int>\<close> and \<open>\<int>\<close>. A standalone congruence prints its top as \<open>\<top>\<close>.
\<close>

definition string_of_congruence :: "congruence \<Rightarrow> String.literal" where
  "string_of_congruence c =
     (case Rep_congruence c of
        None \<Rightarrow> sym_bottom
      | Some (r, m) \<Rightarrow>
          if m = 0 then string_of_int r
          else (if r = 0 then STR '''' else string_of_int r + STR ''+'')
             + (if m = 1 then STR '''' else string_of_int m) + sym_int)"

lemma string_of_congruence_regression:
  "string_of_congruence bottom_congruence = sym_bottom"
  "string_of_congruence (mk_congruence (-7) 0) = STR ''-7''"
  "string_of_congruence (mk_congruence 0 1) = sym_int"
  "string_of_congruence (mk_congruence 0 3) = STR ''3<int>''"
  "string_of_congruence (mk_congruence 4 3) = STR ''1+3<int>''"
  by eval+

end
