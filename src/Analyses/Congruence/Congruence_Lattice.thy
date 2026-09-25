theory Congruence_Lattice
  imports Congruence_Domain
begin

section \<open>When is one residue class contained in another?\<close>

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


section \<open>Join\<close>

fun join_congruence_rep :: "congruence_rep => congruence_rep => congruence_rep" where
  "join_congruence_rep None y = y"
| "join_congruence_rep x None = x"
| "join_congruence_rep (Some (c1, m1)) (Some (c2, m2)) =
     Some (c1, gcd m1 (gcd m2 (c1 - c2)))"

lift_definition join_congruence :: "congruence => congruence => congruence"
  is "\<lambda>x y. normalize_congruence_rep (join_congruence_rep x y)"
  by (rule normalized_normalize_congruence_rep)

lemma Rep_join_congruence [simp]:
  "Rep_congruence (join_congruence a b) =
   normalize_congruence_rep
     (join_congruence_rep (Rep_congruence a) (Rep_congruence b))"
  by (rule join_congruence.rep_eq)

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
  apply (simp only: Rep_join_congruence gamma_normalize_congruence_rep)
  by (rule gamma_join_congruence_rep_ub1)

lemma join_congruence_ub2:
  "b <= join_congruence a b"
  unfolding less_eq_congruence_iff_gamma
    gamma_congruence_def
  apply (simp only: Rep_join_congruence gamma_normalize_congruence_rep)
  by (rule gamma_join_congruence_rep_ub2)

lemma join_congruence_least:
  assumes "a <= c" and "b <= c"
  shows "join_congruence a b <= c"
  using assms
  unfolding less_eq_congruence_iff_gamma
    gamma_congruence_def
  apply (simp only: Rep_join_congruence gamma_normalize_congruence_rep)
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

section \<open>Executable domain interface\<close>

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
  "string_of_congruence bottom_congruence = STR ''<bottom>''"
  "string_of_congruence (mk_congruence (-7) 0) = STR ''-7''"
  "string_of_congruence (mk_congruence 0 1) = STR ''<int>''"
  "string_of_congruence (mk_congruence 0 3) = STR ''3<int>''"
  "string_of_congruence (mk_congruence 4 3) = STR ''1+3<int>''"
  by eval+

end
