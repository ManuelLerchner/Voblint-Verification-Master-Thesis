theory Int_Domain
  imports Sign_Lattice Interval_Lattice Parity_Domain Congruence_Lattice
begin

section \<open>Composite integer domain\<close>

text \<open>
  The carrier keeps the four scalar abstractions independently. Its
  concretization is their intersection; componentwise order and join preserve
  the existing domain structures. Cross-domain reduction is separate from
  this carrier definition.
\<close>

record int_dom =
  int_sign :: sign
  int_ivl :: ivl
  int_parity :: parity
  int_congruence :: congruence

class int_dom_record_lattice = bounded_semilattice_sup_bot + order_top

instance unit :: int_dom_record_lattice
  by intro_classes

text \<open>
  The record package represents a closed record through an extensible scheme.
  Giving the scheme a componentwise instance makes the closed \<open>int_dom\<close>
  abbreviation usable at every existing lattice-polymorphic boundary. The
  scheme's \<open>more\<close> field is Isabelle machinery, not a semantic extension point:
  new integer components belong in \<open>int_dom\<close> and must participate explicitly
  in its lattice, concretization, and exact bottom decision.
\<close>

instantiation int_dom_ext :: (int_dom_record_lattice) int_dom_record_lattice
begin

definition less_eq_int_dom_ext ::
  "'a int_dom_scheme => 'a int_dom_scheme => bool" where
  "less_eq_int_dom_ext a b \<longleftrightarrow>
     int_sign a <= int_sign b \<and>
     int_ivl a <= int_ivl b \<and>
     int_parity a <= int_parity b \<and>
     int_congruence a <= int_congruence b \<and>
     more a <= more b"

definition less_int_dom_ext ::
  "'a int_dom_scheme => 'a int_dom_scheme => bool" where
  "less_int_dom_ext a b \<longleftrightarrow> a \<le> b \<and> \<not> b \<le> a"

definition sup_int_dom_ext ::
  "'a int_dom_scheme => 'a int_dom_scheme => 'a int_dom_scheme" where
  "sup_int_dom_ext a b =
     int_dom_ext
       (sup (int_sign a) (int_sign b))
       (sup (int_ivl a) (int_ivl b))
       (sup (int_parity a) (int_parity b))
       (sup (int_congruence a) (int_congruence b))
       (sup (more a) (more b))"

definition bot_int_dom_ext :: "'a int_dom_scheme" where
  "bot_int_dom_ext = int_dom_ext bot bot bot bot bot"

definition top_int_dom_ext :: "'a int_dom_scheme" where
  "top_int_dom_ext = int_dom_ext top top top top top"

instance
proof intro_classes
  fix x y z :: "'a int_dom_scheme"
  show "x < y \<longleftrightarrow> x \<le> y \<and> \<not> y \<le> x"
    by (simp add: less_int_dom_ext_def)
  show "x \<le> x"
    by (simp add: less_eq_int_dom_ext_def)
  show "x \<le> y \<Longrightarrow> y \<le> z \<Longrightarrow> x \<le> z"
    by (auto simp: less_eq_int_dom_ext_def intro: order_trans)
  show "x \<le> y \<Longrightarrow> y \<le> x \<Longrightarrow> x = y"
    by (cases x; cases y)
       (auto simp: less_eq_int_dom_ext_def intro: antisym)
  show "x \<le> sup x y"
    by (simp add: less_eq_int_dom_ext_def sup_int_dom_ext_def)
  show "y \<le> sup x y"
    by (simp add: less_eq_int_dom_ext_def sup_int_dom_ext_def)
  show "y \<le> x \<Longrightarrow> z \<le> x \<Longrightarrow> sup y z \<le> x"
    by (auto simp: less_eq_int_dom_ext_def sup_int_dom_ext_def)
  show "bot \<le> x"
    by (simp add: less_eq_int_dom_ext_def bot_int_dom_ext_def)
  show "x \<le> top"
    by (simp add: less_eq_int_dom_ext_def top_int_dom_ext_def)
qed

end

definition int_dom_sip :: "sign => ivl => parity => int_dom" where
  "int_dom_sip s i p =
     (top :: int_dom)\<lparr>int_sign := s, int_ivl := i, int_parity := p\<rparr>"

definition int_dom_sipc ::
  "sign => ivl => parity => congruence => int_dom" where
  "int_dom_sipc s i p c =
     (top :: int_dom)\<lparr>
       int_sign := s,
       int_ivl := i,
       int_parity := p,
       int_congruence := c
     \<rparr>"

lemma int_congruence_int_dom_sip [simp]:
  "int_congruence (int_dom_sip s i p) = top"
  by (simp add: int_dom_sip_def top_int_dom_ext_def)


subsection \<open>Concretization\<close>

definition gamma_int_dom :: "'a int_dom_scheme => int set" where
  "gamma_int_dom d =
     gamma_sign (int_sign d) \<inter>
     gamma_ivl (int_ivl d) \<inter>
     gamma_parity (int_parity d) \<inter>
     gamma_congruence (int_congruence d)"

lemma gamma_int_dom_update_sign [simp]:
  "gamma_int_dom (d\<lparr>int_sign := s\<rparr>) =
   gamma_sign s \<inter>
   gamma_ivl (int_ivl d) \<inter>
   gamma_parity (int_parity d) \<inter>
   gamma_congruence (int_congruence d)"
  by (simp add: gamma_int_dom_def)

lemma gamma_int_dom_update_ivl [simp]:
  "gamma_int_dom (d\<lparr>int_ivl := i\<rparr>) =
   gamma_sign (int_sign d) \<inter>
   gamma_ivl i \<inter>
   gamma_parity (int_parity d) \<inter>
   gamma_congruence (int_congruence d)"
  by (simp add: gamma_int_dom_def)

lemma gamma_int_dom_update_parity [simp]:
  "gamma_int_dom (d\<lparr>int_parity := p\<rparr>) =
   gamma_sign (int_sign d) \<inter>
   gamma_ivl (int_ivl d) \<inter>
   gamma_parity p \<inter>
   gamma_congruence (int_congruence d)"
  by (simp add: gamma_int_dom_def)

lemma gamma_int_dom_update_congruence [simp]:
  "gamma_int_dom (d\<lparr>int_congruence := c\<rparr>) =
   gamma_sign (int_sign d) \<inter>
   gamma_ivl (int_ivl d) \<inter>
   gamma_parity (int_parity d) \<inter>
   gamma_congruence c"
  by (simp add: gamma_int_dom_def)

lemma update_sign_exact:
  assumes
    "gamma_sign s \<inter>
     gamma_ivl (int_ivl d) \<inter>
     gamma_parity (int_parity d) \<inter>
     gamma_congruence (int_congruence d) = gamma_int_dom d"
  shows "gamma_int_dom (d\<lparr>int_sign := s\<rparr>) = gamma_int_dom d"
  using assms by simp

lemma update_ivl_exact:
  assumes
    "gamma_sign (int_sign d) \<inter>
     gamma_ivl i \<inter>
     gamma_parity (int_parity d) \<inter>
     gamma_congruence (int_congruence d) = gamma_int_dom d"
  shows "gamma_int_dom (d\<lparr>int_ivl := i\<rparr>) = gamma_int_dom d"
  using assms by simp

lemma update_parity_exact:
  assumes
    "gamma_sign (int_sign d) \<inter>
     gamma_ivl (int_ivl d) \<inter>
     gamma_parity p \<inter>
     gamma_congruence (int_congruence d) = gamma_int_dom d"
  shows "gamma_int_dom (d\<lparr>int_parity := p\<rparr>) = gamma_int_dom d"
  using assms by simp

lemma update_congruence_exact:
  assumes
    "gamma_sign (int_sign d) \<inter>
     gamma_ivl (int_ivl d) \<inter>
     gamma_parity (int_parity d) \<inter>
     gamma_congruence c = gamma_int_dom d"
  shows "gamma_int_dom (d\<lparr>int_congruence := c\<rparr>) = gamma_int_dom d"
  using assms by simp

lemma update_sign_le:
  "s <= int_sign d \<Longrightarrow>
   d\<lparr>int_sign := s\<rparr> <= d"
  by (simp add: less_eq_int_dom_ext_def)

lemma update_ivl_le:
  "i <= int_ivl d \<Longrightarrow>
   d\<lparr>int_ivl := i\<rparr> <= d"
  by (simp add: less_eq_int_dom_ext_def)

lemma update_parity_le:
  "p <= int_parity d \<Longrightarrow>
   d\<lparr>int_parity := p\<rparr> <= d"
  by (simp add: less_eq_int_dom_ext_def)

lemma update_congruence_le:
  "c <= int_congruence d \<Longrightarrow>
   d\<lparr>int_congruence := c\<rparr> <= d"
  by (simp add: less_eq_int_dom_ext_def)


fun interval_fact_of_sign :: "sign \<Rightarrow> ivl" where
  "interval_fact_of_sign SBot = \<bottom>"
| "interval_fact_of_sign SNeg = Ivl MinInf (Fin (-1))"
| "interval_fact_of_sign SNonPos = Ivl MinInf (Fin 0)"
| "interval_fact_of_sign SZero = Ivl (Fin 0) (Fin 0)"
| "interval_fact_of_sign SNonNeg = Ivl (Fin 0) PlusInf"
| "interval_fact_of_sign SPos = Ivl (Fin 1) PlusInf"
| "interval_fact_of_sign STop = \<top>"

lemma gamma_interval_fact_of_sign [simp]:
  "gamma_ivl (interval_fact_of_sign s) = gamma_sign s"
  by (cases s) (auto simp: bot_ivl_def top_ivl_def ivl_top_def)

fun congruence_fact_of_parity :: "parity => congruence" where
  "congruence_fact_of_parity PBot = bot"
| "congruence_fact_of_parity PEven = mk_congruence 0 2"
| "congruence_fact_of_parity POdd = mk_congruence 1 2"
| "congruence_fact_of_parity PTop = top"

lemma gamma_congruence_fact_of_parity [simp]:
  "gamma_congruence (congruence_fact_of_parity p) = gamma_parity p"
  by (cases p)
     (auto simp: bot_congruence_def)

lemma gamma_intersect_ivl_exact:
  "gamma_ivl (intersect_ivl a b) = gamma_ivl a \<inter> gamma_ivl b"
  using gamma_ivl_mono[OF intersect_ivl_le1]
        gamma_ivl_mono[OF intersect_ivl_le2]
        intersect_ivl_gamma
  by blast

subsection \<open>Exact executable emptiness\<close>

lemma inter_nonempty_iff:
  "A \<inter> B \<noteq> {} \<longleftrightarrow> (\<exists>x. x \<in> A \<and> x \<in> B)"
  by blast

lemma congruence_between_iff:
  assumes normalized: "normalized_congruence_rep (Some (c, m))"
  shows
    "(\<exists>n::int. l \<le> n \<and> n \<le> u \<and> m dvd n - c) \<longleftrightarrow>
     (if m = 0 then l \<le> c \<and> c \<le> u
      else l \<le> u \<and> l + ((c - l) mod m) \<le> u)"
proof (cases "m = 0")
  case True
  then show ?thesis by simp
next
  case False
  from normalized_congruence_rep_nonzero[OF normalized False]
  have modulus: "0 < m" by simp
  show ?thesis
  proof
    assume "\<exists>n::int. l \<le> n \<and> n \<le> u \<and> m dvd n - c"
    then obtain n where n: "l \<le> n" "n \<le> u" "m dvd n - c"
      by blast
    have offset: "m dvd c - n"
      using n(3) by (metis dvd_minus_iff minus_diff_eq)
    have mod_eq: "(c - l) mod m = (n - l) mod m"
      using offset
      by (simp add:
          Euclidean_Rings.euclidean_ring_cancel_class.mod_eq_dvd_iff)
    have remainder_le: "(n - l) mod m \<le> n - l"
      by (rule Euclidean_Rings.zmod_le_nonneg_dividend) (use n(1) in linarith)
    show
      "if m = 0 then l \<le> c \<and> c \<le> u
       else l \<le> u \<and> l + ((c - l) mod m) \<le> u"
      using False mod_eq n(1,2) remainder_le
      by simp
  next
    assume rhs:
      "if m = 0 then l \<le> c \<and> c \<le> u
       else l \<le> u \<and> l + ((c - l) mod m) \<le> u"
    let ?n = "l + ((c - l) mod m)"
    have lower: "l \<le> ?n"
      using modulus by simp
    have congruent: "m dvd ?n - c"
    proof -
      have base: "m dvd (c - l) - (c - l) mod m"
        by (rule dvd_minus_mod)
      have "m dvd - ((c - l) - (c - l) mod m)"
        using base by (simp only: dvd_minus_iff)
      also have
        "- ((c - l) - (c - l) mod m) = ?n - c"
        by simp
      finally show ?thesis .
    qed
    have upper: "?n \<le> u"
      using rhs False by simp
    show "\<exists>n::int. l \<le> n \<and> n \<le> u \<and> m dvd n - c"
      by (rule exI[of _ ?n]) (use lower upper congruent in blast)
  qed
qed

lemma congruence_class_nonempty:
  "\<exists>n::int. m dvd n - c"
  by (rule exI[of _ c]) simp

lemma exists_congruence_le:
  assumes normalized: "normalized_congruence_rep (Some (c, m))"
      and nonzero: "m \<noteq> 0"
  shows "\<exists>n::int. n \<le> u \<and> m dvd n - c"
proof -
  from normalized_congruence_rep_nonzero[OF normalized nonzero]
  have one_le: "1 \<le> m" by simp
  let ?q = "abs (c - u) + 1"
  have q_nonnegative: "0 \<le> ?q" by simp
  have difference_le_q: "c - u \<le> ?q"
    using abs_ge_self[of "c - u"] by linarith
  have scale: "?q \<le> m * ?q"
    using mult_right_mono[OF one_le q_nonnegative] by simp
  let ?n = "c - m * ?q"
  have upper: "?n \<le> u"
    using difference_le_q scale by linarith
  have congruent: "m dvd ?n - c"
    by simp
  show ?thesis
    by (rule exI[of _ ?n]) (use upper congruent in blast)
qed

lemma exists_congruence_ge:
  assumes normalized: "normalized_congruence_rep (Some (c, m))"
      and nonzero: "m \<noteq> 0"
  shows "\<exists>n::int. l \<le> n \<and> m dvd n - c"
proof -
  from normalized_congruence_rep_nonzero[OF normalized nonzero]
  have one_le: "1 \<le> m" by simp
  let ?q = "abs (l - c) + 1"
  have q_nonnegative: "0 \<le> ?q" by simp
  have difference_le_q: "l - c \<le> ?q"
    using abs_ge_self[of "l - c"] by linarith
  have scale: "?q \<le> m * ?q"
    using mult_right_mono[OF one_le q_nonnegative] by simp
  let ?n = "c + m * ?q"
  have lower: "l \<le> ?n"
    using difference_le_q scale by linarith
  have congruent: "m dvd ?n - c"
    by simp
  show ?thesis
    by (rule exI[of _ ?n]) (use lower congruent in blast)
qed

fun ivl_congruence_rep_nonempty ::
  "ivl => congruence_rep => bool" where
  "ivl_congruence_rep_nonempty i None = False"
| "ivl_congruence_rep_nonempty (Ivl MinInf MinInf) (Some cm) = False"
| "ivl_congruence_rep_nonempty (Ivl MinInf (Fin u)) (Some (c, m)) =
     (if m = 0 then c \<le> u else True)"
| "ivl_congruence_rep_nonempty (Ivl MinInf PlusInf) (Some cm) = True"
| "ivl_congruence_rep_nonempty (Ivl (Fin l) MinInf) (Some cm) = False"
| "ivl_congruence_rep_nonempty (Ivl (Fin l) (Fin u)) (Some (c, m)) =
     (if m = 0 then l \<le> c \<and> c \<le> u
      else l \<le> u \<and> l + ((c - l) mod m) \<le> u)"
| "ivl_congruence_rep_nonempty (Ivl (Fin l) PlusInf) (Some (c, m)) =
     (if m = 0 then l \<le> c else True)"
| "ivl_congruence_rep_nonempty (Ivl PlusInf u) (Some cm) = False"

lemma ivl_congruence_rep_nonempty_correct:
  assumes normalized: "normalized_congruence_rep r"
  shows
    "ivl_congruence_rep_nonempty i r \<longleftrightarrow>
     gamma_ivl i \<inter> gamma_congruence_rep r \<noteq> {}"
proof (cases r)
  case None
  then show ?thesis by simp
next
  case (Some cm)
  obtain c m where cm: "cm = (c, m)"
    by (cases cm)
  have rep: "r = Some (c, m)"
    using Some cm by simp
  have normalized': "normalized_congruence_rep (Some (c, m))"
    using normalized unfolding rep .
  show ?thesis
  proof (cases i)
    case (Ivl l u)
    show ?thesis
      unfolding rep Ivl
      by (cases l; cases u; cases "m = 0")
         (auto simp: inter_nonempty_iff
            congruence_between_iff[OF normalized']
            congruence_class_nonempty
            exists_congruence_le[OF normalized']
            exists_congruence_ge[OF normalized'])
  qed
qed

fun parity_accepts :: "parity => int => bool" where
  "parity_accepts PBot n = False"
| "parity_accepts PEven n = even n"
| "parity_accepts POdd n = odd n"
| "parity_accepts PTop n = True"

lemma parity_accepts_gamma [simp]:
  "parity_accepts p n \<longleftrightarrow> n \<in> gamma_parity p"
  by (cases p) simp_all

lemma parity_accepts_difference:
  assumes concrete: "p = PEven \<or> p = POdd"
      and accepts: "parity_accepts p r"
  shows "2 dvd n - r \<longleftrightarrow> parity_accepts p n"
  using concrete accepts
  by (cases p) auto

lemma dvd_shift_modulus:
  fixes m n c :: int
  shows "m dvd n - (c + m) \<longleftrightarrow> m dvd n - c"
proof
  assume shifted: "m dvd n - (c + m)"
  have "m dvd (n - (c + m)) + m"
    by (rule dvd_add[OF shifted dvd_refl[of m]])
  then show "m dvd n - c" by simp
next
  assume original: "m dvd n - c"
  have "m dvd (n - c) - m"
    by (rule dvd_diff[OF original dvd_refl[of m]])
  also have "(n - c) - m = n - (c + m)"
    by simp
  finally show "m dvd n - (c + m)" .
qed

lemma gamma_normalized_lcm_two:
  "gamma_congruence_rep
     (normalize_congruence_rep (Some (r, lcm m 2))) =
   {n. m dvd n - r \<and> 2 dvd n - r}"
  by (simp only: gamma_normalize_congruence_rep
      gamma_congruence_rep.simps
      GCD.semiring_gcd_class.lcm_least_iff)

lemma congruent_even_modulus:
  fixes m n c :: int
  assumes modulus: "even m"
      and congruent: "m dvd n - c"
  shows "even n \<longleftrightarrow> even c"
proof -
  obtain k where difference: "n - c = m * k"
    using congruent unfolding dvd_def by blast
  have difference_even: "even (n - c)"
    using modulus difference by simp
  have parity_eq: "even (n - c) = even (n + c)"
    by (rule even_diff_iff)
  have sum_even: "even (n + c)"
    using parity_eq difference_even by blast
  show ?thesis
    using sum_even
    by (simp only: Parity.semiring_parity_class.even_add)
qed

lemma normalized_lcm_two_inter_parity:
  assumes concrete: "p = PEven \<or> p = POdd"
      and accepts: "parity_accepts p r"
  shows
    "gamma_congruence_rep
       (normalize_congruence_rep (Some (r, lcm m 2))) =
     gamma_parity p \<inter> {n. m dvd n - r}"
proof -
  have difference:
    "\<And>n. 2 dvd n - r \<longleftrightarrow> parity_accepts p n"
    by (rule parity_accepts_difference[OF concrete accepts])
  show ?thesis
    unfolding gamma_normalized_lcm_two
    using difference by auto
qed

lemma even_modulus_disjoint_parity:
  assumes concrete: "p = PEven \<or> p = POdd"
      and modulus: "even m"
      and rejects: "\<not> parity_accepts p c"
  shows "gamma_parity p \<inter> {n. m dvd n - c} = {}"
proof (rule equals0I)
  fix n
  assume member:
    "n \<in> gamma_parity p \<inter> {n. m dvd n - c}"
  from member have accepts: "parity_accepts p n"
    by simp
  from member have congruent: "m dvd n - c"
    by simp
  have same: "even n \<longleftrightarrow> even c"
    by (rule congruent_even_modulus[OF modulus congruent])
  from concrete rejects accepts same show False
    by (cases p) auto
qed

lemma parity_accepts_add_odd:
  assumes concrete: "p = PEven \<or> p = POdd"
      and rejects: "\<not> parity_accepts p c"
      and modulus: "odd m"
  shows "parity_accepts p (c + m)"
  using concrete rejects modulus by (cases p) auto

fun restrict_congruence_rep_by_parity ::
  "parity => congruence_rep => congruence_rep" where
  "restrict_congruence_rep_by_parity PBot r = None"
| "restrict_congruence_rep_by_parity PTop r = r"
| "restrict_congruence_rep_by_parity p None = None"
| "restrict_congruence_rep_by_parity p (Some (c, m)) =
     (if m = 0 then
        if parity_accepts p c then Some (c, 0) else None
      else if even m \<and> \<not> parity_accepts p c then None
      else
        normalize_congruence_rep
          (Some
            (c + (if parity_accepts p c then 0 else m),
             lcm m 2)))"

lemma normalized_restrict_congruence_rep_by_parity:
  assumes "normalized_congruence_rep r"
  shows
    "normalized_congruence_rep
       (restrict_congruence_rep_by_parity p r)"
  using assms
  by (cases p; cases r)
     (auto simp only: restrict_congruence_rep_by_parity.simps
        normalized_congruence_rep.simps
        normalized_normalize_congruence_rep
        option.simps
        split: prod.splits if_splits)

lemma restrict_concrete_parity_correct:
  assumes concrete: "p = PEven \<or> p = POdd"
  shows
    "gamma_congruence_rep
       (restrict_congruence_rep_by_parity p (Some (c, m))) =
     gamma_parity p \<inter> gamma_congruence_rep (Some (c, m))"
proof (cases "m = 0")
  case True
  with concrete show ?thesis
    by (cases p) auto
next
  case nonzero: False
  show ?thesis
  proof (cases "even m")
    case modulus: True
    show ?thesis
    proof (cases "parity_accepts p c")
      case accepts: True
      have reduced:
        "restrict_congruence_rep_by_parity p (Some (c, m)) =
         normalize_congruence_rep (Some (c, lcm m 2))"
        using concrete nonzero modulus accepts
        by (cases p) simp_all
      have exact:
        "gamma_congruence_rep
           (normalize_congruence_rep (Some (c, lcm m 2))) =
         gamma_parity p \<inter> {n. m dvd n - c}"
        by (rule normalized_lcm_two_inter_parity[OF concrete accepts])
      show ?thesis
        unfolding reduced
        using exact by simp
    next
      case rejects: False
      have reduced:
        "restrict_congruence_rep_by_parity p (Some (c, m)) = None"
        using concrete nonzero modulus rejects
        by (cases p) simp_all
      have disjoint:
        "gamma_parity p \<inter> {n. m dvd n - c} = {}"
        by (rule even_modulus_disjoint_parity[OF concrete modulus rejects])
      show ?thesis
        unfolding reduced
        using disjoint by simp
    qed
  next
    case modulus: False
    show ?thesis
    proof (cases "parity_accepts p c")
      case accepts: True
      have reduced:
        "restrict_congruence_rep_by_parity p (Some (c, m)) =
         normalize_congruence_rep (Some (c, lcm m 2))"
        using concrete nonzero modulus accepts
        by (cases p) simp_all
      have exact:
        "gamma_congruence_rep
           (normalize_congruence_rep (Some (c, lcm m 2))) =
         gamma_parity p \<inter> {n. m dvd n - c}"
        by (rule normalized_lcm_two_inter_parity[OF concrete accepts])
      show ?thesis
        unfolding reduced
        using exact by simp
    next
      case rejects: False
      have odd_modulus: "odd m"
        using modulus by simp
      have shifted_accepts: "parity_accepts p (c + m)"
        by (rule parity_accepts_add_odd[OF concrete rejects odd_modulus])
      have reduced:
        "restrict_congruence_rep_by_parity p (Some (c, m)) =
         normalize_congruence_rep (Some (c + m, lcm m 2))"
        using concrete nonzero modulus rejects
        by (cases p) simp_all
      have exact:
        "gamma_congruence_rep
           (normalize_congruence_rep (Some (c + m, lcm m 2))) =
         gamma_parity p \<inter> {n. m dvd n - (c + m)}"
        by (rule normalized_lcm_two_inter_parity[
              OF concrete shifted_accepts])
      show ?thesis
        unfolding reduced
        using exact by (simp only: gamma_congruence_rep.simps
            dvd_shift_modulus)
    qed
  qed
qed

lemma restrict_congruence_rep_by_parity_correct:
  assumes normalized: "normalized_congruence_rep r"
  shows
    "gamma_congruence_rep
       (restrict_congruence_rep_by_parity p r) =
     gamma_parity p \<inter> gamma_congruence_rep r"
proof (cases p)
  case PBot
  then show ?thesis by simp
next
  case PTop
  then show ?thesis by simp
next
  case destination: PEven
  show ?thesis
  proof (cases r)
    case None
    with destination show ?thesis by simp
  next
    case (Some cm)
    obtain c m where cm: "cm = (c, m)"
      by (cases cm)
    have rep: "r = Some (c, m)"
      using Some cm by simp
    show ?thesis
      unfolding destination rep
      by (rule restrict_concrete_parity_correct) simp
  qed
next
  case destination: POdd
  show ?thesis
  proof (cases r)
    case None
    with destination show ?thesis by simp
  next
    case (Some cm)
    obtain c m where cm: "cm = (c, m)"
      by (cases cm)
    have rep: "r = Some (c, m)"
      using Some cm by simp
    show ?thesis
      unfolding destination rep
      by (rule restrict_concrete_parity_correct) simp
  qed
qed


lift_definition restrict_congruence_by_parity ::
  "parity => congruence => congruence"
  is restrict_congruence_rep_by_parity
  by (rule normalized_restrict_congruence_rep_by_parity)

lemma Rep_restrict_congruence_by_parity [simp]:
  "Rep_congruence (restrict_congruence_by_parity p c) =
   restrict_congruence_rep_by_parity p (Rep_congruence c)"
  by (rule restrict_congruence_by_parity.rep_eq)

lemma gamma_restrict_congruence_by_parity [simp]:
  "gamma_congruence (restrict_congruence_by_parity p c) =
   gamma_parity p \<inter> gamma_congruence c"
proof -
  have normalized:
    "normalized_congruence_rep (Rep_congruence c)"
    using Rep_congruence[of c] by simp
  have raw:
    "gamma_congruence_rep
       (restrict_congruence_rep_by_parity p (Rep_congruence c)) =
     gamma_parity p \<inter>
     gamma_congruence_rep (Rep_congruence c)"
    by (rule restrict_congruence_rep_by_parity_correct[OF normalized])
  show ?thesis
    unfolding gamma_congruence_def
    using raw by simp
qed

definition ivl_congruence_nonempty ::
  "ivl => congruence => bool" where
  "ivl_congruence_nonempty i c =
   ivl_congruence_rep_nonempty i (Rep_congruence c)"

lemma ivl_congruence_nonempty_correct:
  "ivl_congruence_nonempty i c \<longleftrightarrow>
   gamma_ivl i \<inter> gamma_congruence c \<noteq> {}"
proof -
  have normalized:
    "normalized_congruence_rep (Rep_congruence c)"
    using Rep_congruence[of c] by simp
  show ?thesis
    unfolding ivl_congruence_nonempty_def gamma_congruence_def
    by (rule ivl_congruence_rep_nonempty_correct[OF normalized])
qed

definition is_bottom_int_dom :: "'a int_dom_scheme => bool" where
  "is_bottom_int_dom d =
     (\<not> ivl_congruence_nonempty
       (intersect_ivl
         (interval_fact_of_sign (int_sign d))
         (int_ivl d))
       (restrict_congruence_by_parity
         (int_parity d)
         (int_congruence d)))"

lemma is_bottom_int_dom_correct:
  "is_bottom_int_dom d \<longleftrightarrow> gamma_int_dom d = {}"
proof -
  let ?i =
    "intersect_ivl
       (interval_fact_of_sign (int_sign d))
       (int_ivl d)"
  let ?c =
    "restrict_congruence_by_parity
       (int_parity d)
       (int_congruence d)"
  have nonempty:
    "ivl_congruence_nonempty ?i ?c \<longleftrightarrow>
     gamma_ivl ?i \<inter> gamma_congruence ?c \<noteq> {}"
    by (rule ivl_congruence_nonempty_correct)
  have restricted:
    "gamma_congruence ?c =
     gamma_parity (int_parity d) \<inter>
     gamma_congruence (int_congruence d)"
    by simp
  have interval:
    "gamma_ivl ?i =
     gamma_sign (int_sign d) \<inter> gamma_ivl (int_ivl d)"
    by (simp only: gamma_intersect_ivl_exact
          gamma_interval_fact_of_sign)
  show ?thesis
    unfolding is_bottom_int_dom_def gamma_int_dom_def
    using nonempty restricted interval by blast
qed

text \<open>
  Semantic fullness, symmetric to \<open>is_bottom_int_dom\<close> above: \<open>d = top\<close>
  additionally pins the record's own \<open>more\<close> extension field to its top,
  which \<open>gamma_int_dom\<close> never inspects, so it is strictly stronger than
  \<open>gamma_int_dom d = UNIV\<close> at this instance's actual, extension-polymorphic
  \<open>'a int_dom_scheme\<close> type. Testing each of the four concrete components'
  own exact fullness instead reads off \<open>gamma_int_dom\<close>'s own definition
  directly, the same move \<open>is_bottom_int_dom\<close> already makes for emptiness.
\<close>

definition is_top_int_dom :: "'a int_dom_scheme => bool" where
  "is_top_int_dom d \<longleftrightarrow>
     is_top_sign (int_sign d) \<and> is_top_ivl (int_ivl d) \<and>
     is_top_parity (int_parity d) \<and> is_top_congruence (int_congruence d)"

lemma is_top_int_dom_correct_gamma: "is_top_int_dom d \<longleftrightarrow> gamma_int_dom d = UNIV"
  unfolding is_top_int_dom_def gamma_int_dom_def
  using is_top_sign_correct_gamma is_top_ivl_correct_gamma
        is_top_parity_correct_gamma is_top_congruence_correct_gamma
  by auto

lemma gamma_int_dom_mono:
  assumes ab: "a \<le> b"
  shows "gamma_int_dom a \<subseteq> gamma_int_dom b"
proof -
  from ab have le:
    "int_sign a \<le> int_sign b"
    "int_ivl a \<le> int_ivl b"
    "int_parity a \<le> int_parity b"
    "int_congruence a \<le> int_congruence b"
    by (simp_all add: less_eq_int_dom_ext_def)
  have S: "gamma_sign (int_sign a) \<subseteq> gamma_sign (int_sign b)"
    using le(1) unfolding less_eq_sign_def by (rule gamma_sign_mono)
  have I: "gamma_ivl (int_ivl a) \<subseteq> gamma_ivl (int_ivl b)"
    using le(2) by (rule gamma_ivl_mono)
  have P: "gamma_parity (int_parity a) \<subseteq> gamma_parity (int_parity b)"
    using le(3) unfolding less_eq_parity_def by (rule gamma_parity_mono)
  have C:
    "gamma_congruence (int_congruence a) \<subseteq>
     gamma_congruence (int_congruence b)"
    using le(4)
    unfolding less_eq_congruence_def congruence_le_iff_gamma .
  show ?thesis
    unfolding gamma_int_dom_def using S I P C by auto
qed

subsection \<open>Sound-domain instance\<close>

definition string_of_int_dom :: "'a int_dom_scheme \<Rightarrow> string" where
  "string_of_int_dom d =
     ''sign='' @ string_of_sign (int_sign d)
     @ '', ivl='' @ string_of_ivl (int_ivl d)
     @ '', parity='' @ string_of_parity (int_parity d)
     @ '', congruence='' @ string_of_congruence (int_congruence d)"

instantiation int_dom_ext ::
  (int_dom_record_lattice) sound_domain
begin

definition gamma_abs_int_dom_ext [simp]:
  "gamma (d :: 'a int_dom_scheme) = gamma_int_dom d"

definition is_empty_int_dom_ext [simp]:
  "is_empty (d :: 'a int_dom_scheme) = is_bottom_int_dom d"

definition is_full_int_dom_ext [simp]:
  "is_full (d :: 'a int_dom_scheme) = is_top_int_dom d"

definition to_string_int_dom_ext [simp]:
  "to_string (d :: 'a int_dom_scheme) = string_of_int_dom d"

instance
proof intro_classes
  show "gamma (bot :: 'a int_dom_scheme) = {}"
    by (simp add: gamma_int_dom_def bot_int_dom_ext_def
          bot_sign_def bot_ivl_def bot_parity_def)
next
  show "gamma (top :: 'a int_dom_scheme) = UNIV"
    by (simp add: gamma_int_dom_def top_int_dom_ext_def
          gamma_sign_top gamma_ivl_top top_ivl_def gamma_parity_top)
next
  fix a b :: "'a int_dom_scheme"
  show "a \<le> b \<Longrightarrow> gamma a \<subseteq> gamma b"
    by (simp add: gamma_int_dom_mono)
next
  fix a :: "'a int_dom_scheme"
  show "is_empty a \<longleftrightarrow> gamma a = {}"
    by (simp add: is_bottom_int_dom_correct)
next
  fix a :: "'a int_dom_scheme"
  show "is_full a \<longleftrightarrow> gamma a = UNIV"
    by (simp add: is_top_int_dom_correct_gamma)
qed

end


end
