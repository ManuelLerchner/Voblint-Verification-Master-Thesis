theory Congruence_Kind
  imports
    "Voblint_Analysis_Congruence.Congruence_Arithmetic" "Voblint_Nonrelational.Nonrelational_Domain"
begin

section \<open>Congruences at a kind\<close>

text \<open>
  Normalizing to kind \<open>k\<close> changes a value by a multiple of \<open>2 ^ w\<close>, the kind's modulus.
  A class \<open>c + m\<int>\<close> therefore survives the normalization modulo \<open>gcd m (2 ^ w)\<close>, and when
  that divisor is \<open>2 ^ w\<close> itself the class holds one value of the kind. This is
  Goblint's \<^verbatim>\<open>handle_overflow\<close> in \<^verbatim>\<open>congruenceDomain.ml\<close>, which keeps the largest
  power of two dividing \<open>m\<close>; it applies to every kind that wraps under the overflow
  policy.
\<close>

lemma ik_mod_dvd_ik_norm: "ik_mod k dvd ik_norm k n - n"
proof -
  have "ik_norm k n - n = - ((n - ik_min k) - (n - ik_min k) mod ik_mod k)"
    by (simp add: ik_norm_mod)
  then show ?thesis by (simp only: dvd_minus_iff dvd_minus_mod)
qed

lemma ik_norm_eq_if_dvd:
  assumes "ik_mod k dvd n - c"
  shows "ik_norm k n = ik_norm k c"
proof -
  have "(n - ik_min k) mod ik_mod k = (c - ik_min k) mod ik_mod k"
    using assms by (simp add: mod_eq_dvd_iff)
  then show ?thesis by (simp add: ik_norm_mod)
qed

definition norm_cong_ik :: "ikind \<Rightarrow> congruence \<Rightarrow> congruence" where
  "norm_cong_ik k a =
     (case Rep_congruence a of
        None \<Rightarrow> bot
      | Some (c, m) \<Rightarrow>
          (let g = gcd m (ik_mod k)
           in if g = ik_mod k then congruence_of_int (ik_norm k c) else mk_congruence c g))"

lemma gamma_congruence_Some:
  "Rep_congruence a = Some (c, m) \<Longrightarrow> gamma_congruence a = {n. m dvd n - c}"
  by (simp add: gamma_congruence_def)

lemma norm_cong_ik_sound:
  assumes n: "n \<in> gamma_congruence a"
  shows "ik_norm k n \<in> gamma_congruence (norm_cong_ik k a)"
proof (cases a rule: congruence_rep_cases)
  case Bot
  then show ?thesis using n by (simp add: gamma_congruence_def)
next
  case (Class c m)
  let ?g = "gcd m (ik_mod k)"
  have "m dvd n - c" using n Class by (simp add: gamma_congruence_Some)
  then have gn: "?g dvd n - c" by (rule dvd_trans[rotated]) simp
  have "?g dvd ik_norm k n - n" by (rule dvd_trans[OF _ ik_mod_dvd_ik_norm]) simp
  with gn have g: "?g dvd ik_norm k n - c"
    using dvd_add[of ?g "ik_norm k n - n" "n - c"] by simp
  show ?thesis
  proof (cases "?g = ik_mod k")
    case True
    with gn have "ik_norm k n = ik_norm k c" by (intro ik_norm_eq_if_dvd) simp
    with True Class show ?thesis by (simp add: norm_cong_ik_def)
  next
    case False
    with g Class show ?thesis by (simp add: norm_cong_ik_def Let_def)
  qed
qed

text \<open>The least value of a class at or above a bound decides whether the class meets a
  kind's range.\<close>

lemma cong_least_above:
  fixes m c lo :: int
  assumes m: "0 < m"
  defines "r \<equiv> lo + (c - lo) mod m"
  shows "lo \<le> r" and "m dvd r - c"
    and "m dvd n - c \<Longrightarrow> lo \<le> n \<Longrightarrow> r \<le> n"
proof -
  show "lo \<le> r" using m by (simp add: r_def)
  have "r - c = - ((c - lo) - (c - lo) mod m)" by (simp add: r_def)
  then show "m dvd r - c" by (simp only: dvd_minus_iff dvd_minus_mod)
  assume d: "m dvd n - c" and lo: "lo \<le> n"
  have "(n - lo) mod m = (c - lo) mod m"
    using d by (simp add: mod_eq_dvd_iff)
  moreover have "(n - lo) mod m \<le> n - lo"
    using lo m by (simp add: zmod_le_nonneg_dividend)
  ultimately show "r \<le> n" by (simp add: r_def)
qed

instantiation congruence :: ik_domain
begin

definition widen_ik_congruence :: "ikind \<Rightarrow> congruence \<Rightarrow> congruence \<Rightarrow> congruence" where
  "widen_ik_congruence k a b = a \<squnion> b"

definition narrow_ik_congruence :: "ikind \<Rightarrow> congruence \<Rightarrow> congruence \<Rightarrow> congruence" where
  "narrow_ik_congruence k a b = a \<sqinter> b"

definition empty_ik_congruence :: "ikind \<Rightarrow> congruence \<Rightarrow> bool" where
  "empty_ik_congruence k a =
     (case Rep_congruence a of
        None \<Rightarrow> True
      | Some (c, m) \<Rightarrow>
          if m = 0 then \<not> (ik_min k \<le> c \<and> c \<le> ik_max k)
          else ik_max k < ik_min k + (c - ik_min k) mod m)"

instance proof
  fix k :: ikind and a b :: congruence
  show "a \<le> widen_ik k a b" "b \<le> widen_ik k a b"
    by (simp_all add: widen_ik_congruence_def)
  show "b \<le> a \<Longrightarrow> b \<le> narrow_ik k a b" "b \<le> a \<Longrightarrow> narrow_ik k a b \<le> a"
    by (simp_all add: narrow_ik_congruence_def)
  show "empty_ik k a \<longleftrightarrow> numeric_domain_class.gamma a \<inter> ik_range k = {}"
  proof (cases a rule: congruence_rep_cases)
    case Bot
    then show ?thesis by (simp add: empty_ik_congruence_def gamma_congruence_def)
  next
    case (Class c m)
    show ?thesis
    proof (cases "m = 0")
      case True
      with Class show ?thesis
        by (auto simp: empty_ik_congruence_def gamma_congruence_Some)
    next
      case False
      then have m: "0 < m" using normalized_Rep_congruence[of a] Class by auto
      define r where "r = ik_min k + (c - ik_min k) mod m"
      have r: "ik_min k \<le> r" "m dvd r - c" "\<And>n. m dvd n - c \<Longrightarrow> ik_min k \<le> n \<Longrightarrow> r \<le> n"
        using cong_least_above[OF m, where lo = "ik_min k" and c = c] by (simp_all add: r_def)
      have "empty_ik k a \<longleftrightarrow> ik_max k < r"
        using Class False by (simp add: empty_ik_congruence_def r_def)
      moreover have "ik_max k < r \<longleftrightarrow> gamma_congruence a \<inter> ik_range k = {}"
        using r by (fastforce simp: Class gamma_congruence_Some)
      ultimately show ?thesis by simp
    qed
  qed
qed

end

section \<open>Congruences as a kind-aware integer domain\<close>

text \<open>
  An operation at kind \<open>k\<close> computes the class of the mathematical result and then
  treats a possible overflow as Goblint's \<^verbatim>\<open>congruenceDomain.ml\<close> does under the
  overflow policy; a conversion follows its \<^verbatim>\<open>cast_to\<close>.
\<close>

fun cong_aop :: "aop \<Rightarrow> congruence \<Rightarrow> congruence \<Rightarrow> congruence" where
  "cong_aop AAdd a b = a + b"
| "cong_aop ASub a b = a - b"
| "cong_aop AMul a b = a * b"
| "cong_aop ADiv a b = congruence_div a b"
| "cong_aop AMod a b = congruence_mod a b"

lemma cong_aop_sound:
  "m \<in> gamma_congruence a \<Longrightarrow> n \<in> gamma_congruence b
     \<Longrightarrow> aop_eval op m n \<in> gamma_congruence (cong_aop op a b)"
  by (cases op) (simp_all add: congruence_plus_sound congruence_minus_sound
      congruence_times_sound congruence_div_sound congruence_mod_sound)

text \<open>Two classes with no common value are unequal, as in Goblint's \<^verbatim>\<open>eq\<close>.\<close>

definition cong_eq :: "congruence \<Rightarrow> congruence \<Rightarrow> bool option" where
  "cong_eq a b =
     (case congruence_eqb a b of
        Some r \<Rightarrow> Some r
      | None \<Rightarrow> if is_bottom_congruence (a \<sqinter> b) then Some False else None)"

lemma cong_eq_sound:
  "cong_eq a b = Some r \<Longrightarrow> m \<in> gamma_congruence a \<Longrightarrow> n \<in> gamma_congruence b \<Longrightarrow> (m = n) = r"
  by (auto simp: cong_eq_def is_bottom_congruence_correct split: option.splits if_splits
      dest: congruence_eqb_sound)


fun cong_refine :: "cop \<Rightarrow> congruence \<Rightarrow> congruence \<Rightarrow> congruence \<times> congruence" where
  "cong_refine CEq a b = (a \<sqinter> b, a \<sqinter> b)"
| "cong_refine _ a b = (a, b)"

lemma cong_refine_sound:
  "cop_eval c m n \<Longrightarrow> m \<in> gamma_congruence a \<Longrightarrow> n \<in> gamma_congruence b
     \<Longrightarrow> m \<in> gamma_congruence (fst (cong_refine c a b))
       \<and> n \<in> gamma_congruence (snd (cong_refine c a b))"
  by (cases c) simp_all

definition cong_fits :: "ikind \<Rightarrow> congruence \<Rightarrow> bool" where
  "cong_fits k a =
     (case Rep_congruence a of
        None \<Rightarrow> True
      | Some (c, m) \<Rightarrow> m = 0 \<and> ik_min k \<le> c \<and> c \<le> ik_max k)"

lemma cong_fits_sound: "cong_fits k a \<Longrightarrow> n \<in> gamma_congruence a \<Longrightarrow> n \<in> ik_range k"
  by (cases a rule: congruence_rep_cases)
     (auto simp: cong_fits_def gamma_congruence_Some gamma_congruence_def)

definition cong_excludes :: "int \<Rightarrow> congruence \<Rightarrow> bool" where
  "cong_excludes x a = (case Rep_congruence a of None \<Rightarrow> True | Some (c, m) \<Rightarrow> \<not> m dvd x - c)"

lemma cong_excludes_sound: "cong_excludes x a \<Longrightarrow> n \<in> gamma_congruence a \<Longrightarrow> n \<noteq> x"
  by (auto simp: cong_excludes_def gamma_congruence_def split: option.splits)

text \<open>
  A conversion keeps the class when the source kind's range lies inside the target's,
  wraps a constant, and answers top otherwise, as Goblint's \<^verbatim>\<open>cast_to\<close> does under every
  overflow policy.
\<close>

definition cast_cong_ik :: "ikind \<Rightarrow> congruence \<Rightarrow> congruence" where
  "cast_cong_ik k a =
     (case Rep_congruence a of
        None \<Rightarrow> bot
      | Some (c, m) \<Rightarrow> if m = 0 then congruence_of_int (ik_norm k c) else top)"

lemma cast_cong_ik_sound:
  "n \<in> gamma_congruence a \<Longrightarrow> ik_norm k n \<in> gamma_congruence (cast_cong_ik k a)"
  by (cases a rule: congruence_rep_cases)
     (simp add: gamma_congruence_def, auto simp: cast_cong_ik_def gamma_congruence_Some)

text \<open>
  An arithmetic result follows Goblint's \<^verbatim>\<open>add\<close>, \<^verbatim>\<open>sub\<close>, \<^verbatim>\<open>mul\<close>, \<^verbatim>\<open>div\<close> and \<^verbatim>\<open>rem\<close>.
  A remainder of in-range operands, and a quotient by a divisor other than \<open>-1\<close>, stays
  in range and keeps its class. Otherwise a kind that wraps under the overflow policy
  normalizes the class to the kind (\<^verbatim>\<open>handle_overflow\<close>). A signed kind under
  \<^verbatim>\<open>assume_top\<close> keeps only a difference of two constants that lies in range and answers
  top for everything else. The Int product passes Goblint's \<^verbatim>\<open>no_ov\<close> case itself, when
  its interval shows that the result fits.
\<close>

definition cong_arith_ik ::
    "signed_overflow_policy \<Rightarrow> ikind \<Rightarrow> aop \<Rightarrow> bool \<Rightarrow> congruence \<Rightarrow> congruence \<Rightarrow> congruence" where
  "cong_arith_ik ovp k op operands_fit a b =
     (let r = cong_aop op a b
      in if operands_fit \<and> (op = AMod \<or> op = ADiv \<and> cong_excludes (-1) b) then r
         else if should_wrap ovp k then norm_cong_ik k r
         else if op = ASub \<and> cong_fits k r then r
         else top)"

lemma cong_arith_ik_sound:
  assumes fit: "operands_fit \<Longrightarrow> m \<in> ik_range k \<and> n \<in> ik_range k"
    and ma: "m \<in> gamma_congruence a" and nb: "n \<in> gamma_congruence b"
  shows "ik_norm k (aop_eval op m n) \<in> gamma_congruence (cong_arith_ik ovp k op operands_fit a b)"
proof -
  let ?r = "cong_aop op a b"
  have r: "aop_eval op m n \<in> gamma_congruence ?r" using ma nb by (rule cong_aop_sound)
  show ?thesis
  proof (cases "operands_fit \<and> (op = AMod \<or> op = ADiv \<and> cong_excludes (-1) b)")
    case True
    then have "aop_eval op m n \<in> ik_range k"
      using fit cong_excludes_sound[of "-1" b n] nb c_mod_in_range c_div_in_range by auto
    with True r show ?thesis by (simp add: cong_arith_ik_def)
  next
    case nr: False
    show ?thesis
    proof (cases "should_wrap ovp k")
      case True
      with nr r show ?thesis by (auto simp: cong_arith_ik_def Let_def norm_cong_ik_sound)
    next
      case False
      have "op = ASub \<and> cong_fits k ?r \<Longrightarrow> aop_eval op m n \<in> ik_range k"
        using r cong_fits_sound by blast
      with nr False r show ?thesis by (auto simp: cong_arith_ik_def Let_def)
    qed
  qed
qed

instantiation congruence :: kind_int_domain
begin

definition top_ik_congruence :: "ikind \<Rightarrow> congruence" where "top_ik_congruence k = top"

definition of_int_ik_congruence :: "ikind \<Rightarrow> int \<Rightarrow> congruence" where
  "of_int_ik_congruence k n = congruence_of_int (ik_norm k n)"

definition cast_ik_congruence ::
    "signed_overflow_policy \<Rightarrow> ikind option \<Rightarrow> ikind \<Rightarrow> congruence \<Rightarrow> congruence" where
  "cast_ik_congruence ovp sk k a =
     (case sk of Some s \<Rightarrow> if ik_widens s k then a else cast_cong_ik k a | None \<Rightarrow> cast_cong_ik k a)"

definition arith_ik_congruence ::
    "signed_overflow_policy \<Rightarrow> ikind \<Rightarrow> aop \<Rightarrow> bool \<Rightarrow> congruence \<Rightarrow> congruence \<Rightarrow> congruence" where
  "arith_ik_congruence = cong_arith_ik"

definition cmp_ik_congruence :: "cop \<Rightarrow> congruence \<Rightarrow> congruence \<Rightarrow> bool option" where
  "cmp_ik_congruence = cop_of congruence_lt cong_eq"

definition meet_ik_congruence :: "congruence \<Rightarrow> congruence \<Rightarrow> congruence" where
  "meet_ik_congruence a b = a \<sqinter> b"

definition refine_ik_congruence :: "cop \<Rightarrow> congruence \<Rightarrow> congruence \<Rightarrow> congruence \<times> congruence" where
  "refine_ik_congruence = cong_refine"

definition raw_aop_ik_congruence :: "aop \<Rightarrow> congruence \<Rightarrow> congruence \<Rightarrow> congruence" where
  "raw_aop_ik_congruence = cong_aop"

definition fits_ik_congruence :: "ikind \<Rightarrow> congruence \<Rightarrow> bool" where
  "fits_ik_congruence = cong_fits"

definition answer_ik_congruence :: "congruence \<Rightarrow> answer" where
  "answer_ik_congruence a = answer_with (int_congruence_update (\<lambda>_. a))"

definition of_answer_ik_congruence :: "ikind option \<Rightarrow> answer \<Rightarrow> congruence" where
  "of_answer_ik_congruence sk q = (case q of QBot \<Rightarrow> \<bottom> | QTop \<Rightarrow> \<top> | QLifted d \<Rightarrow> int_congruence d)"

instance proof
  fix n m :: int and k :: ikind and a b :: congruence and op :: aop and c :: cop and r :: bool
  show "n \<in> ik_range k \<Longrightarrow> n \<in> numeric_domain_class.gamma (top_ik k :: congruence)"
    by (simp add: top_ik_congruence_def)
  show "ik_norm k n \<in> numeric_domain_class.gamma (of_int_ik k n :: congruence)"
    by (simp add: of_int_ik_congruence_def)
  show "(\<And>k'. sk = Some k' \<Longrightarrow> n \<in> ik_range k') \<Longrightarrow> n \<in> numeric_domain_class.gamma a
      \<Longrightarrow> ik_norm k n \<in> numeric_domain_class.gamma (cast_ik ovp sk k a)" for ovp sk
    by (cases sk)
       (auto simp: cast_ik_congruence_def ik_widens_def cast_cong_ik_sound simp del: ik_range_iff,
        auto)
  show "(fits \<Longrightarrow> m \<in> ik_range k \<and> n \<in> ik_range k) \<Longrightarrow> m \<in> numeric_domain_class.gamma a
      \<Longrightarrow> n \<in> numeric_domain_class.gamma b
      \<Longrightarrow> ik_norm k (aop_eval op m n) \<in> numeric_domain_class.gamma (arith_ik ovp k op fits a b)" for ovp fits
    using cong_arith_ik_sound[where operands_fit = fits and ovp = ovp and op = op and k = k and m =
      m and n = n]
    by (simp add: arith_ik_congruence_def)
  show "cmp_ik c a b = Some r \<Longrightarrow> m \<in> numeric_domain_class.gamma a
      \<Longrightarrow> n \<in> numeric_domain_class.gamma b \<Longrightarrow> cop_eval c m n = r"
    unfolding cmp_ik_congruence_def
    by simp (rule cop_of_sound[OF congruence_lt_sound cong_eq_sound])
  show "m \<in> numeric_domain_class.gamma a \<Longrightarrow> m \<in> numeric_domain_class.gamma b
      \<Longrightarrow> m \<in> numeric_domain_class.gamma (meet_ik a b)"
    by (simp add: meet_ik_congruence_def)
  show "cop_eval c m n \<Longrightarrow> m \<in> numeric_domain_class.gamma a \<Longrightarrow> n \<in> numeric_domain_class.gamma b
      \<Longrightarrow> m \<in> numeric_domain_class.gamma (fst (refine_ik c a b))
        \<and> n \<in> numeric_domain_class.gamma (snd (refine_ik c a b))"
    by (simp add: refine_ik_congruence_def cong_refine_sound)
  show "m \<in> numeric_domain_class.gamma a \<Longrightarrow> n \<in> numeric_domain_class.gamma b
      \<Longrightarrow> aop_eval op m n \<in> numeric_domain_class.gamma (raw_aop_ik op a b)"
    by (simp add: raw_aop_ik_congruence_def cong_aop_sound)
  show "fits_ik k a \<Longrightarrow> n \<in> numeric_domain_class.gamma a \<Longrightarrow> n \<in> ik_range k"
    using cong_fits_sound[of k a n] by (simp add: fits_ik_congruence_def)
  show "n \<in> numeric_domain_class.gamma a \<Longrightarrow> n \<in> gamma_answer (answer_ik a)"
    by (simp add: answer_ik_congruence_def gamma_int_dom_def top_int_dom_ext_def gamma_sign_top
        gamma_parity_top top_ivl_def gamma_ivl_top)
  show "(\<And>k. sk = Some k \<Longrightarrow> n \<in> ik_range k) \<Longrightarrow> n \<in> gamma_answer q
      \<Longrightarrow> n \<in> numeric_domain_class.gamma (of_answer_ik sk q :: congruence)" for sk q
    by (cases q)
      (simp_all add: of_answer_ik_congruence_def gamma_int_dom_def gamma_sign_top gamma_parity_top)
qed

end

text \<open>As for intervals, the class dictionary of a typed analysis carries the
  concretization, which is never called.\<close>

declare [[code abort: gamma_congruence]]

end
