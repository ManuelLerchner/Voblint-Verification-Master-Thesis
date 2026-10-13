theory Congruence_Kind
  imports
    "Voblint_Analysis_Congruence.Congruence_Arithmetic" "Voblint_Typed_Nonrel.Typed_Nonrel"
begin

section \<open>Congruences at a kind\<close>

text \<open>
  Normalizing to kind \<open>k\<close> changes a value by a multiple of \<open>2 ^ w\<close>, the kind's modulus.
  A class \<open>c + m\<int>\<close> therefore survives the normalization modulo \<open>gcd m (2 ^ w)\<close>, and when
  that divisor is \<open>2 ^ w\<close> itself the class holds one value of the kind. This is
  Goblint's \<^verbatim>\<open>handle_overflow\<close> in \<^verbatim>\<open>congruenceDomain.ml\<close>, which keeps the largest
  power of two dividing \<open>m\<close>. Goblint applies it to unsigned kinds only and answers
  top for a signed overflow; the concrete semantics here wraps signed kinds too, so the
  same normalization is sound and more precise for them.
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
  An operation at kind \<open>k\<close> computes the class of the mathematical result and normalizes
  it to \<open>k\<close>. A conversion from a kind whose range lies inside \<open>k\<close>'s keeps the class, as
  Goblint's \<^verbatim>\<open>cast_to\<close> does for such a \<^verbatim>\<open>from_ik\<close>; any other conversion normalizes,
  where Goblint answers top unless the value is a constant.
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

fun cong_cop :: "cop \<Rightarrow> congruence \<Rightarrow> congruence \<Rightarrow> bool option" where
  "cong_cop CLt a b = congruence_lt a b"
| "cong_cop CGt a b = congruence_lt b a"
| "cong_cop CLe a b = map_option HOL.Not (congruence_lt b a)"
| "cong_cop CGe a b = map_option HOL.Not (congruence_lt a b)"
| "cong_cop CEq a b = cong_eq a b"
| "cong_cop CNe a b = map_option HOL.Not (cong_eq a b)"

lemma cong_cop_sound:
  "cong_cop c a b = Some r \<Longrightarrow> m \<in> gamma_congruence a \<Longrightarrow> n \<in> gamma_congruence b
     \<Longrightarrow> cop_eval c m n = r"
  by (cases c) (auto dest: congruence_lt_sound cong_eq_sound)

fun cong_refine :: "cop \<Rightarrow> congruence \<Rightarrow> congruence \<Rightarrow> congruence \<times> congruence" where
  "cong_refine CEq a b = (a \<sqinter> b, a \<sqinter> b)"
| "cong_refine _ a b = (a, b)"

lemma cong_refine_sound:
  "cop_eval c m n \<Longrightarrow> m \<in> gamma_congruence a \<Longrightarrow> n \<in> gamma_congruence b
     \<Longrightarrow> m \<in> gamma_congruence (fst (cong_refine c a b))
       \<and> n \<in> gamma_congruence (snd (cong_refine c a b))"
  by (cases c) simp_all

definition sub_kind :: "ikind \<Rightarrow> ikind \<Rightarrow> bool" where
  "sub_kind s k \<longleftrightarrow> ik_min k \<le> ik_min s \<and> ik_max s \<le> ik_max k"

instantiation congruence :: kind_int_domain
begin

definition top_ik_congruence :: "ikind \<Rightarrow> congruence" where "top_ik_congruence k = top"

definition of_int_ik_congruence :: "ikind \<Rightarrow> int \<Rightarrow> congruence" where
  "of_int_ik_congruence k n = congruence_of_int (ik_norm k n)"

definition cast_ik_congruence :: "ikind option \<Rightarrow> ikind \<Rightarrow> congruence \<Rightarrow> congruence" where
  "cast_ik_congruence sk k a =
     (case sk of Some s \<Rightarrow> if sub_kind s k then a else norm_cong_ik k a | None \<Rightarrow> norm_cong_ik k a)"

definition arith_ik_congruence :: "ikind \<Rightarrow> aop \<Rightarrow> congruence \<Rightarrow> congruence \<Rightarrow> congruence" where
  "arith_ik_congruence k op a b = norm_cong_ik k (cong_aop op a b)"

definition cmp_ik_congruence :: "cop \<Rightarrow> congruence \<Rightarrow> congruence \<Rightarrow> bool option" where
  "cmp_ik_congruence = cong_cop"

definition meet_ik_congruence :: "congruence \<Rightarrow> congruence \<Rightarrow> congruence" where
  "meet_ik_congruence a b = a \<sqinter> b"

definition refine_ik_congruence :: "cop \<Rightarrow> congruence \<Rightarrow> congruence \<Rightarrow> congruence \<times> congruence" where
  "refine_ik_congruence = cong_refine"

definition raw_aop_ik_congruence :: "aop \<Rightarrow> congruence \<Rightarrow> congruence \<Rightarrow> congruence" where
  "raw_aop_ik_congruence = cong_aop"

definition fits_ik_congruence :: "ikind \<Rightarrow> congruence \<Rightarrow> bool" where
  "fits_ik_congruence k a =
     (case Rep_congruence a of
        None \<Rightarrow> True
      | Some (c, m) \<Rightarrow> m = 0 \<and> ik_min k \<le> c \<and> c \<le> ik_max k)"

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
      \<Longrightarrow> ik_norm k n \<in> numeric_domain_class.gamma (cast_ik sk k a)" for sk
    by (cases sk)
       (auto simp: cast_ik_congruence_def sub_kind_def norm_cong_ik_sound simp del: ik_range_iff,
        auto)
  show "m \<in> numeric_domain_class.gamma a \<Longrightarrow> n \<in> numeric_domain_class.gamma b
      \<Longrightarrow> ik_norm k (aop_eval op m n) \<in> numeric_domain_class.gamma (arith_ik k op a b)"
    by (simp add: arith_ik_congruence_def norm_cong_ik_sound cong_aop_sound)
  show "cmp_ik c a b = Some r \<Longrightarrow> m \<in> numeric_domain_class.gamma a
      \<Longrightarrow> n \<in> numeric_domain_class.gamma b \<Longrightarrow> cop_eval c m n = r"
    by (simp add: cmp_ik_congruence_def cong_cop_sound)
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
    by (cases a rule: congruence_rep_cases)
       (auto simp: fits_ik_congruence_def gamma_congruence_Some gamma_congruence_def)
  show "n \<in> numeric_domain_class.gamma a \<Longrightarrow> n \<in> gamma_answer (answer_ik a)"
    by (simp add: answer_ik_congruence_def gamma_int_dom_def top_int_dom_ext_def gamma_sign_top
        gamma_parity_top top_ivl_def gamma_ivl_top)
  show "(\<And>k. sk = Some k \<Longrightarrow> n \<in> ik_range k) \<Longrightarrow> n \<in> gamma_answer q
      \<Longrightarrow> n \<in> numeric_domain_class.gamma (of_answer_ik sk q :: congruence)" for sk q
    by (cases q) (simp_all add: of_answer_ik_congruence_def gamma_int_dom_def gamma_sign_top gamma_parity_top)
qed

end

text \<open>As for intervals, the class dictionary of a typed analysis carries the
  concretization, which is never called.\<close>

declare [[code abort: gamma_congruence]]

end
