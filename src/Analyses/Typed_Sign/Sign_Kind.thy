theory Sign_Kind
  imports "Voblint_Analysis_Sign.Sign_Backward" "Voblint_Typed_Nonrel.Typed_Nonrel_Analysis"
    "Voblint_VIMP.VIMP_Notation"
begin

section \<open>Signs at a kind\<close>

text \<open>
  A sign carries no magnitude, so it cannot rule out an overflow: normalizing a
  nonzero sign to a kind answers the kind's top, every sign at a signed kind and the
  nonnegative ones at an unsigned kind (\<^const>\<open>sign_cast\<close>). Zero survives every
  normalization. A conversion from a kind whose range lies inside the target's
  changes no value and keeps the sign. Sign has no Goblint counterpart; the typed
  Sign is sound and much weaker than the untyped one, whose integers do not wrap.
\<close>

lemma minus_one_in_signed_range: "ik_signed k \<Longrightarrow> - 1 \<in> ik_range k"
  by (cases k) (simp_all add: ik_min_def ik_max_def ik_half_def)

lemma unsigned_range_nonneg: "\<not> ik_signed k \<Longrightarrow> n \<in> ik_range k \<Longrightarrow> 0 \<le> n"
  by (simp add: ik_min_def)

instantiation sign :: ik_domain
begin

definition widen_ik_sign :: "ikind \<Rightarrow> sign \<Rightarrow> sign \<Rightarrow> sign" where
  "widen_ik_sign k a b = a \<squnion> b"

definition narrow_ik_sign :: "ikind \<Rightarrow> sign \<Rightarrow> sign \<Rightarrow> sign" where
  "narrow_ik_sign k a b = a \<sqinter> b"

definition empty_ik_sign :: "ikind \<Rightarrow> sign \<Rightarrow> bool" where
  "empty_ik_sign k a \<longleftrightarrow> a = SBot \<or> (\<not> ik_signed k \<and> a = SNeg)"

instance proof
  fix k :: ikind and a b :: sign
  show "a \<le> widen_ik k a b" "b \<le> widen_ik k a b" by (simp_all add: widen_ik_sign_def)
  show "b \<le> a \<Longrightarrow> b \<le> narrow_ik k a b" "b \<le> a \<Longrightarrow> narrow_ik k a b \<le> a"
    by (simp_all add: narrow_ik_sign_def inf_absorb2)
  show "empty_ik k a \<longleftrightarrow> numeric_domain_class.gamma a \<inter> ik_range k = {}"
  proof
    assume "empty_ik k a"
    then show "numeric_domain_class.gamma a \<inter> ik_range k = {}"
      using unsigned_range_nonneg[of k]
      by (fastforce simp: empty_ik_sign_def simp del: ik_range_iff)
  next
    assume e: "numeric_domain_class.gamma a \<inter> ik_range k = {}"
    have "0 \<notin> gamma_sign a" "1 \<notin> gamma_sign a" "ik_signed k \<Longrightarrow> - 1 \<notin> gamma_sign a"
      using e minus_one_in_signed_range[of k] zero_in_ik_range[of k] one_in_ik_range[of k]
      by (auto simp del: ik_range_iff zero_in_ik_range one_in_ik_range)
    then show "empty_ik k a" by (cases a) (auto simp: empty_ik_sign_def)
  qed
qed

end

fun sign_aop :: "aop \<Rightarrow> sign \<Rightarrow> sign \<Rightarrow> sign" where
  "sign_aop AAdd a b = a + b"
| "sign_aop ASub a b = a - b"
| "sign_aop AMul a b = a * b"
| "sign_aop ADiv a b = sign_div a b"
| "sign_aop AMod a b = sign_mod a b"

lemma sign_aop_sound:
  "m \<in> gamma_sign a \<Longrightarrow> n \<in> gamma_sign b \<Longrightarrow> aop_eval op m n \<in> gamma_sign (sign_aop op a b)"
  by (cases op) (simp_all add: sign_plus_sound sign_minus_sound sign_times_sound
      sign_div_sound sign_mod_sound)


instantiation sign :: kind_int_domain
begin

definition top_ik_sign :: "ikind \<Rightarrow> sign" where
  "top_ik_sign k = (if ik_signed k then STop else SNonNeg)"

definition of_int_ik_sign :: "ikind \<Rightarrow> int \<Rightarrow> sign" where
  "of_int_ik_sign k n = sign_of_int (ik_norm k n)"

definition cast_ik_sign :: "signed_overflow_policy \<Rightarrow> ikind option \<Rightarrow> ikind \<Rightarrow> sign \<Rightarrow> sign" where
  "cast_ik_sign ovp sk k a =
     (case sk of
        Some s \<Rightarrow> if ik_min k \<le> ik_min s \<and> ik_max s \<le> ik_max k then a else sign_cast k a
      | None \<Rightarrow> sign_cast k a)"

text \<open>Some operations on in-range operands cannot leave a signed kind's range, whatever
  their magnitudes: a sum of opposite signs, a difference of equal signs or with a
  negative minuend, a product with zero, a quotient unless both operands may be negative
  (only the minimum divided by \<open>-1\<close> overflows), and every remainder. Their sign needs no
  normalization.\<close>

fun sign_safe :: "aop \<Rightarrow> sign \<Rightarrow> sign \<Rightarrow> bool" where
  "sign_safe AAdd a b \<longleftrightarrow> a \<le> SZero \<or> b \<le> SZero
     \<or> (a \<le> SNonNeg \<and> b \<le> SNonPos) \<or> (a \<le> SNonPos \<and> b \<le> SNonNeg)"
| "sign_safe ASub a b \<longleftrightarrow> b \<le> SZero \<or> (a \<le> SNonNeg \<and> b \<le> SNonNeg) \<or> (a \<le> SNeg \<and> b \<le> SNonPos)"
| "sign_safe AMul a b \<longleftrightarrow> a \<le> SZero \<or> b \<le> SZero"
| "sign_safe ADiv a b \<longleftrightarrow> a \<le> SNonNeg \<or> b \<le> SNonNeg"
| "sign_safe AMod a b \<longleftrightarrow> True"


lemma c_div_between:
  assumes "0 \<le> a \<or> 0 \<le> b"
  shows "min 0 a - (if 0 \<le> a then a else 0) \<le> c_div a b \<and> c_div a b \<le> max 0 a"
proof (cases "b = 0")
  case False
  have q1: "0 \<le> \<bar>a\<bar> div \<bar>b\<bar>" using False by (simp add: pos_imp_zdiv_nonneg_iff)
  have q2: "\<bar>a\<bar> div \<bar>b\<bar> \<le> \<bar>a\<bar>"
    by (cases "a = 0") (simp_all add: int_div_le_self)
  note q = q1 q2
  then show ?thesis
    using False assms by (cases "0 \<le> a"; cases "0 < b") (auto simp: c_div_def sgn_if)
qed (simp add: c_div_def)

lemma sign_safe_range:
  assumes s: "ik_signed k" and m: "m \<in> ik_range k" and n: "n \<in> ik_range k"
    and ma: "m \<in> gamma_sign a" and nb: "n \<in> gamma_sign b" and safe: "sign_safe op a b"
  shows "aop_eval op m n \<in> ik_range k"
proof -
  have lo: "ik_min k = - ik_max k - 1"
    using s by (simp add: ik_min_def ik_max_def)
  have mk: "ik_min k \<le> m" "m \<le> ik_max k" and nk: "ik_min k \<le> n" "n \<le> ik_max k"
    using m n by simp_all
  have sg: "\<And>x c. x \<in> gamma_sign c \<Longrightarrow> c \<le> SZero \<Longrightarrow> x = 0"
    "\<And>x c. x \<in> gamma_sign c \<Longrightarrow> c \<le> SNonNeg \<Longrightarrow> 0 \<le> x"
    "\<And>x c. x \<in> gamma_sign c \<Longrightarrow> c \<le> SNonPos \<Longrightarrow> x \<le> 0"
    "\<And>x c. x \<in> gamma_sign c \<Longrightarrow> c \<le> SNeg \<Longrightarrow> x < 0"
    by (case_tac [!] c) (auto simp: less_eq_sign_def)
  show ?thesis
  proof (cases op)
    case ADiv
    have "0 \<le> m \<or> 0 \<le> n" using safe ADiv sg(2)[OF ma] sg(2)[OF nb] by auto
    with c_div_between[of m n] mk nk lo ADiv show ?thesis by (auto split: if_splits)
  next
    case AMod
    have z: "ik_min k \<le> 0" "0 \<le> ik_max k" by simp_all
    with c_mod_between[of m n] mk AMod show ?thesis
      by (cases "0 \<le> m") (auto simp: min_def max_def simp del: ik_min_le_zero zero_le_ik_max)
  qed (use safe mk nk lo sg ma nb in \<open>auto dest: sg\<close>)
qed

definition arith_ik_sign :: "signed_overflow_policy \<Rightarrow> ikind \<Rightarrow> aop \<Rightarrow> bool \<Rightarrow> sign \<Rightarrow> sign \<Rightarrow> sign" where
  "arith_ik_sign ovp k op fits a b =
     (if fits \<and> ik_signed k \<and> sign_safe op a b then sign_aop op a b
      else sign_cast k (sign_aop op a b))"

definition cmp_ik_sign :: "cop \<Rightarrow> sign \<Rightarrow> sign \<Rightarrow> bool option" where
  "cmp_ik_sign = cop_of sign_lt sign_eqb"

definition meet_ik_sign :: "sign \<Rightarrow> sign \<Rightarrow> sign" where
  "meet_ik_sign a b = a \<sqinter> b"

text \<open>A disequality with zero excludes zero from the other side, the sign counterpart
  of the bound exclusion of \<^verbatim>\<open>inv_bin_int\<close> for \<^verbatim>\<open>Ne\<close>.\<close>

fun sign_excl :: "sign \<Rightarrow> sign \<Rightarrow> sign" where
  "sign_excl SNonNeg SZero = SPos"
| "sign_excl SNonPos SZero = SNeg"
| "sign_excl SZero SZero = SBot"
| "sign_excl a b = a"

lemma sign_excl_sound:
  "m \<noteq> n \<Longrightarrow> m \<in> gamma_sign a \<Longrightarrow> n \<in> gamma_sign b \<Longrightarrow> m \<in> gamma_sign (sign_excl a b)"
  by (induction a b rule: sign_excl.induct) auto

text \<open>An order between two values refines each by the other's sign, as the untyped
  \<^const>\<open>inv_less_sign\<close>: a comparison reads values the kind already holds, so no
  wraparound is involved.\<close>

definition refine_ik_sign :: "cop \<Rightarrow> sign \<Rightarrow> sign \<Rightarrow> sign \<times> sign" where
  "refine_ik_sign c a b =
     (case c of
        CEq \<Rightarrow> (a \<sqinter> b, a \<sqinter> b)
      | CNe \<Rightarrow> (sign_excl a b, sign_excl b a)
      | CLt \<Rightarrow> inv_less_sign True a b
      | CGe \<Rightarrow> inv_less_sign False a b
      | CGt \<Rightarrow> prod.swap (inv_less_sign True b a)
      | CLe \<Rightarrow> prod.swap (inv_less_sign False b a))"

definition raw_aop_ik_sign :: "aop \<Rightarrow> sign \<Rightarrow> sign \<Rightarrow> sign" where
  "raw_aop_ik_sign = sign_aop"

definition fits_ik_sign :: "ikind \<Rightarrow> sign \<Rightarrow> bool" where
  "fits_ik_sign k a \<longleftrightarrow> a = SBot \<or> a = SZero"

definition answer_ik_sign :: "sign \<Rightarrow> answer" where
  "answer_ik_sign a = answer_with (int_sign_update (\<lambda>_. a))"

definition of_answer_ik_sign :: "ikind option \<Rightarrow> answer \<Rightarrow> sign" where
  "of_answer_ik_sign sk q = (case q of QBot \<Rightarrow> \<bottom> | QTop \<Rightarrow> \<top> | QLifted d \<Rightarrow> int_sign d)"

instance proof
  fix n m :: int and k :: ikind and a b :: sign and op :: aop and c :: cop and r :: bool
  show "n \<in> ik_range k \<Longrightarrow> n \<in> numeric_domain_class.gamma (top_ik k :: sign)"
    using unsigned_range_nonneg[of k n] by (auto simp: top_ik_sign_def simp del: ik_range_iff)
  show "ik_norm k n \<in> numeric_domain_class.gamma (of_int_ik k n :: sign)"
    by (simp add: of_int_ik_sign_def sign_of_int_gamma)
  show "(\<And>k'. sk = Some k' \<Longrightarrow> n \<in> ik_range k') \<Longrightarrow> n \<in> numeric_domain_class.gamma a
      \<Longrightarrow> ik_norm k n \<in> numeric_domain_class.gamma (cast_ik ovp sk k a)" for ovp sk
    by (cases sk) (auto simp: cast_ik_sign_def sign_cast_sound split: if_splits)
  show "(fits \<Longrightarrow> m \<in> ik_range k \<and> n \<in> ik_range k) \<Longrightarrow> m \<in> numeric_domain_class.gamma a
      \<Longrightarrow> n \<in> numeric_domain_class.gamma b
      \<Longrightarrow> ik_norm k (aop_eval op m n) \<in> numeric_domain_class.gamma (arith_ik ovp k op fits a b)" for ovp fits
    using sign_safe_range[of k m n a b op] sign_aop_sound[of m a n b op]
    by (auto simp: arith_ik_sign_def sign_cast_sound simp del: ik_range_iff)
  show "cmp_ik c a b = Some r \<Longrightarrow> m \<in> numeric_domain_class.gamma a
      \<Longrightarrow> n \<in> numeric_domain_class.gamma b \<Longrightarrow> cop_eval c m n = r"
    unfolding cmp_ik_sign_def by simp (rule cop_of_sound[OF sign_lt_sound sign_eqb_sound])
  show "m \<in> numeric_domain_class.gamma a \<Longrightarrow> m \<in> numeric_domain_class.gamma b
      \<Longrightarrow> m \<in> numeric_domain_class.gamma (meet_ik a b)"
    by (simp add: meet_ik_sign_def)
  show "cop_eval c m n \<Longrightarrow> m \<in> numeric_domain_class.gamma a \<Longrightarrow> n \<in> numeric_domain_class.gamma b
      \<Longrightarrow> m \<in> numeric_domain_class.gamma (fst (refine_ik c a b))
        \<and> n \<in> numeric_domain_class.gamma (snd (refine_ik c a b))"
    using inv_less_sign_sound[of m a n b True] inv_less_sign_sound[of m a n b False]
      inv_less_sign_sound[of n b m a True] inv_less_sign_sound[of n b m a False]
      sign_excl_sound[of m n a b] sign_excl_sound[of n m b a]
    by (cases c) (auto simp: refine_ik_sign_def not_less)
  show "m \<in> numeric_domain_class.gamma a \<Longrightarrow> n \<in> numeric_domain_class.gamma b
      \<Longrightarrow> aop_eval op m n \<in> numeric_domain_class.gamma (raw_aop_ik op a b)"
    by (simp add: raw_aop_ik_sign_def sign_aop_sound)
  show "fits_ik k a \<Longrightarrow> n \<in> numeric_domain_class.gamma a \<Longrightarrow> n \<in> ik_range k"
    by (auto simp: fits_ik_sign_def)
  show "n \<in> numeric_domain_class.gamma a \<Longrightarrow> n \<in> gamma_answer (answer_ik a)"
    by (simp add: answer_ik_sign_def gamma_int_dom_def top_int_dom_ext_def gamma_sign_top
        gamma_parity_top top_ivl_def gamma_ivl_top)
  show "(\<And>k. sk = Some k \<Longrightarrow> n \<in> ik_range k) \<Longrightarrow> n \<in> gamma_answer q
      \<Longrightarrow> n \<in> numeric_domain_class.gamma (of_answer_ik sk q :: sign)" for sk q
    by (cases q)
      (simp_all add: of_answer_ik_sign_def gamma_int_dom_def gamma_sign_top gamma_parity_top)
qed

end

declare [[code abort: gamma_sign]]

subsection \<open>Executed\<close>

text \<open>An unsigned \<open>x\<close> is nonnegative whatever its arithmetic did.\<close>

definition sign_prog :: imp_prog where
  "sign_prog = program { fun f() { x = 0; x = x - 5; } fun main() { f(); } }"

lemma sign_value:
  "typed_nonrel.state_at default_sem_conf [(ScopedId (STR ''f'') (STR ''x''), U8)] 0 Globals_Join tglobal sign_prog []
     (FunctionResult (STR ''f'')) (ScopedId (STR ''f'') (STR ''x''))
     = KD U8 SNonNeg"
  by eval

end
