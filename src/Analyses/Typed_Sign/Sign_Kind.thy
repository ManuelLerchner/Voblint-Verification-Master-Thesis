theory Sign_Kind
  imports "Voblint_Analysis_Sign.Sign_Arithmetic" "Voblint_Typed_Nonrel.Typed_Nonrel_Analysis"
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
      using unsigned_range_nonneg[of k] by (fastforce simp: empty_ik_sign_def simp del: ik_range_iff)
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

fun sign_cop :: "cop \<Rightarrow> sign \<Rightarrow> sign \<Rightarrow> bool option" where
  "sign_cop CLt a b = sign_lt a b"
| "sign_cop CGt a b = sign_lt b a"
| "sign_cop CLe a b = map_option HOL.Not (sign_lt b a)"
| "sign_cop CGe a b = map_option HOL.Not (sign_lt a b)"
| "sign_cop CEq a b = sign_eqb a b"
| "sign_cop CNe a b = map_option HOL.Not (sign_eqb a b)"

lemma sign_cop_sound:
  "sign_cop c a b = Some r \<Longrightarrow> m \<in> gamma_sign a \<Longrightarrow> n \<in> gamma_sign b \<Longrightarrow> cop_eval c m n = r"
  by (cases c) (auto dest: sign_lt_sound sign_eqb_sound simp del: sign_lt.simps sign_eqb.simps)

instantiation sign :: kind_int_domain
begin

definition top_ik_sign :: "ikind \<Rightarrow> sign" where
  "top_ik_sign k = (if ik_signed k then STop else SNonNeg)"

definition of_int_ik_sign :: "ikind \<Rightarrow> int \<Rightarrow> sign" where
  "of_int_ik_sign k n = sign_of_int (ik_norm k n)"

definition cast_ik_sign :: "ikind option \<Rightarrow> ikind \<Rightarrow> sign \<Rightarrow> sign" where
  "cast_ik_sign sk k a =
     (case sk of
        Some s \<Rightarrow> if ik_min k \<le> ik_min s \<and> ik_max s \<le> ik_max k then a else sign_cast k a
      | None \<Rightarrow> sign_cast k a)"

definition arith_ik_sign :: "ikind \<Rightarrow> aop \<Rightarrow> sign \<Rightarrow> sign \<Rightarrow> sign" where
  "arith_ik_sign k op a b = sign_cast k (sign_aop op a b)"

definition cmp_ik_sign :: "cop \<Rightarrow> sign \<Rightarrow> sign \<Rightarrow> bool option" where
  "cmp_ik_sign = sign_cop"

definition meet_ik_sign :: "sign \<Rightarrow> sign \<Rightarrow> sign" where
  "meet_ik_sign a b = a \<sqinter> b"

definition refine_ik_sign :: "cop \<Rightarrow> sign \<Rightarrow> sign \<Rightarrow> sign \<times> sign" where
  "refine_ik_sign c a b = (if c = CEq then (a \<sqinter> b, a \<sqinter> b) else (a, b))"

definition raw_aop_ik_sign :: "aop \<Rightarrow> sign \<Rightarrow> sign \<Rightarrow> sign" where
  "raw_aop_ik_sign = sign_aop"

definition fits_ik_sign :: "ikind \<Rightarrow> sign \<Rightarrow> bool" where
  "fits_ik_sign k a \<longleftrightarrow> a = SBot \<or> a = SZero"

instance proof
  fix n m :: int and k :: ikind and a b :: sign and op :: aop and c :: cop and r :: bool
  show "n \<in> ik_range k \<Longrightarrow> n \<in> numeric_domain_class.gamma (top_ik k :: sign)"
    using unsigned_range_nonneg[of k n] by (auto simp: top_ik_sign_def simp del: ik_range_iff)
  show "ik_norm k n \<in> numeric_domain_class.gamma (of_int_ik k n :: sign)"
    by (simp add: of_int_ik_sign_def sign_of_int_gamma)
  show "(\<And>k'. sk = Some k' \<Longrightarrow> n \<in> ik_range k') \<Longrightarrow> n \<in> numeric_domain_class.gamma a
      \<Longrightarrow> ik_norm k n \<in> numeric_domain_class.gamma (cast_ik sk k a)" for sk
    by (cases sk) (auto simp: cast_ik_sign_def sign_cast_sound split: if_splits)
  show "m \<in> numeric_domain_class.gamma a \<Longrightarrow> n \<in> numeric_domain_class.gamma b
      \<Longrightarrow> ik_norm k (aop_eval op m n) \<in> numeric_domain_class.gamma (arith_ik k op a b)"
    by (simp add: arith_ik_sign_def sign_cast_sound sign_aop_sound)
  show "cmp_ik c a b = Some r \<Longrightarrow> m \<in> numeric_domain_class.gamma a
      \<Longrightarrow> n \<in> numeric_domain_class.gamma b \<Longrightarrow> cop_eval c m n = r"
    by (simp add: cmp_ik_sign_def sign_cop_sound)
  show "m \<in> numeric_domain_class.gamma a \<Longrightarrow> m \<in> numeric_domain_class.gamma b
      \<Longrightarrow> m \<in> numeric_domain_class.gamma (meet_ik a b)"
    by (simp add: meet_ik_sign_def)
  show "cop_eval c m n \<Longrightarrow> m \<in> numeric_domain_class.gamma a \<Longrightarrow> n \<in> numeric_domain_class.gamma b
      \<Longrightarrow> m \<in> numeric_domain_class.gamma (fst (refine_ik c a b))
        \<and> n \<in> numeric_domain_class.gamma (snd (refine_ik c a b))"
    by (cases c) (simp_all add: refine_ik_sign_def)
  show "m \<in> numeric_domain_class.gamma a \<Longrightarrow> n \<in> numeric_domain_class.gamma b
      \<Longrightarrow> aop_eval op m n \<in> numeric_domain_class.gamma (raw_aop_ik op a b)"
    by (simp add: raw_aop_ik_sign_def sign_aop_sound)
  show "fits_ik k a \<Longrightarrow> n \<in> numeric_domain_class.gamma a \<Longrightarrow> n \<in> ik_range k"
    by (auto simp: fits_ik_sign_def)
qed

end

declare [[code abort: gamma_sign]]

subsection \<open>Executed\<close>

text \<open>An unsigned \<open>x\<close> is nonnegative whatever its arithmetic did.\<close>

definition sign_prog :: imp_prog where
  "sign_prog = program { fun f() { x = 0; x = x - 5; } fun main() { f(); } }"

lemma sign_value:
  "(case typed_nonrel.state_at [(ScopedId (STR ''f'') (STR ''x''), U8)] 0 Globals_Join tglobal sign_prog []
          (FunctionResult (STR ''f'')) of
      TTop \<Rightarrow> KTop | TL \<sigma> \<Rightarrow> \<sigma> (ScopedId (STR ''f'') (STR ''x'')))
     = KD U8 SNonNeg"
  by eval

end
