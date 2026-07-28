theory Sign_Arithmetic
  imports Sign_Lattice "Voblint_IMP2.IMP2_Expr"
begin

section \<open>Sign arithmetic\<close>

instantiation sign :: plus begin
fun plus_sign :: "sign => sign => sign" where
    "plus_sign SBot    _       = SBot"
  | "plus_sign _       SBot    = SBot"
  | "plus_sign SNeg    SNeg    = SNeg"
  | "plus_sign SNeg    SNonPos = SNeg"
  | "plus_sign SNonPos SNeg    = SNeg"
  | "plus_sign SNonPos SNonPos = SNonPos"
  | "plus_sign SPos    SPos    = SPos"
  | "plus_sign SPos    SNonNeg = SPos"
  | "plus_sign SNonNeg SPos    = SPos"
  | "plus_sign SNonNeg SNonNeg = SNonNeg"
  | "plus_sign SZero   b       = b"
  | "plus_sign a       SZero   = a"
  | "plus_sign _       _       = STop"
instance ..
end

instantiation sign :: minus begin
fun minus_sign :: "sign => sign => sign" where
    "minus_sign SBot    _       = SBot"
  | "minus_sign _       SBot    = SBot"
  | "minus_sign SNeg    SPos    = SNeg"
  | "minus_sign SNeg    SNonNeg = SNeg"
  | "minus_sign SPos    SNeg    = SPos"
  | "minus_sign SPos    SNonPos = SPos"
  | "minus_sign SNeg    SZero   = SNeg"
  | "minus_sign SPos    SZero   = SPos"
  | "minus_sign SZero   SZero   = SZero"
  | "minus_sign SZero   SNeg    = SPos"
  | "minus_sign SZero   SPos    = SNeg"
  | "minus_sign SZero   SNonNeg = SNonPos"
  | "minus_sign SZero   SNonPos = SNonNeg"
  | "minus_sign SNonNeg SZero   = SNonNeg"
  | "minus_sign SNonNeg SNeg    = SPos"
  | "minus_sign SNonNeg SNonPos = SNonNeg"
  | "minus_sign SNonPos SZero   = SNonPos"
  | "minus_sign SNonPos SPos    = SNeg"
  | "minus_sign SNonPos SNonNeg = SNonPos"
  | "minus_sign _       _       = STop"
instance ..
end

instantiation sign :: times begin
fun times_sign :: "sign => sign => sign" where
    "times_sign SBot    _       = SBot"
  | "times_sign _       SBot    = SBot"
  | "times_sign SZero   _       = SZero"
  | "times_sign _       SZero   = SZero"
  | "times_sign SNeg    SNeg    = SPos"
  | "times_sign SPos    SPos    = SPos"
  | "times_sign SNeg    SPos    = SNeg"
  | "times_sign SPos    SNeg    = SNeg"
  | "times_sign SNeg    SNonPos = SNonNeg"
  | "times_sign SNonPos SNeg    = SNonNeg"
  | "times_sign SNeg    SNonNeg = SNonPos"
  | "times_sign SNonNeg SNeg    = SNonPos"
  | "times_sign SPos    SNonNeg = SNonNeg"
  | "times_sign SNonNeg SPos    = SNonNeg"
  | "times_sign SPos    SNonPos = SNonPos"
  | "times_sign SNonPos SPos    = SNonPos"
  | "times_sign SNonNeg SNonNeg = SNonNeg"
  | "times_sign SNonNeg SNonPos = SNonPos"
  | "times_sign SNonPos SNonNeg = SNonPos"
  | "times_sign SNonPos SNonPos = SNonNeg"
  | "times_sign _       _       = STop"
instance ..
end

fun sign_of_int :: "int => sign" where
  "sign_of_int n = (if n < 0 then SNeg else if n = 0 then SZero else SPos)"

lemma sign_of_int_gamma: "n : gamma_sign (sign_of_int n)"
  by (auto split: if_splits)

fun aval_sign :: "aexp => (vname => sign) => sign" where
    "aval_sign (N n)        \<sigma> = sign_of_int n"
  | "aval_sign (V x)        \<sigma> = \<sigma> x"
  | "aval_sign (Plus  a b)  \<sigma> = aval_sign a \<sigma> + aval_sign b \<sigma>"
  | "aval_sign (Minus a b)  \<sigma> = aval_sign a \<sigma> - aval_sign b \<sigma>"
  | "aval_sign (Times a b)  \<sigma> = aval_sign a \<sigma> * aval_sign b \<sigma>"

lemma sign_plus_sound:
  assumes "i \<in> gamma_sign a" "j \<in> gamma_sign b"
  shows "i + j \<in> gamma_sign (a + b)"
  using assms by (cases a; cases b; auto)

lemma sign_minus_sound:
  assumes "i \<in> gamma_sign a" "j \<in> gamma_sign b"
  shows "i - j \<in> gamma_sign (a - b)"
  using assms by (cases a; cases b; auto)

lemma sign_times_sound:
  assumes "i \<in> gamma_sign a" "j \<in> gamma_sign b"
  shows "i * j \<in> gamma_sign (a * b)"
  using assms by (cases a; cases b; auto simp: mult_neg_neg mult_neg_pos mult_pos_neg
                                                zero_le_mult_iff mult_le_0_iff)

lemma aval_sign_sound:
  "(\<forall>x. s x \<in> gamma_sign (\<sigma> x))
   \<Longrightarrow> aval a s \<in> gamma_sign (aval_sign a \<sigma>)"
  by (induction a arbitrary: s \<sigma>;
      simp add: sign_of_int_gamma sign_plus_sound sign_minus_sound sign_times_sound)

lemma sign_plus_mono1:
  "a1 \<le> a2 \<Longrightarrow> a1 + b \<le> a2 + (b::sign)"
  unfolding less_eq_sign_def
  by (cases a1; cases a2; cases b; simp)

lemma sign_plus_mono2:
  "b1 \<le> b2 \<Longrightarrow> a + b1 \<le> a + (b2::sign)"
  unfolding less_eq_sign_def
  by (cases a; cases b1; cases b2; simp)

lemma sign_minus_mono1:
  "a1 \<le> a2 \<Longrightarrow> a1 - b \<le> a2 - (b::sign)"
  unfolding less_eq_sign_def
  by (cases a1; cases a2; cases b; simp)

lemma sign_minus_mono2:
  "b1 \<le> b2 \<Longrightarrow> a - b1 \<le> a - (b2::sign)"
  unfolding less_eq_sign_def
  by (cases a; cases b1; cases b2; simp)

lemma sign_times_mono1:
  "a1 \<le> a2 \<Longrightarrow> a1 * b \<le> a2 * (b::sign)"
  unfolding less_eq_sign_def
  by (cases a1; cases a2; cases b; simp)

lemma sign_times_mono2:
  "b1 \<le> b2 \<Longrightarrow> a * b1 \<le> a * (b2::sign)"
  unfolding less_eq_sign_def

  by (cases a; cases b1; cases b2; simp)
lemma sign_plus_combine_mono:
  "\<lbrakk>a1 \<le> a2; b1 \<le> b2\<rbrakk> \<Longrightarrow> a1 + b1 \<le> a2 + (b2::sign)"
  by (meson order.trans sign_plus_mono1 sign_plus_mono2)

lemma aval_sign_mono:
  "sigma1 \<le> sigma2 \<Longrightarrow> aval_sign a sigma1 \<le> aval_sign a sigma2"
  apply (induction a arbitrary: sigma1 sigma2)
  apply(auto simp add: sign_plus_combine_mono le_funD)
  apply (meson order.trans sign_minus_mono1 sign_minus_mono2)
  by (meson dual_order.trans sign_times_mono1 sign_times_mono2)

end
