theory Sign_Arithmetic
  imports Sign_Lattice "Voblint_VIMP.VIMP_Expr" Abstract_Arithmetic
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

subsection \<open>Comparison and truthiness queries\<close>

text \<open>
  \<open>sign_lt\<close>/\<open>sign_eqb\<close>/\<open>sign_tobool\<close> are Sign's three-valued \<open>bool option\<close>
  queries for \<open>Voblint_Analysis.Abstract_Arithmetic\<close>'s \<open>expression_domain_sound\<close>
  locale: \<open>Some True\<close>/\<open>Some False\<close> when the two operands' sign bounds alone
  decide it, \<open>None\<close> otherwise. Every guard here is a \<open>sign_le\<close> test against a
  fixed threshold, so downward-closedness under \<open>\<le>\<close> (needed for
  \<open>aval_dom_mono\<close>) follows from \<open>sign_le\<close>'s own transitivity, not from any
  extra reasoning about \<open>SBot\<close>.
\<close>

fun sign_lt :: "sign \<Rightarrow> sign \<Rightarrow> bool option" where
  "sign_lt a b =
     (if sign_le a SNeg \<and> sign_le b SNonNeg then Some True
      else if sign_le a SNonPos \<and> sign_le b SPos then Some True
      else if sign_le b SNonPos \<and> sign_le a SNonNeg then Some False
      else if sign_le b SNeg \<and> sign_le a SPos then Some False
      else None)"

fun sign_eqb :: "sign \<Rightarrow> sign \<Rightarrow> bool option" where
  "sign_eqb a b =
     (if a = SZero \<and> b = SZero then Some True
      else if (sign_le a SNeg \<and> sign_le b SNonNeg) \<or> (sign_le b SNeg \<and> sign_le a SNonNeg)
           \<or> (sign_le a SPos \<and> sign_le b SNonPos) \<or> (sign_le b SPos \<and> sign_le a SNonPos)
      then Some False
      else None)"

fun sign_tobool :: "sign \<Rightarrow> bool option" where
  "sign_tobool a =
     (if sign_le a SNeg \<or> sign_le a SPos then Some True
      else if sign_le a SZero then Some False
      else None)"

lemma sign_lt_sound:
  assumes "sign_lt a b = Some c" and "i \<in> gamma_sign a" and "j \<in> gamma_sign b"
  shows "(i < j) = c"
  using assms unfolding less_eq_sign_def[symmetric]
  by (cases a; cases b; auto split: if_splits)

lemma sign_eqb_sound:
  assumes "sign_eqb a b = Some c" and "i \<in> gamma_sign a" and "j \<in> gamma_sign b"
  shows "(i = j) = c"
  using assms unfolding less_eq_sign_def[symmetric]
  by (cases a; cases b; auto split: if_splits)

lemma sign_tobool_sound:
  assumes "sign_tobool a = Some c" and "i \<in> gamma_sign a"
  shows "(i \<noteq> 0) = c"
  using assms unfolding less_eq_sign_def[symmetric]
  by (cases a; auto split: if_splits)

lemma sign_le_trans_below:
  fixes a1 a2 :: sign
  assumes "sign_le a2 t" and "a1 \<le> a2"
  shows "sign_le a1 t"
  using assms sign_le_trans unfolding less_eq_sign_def
  by blast

lemma sign_lt_mono:
  assumes hp: "\<not> is_bot (a1::sign)" and hq: "\<not> is_bot b1"
      and hab: "a1 \<le> a2" and hbb: "b1 \<le> b2"
      and hwide: "sign_lt a2 b2 = Some c"
  shows "sign_lt a1 b1 = Some c"
proof (cases c)
  case True
  then have "sign_le a2 SNeg \<and> sign_le b2 SNonNeg \<or> sign_le a2 SNonPos \<and> sign_le b2 SPos"
    using hwide by (auto split: if_splits)
  then have "sign_le a1 SNeg \<and> sign_le b1 SNonNeg \<or> sign_le a1 SNonPos \<and> sign_le b1 SPos"
    using sign_le_trans_below[OF _ hab] sign_le_trans_below[OF _ hbb] by blast
  then show ?thesis using True by auto
next
  case False
  then have "sign_le b2 SNonPos \<and> sign_le a2 SNonNeg \<or> sign_le b2 SNeg \<and> sign_le a2 SPos"
    using hwide by (auto split: if_splits)
  then have hyp: "sign_le b1 SNonPos \<and> sign_le a1 SNonNeg \<or> sign_le b1 SNeg \<and> sign_le a1 SPos"
    using sign_le_trans_below[OF _ hab] sign_le_trans_below[OF _ hbb] by blast
  show ?thesis using hyp False hp hq unfolding is_bot_sign is_bottom_sign_def
    by (cases a1; cases b1; auto)
qed

lemma sign_eqb_mono:
  assumes hp: "\<not> is_bot (a1::sign)" and hq: "\<not> is_bot b1"
      and hab: "a1 \<le> a2" and hbb: "b1 \<le> b2"
      and hwide: "sign_eqb a2 b2 = Some c"
  shows "sign_eqb a1 b1 = Some c"
proof (cases c)
  case True
  then have "a2 = SZero \<and> b2 = SZero" using hwide by (auto split: if_splits)
  then have "sign_le a2 SZero" and "sign_le b2 SZero"
    unfolding less_eq_sign_def[symmetric] by simp_all
  then have hle1: "sign_le a1 SZero" and hle2: "sign_le b1 SZero"
    using sign_le_trans_below[OF _ hab] sign_le_trans_below[OF _ hbb] by blast+
  have ha1: "a1 = SBot \<or> a1 = SZero" using hle1 by (cases a1) auto
  have hb1: "b1 = SBot \<or> b1 = SZero" using hle2 by (cases b1) auto
  show ?thesis using True hp hq ha1 hb1 unfolding is_bot_sign is_bottom_sign_def by auto
next
next
  case False
  then have "sign_le a2 SNeg \<and> sign_le b2 SNonNeg \<or> sign_le b2 SNeg \<and> sign_le a2 SNonNeg
             \<or> sign_le a2 SPos \<and> sign_le b2 SNonPos \<or> sign_le b2 SPos \<and> sign_le a2 SNonPos"
    using hwide by (auto split: if_splits)
  then have "sign_le a1 SNeg \<and> sign_le b1 SNonNeg \<or> sign_le b1 SNeg \<and> sign_le a1 SNonNeg
             \<or> sign_le a1 SPos \<and> sign_le b1 SNonPos \<or> sign_le b1 SPos \<and> sign_le a1 SNonPos"
    using sign_le_trans_below[OF _ hab] sign_le_trans_below[OF _ hbb] by blast
  then show ?thesis using False by auto
qed

lemma sign_tobool_mono:
  assumes "\<not> is_bot (a1::sign)" and "a1 \<le> a2" and "sign_tobool a2 = Some c"
  shows "sign_tobool a1 = Some c"
  using assms unfolding is_bot_sign is_bottom_sign_def
  by (cases a1; cases a2; auto simp: less_eq_sign_def split: if_splits)

subsection \<open>Abstract expression evaluation\<close>

fun aval_sign :: "exp => (vname => sign) => sign" where
    "aval_sign (N n)        \<sigma> = sign_of_int n"
  | "aval_sign (V x)        \<sigma> = \<sigma> x"
  | "aval_sign (Plus  a b)  \<sigma> = aval_sign a \<sigma> + aval_sign b \<sigma>"
  | "aval_sign (Minus a b)  \<sigma> = aval_sign a \<sigma> - aval_sign b \<sigma>"
  | "aval_sign (Times a b)  \<sigma> = aval_sign a \<sigma> * aval_sign b \<sigma>"
  | "aval_sign (Less a b)   \<sigma> =
       (if is_bot (aval_sign a \<sigma>) \<or> is_bot (aval_sign b \<sigma>) then bot
        else if sign_lt (aval_sign a \<sigma>) (aval_sign b \<sigma>) = Some True then SPos
        else if sign_lt (aval_sign a \<sigma>) (aval_sign b \<sigma>) = Some False then SZero
        else SNonNeg)"
  | "aval_sign (exp.Eq a b) \<sigma> =
       (if is_bot (aval_sign a \<sigma>) \<or> is_bot (aval_sign b \<sigma>) then bot
        else if sign_eqb (aval_sign a \<sigma>) (aval_sign b \<sigma>) = Some True then SPos
        else if sign_eqb (aval_sign a \<sigma>) (aval_sign b \<sigma>) = Some False then SZero
        else SNonNeg)"
  | "aval_sign (exp.Not a)  \<sigma> =
       (if is_bot (aval_sign a \<sigma>) then bot
        else if sign_tobool (aval_sign a \<sigma>) = Some True then SZero
        else if sign_tobool (aval_sign a \<sigma>) = Some False then SPos
        else SNonNeg)"
  | "aval_sign (And a b)    \<sigma> =
       (if is_bot (aval_sign a \<sigma>) \<or> is_bot (aval_sign b \<sigma>) then bot
        else if sign_tobool (aval_sign a \<sigma>) = Some False \<or> sign_tobool (aval_sign b \<sigma>) = Some False
        then SZero
        else if sign_tobool (aval_sign a \<sigma>) = Some True \<and> sign_tobool (aval_sign b \<sigma>) = Some True
        then SPos
        else SNonNeg)"
  | "aval_sign (Or a b)     \<sigma> =
       (if is_bot (aval_sign a \<sigma>) \<or> is_bot (aval_sign b \<sigma>) then bot
        else if sign_tobool (aval_sign a \<sigma>) = Some True \<or> sign_tobool (aval_sign b \<sigma>) = Some True
        then SPos
        else if sign_tobool (aval_sign a \<sigma>) = Some False \<and> sign_tobool (aval_sign b \<sigma>) = Some False
        then SZero
        else SNonNeg)"

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

lemma sign_minus_combine_mono:
  "\<lbrakk>a1 \<le> a2; b1 \<le> b2\<rbrakk> \<Longrightarrow> a1 - b1 \<le> a2 - (b2::sign)"
  by (meson order.trans sign_minus_mono1 sign_minus_mono2)

lemma sign_times_combine_mono:
  "\<lbrakk>a1 \<le> a2; b1 \<le> b2\<rbrakk> \<Longrightarrow> a1 * b1 \<le> a2 * (b2::sign)"
  by (meson order.trans sign_times_mono1 sign_times_mono2)

interpretation sign_arith: expression_domain_sound
    aval_sign sign_of_int sign_lt sign_eqb sign_tobool
  apply unfold_locales
  apply (simp_all add: sign_of_int_gamma sign_plus_sound sign_minus_sound sign_times_sound
                        sign_plus_combine_mono sign_minus_combine_mono sign_times_combine_mono
                        sign_lt_sound sign_eqb_sound sign_tobool_sound[unfolded truthy_def]
                        sup_sign_def join_sign.simps truthy_def
                    del: sign_lt.simps sign_eqb.simps sign_tobool.simps)
  apply (blast intro: sign_lt_mono[unfolded is_bot_sign])
  apply (blast intro: sign_eqb_mono[unfolded is_bot_sign])
  apply (blast intro: sign_tobool_mono[unfolded is_bot_sign])
  done

lemmas aval_sign_sound = sign_arith.aval_dom_sound[unfolded gamma_abs_sign]
lemmas aval_sign_mono = sign_arith.aval_dom_mono

end
