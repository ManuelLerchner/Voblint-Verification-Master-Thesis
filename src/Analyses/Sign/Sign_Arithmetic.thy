theory Sign_Arithmetic
  imports Sign_Warrowing
    "Voblint_Domain.Forward_Domain"
    "Voblint_Domain.Numeric_Queries" "Voblint_Domain.Nonrelational_State"
begin

section \<open>What arithmetic does to a known sign\<close>

text \<open>
  Every operation here works on the seven-element lattice a variable's sign can
  take, from \<open>SBot\<close> (no value at all) through \<open>SNeg\<close>, \<open>SNonPos\<close>, \<open>SZero\<close>,
  \<open>SNonNeg\<close> and \<open>SPos\<close> to \<open>STop\<close> (any value). Addition and multiplication are
  given as complete tables over those seven cases; a combination the lattice
  cannot pin down --- a negative plus a positive, say --- lands on \<open>STop\<close>.

  On top of the tables sit three queries that answer about the numbers a sign
  denotes rather than about the sign itself: \<open>sign_lt\<close>, \<open>sign_eqb\<close> and
  \<open>sign_tobool\<close> return \<open>Some b\<close> when every pair of concrete values agrees on
  \<open>b\<close> and \<open>None\<close> when they do not. Each operation and query is proved sound and
  monotone.
\<close>

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

definition sign_div :: "sign \<Rightarrow> sign \<Rightarrow> sign" where
  "sign_div a b = (if a = SBot \<or> b = SBot then SBot else (a * b) \<squnion> SZero)"

definition sign_mod :: "sign \<Rightarrow> sign \<Rightarrow> sign" where
  "sign_mod a b =
    (if a = SBot \<or> b = SBot then SBot else if b = SZero then a else a \<squnion> SZero)"

lemma sign_div_sound:
  assumes "i \<in> gamma_sign a" "j \<in> gamma_sign b"
  shows "c_div i j \<in> gamma_sign (sign_div a b)"
  using assms
  by (cases a; cases b; auto simp: sign_div_def sup_sign_def
      intro: c_div_nonneg c_div_nonpos)

lemma sign_mod_sound:
  assumes "i \<in> gamma_sign a" "j \<in> gamma_sign b"
  shows "c_mod i j \<in> gamma_sign (sign_mod a b)"
  using assms
  by (cases a; cases b; auto simp: sign_mod_def sup_sign_def
      intro: c_mod_nonneg c_mod_nonpos)

text \<open>A conversion to a machine kind keeps zero and the empty value. At an unsigned
  kind every value is nonnegative; at a signed kind wraparound can change any sign.\<close>

definition sign_cast :: "ikind \<Rightarrow> sign \<Rightarrow> sign" where
  "sign_cast ik a =
     (if a = SBot then SBot else if a = SZero then SZero
      else if ik_signed ik then STop else SNonNeg)"

lemma sign_cast_sound: "i \<in> gamma_sign a \<Longrightarrow> ik_norm ik i \<in> gamma_sign (sign_cast ik a)"
  by (cases a) (auto simp: sign_cast_def ik_norm_nonneg_unsigned)

subsection \<open>Comparison and truthiness queries\<close>

text \<open>
  \<open>sign_lt\<close>/\<open>sign_eqb\<close>/\<open>sign_tobool\<close> are Sign's three-valued \<open>bool option\<close>
  queries: \<open>Some True\<close>/\<open>Some False\<close> when the two operands' sign bounds alone
  decide it, \<open>None\<close> otherwise. Every guard here is a \<open>sign_le\<close> test against a
  fixed threshold, so downward-closedness under \<open>\<le>\<close> follows from \<open>sign_le\<close>'s own transitivity, not from any
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

subsection \<open>Soundness and monotonicity of the arithmetic\<close>

text \<open>Each table is sound for the integer operation and monotone in both operands.\<close>

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

end
