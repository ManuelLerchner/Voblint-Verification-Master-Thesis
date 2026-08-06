theory Sign_Numeric_Queries
  imports Sign_Arithmetic "Voblint_Core.Abstract_Checks"
begin

section \<open>Sign interpretation of the generic numeric-query interface\<close>

text \<open>
  These four tables are Sign-specific facts about the seven-element sign
  lattice, not generic reasoning: \<open>abstract_numeric_queries\<close>
  (\<open>Voblint_Core.Abstract_Checks\<close>) is the reusable interface, this theory
  supplies its Sign instance.
\<close>

subsection \<open>Comparison judgments\<close>

text \<open>
  \<open>sign_less_true a b\<close> holds when every concrete pair \<open>i \<in> gamma_sign a\<close>,
  \<open>j \<in> gamma_sign b\<close> satisfies \<open>i < j\<close>; \<open>sign_less_false a b\<close> when every such
  pair satisfies \<open>\<not> i < j\<close>. The two tables are not complements of each other:
  overlapping abstractions (e.g. \<open>SNonPos\<close> against \<open>SNonNeg\<close>) make both false,
  meaning unknown. \<open>SBot\<close> on either side makes both vacuously true.
\<close>

fun sign_less_true :: "sign \<Rightarrow> sign \<Rightarrow> bool" where
    "sign_less_true SBot _ = True"
  | "sign_less_true _ SBot = True"
  | "sign_less_true SNeg SZero = True"
  | "sign_less_true SNeg SNonNeg = True"
  | "sign_less_true SNeg SPos = True"
  | "sign_less_true SNonPos SPos = True"
  | "sign_less_true SZero SPos = True"
  | "sign_less_true _ _ = False"

lemma sign_less_true_sound:
  assumes "sign_less_true a b" and "i \<in> gamma_sign a" and "j \<in> gamma_sign b"
  shows "i < j"
  using assms by (induction a b rule: sign_less_true.induct) auto

fun sign_less_false :: "sign \<Rightarrow> sign \<Rightarrow> bool" where
    "sign_less_false SBot _ = True"
  | "sign_less_false _ SBot = True"
  | "sign_less_false SZero SNeg = True"
  | "sign_less_false SZero SNonPos = True"
  | "sign_less_false SZero SZero = True"
  | "sign_less_false SNonNeg SNeg = True"
  | "sign_less_false SNonNeg SNonPos = True"
  | "sign_less_false SNonNeg SZero = True"
  | "sign_less_false SPos SNeg = True"
  | "sign_less_false SPos SNonPos = True"
  | "sign_less_false SPos SZero = True"
  | "sign_less_false _ _ = False"

lemma sign_less_false_sound:
  assumes "sign_less_false a b" and "i \<in> gamma_sign a" and "j \<in> gamma_sign b"
  shows "\<not> i < j"
  using assms by (induction a b rule: sign_less_false.induct) auto

text \<open>Only \<open>SZero\<close> concretizes to a singleton, so equality is provable exactly
  there; two abstractions are provably unequal exactly when their
  concretizations are disjoint.\<close>

fun sign_eq_true :: "sign \<Rightarrow> sign \<Rightarrow> bool" where
    "sign_eq_true SBot _ = True"
  | "sign_eq_true _ SBot = True"
  | "sign_eq_true SZero SZero = True"
  | "sign_eq_true _ _ = False"

lemma sign_eq_true_sound:
  assumes "sign_eq_true a b" and "i \<in> gamma_sign a" and "j \<in> gamma_sign b"
  shows "i = j"
  using assms by (induction a b rule: sign_eq_true.induct) auto

fun sign_eq_false :: "sign \<Rightarrow> sign \<Rightarrow> bool" where
    "sign_eq_false SBot _ = True"
  | "sign_eq_false _ SBot = True"
  | "sign_eq_false SNeg SNonNeg = True"
  | "sign_eq_false SNonNeg SNeg = True"
  | "sign_eq_false SNeg SZero = True"
  | "sign_eq_false SZero SNeg = True"
  | "sign_eq_false SNeg SPos = True"
  | "sign_eq_false SPos SNeg = True"
  | "sign_eq_false SNonPos SPos = True"
  | "sign_eq_false SPos SNonPos = True"
  | "sign_eq_false SZero SPos = True"
  | "sign_eq_false SPos SZero = True"
  | "sign_eq_false _ _ = False"

lemma sign_eq_false_sound:
  assumes "sign_eq_false a b" and "i \<in> gamma_sign a" and "j \<in> gamma_sign b"
  shows "i \<noteq> j"
  using assms by (induction a b rule: sign_eq_false.induct) auto

subsection \<open>Interpreting the generic numeric-query interface\<close>

global_interpretation sign_numeric_queries:
  abstract_numeric_queries gamma_sign sign_less_true sign_less_false sign_eq_true sign_eq_false
proof unfold_locales
  fix a b :: sign and i j :: int
  assume "sign_less_true a b" and "i \<in> gamma_sign a" and "j \<in> gamma_sign b"
  then show "i < j" using sign_less_true_sound by blast
next
  fix a b :: sign and i j :: int
  assume "sign_less_false a b" and "i \<in> gamma_sign a" and "j \<in> gamma_sign b"
  then show "\<not> i < j" using sign_less_false_sound by blast
next
  fix a b :: sign and i j :: int
  assume "sign_eq_true a b" and "i \<in> gamma_sign a" and "j \<in> gamma_sign b"
  then show "i = j" using sign_eq_true_sound by blast
next
  fix a b :: sign and i j :: int
  assume "sign_eq_false a b" and "i \<in> gamma_sign a" and "j \<in> gamma_sign b"
  then show "i \<noteq> j" using sign_eq_false_sound by blast
qed

end
