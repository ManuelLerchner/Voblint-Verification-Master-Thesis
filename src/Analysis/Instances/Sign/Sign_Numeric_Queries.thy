theory Sign_Numeric_Queries
  imports Sign_Arithmetic Sign_Backward "Voblint_Core.Abstract_Checks"
begin

section \<open>Sign interpretation of the generic numeric-query interface\<close>

text \<open>
  \<open>abstract_numeric_queries\<close> (\<open>Voblint_Core.Abstract_Checks\<close>) is the reusable
  interface; this theory supplies its Sign instance. None of the four query
  functions is a hand-built table any more: all four are Sign's instance of
  generic derivations in \<open>Voblint_Core.Abstract_Domain\<close> --- \<open>sign_less_true\<close>/
  \<open>sign_less_false\<close> from \<open>derived_less_queries\<close> (read off \<open>inv_less_sign\<close>),
  \<open>sign_eq_true\<close> from \<open>derived_eq_true_from_less\<close> (read off \<open>sign_less_false\<close>
  in both directions), and \<open>sign_eq_false\<close> from \<open>derived_eq_false_from_meet\<close>
  (read off \<open>meet_sign\<close> collapsing to \<open>SBot\<close>) --- through the \<open>sublocale\<close>
  chain every \<open>backward_domain\<close> instance carries, with no extra proof
  obligation. Exhaustive case analysis over the seven-element lattice confirms
  each derived pair classifies exactly the pairs a hand-written table would.
\<close>

subsection \<open>Comparison judgments\<close>

text \<open>
  \<open>sign_less_true a b\<close> holds when every concrete pair \<open>i \<in> gamma_sign a\<close>,
  \<open>j \<in> gamma_sign b\<close> satisfies \<open>i < j\<close>; \<open>sign_less_false a b\<close> when every such
  pair satisfies \<open>\<not> i < j\<close>. The two are not complements of each other:
  overlapping abstractions (e.g. \<open>SNonPos\<close> against \<open>SNonNeg\<close>) make both false,
  meaning unknown. \<open>SBot\<close> on either side makes both vacuously true.
\<close>

definition sign_less_true :: "sign \<Rightarrow> sign \<Rightarrow> bool" where
  "sign_less_true = sign_less_true_of_inv"

lemma sign_less_true_sound:
  assumes "sign_less_true a b" and "i \<in> gamma_sign a" and "j \<in> gamma_sign b"
  shows "i < j"
proof -
  have "i \<in> gamma a" and "j \<in> gamma b" using assms by simp_all
  then show ?thesis
    using assms(1) unfolding sign_less_true_def
    by (blast intro: sign_backward_domain.less_true_sound)
qed

definition sign_less_false :: "sign \<Rightarrow> sign \<Rightarrow> bool" where
  "sign_less_false = sign_less_false_of_inv"

lemma sign_less_false_sound:
  assumes "sign_less_false a b" and "i \<in> gamma_sign a" and "j \<in> gamma_sign b"
  shows "\<not> i < j"
proof -
  have "i \<in> gamma a" and "j \<in> gamma b" using assms by simp_all
  then show ?thesis
    using assms(1) unfolding sign_less_false_def
    using sign_backward_domain.less_false_sound by blast
qed

lemma sign_less_true_eq: "sign_less_true a b \<longleftrightarrow>
  (fst (inv_less_sign False a b) = SBot \<or> snd (inv_less_sign False a b) = SBot)"
  by (cases a; cases b;
      simp add: sign_less_true_def sign_backward_domain.less_true_def
                inv_less_sign.simps bot_sign_def)

lemma sign_less_false_eq: "sign_less_false a b \<longleftrightarrow>
  (fst (inv_less_sign True a b) = SBot \<or> snd (inv_less_sign True a b) = SBot)"
  by (cases a; cases b;
      simp add: sign_less_false_def sign_backward_domain.less_false_def
                inv_less_sign.simps bot_sign_def)

subsection \<open>Equality judgments\<close>

text \<open>Only \<open>SZero\<close> concretizes to a singleton, so equality is provable exactly
  there; two abstractions are provably unequal exactly when their
  concretizations are disjoint. Neither table is hand-built: \<open>sign_eq_true\<close>
  is Sign's instance of \<open>derived_eq_true_from_less\<close> (\<open>Voblint_Core.Abstract_Domain\<close>),
  read off \<open>sign_less_false\<close> in both directions (integer trichotomy);
  \<open>sign_eq_false\<close> is Sign's instance of \<open>derived_eq_false_from_meet\<close>, read off
  \<open>meet_sign\<close> collapsing to \<open>SBot\<close> (disjoint concretizations). Both sublocale
  under \<open>backward_domain\<close> with no extra proof obligation, and exhaustive case
  analysis over the seven-element lattice confirms each classifies exactly the
  pairs a hand-written table would.\<close>

definition sign_eq_true :: "sign \<Rightarrow> sign \<Rightarrow> bool" where
  "sign_eq_true = sign_eq_true_of_less"

lemma sign_eq_true_eq: "sign_eq_true a b \<longleftrightarrow> (sign_less_false a b \<and> sign_less_false b a)"
  using sign_backward_domain.eq_true_def sign_eq_true_def sign_eq_true_of_less_def
    sign_less_false_def sign_less_false_of_inv_def by auto

lemma sign_eq_true_sound:
  assumes "sign_eq_true a b" and "i \<in> gamma_sign a" and "j \<in> gamma_sign b"
  shows "i = j"
proof -
  have lf1: "sign_less_false a b" and lf2: "sign_less_false b a"
    using assms(1) unfolding sign_eq_true_eq by auto
  have n1: "\<not> i < j" using sign_less_false_sound[OF lf1 assms(2) assms(3)] .
  have n2: "\<not> j < i" using sign_less_false_sound[OF lf2 assms(3) assms(2)] .
  from n1 n2 show ?thesis by linarith
qed

definition sign_eq_false :: "sign \<Rightarrow> sign \<Rightarrow> bool" where
  "sign_eq_false = sign_eq_false_of_meet"

lemma sign_eq_false_eq: "sign_eq_false a b \<longleftrightarrow> meet_sign a b = SBot"
  by (cases a; cases b;
      simp add: sign_eq_false_def sign_backward_domain.eq_false_def bot_sign_def)

lemma sign_eq_false_sound:
  assumes "sign_eq_false a b" and "i \<in> gamma_sign a" and "j \<in> gamma_sign b"
  shows "i \<noteq> j"
proof
  assume heq: "i = j"
  have hia: "i \<in> gamma_sign a" using assms(2) .
  have hib: "i \<in> gamma_sign b" using assms(3) heq by simp
  have "i \<in> gamma_sign (meet_sign a b)" using meet_sign_sound[OF hia hib] .
  moreover have "meet_sign a b = SBot" using assms(1) sign_eq_false_eq by blast
  ultimately show False by simp
qed


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
