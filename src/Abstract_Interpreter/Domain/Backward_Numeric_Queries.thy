theory Backward_Numeric_Queries
  imports Backward_Domain Abstract_Numeric_Queries
begin

section \<open>Queries derived from backward inversion\<close>

text \<open>
  Any @{locale backward_domain} instance already proves \<open>inv_less_sound\<close>/
  \<open>intersect_sound\<close>, so it answers entailment/refutation of
  \<open><\<close>/\<open>=\<close> over two atomic values for free: narrowing under an assumed truth
  value yields an @{const is_empty} component only if no represented witness
  pair can satisfy that assumption. Thus emptiness of the inverse result gives
  a sound entailment/refutation test, though an imprecise inverse may still
  answer "unknown" even when the relation is already concrete-semantically
  fixed. The four judgments are defined directly in
  @{locale backward_domain}'s own context, so every interpretation of it --
  and every existing @{command global_interpretation} of it -- gets them with
  no restated proof obligation: the premises used below are already
  assumptions of @{locale backward_domain} itself. Turning the four into the
  two queries a caller asks for is not backward-specific and is not done
  here: this file ends by interpreting
  \<^locale>\<open>numeric_query_judgments\<close> at them, so every
  @{locale backward_domain} instance is a numeric-query instance too.

  Classification tests @{const is_empty}, not canonical-\<open>bot\<close> equality: a value
  can denote \<open>{}\<close> without being the representation's chosen \<open>bot\<close> element
  (@{class sound_domain}'s whole reason for distinguishing the two), so a
  \<open>= bot\<close> test would under-classify any domain with non-canonical empty
  representations. \<open>less_true\<close>/\<open>less_false\<close>/\<open>eq_true\<close>/\<open>eq_false\<close> stay implementation
  judgments, not the public interface \<^theory>\<open>Voblint_Domain.Abstract_Numeric_Queries\<close>
  gives: a caller after the generic default wants \<open>less\<close>/\<open>eq\<close>; these four
  remain named and proved because \<open>Sign_Backward\<close> and \<open>Int_Classify\<close> cite
  them directly off a concrete @{locale backward_domain} interpretation to
  state that a domain's own sharper, hand-tuned query agrees with this
  generic default.
\<close>

context backward_domain
begin

subsection \<open>Comparison judgments\<close>

text \<open>A comparison is decided by narrowing against its own negation: if refining the two
  values under \<open>\<not> a < b\<close> empties either side, no concrete pair can violate \<open>a < b\<close>, so the
  judgment holds.  Nothing new is assumed of the domain -- the answer comes from the
  narrowing operator it already supplies.\<close>
definition less_true :: "'a \<Rightarrow> 'a \<Rightarrow> bool" where
  "less_true a b \<longleftrightarrow> is_empty (fst (inv_less False a b)) \<or> is_empty (snd (inv_less False a b))"

definition less_false :: "'a \<Rightarrow> 'a \<Rightarrow> bool" where
  "less_false a b \<longleftrightarrow> is_empty (fst (inv_less True a b)) \<or> is_empty (snd (inv_less True a b))"

lemma less_true_sound:
  assumes "less_true a b" and "i \<in> \<gamma> a" and "j \<in> \<gamma> b"
  shows "i < j"
  using assms inv_less_sound[OF assms(2,3), of False]
  unfolding less_true_def
  by (auto simp: is_empty_correct)

lemma less_false_sound:
  assumes "less_false a b" and "i \<in> \<gamma> a" and "j \<in> \<gamma> b"
  shows "\<not> i < j"
  using assms inv_less_sound[OF assms(2,3), of True]
  unfolding less_false_def
  by (auto simp: is_empty_correct)

subsection \<open>Equality judgments\<close>

text \<open>
  Two independent derivations, from different existing capabilities:
  \<open>eq_true\<close> from \<open>less_false\<close> in both directions (integer trichotomy -- if
  every pair is provably \<open>\<not> i < j\<close> and every pair is provably \<open>\<not> j < i\<close>,
  every pair is \<open>i = j\<close>); \<open>eq_false\<close> from \<open>intersect\<close> (a common witness
  would belong to its concretization, so an @{const is_empty} intersection
  rules one out).
\<close>

definition eq_true :: "'a \<Rightarrow> 'a \<Rightarrow> bool" where
  "eq_true a b \<longleftrightarrow> less_false a b \<and> less_false b a"

lemma eq_true_sound:
  assumes "eq_true a b" and "i \<in> \<gamma> a" and "j \<in> \<gamma> b"
  shows "i = j"
  using assms less_false_sound[of a b i j] less_false_sound[of b a j i]
  unfolding eq_true_def
  by fastforce

definition eq_false :: "'a \<Rightarrow> 'a \<Rightarrow> bool" where
  "eq_false a b \<longleftrightarrow> is_empty (intersect a b)"

lemma eq_false_sound:
  assumes "eq_false a b" and "i \<in> \<gamma> a" and "j \<in> \<gamma> b"
  shows "i \<noteq> j"
  using assms intersect_sound
  unfolding eq_false_def
  by (fastforce simp: is_empty_correct)

end

subsection \<open>Packaging the derived judgments\<close>

text \<open>
  The qualifier is mandatory rather than cosmetic: the packaging locale
  assumes the same four soundness statements this context proves, under the
  same four names, so an unqualified registration would try to declare each
  twice in every @{command global_interpretation} of
  @{locale backward_domain}.
\<close>

sublocale backward_domain \<subseteq> queries:
  numeric_query_judgments less_true less_false eq_true eq_false
  by unfold_locales
     (fact less_true_sound, fact less_false_sound, fact eq_true_sound, fact eq_false_sound)

end
