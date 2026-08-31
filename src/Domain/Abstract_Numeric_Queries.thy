theory Abstract_Numeric_Queries
  imports Backward_Domain
begin

section \<open>Numeric relational query interface\<close>

text \<open>
  Entailment/refutation of \<open><\<close>/\<open>=\<close> over an abstract numeric value is not
  check-specific: it is the same question a backward/guard domain answers,
  phrased as a query instead of a narrowing. \<open>less\<close>/\<open>eq\<close> package that answer
  in Goblint's own shape -- \<open>ID.lt\<close>/\<open>ID.eq\<close> -- a definite \<open>Some True\<close>, a
  definite \<open>Some False\<close>, or \<open>None\<close> when neither direction is provable, the
  same three-way shape \<open>tobool\<close> already gives a single abstract value's
  truthiness.

  Kept as its own locale, separate from expression abstraction, so a domain
  that only has these two operations (no \<open>exp\<close>/\<open>store\<close> concept at all)
  could still interpret it. @{locale backward_domain}
  (\<^theory>\<open>Voblint_Domain.Abstract_Domain\<close>) refines an abstract value under an
  assumed truth value; this locale instead classifies an already-fixed pair
  of values as provably related, provably unrelated, or neither. Every
  @{locale backward_domain} instance gets this for free, below, off its own
  narrowing operators -- a concrete domain interprets this locale explicitly,
  choosing either that derivation or its own sharper, hand-tuned queries when
  the generic derivation loses precision it cannot recover.
\<close>

locale abstract_numeric_queries =
  fixes less :: "'a::sound_domain \<Rightarrow> 'a \<Rightarrow> bool option"
    and eq   :: "'a \<Rightarrow> 'a \<Rightarrow> bool option"
  assumes less_sound[intro]:
      "less a b = Some r \<Longrightarrow> i \<in> gamma a \<Longrightarrow> j \<in> gamma b \<Longrightarrow> (i < j) = r"
    and eq_sound[intro]:
      "eq a b = Some r \<Longrightarrow> i \<in> gamma a \<Longrightarrow> j \<in> gamma b \<Longrightarrow> (i = j) = r"

section \<open>Queries derived from backward inversion\<close>

text \<open>
  Any @{locale backward_domain} instance already proves \<open>inv_less_sound\<close>/
  \<open>intersect_sound\<close>, so it answers entailment/refutation of
  \<open><\<close>/\<open>=\<close> over two atomic values for free: narrowing under an assumed truth
  value yields an @{const is_empty} component only if no represented witness
  pair can satisfy that assumption. Thus emptiness of the inverse result gives
  a sound entailment/refutation test, though an imprecise inverse may still
  answer "unknown" even when the relation is already concrete-semantically
  fixed. Defined directly in @{locale backward_domain}'s own context rather
  than through intermediate capability locales, so every interpretation of
  @{locale backward_domain} -- and every existing @{command global_interpretation}
  of it -- gets these with no restated proof obligation: the premises used
  below are already assumptions of @{locale backward_domain} itself.

  Classification tests @{const is_empty}, not canonical-\<open>bot\<close> equality: a value
  can denote \<open>{}\<close> without being the representation's chosen \<open>bot\<close> element
  (@{class sound_domain}'s whole reason for distinguishing the two), so a
  \<open>= bot\<close> test would under-classify any domain with non-canonical empty
  representations. \<open>less_true\<close>/\<open>less_false\<close>/\<open>eq_true\<close>/\<open>eq_false\<close> stay implementation
  judgments, not the public interface above: a caller after the generic default
  wants \<open>less\<close>/\<open>eq\<close>; these four remain named and proved because
  \<open>Sign_Backward\<close> and \<open>Int_Classify\<close> cite them directly off a concrete
  @{locale backward_domain} interpretation to state that a domain's own
  sharper, hand-tuned query agrees with this generic default.
\<close>

context backward_domain
begin

subsection \<open>Comparison judgments\<close>

definition less_true :: "'a \<Rightarrow> 'a \<Rightarrow> bool" where
  "less_true a b \<longleftrightarrow> is_empty (fst (inv_less False a b)) \<or> is_empty (snd (inv_less False a b))"

definition less_false :: "'a \<Rightarrow> 'a \<Rightarrow> bool" where
  "less_false a b \<longleftrightarrow> is_empty (fst (inv_less True a b)) \<or> is_empty (snd (inv_less True a b))"

lemma less_true_sound:
  assumes "less_true a b" and "i \<in> gamma a" and "j \<in> gamma b"
  shows "i < j"
  using assms inv_less_sound[OF assms(2,3), of False]
  unfolding less_true_def
  by (auto simp: is_empty_correct)

lemma less_false_sound:
  assumes "less_false a b" and "i \<in> gamma a" and "j \<in> gamma b"
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
  assumes "eq_true a b" and "i \<in> gamma a" and "j \<in> gamma b"
  shows "i = j"
  using assms less_false_sound[of a b i j] less_false_sound[of b a j i]
  unfolding eq_true_def
  by fastforce

definition eq_false :: "'a \<Rightarrow> 'a \<Rightarrow> bool" where
  "eq_false a b \<longleftrightarrow> is_empty (intersect a b)"

lemma eq_false_sound:
  assumes "eq_false a b" and "i \<in> gamma a" and "j \<in> gamma b"
  shows "i \<noteq> j"
  using assms intersect_sound
  unfolding eq_false_def
  by (fastforce simp: is_empty_correct)

subsection \<open>Goblint-style optional-Boolean queries\<close>

text \<open>
  \<open>less\<close>/\<open>eq\<close> package the four judgments above into one optional-Boolean
  answer per relation -- not equivalent on witness-bottom operands, where both
  predicates in a pair can hold vacuously and \<open>less\<close>/\<open>eq\<close> pick one answer.
\<close>

definition less :: "'a \<Rightarrow> 'a \<Rightarrow> bool option" where
  "less a b = (if less_true a b then Some True else if less_false a b then Some False else None)"

definition eq :: "'a \<Rightarrow> 'a \<Rightarrow> bool option" where
  "eq a b = (if eq_true a b then Some True else if eq_false a b then Some False else None)"

lemma less_opt_sound:
  assumes "less a b = Some r" and "i \<in> gamma a" and "j \<in> gamma b"
  shows "(i < j) = r"
  using assms less_true_sound less_false_sound unfolding less_def by (auto split: if_splits)

lemma eq_opt_sound:
  assumes "eq a b = Some r" and "i \<in> gamma a" and "j \<in> gamma b"
  shows "(i = j) = r"
  using assms eq_true_sound eq_false_sound unfolding eq_def by (auto split: if_splits)

end

sublocale backward_domain \<subseteq> abstract_numeric_queries less eq
  by unfold_locales (metis less_opt_sound eq_opt_sound)+

end

