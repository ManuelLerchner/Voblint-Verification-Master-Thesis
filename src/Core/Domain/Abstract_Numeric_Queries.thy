theory Abstract_Numeric_Queries
  imports Abstract_Domain
begin

section \<open>Derived less-queries from backward inversion\<close>

text \<open>
  Any @{locale backward_domain} instance already proves \<open>inv_less_sound\<close>, so it can
  answer \<open>less_true\<close>/\<open>less_false\<close> --- entailment/refutation of \<open><\<close> over two atomic
  values --- for free: narrowing under the assumed truth value collapses to \<open>bot\<close>
  exactly when no witness pair could have satisfied that assumption, by \<open>gamma_bot\<close>.
  Kept as its own locale, separate from @{locale backward_domain} itself, so a domain
  with only \<open>inv_less\<close> (no \<open>intersect\<close>/\<open>aval_abs\<close>/\<open>inv_plus\<close>/\<open>inv_minus\<close>/\<open>inv_times\<close>)
  could still interpret it; @{locale backward_domain} picks it up automatically through
  the \<open>sublocale\<close> declaration below, with no extra proof obligation. Like
  @{locale backward_domain} itself, \<open>gamma\<close> is the @{class sound_domain} class
  operation here, not a separate locale parameter, so \<open>gamma_bot\<close> applies directly
  without an extra premise. \<open>bfilter\<close>'s own \<open>Eq\<close> case narrows through \<open>inv_eq\<close>
  directly (both branches), a separate backward-narrowing operator from the
  boolean query interface here; \<open>eq_true\<close>/\<open>eq_false\<close> are derived below from
  \<open>less_false\<close> and \<open>intersect\<close> instead, not from \<open>inv_less\<close> or \<open>inv_eq\<close>.
\<close>

locale derived_less_queries =
  fixes inv_less :: "bool \<Rightarrow> 'a::sound_domain \<Rightarrow> 'a \<Rightarrow> 'a * 'a"
  assumes derived_inv_less_sound[intro]:
    "n1 \<in> gamma a1 \<Longrightarrow> n2 \<in> gamma a2 \<Longrightarrow> (n1 < n2) = res
     \<Longrightarrow> n1 \<in> gamma (fst (inv_less res a1 a2)) \<and> n2 \<in> gamma (snd (inv_less res a1 a2))"
begin

definition less_true :: "'a \<Rightarrow> 'a \<Rightarrow> bool" where
  "less_true a b \<longleftrightarrow> fst (inv_less False a b) = bot \<or> snd (inv_less False a b) = bot"

definition less_false :: "'a \<Rightarrow> 'a \<Rightarrow> bool" where
  "less_false a b \<longleftrightarrow> fst (inv_less True a b) = bot \<or> snd (inv_less True a b) = bot"

lemma less_true_sound:
  assumes "less_true a b" and "i \<in> gamma a" and "j \<in> gamma b"
  shows "i < j"
proof (rule ccontr)
  assume "\<not> i < j"
  then have "i \<in> gamma (fst (inv_less False a b)) \<and> j \<in> gamma (snd (inv_less False a b))"
    using derived_inv_less_sound[OF assms(2,3)] by simp
  then show False using assms(1) gamma_bot unfolding less_true_def by auto
qed

lemma less_false_sound:
  assumes "less_false a b" and "i \<in> gamma a" and "j \<in> gamma b"
  shows "\<not> i < j"
proof
  assume "i < j"
  then have "i \<in> gamma (fst (inv_less True a b)) \<and> j \<in> gamma (snd (inv_less True a b))"
    using derived_inv_less_sound[OF assms(2,3)] by simp
  then show False using assms(1) gamma_bot unfolding less_false_def by auto
qed

end

text \<open>
  Every @{locale backward_domain} instance --- and every existing @{command
  global_interpretation} of it --- inherits \<open>less_true\<close>/\<open>less_false\<close> and their
  soundness through this sublocale, with no restated proof obligation: the only
  premise, \<open>inv_less_sound\<close>, is already an assumption of @{locale backward_domain}.
\<close>

sublocale backward_domain \<subseteq> derived_less_queries inv_less
  by unfold_locales (rule inv_less_sound)

section \<open>Derived equality queries\<close>

text \<open>
  Two independent derivations, not one shared mechanism: entailment
  (\<open>eq_true\<close>) and refutation (\<open>eq_false\<close>) of \<open>=\<close> come from different existing
  capabilities and are proved in separate locales.

  \<open>eq_true\<close> follows from \<open>less_false\<close> alone, via integer trichotomy: if every
  pair is provably \<open>\<not> i < j\<close> and every pair is provably \<open>\<not> j < i\<close>, every pair
  is \<open>i = j\<close>. This needs nothing beyond \<open>derived_less_queries\<close>'s own
  \<open>less_false_sound\<close>, so \<open>derived_eq_true_from_less\<close> sublocales under it
  directly with no new premise.

  \<open>eq_false\<close> follows from \<open>intersect\<close>, via the same \<open>intersect_sound\<close>/\<open>gamma_bot\<close> pair
  \<open>backward_domain\<close> already assumes for narrowing: if intersection yields
  \<open>bot\<close>, any common witness would belong to its empty concretization.
  \<open>derived_eq_false_from_intersection\<close> sublocales under \<open>backward_domain\<close>
  directly, reusing its \<open>intersect_sound\<close> premise.

  Both locales fix their own capability rather than re-fixing \<open>inv_less\<close> or
  \<open>intersect\<close> as \<open>backward_domain\<close> does, so a domain with only one of these
  operations --- a raw \<open>less_false\<close> query, or a raw \<open>intersect\<close> --- could still
  interpret the matching locale on its own.
\<close>

locale derived_eq_true_from_less =
  fixes less_false :: "'a::sound_domain \<Rightarrow> 'a \<Rightarrow> bool"
  assumes less_false_sound_for_eq[intro]:
    "less_false a b \<Longrightarrow> i \<in> gamma a \<Longrightarrow> j \<in> gamma b \<Longrightarrow> \<not> i < j"
begin

definition eq_true :: "'a \<Rightarrow> 'a \<Rightarrow> bool" where
  "eq_true a b \<longleftrightarrow> less_false a b \<and> less_false b a"

lemma eq_true_sound:
  assumes "eq_true a b" and "i \<in> gamma a" and "j \<in> gamma b"
  shows "i = j"
proof -
  have lf_ab: "less_false a b" and lf_ba: "less_false b a"
    using assms(1) unfolding eq_true_def by auto
  have n1: "\<not> i < j" using less_false_sound_for_eq[OF lf_ab assms(2) assms(3)] .
  have n2: "\<not> j < i" using less_false_sound_for_eq[OF lf_ba assms(3) assms(2)] .
  from n1 n2 show ?thesis by linarith
qed

end

sublocale derived_less_queries \<subseteq> derived_eq_true_from_less less_false
  by unfold_locales (rule less_false_sound)

locale derived_eq_false_from_intersection =
  fixes intersect :: "'a::sound_domain \<Rightarrow> 'a \<Rightarrow> 'a"
  assumes intersect_sound_for_eq[intro]:
    "n \<in> gamma a \<Longrightarrow> n \<in> gamma b \<Longrightarrow> n \<in> gamma (intersect a b)"
begin

definition eq_false :: "'a \<Rightarrow> 'a \<Rightarrow> bool" where
  "eq_false a b \<longleftrightarrow> intersect a b = bot"

lemma eq_false_sound:
  assumes "eq_false a b" and "i \<in> gamma a" and "j \<in> gamma b"
  shows "i \<noteq> j"
proof
  assume heq: "i = j"
  have hia: "i \<in> gamma a" using assms(2) .
  have hib: "i \<in> gamma b" using assms(3) heq by simp
  have "i \<in> gamma (intersect a b)" using intersect_sound_for_eq[OF hia hib] .
  moreover have "intersect a b = bot" using assms(1) unfolding eq_false_def .
  ultimately have "i \<in> gamma (bot :: 'a)" by simp
  then show False using gamma_bot by auto
qed

end

sublocale backward_domain \<subseteq> derived_eq_false_from_intersection intersect
  by unfold_locales (rule intersect_sound)

section \<open>Generic numeric relational queries\<close>

text \<open>
  Entailment/refutation of \<open><\<close>/\<open>=\<close> over an abstract numeric value is not
  check-specific: it is the same question a backward/guard domain answers,
  phrased as a query instead of a narrowing. Kept as its own locale, separate
  from expression abstraction and separate from the Boolean layer, so a
  domain that only has these four operations (no \<open>exp\<close>/\<open>store\<close> concept at
  all) could still interpret it. @{locale backward_domain}
  (\<^theory>\<open>Voblint_Core.Abstract_Domain\<close>) refines an abstract value under an
  assumed truth value; this locale instead classifies an already-fixed pair
  of values as provably related or provably unrelated. The derivations above
  read the four functions off any @{locale backward_domain} instance's own
  narrowing operators as a sound default --- a concrete domain interprets
  this locale explicitly, choosing either that derivation or its own
  sharper, hand-tuned predicates when the generic derivation loses precision
  it cannot recover.
\<close>

locale abstract_numeric_queries =
  fixes gamma_num :: "'a \<Rightarrow> int set"
    and less_true :: "'a \<Rightarrow> 'a \<Rightarrow> bool"
    and less_false :: "'a \<Rightarrow> 'a \<Rightarrow> bool"
    and eq_true :: "'a \<Rightarrow> 'a \<Rightarrow> bool"
    and eq_false :: "'a \<Rightarrow> 'a \<Rightarrow> bool"
  assumes less_true_sound[intro]:
      "less_true a b \<Longrightarrow> i \<in> gamma_num a \<Longrightarrow> j \<in> gamma_num b \<Longrightarrow> i < j"
    and less_false_sound[intro]:
      "less_false a b \<Longrightarrow> i \<in> gamma_num a \<Longrightarrow> j \<in> gamma_num b \<Longrightarrow> \<not> i < j"
    and eq_true_sound[intro]:
      "eq_true a b \<Longrightarrow> i \<in> gamma_num a \<Longrightarrow> j \<in> gamma_num b \<Longrightarrow> i = j"
    and eq_false_sound[intro]:
      "eq_false a b \<Longrightarrow> i \<in> gamma_num a \<Longrightarrow> j \<in> gamma_num b \<Longrightarrow> i \<noteq> j"

end
