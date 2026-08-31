theory Parity_Numeric_Queries
  imports Parity_Domain "Voblint_Domain.Abstract_Numeric_Queries"
begin

section \<open>Parity interpretation of the generic numeric-query interface\<close>

text \<open>
  Third-domain validation for \<open>abstract_numeric_queries\<close>
  (\<^theory>\<open>Voblint_Domain.Abstract_Numeric_Queries\<close>), hand-tuned like
  Voblint_Analysis.Interval_Numeric_Queries rather than derived through
  \<open>backward_domain\<close>: parity has no \<open>inv_less\<close>/\<open>meet\<close> instance (guards do not
  refine parity, \<^theory>\<open>Voblint_Analysis.Parity_Domain\<close>), so there is nothing for
  the generic derivations to read off. Parity carries no order information at
  all, so \<open>parity_less_true\<close>/\<open>parity_less_false\<close> are provable only in the
  vacuous case (one side \<open>PBot\<close>); every genuine pair is unknown. \<open>PBot\<close> is the
  lattice's unique empty representative (unlike Interval's raw \<open>ivl\<close> type,
  which has infinitely many non-canonical empty representations), so the
  vacuous case is a single clean equality test, as for Sign's \<open>SBot\<close>.
\<close>

subsection \<open>Comparison judgments: vacuous only\<close>

text \<open>
  \<open>parity_less_true a b\<close>/\<open>parity_less_false a b\<close> both hold exactly when one
  side concretizes to nothing: neither judgment can ever be established from
  parity alone, since knowing a value's evenness says nothing about its order
  against another value's evenness. The two coincide definitionally --- both
  are the same vacuity test --- which is itself the content of the "usually
  unknown" fact about Parity's order queries.
\<close>

definition parity_vacuous :: "parity \<Rightarrow> parity \<Rightarrow> bool" where
  "parity_vacuous a b \<longleftrightarrow> (a = PBot \<or> b = PBot)"

definition parity_less_true :: "parity \<Rightarrow> parity \<Rightarrow> bool" where
  "parity_less_true = parity_vacuous"

definition parity_less_false :: "parity \<Rightarrow> parity \<Rightarrow> bool" where
  "parity_less_false = parity_vacuous"

lemma parity_less_true_sound:
  assumes "parity_less_true a b" and "i \<in> gamma_parity a" and "j \<in> gamma_parity b"
  shows "i < j"
  using assms unfolding parity_less_true_def parity_vacuous_def by (cases a; cases b; auto)

lemma parity_less_false_sound:
  assumes "parity_less_false a b" and "i \<in> gamma_parity a" and "j \<in> gamma_parity b"
  shows "\<not> i < j"
  using assms unfolding parity_less_false_def parity_vacuous_def by (cases a; cases b; auto)

subsection \<open>Equality judgments\<close>

text \<open>
  \<open>parity_eq_true\<close> is vacuous-only for the same reason as the order queries:
  no parity class concretizes to a singleton (unlike Sign's \<open>SZero\<close> or an
  Interval point interval), so no non-vacuous pair is ever provably equal.
  \<open>parity_eq_true a b\<close> asks provable equality of every witness pair, so a
  reflexive-looking check such as \<open>x == x\<close> is \<^emph>\<open>not\<close> classified true by this
  interface either: \<open>aval_abs\<close> only ever hands both sides the same
  \<^emph>\<open>abstract\<close> value \<open>PEven\<close>/\<open>POdd\<close>/\<open>PTop\<close>, which still ranges over
  infinitely many concrete integers, so \<open>eq_true\<close> stays false there too ---
  correctly: this classification layer never assumes two occurrences of the
  same syntactic expression carry a hidden equality constraint.

  \<open>parity_eq_true\<close> is genuinely provable to be true for identical parity
  classes when combined at the check level with the compiler-independent
  evaluator; this file states it as it is, no more.
\<close>

definition parity_eq_true :: "parity \<Rightarrow> parity \<Rightarrow> bool" where
  "parity_eq_true = parity_vacuous"

lemma parity_eq_true_sound:
  assumes "parity_eq_true a b" and "i \<in> gamma_parity a" and "j \<in> gamma_parity b"
  shows "i = j"
  using assms unfolding parity_eq_true_def parity_vacuous_def by (cases a; cases b; auto)

text \<open>
  \<open>parity_eq_false\<close> is where parity earns its keep: two values of disjoint
  parity classes --- one \<open>PEven\<close>, the other \<open>POdd\<close> --- can never be equal,
  regardless of how imprecise Sign or Interval are about the same pair (both
  may see fully overlapping sign/range information). This is the one query
  Parity answers strictly better than a vacuity check.
\<close>

fun parity_eq_false :: "parity \<Rightarrow> parity \<Rightarrow> bool" where
    "parity_eq_false PEven POdd = True"
  | "parity_eq_false POdd PEven = True"
  | "parity_eq_false a b = (a = PBot \<or> b = PBot)"

lemma parity_eq_false_sound:
  assumes "parity_eq_false a b" and "i \<in> gamma_parity a" and "j \<in> gamma_parity b"
  shows "i \<noteq> j"
  using assms by (cases a; cases b; auto)

subsection \<open>Goblint-style optional-Boolean queries\<close>

definition parity_less :: "parity \<Rightarrow> parity \<Rightarrow> bool option" where
  "parity_less a b = (if parity_less_true a b then Some True
                       else if parity_less_false a b then Some False else None)"

definition parity_eq :: "parity \<Rightarrow> parity \<Rightarrow> bool option" where
  "parity_eq a b = (if parity_eq_true a b then Some True
                     else if parity_eq_false a b then Some False else None)"

lemma parity_less_sound:
  assumes "parity_less a b = Some r" and "i \<in> gamma a" and "j \<in> gamma b"
  shows "(i < j) = r"
  using assms parity_less_true_sound parity_less_false_sound
  unfolding parity_less_def by (auto split: if_splits)

lemma parity_eq_sound:
  assumes "parity_eq a b = Some r" and "i \<in> gamma a" and "j \<in> gamma b"
  shows "(i = j) = r"
  using assms parity_eq_true_sound parity_eq_false_sound
  unfolding parity_eq_def by (auto split: if_splits)

subsection \<open>Interpreting the generic numeric-query interface\<close>

global_interpretation parity_numeric_queries: abstract_numeric_queries parity_less parity_eq
  by unfold_locales (metis parity_less_sound parity_eq_sound)+

end
