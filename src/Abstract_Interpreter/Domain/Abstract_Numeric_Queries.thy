theory Abstract_Numeric_Queries
  imports Abstract_Domain
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

  \<open>executable_numeric_queries\<close> fixes that shape alone: a consumer that only
  ever calls \<open>less\<close>/\<open>eq\<close>, never proves anything about them, requests
  \<open>'a::executable_domain\<close> and never drags \<open>gamma\<close> into its type-class
  dictionary. \<open>abstract_numeric_queries\<close> adds the soundness obligation on
  top. Kept in a session with no \<open>exp\<close>/\<open>store\<close> concept at all, so a domain
  that only has these two operations could still interpret it: the
  \<open>backward_domain\<close> locale refines an
  abstract value under an assumed truth value; \<open>abstract_numeric_queries\<close>
  instead classifies an already-fixed pair of values as provably related,
  provably unrelated, or neither.

  \<open>numeric_query_judgments\<close>, below, is how every domain here builds such an
  instance: it packages four yes/no judgments into the two queries and proves
  the obligation once, so no domain restates that step. Where the four
  judgments come from is the domain's business. Every \<open>backward_domain\<close>
  instance reads them off its own narrowing operators, in the
  \<open>Backward_Numeric_Queries\<close> theory, and gets an instance for free; a
  concrete domain may instead supply sharper, hand-tuned judgments when that
  derivation loses precision it cannot recover, or judgments unrelated to
  narrowing altogether.
\<close>

locale executable_numeric_queries =
  fixes less :: "'a::executable_domain \<Rightarrow> 'a \<Rightarrow> bool option"
    and eq   :: "'a \<Rightarrow> 'a \<Rightarrow> bool option"

text \<open>The soundness obligation, stated so that a \<open>Some\<close> answer is exact rather than merely
  one-sided: every concrete pair drawn from the two values must relate the way the answer
  says.  \<open>None\<close> carries no obligation at all, which is what lets a domain answer it whenever
  it cannot decide.\<close>
locale abstract_numeric_queries = executable_numeric_queries less eq
  for less :: "'a::sound_domain \<Rightarrow> 'a \<Rightarrow> bool option"
    and eq :: "'a \<Rightarrow> 'a \<Rightarrow> bool option" +
  assumes less_sound[intro]:
      "less a b = Some r \<Longrightarrow> i \<in> \<gamma> a \<Longrightarrow> j \<in> \<gamma> b \<Longrightarrow> (i < j) = r"
    and eq_sound[intro]:
      "eq a b = Some r \<Longrightarrow> i \<in> \<gamma> a \<Longrightarrow> j \<in> \<gamma> b \<Longrightarrow> (i = j) = r"

subsection \<open>Building an instance from four judgments\<close>

text \<open>
  A domain rarely decides \<open>less\<close>/\<open>eq\<close> in one step. It decides four separate
  judgments -- every witness pair satisfies \<open><\<close>, every witness pair refutes
  it, and the same two for \<open>=\<close> -- and the two queries are those four read in
  order: prefer the affirmative judgment, fall back to the refuting one,
  answer \<open>None\<close> when neither fires. \<open>numeric_query_judgments\<close> fixes the four
  and their soundness, and nothing else, so a domain interprets it whatever
  the judgments were read off: a narrowing operator, a comparison of bounds,
  a test that one side denotes nothing.

  Interpreting it introduces \<open>less\<close>/\<open>eq\<close> as ordinary top-level constants
  through a \<^theory_text>\<open>defines\<close> clause, and therefore with the code
  equation a constant living in a still-abstract locale context does not
  have.

  \<open>less_true\<close> and \<open>less_false\<close> (and \<open>eq_true\<close> and \<open>eq_false\<close>) can both hold
  at once only when an operand denotes nothing: a live witness pair on both
  sides would have to satisfy \<open>i < j\<close> and \<open>\<not> i < j\<close> simultaneously. So on
  any pair of feasible operands the \<open>if\<close> choice between \<open>Some True\<close> and
  \<open>Some False\<close> below is never live.
\<close>

locale numeric_query_judgments =
  fixes less_true :: "'a::sound_domain \<Rightarrow> 'a \<Rightarrow> bool"
    and less_false :: "'a \<Rightarrow> 'a \<Rightarrow> bool"
    and eq_true :: "'a \<Rightarrow> 'a \<Rightarrow> bool"
    and eq_false :: "'a \<Rightarrow> 'a \<Rightarrow> bool"
  assumes less_true_sound:
      "less_true a b \<Longrightarrow> i \<in> \<gamma> a \<Longrightarrow> j \<in> \<gamma> b \<Longrightarrow> i < j"
    and less_false_sound:
      "less_false a b \<Longrightarrow> i \<in> \<gamma> a \<Longrightarrow> j \<in> \<gamma> b \<Longrightarrow> \<not> i < j"
    and eq_true_sound:
      "eq_true a b \<Longrightarrow> i \<in> \<gamma> a \<Longrightarrow> j \<in> \<gamma> b \<Longrightarrow> i = j"
    and eq_false_sound:
      "eq_false a b \<Longrightarrow> i \<in> \<gamma> a \<Longrightarrow> j \<in> \<gamma> b \<Longrightarrow> i \<noteq> j"
begin

definition less :: "'a \<Rightarrow> 'a \<Rightarrow> bool option" where
  "less a b = (if less_true a b then Some True else if less_false a b then Some False else None)"

definition eq :: "'a \<Rightarrow> 'a \<Rightarrow> bool option" where
  "eq a b = (if eq_true a b then Some True else if eq_false a b then Some False else None)"

lemma less_opt_sound:
  assumes "less a b = Some r" and "i \<in> \<gamma> a" and "j \<in> \<gamma> b"
  shows "(i < j) = r"
  using assms less_true_sound less_false_sound unfolding less_def by (auto split: if_splits)

lemma eq_opt_sound:
  assumes "eq a b = Some r" and "i \<in> \<gamma> a" and "j \<in> \<gamma> b"
  shows "(i = j) = r"
  using assms eq_true_sound eq_false_sound unfolding eq_def by (auto split: if_splits)

end

sublocale numeric_query_judgments \<subseteq> abstract_numeric_queries less eq
proof
  fix a b r i j
  assume "less a b = Some r" and "i \<in> \<gamma> a" and "j \<in> \<gamma> b"
  then show "(i < j) = r" by (rule less_opt_sound)
next
  fix a b r i j
  assume "eq a b = Some r" and "i \<in> \<gamma> a" and "j \<in> \<gamma> b"
  then show "(i = j) = r" by (rule eq_opt_sound)
qed

end

