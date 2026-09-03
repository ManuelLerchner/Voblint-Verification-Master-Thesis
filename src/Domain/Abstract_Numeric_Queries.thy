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
  provably unrelated, or neither. Every \<open>backward_domain\<close> instance gets this
  for free, in the \<open>Backward_Numeric_Queries\<close> theory, off its own narrowing
  operators -- a concrete domain then chooses either that derivation or its
  own sharper, hand-tuned queries when the generic derivation loses precision
  it cannot recover.
\<close>

locale executable_numeric_queries =
  fixes less :: "'a::executable_domain \<Rightarrow> 'a \<Rightarrow> bool option"
    and eq   :: "'a \<Rightarrow> 'a \<Rightarrow> bool option"

locale abstract_numeric_queries = executable_numeric_queries less eq
  for less :: "'a::sound_domain \<Rightarrow> 'a \<Rightarrow> bool option"
    and eq :: "'a \<Rightarrow> 'a \<Rightarrow> bool option" +
  assumes less_sound[intro]:
      "less a b = Some r \<Longrightarrow> i \<in> gamma a \<Longrightarrow> j \<in> gamma b \<Longrightarrow> (i < j) = r"
    and eq_sound[intro]:
      "eq a b = Some r \<Longrightarrow> i \<in> gamma a \<Longrightarrow> j \<in> gamma b \<Longrightarrow> (i = j) = r"

end

