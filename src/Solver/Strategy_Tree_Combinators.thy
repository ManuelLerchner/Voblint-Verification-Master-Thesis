theory Strategy_Tree_Combinators
  imports Strategy_Tree_Sequencing
begin

section \<open>Reading and side-effecting combinators\<close>

text \<open>
  The underlying verified TD solver represents RHS computations with four
  constructors on \<^typ>\<open>('x, 'g, 'd) strategy_tree\<close>: \<^const>\<open>QueryL\<close> reads
  a local unknown, \<^const>\<open>QueryG\<close> reads a global unknown, \<^const>\<open>Side\<close>
  contributes a value to a global unknown as a side effect and continues,
  \<^const>\<open>Answer\<close> yields the local result. This theory names each
  constructor for what it does at a call site, so an equation author writes
  \<open>read_local\<close>/\<open>side_effect\<close> rather than nested nameless lambdas over
  \<open>QueryL\<close>/\<open>QueryG\<close>.
\<close>

subsection \<open>Named abbreviations, not new constants\<close>

text \<open>
  Read and side effect are dual, not the same relationship: a read creates a
  dependency on the unknown it queries, while a side effect contributes to a
  \<^emph>\<open>different\<close> unknown without depending on it. Every combinator below is a
  plain \<open>abbreviation\<close> -- a syntax translation, not a new constant: a term
  written with the named form parses to and unfolds as exactly the
  constructor term it abbreviates, so every existing lemma about
  \<open>QueryL\<close>/\<open>QueryG\<close>/\<open>Side\<close>/\<open>Answer\<close> -- and every proof that unfolds an
  equation's \<open>_def\<close> and pattern-matches on those constructors -- applies
  unchanged.
\<close>

abbreviation answer :: "'d \<Rightarrow> ('x, 'g, 'd) strategy_tree" where
  "answer d \<equiv> Answer d"

text \<open>
  \<open>read_local\<close>/\<open>read_global\<close> are value-producing: the queried value itself is
  the tree's answer, so \<open>seqcomp_tree\<close> (bind for this monad,
  \<open>Strategy_Tree_Sequencing\<close>, which also gives it \<open>do\<close>-notation via
  \<^verbatim>\<open>adhoc_overloading\<close>) sequences a read directly as
  \<open>do { d \<leftarrow> read_local key; ... }\<close>.
\<close>

abbreviation read_local :: "'x \<Rightarrow> ('x, 'g, 'd) strategy_tree" where
  "read_local key \<equiv> QueryL key answer"

abbreviation read_global :: "'g \<Rightarrow> ('x, 'g, 'd) strategy_tree" where
  "read_global key \<equiv> QueryG key answer"

text \<open>
  \<open>read_at\<close> reads an unknown represented in the solver's combined address
  space \<^typ>\<open>'x + 'g\<close>, dispatching \<^const>\<open>Inl\<close> to a local query and
  \<^const>\<open>Inr\<close> to a global query instead of fixing the constructor at the
  call site.
\<close>

fun read_at :: "'x + 'g \<Rightarrow> ('x, 'g, 'd) strategy_tree" where
  "read_at (Inl x) = read_local x"
| "read_at (Inr y) = read_global y"

lemma traverse_read_at [simp]: "traverse_rhs (read_at src) sigma = sigma src"
  by (cases src) auto

lemma sides_read_at [simp]:
  fixes src :: "'x + 'g"
  shows "sides_of_rhs (read_at src) sigma = (\<lambda>_. bot)"
  by (cases src) auto

lemma dep_aux_read_at [simp]: "dep_aux sigma (read_at src) = {src}"
  by (cases src) auto

text \<open>
  \<open>side_effect key val cont\<close> contributes \<open>val\<close> to the global unknown \<open>key\<close>
  as a side effect, then continues as \<open>cont\<close> -- the write/contribution
  operation of a side-effecting constraint system, dual to
  \<open>read_local\<close>/\<open>read_global\<close>, which query unknowns. A side effect is not a
  dependency on its target: dependencies arise from queried unknowns, while
  \<open>Side\<close> contributes to another unknown. Its trailing continuation is what a
  do-block statement (no \<open>\<leftarrow>\<close>) needs, so \<open>side_effect\<close> itself keeps this
  shape rather than gaining a value-producing twin: a caller writing it as a
  do-block statement supplies the neutral answer as that continuation.
\<close>

abbreviation side_effect ::
  "'g \<Rightarrow> 'd \<Rightarrow> ('x, 'g, 'd) strategy_tree \<Rightarrow> ('x, 'g, 'd) strategy_tree"
where
  "side_effect key val cont \<equiv> Side key val cont"

end
