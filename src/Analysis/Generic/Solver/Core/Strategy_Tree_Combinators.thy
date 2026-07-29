theory Strategy_Tree_Combinators
  imports TD_Side_CFG
begin

section \<open>Reading and side-publishing combinators\<close>

text \<open>
  The verified TD solver's instruction set is four constructors on
  \<^typ>\<open>('x, 'g, 'd) strategy_tree\<close>: \<^const>\<open>QueryL\<close> reads a local unknown,
  \<^const>\<open>QueryG\<close> reads a global unknown, \<^const>\<open>Side\<close> publishes a value
  under a global key and continues, \<^const>\<open>Answer\<close> yields the local result.
  Equation authors construct trees directly with these constructors, so an
  equation such as ``combine the caller state, the routed callee state, and
  the globals'' reads as nested nameless lambdas over \<open>QueryL\<close>/\<open>QueryG\<close>
  rather than as the combine it computes.

  The abbreviations below rename the four constructors to their
  equation-authoring role. Each is a plain syntax translation, not a new
  constant: a term written with the renamed form parses to and unfolds as
  exactly the constructor term it abbreviates, so every existing lemma about
  \<open>QueryL\<close>/\<open>QueryG\<close>/\<open>Side\<close>/\<open>Answer\<close> -- and every proof that unfolds an
  equation's \<open>_def\<close> and pattern-matches on those constructors -- applies
  unchanged.
\<close>

abbreviation read_local ::
  "'x \<Rightarrow> ('d \<Rightarrow> ('x, 'g, 'd) strategy_tree) \<Rightarrow> ('x, 'g, 'd) strategy_tree"
where
  "read_local key k \<equiv> QueryL key k"

abbreviation read_global ::
  "'g \<Rightarrow> ('d \<Rightarrow> ('x, 'g, 'd) strategy_tree) \<Rightarrow> ('x, 'g, 'd) strategy_tree"
where
  "read_global key k \<equiv> QueryG key k"

text \<open>
  \<open>depend_on key val cont\<close> publishes \<open>val\<close> as a side effect on the global
  unknown \<open>key\<close> and continues as \<open>cont\<close>. The name reflects the direction an
  equation author reasons in: ``this equation also depends on -- contributes
  to -- \<open>key\<close>'', not the solver-internal notion of a queued side write.
\<close>

abbreviation depend_on ::
  "'g \<Rightarrow> 'd \<Rightarrow> ('x, 'g, 'd) strategy_tree \<Rightarrow> ('x, 'g, 'd) strategy_tree"
where
  "depend_on key val cont \<equiv> Side key val cont"

abbreviation answer :: "'d \<Rightarrow> ('x, 'g, 'd) strategy_tree" where
  "answer d \<equiv> Answer d"

end
