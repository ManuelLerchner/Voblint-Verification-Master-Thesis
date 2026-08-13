theory Strategy_Tree_Combinators
  imports Strategy_Tree_Do
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

abbreviation answer :: "'d \<Rightarrow> ('x, 'g, 'd) strategy_tree" where
  "answer d \<equiv> Answer d"

text \<open>
  \<open>read_local\<close>/\<open>read_global\<close> are value-producing: the queried value itself is
  the tree's answer, so \<open>seqcomp_tree\<close> (bind for this monad,
  \<open>Strategy_Tree_Monad.thy\<close>, given \<open>do\<close>-notation via \<open>Strategy_Tree_Do.thy\<close>'s
  \<^verbatim>\<open>adhoc_overloading\<close>) sequences a read directly as
  \<open>do { d \<leftarrow> read_local key; ... }\<close>. Unfolding \<open>seqcomp_tree\<close>'s two
  defining equations on a bound read reduces it to exactly the \<open>_cont\<close> form
  below, so proofs that need the flat constructor shape add
  \<open>seqcomp_tree.simps\<close> to their simp set once, then proceed as before.
\<close>

abbreviation read_local :: "'x \<Rightarrow> ('x, 'g, 'd) strategy_tree" where
  "read_local key \<equiv> QueryL key answer"

abbreviation read_global :: "'g \<Rightarrow> ('x, 'g, 'd) strategy_tree" where
  "read_global key \<equiv> QueryG key answer"

text \<open>
  \<open>_cont\<close> suffix: the original continuation-passing shape, kept for direct,
  single-step low-level use (no bind/do-notation needed) and as the primitive
  \<open>read_local\<close>/\<open>read_global\<close> themselves compile down to.
\<close>

abbreviation read_local_cont ::
  "'x \<Rightarrow> ('d \<Rightarrow> ('x, 'g, 'd) strategy_tree) \<Rightarrow> ('x, 'g, 'd) strategy_tree"
where
  "read_local_cont key k \<equiv> QueryL key k"

abbreviation read_global_cont ::
  "'g \<Rightarrow> ('d \<Rightarrow> ('x, 'g, 'd) strategy_tree) \<Rightarrow> ('x, 'g, 'd) strategy_tree"
where
  "read_global_cont key k \<equiv> QueryG key k"

text \<open>
  \<open>depend_on key val cont\<close> publishes \<open>val\<close> as a side effect on the global
  unknown \<open>key\<close> and continues as \<open>cont\<close>. The name reflects the direction an
  equation author reasons in: ``this equation also depends on -- contributes
  to -- \<open>key\<close>'', not the solver-internal notion of a queued side write. Its
  trailing continuation is what a do-block statement (no \<open>\<leftarrow>\<close>) needs, so
  \<open>depend_on\<close> itself keeps this shape rather than gaining a value-producing
  twin: statement-form combinators built on it (\<open>publish_global\<close>,
  \<open>publish_seed\<close>, \<open>DG_Transfer_Combinators.thy\<close>) supply \<open>answer bot\<close> as that
  continuation.
\<close>

abbreviation depend_on ::
  "'g \<Rightarrow> 'd \<Rightarrow> ('x, 'g, 'd) strategy_tree \<Rightarrow> ('x, 'g, 'd) strategy_tree"
where
  "depend_on key val cont \<equiv> Side key val cont"

end
