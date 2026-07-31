theory Strategy_Tree_Do
  imports Strategy_Tree_Monad "HOL-Library.Monad_Syntax"
begin

section \<open>Do-notation for the strategy tree monad\<close>

text \<open>
  \<^const>\<open>seqcomp_tree\<close> is bind for \<^type>\<open>strategy_tree\<close>
  (\<open>Strategy_Tree_Monad.thy\<close>). This registers it under
  \<^const>\<open>Monad_Syntax.bind\<close>'s ad hoc overloading, so \<open>t \<bind> k\<close> and
  \<open>do { x \<leftarrow> t; k x }\<close> both parse to exactly \<open>seqcomp_tree t k\<close> -- a pure
  syntax translation resolved at elaboration time, so every lemma about
  \<^const>\<open>seqcomp_tree\<close> applies unchanged to code written with \<open>do\<close> notation.
\<close>

adhoc_overloading Monad_Syntax.bind == seqcomp_tree

end
