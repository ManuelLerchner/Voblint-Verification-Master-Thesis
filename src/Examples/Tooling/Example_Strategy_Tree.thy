theory Example_Strategy_Tree
  imports "TD.Basics_side"
begin

section \<open>Strategy trees as a dependency/effect language\<close>

text \<open>
  A minimal, domain-independent demonstration that \<^type>\<open>strategy_tree\<close> is a
  small effect language on its own -- no abstract domain, CFG, or context
  involved. \<open>demo_tree\<close> is built directly from \<^const>\<open>QueryL\<close>,
  \<^const>\<open>Side\<close>, and \<^const>\<open>Answer\<close>: it reads local unknown
  \<open>STR ''local''\<close>, and only when that value is positive publishes one more
  than it to global key \<open>STR ''global''\<close> before doubling it; otherwise it
  answers the value unchanged.
\<close>

definition demo_tree :: "(String.literal, String.literal, nat) strategy_tree" where
  "demo_tree =
     QueryL (STR ''local'') (\<lambda>x.
       if x > 0
       then Side (STR ''global'') (x + 1) (Answer (x * 2))
       else Answer x)"

end
