(* vendor/td-verification/Basics_side.thy *)
datatype ('x,'g,'d) strategy_tree = Answer 'd |
  QueryL 'x "'d \<Rightarrow> ('x,'g,'d) strategy_tree" |
  QueryG 'g "'d \<Rightarrow> ('x,'g,'d) strategy_tree" |
  Side 'g 'd "('x,'g,'d) strategy_tree"
