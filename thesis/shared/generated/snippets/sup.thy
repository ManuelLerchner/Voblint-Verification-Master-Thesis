(* ~~/src/HOL/Lattices.thy *)
class sup =
  fixes sup :: "'a \<Rightarrow> 'a \<Rightarrow> 'a" (infixl \<open>\<squnion>\<close> 65)
