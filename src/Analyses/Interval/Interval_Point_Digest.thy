theory Interval_Point_Digest
  imports Interval_Domain
begin

section \<open>Interval point abstraction\<close>

text \<open>The point abstraction maps an integer to its singleton interval.\<close>

definition ivl_decode :: "Int.int \<Rightarrow> ivl" where
  "ivl_decode v = Ivl (Fin v) (Fin v)"

end
