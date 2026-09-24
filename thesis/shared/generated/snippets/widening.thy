(* vendor/td-verification/Update_rules.thy *)
class widening =
  fixes widen :: "'a :: order \<Rightarrow> 'a \<Rightarrow> 'a" (infixl "\<nabla>" 65)
  assumes widen_ge1: "a \<le> a \<nabla> b" and widen_ge2: "b \<le> a \<nabla> b"
