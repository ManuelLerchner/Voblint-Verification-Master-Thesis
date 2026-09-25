(* vendor/td-verification/Update_rules.thy *)
class narrowing =
  fixes narrow :: "'a :: order \<Rightarrow> 'a \<Rightarrow> 'a" (infixl "\<Delta>" 70)
  assumes narrow_ge: "b \<le> a \<Longrightarrow> b \<le> a \<Delta> b"
    and narrow_le: "b \<le> a \<Longrightarrow> a \<Delta> b \<le> a"
