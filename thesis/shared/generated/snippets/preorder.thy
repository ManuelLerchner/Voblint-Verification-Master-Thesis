(* ~~/src/HOL/Orderings.thy *)
class preorder = ord +
  assumes less_le_not_le: "x < y \<longleftrightarrow> x \<le> y \<and> \<not> (y \<le> x)"
  and order_refl [iff]: "x \<le> x"
  and order_trans: "x \<le> y \<Longrightarrow> y \<le> z \<Longrightarrow> x \<le> z"
