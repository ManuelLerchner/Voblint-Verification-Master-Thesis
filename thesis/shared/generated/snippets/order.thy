(* ~~/src/HOL/Orderings.thy *)
class order = preorder +
  assumes order_antisym: "x \<le> y \<Longrightarrow> y \<le> x \<Longrightarrow> x = y"
