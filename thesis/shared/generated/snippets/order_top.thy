(* ~~/src/HOL/Orderings.thy *)
class order_top = order + top +
  assumes top_greatest: "a \<le> \<top>"
