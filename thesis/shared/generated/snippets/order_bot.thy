(* ~~/src/HOL/Orderings.thy *)
class order_bot = order + bot +
  assumes bot_least: "\<bottom> \<le> a"
