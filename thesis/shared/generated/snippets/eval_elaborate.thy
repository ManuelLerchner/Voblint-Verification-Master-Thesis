(* src/Program_Model/VIMP/Core_Exp.thy *)
theorem eval_elaborate:
  assumes "all_in_kinds \<kappa> t"
  shows "eval (elaborate \<rho> \<kappa> ik e) t = src_eval (\<kappa> \<circ> \<rho>) ik e (t \<circ> \<rho>)"
