theory HOL_IMP_Countable
  imports "HOL-Library.Countable" "HOL-IMP.AExp" "HOL-IMP.BExp"
begin

(* Upstream HOL-IMP countable instances (separate theory avoids arity-fact clash). *)

instance AExp.aexp :: countable
  by countable_datatype

instance BExp.bexp :: countable
  by countable_datatype

end
