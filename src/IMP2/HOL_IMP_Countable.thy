theory HOL_IMP_Countable
  imports "HOL-Library.Countable" "HOL-IMP.AExp" "HOL-IMP.BExp"
          "Deriving.Compare_Order_Instances"
begin

(* Upstream HOL-IMP countable instances (separate theory avoids arity-fact clash). *)

instance AExp.aexp :: countable
  by countable_datatype

instance BExp.bexp :: countable
  by countable_datatype

(* Executable structural linear orders for the wrapped Nipkow expression types
   (AFP Deriving). Isolated here so the generated comparator constants
   (partial_comparator_aexp etc.) do not clash with the same-base-name
   IMP2_Syntax.aexp / IMP2_Syntax.bexp derivations. *)
derive linorder "AExp.aexp"
derive linorder "BExp.bexp"

end
