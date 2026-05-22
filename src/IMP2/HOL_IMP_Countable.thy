theory HOL_IMP_Countable
  imports "HOL-Library.Countable" "HOL-IMP.AExp" "HOL-IMP.BExp"
begin

(*
  Derive Countable instances for the upstream HOL-IMP datatypes
  AExp.aexp and BExp.bexp. Kept in a dedicated theory to avoid the
  arity-fact name clash that would arise if we declared these
  instances alongside our wrapped versions in IMP2_Syntax (both
  base names end in "_aexp"/"_bexp", and arity facts are named
  by suffix only, so two such instances in the same theory
  trigger a Duplicate fact declaration error).
*)

instance AExp.aexp :: countable
  by countable_datatype

instance BExp.bexp :: countable
  by countable_datatype

end
