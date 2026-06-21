theory IMP2_Expr
  imports IMP2_Syntax "HOL-IMP.Star"
begin

(*
  IMP2 -- expression evaluation.

  aval/bval evaluate the IMP2 expression extensions, delegating
  BaseN/BaseB to Nipkow's HOL-IMP AExp/BExp.

  The actual small-step relation `pstep` lives in IMP2_Proc.thy;
  this module is expression evaluation only.  `HOL-IMP.Star` is
  re-exported here so `pstep`'s `star` closure resolves downstream.
*)

(* -- Expression Evaluation -------------------------------------- *)

fun aval :: "aexp => store => int" where
    "aval (BaseN a)   s  = AExp.aval a s"
  | "aval (Plus  a b) s  = aval a s + aval b s"
  | "aval (Minus a b) s  = aval a s - aval b s"
  | "aval (Times a b) s  = aval a s * aval b s"

fun bval :: "bexp => store => bool" where
    "bval (BaseB b)   s  = BExp.bval b s"
  | "bval (Not b)     s  = (\<not> bval b s)"
  | "bval (And b1 b2) s  = (bval b1 s \<and> bval b2 s)"
  | "bval (Or  b1 b2) s  = (bval b1 s \<or> bval b2 s)"
  | "bval (Less a b)  s  = (aval a s < aval b s)"
  | "bval (Eq   a b)  s  = (aval a s = aval b s)"

subsection \<open>Executable examples\<close>

value "aval (Plus (N 3) (N 4)) (\<lambda>_. 0::int)"
value "aval (V ''x'') ((\<lambda>_. 0::int)(''x'' := 42))"
value "aval (Times (Minus (V ''x'') (N 2)) (N 3)) ((\<lambda>_. 0::int)(''x'' := 5))"

value "bval (Less (V ''x'') (N 10)) ((\<lambda>_. 0::int)(''x'' := 7))"
value "bval (Eq (V ''x'') (N 5)) ((\<lambda>_. 0::int)(''x'' := 5))"
value "bval (Not (Bc True)) (\<lambda>_. 0::int)"

end


