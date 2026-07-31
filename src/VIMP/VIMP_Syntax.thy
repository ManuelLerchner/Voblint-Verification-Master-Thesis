theory VIMP_Syntax
  imports Main "HOL-Library.Countable" "Deriving.Compare_Order_Instances"
begin

section \<open>Source-language expressions\<close>

text \<open>
  Arithmetic and Boolean leaves (\<open>N\<close>, \<open>V\<close>, \<open>Bc\<close>) are native constructors
  alongside the extended operators, rather than wrapping an imported base
  language.
\<close>

type_synonym vname = string
type_synonym store = "vname => int"

(* -- Arithmetic Expressions ---------------------------------------- *)

datatype aexp =
    N (aexp_lit: int)
  | V (aexp_var: vname)
  | Plus  (aexp_lhs: aexp) (aexp_rhs: aexp)
  | Minus (aexp_lhs: aexp) (aexp_rhs: aexp)
  | Times (aexp_lhs: aexp) (aexp_rhs: aexp)

(* -- Boolean Expressions -------------------------------------------- *)

datatype bexp =
    Bc (bexp_lit: bool)
  | Not (bexp_arg: bexp)
  | And (bexp_lhs: bexp) (bexp_rhs: bexp)
  | Or (bexp_lhs: bexp) (bexp_rhs: bexp)
  | Less (cmp_lhs: aexp) (cmp_rhs: aexp)
  | Eq (cmp_lhs: aexp) (cmp_rhs: aexp)

instance aexp :: countable
  by countable_datatype

instance bexp :: countable
  by countable_datatype

text \<open>The executable linear order gives @{const sorted_list_of_set} a deterministic
  representation of CFG edge sets. A @{typ bexp} order has no comparable consumer, and
  deriving one adds duplicate simplification rules.\<close>
derive linorder aexp

end

