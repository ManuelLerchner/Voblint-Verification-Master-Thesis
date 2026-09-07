theory VIMP_Syntax
  imports Main "HOL-Library.Countable" "Deriving.Compare_Order_Instances"
begin

section \<open>Source-language expressions\<close>

text \<open>
  One integer-valued expression language, as in C: comparisons and logical
  operators are ordinary constructors evaluating to \<open>0\<close>/\<open>1\<close>, and source
  \<open>true\<close>/\<open>false\<close> lower to \<open>N 1\<close>/\<open>N 0\<close> in the grammar.
\<close>

type_synonym vname = String.literal
type_synonym store = "vname \<Rightarrow> int"

datatype exp =
    N (exp_lit: int)
  | V (exp_var: vname)
  | Plus  (exp_lhs: exp) (exp_rhs: exp)
  | Minus (exp_lhs: exp) (exp_rhs: exp)
  | Times (exp_lhs: exp) (exp_rhs: exp)
  | Less (cmp_lhs: exp) (cmp_rhs: exp)
  | Eq (cmp_lhs: exp) (cmp_rhs: exp)
  | Not (exp_arg: exp)
  | And (exp_lhs: exp) (exp_rhs: exp)
  | Or (exp_lhs: exp) (exp_rhs: exp)

instance exp :: countable
  by countable_datatype

text \<open>The executable linear order gives @{const sorted_list_of_set} a
  deterministic representation of CFG edge sets; @{class compare_order} on
  \<^typ>\<open>String.literal\<close> makes it a usable leaf for the derivation.\<close>
derive (linorder) compare_order String.literal
derive linorder exp

end

