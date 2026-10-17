theory VIMP_Syntax
  imports Machine_Kind
begin

section \<open>Source-language expressions\<close>

text \<open>
  One integer-valued expression language, as in C: comparisons and logical
  operators are ordinary constructors evaluating to \<open>0\<close>/\<open>1\<close>, and source
  \<open>true\<close>/\<open>false\<close> lower to \<open>N 1\<close>/\<open>N 0\<close> in the grammar.
  \<open>Cast ik e\<close> converts the value of \<open>e\<close> to the machine kind \<open>ik\<close> by wraparound.
  A program without machine kinds contains none, and its expressions compute over
  mathematical integers.
\<close>

type_synonym vname = String.literal
type_synonym src_store = "vname \<Rightarrow> int"

datatype src_exp =
    N (exp_lit: int)
  | V (exp_var: vname)
  | Plus  (exp_lhs: src_exp) (exp_rhs: src_exp)
  | Minus (exp_lhs: src_exp) (exp_rhs: src_exp)
  | Times (exp_lhs: src_exp) (exp_rhs: src_exp)
  | Div (exp_lhs: src_exp) (exp_rhs: src_exp)
  | Mod (exp_lhs: src_exp) (exp_rhs: src_exp)
  | Less (cmp_lhs: src_exp) (cmp_rhs: src_exp)
  | LessEq (cmp_lhs: src_exp) (cmp_rhs: src_exp)
  | Greater (cmp_lhs: src_exp) (cmp_rhs: src_exp)
  | GreaterEq (cmp_lhs: src_exp) (cmp_rhs: src_exp)
  | NotEq (cmp_lhs: src_exp) (cmp_rhs: src_exp)
  | Eq (cmp_lhs: src_exp) (cmp_rhs: src_exp)
  | Not (exp_arg: src_exp)
  | And (exp_lhs: src_exp) (exp_rhs: src_exp)
  | Or (exp_lhs: src_exp) (exp_rhs: src_exp)
  | Cast (cast_kind: ikind) (cast_arg: src_exp)

instance src_exp :: countable
  by countable_datatype

text \<open>The executable linear order gives @{const sorted_list_of_set} a
  deterministic representation of CFG edge sets; @{class compare_order} on
  \<^typ>\<open>String.literal\<close> makes it a usable leaf for the derivation.\<close>
derive (linorder) compare_order String.literal
derive linorder src_exp

end
