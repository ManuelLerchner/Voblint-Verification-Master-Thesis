theory VIMP_Syntax
  imports VIMP_Settings "HOL-Library.Countable" "Deriving.Compare_Order_Instances"
begin

section \<open>Source-language expressions\<close>

text \<open>
  \<open>exp\<close> is one integer-valued expression language, matching C: there is no
  separate Boolean AST.  \<open>N\<close> and \<open>V\<close> are the leaves; \<open>Less\<close>/\<open>Eq\<close>/\<open>Not\<close>/
  \<open>And\<close>/\<open>Or\<close> are ordinary constructors that happen to evaluate to \<open>0\<close>/\<open>1\<close>
  (\<open>VIMP_Expr\<close>'s \<open>aval\<close>/\<open>truthy\<close>), exactly as a C comparison or logical
  operator yields an \<open>int\<close>.  There is no \<open>Bc\<close> constructor: source \<open>true\<close>/
  \<open>false\<close> literals lower to \<open>N 1\<close>/\<open>N 0\<close> at the grammar level.
\<close>

type_synonym vname = String.literal
type_synonym store = "vname => int"

(* -- Expressions ------------------------------------------------------ *)

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

text \<open>\<^typ>\<open>String.literal\<close> already carries a @{class linorder} instance
  (\<^theory>\<open>HOL.String\<close>); registering it with @{class compare_order} makes it a usable
  leaf for the derivation below, the same way @{type char} already is.\<close>
derive (linorder) compare_order String.literal

text \<open>The executable linear order gives @{const sorted_list_of_set} a deterministic
  representation of CFG edge sets.\<close>
derive linorder exp

end

