theory VIMP_Regression
  imports "Voblint_VIMP.Core_Com" "Voblint_VIMP.VIMP_Notation"
begin

section \<open>VIMP syntax and semantics regressions\<close>

text \<open>Build-checked regression assertions on concrete VIMP snippets and values, moved out of
  \<open>VIMP_Notation\<close> and \<open>VIMP_Expr\<close>.  Nothing cites them; the build failing is the signal.\<close>

subsection \<open>Concrete syntax and precedence\<close>

text \<open>Each snippet elaborates to a fixed \<open>src_com\<close> term or to its fully parenthesised form: dangling
  and chained \<open>else\<close>, statement boundaries, calls and returns, and C operator precedence.\<close>

lemma notation_if_without_else:
  "imp \<lbrakk> if (x < 0) { x = -x; } \<rbrakk> =
    If () (Less (V (STR ''x'')) (N 0))
      (Assign () (STR ''x'') (Minus (N 0) (V (STR ''x'')))) (SKIP ())"
  by simp

lemma notation_else_if_chain:
  "imp \<lbrakk>
     if (x < 0) { y = -1; }
     else if (x == 0) { y = 0; }
     else if (x < 10) { y = 1; }
   \<rbrakk> =
   imp \<lbrakk>
     if (x < 0) { y = -1; } else {
       if (x == 0) { y = 0; } else {
         if (x < 10) { y = 1; } else { skip; }
       }
     }
   \<rbrakk>"
  by simp

lemma notation_else_if_final_else:
  "imp \<lbrakk> if (x) { } else if (y) { skip; } else { x = 1; } \<rbrakk> =
    If () (V (STR ''x'')) (SKIP ())
      (If () (V (STR ''y'')) (SKIP ()) (Assign () (STR ''x'') (N 1)))"
  by simp

lemma notation_block_statement_boundaries:
  "imp \<lbrakk> x = 0; while (x < 2) { x = x + 1; } if (x) { } \<rbrakk> =
    Seq (Seq (Assign () (STR ''x'') (N 0))
      (While () (Less (V (STR ''x'')) (N 2))
        (Assign () (STR ''x'') (Plus (V (STR ''x'')) (N 1)))))
      (If () (V (STR ''x'')) (SKIP ()) (SKIP ()))"
  by simp

lemma notation_fun_call_return:
  "prog_main (program {
      fun id(x) { return x; }
      fun ping() { return; }
      fun main() { x = id(1); ping(); }
    }) =
    Seq (Call () (Some (STR ''x'')) (STR ''id'') [N 1])
      (Call () None (STR ''ping'') [])"
  by simp

lemma notation_comparison_less:
  "imp \<lbrakk> __voblint_check(x < y); \<rbrakk> =
    Check () (0, 0) (Less (V (STR ''x'')) (V (STR ''y'')))"
  by simp

lemma notation_comparison_less_eq:
  "imp \<lbrakk> __voblint_check(x <= y); \<rbrakk> =
    Check () (0, 0) (LessEq (V (STR ''x'')) (V (STR ''y'')))"
  by simp

lemma notation_comparison_greater:
  "imp \<lbrakk> __voblint_check(x > y); \<rbrakk> =
    Check () (0, 0) (Greater (V (STR ''x'')) (V (STR ''y'')))"
  by simp

lemma notation_comparison_greater_eq:
  "imp \<lbrakk> __voblint_check(x >= y); \<rbrakk> =
    Check () (0, 0) (GreaterEq (V (STR ''x'')) (V (STR ''y'')))"
  by simp

lemma notation_comparison_eq:
  "imp \<lbrakk> __voblint_check(x == y); \<rbrakk> =
    Check () (0, 0) (Eq (V (STR ''x'')) (V (STR ''y'')))"
  by simp

lemma notation_comparison_not_eq:
  "imp \<lbrakk> __voblint_check(x != y); \<rbrakk> =
    Check () (0, 0) (NotEq (V (STR ''x'')) (V (STR ''y'')))"
  by simp

lemma notation_comparison_precedence:
  "imp \<lbrakk> __voblint_check(x + 1 <= y * 2 && x != y); \<rbrakk> =
    Check () (0, 0) (And
      (LessEq (Plus (V (STR ''x'')) (N 1)) (Times (V (STR ''y'')) (N 2)))
      (NotEq (V (STR ''x'')) (V (STR ''y''))))"
  by simp

lemma notation_relational_before_equality:
  "imp \<lbrakk> __voblint_check(x == y < z); \<rbrakk> =
    imp \<lbrakk> __voblint_check(x == (y < z)); \<rbrakk>"
  "imp \<lbrakk> __voblint_check(x < y != z); \<rbrakk> =
    imp \<lbrakk> __voblint_check((x < y) != z); \<rbrakk>"
  "imp \<lbrakk> __voblint_check(x + 1 >= y == z <= w * 2); \<rbrakk> =
    imp \<lbrakk> __voblint_check((x + 1 >= y) == (z <= w * 2)); \<rbrakk>"
  by simp_all

lemma notation_division_remainder:
  "imp \<lbrakk> x = a / b; y = a % b; \<rbrakk> =
    Seq (Assign () (STR ''x'') (Div (V (STR ''a'')) (V (STR ''b''))))
      (Assign () (STR ''y'') (Mod (V (STR ''a'')) (V (STR ''b''))))"
  by simp

lemma notation_multiplicative_precedence:
  "imp \<lbrakk> x = 20 / 3 % 4 * 2 + 1; \<rbrakk> =
    imp \<lbrakk> x = (((20 / 3) % 4) * 2) + 1; \<rbrakk>"
  "imp \<lbrakk> x = -7 / 3; \<rbrakk> = Assign () (STR ''x'') (Div (N (-7)) (N 3))"
  "imp \<lbrakk> __voblint_check(1 == 20 / 3 % 4 < 3); \<rbrakk> =
    imp \<lbrakk> __voblint_check(1 == (((20 / 3) % 4) < 3)); \<rbrakk>"
  by simp_all

subsection \<open>Comparison semantics\<close>

text \<open>Comparisons of core expressions yield \<open>1\<close> or \<open>0\<close> on signed operands, including the
  boundaries at \<open>-1\<close> and \<open>0\<close>.\<close>

lemma comparison_signed_boundaries:
  "map (\<lambda>e. eval e s)
    [TCmp CLt (TN I32 (-1)) (TN I32 0), TCmp CLe (TN I32 (-1)) (TN I32 (-1)),
     TCmp CGt (TN I32 0) (TN I32 (-1)), TCmp CGe (TN I32 (-1)) (TN I32 (-1)),
     TCmp CEq (TN I32 (-1)) (TN I32 (-1)), TCmp CNe (TN I32 (-1)) (TN I32 0)] = [1, 1, 1, 1, 1, 1]"
  "map (\<lambda>e. eval e s)
    [TCmp CLt (TN I32 (-1)) (TN I32 (-1)), TCmp CLe (TN I32 0) (TN I32 (-1)),
     TCmp CGt (TN I32 (-1)) (TN I32 (-1)), TCmp CGe (TN I32 (-1)) (TN I32 0),
     TCmp CEq (TN I32 (-1)) (TN I32 0), TCmp CNe (TN I32 (-1)) (TN I32 (-1))] = [0, 0, 0, 0, 0, 0]"
  by (simp_all add: ik_min_def ik_max_def ik_half_def)

subsection \<open>Division and remainder\<close>

text \<open>\<open>c_div\<close> truncates toward zero and \<open>c_mod\<close> takes the dividend's sign, for all four sign
  combinations; a zero divisor yields \<open>0\<close> for division and the dividend for remainder.\<close>

lemma c_div_signed_examples:
  "map (\<lambda>(a, b). c_div a b) [(7, 3), (-7, 3), (7, -3), (-7, -3)] =
    [2, -2, -2, 2]"
  by (simp add: c_div_def)

lemma c_mod_signed_examples:
  "map (\<lambda>(a, b). c_mod a b) [(7, 3), (-7, 3), (7, -3), (-7, -3)] =
    [1, -1, 1, -1]"
  by (simp add: c_mod_def c_div_def)

lemma eval_division_remainder:
  "map (\<lambda>e. eval e s)
    [TArith I32 ADiv (TN I32 7) (TN I32 3), TArith I32 ADiv (TN I32 (-7)) (TN I32 3),
     TArith I32 ADiv (TN I32 7) (TN I32 (-3)), TArith I32 ADiv (TN I32 (-7)) (TN I32 (-3)),
     TArith I32 AMod (TN I32 7) (TN I32 3), TArith I32 AMod (TN I32 (-7)) (TN I32 3),
     TArith I32 AMod (TN I32 7) (TN I32 (-3)), TArith I32 AMod (TN I32 (-7)) (TN I32 (-3)),
     TArith I32 ADiv (TN I32 7) (TN I32 0), TArith I32 AMod (TN I32 (-7)) (TN I32 0)]
   = [2, -2, -2, 2, 1, -1, 1, -1, 0, -7]"
  by (simp add: ik_min_def ik_max_def ik_half_def c_div_def c_mod_def)

end
