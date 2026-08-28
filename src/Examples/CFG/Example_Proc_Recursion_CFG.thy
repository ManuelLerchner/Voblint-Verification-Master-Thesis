section \<open>Example: recursive procedure CFG layout\<close>

theory Example_Proc_Recursion_CFG
  imports "Voblint_CFG.VIMP_Proc_to_CFG" "Voblint_VIMP.VIMP_Notation"
begin

text \<open>
  Source-level regression for procedure layout.  The procedure list is known
  before any body is compiled, so calls may target the current procedure, a
  later procedure, or a mutually recursive sibling.
\<close>

definition proc_layout_regression_prog :: imp_prog where
  "proc_layout_regression_prog = program {
     global int32 G;
     void f() {
       if (G < 1) { f() } else { G := G }
     }
     void g() { h() }
     void h() { g() }
     void inc() { G := G + 1 }
     void main() { f(); g(); inc() }
   }"

definition proc_layout_regression_cfg :: cfg where
  "proc_layout_regression_cfg =
     compile_prog (prog_tyenv proc_layout_regression_prog) (prog_table proc_layout_regression_prog)
       (prog_procs proc_layout_regression_prog)
       (STR ''main'') (prog_main proc_layout_regression_prog)"

text \<open>A call edge names its callee entry and its continuation directly, so each case below
  reads the callee off the edge instead of off a separate matching relation.\<close>

lemma proc_layout_regression_direct_recursion:
  "(Statement 1, CallEdge None [] [], FunctionEntry (STR ''f''), Statement 3)
     \<in> calls proc_layout_regression_cfg"
  unfolding proc_layout_regression_cfg_def proc_layout_regression_prog_def by eval

lemma proc_layout_regression_mutual_recursion:
  "(Statement 4, CallEdge None [] [], FunctionEntry (STR ''h''), Statement 5)
     \<in> calls proc_layout_regression_cfg \<and>
   (Statement 6, CallEdge None [] [], FunctionEntry (STR ''g''), Statement 7)
     \<in> calls proc_layout_regression_cfg"
  unfolding proc_layout_regression_cfg_def proc_layout_regression_prog_def by eval

text \<open>\<open>g\<close> calls \<open>h\<close>, which is declared after it: the procedure list is known before any
  body is compiled, so a forward call needs no second pass.\<close>

lemma proc_layout_regression_forward_call:
  "(Statement 4, CallEdge None [] [], FunctionEntry (STR ''h''), Statement 5)
     \<in> calls proc_layout_regression_cfg"
  unfolding proc_layout_regression_cfg_def proc_layout_regression_prog_def by eval

lemma proc_layout_regression_ordinary_call:
  "(Statement 12, CallEdge None [] [], FunctionEntry (STR ''inc''), Statement 13)
     \<in> calls proc_layout_regression_cfg"
  unfolding proc_layout_regression_cfg_def proc_layout_regression_prog_def by eval

text \<open>Layout regression: statement indices are allocated procedure by procedure in
  declaration order, with \<open>main\<close> last.  Each procedure's \<^const>\<open>FunctionEntry\<close> edge pins
  the first index of its block, and its \<^const>\<open>EA_Ret\<close> edge the last.\<close>

lemma proc_layout_regression_blocks:
  "(FunctionEntry (STR ''f''), EA_Nop, Statement 0) \<in> intra proc_layout_regression_cfg \<and>
   (Statement 3, EA_Ret None (STR ''f'') I32, FunctionResult (STR ''f'')) \<in> intra proc_layout_regression_cfg \<and>
   (FunctionEntry (STR ''g''), EA_Nop, Statement 4) \<in> intra proc_layout_regression_cfg \<and>
   (Statement 5, EA_Ret None (STR ''g'') I32, FunctionResult (STR ''g'')) \<in> intra proc_layout_regression_cfg \<and>
   (FunctionEntry (STR ''h''), EA_Nop, Statement 6) \<in> intra proc_layout_regression_cfg \<and>
   (Statement 7, EA_Ret None (STR ''h'') I32, FunctionResult (STR ''h'')) \<in> intra proc_layout_regression_cfg \<and>
   (FunctionEntry (STR ''inc''), EA_Nop, Statement 8) \<in> intra proc_layout_regression_cfg \<and>
   (Statement 9, EA_Ret None (STR ''inc'') I32, FunctionResult (STR ''inc''))
     \<in> intra proc_layout_regression_cfg \<and>
   (FunctionEntry (STR ''main''), EA_Nop, Statement 10) \<in> intra proc_layout_regression_cfg \<and>
   (Statement 13, EA_Ret None (STR ''main'') I32, FunctionResult (STR ''main''))
     \<in> intra proc_layout_regression_cfg"
  unfolding proc_layout_regression_cfg_def proc_layout_regression_prog_def by eval

end
