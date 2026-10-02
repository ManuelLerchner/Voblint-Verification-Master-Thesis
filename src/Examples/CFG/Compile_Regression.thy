theory Compile_Regression
  imports "Voblint_Compile.Compile_Invariants"
begin

section \<open>Compiler regressions\<close>

text \<open>
  Two facts about the edges \<open>compile\<close> emits, moved out of \<open>Compile_Invariants\<close>: nothing
  in the core uses them, and the build is what keeps them true.
\<close>

subsection \<open>Returns and self-calls\<close>

text \<open>Both branches of a conditional return keep their own result edge, and a self-call of
  an ordinary procedure is a call edge into its own entry.\<close>
theorem compile_multi_return_converge:
  assumes "compile \<Pi> p (If b (Return e1) (Return e2)) k n = (n', en, E, K)"
  shows "(\<exists>j. (Statement j, EA_Ret e1 p, FunctionResult p) \<in> E)
       \<and> (\<exists>j. (Statement j, EA_Ret e2 p, FunctionResult p) \<in> E)"
  using compile_return_edge[OF assms, of e1] compile_return_edge[OF assms, of e2] by simp

text \<open>A self-call targets the procedure's own entry node; its call site is an ordinary
  statement node and its continuation is the caller's own next program point.  Restricted to
  \<open>p\<close> classified as an ordinary procedure: a self-call \<^const>\<open>special_table\<close> classifies
  instead sits on an intra edge, not a \<^const>\<open>CallEdge\<close>.\<close>
theorem compile_self_call_edge:
  assumes "special_table p = None"
  shows "(Statement n, CallEdge None (call_formals \<Pi> p) [], FunctionEntry p, k)
           \<in> snd (snd (snd (compile \<Pi> p (Call None p []) k n)))"
  using assms by simp

end
