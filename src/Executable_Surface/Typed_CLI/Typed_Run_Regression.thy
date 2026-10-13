theory Typed_Run_Regression
  imports Typed_Run "Voblint_VIMP.VIMP_Notation"
begin

section \<open>Regression: the typed entry point\<close>

text \<open>One check, four analyses. After the loop, \<open>x == 99\<close> needs both the bound and the
  class: Interval sees \<open>[99, 101]\<close>, Congruence alone loses the class to a possible
  wraparound, and only their reduced product decides the check.\<close>

definition step_prog :: imp_prog where
  "step_prog = program {
     fun main() { x = 0; while (x < 99) { x = x + 3; } __voblint_check(x == 99); } }"

definition verdicts :: "typed_answer \<Rightarrow> check_result list" where
  "verdicts a = (case a of Typed_Analysed rs \<Rightarrow> map (\<lambda>(_, _, r). r) rs | _ \<Rightarrow> [])"

lemma step_verdicts:
  "verdicts (run_typed Typed_Interval Globals_Join [] step_prog) = [Check_Unknown]"
  "verdicts (run_typed Typed_Congruence Globals_Join [] step_prog) = [Check_Unknown]"
  "verdicts (run_typed Typed_Int Globals_Join [] step_prog) = [Check_Proved]"
  "verdicts (run_typed Typed_Order Globals_Join [] step_prog) = [Check_Unknown]"
  "verdicts (run_typed Typed_Sign Globals_Join [] step_prog) = [Check_Unknown]"
  "verdicts (run_typed Typed_Parity Globals_Join [] step_prog) = [Check_Unknown]"
  by eval+

end
