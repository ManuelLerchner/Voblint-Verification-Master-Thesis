theory Typed_Run_Regression
  imports Typed_MCP
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
  "verdicts (run_typed [Typed_Interval] Globals_Join (Typed_Call_String 0) [] step_prog) = [Check_Unknown]"
  "verdicts (run_typed [Typed_Congruence] Globals_Join (Typed_Call_String 0) [] step_prog) = [Check_Unknown]"
  "verdicts (run_typed [Typed_Int] Globals_Join (Typed_Call_String 0) [] step_prog) = [Check_Proved]"
  "verdicts (run_typed [Typed_Order] Globals_Join (Typed_Call_String 0) [] step_prog) = [Check_Unknown]"
  "verdicts (run_typed [Typed_Sign] Globals_Join (Typed_Call_String 0) [] step_prog) = [Check_Unknown]"
  "verdicts (run_typed [Typed_Parity] Globals_Join (Typed_Call_String 0) [] step_prog) = [Check_Unknown]"
  by eval+

subsection \<open>Call-string contexts\<close>

text \<open>\<open>inc\<close> is called with \<open>1\<close> and with \<open>10\<close>. Without contexts its two activations
  share one state, so each call's result lies in \<open>[2, 11]\<close> and neither check is decided.
  A call string of length \<open>1\<close> separates the two call sites, and so does the entry state, whose
  context is the value of \<open>x\<close>: both checks are proved either way.\<close>

definition calls_prog :: imp_prog where
  "calls_prog = program {
     fun inc(x) { return x + 1; }
     fun main() { a = inc(1); __voblint_check(a == 2); b = inc(10); __voblint_check(b == 11); } }"

lemma call_string_verdicts:
  "verdicts (run_typed [Typed_Interval] Globals_Join (Typed_Call_String 0) [] calls_prog) = [Check_Unknown, Check_Unknown]"
  "verdicts (run_typed [Typed_Interval] Globals_Join (Typed_Call_String 1) [] calls_prog) = [Check_Proved, Check_Proved]"
  "verdicts (run_typed [Typed_Interval] Globals_Join Typed_Entry_State [] calls_prog) = [Check_Proved, Check_Proved]"
  by eval+

end
