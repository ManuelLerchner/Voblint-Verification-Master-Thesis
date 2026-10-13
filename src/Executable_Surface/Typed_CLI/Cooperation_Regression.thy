theory Cooperation_Regression
  imports Typed_MCP
begin

section \<open>Regression: two analyses that ask each other\<close>

text \<open>
  Interval and Order run in one solve and ask each other through \<open>EvalInt\<close>, as Goblint's
  \<^verbatim>\<open>base\<close> asks its partners. \<open>f\<close> is entered only by \<open>f(100, 0)\<close>, so inside the branch
  \<open>x = 100\<close> and \<open>y = 0\<close>; without call strings both parameters range over \<open>[0, 100]\<close>.

  \<^item> \<open>(y <= x) + 1 == 2\<close>: Interval evaluates the comparison by asking it, and Order
    answers \<open>1\<close>. Neither analysis decides it alone.
  \<^item> The check under \<open>x < y\<close>: Interval's guard asks the condition, Order answers \<open>0\<close>, and
    the branch is unreachable. Interval alone reaches it and refutes the check.
  \<^item> \<open>z == 1\<close> after \<open>x = 0\<close>, which removes Order's fact: Interval stored \<open>z = 1\<close> when it
    evaluated the assignment through the channel, so its own state proves the check.
  \<^item> \<open>y == 1\<close> fails at the one store reaching it. No answer of either analysis decides it,
    and the product leaves it unknown.
\<close>

definition coop_prog :: imp_prog where
  "coop_prog = program {
     fun f(x, y) {
       if (y <= x) {
         __voblint_check((y <= x) + 1 == 2);
         z = (y <= x);
         if (x < y) { __voblint_check(0 == 1); }
         x = 0;
         __voblint_check(z == 1);
         __voblint_check(y == 1);
       }
     }
     fun main() { f(0, 100); f(100, 0); } }"

definition verdicts_of :: "('v \<times> 'c \<times> 'r) list \<Rightarrow> 'r list" where
  "verdicts_of rs = map (\<lambda>(_, _, r). r) rs"

lemma coop_verdicts:
  "verdicts_of (typed_mcp.verdict_report [] [Typed_Interval, Typed_Order] 0 Globals_Join tglobal coop_prog)
     = [Decided Check_Proved, Dead, Decided Check_Proved, Decided Check_Unknown]"
  "verdicts_of (typed_nonrel.verdict_report TYPE(ivl) [] 0 Globals_Join tglobal coop_prog)
     = [Decided Check_Unknown, Decided Check_Refuted, Decided Check_Unknown, Decided Check_Unknown]"
  "verdicts_of (typed_order.report Globals_Join [] tglobal coop_prog ())
     = [Check_Unknown, Check_Unknown, Check_Unknown, Check_Unknown]"
  by eval+

end

