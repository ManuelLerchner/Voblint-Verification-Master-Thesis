theory Example_Sign_Report_Regression
  imports
    "Voblint_Analysis_Sign.Sign_Checks"
    "Voblint_VIMP.VIMP_Notation"
begin

hide_const phase.N

section \<open>Four whole-program runs Sign's report has to keep getting right\<close>

text \<open>
  Four regression fixtures over \<^const>\<open>analyse_sign_report\<close>: each is a whole VIMP program
  the analysis runs end to end, with a \<^verbatim>\<open>by eval\<close> assertion pinning the
  verdicts it must produce. Two pin what carrying the whole abstract state in \<open>D\<close> buys ---
  a global assigned in a callee read back exactly at the caller, and a call whose argument
  refutes a branch guard leaving that arm genuinely dead. Two more exercise the shapes that
  separate how callee-entry values thread through the equation system: a recursive
  procedure, and one procedure called from two sites. Each fixture's own comment names the
  mechanism it isolates.
\<close>

subsection \<open>Base-style flow-sensitive global regressions\<close>

text \<open>
  \<open>D\<close> carries the whole abstract state, VIMP globals included, reachability-lifted, rather
  than routing globals through a separate flow-\<^emph>\<open>in\<close>sensitive solver-global unknown. The
  two fixtures here are what pins that: the first reads a callee's write back exactly at
  the caller, the second keeps a refuted branch arm out of the exit join.
\<close>

text \<open>This program is byte-identical to \<open>Example_Sign_Unit_Assembly\<close>'s
  \<open>sign_assembly_demo_prog\<close>, and deliberately so: it is the smallest program whose verdict
  separates a flow-sensitive global from a flow-insensitive one, and each theory defines it
  locally so neither witness inherits the other's imports.\<close>

definition sign_flow_sensitive_global_prog :: imp_prog where
  "sign_flow_sensitive_global_prog = program { global Gx;
     fun f() { Gx = 1; }
     fun main() { Gx = 0; f(); __voblint_check(0 < Gx); } }"

text \<open>
  Were globals routed through a separate flow-insensitive shared summary, \<open>Gx := 0\<close> and
  \<open>Gx := 1\<close> would both feed it and join to \<open>SNonNeg\<close>, leaving the check \<open>UNKNOWN\<close>. With
  the whole state lifted into \<open>D\<close>, the call's own local answer at the \<open>main\<close> exit carries
  \<open>Gx\<close>'s value exactly as \<^const>\<open>sign_tf_st_for\<close> and \<^const>\<open>sign_enter_st_for\<close> left it,
  so the check is exact.
\<close>

lemma sign_flow_sensitive_global_result:
  "(Statement 4, Less (N 0) (V (STR ''Gx'')), Check_Proved)
     \<in> set (analyse_sign_report sign_flow_sensitive_global_prog)"
  by eval

definition sign_dead_branch_bot_prog :: imp_prog where
  "sign_dead_branch_bot_prog = program { global Gx;
     fun f(n) { if (n < 0) { Gx = -1; } else { Gx = 1; } }
     fun main() { Gx = 0; f(5); __voblint_check(0 < Gx); } }"

text \<open>
  \<open>f\<close> is called with \<open>n = 5\<close>, abstracted to \<open>SPos\<close>: Sign's own comparison-against-zero
  tables refute \<open>n < 0\<close> exactly (\<open>SPos < SZero\<close> is definitely false), so the \<open>Gx := -1\<close>
  arm's own local answer is genuinely \<^const>\<open>Bot\<close> in the lifted carrier, not merely an
  imprecise contribution the exit join has to absorb. The two arms deliberately carry
  \<^emph>\<open>different\<close> signs so a leaked dead arm is observable: without the reachability lift,
  the join \<open>SNeg \<squnion> SPos = STop\<close> would leave the check \<open>UNKNOWN\<close> instead of \<open>PROVED\<close>.
  Contrast a numeric-bound guard such as \<open>n < 2\<close> at \<open>n = 5\<close>: Sign cannot refute that from
  \<open>SPos\<close> alone, where Interval can because it tracks exact bounds, so that shape does not
  isolate this property for Sign.
\<close>

lemma sign_dead_branch_bot_result:
  "(Statement 6, Less (N 0) (V (STR ''Gx'')), Check_Proved)
     \<in> set (analyse_sign_report sign_dead_branch_bot_prog)"
  by eval

subsection \<open>Recursion and repeated call sites\<close>

text \<open>
  Recursion and a procedure called from two sites are the two shapes that separate how
  callee-entry values thread through the equation system: a flow-sensitive local unknown
  revisited per predecessor against a keyed-seed slot per callee entry.
  \<open>sign_factorial_prog\<close> is the recursive one, mirroring Interval's own recursive-factorial
  fixture at Sign's coarser granularity; Sign has no \<open>--context\<close> flag, so the program shape
  is the only parameter to fix here. The entry check \<open>0 < n\<close> stays \<open>UNKNOWN\<close>: Sign has no
  context-sensitivity feature, so the callee entry joins over every call site's argument
  (here \<open>3\<close> and \<open>4\<close>).
\<close>

definition sign_factorial_prog :: imp_prog where
  "sign_factorial_prog =
     program {
       fun factorial(n) {
         __voblint_check(0 < n);
         if (n < 2) {
           return 1;
         } else {
           r = factorial(n - 1);
           __voblint_check(0 < r);
           return n * r;
         }
       }
       fun main() {
         a = factorial(3);
         b = factorial(4);
         __voblint_check(0 < a);
         __voblint_check(0 < b);
       }
     }"

text \<open>
  Statement indices run in source order, callees before \<open>main\<close>, one index per command plus
  one epilogue index per procedure. So \<open>factorial\<close> holds \<open>Statement 0\<close> to \<open>Statement 6\<close>:
  the entry check \<open>0 < n\<close> at \<open>0\<close>, the guard at \<open>1\<close>, \<open>return 1\<close> at \<open>2\<close>, the recursive call
  at \<open>3\<close>, the check \<open>0 < r\<close> at \<open>4\<close>, \<open>return n * r\<close> at \<open>5\<close> and the epilogue at \<open>6\<close>; \<open>main\<close>
  follows with its two calls at \<open>7\<close> and \<open>8\<close> and its two checks at \<open>9\<close> and \<open>10\<close>. The four
  verdicts below are therefore the program's four checks, in source order.
\<close>

lemma sign_factorial_result:
  "set (analyse_sign_report sign_factorial_prog) =
     {(Statement 0, Less (N 0) (V (STR ''n'')), Check_Unknown),
      (Statement 4, Less (N 0) (V (STR ''r'')), Check_Proved),
      (Statement 9, Less (N 0) (V (STR ''a'')), Check_Proved),
      (Statement 10, Less (N 0) (V (STR ''b'')), Check_Proved)}"
  by eval

text \<open>
  \<open>sign_two_call_sites_prog\<close> isolates repeated evaluation of one callee entry node without
  recursion's added complexity: one non-recursive procedure, two call sites. Unlike
  Interval's analogue, which genuinely loses precision at a repeated call site under
  Interval's infinite-height carrier and its warrowing solver, both checks here stay
  \<open>PROVED\<close>: Sign's finite height and its always-join solver rule never separate the two
  call sites' contributions here.

  Under the same numbering, \<open>square\<close>'s \<open>return n * n\<close> is \<open>Statement 0\<close> and its epilogue
  \<open>Statement 1\<close>, so \<open>main\<close>'s two calls are \<open>Statement 2\<close> and \<open>Statement 3\<close> and its two
  checks \<open>Statement 4\<close> and \<open>Statement 5\<close>.
\<close>

definition sign_two_call_sites_prog :: imp_prog where
  "sign_two_call_sites_prog =
     program {
       fun square(n) {
         return n * n;
       }
       fun main() {
         a = square(3);
         b = square(4);
         __voblint_check(0 < a);
         __voblint_check(0 < b);
       }
     }"

lemma sign_two_call_sites_result:
  "set (analyse_sign_report sign_two_call_sites_prog) =
     {(Statement 4, Less (N 0) (V (STR ''a'')), Check_Proved),
      (Statement 5, Less (N 0) (V (STR ''b'')), Check_Proved)}"
  by eval

end
