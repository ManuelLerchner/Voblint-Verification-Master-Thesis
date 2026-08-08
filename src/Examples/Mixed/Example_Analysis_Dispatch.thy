theory Example_Analysis_Dispatch
  imports Example_Sign_Codegen Voblint_Analysis.Interval_Checks
begin

section \<open>A unified, verified check-report API across domains\<close>

text \<open>
  \<open>analyse_sign_report\<close> (\<^theory>\<open>Voblint_Examples.Example_Sign_Codegen\<close>) and
  \<open>interval_check_report\<close>/\<open>analyse_interval_report\<close>
  (\<^theory>\<open>Voblint_Analysis.Interval_Checks\<close>) already share one observable
  result type, \<open>check_report_entry list\<close>
  (\<^theory>\<open>Voblint_Core.Abstract_Checks\<close>), even though the two domains'
  internal abstract states (\<open>sign abs_state\<close> vs \<open>ivl abs_state\<close>) genuinely
  differ. \<open>analyse\<close> below is therefore a thin dispatcher, not a new proof:
  each branch reuses the domain's own already-generic, already-sound report
  function unchanged.

  Interval's warrowing variant (\<open>analyse_interval_td\<close>) is deliberately not a
  branch here: it has no soundness theorem yet (see
  \<^theory>\<open>Voblint_Analysis.Interval_Exec_Sound\<close>), so it stays outside this
  verified frontend rather than silently reporting an unbacked
  \<open>Check_Proved\<close>/\<open>Check_Refuted\<close>.
\<close>

datatype analysis_kind = Sign_Analysis | Interval_Analysis

fun analyse :: "analysis_kind \<Rightarrow> imp_prog \<Rightarrow> check_report_entry list" where
  "analyse Sign_Analysis p = analyse_sign_report p"
| "analyse Interval_Analysis p = analyse_interval_report p"

subsection \<open>A program that tells the two domains apart\<close>

text \<open>
  \<open>y := 1\<close> then check \<open>0 < y\<close> (should hold), then \<open>y := 0 - 1\<close> and check
  \<open>0 < y\<close> again (should now fail): a case where Interval's numeric bounds
  settle both checks precisely, while Sign's native D/G pipeline reports
  \<open>Check_Unknown\<close> for both --- the same always-join imprecision
  \<open>dgEx_inspect\<close> (\<^theory>\<open>Voblint_Examples.Exec_Sign_DG_Run\<close>) already
  documents for that pipeline, not a new limitation introduced here.
\<close>

definition dispatch_demo_prog :: imp_prog where
  "dispatch_demo_prog =
     program {
       void main() {
         y := 1;
         __voblint_check(0 < y);
         y := 0 - 1;
         __voblint_check(0 < y)
       }
     }"

lemma dispatch_demo_sign_unknown:
  "analyse Sign_Analysis dispatch_demo_prog =
     [(Statement 1, Less (N 0) (V ''y''), Check_Unknown),
      (Statement 3, Less (N 0) (V ''y''), Check_Unknown)]"
  by eval

lemma dispatch_demo_interval_precise:
  "analyse Interval_Analysis dispatch_demo_prog =
     [(Statement 1, Less (N 0) (V ''y''), Check_Proved),
      (Statement 3, Less (N 0) (V ''y''), Check_Refuted)]"
  by eval

subsection \<open>Executable code generation\<close>

text \<open>
  The unified dispatcher exports the same way its two branches already do:
  \<open>analyse\<close> genuinely takes the domain choice and the program as runtime
  arguments, not constants baked in at export time.
\<close>

export_code analyse Sign_Analysis Interval_Analysis
  in Haskell module_name Voblint_Analyse file_prefix "Voblint_Analyse"

export_code analyse Sign_Analysis Interval_Analysis
  in OCaml module_name Voblint_Analyse file_prefix "Voblint_Analyse_OCaml"

end
