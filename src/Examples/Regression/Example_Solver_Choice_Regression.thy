theory Example_Solver_Choice_Regression
  imports Analyse_Dispatch
begin

section \<open>Regression: solver-choice comparison via analyse_with_solver\<close>

text \<open>
  Small acceptance-regression witnesses for issue #131's \<open>analyse_with_solver\<close>:
  the same program's report is compared across solver choices where a
  domain supports more than one, following the same \<open>by eval\<close> acceptance
  style as \<open>Example_Analysis_Dispatch_Regression\<close>. Not a precision
  showcase -- \<open>loop_head_across_update_rules\<close> (\<open>Exec_Ivl_Run\<close>) already
  demonstrates that different update rules can agree on the same bound for
  a bounded loop; the point here is that \<open>analyse_with_solver\<close> actually
  wires each named choice to the right concrete report function on a
  program with a real global side effect (so the update-rule choice is
  genuinely exercised, not vacuous), not that solvers diverge in general.
\<close>

text \<open>
  A single constant write to a global, not a self-referential one (contrast
  \<open>total := total + n\<close>, the documented always-join non-termination
  reproducer, \<^theory>\<open>Voblint_Examples.Analyse_Dispatch\<close>): this program
  terminates under every update rule, so it can genuinely compare all
  three without hitting that known divergence.
\<close>

definition solver_choice_demo_prog :: imp_prog where
  "solver_choice_demo_prog =
     program {
       global total;
       void main() {
         total := 1;
         __voblint_check(0 < total)
       }
     }"

lemma solver_choice_demo_sign_join_eq_per_origin:
  "analyse_with_solver Sign_Analysis Solver_Join solver_choice_demo_prog =
     analyse_with_solver Sign_Analysis Solver_PerOrigin solver_choice_demo_prog"
  by eval

lemma solver_choice_demo_sign_warrow_unsupported:
  "analyse_with_solver Sign_Analysis Solver_Warrow solver_choice_demo_prog = None"
  by eval

lemma solver_choice_demo_interval_join_defined:
  "analyse_with_solver Interval_Analysis Solver_Join solver_choice_demo_prog
     = Some [(Statement 1, Less (N 0) (V (STR ''total'')), Check_Proved)]"
  by eval

lemma solver_choice_demo_interval_warrow_defined:
  "analyse_with_solver Interval_Analysis Solver_Warrow solver_choice_demo_prog
     = Some [(Statement 1, Less (N 0) (V (STR ''total'')), Check_Proved)]"
  by eval

end
