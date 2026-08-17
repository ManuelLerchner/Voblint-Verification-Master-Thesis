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

text \<open>
  \<open>Solver_Join\<close> and \<open>Solver_Warrow\<close> now diverge here, and the split is
  \<^emph>\<open>which pipeline each dispatches to\<close>, not a shared precision limit: on
  \<open>Interval_Analysis\<close>, \<open>Solver_Warrow\<close> dispatches to
  \<^const>\<open>analyse_interval_td_report\<close>, the Base-style production pipeline
  (\<^theory>\<open>Voblint_Analysis.Interval_Exec_Sound\<close>) where declared globals live
  flow-sensitively in \<open>D\<close> like any local, so \<open>total := 1\<close> reaches the check
  precisely and \<open>0 < total\<close> settles at \<open>Check_Proved\<close>. \<open>Solver_Join\<close>
  instead dispatches to \<^const>\<open>analyse_interval_report\<close>
  (\<^theory>\<open>Voblint_Analysis.Interval_Checks\<close>), built on the older
  \<open>ivl_exec_prog\<close>/\<open>side_env_lift_st\<close> pipeline that was not part of the
  production migration: \<open>cinit_ivl_st\<close> seeds every declared global at
  \<open>Ivl (Fin 0) (Fin 0)\<close>, and its flow-insensitive global summary joins that
  seed with the write's own contribution -- \<open>join [0,0] [1,1] = [0,1]\<close>,
  under which \<open>0 < total\<close> is genuinely undecided (\<open>0\<close> itself is a member).
  Not a precision bug in either pipeline; \<open>Solver_Join\<close>'s result reflects a
  pipeline this migration has not touched.
\<close>

lemma solver_choice_demo_interval_join_defined:
  "analyse_with_solver Interval_Analysis Solver_Join solver_choice_demo_prog
     = Some [(Statement 1, Less (N 0) (V (STR ''total'')), Check_Unknown)]"
  by eval

lemma solver_choice_demo_interval_warrow_defined:
  "analyse_with_solver Interval_Analysis Solver_Warrow solver_choice_demo_prog
     = Some [(Statement 1, Less (N 0) (V (STR ''total'')), Check_Proved)]"
  by eval

subsection \<open>Per-origin, isolated\<close>

text \<open>
  Kept out of \<open>analyse_with_solver\<close> (\<open>Interval_Analysis\<close>/\<open>Solver_PerOrigin\<close>
  returns \<open>None\<close> there) and tested here on its own: an earlier combined
  three-way comparison lemma for Interval hung under interactive \<open>by eval\<close>,
  and this isolates whether the per-origin construction itself is the
  actual cause, separate from \<open>analyse_with_solver\<close>'s dispatch or from a
  wrong expected value (which is what the Join/Warrow failures above turned
  out to be).
\<close>

lemma solver_choice_demo_interval_per_origin_defined:
  "analyse_interval_report_per_origin solver_choice_demo_prog
     = [(Statement 1, Less (N 0) (V (STR ''total'')), Check_Unknown)]"
  by eval

end
