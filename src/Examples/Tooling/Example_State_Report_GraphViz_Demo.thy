theory Example_State_Report_GraphViz_Demo
  imports
    "Voblint_CLI.State_Report_GraphViz"
    Example_Analysis_Dispatch_Regression
begin

text \<open>
  Reuses \<open>state_wiring_ex_prog\<close>
  (\<^theory>\<open>Voblint_Examples.Example_Analysis_Dispatch_Regression\<close>) rather than a fresh
  program: a single exact write with no widening, so \<^const>\<open>analyse\<close>
  itself already classifies the check \<open>Check_Proved\<close> under
  \<open>Interval_Analysis\<close>, and \<open>analyse_with_state\<close> reports the exact
  \<open>[5,5]\<close> interval behind it --- the checked verdict and the rendered
  state agree because both come from the same solved report.
\<close>

definition state_report_demo_dot :: String.literal where
  "state_report_demo_dot =
     state_report_dot Interval_Analysis state_wiring_ex_prog [STR ''x'']"

ML_val \<open>writeln (@{code state_report_demo_dot})\<close>

end
