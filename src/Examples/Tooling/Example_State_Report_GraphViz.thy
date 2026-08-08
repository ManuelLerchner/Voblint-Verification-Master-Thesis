theory Example_State_Report_GraphViz
  imports
    "Voblint_Analysis.Analysis_GraphViz"
    "Voblint_Analysis.Sign_Print"
    "Voblint_Analysis.Interval_Print"
    "Voblint_Examples.Example_Analysis_Dispatch"
begin

text \<open>
  \<open>raw_cfg_dot\<close>'s \<open>node_annotation\<close> hook already renders a verdict-only
  \<^const>\<open>classify_checks\<close> report through \<^const>\<open>check_report_node_annotation\<close>.
  This is the same idea over \<open>analyse_with_state\<close>'s richer report: the
  rendered label gains one line per queried variable, printed through the
  same domain print functions (\<open>string_of_sign\<close>, \<open>string_of_ivl\<close>) the
  standalone \<open>Sign_Print\<close>/\<open>Interval_Print\<close> theories already export, so the
  DOT rendering shows a real solved state rather than a hand-built one.
\<close>

fun string_of_abstract_value :: "abstract_value \<Rightarrow> string" where
  "string_of_abstract_value (SignValue s) = string_of_sign s"
| "string_of_abstract_value (IntervalValue i) = string_of_ivl i"

definition state_line :: "(vname \<Rightarrow> abstract_value) \<Rightarrow> vname \<Rightarrow> string" where
  "state_line f x = String.explode x @ ''='' @ string_of_abstract_value (f x)"

definition state_report_node_annotation ::
    "vname list \<Rightarrow> (pp \<times> bexp \<times> check_result \<times> (vname \<Rightarrow> abstract_value)) list
     \<Rightarrow> pp \<Rightarrow> graphviz_node_annotation option" where
  "state_report_node_annotation vars report v =
     (case find (\<lambda>entry. fst entry = v) report of
        None \<Rightarrow> None
      | Some (_, cnd, res, f) \<Rightarrow>
          (case check_result_annotation res cnd of
             Node_Annotation lbl style \<Rightarrow>
               Some (Node_Annotation (join_gv_nl (lbl # map (state_line f) vars)) style)))"

definition state_report_dot ::
    "analysis_kind \<Rightarrow> imp_prog \<Rightarrow> vname list \<Rightarrow> String.literal" where
  "state_report_dot kind p vars =
     raw_cfg_dot_lit (prog_table p) (prog_procs p) prog_main_name (prog_main p)
       (state_report_node_annotation vars (analyse_with_state kind p))"

text \<open>
  Reuses \<open>state_wiring_ex_prog\<close>
  (\<^theory>\<open>Voblint_Examples.Example_Analysis_Dispatch\<close>) rather than a fresh
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
