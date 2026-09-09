theory Dispatch_Tables
  imports
    Analysis_Config
    Dispatch_Carrier
begin

section \<open>The dispatcher's domain and solver tables\<close>

text \<open>
  GENERATED FILE. Source: \<^verbatim>\<open>assembly/analyses.yaml\<close>; generator:
  \<^verbatim>\<open>scripts/gen_analysis_assembly.py\<close>. Regenerate with the generator
  rather than hand-editing; a drift check compares regenerated output against
  this file.

  A pairing of domain and solver discipline is supported exactly when the registry
  publishes a route for it, and answers \<^const>\<open>None\<close> otherwise. The four
  tables below are that one list, read four ways; keeping them in step is what the
  generator is for.
\<close>

fun analyse :: "analysis_domain \<Rightarrow> imp_prog \<Rightarrow> check_report_entry list" where
  "analyse Sign_Analysis p = analyse_sign_report p"
| "analyse Interval_Analysis p = analyse_interval_td_report p"
| "analyse Parity_Analysis p = analyse_parity_report p"
| "analyse Int_Analysis p = analyse_int_report p"
| "analyse Congruence_Analysis p = analyse_congruence_report p"

fun analyse_with_solver ::
    "analysis_domain \<Rightarrow> solver_choice \<Rightarrow> imp_prog
       \<Rightarrow> check_report_entry list option" where
  "analyse_with_solver Sign_Analysis Solver_Join p = Some (analyse_sign_report p)"
| "analyse_with_solver Sign_Analysis Solver_PerOrigin p = Some (analyse_sign_report_per_origin p)"
| "analyse_with_solver Sign_Analysis Solver_Warrow p = None"
| "analyse_with_solver Sign_Analysis Solver_WarrowPerOrigin p = None"
| "analyse_with_solver Interval_Analysis Solver_Join p = Some (analyse_interval_report p)"
| "analyse_with_solver Interval_Analysis Solver_PerOrigin p =
     Some (analyse_interval_report_per_origin p)"
| "analyse_with_solver Interval_Analysis Solver_Warrow p = Some (analyse_interval_td_report p)"
| "analyse_with_solver Interval_Analysis Solver_WarrowPerOrigin p =
     Some (analyse_interval_report_wpo p)"
| "analyse_with_solver Parity_Analysis Solver_Join p = Some (analyse_parity_report p)"
| "analyse_with_solver Parity_Analysis Solver_PerOrigin p =
     Some (analyse_parity_report_per_origin p)"
| "analyse_with_solver Parity_Analysis Solver_Warrow p = None"
| "analyse_with_solver Parity_Analysis Solver_WarrowPerOrigin p = None"
| "analyse_with_solver Int_Analysis Solver_Join p = Some (analyse_int_report_join p)"
| "analyse_with_solver Int_Analysis Solver_PerOrigin p = Some (analyse_int_report_per_origin p)"
| "analyse_with_solver Int_Analysis Solver_Warrow p = Some (analyse_int_report p)"
| "analyse_with_solver Int_Analysis Solver_WarrowPerOrigin p = Some (analyse_int_report_wpo p)"
| "analyse_with_solver Congruence_Analysis Solver_Join p = Some (analyse_congruence_report p)"
| "analyse_with_solver Congruence_Analysis Solver_PerOrigin p =
     Some (analyse_congruence_report_per_origin p)"
| "analyse_with_solver Congruence_Analysis Solver_Warrow p = None"
| "analyse_with_solver Congruence_Analysis Solver_WarrowPerOrigin p = None"

lemma analyse_with_solver_sign_default:
  "analyse_with_solver Sign_Analysis Solver_Join p = Some (analyse Sign_Analysis p)"
  by simp

lemma analyse_with_solver_interval_default:
  "analyse_with_solver Interval_Analysis Solver_Warrow p = Some (analyse Interval_Analysis p)"
  by simp

lemma analyse_with_solver_parity_default:
  "analyse_with_solver Parity_Analysis Solver_Join p = Some (analyse Parity_Analysis p)"
  by simp

lemma analyse_with_solver_int_default:
  "analyse_with_solver Int_Analysis Solver_Warrow p = Some (analyse Int_Analysis p)"
  by simp

lemma analyse_with_solver_congruence_default:
  "analyse_with_solver Congruence_Analysis Solver_Join p = Some (analyse Congruence_Analysis p)"
  by simp

fun analyse_with_state ::
    "analysis_domain \<Rightarrow> solver_choice \<Rightarrow> imp_prog
       \<Rightarrow> (pp \<times> exp \<times> check_result \<times> bool
             \<times> abstract_value abs_state) list option" where
  "analyse_with_state Sign_Analysis Solver_Join p =
     Some (tag_states SignValue (analyse_sign_report_with_state p))"
| "analyse_with_state Sign_Analysis Solver_PerOrigin p =
     Some (tag_states SignValue (sign_per_origin.report_with_state p))"
| "analyse_with_state Sign_Analysis Solver_Warrow p = None"
| "analyse_with_state Sign_Analysis Solver_WarrowPerOrigin p = None"
| "analyse_with_state Interval_Analysis Solver_Join p =
     Some (tag_states IntervalValue (interval_join.report_with_state p))"
| "analyse_with_state Interval_Analysis Solver_PerOrigin p =
     Some (tag_states IntervalValue (interval_per_origin.report_with_state p))"
| "analyse_with_state Interval_Analysis Solver_Warrow p =
     Some (tag_states IntervalValue (analyse_interval_td_report_with_state p))"
| "analyse_with_state Interval_Analysis Solver_WarrowPerOrigin p =
     Some (tag_states IntervalValue (interval_wpo.report_with_state p))"
| "analyse_with_state Parity_Analysis Solver_Join p =
     Some (tag_states ParityValue (analyse_parity_report_with_state p))"
| "analyse_with_state Parity_Analysis Solver_PerOrigin p =
     Some (tag_states ParityValue (parity_per_origin.report_with_state p))"
| "analyse_with_state Parity_Analysis Solver_Warrow p = None"
| "analyse_with_state Parity_Analysis Solver_WarrowPerOrigin p = None"
| "analyse_with_state Int_Analysis Solver_Join p =
     Some (tag_states IntDomValue (int_join.report_with_state p))"
| "analyse_with_state Int_Analysis Solver_PerOrigin p =
     Some (tag_states IntDomValue (int_per_origin.report_with_state p))"
| "analyse_with_state Int_Analysis Solver_Warrow p =
     Some (tag_states IntDomValue (analyse_int_report_with_state p))"
| "analyse_with_state Int_Analysis Solver_WarrowPerOrigin p =
     Some (tag_states IntDomValue (int_wpo.report_with_state p))"
| "analyse_with_state Congruence_Analysis Solver_Join p =
     Some (tag_states CongruenceValue (analyse_congruence_report_with_state p))"
| "analyse_with_state Congruence_Analysis Solver_PerOrigin p =
     Some (tag_states CongruenceValue (congruence_per_origin.report_with_state p))"
| "analyse_with_state Congruence_Analysis Solver_Warrow p = None"
| "analyse_with_state Congruence_Analysis Solver_WarrowPerOrigin p = None"

lemma analyse_with_state_some_iff_with_solver:
  "(analyse_with_state d s p = None) = (analyse_with_solver d s p = None)"
  by (cases d; cases s) simp_all

fun analyse_with_state_default ::
    "analysis_domain \<Rightarrow> imp_prog
       \<Rightarrow> (pp \<times> exp \<times> check_result \<times> bool
             \<times> abstract_value abs_state) list" where
  "analyse_with_state_default Sign_Analysis p =
     tag_states SignValue (analyse_sign_report_with_state p)"
| "analyse_with_state_default Interval_Analysis p =
     tag_states IntervalValue (analyse_interval_td_report_with_state p)"
| "analyse_with_state_default Parity_Analysis p =
     tag_states ParityValue (analyse_parity_report_with_state p)"
| "analyse_with_state_default Int_Analysis p =
     tag_states IntDomValue (analyse_int_report_with_state p)"
| "analyse_with_state_default Congruence_Analysis p =
     tag_states CongruenceValue (analyse_congruence_report_with_state p)"

lemma analyse_with_state_default_eq:
  "analyse_with_state Sign_Analysis Solver_Join p =
       Some (analyse_with_state_default Sign_Analysis p)"
  "analyse_with_state Interval_Analysis Solver_Warrow p =
       Some (analyse_with_state_default Interval_Analysis p)"
  "analyse_with_state Parity_Analysis Solver_Join p =
       Some (analyse_with_state_default Parity_Analysis p)"
  "analyse_with_state Int_Analysis Solver_Warrow p =
       Some (analyse_with_state_default Int_Analysis p)"
  "analyse_with_state Congruence_Analysis Solver_Join p =
       Some (analyse_with_state_default Congruence_Analysis p)"
  by simp_all

end
