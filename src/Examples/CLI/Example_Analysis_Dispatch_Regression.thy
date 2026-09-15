theory Example_Analysis_Dispatch_Regression
  imports
    "Voblint_VIMP.VIMP_Notation" "Voblint_CLI.Analysis_Run"
begin

text \<open>
  \<^const>\<open>run_voblint\<close> on one small program, at every axis a caller chooses: the
  domain, the rule that merges contributions to side-effected globals, and the context
  policy. The CLI regression groups pin verdicts across globals, calls, repeated call
  sites and every selectable domain by running the generated analyzer; what stays here
  pins the operation Isabelle exports, by evaluation. The certified reading of such an
  answer is \<open>Example_End_To_End_Certificate\<close>.
\<close>

subsection \<open>One program, two verdicts\<close>

text \<open>
  \<open>y := 1\<close> then check \<open>0 < y\<close> (holds), then \<open>y := 0 - 1\<close> and check \<open>0 < y\<close>
  again (fails): Interval's numeric bounds settle both checks precisely.
\<close>

definition dispatch_demo_prog :: imp_prog where
  "dispatch_demo_prog =
     program {
       fun main() {
         y = 1;
         __voblint_check(0 < y);
         y = 0 - 1;
         __voblint_check(0 < y);

       }
     }"

definition dispatch_demo_checks where
  "dispatch_demo_checks D rule ctx =
     (case run_voblint D rule ctx dispatch_demo_prog of
        Analysed res \<Rightarrow> Some (map (\<lambda>chk. (check_point chk, check_exp chk, check_verdict chk))
                                 (res_checks res))
      | Malformed_Program \<Rightarrow> None)"

lemma dispatch_demo_interval_precise:
  "dispatch_demo_checks Interval_Analysis Globals_Warrow Ctx_None =
     Some [(Statement 1, Less (N 0) (V (STR ''y'')), Lifted Check_Proved),
           (Statement 3, Less (N 0) (V (STR ''y'')), Lifted Check_Refuted)]"
  by eval

text \<open>
  The rule is an argument of the solve, not of the report: a program with no side-effected
  global reaches the same verdicts under every rule, at every context policy, including a
  call string of length zero.
\<close>

lemma dispatch_demo_rule_invariant:
  "\<forall>rule \<in> {Globals_Join, Globals_Per_Origin, Globals_Warrow, Globals_Warrow_Per_Origin}.
     \<forall>ctx \<in> {Ctx_None, Ctx_EntryState, Ctx_CallString 0, Ctx_CallString 1}.
       dispatch_demo_checks Interval_Analysis rule ctx =
         dispatch_demo_checks Interval_Analysis Globals_Warrow Ctx_None"
  by eval

text \<open>
  The call-string plan reads the table its rule names, not whichever one its domain
  publishes first. Int is where that is observable: its call-string route publishes an
  always-join table and a warrowing one, and the two rows below are the two solves.
\<close>

lemma dispatch_demo_call_string_reads_the_named_rule:
  "(case run_voblint Int_Analysis Globals_Warrow (Ctx_CallString 1) dispatch_demo_prog of
      Analysed res \<Rightarrow>
        map (\<lambda>chk. (check_point chk, check_exp chk, check_verdict chk)) (res_checks res)
          = analyse_int_call_string_report_warrow 1 dispatch_demo_prog
    | _ \<Rightarrow> False)"
  "(case run_voblint Int_Analysis Globals_Join (Ctx_CallString 1) dispatch_demo_prog of
      Analysed res \<Rightarrow>
        map (\<lambda>chk. (check_point chk, check_exp chk, check_verdict chk)) (res_checks res)
          = analyse_int_call_string_report 1 dispatch_demo_prog
    | _ \<Rightarrow> False)"
  by eval+

text \<open>
  The public entry point at an entry-state configuration. Its check column and its
  states come off one solved table.
\<close>

lemma dispatch_demo_run_voblint_entry_state:
  "(case run_voblint Interval_Analysis Globals_Warrow Ctx_EntryState dispatch_demo_prog of
      Analysed res \<Rightarrow>
        map (\<lambda>chk. (check_point chk, check_verdict chk)) (res_checks res) =
          [(Statement 1, Lifted Check_Proved), (Statement 3, Lifted Check_Refuted)]
        \<and> res_contexts res = [Context_Entry []]
        \<and> res_states res \<noteq> []
    | _ \<Rightarrow> False)"
  by eval

lemma dispatch_demo_run_voblint_flat:
  "(case run_voblint Interval_Analysis Globals_Warrow Ctx_None dispatch_demo_prog of
      Analysed res \<Rightarrow> res_contexts res = [Context_Unit]
    | _ \<Rightarrow> False)"
  by eval

end

