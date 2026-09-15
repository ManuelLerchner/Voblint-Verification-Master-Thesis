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
     Some [(Statement 1, Less (exp.N 0) (V (STR ''y'')), Lifted Check_Proved),
           (Statement 3, Less (exp.N 0) (V (STR ''y'')), Lifted Check_Refuted)]"
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
  publishes first. Int is where that is observable: its call-string registration
  \<open>int_cs_rule\<close> solves an always-join table and a warrowing one, and the two rows
  below are the two solves.
\<close>

lemma dispatch_demo_call_string_reads_the_named_rule:
  "(case run_voblint Int_Analysis Globals_Warrow (Ctx_CallString 1) dispatch_demo_prog of
      Analysed res \<Rightarrow>
        map (\<lambda>chk. (check_point chk, check_exp chk, check_verdict chk)) (res_checks res)
          = int_cs_rule.verdict_report 1 Globals_Warrow
              (declared_global dispatch_demo_prog) dispatch_demo_prog
    | _ \<Rightarrow> False)"
  "(case run_voblint Int_Analysis Globals_Join (Ctx_CallString 1) dispatch_demo_prog of
      Analysed res \<Rightarrow>
        map (\<lambda>chk. (check_point chk, check_exp chk, check_verdict chk)) (res_checks res)
          = int_cs_rule.verdict_report 1 Globals_Join
              (declared_global dispatch_demo_prog) dispatch_demo_prog
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

subsection \<open>What one statement makes of its state\<close>

text \<open>
  \<open>i := 0\<close> and \<open>i := i + 1\<close> both flow into the loop head, which stores only the
  join of the two, \<open>[0, 5]\<close>. Each statement's own step survives beside its source
  state: the body's assignment makes \<open>[1, 5]\<close> of the \<open>[0, 4]\<close> the guard lets
  through, and the assignment before the loop makes \<open>[0, 0]\<close>.
\<close>

definition step_demo_prog :: imp_prog where
  "step_demo_prog =
     program {
       fun main() {
         i = 0;
         while (i < 5) {
           i = i + 1;
         }
       }
     }"

text \<open>One variable's value at a point and after each of the point's steps, under Interval.\<close>

definition step_view :: "imp_prog \<Rightarrow> vname \<Rightarrow> pp \<Rightarrow> (abstract_value option lifted
    \<times> (pp \<times> abstract_value option lifted) list) list" where
  "step_view p x v =
     map (\<lambda>st. (map_lift (\<lambda>bs. map_of bs x) (state_value st),
                map (\<lambda>(w, s). (w, map_lift (\<lambda>bs. map_of bs x) s)) (state_steps st)))
       (filter (\<lambda>st. state_point st = v)
          (res_states (analysis_result Interval_Analysis Globals_Warrow Ctx_None p)))"

abbreviation step_demo_i :: "pp \<Rightarrow> (abstract_value option lifted
    \<times> (pp \<times> abstract_value option lifted) list) list" where
  "step_demo_i \<equiv> step_view step_demo_prog (STR ''i'')"

lemma step_demo_body_step:
  "step_demo_i (Statement 2) =
     [(Lifted (Some (IntervalValue (Ivl (Fin 0) (Fin 4)))),
       [(Statement 1, Lifted (Some (IntervalValue (Ivl (Fin 1) (Fin 5)))))])]"
  by eval

lemma step_demo_head_stores_join:
  "step_demo_i (Statement 1) =
     [(Lifted (Some (IntervalValue (Ivl (Fin 0) (Fin 5)))),
       [(Statement 2, Lifted (Some (IntervalValue (Ivl (Fin 0) (Fin 4))))),
        (Statement 3, Lifted (Some (IntervalValue (Ivl (Fin 5) (Fin 5)))))])]"
  by eval

lemma step_demo_before_loop_step:
  "step_demo_i (Statement 0) =
     [(Lifted (Some (IntervalValue (Ivl MinInf PlusInf))),
       [(Statement 1, Lifted (Some (IntervalValue (Ivl (Fin 0) (Fin 0)))))])]"
  by eval

text \<open>
  A guard no store satisfies has no successor. Its step reads back as \<^const>\<open>Bot\<close>,
  as the solve's reachability lift makes it, not as a store of empty values, and the
  dead branch then steps nowhere either.
\<close>

definition dead_step_prog :: imp_prog where
  "dead_step_prog =
     program {
       fun main() {
         x = 5;
         if (x < 0) {
           x = 1;
         }
       }
     }"

lemma dead_step_guard_is_bot:
  "step_view dead_step_prog (STR ''x'') (Statement 1) =
     [(Lifted (Some (IntervalValue (Ivl (Fin 5) (Fin 5)))),
       [(Statement 2, Bot),
        (Statement 4, Lifted (Some (IntervalValue (Ivl (Fin 5) (Fin 5)))))])]"
  by eval

lemma dead_step_branch_steps_nowhere:
  "step_view dead_step_prog (STR ''x'') (Statement 2) = [(Bot, [(Statement 4, Bot)])]"
  by eval

end

