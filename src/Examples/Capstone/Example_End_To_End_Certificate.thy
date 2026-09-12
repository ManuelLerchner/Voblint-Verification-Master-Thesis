theory Example_End_To_End_Certificate
  imports "Voblint_VIMP.VIMP_Notation" "Voblint_CLI.Analysis_Certified"
begin

section \<open>One configuration, one program, no premise left standing\<close>

text \<open>
  \<open>run_voblint_certified_source_sound\<close> is stated for an arbitrary configuration
  and an arbitrary program, so on its own it says nothing about any particular
  run: a caller still owes the solve's termination and the answer. This theory
  pays all of them, by evaluation, for one program at one configuration --- the
  product domain, a call-string context of length one, and always-join named
  explicitly rather than defaulted --- and reads the theorem's conclusion off
  the result.

  Three dimensions at once is the point. A composite domain exercises the
  product's transfer; a call-string policy keys the solved table by call history;
  and naming a discipline the pairing does not default to shows the certificate
  travels with the solver actually run, not with the one the registry prefers.
\<close>

subsection \<open>The program\<close>

text \<open>
  \<open>bump\<close> is called twice with different actuals, so a call string of length one
  files two activations of it under two contexts. The check reads the second
  result.
\<close>

definition certificate_demo_prog :: imp_prog where
  "certificate_demo_prog = program {
     fun bump(n) { return n + 1; }
     fun main() {
       a = bump(1);
       b = bump(41);
       __voblint_check(0 < b);
     }
   }"

lemma certificate_demo_wf: "wf_program_compile_input_exec certificate_demo_prog"
  by eval

subsection \<open>What the configuration answers\<close>

lemma certificate_demo_report:
  "(case run_voblint Int_Analysis (Some Solver_Join) (Ctx_CallString 1) View_Report
            certificate_demo_prog of
      Analysed out \<Rightarrow>
        map (\<lambda>row. (row_point row, row_verdict row)) (out_checks out)
          = [(Statement 4, Decided Check_Proved)]
    | _ \<Rightarrow> False)"
  by eval

text \<open>
  The endpoint below reads an \<open>out\<close>, so the answer is named rather than only
  inspected: \<^const>\<open>Analysed\<close> is what this configuration returns on this program,
  and the row above is the check column it returns.
\<close>

lemma certificate_demo_analysed:
  "\<exists>out. run_voblint Int_Analysis (Some Solver_Join) (Ctx_CallString 1) View_Report
           certificate_demo_prog = Analysed out
       \<and> map (\<lambda>row. (row_point row, row_verdict row)) (out_checks out)
           = [(Statement 4, Decided Check_Proved)]"
  using certificate_demo_report
  by (cases "run_voblint Int_Analysis (Some Solver_Join) (Ctx_CallString 1) View_Report
               certificate_demo_prog")
     auto

subsection \<open>One source run, constructed\<close>

text \<open>
  The endpoint speaks about a source execution, so this one is built rather than
  assumed: start every variable at \<open>0\<close>, run both calls and the check, and end with
  \<open>a = 2\<close> and \<open>b = 42\<close>. Two facts about the source semantics are needed and are
  general rather than about this program --- a check steps to \<^const>\<open>SKIP\<close>
  without touching the store, and a call whose body is a single \<^const>\<open>Return\<close>
  completes in three steps: enter the callee, publish the return value, and pop
  the frame writing the destination.
\<close>

lemma pcompletes_Check: "pcompletes gs \<Pi> (VIMP_Proc.com.Check cond) s s"
  by (rule star.step) (rule pstep.Check, rule star.refl)

lemma pcompletes_Call_return:
  assumes p: "\<Pi> p = Some decl"
      and bd: "body decl = VIMP_Proc.com.Return (Some e)"
      and arity: "length actuals = length (formals decl)"
      and dist: "distinct (formals decl)"
      and glob: "\<not> gs ret_var"
  shows "pcompletes gs \<Pi> (VIMP_Proc.com.Call dst p actuals) s
           (combine_assign dst
              (aval e (bind_formals (formals decl) (map (\<lambda>a. aval a s) actuals)
                         (enter_state gs s)))
              (combine_env gs s
                 (bind_formals (formals decl) (map (\<lambda>a. aval a s) actuals)
                    (enter_state gs s))))"
proof -
  let ?callee = "bind_formals (formals decl) (map (\<lambda>a. aval a s) actuals) (enter_state gs s)"
  let ?entered = "VIMP_Proc.com.Seq (VIMP_Proc.com.Return (Some e)) VIMP_Proc.com.Restore"
  let ?unwinding = "VIMP_Proc.com.Seq VIMP_Proc.com.Unwind VIMP_Proc.com.Restore"
  have c1: "pstep gs \<Pi> (VIMP_Proc.com.Call dst p actuals, s, [])
              (?entered, ?callee, [Frame s dst])"
    using arity bd dist p pstep_Call by fastforce
  have c2: "pstep gs \<Pi> (?entered, ?callee, [Frame s dst])
              (?unwinding, ?callee(ret_var := aval e ?callee), [Frame s dst])"
    by (rule pstep.Seq2) (rule pstep.ReturnSome)
  have c3: "pstep gs \<Pi> (?unwinding, ?callee(ret_var := aval e ?callee), [Frame s dst])
              (VIMP_Proc.com.SKIP,
               combine_assign dst (aval e ?callee) (combine_env gs s ?callee), [])"
    using pstep.UnwindAct [where gs = gs and \<Pi> = \<Pi> and dst = dst and fr = s and frs = "[]"
                             and s = "?callee(ret_var := aval e ?callee)"]
    by (simp add: glob)
  show ?thesis
    using c1 c2 c3 by (meson star.refl star.step)
qed

lemma certificate_demo_table:
  "prog_table certificate_demo_prog (STR ''bump'')
     = Some \<lparr>formals = [STR ''n''],
              body = VIMP_Proc.com.Return (Some (Plus (V (STR ''n'')) (N 1)))\<rparr>"
  by (simp add: certificate_demo_prog_def prog_main_name_def)

lemma certificate_demo_main:
  "main_body (prog_table certificate_demo_prog)
     = VIMP_Proc.com.Seq
         (VIMP_Proc.com.Seq (VIMP_Proc.com.Call (Some (STR ''a'')) (STR ''bump'') [N 1])
            (VIMP_Proc.com.Call (Some (STR ''b'')) (STR ''bump'') [N 41]))
         (VIMP_Proc.com.Check (Less (N 0) (V (STR ''b''))))"
  by (simp add: certificate_demo_prog_def main_body_def prog_main_name_def)

lemma certificate_demo_no_globals: "declared_global certificate_demo_prog = (\<lambda>_. False)"
  by (simp add: certificate_demo_prog_def fun_eq_iff)

lemma certificate_demo_call:
  "pcompletes (declared_global certificate_demo_prog) (prog_table certificate_demo_prog)
     (VIMP_Proc.com.Call (Some x) (STR ''bump'') [N k]) s (s(x := k + 1))"
  using pcompletes_Call_return
          [where \<Pi> = "prog_table certificate_demo_prog" and p = "STR ''bump''"
             and decl = "\<lparr>formals = [STR ''n''],
                          body = VIMP_Proc.com.Return (Some (Plus (V (STR ''n'')) (N 1)))\<rparr>"
             and e = "Plus (V (STR ''n'')) (N 1)" and actuals = "[N k]" and dst = "Some x"
             and gs = "declared_global certificate_demo_prog" and s = s,
           OF certificate_demo_table]
  by (simp add: certificate_demo_no_globals enter_state_def combine_env_def)

lemma certificate_demo_calls:
  "pcompletes (declared_global certificate_demo_prog) (prog_table certificate_demo_prog)
     (VIMP_Proc.com.Seq (VIMP_Proc.com.Call (Some (STR ''a'')) (STR ''bump'') [N 1])
        (VIMP_Proc.com.Call (Some (STR ''b'')) (STR ''bump'') [N 41]))
     (\<lambda>_. 0) ((\<lambda>_. 0)(STR ''a'' := 2, STR ''b'' := 42))"
proof -
  have c1: "pcompletes (declared_global certificate_demo_prog)
              (prog_table certificate_demo_prog)
              (VIMP_Proc.com.Call (Some (STR ''a'')) (STR ''bump'') [N 1]) (\<lambda>_. 0)
              ((\<lambda>_. 0)(STR ''a'' := 2))"
    using certificate_demo_call [where x = "STR ''a''" and k = 1 and s = "\<lambda>_. 0"] by simp
  have c2: "pcompletes (declared_global certificate_demo_prog)
              (prog_table certificate_demo_prog)
              (VIMP_Proc.com.Call (Some (STR ''b'')) (STR ''bump'') [N 41])
              ((\<lambda>_. 0)(STR ''a'' := 2))
              ((\<lambda>_. 0)(STR ''a'' := 2, STR ''b'' := 42))"
    using certificate_demo_call
            [where x = "STR ''b''" and k = 41 and s = "(\<lambda>_. 0)(STR ''a'' := 2)"]
    by simp
  show ?thesis by (rule pcompletes_Seq [OF c1 c2])
qed

lemma certificate_demo_run:
  "pcompletes (declared_global certificate_demo_prog) (prog_table certificate_demo_prog)
     (main_body (prog_table certificate_demo_prog)) (\<lambda>_. 0)
     ((\<lambda>_. 0)(STR ''a'' := 2, STR ''b'' := 42))"
  unfolding certificate_demo_main
  by (rule pcompletes_Seq [OF certificate_demo_calls pcompletes_Check])

text \<open>The same run stopped one step short of the check: both calls are done and
  \<^const>\<open>VIMP_Proc.com.Check\<close> is the command about to run.\<close>

lemma certificate_demo_to_check:
  "star (pstep (declared_global certificate_demo_prog) (prog_table certificate_demo_prog))
     (main_body (prog_table certificate_demo_prog), \<lambda>_. 0, [])
     (VIMP_Proc.com.Check (Less (N 0) (V (STR ''b''))),
      (\<lambda>_. 0)(STR ''a'' := 2, STR ''b'' := 42), [])"
  unfolding certificate_demo_main
  using psteps_Seq2 [OF certificate_demo_calls] by (meson Seq1 star.step star.refl star_trans)

lemma certificate_demo_init: "(\<lambda>_. 0) \<in> cinit_stores (declared_global certificate_demo_prog)"
  by (simp add: cinit_stores_def)


subsection \<open>The same run in the graph, at a node this theory can name\<close>

text \<open>
  \<^const>\<open>csim\<close> is structural and not functional, so the endpoint below can only
  say \<^emph>\<open>some\<close> node represents where the run stopped. Naming the check's own node
  takes a second witness, built in the graph rather than in the source: the
  collecting semantics at \<open>Statement 4\<close> really does contain the store this
  program computes, which is what makes the verdict claim there bite.

  Walking it takes one hop the collecting vocabulary does not close over
  step by step: \<^const>\<open>ltr_collect\<close> is closed under intra edges but not under a
  call or a return alone, since a return has to pop the trace's \<^emph>\<open>own\<close> caller.
  A call and its matching return together do compose, and that is
  \<open>ltr_collect_call_return_step\<close> in
  \<^theory>\<open>Voblint_CFG.LTR_Collect\<close>; the two hops through \<open>bump\<close> below are its two
  instances.
\<close>

lemma certificate_demo_entry_eval:
  "cfg_entry (prog_cfg certificate_demo_prog) = FunctionEntry (STR ''main'')"
  by (simp only: prog_cfg_def cfg_entry_compile_prog prog_main_name_def)

lemma certificate_demo_intra_eval:
  "intra (prog_cfg certificate_demo_prog) =
     {(FunctionEntry (STR ''bump''), EA_Body (STR ''bump''), Statement 0),
      (Statement 0, EA_Ret (Some (Plus (V (STR ''n'')) (N 1))) (STR ''bump''),
       FunctionResult (STR ''bump'')),
      (FunctionEntry (STR ''main''), EA_Body (STR ''main''), Statement 2),
      (Statement 5, EA_Ret None (STR ''main''), FunctionResult (STR ''main'')),
      (Statement 4, EA_Check (Less (N 0) (V (STR ''b''))), Statement 5)}"
  unfolding prog_cfg_def by eval

lemma certificate_demo_calls_eval:
  "calls (prog_cfg certificate_demo_prog) =
     {(Statement 3, CallEdge (Some (STR ''b'')) [STR ''n''] [N 41],
       FunctionEntry (STR ''bump''), Statement 4),
      (Statement 2, CallEdge (Some (STR ''a'')) [STR ''n''] [N 1],
       FunctionEntry (STR ''bump''), Statement 3)}"
  unfolding prog_cfg_def by eval

text \<open>
  A call to \<open>bump\<close> runs its whole body inside the callee's own activation: enter
  with the formal bound, take the body edge, then the return edge, which is where
  the returned value is published.
\<close>

lemma certificate_demo_bump_body:
  "intra_path (prog_cfg certificate_demo_prog)
     (FunctionEntry (STR ''bump''), (\<lambda>_. 0)(STR ''n'' := k))
     (FunctionResult (STR ''bump''), ((\<lambda>_. 0)(STR ''n'' := k))(ret_var := k + 1))"
proof (rule star_trans)
  show "intra_path (prog_cfg certificate_demo_prog)
          (FunctionEntry (STR ''bump''), (\<lambda>_. 0)(STR ''n'' := k))
          (Statement 0, (\<lambda>_. 0)(STR ''n'' := k))"
    by (rule intra_path_single [where a = "EA_Body (STR ''bump'')"])
       (auto simp: certificate_demo_intra_eval)
next
  show "intra_path (prog_cfg certificate_demo_prog)
          (Statement 0, (\<lambda>_. 0)(STR ''n'' := k))
          (FunctionResult (STR ''bump''), ((\<lambda>_. 0)(STR ''n'' := k))(ret_var := k + 1))"
    by (rule intra_path_single
          [where a = "EA_Ret (Some (Plus (V (STR ''n'')) (N 1))) (STR ''bump'')"])
       (auto simp: certificate_demo_intra_eval)
qed

text \<open>
  The two store maps a call crosses, at this program's one procedure: entry resets
  the locals and binds the formal, and the return writes the published value into
  the destination while the caller keeps its own locals. No globals are declared,
  so nothing survives entry but the binding.
\<close>

lemma certificate_demo_enter:
  "call_enter (declared_global certificate_demo_prog) (CallEdge dst [STR ''n''] [e]) s
     = (\<lambda>_. 0)(STR ''n'' := aval e s)"
  by (simp add: certificate_demo_no_globals call_enter_CallEdge enter_binding_def
      enter_frame_def fun_eq_iff)

lemma certificate_demo_combine:
  "combine_collect (declared_global certificate_demo_prog) (Some x) s
     (((\<lambda>_. 0)(STR ''n'' := k))(ret_var := v)) = s(x := v)"
  by (simp add: certificate_demo_no_globals combine_collect_def combine_env_def
      ret_var_def fun_eq_iff)

lemma certificate_demo_reaches_check:
  "(\<lambda>_. 0)(STR ''a'' := 2, STR ''b'' := 42)
     \<in> ltr_collect (declared_global certificate_demo_prog) (prog_cfg certificate_demo_prog)
           (cinit_stores (declared_global certificate_demo_prog)) (Statement 4)"
proof -
  have e0: "(\<lambda>_. 0) \<in> ltr_collect (declared_global certificate_demo_prog)
                          (prog_cfg certificate_demo_prog)
                          (cinit_stores (declared_global certificate_demo_prog))
                          (FunctionEntry (STR ''main''))"
    using ltr_collect_init
            [OF certificate_demo_init,
             where gs = "declared_global certificate_demo_prog"
               and g = "prog_cfg certificate_demo_prog"]
    by (simp add: certificate_demo_entry_eval)
  have s2: "(\<lambda>_. 0) \<in> ltr_collect (declared_global certificate_demo_prog)
                          (prog_cfg certificate_demo_prog)
                          (cinit_stores (declared_global certificate_demo_prog)) (Statement 2)"
    by (rule ltr_collect_intra_step [OF e0, where a = "EA_Body (STR ''main'')"])
       (auto simp: certificate_demo_intra_eval)
  have ce1: "(Statement 2, CallEdge (Some (STR ''a'')) [STR ''n''] [N 1],
              FunctionEntry (STR ''bump''), Statement 3)
               \<in> calls (prog_cfg certificate_demo_prog)"
    by (simp add: certificate_demo_calls_eval)
  have bd1: "intra_path (prog_cfg certificate_demo_prog)
               (FunctionEntry (STR ''bump''),
                call_enter (declared_global certificate_demo_prog)
                  (CallEdge (Some (STR ''a'')) [STR ''n''] [N 1]) (\<lambda>_. 0))
               (FunctionResult (STR ''bump''), ((\<lambda>_. 0)(STR ''n'' := 1))(ret_var := 1 + 1))"
    using certificate_demo_bump_body [where k = 1]
    by (simp add: certificate_demo_enter)
  have s3: "(\<lambda>_. 0)(STR ''a'' := 2)
              \<in> ltr_collect (declared_global certificate_demo_prog)
                    (prog_cfg certificate_demo_prog)
                    (cinit_stores (declared_global certificate_demo_prog)) (Statement 3)"
    using ltr_collect_call_return_step [OF s2 ce1 bd1]
    by (simp add: certificate_demo_combine)
  have ce2: "(Statement 3, CallEdge (Some (STR ''b'')) [STR ''n''] [N 41],
              FunctionEntry (STR ''bump''), Statement 4)
               \<in> calls (prog_cfg certificate_demo_prog)"
    by (simp add: certificate_demo_calls_eval)
  have bd2: "intra_path (prog_cfg certificate_demo_prog)
               (FunctionEntry (STR ''bump''),
                call_enter (declared_global certificate_demo_prog)
                  (CallEdge (Some (STR ''b'')) [STR ''n''] [N 41]) ((\<lambda>_. 0)(STR ''a'' := 2)))
               (FunctionResult (STR ''bump''), ((\<lambda>_. 0)(STR ''n'' := 41))(ret_var := 41 + 1))"
    using certificate_demo_bump_body [where k = 41]
    by (simp add: certificate_demo_enter)
  show ?thesis
    using ltr_collect_call_return_step [OF s3 ce2 bd2]
    by (simp add: certificate_demo_combine)
qed


subsection \<open>What the solve owes\<close>

text \<open>
  The solver's own run is the first. \<^const>\<open>routed_dg_pipeline.root_query\<close> has no
  code equation of its own --- its type does not mention the domain, so the
  generator cannot see its sort hypothesis --- and a call-string bound is a
  runtime argument, so no registration inlined it here. Unfolding it once is what
  the reflection below needs to reach \<open>eval\<close>.
\<close>

lemma certificate_demo_solve_c:
  "TD_side_always_join_Interp_solve_c
     (routed_dg_pipeline.equations (int_tf_st_for Refine_Fixpoint)
        (int_dom_enter_st_for Refine_Fixpoint) cinit_int_dom_st
        Call_String_Context.Global Call_String_Context.Seed (\<lambda>_. cs_route 1)
        (declared_global certificate_demo_prog) certificate_demo_prog)
     (routed_dg_pipeline.root_query [] certificate_demo_prog) \<noteq> None"
  unfolding routed_dg_pipeline.root_query_def by eval

lemma certificate_demo_terminates:
  "int_cs_join_terminates 1 (declared_global certificate_demo_prog) certificate_demo_prog"
  by (rule int_call_string_terminates_via_solve_c [OF certificate_demo_solve_c])

text \<open>
  Nothing about which keys the solve reached is owed: the keys a run can reach are
  closed once the solve terminates, so termination is the one fact about the solve
  this theory evaluates.
\<close>

lemma certificate_demo_config_terminates:
  "config_terminates Int_Analysis (Some Solver_Join) (Ctx_CallString 1) certificate_demo_prog"
  by (simp del: One_nat_def
        add: config_terminates_def mk_analysis_config_def certificate_demo_terminates)

subsection \<open>What the printed verdict means at that node\<close>

text \<open>
  The row the configuration prints carries its own check expression, so it is
  worth reading back in full rather than by point and verdict alone.
\<close>

lemma certificate_demo_report_full:
  "(case run_voblint Int_Analysis (Some Solver_Join) (Ctx_CallString 1) View_Report
            certificate_demo_prog of
      Analysed out \<Rightarrow>
        map (\<lambda>row. (row_point row, row_exp row, row_verdict row)) (out_checks out)
          = [(Statement 4, Less (N 0) (V (STR ''b'')), Decided Check_Proved)]
    | _ \<Rightarrow> False)"
  by eval

lemma certificate_demo_row:
  assumes ans: "run_voblint Int_Analysis (Some Solver_Join) (Ctx_CallString 1) View_Report
                  certificate_demo_prog = Analysed out"
  shows "\<exists>row. out_checks out = [row] \<and> row_point row = Statement 4
             \<and> row_exp row = Less (N 0) (V (STR ''b''))
             \<and> row_verdict row = Decided Check_Proved"
  using certificate_demo_report_full assms by (cases "out_checks out") auto

text \<open>
  The three facts about this configuration's own solve that the endpoint reads,
  named once and reused below. Every one of them is the always-join route's:
  \<^const>\<open>analyse_int_call_string_result\<close> is defined at
  \<open>TD_side_always_join_Interp_solve\<close> and \<open>Analysis_Run\<close> dispatches
  \<open>Plan_Int_CallString Solver_Join\<close> to exactly it, with the warrowing default
  carrying the \<open>_warrow\<close> suffix instead --- which is why the unsuffixed names pair
  with \<open>int_cs_join_terminates\<close> and its two companions above rather than clashing
  with them.
\<close>

lemma certificate_demo_union:
  "ltr_collect (declared_global certificate_demo_prog) (prog_cfg certificate_demo_prog)
       (cinit_stores (declared_global certificate_demo_prog)) u
     \<subseteq> (\<Union>c. activation_collect (declared_global certificate_demo_prog)
                (call_context_rel_of_fun (\<lambda>u c t. cs_context 1 u c t)) []
                (prog_cfg certificate_demo_prog)
                (cinit_stores (declared_global certificate_demo_prog)) u c)"
  by (rule equalityD1
        [OF analyse_int_call_string_ltr_collect_eq_Union [where ctx_fun = "cs_context 1"]])

lemma certificate_demo_sound:
  "activation_collect (declared_global certificate_demo_prog)
       (call_context_rel_of_fun (\<lambda>u c t. cs_context 1 u c t)) []
       (prog_cfg certificate_demo_prog)
       (cinit_stores (declared_global certificate_demo_prog)) u ctx
     \<subseteq> gamma_point
          (lookup_context (analyse_int_call_string_result 1 certificate_demo_prog) u ctx)"
  using analyse_int_call_string_sound_of_terminates
          [OF wf_program_compile_input_exec_sound [OF certificate_demo_wf]
              certificate_demo_terminates,
           where s = "\<lambda>u c t. t"]
  unfolding analyse_int_call_string_result_def
            analyse_int_call_string_result_for_def
            analyse_int_call_string_gamma_reader_eq_lookup .

lemma certificate_demo_result_finite:
  "finite_analysis_result (analyse_int_call_string_result 1 certificate_demo_prog)"
  using analyse_int_call_string_vars_finite [OF certificate_demo_terminates]
  by (simp add: finite_analysis_result_def analyse_int_call_string_result_def
      analyse_int_call_string_result_for_def
      routed_dg_pipeline.result_def routed_dg_pipeline.sol_vars_def)

text \<open>
  The endpoint's state conjunct, at the check's node rather than at an existential
  witness: the store the program computes lies in the concretization of the entry
  this configuration's solve filed for that node, under the context the run's own
  call string produced.
\<close>

lemma certificate_demo_result_covers_at_check:
  "analysis_result_covers Int_Analysis (Some Solver_Join) (Ctx_CallString 1)
     certificate_demo_prog (Statement 4) ((\<lambda>_. 0)(STR ''a'' := 2, STR ''b'' := 42))"
proof -
  obtain ctx st
    where "lookup_context (analyse_int_call_string_result 1 certificate_demo_prog)
             (Statement 4) ctx = Lifted st"
      and "(\<lambda>_. 0)(STR ''a'' := 2, STR ''b'' := 42) \<in> \<lbrakk>st\<rbrakk>"
    by (rule lookup_context_covers_of_activation
          [OF certificate_demo_union certificate_demo_sound certificate_demo_reaches_check])
  then have "table_covers (analyse_int_call_string_result 1 certificate_demo_prog) (Statement 4)
               ((\<lambda>_. 0)(STR ''a'' := 2, STR ''b'' := 42))"
    by (rule table_coversI)
  then show ?thesis
    by (simp del: One_nat_def add: analysis_result_covers_def mk_analysis_config_def)
qed

text \<open>
  And the endpoint's check conjunct at the same node, from
  \<open>ctx_rows_sound_at\<close>: the \<^const>\<open>Check_Proved\<close> the report prints is not a claim
  about the analyzer's table but about every execution the semantics admits there.
\<close>

lemma certificate_demo_checks_sound_at_check:
  assumes ans: "run_voblint Int_Analysis (Some Solver_Join) (Ctx_CallString 1) View_Report
                  certificate_demo_prog = Analysed out"
      and mem: "s \<in> ltr_collect (declared_global certificate_demo_prog)
                      (prog_cfg certificate_demo_prog)
                      (cinit_stores (declared_global certificate_demo_prog)) (Statement 4)"
  shows "checks_sound_at out (Statement 4) s"
proof -
  from ans
  have out_eq: "cs_output_of View_Report IntDomValue int_classify_check
                  (analyse_int_call_string_result 1 certificate_demo_prog) 1
                  certificate_demo_prog = Analysed out"
    by (simp add: run_voblint_def mk_analysis_config_def plan_answer_def split: if_splits)
  obtain ctx st
    where "lookup_context (analyse_int_call_string_result 1 certificate_demo_prog)
             (Statement 4) ctx = Lifted st"
      and "s \<in> \<lbrakk>st\<rbrakk>"
    by (rule lookup_context_covers_of_activation
          [OF certificate_demo_union certificate_demo_sound mem])
  then show ?thesis
    by (rule ctx_rows_sound_at
          [OF finite_contexts_at [OF certificate_demo_result_finite] _ _
              int_classify_check_proved int_classify_check_refuted
              out_checks_of_cs_output [OF out_eq]])
qed

theorem certificate_demo_check_semantically_true:
  assumes ans: "run_voblint Int_Analysis (Some Solver_Join) (Ctx_CallString 1) View_Report
                  certificate_demo_prog = Analysed out"
  shows "\<forall>s \<in> ltr_collect (declared_global certificate_demo_prog)
                  (prog_cfg certificate_demo_prog)
                  (cinit_stores (declared_global certificate_demo_prog)) (Statement 4).
           truthy (aval (Less (N 0) (V (STR ''b''))) s)"
proof (intro ballI)
  fix s :: store
  assume mem: "s \<in> ltr_collect (declared_global certificate_demo_prog)
                     (prog_cfg certificate_demo_prog)
                     (cinit_stores (declared_global certificate_demo_prog)) (Statement 4)"
  obtain row where r: "out_checks out = [row]" and rp: "row_point row = Statement 4"
    and re: "row_exp row = Less (N 0) (V (STR ''b''))"
    and rv: "row_verdict row = Decided Check_Proved"
    using certificate_demo_row [OF ans] by blast
  from certificate_demo_checks_sound_at_check [OF ans mem] r rp re rv
  show "truthy (aval (Less (N 0) (V (STR ''b''))) s)"
    unfolding checks_sound_at_def by simp
qed

text \<open>
  Everything above, in one place and with every witness named. The generic endpoint
  is existential in the node and the frame stack because \<^const>\<open>csim\<close> is
  structural; here the node is \<open>Statement 4\<close>, the store is the one the program
  computes, and the answer is the one \<^const>\<open>run_voblint\<close> returns --- so each
  conjunct of the headline theorem can be read off separately rather than inferred
  from an existential.
\<close>

theorem certificate_demo_full_certificate:
  obtains out where
    "run_voblint Int_Analysis (Some Solver_Join) (Ctx_CallString 1) View_Report
       certificate_demo_prog = Analysed out"
    "map (\<lambda>row. (row_point row, row_exp row, row_verdict row)) (out_checks out)
       = [(Statement 4, Less (N 0) (V (STR ''b'')), Decided Check_Proved)]"
    "pcompletes (declared_global certificate_demo_prog) (prog_table certificate_demo_prog)
       (main_body (prog_table certificate_demo_prog)) (\<lambda>_. 0)
       ((\<lambda>_. 0)(STR ''a'' := 2, STR ''b'' := 42))"
    "(\<lambda>_. 0)(STR ''a'' := 2, STR ''b'' := 42)
       \<in> ltr_collect (declared_global certificate_demo_prog)
             (prog_cfg certificate_demo_prog)
             (cinit_stores (declared_global certificate_demo_prog)) (Statement 4)"
    "analysis_result_covers Int_Analysis (Some Solver_Join) (Ctx_CallString 1)
       certificate_demo_prog (Statement 4) ((\<lambda>_. 0)(STR ''a'' := 2, STR ''b'' := 42))"
    "checks_sound_at out (Statement 4) ((\<lambda>_. 0)(STR ''a'' := 2, STR ''b'' := 42))"
    "truthy (aval (Less (N 0) (V (STR ''b''))) ((\<lambda>_. 0)(STR ''a'' := 2, STR ''b'' := 42)))"
proof (cases "run_voblint Int_Analysis (Some Solver_Join) (Ctx_CallString 1) View_Report
                certificate_demo_prog")
  case (Analysed out)
  then have rows: "map (\<lambda>row. (row_point row, row_exp row, row_verdict row)) (out_checks out)
                     = [(Statement 4, Less (N 0) (V (STR ''b'')), Decided Check_Proved)]"
    using certificate_demo_report_full by simp
  have true_here:
    "truthy (aval (Less (N 0) (V (STR ''b''))) ((\<lambda>_. 0)(STR ''a'' := 2, STR ''b'' := 42)))"
    using certificate_demo_check_semantically_true [OF Analysed]
          certificate_demo_reaches_check
    by blast
  show thesis
    by (rule that [OF Analysed rows certificate_demo_run certificate_demo_reaches_check
                      certificate_demo_result_covers_at_check
                      certificate_demo_checks_sound_at_check
                        [OF Analysed certificate_demo_reaches_check] true_here])
qed (use certificate_demo_report in simp_all)

subsection \<open>The endpoint, with nothing left to assume\<close>

text \<open>
  Nothing is left to assume. The run is the one built above, the answer is the one
  computed above, and the solve's termination is the fact evaluated above, so
  the endpoint's conclusion holds outright: the store the program actually ends
  with sits in the entry the always-join solve filed under that activation's own
  call string, and the \<^const>\<open>Check_Proved\<close> row the configuration printed is true
  of it.
\<close>

theorem certificate_demo_source_certified:
  "\<exists>out v stk.
     run_voblint Int_Analysis (Some Solver_Join) (Ctx_CallString 1) View_Report
       certificate_demo_prog = Analysed out
   \<and> map (\<lambda>row. (row_point row, row_verdict row)) (out_checks out)
       = [(Statement 4, Decided Check_Proved)]
   \<and> csim (prog_table certificate_demo_prog) (prog_cfg certificate_demo_prog)
       (SKIP, (\<lambda>_. 0)(STR ''a'' := 2, STR ''b'' := 42), [])
       (v, (\<lambda>_. 0)(STR ''a'' := 2, STR ''b'' := 42), stk)
   \<and> (\<lambda>_. 0)(STR ''a'' := 2, STR ''b'' := 42)
       \<in> ltr_collect (declared_global certificate_demo_prog)
             (prog_cfg certificate_demo_prog)
             (cinit_stores (declared_global certificate_demo_prog)) v
   \<and> analysis_result_covers Int_Analysis (Some Solver_Join) (Ctx_CallString 1)
       certificate_demo_prog v ((\<lambda>_. 0)(STR ''a'' := 2, STR ''b'' := 42))
   \<and> checks_sound_at out v ((\<lambda>_. 0)(STR ''a'' := 2, STR ''b'' := 42))"
proof (cases "run_voblint Int_Analysis (Some Solver_Join) (Ctx_CallString 1) View_Report
                certificate_demo_prog")
  case (Analysed out)
  then have rows: "map (\<lambda>row. (row_point row, row_verdict row)) (out_checks out)
                     = [(Statement 4, Decided Check_Proved)]"
    using certificate_demo_report by simp
  from run_voblint_certified_source_sound
         [OF certificate_demo_init certificate_demo_run certificate_demo_config_terminates
             Analysed]
  show ?thesis using Analysed rows by meson
qed (use certificate_demo_report in simp_all)

text \<open>
  The check theorem, with nothing left to assume.  The run stopped just before the
  check finds the report's row for the checked condition at a node that store
  reaches, and the \<^const>\<open>Check_Proved\<close> in it is true of the store.
\<close>

theorem certificate_demo_check_row_sound:
  "\<exists>out. run_voblint Int_Analysis (Some Solver_Join) (Ctx_CallString 1) View_Report
           certificate_demo_prog = Analysed out
     \<and> (\<exists>row \<in> set (out_checks out). row_exp row = Less (N 0) (V (STR ''b''))
          \<and> (\<lambda>_. 0)(STR ''a'' := 2, STR ''b'' := 42)
              \<in> ltr_collect (declared_global certificate_demo_prog)
                   (prog_cfg certificate_demo_prog)
                   (cinit_stores (declared_global certificate_demo_prog)) (row_point row)
          \<and> row_verdict row = Decided Check_Proved
          \<and> truthy (aval (Less (N 0) (V (STR ''b'')))
                     ((\<lambda>_. 0)(STR ''a'' := 2, STR ''b'' := 42))))"
proof (cases "run_voblint Int_Analysis (Some Solver_Join) (Ctx_CallString 1) View_Report
                certificate_demo_prog")
  case (Analysed out)
  have rows: "map (\<lambda>row. (row_point row, row_verdict row)) (out_checks out)
                = [(Statement 4, Decided Check_Proved)]"
    using certificate_demo_report Analysed by simp
  from run_voblint_check_sound
         [OF certificate_demo_init certificate_demo_to_check next_check.simps(1)
             certificate_demo_config_terminates Analysed]
  obtain row
    where row: "row \<in> set (out_checks out)"
      and re: "row_exp row = Less (N 0) (V (STR ''b''))"
      and mem: "(\<lambda>_. 0)(STR ''a'' := 2, STR ''b'' := 42)
                  \<in> ltr_collect (declared_global certificate_demo_prog)
                       (prog_cfg certificate_demo_prog)
                       (cinit_stores (declared_global certificate_demo_prog)) (row_point row)"
      and pr: "row_verdict row = Decided Check_Proved
                 \<longrightarrow> truthy (aval (Less (N 0) (V (STR ''b'')))
                            ((\<lambda>_. 0)(STR ''a'' := 2, STR ''b'' := 42)))"
    by blast
  have "(row_point row, row_verdict row) \<in> set [(Statement 4, Decided Check_Proved)]"
    unfolding rows [symmetric] using row by auto
  then have "row_verdict row = Decided Check_Proved" by simp
  with Analysed row re mem pr show ?thesis by blast
qed (use certificate_demo_report in simp_all)

end
