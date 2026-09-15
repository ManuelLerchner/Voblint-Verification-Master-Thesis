theory Example_Analysis_Dispatch_Regression
  imports
    "Voblint_VIMP.VIMP_Notation" "Voblint_CLI.Analysis_Run"
    "Voblint_VIMP.VIMP_Source_Print"
begin

text \<open>
  One \<^theory>\<open>Voblint_CLI.Analyse_Dispatch\<close> verdict carried all the way to a
  closed semantic theorem. \<open>dispatch_demo_first_check_certified\<close> is the point of
  this theory: a concrete \<^const>\<open>Check_Proved\<close> entry that \<^const>\<open>analyse\<close>
  actually returns, with every hypothesis of \<open>analyse_interval_proved_sound\<close>
  discharged rather than assumed --- well-formedness, solver termination, node
  coverage, and the report membership itself.

  The CLI dispatch regression groups pin verdicts across globals, calls,
  repeated call sites, and every selectable domain. They run the generated
  analyzer directly. What stays here is what a verdict fixture cannot express:
  the semantic proof.
\<close>

subsection \<open>A program whose first check is certified\<close>

text \<open>
  \<open>y := 1\<close> then check \<open>0 < y\<close> (holds), then \<open>y := 0 - 1\<close> and check \<open>0 < y\<close>
  again (fails): Interval's numeric bounds settle both checks precisely. The
  computed report below is what the certified theorem reads its membership
  hypothesis off, so it is load-bearing, not a verdict witness of its own.
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

lemma dispatch_demo_interval_precise:
  "analyse Interval_Analysis dispatch_demo_prog =
     [(Statement 1, Less (N 0) (V (STR ''y'')), Check_Proved),
      (Statement 3, Less (N 0) (V (STR ''y'')), Check_Refuted)]"
  by eval

text \<open>
  The explicit-solver payload owns every projection of its solved table. Its globals
  column was empty when the CLI obtained that column through a second analysis call.
\<close>

lemma dispatch_demo_solver_payload_has_globals:
  "map_option (\<lambda>(_, _, globals). globals \<noteq> [])
     (solver_checked_payload_auto Interval_Analysis Solver_Warrow dispatch_demo_prog)
   = Some True"
  by eval

lemma dispatch_demo_call_string_payload:
  "(case cs_ctx_checked_payload_auto Interval_Analysis Solver_Warrow 1 dispatch_demo_prog of
      None \<Rightarrow> False
    | Some (_, verdicts, globals) \<Rightarrow>
        verdicts =
          [(Statement 1, Less (N 0) (V (STR ''y'')), Lifted Check_Proved),
           (Statement 3, Less (N 0) (V (STR ''y'')), Lifted Check_Refuted)]
        \<and> globals \<noteq> [])"
  by eval

text \<open>
  The call-string dispatcher reads the table its caller's plan named, not whichever
  one its domain publishes first. Int is where that is observable: its call-string
  route publishes an always-join table and a warrowing one, and the two rows below
  are the two solves. A dispatcher keyed on the domain alone answered the join row
  for both, while the text report answered from warrowing --- which is the
  discipline \<^const>\<open>resolve_analysis_config\<close> defaults that pairing to.
\<close>

lemma dispatch_demo_call_string_reads_the_named_discipline:
  "map_option (fst \<circ> snd)
     (cs_ctx_checked_payload_auto Int_Analysis Solver_Warrow 1 dispatch_demo_prog)
   = Some (analyse_int_call_string_report_warrow 1 dispatch_demo_prog)"
  "map_option (fst \<circ> snd)
     (cs_ctx_checked_payload_auto Int_Analysis Solver_Join 1 dispatch_demo_prog)
   = Some (analyse_int_call_string_report 1 dispatch_demo_prog)"
  by eval+

text \<open>
  The public entry point at an entry-state configuration. Its check column and its
  states come off one solved table: before this the graph, the verdicts and the seed
  listing each named an analyser of their own, so a report browser solved the same
  equation system three times and the columns agreed only by construction.
\<close>

lemma dispatch_demo_run_program_entry_state:
  "(case run_program Interval_Analysis None Ctx_EntryState dispatch_demo_prog of
      Result_Analysed res \<Rightarrow>
        map (\<lambda>chk. (check_point chk, check_verdict chk)) (res_checks res) =
          [(Statement 1, Lifted Check_Proved), (Statement 3, Lifted Check_Refuted)]
        \<and> res_contexts res = [Context_Entry []]
        \<and> res_states res \<noteq> []
    | _ \<Rightarrow> False)"
  by eval

text \<open>
  The same program at a context-free configuration reaches the same two verdicts
  through an entirely different plan --- a flat equation system, no activation keys
  --- which is what makes the pair worth stating: the entry point's answer is the
  analysis's, not the dispatcher's.
\<close>

lemma dispatch_demo_run_program_flat:
  "(case run_program Interval_Analysis None Ctx_None dispatch_demo_prog of
      Result_Analysed res \<Rightarrow>
        map (\<lambda>chk. (check_point chk, check_verdict chk)) (res_checks res) =
          [(Statement 1, Lifted Check_Proved), (Statement 3, Lifted Check_Refuted)]
        \<and> res_contexts res = [Context_Unit]
    | _ \<Rightarrow> False)"
  by eval



text \<open>
  Structural facts about the compiled CFG, computed rather than asserted: the intra edges (there
  are no calls in this program) and the exit node --- the ingredients \<open>cfg_reaches_intra\<close> below
  chains into the first check's reachability to \<open>cfg_exit\<close>.
\<close>

lemma dispatch_demo_intra_eval:
  "intra (prog_cfg dispatch_demo_prog) =
     {(FunctionEntry (STR ''main''), EA_Body (STR ''main''), Statement 0),
      (Statement 0, EA_Assign (STR ''y'') (N 1), Statement 1),
      (Statement 1, EA_Check (Less (N 0) (V (STR ''y''))), Statement 2),
      (Statement 2, EA_Assign (STR ''y'') (Minus (N 0) (N 1)), Statement 3),
      (Statement 3, EA_Check (Less (N 0) (V (STR ''y''))), Statement 4),
      (Statement 4, EA_Ret None (STR ''main''), FunctionResult (STR ''main''))}"
  unfolding prog_cfg_def by eval

lemma dispatch_demo_exit_eval:
  "cfg_exit (prog_cfg dispatch_demo_prog) = FunctionResult (STR ''main'')"
  unfolding prog_cfg_def by (simp add: prog_main_name_def)

text \<open>Structural reachability of the first check node to the exit --- a fact about the CFG's
  shape, following the same \<open>cfg_reaches_intra\<close>/\<open>cfg_reaches_trans\<close> chaining the
  store-only check examples use.\<close>

lemma dispatch_demo_statement1_reaches_exit:
  "cfg_reaches (prog_cfg dispatch_demo_prog) (Statement 1)
     (cfg_exit (prog_cfg dispatch_demo_prog))"
proof -
  have r1: "cfg_reaches (prog_cfg dispatch_demo_prog) (Statement 1) (Statement 2)"
    by (rule cfg_reaches_intra) (simp add: dispatch_demo_intra_eval)
  have r2: "cfg_reaches (prog_cfg dispatch_demo_prog) (Statement 2) (Statement 3)"
    by (rule cfg_reaches_intra) (simp add: dispatch_demo_intra_eval)
  have r3: "cfg_reaches (prog_cfg dispatch_demo_prog) (Statement 3) (Statement 4)"
    by (rule cfg_reaches_intra) (simp add: dispatch_demo_intra_eval)
  have r4: "cfg_reaches (prog_cfg dispatch_demo_prog) (Statement 4)
              (FunctionResult (STR ''main''))"
    by (rule cfg_reaches_intra) (simp add: dispatch_demo_intra_eval)
  show ?thesis
    unfolding dispatch_demo_exit_eval
    using r1 r2 r3 r4 cfg_reaches_trans by blast
qed

text \<open>
  Solver termination is reflected from the same executable solve the report above is read
  from; coverage is decided by \<^const>\<open>vars_cover_exec\<close> over the two edge enumerations, and
  \<open>interval_conf_vars_cover_prog_of_exec\<close>
  (\<^theory>\<open>Voblint_Analysis_Interval.Interval_Entry\<close>) transports that decision to the
  \<^const>\<open>vars_cover\<close> the corollary asks for.
\<close>

lemma dispatch_demo_terminates:
  "interval_conf_terminates_prog_warrow (declared_global dispatch_demo_prog) dispatch_demo_prog"
  by (rule interval_conf_terminates_prog_warrow_via_solve_c) eval

lemma dispatch_demo_vars_cover_exec:
  "vars_cover_exec (prog_cfg dispatch_demo_prog)
     (fst (interval_conf_sol_prog_warrow (declared_global dispatch_demo_prog)
             dispatch_demo_prog))"
  by eval

text \<open>
  The end-to-end witness: not just that the soundness machinery \<^emph>\<open>could\<close> certify a runtime
  verdict, but that it does, for one concrete program and node, with every hypothesis of
  \<open>analyse_interval_proved_sound\<close> actually discharged rather than left open. \<open>solve\<close>
  reflects the same \<open>eval\<close> witness \<open>dispatch_demo_interval_precise\<close> already computes the report
  from; \<open>cover\<close> is decided by evaluation and transported; \<open>mem\<close> reads off
  \<open>dispatch_demo_interval_precise\<close>. No assumption remains: this is a closed theorem about a
  concrete \<open>Check_Proved\<close> value \<open>analyse\<close> actually returns.
\<close>

theorem dispatch_demo_first_check_certified:
  "\<forall>s \<in> ltr_collect (declared_global dispatch_demo_prog) (prog_cfg dispatch_demo_prog)
           (cinit_stores (declared_global dispatch_demo_prog)) (Statement 1).
     truthy (aval (Less (N 0) (V (STR ''y''))) s)"
proof (rule analyse_interval_proved_sound)
  show
    "interval_conf_terminates_prog_warrow (declared_global dispatch_demo_prog)
       dispatch_demo_prog"
    by (rule dispatch_demo_terminates)
  show "vars_cover (prog_cfg dispatch_demo_prog)
          (fst (interval_conf_sol_prog_warrow (declared_global dispatch_demo_prog)
                  dispatch_demo_prog))"
    by (rule interval_conf_vars_cover_prog_of_exec[OF dispatch_demo_vars_cover_exec])
  show "(Statement 1, Less (N 0) (V (STR ''y'')), Check_Proved)
          \<in> set (analyse Interval_Analysis dispatch_demo_prog)"
    unfolding dispatch_demo_interval_precise by simp
qed

text \<open>
  \<^const>\<open>string_of_exp\<close> (\<^theory>\<open>Voblint_VIMP.VIMP_Source_Print\<close>) renders the
  \<open>exp\<close> half of a \<open>check_report_entry\<close> as a native string, so an external
  consumer of \<open>analyse\<close>'s report can print a check's condition without decoding
  the \<open>exp\<close> AST itself.
\<close>

lemma dispatch_demo_check_cond_rendered:
  "string_of_exp 0 (Less (N 0) (V (STR ''y''))) = STR ''0<y''"
  by eval

subsection \<open>The pipeline theorem on a concrete program\<close>

text \<open>
  \<open>analyse_source_sound\<close> (\<^theory>\<open>Voblint_CLI.Analyse_Dispatch\<close>) reads the
  report and a source run together, and leaves exactly one per-program
  hypothesis: \<^const>\<open>analyse_certified\<close>. Discharging it here, by evaluation on
  \<open>dispatch_demo_prog\<close>, shows the hypothesis is satisfiable and not a premise no
  program meets --- what is left in the theorem below is the source run itself.
\<close>

lemma dispatch_demo_reserved: "reserved_ret_var (declared_global dispatch_demo_prog)"
  unfolding reserved_ret_var_def dispatch_demo_prog_def by (simp add: ret_var_def)

lemma dispatch_demo_certified: "analyse_certified Interval_Analysis dispatch_demo_prog"
  by (simp add: dispatch_demo_terminates
        interval_conf_vars_cover_prog_of_exec[OF dispatch_demo_vars_cover_exec])

lemma dispatch_demo_wf:
  "wf_compile_input (declared_global dispatch_demo_prog) (prog_table dispatch_demo_prog)
     (prog_procs dispatch_demo_prog)"
  by (auto simp: wf_compile_input_simps dispatch_demo_prog_def split: if_splits)

theorem dispatch_demo_source_certified:
  assumes s0: "s0 \<in> cinit_stores (declared_global dispatch_demo_prog)"
    and run: "star (pstep (declared_global dispatch_demo_prog) (prog_table dispatch_demo_prog))
                (main_body (prog_table dispatch_demo_prog), s0, []) (residual, s, frs)"
  shows "\<exists>v stk. csim (prog_table dispatch_demo_prog) (prog_cfg dispatch_demo_prog)
                   (residual, s, frs) (v, s, stk)
                 \<and> (\<forall>c. (v, c, Check_Proved) \<in> set (analyse Interval_Analysis dispatch_demo_prog)
                        \<longrightarrow> truthy (aval c s))
                 \<and> (\<forall>c. (v, c, Check_Refuted) \<in> set (analyse Interval_Analysis dispatch_demo_prog)
                        \<longrightarrow> \<not> truthy (aval c s))"
  by (rule analyse_source_sound[OF dispatch_demo_wf dispatch_demo_certified s0 run])

end

