theory Example_Analysis_Dispatch_Regression
  imports
    "Voblint_VIMP.VIMP_Notation" "Voblint_CLI.Analyse_Dispatch"
    "Voblint_VIMP.VIMP_Source_Print"
begin

text \<open>
  One \<^theory>\<open>Voblint_CLI.Analyse_Dispatch\<close> verdict carried all the way to a
  closed semantic theorem. \<open>dispatch_demo_first_check_certified\<close> is the point of
  this theory: a concrete \<^const>\<open>Check_Proved\<close> entry that \<^const>\<open>analyse\<close>
  actually returns, with every hypothesis of \<open>analyse_interval_proved_sound\<close>
  discharged rather than assumed --- well-formedness, solver termination, node
  coverage, and the report membership itself.

  Verdicts alone, on this and on the other dispatcher shapes (globals, calls,
  repeated call sites, both domains), are pinned by the executable corpus under
  \<open>tests/regression/\<close> instead, which runs the same analysis through the
  code-generated CLI in milliseconds rather than through \<open>eval\<close> at build time.
  What stays here is what a verdict fixture cannot express: the proof.
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
       void main() {
         y := 1;
         __voblint_check(0 < y);
         y := 0 - 1;
         __voblint_check(0 < y)
       }
     }"

lemma dispatch_demo_interval_precise:
  "analyse Interval_Analysis dispatch_demo_prog =
     [(Statement 1, Less (N 0) (V (STR ''y'')), Check_Proved),
      (Statement 3, Less (N 0) (V (STR ''y'')), Check_Refuted)]"
  by eval

text \<open>
  Structural facts about the compiled CFG, computed rather than asserted: the intra edges (there
  are no calls in this program) and the exit node --- the ingredients \<open>cfg_reaches_intra\<close> below
  chains into the first check's reachability to \<open>cfg_exit\<close>.
\<close>

lemma dispatch_demo_intra_eval:
  "intra (prog_cfg dispatch_demo_prog) =
     {(FunctionEntry (STR ''main''), EA_Nop, Statement 0),
      (Statement 0, EA_Assign (STR ''y'') (N 1), Statement 1),
      (Statement 1, EA_Check (Less (N 0) (V (STR ''y''))), Statement 2),
      (Statement 2, EA_Assign (STR ''y'') (Minus (N 0) (N 1)), Statement 3),
      (Statement 3, EA_Check (Less (N 0) (V (STR ''y''))), Statement 4),
      (Statement 4, EA_Ret None (STR ''main''), FunctionResult (STR ''main''))}"
  unfolding prog_cfg_def by eval

lemma dispatch_demo_exit_eval:
  "cfg_exit (prog_cfg dispatch_demo_prog) = FunctionResult (STR ''main'')"
  unfolding prog_cfg_def by (simp add: cfg_exit_compile_prog prog_main_name_def)

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
  The end-to-end witness: not just that the soundness machinery \<^emph>\<open>could\<close> certify a runtime
  verdict, but that it does, for one concrete program and node, with every hypothesis of
  \<open>analyse_interval_proved_sound\<close> actually discharged rather than left open. \<open>terminates\<close>
  reflects the same \<open>eval\<close> witness \<open>dispatch_demo_interval_precise\<close> already computes the report
  from; \<open>reach_exit\<close> is \<open>dispatch_demo_statement1_reaches_exit\<close> above; \<open>mem\<close> reads off
  \<open>dispatch_demo_interval_precise\<close>. No assumption remains: this is a closed theorem about a
  concrete \<open>Check_Proved\<close> value \<open>analyse\<close> actually returns.
\<close>

lemma dispatch_demo_calls_eval:
  "calls (prog_cfg dispatch_demo_prog) = {}"
  unfolding prog_cfg_def by eval

text \<open>
  Routed-spine cover facts: \<open>dispatch_demo_prog\<close> is straight-line, so every intra
  target is covered by the routed solve unconditionally.
\<close>

lemma dispatch_demo_terminates:
  "interval_conf_terminates_prog_warrow (declared_global dispatch_demo_prog) dispatch_demo_prog"
proof (rule interval_conf_terminates_prog_warrow_via_solve_c)
  show "TD_side_warrowing_apinis_Interp_solve_c
          (interval_conf_eqs (declared_global dispatch_demo_prog)
             (resolved_st_q_is_bot_for (declared_global_vars dispatch_demo_prog))
             (prog_table dispatch_demo_prog) (prog_procs dispatch_demo_prog))
          (cfg_exit (compile_prog (prog_table dispatch_demo_prog) (prog_procs dispatch_demo_prog)), ()) \<noteq> None"
    by eval
qed

lemma dispatch_demo_cover_edge_ball:
  "\<forall>(u, a, w) \<in> intra (prog_cfg dispatch_demo_prog).
     (w, ()) \<in> fst (interval_conf_sol_prog_warrow (declared_global dispatch_demo_prog) dispatch_demo_prog)"
  by eval

lemma dispatch_demo_cover_edge:
  "\<And>u a w ctx. (u, ctx) \<in> fst (interval_conf_sol_prog_warrow (declared_global dispatch_demo_prog) dispatch_demo_prog)
     \<Longrightarrow> (u, a, w) \<in> intra (prog_cfg dispatch_demo_prog)
     \<Longrightarrow> (w, ctx) \<in> fst (interval_conf_sol_prog_warrow (declared_global dispatch_demo_prog) dispatch_demo_prog)"
  using dispatch_demo_cover_edge_ball by auto

lemma dispatch_demo_entry_cov:
  "(cfg_entry (prog_cfg dispatch_demo_prog), ())
     \<in> fst (interval_conf_sol_prog_warrow (declared_global dispatch_demo_prog) dispatch_demo_prog)"
  by eval

theorem dispatch_demo_first_check_certified:
  "\<forall>s \<in> ltr_collect (declared_global dispatch_demo_prog) (prog_cfg dispatch_demo_prog)
           (cinit_stores (declared_global dispatch_demo_prog)) (Statement 1).
     truthy (aval (Less (N 0) (V (STR ''y''))) s)"
proof (rule analyse_interval_proved_sound)
  show "wf_compile_input (declared_global dispatch_demo_prog) (prog_table dispatch_demo_prog)
          (prog_procs dispatch_demo_prog)"
    by (auto simp: wf_compile_input_simps dispatch_demo_prog_def split: if_splits)
  show "interval_conf_terminates_prog_warrow (declared_global dispatch_demo_prog) dispatch_demo_prog"
    by (rule dispatch_demo_terminates)
  show "(cfg_entry (prog_cfg dispatch_demo_prog), ())
          \<in> fst (interval_conf_sol_prog_warrow (declared_global dispatch_demo_prog) dispatch_demo_prog)"
    by (rule dispatch_demo_entry_cov)
  show "\<And>u a w ctx. (u, ctx) \<in> fst (interval_conf_sol_prog_warrow (declared_global dispatch_demo_prog) dispatch_demo_prog)
          \<Longrightarrow> (u, a, w) \<in> intra (prog_cfg dispatch_demo_prog)
          \<Longrightarrow> (w, ctx) \<in> fst (interval_conf_sol_prog_warrow (declared_global dispatch_demo_prog) dispatch_demo_prog)"
    by (rule dispatch_demo_cover_edge)
  show "\<And>u ctx dst fs as q k. (u, ctx) \<in> fst (interval_conf_sol_prog_warrow (declared_global dispatch_demo_prog) dispatch_demo_prog)
          \<Longrightarrow> (u, CallEdge dst fs as, FunctionEntry q, k) \<in> calls (prog_cfg dispatch_demo_prog)
          \<Longrightarrow> (FunctionEntry q, ()) \<in> fst (interval_conf_sol_prog_warrow (declared_global dispatch_demo_prog) dispatch_demo_prog)"
    by (simp add: dispatch_demo_calls_eval)
  show "\<And>cl c1 dst fs as q k. (cl, c1) \<in> fst (interval_conf_sol_prog_warrow (declared_global dispatch_demo_prog) dispatch_demo_prog)
          \<Longrightarrow> (cl, CallEdge dst fs as, FunctionEntry q, k) \<in> calls (prog_cfg dispatch_demo_prog)
          \<Longrightarrow> (k, c1) \<in> fst (interval_conf_sol_prog_warrow (declared_global dispatch_demo_prog) dispatch_demo_prog)"
    by (simp add: dispatch_demo_calls_eval)
  show "(Statement 1, Less (N 0) (V (STR ''y'')), Check_Proved) \<in> set (analyse Interval_Analysis dispatch_demo_prog)"
    unfolding dispatch_demo_interval_precise by simp
qed

text \<open>
  \<^const>\<open>string_of_exp\<close> (\<^theory>\<open>Voblint_VIMP.VIMP_Source_Print\<close>) renders the
  \<open>exp\<close> half of a \<open>check_report_entry\<close> as a native string, so an external
  consumer of \<open>analyse\<close>'s report can print a check's condition without decoding
  the \<open>exp\<close> AST itself.
\<close>

lemma dispatch_demo_check_cond_rendered:
  "string_of_exp 0 (Less (N 0) (V (STR ''y''))) = ''0<y''"
  by eval

end

