theory Example_Analysis_Dispatch_Regression
  imports
    "Voblint_CLI.Analyse_Dispatch"
begin

text \<open>
  Acceptance-regression witnesses for \<^theory>\<open>Voblint_CLI.Analyse_Dispatch\<close>'s
  runtime dispatcher: concrete programs plus \<open>by eval\<close>/proved checks against
  their expected reports. This theory is a consumer of \<open>Analyse_Dispatch\<close>,
  not a source of any production constant it exports -- moving this content
  out of the dispatcher's own theory keeps a codegen-only build from paying
  for these regression checks (issue #115).
\<close>

subsection \<open>A program that tells the two domains apart\<close>

text \<open>
  \<open>y := 1\<close> then check \<open>0 < y\<close> (should hold), then \<open>y := 0 - 1\<close> and check
  \<open>0 < y\<close> again (should now fail): Interval's numeric bounds settle both
  checks precisely, and so does Sign, at the coarser sign-only granularity
  --- \<open>SPos\<close> proves the first check, \<open>SNeg\<close> refutes the second.
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

lemma dispatch_demo_sign_precise:
  "analyse Sign_Analysis dispatch_demo_prog =
     [(Statement 1, Less (N 0) (V (STR ''y'')), Check_Proved),
      (Statement 3, Less (N 0) (V (STR ''y'')), Check_Refuted)]"
  by eval

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
  "intra (prog_cfg prog_main_name dispatch_demo_prog) =
     {(FunctionEntry (STR ''main''), EA_Nop, Statement 0),
      (Statement 0, EA_Assign (STR ''y'') (N 1), Statement 1),
      (Statement 1, EA_Check (Less (N 0) (V (STR ''y''))), Statement 2),
      (Statement 2, EA_Assign (STR ''y'') (Minus (N 0) (N 1)), Statement 3),
      (Statement 3, EA_Check (Less (N 0) (V (STR ''y''))), Statement 4),
      (Statement 4, EA_Ret None (STR ''main''), FunctionResult (STR ''main''))}"
  unfolding prog_cfg_def by eval

lemma dispatch_demo_exit_eval:
  "cfg_exit (prog_cfg prog_main_name dispatch_demo_prog) = FunctionResult (STR ''main'')"
  unfolding prog_cfg_def by (simp add: cfg_exit_compile_prog prog_main_name_def)

text \<open>Structural reachability of the first check node to the exit --- a fact about the CFG's
  shape, following the same \<open>cfg_reaches_intra\<close>/\<open>cfg_reaches_trans\<close> chaining as
  \<open>checks_ivl_ex_statement2_reaches_exit\<close> (\<open>Example_Interval_Checks_Store_Only\<close>).\<close>

lemma dispatch_demo_statement1_reaches_exit:
  "cfg_reaches (prog_cfg prog_main_name dispatch_demo_prog) (Statement 1)
     (cfg_exit (prog_cfg prog_main_name dispatch_demo_prog))"
proof -
  have r1: "cfg_reaches (prog_cfg prog_main_name dispatch_demo_prog) (Statement 1) (Statement 2)"
    by (rule cfg_reaches_intra) (simp add: dispatch_demo_intra_eval)
  have r2: "cfg_reaches (prog_cfg prog_main_name dispatch_demo_prog) (Statement 2) (Statement 3)"
    by (rule cfg_reaches_intra) (simp add: dispatch_demo_intra_eval)
  have r3: "cfg_reaches (prog_cfg prog_main_name dispatch_demo_prog) (Statement 3) (Statement 4)"
    by (rule cfg_reaches_intra) (simp add: dispatch_demo_intra_eval)
  have r4: "cfg_reaches (prog_cfg prog_main_name dispatch_demo_prog) (Statement 4)
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
  "calls (prog_cfg prog_main_name dispatch_demo_prog) = {}"
  unfolding prog_cfg_def by eval

lemma dispatch_demo_cover_edge_ball:
  "\<forall>(u, a, w) \<in> intra (prog_cfg prog_main_name dispatch_demo_prog).
     (w, ()) \<in> fst (analyse_interval_dg dispatch_demo_prog)"
  by eval

lemma dispatch_demo_cover_edge:
  "\<And>u a w. (u, a, w) \<in> intra (prog_cfg prog_main_name dispatch_demo_prog)
     \<Longrightarrow> (w, ()) \<in> fst (analyse_interval_dg dispatch_demo_prog)"
  using dispatch_demo_cover_edge_ball by auto

theorem dispatch_demo_first_check_certified:
  "\<forall>s \<in> ltr_collect (declared_global dispatch_demo_prog) (prog_cfg prog_main_name dispatch_demo_prog)
           (cinit_stores (declared_global dispatch_demo_prog)) (Statement 1).
     truthy (aval (Less (N 0) (V (STR ''y''))) s)"
proof (rule analyse_interval_proved_sound)
  show "TD_side_warrowing_apinis_Interp_solve_c (analyse_interval_dg_eqs dispatch_demo_prog)
          (cfg_exit (prog_cfg prog_main_name dispatch_demo_prog), ()) \<noteq> None"
    by eval
  show "wf_compile_input (declared_global dispatch_demo_prog) (prog_table dispatch_demo_prog)
          (prog_procs dispatch_demo_prog) prog_main_name (prog_main dispatch_demo_prog)"
    unfolding wf_compile_input_simps dispatch_demo_prog_def
    by (auto simp: source_exp_def proc_decl_of_def ret_var_def reserved_ret_var_def
        prog_main_name_def special_table_def special_pname_nondet_int_def
        special_pname_min_def special_pname_max_def
        split: if_splits)
  show "(cfg_entry (prog_cfg prog_main_name dispatch_demo_prog), ()) \<in> fst (analyse_interval_dg dispatch_demo_prog)"
    by eval
  show "\<And>u a w. (u, a, w) \<in> intra (prog_cfg prog_main_name dispatch_demo_prog)
          \<Longrightarrow> (w, ()) \<in> fst (analyse_interval_dg dispatch_demo_prog)"
    by (rule dispatch_demo_cover_edge)
  show "\<And>c dst fs as q k. (c, CallEdge dst fs as, FunctionEntry q, k) \<in> calls (prog_cfg prog_main_name dispatch_demo_prog)
          \<Longrightarrow> (FunctionEntry q, ()) \<in> fst (analyse_interval_dg dispatch_demo_prog)"
    by (simp add: dispatch_demo_calls_eval)
  show "\<And>c dst fs as q k. (c, CallEdge dst fs as, FunctionEntry q, k) \<in> calls (prog_cfg prog_main_name dispatch_demo_prog)
          \<Longrightarrow> (k, ()) \<in> fst (analyse_interval_dg dispatch_demo_prog)"
    by (simp add: dispatch_demo_calls_eval)
  show "(Statement 1, Less (N 0) (V (STR ''y'')), Check_Proved) \<in> set (analyse Interval_Analysis dispatch_demo_prog)"
    unfolding dispatch_demo_interval_precise by simp
qed

text \<open>
  \<^const>\<open>string_of_exp\<close> (\<^theory>\<open>Voblint_Analysis.Analysis_GraphViz\<close>, already an
  ancestor) renders the \<open>exp\<close> half of a \<open>check_report_entry\<close> as a native
  string, so an external consumer of \<open>analyse\<close>'s report can print a check's
  condition without decoding the \<open>exp\<close> AST itself.
\<close>

lemma dispatch_demo_check_cond_rendered:
  "string_of_exp 0 (Less (N 0) (V (STR ''y''))) = ''0<y''"
  by eval

subsection \<open>Sign: trivial straight-line code is precise\<close>

text \<open>
  \<open>x := 5\<close> is exactly \<open>SPos\<close> at the sign level, and \<open>analyse Sign_Analysis\<close> now settles \<open>0 < x\<close>
  outright from it, on a program with no global at all. The native D/G pipeline's
  \<open>analyse_sign_env_for\<close> routes each name to the one component that owns it
  (\<^const>\<open>combine_env_abs\<close>) instead of unconditionally joining the local answer with the global
  side-effect slot, so an untouched local's precision is no longer destroyed by the global
  slot's unrelated \<^term>\<open>STop\<close> default.
\<close>

lemma sign_straight_line_const_proved:
  "analyse Sign_Analysis (program { void main() { x := 5; __voblint_check(0 < x) } }) =
     [(Statement 1, Less (N 0) (V (STR ''x'')), Check_Proved)]"
  by eval

lemma sign_straight_line_neg_const_refuted:
  "analyse Sign_Analysis (program { void main() { x := 0 - 5; __voblint_check(0 < x) } }) =
     [(Statement 1, Less (N 0) (V (STR ''x'')), Check_Refuted)]"
  by eval

subsection \<open>A program with a global, a procedure, and a call\<close>

text \<open>
  \<open>total\<close> is a declared global; \<open>inc\<close> takes one formal and adds it to
  \<open>total\<close>; \<open>main\<close> calls \<open>inc\<close> twice, then checks the accumulated total ---
  exercising \<open>imp_prog.make\<close>'s procedure list, \<open>proc_decl_of\<close>'s formals, and
  \<open>com.Call\<close> together, not just straight-line assignment/check as
  \<open>dispatch_demo_prog\<close> does above.
\<close>

definition proc_demo_prog :: imp_prog where
  "proc_demo_prog =
     program {
       global total;
       void inc(n) {
         total := total + n
       }
       void main() {
         total := 0;
         inc(3);
         inc(4);
         __voblint_check(0 < total);
         __voblint_check(total < 100)
       }
     }"

text \<open>
  \<^const>\<open>string_of_check_report\<close>/\<^const>\<open>string_of_action\<close>/
  \<^const>\<open>string_of_call_action\<close> (\<^theory>\<open>Voblint_Analysis.Analysis_GraphViz\<close>,
  already an ancestor via \<^theory>\<open>Voblint_Analysis.Sign_Exec_Sound\<close>) already
  print a report/edge/call action; only the two CFG-edge-list joiners are new
  here.
\<close>

definition string_of_intra_list ::
  "(cfg_node \<times> edge_action \<times> cfg_node) list \<Rightarrow> string" where
  "string_of_intra_list es = join_source ''; ''
     (map (\<lambda>(u, a, v). string_of_cfg_node u @ '' --['' @ string_of_action a
             @ '']--> '' @ string_of_cfg_node v) es)"

definition string_of_calls_list ::
  "(cfg_node \<times> call_action \<times> cfg_node \<times> cfg_node) list \<Rightarrow> string" where
  "string_of_calls_list es = join_source ''; ''
     (map (\<lambda>(call, ca, entry, cont). string_of_cfg_node call @ '' --['' @
             string_of_call_action ca @ '']--> '' @ string_of_cfg_node entry
             @ '' ~cont~> '' @ string_of_cfg_node cont) es)"

text \<open>
  Under the Base-style migration, \<open>total\<close>'s value is exact by the second check
  (\<open>0 < total\<close> is now \<open>Check_Proved\<close>, matching the true accumulated \<open>total = 7\<close>):
  the local unknown carries the whole abstract state through both calls,
  flow-sensitively, instead of routing \<open>total\<close> through a flow-insensitive
  solver-global summary. The third check (\<open>total < 100\<close>) stays \<open>Check_Unknown\<close>
  regardless -- Sign has no comparison-against-a-nonzero-constant table at all,
  so it cannot decide a bound like \<open>< 100\<close> even given the exact value.
\<close>

lemma proc_demo_sign_result:
  "analyse Sign_Analysis proc_demo_prog =
     [(Statement 5, Less (N 0) (V (STR ''total'')), Check_Proved),
      (Statement 6, Less (V (STR ''total'')) (N 100), Check_Unknown)]"
  by eval


text \<open>
  \<open>total+n\<close>, not \<open>(total+n)\<close>: \<open>string_of_exp\<close> no longer parenthesizes
  \<open>Plus\<close>/\<open>Minus\<close>/\<open>Times\<close> (see \<open>VIMP_Source_Print.thy\<close> --- VIMP's source
  grammar has no parenthesized \<open>exp\<close> at all, so the old parenthesized
  rendering was never actually valid VIMP source).
\<close>

lemma proc_demo_cfg_intra:
  "string_of_intra_list (cfg_intra_list (prog_cfg prog_main_name proc_demo_prog)) =
     ''pp0 --[total := total+n]--> pp1; pp1 --[return]--> result_inc; ''
     @ ''pp2 --[total := 0]--> pp3; pp5 --[check(0<total)]--> pp6; ''
     @ ''pp6 --[check(total<100)]--> pp7; pp7 --[return]--> result_main; ''
     @ ''entry_inc --[nop]--> pp0; entry_main --[nop]--> pp2''"
  by eval

lemma proc_demo_cfg_calls:
  "string_of_calls_list (cfg_calls_list (prog_cfg prog_main_name proc_demo_prog)) =
     ''pp3 --[call(3)]--> entry_inc ~cont~> pp4; pp4 --[call(4)]--> entry_inc ~cont~> pp5''"
  by eval

text \<open>
  The originally-documented crash case (a global, one procedure, two calls, two checks) through
  the exact runtime API \<open>analyse\<close> exposes: now terminates in a few seconds via the warrowing
  backend \<open>analyse Interval_Analysis\<close> dispatches to. Base-migration acceptance witness: the
  first check (\<open>0 < total\<close>) is now \<open>Check_Proved\<close> --- \<open>total\<close> lives in the reachability-lifted
  local unknown, flow-sensitively through both calls to \<open>inc\<close>, so its exact value (\<open>7\<close>) survives
  to the check, the same fix \<open>Sign_Analysis\<close>'s \<open>proc_demo_sign_result\<close> demonstrates. The second
  check (\<open>total < 100\<close>) stays \<open>Check_Unknown\<close>: \<open>inc\<close>'s entry node is reached by two distinct call
  sites (\<open>inc(3)\<close> then \<open>inc(4)\<close>), so the D/G solver revisits it, and Apinis warrowing widens the
  entered parameter's upper bound to \<open>+inf\<close> on that second visit for termination; the following
  narrowing phase recovers enough to keep \<open>total\<close>'s lower bound exact (proving \<open>0 < total\<close>) but
  not its upper bound (leaving \<open>total < 100\<close> undecided) --- widening's precision cost at a
  repeated call site, not a bug.
\<close>

lemma proc_demo_interval_terminates:
  "analyse Interval_Analysis proc_demo_prog =
     [(Statement 5, Less (N 0) (V (STR ''total'')), Check_Proved),
      (Statement 6, Less (V (STR ''total'')) (N 100), Check_Unknown)]"
  by eval

text \<open>
  \<open>analyse_interval_report proc_demo_prog\<close> (the always-join backend, no longer what
  \<open>analyse Interval_Analysis\<close> dispatches to) does not terminate within several minutes and
  crashes the evaluating process outright --- reproduced independently in a batch build
  (segfault after ~145s), an I/R REPL (crashed the daemon), and an I/Q jEdit session (crashed the
  backend). Confirmed independent of the \<^typ>\<open>String.literal\<close> migration in this branch --- no
  existing example anywhere in this project previously exercised \<^const>\<open>analyse_interval_report\<close>
  end-to-end on a program containing an actual \<^const>\<open>com.Call\<close> edge, so this was a pre-existing
  latent non-termination, newly exposed at the time, not caused by that migration.

  This is \<^emph>\<open>not\<close> fundamentally about calls, though calls were the original reproducer. Isolated
  (task #39, three \<^verbatim>\<open>Timeout.apply\<close>-guarded probes below, all now completing well inside their
  15s budget once routed through the warrowing backend): a call to a procedure that reads/writes
  no global (\<open>no_global_call_prog\<close>) terminates in under 4 seconds; a call to a procedure that
  touches one global (\<open>one_call_prog\<close>) terminates too; and, decisively,
  \<open>no_call_global_self_ref_prog\<close> --- no procedure, no call, just
  \<open>total := 0; total := total + 3\<close> on a declared global --- reproduces the same divergence
  \<^emph>\<open>alone\<close>, under the always-join backend. The call/return summary was never the cause: a single
  self-referential global write reproduces it by itself. Ordinary constant global writes
  (\<open>g := 1\<close>) are unaffected either way --- the problematic class is specifically a global side
  contribution that depends monotonically on the flow-insensitive summary's own current value.

  The actual mechanism: globals are one flow-insensitive summary point (\<open>Inr ()\<close>). Every transfer
  built through \<open>unit_edge_tree_st\<close> reads that summary via \<open>QueryG\<close> and publishes its own
  contribution back to the same summary via \<open>Side\<close>, so an assignment that both reads and grows a
  global becomes a self-referential equation on \<open>Inr ()\<close>: \<open>total := total + 3\<close> together with the
  independent base case \<open>total := 0\<close> solves as \<open>G = [0,0] \<squnion> (G + [3,3])\<close>. Kleene iteration from
  \<open>bot\<close> produces the ascending chain \<open>[0,0]\<close>, \<open>[0,3]\<close>, \<open>[0,6]\<close>, \<open>[0,9]\<close>, \<open>\<dots>\<close> --- the true least
  fixpoint is \<open>[0,+\<infinity>]\<close>, and plain join (\<^const>\<open>TD_side_always_join_Interp_solve\<close>'s global update
  is \<open>sup\<close>) never reaches an infinite bound in finitely many steps. This was not an arithmetic
  bug: it was exactly the flow-insensitive least fixpoint that solve path computes, on a domain
  whose global-summary update has no widening. Sign and Parity never hit this because their
  lattices are finite-height, so every join-only fixpoint on them is finite regardless.

  \<^const>\<open>analyse_interval_td_report\<close> (the warrowing, native-D/G variant, now what
  \<open>analyse Interval_Analysis\<close> dispatches to) has both the widening and a soundness theorem
  (\<open>analyse_interval_td_report_sound_proved\<close>/\<open>_refuted\<close>,
  \<^theory>\<open>Voblint_CLI.Interval_Codegen\<close>) --- and empirically terminates on every
  case above, including \<open>proc_demo_prog\<close> itself (\<open>proc_demo_interval_terminates\<close> below). Since
  the Base-style migration, globals also live in the same reachability-lifted local unknown as
  locals, so termination no longer costs the always-join backend's precision on the cases below
  that never touched a repeated call site (\<open>one_call_prog\<close>, \<open>harmless_global_prog\<close>,
  \<open>no_call_global_self_ref_prog\<close>): each is now precise, not merely terminating.
\<close>

text \<open>
  Acceptance regression B (interprocedural global self-feedback): a single call to a
  procedure that reads and grows the same global \<open>total\<close> reads back through the same
  flow-insensitive \<open>Inr ()\<close> summary as the zero-call case below --- so this checks the fix
  also survives \<open>dgs_enter\<close>/\<open>dgs_combine\<close> (entry/return) handling, not just a straight-line
  global write.
\<close>

definition one_call_prog :: imp_prog where
  "one_call_prog =
     program {
       global total;
       void inc(n) {
         total := total + n
       }
       void main() {
         total := 0;
         inc(3);
         __voblint_check(0 < total)
       }
     }"

text \<open>
  Base-migration acceptance witness: \<open>total\<close> is now \<open>Check_Proved\<close>, not merely a terminating
  \<open>Check_Unknown\<close> --- \<open>inc\<close>'s single call site reaches its entry node once, so no repeated-visit
  widening applies, and \<open>total\<close>'s exact value (\<open>3\<close>) survives the call/return combine step.
\<close>

lemma one_call_interval_terminates:
  "analyse Interval_Analysis one_call_prog =
     [(Statement 4, Less (N 0) (V (STR ''total'')), Check_Proved)]"
  by eval

text \<open>
  A call that touches no global at all: contrasts with \<open>one_call_prog\<close> to show the call/return
  machinery itself is not the hazard --- only a global read-and-grow is.
\<close>

definition no_global_call_prog :: imp_prog where
  "no_global_call_prog =
     program {
       void noop(n) {
         skip
       }
       void main() {
         x := 0;
         noop(3);
         __voblint_check(0 < x + 1)
       }
     }"

lemma no_global_call_interval_proved:
  "analyse Interval_Analysis no_global_call_prog =
     [(Statement 4, Less (N 0) (Plus (V (STR ''x'')) (N 1)), Check_Proved)]"
  by eval

text \<open>
  A harmless global write --- a plain constant assignment, no self-reference through a
  summary --- always terminated, under \<^emph>\<open>either\<close> backend: distinguishes "a program has a
  global" from "a program has a self-dependent global side contribution" (the actual hazard
  class, isolated below). Base-migration acceptance witness: the result is now \<open>Check_Proved\<close>,
  not \<open>Check_Unknown\<close> --- with no separate flow-insensitive global summary to route \<open>g\<close> through
  at all, the exact value \<open>g := 1\<close> writes reaches the check directly.
\<close>

definition harmless_global_prog :: imp_prog where
  "harmless_global_prog =
     program {
       global g;
       void main() {
         g := 1;
         __voblint_check(0 < g)
       }
     }"

lemma harmless_global_interval_terminates:
  "analyse Interval_Analysis harmless_global_prog =
     [(Statement 1, Less (N 0) (V (STR ''g'')), Check_Proved)]"
  by eval

text \<open>
  Acceptance regression A (no-call global self-feedback, task #39): no procedure, no call,
  just one global write that reads its own prior value, plus one independent base-case write.
  Isolates global-summary widening on its own, without any interprocedural
  (\<open>dgs_enter\<close>/\<open>dgs_combine\<close>) machinery in play at all --- this is the minimal case that first
  proved the call/return summary was never the actual hazard. Base-migration acceptance witness:
  under the Base-style pipeline there is no separate flow-insensitive global summary for
  \<open>total := total + 3\<close> to read back through in the first place, so the result is now
  \<open>Check_Proved\<close>, not merely a terminating \<open>Check_Unknown\<close> --- termination and precision
  coincide once the mechanism that caused both problems (a flow-insensitive global summary) is
  gone.
\<close>

definition no_call_global_self_ref_prog :: imp_prog where
  "no_call_global_self_ref_prog =
     program {
       global total;
       void main() {
         total := 0;
         total := total + 3;
         __voblint_check(0 < total)
       }
     }"

lemma no_call_global_self_ref_interval_terminates:
  "analyse Interval_Analysis no_call_global_self_ref_prog =
     [(Statement 2, Less (N 0) (V (STR ''total'')), Check_Proved)]"
  by eval

text \<open>
  Wiring regression for \<open>analyse_with_state\<close>: a single exact assignment, no
  widening or narrowing in play, so the reported state at the check is
  independently known. This exercises the node environment, the
  global/local merge, and the domain constructor \<open>analyse_with_state\<close>
  wraps its result in --- not merely that the function type-checks.
\<close>

definition state_wiring_ex_prog :: imp_prog where
  "state_wiring_ex_prog =
     program {
       void main() {
         x := 5;
         __voblint_check(0 < x)
       }
     }"

text \<open>
  \<open>x\<close> is local (no \<open>global\<close> declaration). Under the Base-style native D/G pipeline,
  \<open>analyse_sign_report_for_with_state_code\<close>'s per-point environment reads the whole
  abstract state straight off the reachability-lifted local unknown (\<open>map_lift
  (fun_of_exec_dg_st_for gs) (locals (sol (Inl (v, ()))))\<close>, unwrapped through
  \<open>Lifted\<close>/\<open>Bot\<close>) --- there is no separate global/side unknown to route a name to,
  so \<open>x\<close> reads its own precise \<open>SPos\<close> directly regardless of whether it happens to
  be local or global.
\<close>

lemma state_wiring_ex_sign_at_check:
  "(let (_, _, _, unreachable, f) = hd (filter (\<lambda>(u, _, _, _, _). u = Statement 1)
                             (analyse_with_state Sign_Analysis state_wiring_ex_prog))
    in (unreachable, f (STR ''x''))) = (False, SignValue SPos)"
  by eval

lemma state_wiring_ex_interval_at_check:
  "(let (_, _, _, unreachable, f) = hd (filter (\<lambda>(u, _, _, _, _). u = Statement 1)
                             (analyse_with_state Interval_Analysis state_wiring_ex_prog))
    in (unreachable, f (STR ''x''))) = (False, IntervalValue (Ivl (Fin 5) (Fin 5)))"
  by eval

definition state_wiring_ex_dead_prog :: imp_prog where
  "state_wiring_ex_dead_prog =
     program {
       void main() {
         x := 1;
         if (x < 0) {
           __voblint_check(0 < x)
         } else {
           skip
         }
       }
     }"

text \<open>
  \<open>x < 0\<close> is infeasible under \<open>SPos\<close>, so the check inside the \<open>then\<close>
  branch is unreachable dead code -- exactly the case the exported
  \<open>unreachable\<close> flag exists to report, rather than the CLI reconstructing
  it from a probed variable list. \<open>sign_classify_check\<close> still reports a
  vacuous \<open>Check_Proved\<close> here (the whole point's state is witness-bottom,
  so both \<open>check_true\<close>/\<open>check_false\<close> hold vacuously): the \<open>unreachable\<close>
  flag is what lets a caller distinguish this from a genuinely live proof,
  matching Goblint's \<open>__voblint_check(0); // NOWARN (unreachable)\<close>
  convention.
\<close>

lemma state_wiring_ex_dead_at_check:
  "(let (_, _, r, unreachable, _) = hd (filter (\<lambda>(u, _, _, _, _). u = Statement 2)
                             (analyse_with_state Sign_Analysis state_wiring_ex_dead_prog))
    in (unreachable, r)) = (True, Check_Proved)"
  by eval

text \<open>
  Root-cause fix witness for the Sign native D/G pipeline, pinned at its
  actual source rather than at the final report. \<open>unit_step_st\<close>
  (\<^theory>\<open>Voblint_Analysis.Exec_DG_Bridge\<close>), which \<open>unit_dg_spec_st_for\<close>
  uses for every ordinary transfer step (nop, assign, random, assume,
  enter), computes \<open>f (combine_resolved_st_q d g)\<close> before splitting the
  result back into local/global halves: each name is routed to the exec
  state that owns it, never joined against the other's unrelated default.
  \<open>y := 1\<close> here never reads or writes \<open>x\<close>, and there is no call, no global,
  and no widening --- \<open>x\<close> now stays exactly \<open>SPos\<close> by the check, confirming
  the fix reaches the transfer/combine layer itself, not merely
  \<open>analyse_sign_report_for_code\<close>'s readback.
\<close>

definition no_call_two_step_prog :: imp_prog where
  "no_call_two_step_prog =
     program {
       void main() {
         x := 5;
         y := 1;
         __voblint_check(0 < x)
       }
     }"

lemma no_call_two_step_prog_proved:
  "analyse Sign_Analysis no_call_two_step_prog =
     [(Statement 2, Less (N 0) (V (STR ''x'')), Check_Proved)]"
  by eval

lemma no_call_two_step_prog_locals_precise:
  "(case map_lift (fun_of_exec_dg_st_for (declared_global no_call_two_step_prog))
          (locals (snd (analyse_sign no_call_two_step_prog) (Inl (Statement 2, ()))))
    of Lifted s \<Rightarrow> Some (s (STR ''x'')) | Bot \<Rightarrow> None) = Some SPos"
  by eval

text \<open>
  The same fix carries across an actual call boundary: \<open>foo\<close> neither reads
  nor writes the caller-local \<open>x\<close>, and \<open>x\<close> stays precise at the check
  after the call, for the same reason (the call's own combine step,
  \<^const>\<open>base_dg_spec_st_for_lifted\<close>'s \<open>dgs_combine_assign\<close>, restores the
  caller's own local unknown at the return, joining in only the callee's
  declared return value). \<open>g\<close> is now proved too, not merely \<open>x\<close>/\<open>y\<close>: \<open>g\<close>
  lives in the same lifted local unknown as everything else, so the call's
  write reaches the check exactly, with no separate global summary to lose
  precision in. Kept as a second, more realistic witness alongside
  \<open>no_call_two_step_prog_locals_precise\<close>, which isolates the same mechanism
  without any interprocedural machinery at all.
\<close>

definition dg_probe_prog :: imp_prog where
  "dg_probe_prog =
     program {
       global g;
       void foo() {
         g := 5;
         return 2
       }
       void main() {
         x := 1;
         y := foo();
         __voblint_check(0 < x);
         __voblint_check(0 < g);
         __voblint_check(0 < y)
       }
     }"

lemma dg_probe_prog_all_proved:
  "analyse Sign_Analysis dg_probe_prog =
     [(Statement 5, Less (N 0) (V (STR ''x'')), Check_Proved),
      (Statement 6, Less (N 0) (V (STR ''g'')), Check_Proved),
      (Statement 7, Less (N 0) (V (STR ''y'')), Check_Proved)]"
  by eval

text \<open>
  Base-migration acceptance witness: before the migration, \<open>g\<close>'s check above was
  \<open>Check_Unknown\<close>, not because any per-edge routing lost precision, but because
  \<^const>\<open>cinit_sign_st\<close> seeds every declared global at \<open>SZero\<close>, and the old
  flow-\<^emph>\<open>in\<close>sensitive global summary (routed through a separate solver-global
  unknown, joined via \<^const>\<open>TD_side_always_join_Interp_solve\<close>) folded that seed
  in as a real contribution alongside every write, unable to distinguish "before
  this write" from "after": \<open>join_sign SZero SPos = SNonNeg\<close>, and \<open>0 < g\<close> was
  genuinely undecided at \<open>SNonNeg\<close>. With the whole abstract state lifted into the
  local unknown (\<open>D\<close>, no separate global-summary routing at all), \<open>g\<close>'s value
  after \<open>g := 5\<close> is exactly \<open>SPos\<close> by construction, with no entry seed to join
  against -- the seed only ever contributes at the CFG entry, not at every write.
\<close>

definition global_initial_value_remains_in_summary_prog :: imp_prog where
  "global_initial_value_remains_in_summary_prog =
     program {
       global g;
       void main() {
         g := 5;
         __voblint_check(0 < g)
       }
     }"

lemma global_initial_value_remains_in_summary_prog_check_proved:
  "analyse Sign_Analysis global_initial_value_remains_in_summary_prog =
     [(Statement 1, Less (N 0) (V (STR ''g'')), Check_Proved)]"
  by eval

end
