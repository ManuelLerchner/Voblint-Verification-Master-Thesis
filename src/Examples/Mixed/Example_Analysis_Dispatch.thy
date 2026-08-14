theory Example_Analysis_Dispatch
  imports
    Example_Sign_Codegen
    Voblint_Analysis.Interval_Checks
    Voblint_Formalization.Interval_Exec_Ctx_Sound
    "HOL-Library.Code_Target_Numeral"
    "HOL-Library.Code_Abstract_Char"
begin

hide_const phase.N

section \<open>A unified, verified check-report API across domains\<close>

text \<open>
  \<open>analyse_sign_report\<close> (\<^theory>\<open>Voblint_Examples.Example_Sign_Codegen\<close>) and
  \<open>interval_td_check_report\<close>/\<open>analyse_interval_td_report\<close>
  (\<^theory>\<open>Voblint_Analysis.Interval_Checks\<close>) already share one observable
  result type, \<open>check_report_entry list\<close>
  (\<^theory>\<open>Voblint_Core.Abstract_Checks\<close>), even though the two domains'
  internal abstract states (\<open>sign abs_state\<close> vs \<open>ivl abs_state\<close>) genuinely
  differ. \<open>analyse\<close> below is therefore a thin dispatcher, not a new proof:
  each branch reuses the domain's own already-generic, already-sound report
  function unchanged.

  The \<open>Interval_Analysis\<close> branch dispatches to \<open>analyse_interval_td_report\<close>, the
  widening/warrowing-backed report, not the always-join \<open>analyse_interval_report\<close>: the
  always-join backend's flow-insensitive global-summary update has no widening, so it can fail
  to terminate on a finite program whose global-writing transfer depends on the summary's own
  current value (\<open>total := total + n\<close> is the minimal reproducer, isolated below to \<^emph>\<open>not\<close>
  require a call). \<open>analyse_interval_td_report\<close> now carries its own soundness theorems
  (\<^theory>\<open>Voblint_Analysis.Interval_Checks\<close>'s \<open>analyse_interval_td_report_sound_proved\<close>/
  \<open>_refuted\<close>, built on \<open>Voblint_Core.Solver_Side_RG\<close>'s generic
  \<open>TD_side_warrowing_apinis_solve_Inr_rg\<close>), so this is a like-for-like swap, not a precision or
  soundness downgrade.
\<close>

datatype analysis_kind = Sign_Analysis | Interval_Analysis

fun analyse :: "analysis_kind \<Rightarrow> imp_prog \<Rightarrow> check_report_entry list" where
  "analyse Sign_Analysis p = analyse_sign_report p"
| "analyse Interval_Analysis p = analyse_interval_td_report p"

subsection \<open>Context-sensitivity dimension\<close>

text \<open>
  \<open>Ctx_None\<close> is today's flow-insensitive, call-site-insensitive behaviour;
  \<open>Ctx_EntryState\<close> selects the value-derived entry-state context analysis
  (\<^theory>\<open>Voblint_Formalization.Interval_Exec_Ctx_Sound\<close>, #108). Deliberately not
  a wider \<open>analyse\<close>: \<open>analyse\<close>/\<open>analyse_with_state\<close> stay untouched (the CLI's
  no-\<open>--context\<close> path, the GraphViz report, and every existing
  \<open>codegen/regression\<close> consumer already pin their exact two-argument shape as a
  trust boundary), and Sign has no context-sensitive branch to route to yet, so
  widening \<open>analyse\<close> itself would force a fabricated Sign case. \<open>analyse_ctx\<close>
  is the additional export for this one new dimension, reusing \<open>analyse\<close>'s own
  branches unchanged at \<open>Ctx_None\<close> rather than duplicating their logic.
  \<open>None\<close> is a real, checkable unsupported-combination result -- todays's only
  unsupported pairing is \<open>Sign_Analysis\<close>/\<open>Ctx_EntryState\<close> -- not a silent
  fallback to context-insensitive behaviour.
\<close>

datatype context_mode = Ctx_None | Ctx_EntryState

fun analyse_ctx :: "analysis_kind \<Rightarrow> context_mode \<Rightarrow> imp_prog \<Rightarrow> check_report_entry list option" where
  "analyse_ctx Sign_Analysis Ctx_None p = Some (analyse_sign_report p)"
| "analyse_ctx Interval_Analysis Ctx_None p = Some (analyse_interval_td_report p)"
| "analyse_ctx Interval_Analysis Ctx_EntryState p = Some (analyse_interval_entry_state p)"
| "analyse_ctx Sign_Analysis Ctx_EntryState p = None"

text \<open>\<open>Ctx_None\<close> is exactly \<open>analyse\<close>, for both domains: the new dispatcher
  cannot silently drift from the one CLI/regression already exercises.\<close>

lemma analyse_ctx_none_eq_analyse: "analyse_ctx k Ctx_None p = Some (analyse k p)"
  by (cases k) simp_all

subsection \<open>Domain-neutral state-carrying report\<close>

text \<open>
  \<open>abstract_value\<close> wraps each domain's own abstract state type once, so
  \<open>analyse_with_state\<close> can share one report type across branches the same
  way \<open>analyse\<close> already shares \<open>check_result\<close>. \<open>analyse\<close> itself stays
  untouched: external callers (the CLI design, this theory's own
  \<open>codegen/regression\<close> drivers) already pin its \<open>check_report_entry
  list\<close> shape as a trust boundary, so this is an additional export, not a
  replacement. Each branch reuses \<open>analyse_sign_report_with_state\<close>/
  \<open>analyse_interval_td_report_with_state\<close> (\<^theory>\<open>Voblint_Analysis.Sign_Checks\<close>,
  \<^theory>\<open>Voblint_Analysis.Interval_Checks\<close>) unchanged, just as \<open>analyse\<close> reuses
  their state-free counterparts.
\<close>

datatype abstract_value = SignValue sign | IntervalValue ivl

fun analyse_with_state ::
    "analysis_kind \<Rightarrow> imp_prog \<Rightarrow> (pp \<times> bexp \<times> check_result \<times> abstract_value abs_state) list" where
  "analyse_with_state Sign_Analysis p =
     map (\<lambda>(u, c, r, s). (u, c, r, SignValue \<circ> s)) (analyse_sign_report_with_state p)"
| "analyse_with_state Interval_Analysis p =
     map (\<lambda>(u, c, r, s). (u, c, r, IntervalValue \<circ> s)) (analyse_interval_td_report_with_state p)"

subsection \<open>Public API: soundness corollaries stated over the runtime dispatcher\<close>

text \<open>
  \<open>analyse_interval_td_report_sound_proved\<close>/\<open>_refuted\<close>
  (\<^theory>\<open>Voblint_Analysis.Interval_Checks\<close>) and \<open>analyse_sign_report_sound_proved\<close>/\<open>_refuted\<close>
  (\<^theory>\<open>Voblint_Examples.Example_Sign_Codegen\<close>) are proved about \<open>analyse_interval_td_report\<close> and
  \<open>analyse_sign_report\<close> --- the exact constants \<open>analyse\<close> pattern-matches to, one \<open>analyse.simps\<close>
  equation away. The four corollaries below restate them directly over \<open>analyse\<close>, the constant
  \<open>export_code\<close> exports, so connecting a runtime verdict to its soundness theorem never requires
  unfolding the dispatcher by hand.

  \<open>finite (intra (prog_cfg prog_main_name p))\<close> is dropped from the hypothesis lists below: since
  \<^const>\<open>prog_cfg\<close> is \<^const>\<open>compile_prog\<close> under the hood, it always holds, for every \<open>p\<close>, by
  \<open>compile_prog_finite\<close> --- not a per-program obligation.

  The remaining hypotheses stay real per-program obligations, not free: solver termination
  (\<open>analyse_interval_td_terminates\<close> for Interval; \<open>solve \<noteq> None\<close> plus the four \<open>cover_*\<close>
  solver-exploration facts for Sign) and, for both domains, the checked node's reachability to
  \<open>cfg_exit\<close>. Nothing in this formalization proves that either solver terminates on every input
  program, so termination stays a genuine premise --- typically discharged \<open>by eval\<close> on a concrete
  program via \<open>analyse_interval_td_terminates_via_solve_c\<close> / \<open>TD_side_always_join_Interp_solve_c\<close>
  reflection, as \<open>dispatch_demo_first_check_certified\<close> below does for one concrete instance.
  Consequently, a bare \<open>Check_Proved\<close>/\<open>Check_Refuted\<close> value \<open>analyse\<close> returns at runtime is not
  itself a discharged certificate: turning it into one requires supplying these two facts for the
  specific program and node.
\<close>

corollary analyse_interval_proved_sound:
  fixes p :: imp_prog and v :: pp and c :: bexp
  assumes terminates: "analyse_interval_td_terminates
                          (resolved_st_q_is_bot_for (declared_global_vars p))
                          (declared_global p) (prog_table p) (prog_procs p) prog_main_name (prog_main p)"
      and reach_exit: "cfg_reaches (prog_cfg prog_main_name p) v (cfg_exit (prog_cfg prog_main_name p))"
      and mem: "(v, c, Check_Proved) \<in> set (analyse Interval_Analysis p)"
  shows "\<forall>s \<in> ltr_collect (declared_global p) (prog_cfg prog_main_name p) (cinit_stores (declared_global p)) v.
           bval c s"
proof -
  have fin: "finite (intra (prog_cfg prog_main_name p))"
    unfolding prog_cfg_def using compile_prog_finite by simp
  show ?thesis
    by (rule analyse_interval_td_report_sound_proved
          [OF fin terminates reach_exit mem[unfolded analyse.simps]])
qed

corollary analyse_interval_refuted_sound:
  fixes p :: imp_prog and v :: pp and c :: bexp
  assumes terminates: "analyse_interval_td_terminates
                          (resolved_st_q_is_bot_for (declared_global_vars p))
                          (declared_global p) (prog_table p) (prog_procs p) prog_main_name (prog_main p)"
      and reach_exit: "cfg_reaches (prog_cfg prog_main_name p) v (cfg_exit (prog_cfg prog_main_name p))"
      and mem: "(v, c, Check_Refuted) \<in> set (analyse Interval_Analysis p)"
  shows "\<forall>s \<in> ltr_collect (declared_global p) (prog_cfg prog_main_name p) (cinit_stores (declared_global p)) v.
           \<not> bval c s"
proof -
  have fin: "finite (intra (prog_cfg prog_main_name p))"
    unfolding prog_cfg_def using compile_prog_finite by simp
  show ?thesis
    by (rule analyse_interval_td_report_sound_refuted
          [OF fin terminates reach_exit mem[unfolded analyse.simps]])
qed

corollary analyse_sign_proved_sound:
  fixes p :: imp_prog and v :: pp and c :: bexp
  assumes solve: "TD_side_always_join_Interp_solve_c (analyse_sign_eqs p) (cfg_exit (prog_cfg prog_main_name p), ()) \<noteq> None"
      and wf: "wf_compile_input (declared_global p) (prog_table p) (prog_procs p) prog_main_name (prog_main p)"
      and cover_entry: "(cfg_entry (prog_cfg prog_main_name p), ()) \<in> fst (analyse_sign p)"
      and cover_edge:
        "\<And>u a w. (u, a, w) \<in> intra (prog_cfg prog_main_name p) \<Longrightarrow> (w, ()) \<in> fst (analyse_sign p)"
      and cover_enter:
        "\<And>c dst fs as q k. (c, CallEdge dst fs as, FunctionEntry q, k) \<in> calls (prog_cfg prog_main_name p)
           \<Longrightarrow> (FunctionEntry q, ()) \<in> fst (analyse_sign p)"
      and cover_combine:
        "\<And>c dst fs as q k. (c, CallEdge dst fs as, FunctionEntry q, k) \<in> calls (prog_cfg prog_main_name p)
           \<Longrightarrow> (k, ()) \<in> fst (analyse_sign p)"
      and mem: "(v, c, Check_Proved) \<in> set (analyse Sign_Analysis p)"
  shows "\<forall>s \<in> ltr_collect (declared_global p) (prog_cfg prog_main_name p) (cinit_stores (declared_global p)) v. bval c s"
proof -
  have finI: "finite (intra (prog_cfg prog_main_name p))"
    unfolding prog_cfg_def using compile_prog_finite by simp
  have finC: "finite (calls (prog_cfg prog_main_name p))"
    unfolding prog_cfg_def using compile_prog_finite by simp
  show ?thesis
    by (rule analyse_sign_report_sound_proved
          [OF solve wf cover_entry cover_edge cover_enter cover_combine finI finC
              mem[unfolded analyse.simps]])
qed

corollary analyse_sign_refuted_sound:
  fixes p :: imp_prog and v :: pp and c :: bexp
  assumes solve: "TD_side_always_join_Interp_solve_c (analyse_sign_eqs p) (cfg_exit (prog_cfg prog_main_name p), ()) \<noteq> None"
      and wf: "wf_compile_input (declared_global p) (prog_table p) (prog_procs p) prog_main_name (prog_main p)"
      and cover_entry: "(cfg_entry (prog_cfg prog_main_name p), ()) \<in> fst (analyse_sign p)"
      and cover_edge:
        "\<And>u a w. (u, a, w) \<in> intra (prog_cfg prog_main_name p) \<Longrightarrow> (w, ()) \<in> fst (analyse_sign p)"
      and cover_enter:
        "\<And>c dst fs as q k. (c, CallEdge dst fs as, FunctionEntry q, k) \<in> calls (prog_cfg prog_main_name p)
           \<Longrightarrow> (FunctionEntry q, ()) \<in> fst (analyse_sign p)"
      and cover_combine:
        "\<And>c dst fs as q k. (c, CallEdge dst fs as, FunctionEntry q, k) \<in> calls (prog_cfg prog_main_name p)
           \<Longrightarrow> (k, ()) \<in> fst (analyse_sign p)"
      and mem: "(v, c, Check_Refuted) \<in> set (analyse Sign_Analysis p)"
  shows "\<forall>s \<in> ltr_collect (declared_global p) (prog_cfg prog_main_name p) (cinit_stores (declared_global p)) v. \<not> bval c s"
proof -
  have finI: "finite (intra (prog_cfg prog_main_name p))"
    unfolding prog_cfg_def using compile_prog_finite by simp
  have finC: "finite (calls (prog_cfg prog_main_name p))"
    unfolding prog_cfg_def using compile_prog_finite by simp
  show ?thesis
    by (rule analyse_sign_report_sound_refuted
          [OF solve wf cover_entry cover_edge cover_enter cover_combine finI finC
              mem[unfolded analyse.simps]])
qed

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

theorem dispatch_demo_first_check_certified:
  "\<forall>s \<in> ltr_collect (declared_global dispatch_demo_prog) (prog_cfg prog_main_name dispatch_demo_prog)
           (cinit_stores (declared_global dispatch_demo_prog)) (Statement 1).
     bval (Less (N 0) (V (STR ''y''))) s"
proof (rule analyse_interval_proved_sound)
  show "analyse_interval_td_terminates
          (resolved_st_q_is_bot_for (declared_global_vars dispatch_demo_prog))
          (declared_global dispatch_demo_prog) (prog_table dispatch_demo_prog)
          (prog_procs dispatch_demo_prog) prog_main_name (prog_main dispatch_demo_prog)"
    by (rule analyse_interval_td_terminates_via_solve_c) eval
  show "cfg_reaches (prog_cfg prog_main_name dispatch_demo_prog) (Statement 1)
          (cfg_exit (prog_cfg prog_main_name dispatch_demo_prog))"
    by (rule dispatch_demo_statement1_reaches_exit)
  show "(Statement 1, Less (N 0) (V (STR ''y'')), Check_Proved) \<in> set (analyse Interval_Analysis dispatch_demo_prog)"
    unfolding dispatch_demo_interval_precise by simp
qed

text \<open>
  \<^const>\<open>string_of_bexp\<close> (\<^theory>\<open>Voblint_Analysis.Analysis_GraphViz\<close>, already an
  ancestor) renders the \<open>bexp\<close> half of a \<open>check_report_entry\<close> as a native
  string, so an external consumer of \<open>analyse\<close>'s report can print a check's
  condition without decoding the \<open>bexp\<close> AST itself.
\<close>

lemma dispatch_demo_check_cond_rendered:
  "string_of_bexp (Less (N 0) (V (STR ''y''))) = ''0<y''"
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

lemma proc_demo_sign_unknown:
  "analyse Sign_Analysis proc_demo_prog =
     [(Statement 5, Less (N 0) (V (STR ''total'')), Check_Unknown),
      (Statement 6, Less (V (STR ''total'')) (N 100), Check_Unknown)]"
  by eval

text \<open>
  \<open>total+n\<close>, not \<open>(total+n)\<close>: \<open>string_of_aexp\<close> no longer parenthesizes
  \<open>Plus\<close>/\<open>Minus\<close>/\<open>Times\<close> (see \<open>VIMP_Source_Print.thy\<close> --- VIMP's source
  grammar has no parenthesized \<open>aexp\<close> at all, so the old parenthesized
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
  backend \<open>analyse Interval_Analysis\<close> dispatches to, at \<open>Check_Unknown\<close> precision (widening's
  cost, not a bug) rather than crashing.
\<close>

lemma proc_demo_interval_terminates:
  "analyse Interval_Analysis proc_demo_prog =
     [(Statement 5, Less (N 0) (V (STR ''total'')), Check_Unknown),
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

  \<^const>\<open>analyse_interval_td_report\<close> (the warrowing variant, now what \<open>analyse Interval_Analysis\<close>
  dispatches to) has both the widening and a soundness theorem
  (\<open>analyse_interval_td_report_sound_proved\<close>/\<open>_refuted\<close>, \<^theory>\<open>Voblint_Analysis.Interval_Checks\<close>)
  --- and empirically terminates on every case above, including \<open>proc_demo_prog\<close> itself
  (\<open>proc_demo_interval_terminates\<close> below), at the cost of the precision the always-join backend
  would have given on programs it could actually finish.
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

lemma one_call_interval_terminates:
  "analyse Interval_Analysis one_call_prog =
     [(Statement 4, Less (N 0) (V (STR ''total'')), Check_Unknown)]"
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
  A harmless global write --- a plain constant assignment, no self-reference through the
  summary --- always terminated, under \<^emph>\<open>either\<close> backend: distinguishes "a program has a
  global" from "a program has a self-dependent global side contribution" (the actual hazard
  class, isolated below). The result is \<open>Check_Unknown\<close> here (this older \<open>side_cfg_T_eff_st\<close>
  pipeline's local/global environment read loses precision on a global read back right after its
  own write, independent of solver choice), not \<open>Check_Proved\<close> --- termination, not precision,
  is the property this case demonstrates.
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
     [(Statement 1, Less (N 0) (V (STR ''g'')), Check_Unknown)]"
  by eval

subsection \<open>Executable code generation\<close>

text \<open>
  \<open>analyse\<close> genuinely takes the domain choice and the program as runtime
  arguments, not constants baked in at export time. The raw AST constructors,
  \<open>imp_prog.make\<close>, and \<open>proc_decl_of\<close> are exported alongside it so external
  OCaml code can build a fresh \<open>imp_prog\<close> and hand it to \<open>analyse\<close>.

  \<^typ>\<open>vname\<close>/\<^typ>\<open>pname\<close> are \<^typ>\<open>String.literal\<close>
  (\<^theory>\<open>Voblint_VIMP.VIMP_Syntax\<close>/\<^theory>\<open>Voblint_VIMP.VIMP_Globals\<close>), already
  the target language's native string (\<^verbatim>\<open>string\<close> in OCaml
  --- \<^theory>\<open>HOL.String\<close> ships that mapping
  unconditionally), so \<open>V\<close>/\<open>Assign\<close>/\<open>Random\<close>/\<open>com.Call\<close>/\<open>FunctionEntry\<close>/
  \<open>FunctionResult\<close>/\<open>proc_decl_of\<close>/\<open>imp_prog.make\<close> below already take and
  return native strings directly --- no separate construction facade needed.

  \<^theory>\<open>HOL-Library.Code_Target_Numeral\<close> makes \<open>int\<close>/\<open>nat\<close> abstract types
  backed by the target language's native arbitrary-precision integer
  (OCaml's target-numeral representation) instead of
  Isabelle's own binary-numeral/Peano-successor encodings, so arithmetic and
  comparisons inside the exported analyser run on native integers rather
  than walking a \<open>Num\<close>/\<open>Nat\<close> term. \<open>int_of_integer\<close>/\<open>nat_of_integer\<close> and
  their inverses \<open>integer_of_int\<close>/\<open>integer_of_nat\<close> are the resulting
  bridge --- the only way external code can build or inspect an \<open>int\<close>/\<open>nat\<close>
  once the representation is opaque.

  \<^theory>\<open>HOL-Library.Code_Abstract_Char\<close> does the same for \<open>char\<close>, relevant
  wherever a \<open>char\<close> is inspected directly (e.g. \<^const>\<open>String.explode\<close>'s
  result) rather than through the opaque \<open>String.literal\<close> above.
  \<open>char_of_integer\<close>/\<open>integer_of_char\<close> are that bridge.

  \<open>string_of_bexp\<close> is exported alongside the structured \<open>bexp\<close> already in
  every \<open>check_report_entry\<close>: a consumer can pattern-match the AST directly,
  or call \<open>string_of_bexp\<close> to render a check's condition as a native string
  without decoding it --- both stay available, not a replacement report type.
\<close>

text \<open>
  Without a \<open>module_name\<close>, \<open>export_code\<close> distributes generated code over one
  module per contributing Isabelle theory --- around sixty of them here, most
  named after internal proof-repo theories (\<open>TD_side\<close>, \<open>Interval_Warrowing\<close>,
  \<open>DG_Framework\<close>, ...) meaningless to an external reader and irrelevant to
  \<open>analyse\<close>'s public surface. \<open>code_identifier\<close> remaps every contributing
  theory onto two named OCaml modules instead, so an external reader is not
  left staring at either one undifferentiated file or dozens of
  internal-theory names.

  OCaml's serializer emits one file per \<open>export_code\<close> call regardless of
  \<open>module_name\<close>/\<open>code_identifier\<close>, so the remapping instead organizes that
  one file into nested \<open>module ... = struct ... end\<close> blocks: \<open>Analyse\<close> for
  this theory's public facade (\<open>analysis_kind\<close>, \<open>analyse\<close> itself), and
  \<open>Core\<close> for everything it is built from --- VIMP source AST and printing,
  CFG representation and compiler, the executable state substrate
  (\<open>Exec_St\<close>/\<open>Exec_Bridge\<close>, the generic domain interface), the generic
  D/G/effectful analysis plumbing (equation systems, the D/G spec framework,
  generic check classification), the vendored TD/TD_side solver, both
  domains' lattices, transfer functions, and check classification
  (\<open>Sign\<close>, \<open>Interval\<close>), and the underlying HOL-library data structures
  (finite maps and sets, orderings, sum types, target numerals/strings).

  \<open>Core\<close> cannot be split further: \<open>Exec_St\<close>'s executable state is
  generically instantiated at the solver's own \<open>widening\<close>/\<open>narrowing\<close> type
  classes, and the CFG-specific solver instantiation needs \<open>cfg_node\<close> back
  --- real, mutual code-level dependencies, confirmed by a \<^verbatim>\<open>module dependency cycle\<close>
  error from the OCaml serializer when these stayed split, not an arbitrary
  grouping choice. Splitting \<open>Sign\<close>/\<open>Interval\<close> out from \<open>Core\<close> instead
  compiles \<^emph>\<open>and\<close> passes Isabelle's own \<open>export_code\<close> checks, but
  \<^verbatim>\<open>ocamlfind ocamlopt\<close> then rejects the result with an unbound
  type-class dictionary record field (\<open>Core.ord_preorder\<close>) --- Isabelle's
  OCaml module-signature inference does not expose every field a
  differently-grouped sibling module needs once \<open>code_identifier\<close>
  introduces module boundaries the unsplit default did not have. Not a cycle
  this time, and not fixable by regrouping; the two-way split (\<open>Core\<close>,
  \<open>Analyse\<close>) is the finest division the OCaml compiler accepts.

\<close>




code_identifier
  code_module VIMP_Notation \<rightharpoonup> (OCaml) Core
| code_module VIMP_Proc \<rightharpoonup> (OCaml) Core
| code_module VIMP_Source_Print \<rightharpoonup> (OCaml) Core
| code_module VIMP_Syntax \<rightharpoonup> (OCaml) Core
| code_module CFG_Def \<rightharpoonup> (OCaml) Core
| code_module CFG_Enumeration \<rightharpoonup> (OCaml) Core
| code_module CFG_Prune \<rightharpoonup> (OCaml) Core
| code_module Compile_Invariants \<rightharpoonup> (OCaml) Core
| code_module VIMP_Proc_to_CFG \<rightharpoonup> (OCaml) Core
| code_module Abstract_Domain \<rightharpoonup> (OCaml) Core
| code_module Exec_St \<rightharpoonup> (OCaml) Core
| code_module Exec_Bridge \<rightharpoonup> (OCaml) Core
| code_module AList \<rightharpoonup> (OCaml) Core
| code_module Nat \<rightharpoonup> (OCaml) Core
| code_module Int \<rightharpoonup> (OCaml) Core
| code_module Code_Numeral \<rightharpoonup> (OCaml) Core
| code_module Num \<rightharpoonup> (OCaml) Core
| code_module Groups \<rightharpoonup> (OCaml) Core
| code_module Rings \<rightharpoonup> (OCaml) Core
| code_module Fields \<rightharpoonup> (OCaml) Core
| code_module Power \<rightharpoonup> (OCaml) Core
| code_module Parity \<rightharpoonup> (OCaml) Core
| code_module Euclidean_Rings \<rightharpoonup> (OCaml) Core
| code_module Semiring_Normalization \<rightharpoonup> (OCaml) Core
| code_module Code_Target_Int \<rightharpoonup> (OCaml) Core
| code_module Code_Target_Nat \<rightharpoonup> (OCaml) Core
| code_module Pure \<rightharpoonup> (OCaml) Core
| code_module String \<rightharpoonup> (OCaml) Core
| code_module Char_ord \<rightharpoonup> (OCaml) Core
| code_module Code_Abstract_Char \<rightharpoonup> (OCaml) Core
| code_module Comparator \<rightharpoonup> (OCaml) Core
| code_module Compare_Instances \<rightharpoonup> (OCaml) Core
| code_module Countable \<rightharpoonup> (OCaml) Core
| code_module Enum \<rightharpoonup> (OCaml) Core
| code_module FSet \<rightharpoonup> (OCaml) Core
| code_module Finite_Map \<rightharpoonup> (OCaml) Core
| code_module Finite_Set \<rightharpoonup> (OCaml) Core
| code_module Fun \<rightharpoonup> (OCaml) Core
| code_module Lattices \<rightharpoonup> (OCaml) Core
| code_module Lattices_Big \<rightharpoonup> (OCaml) Core
| code_module List \<rightharpoonup> (OCaml) Core
| code_module Map \<rightharpoonup> (OCaml) Core
| code_module Option \<rightharpoonup> (OCaml) Core
| code_module Orderings \<rightharpoonup> (OCaml) Core
| code_module Product_Lexorder \<rightharpoonup> (OCaml) Core
| code_module Product_Type \<rightharpoonup> (OCaml) Core
| code_module Set \<rightharpoonup> (OCaml) Core
| code_module Sum_Type \<rightharpoonup> (OCaml) Core
| code_module Basics_side \<rightharpoonup> (OCaml) Core
| code_module Destabilization_side \<rightharpoonup> (OCaml) Core
| code_module TD_side \<rightharpoonup> (OCaml) Core
| code_module TD_side_upd_rule \<rightharpoonup> (OCaml) Core
| code_module Update_rules \<rightharpoonup> (OCaml) Core
| code_module Strategy_Tree_Monad \<rightharpoonup> (OCaml) Core
| code_module TD_Side_CFG \<rightharpoonup> (OCaml) Core
| code_module TD_Side_Eff_Keyed_Gen \<rightharpoonup> (OCaml) Core
| code_module TD_Side_Tree \<rightharpoonup> (OCaml) Core
| code_module Constraint_System \<rightharpoonup> (OCaml) Core
| code_module DG_Framework \<rightharpoonup> (OCaml) Core
| code_module Abstract_Checks \<rightharpoonup> (OCaml) Core
| code_module Exec_DG_Bridge \<rightharpoonup> (OCaml) Core
| code_module Sign_Arithmetic \<rightharpoonup> (OCaml) Core
| code_module Sign_Backward \<rightharpoonup> (OCaml) Core
| code_module Sign_Checks \<rightharpoonup> (OCaml) Core
| code_module Sign_Exec \<rightharpoonup> (OCaml) Core
| code_module Sign_Exec_Sound \<rightharpoonup> (OCaml) Core
| code_module Sign_Lattice \<rightharpoonup> (OCaml) Core
| code_module Sign_Numeric_Queries \<rightharpoonup> (OCaml) Core
| code_module Interval_Arithmetic \<rightharpoonup> (OCaml) Core
| code_module Interval_Backward \<rightharpoonup> (OCaml) Core
| code_module Interval_Bounds \<rightharpoonup> (OCaml) Core
| code_module Interval_Checks \<rightharpoonup> (OCaml) Core
| code_module Interval_Exec_Sound \<rightharpoonup> (OCaml) Core
| code_module Interval_Lattice \<rightharpoonup> (OCaml) Core
| code_module Interval_Numeric_Queries \<rightharpoonup> (OCaml) Core
| code_module Interval_Warrowing \<rightharpoonup> (OCaml) Core
| code_module Ivl_Exec \<rightharpoonup> (OCaml) Core
| code_module Routed_Context \<rightharpoonup> (OCaml) Core
| code_module Interval_Exec_Ctx_Sound \<rightharpoonup> (OCaml) Core
| code_module Example_Analysis_Dispatch \<rightharpoonup> (OCaml) Analyse


export_code
  analyse Sign_Analysis Interval_Analysis
  analyse_with_state SignValue IntervalValue
  analyse_ctx Ctx_None Ctx_EntryState
  mk_program proc_decl_of
  SKIP com.Call Random com.If Assign Seq While Restore Unwind Return Check
  N V Plus Minus Times
  Bc bexp.Not And Or Less bexp.Eq
  Check_Proved Check_Refuted Check_Unknown
  int_of_integer nat_of_integer integer_of_int integer_of_nat
  Statement FunctionEntry FunctionResult
  char_of_integer integer_of_char
  compile_program prog_main_name cfg_intra_list cfg_calls_list cfg_entry
  EA_Nop EA_Assign EA_Random EA_Assume EA_AssumeNot EA_Ret EA_Check CallEdge
  string_of_bexp

export_code
  analyse Sign_Analysis Interval_Analysis
  analyse_with_state SignValue IntervalValue
  analyse_ctx Ctx_None Ctx_EntryState
  mk_program proc_decl_of
  SKIP com.Call Random com.If Assign Seq While Restore Unwind Return Check
  N V Plus Minus Times
  Bc bexp.Not And Or Less bexp.Eq
  Check_Proved Check_Refuted Check_Unknown
  int_of_integer nat_of_integer integer_of_int integer_of_nat
  Statement FunctionEntry FunctionResult
  char_of_integer integer_of_char
  compile_program prog_main_name cfg_intra_list cfg_calls_list cfg_entry
  EA_Nop EA_Assign EA_Random EA_Assume EA_AssumeNot EA_Ret EA_Check CallEdge
  string_of_bexp
  in OCaml file_prefix "Voblint_Analyse_OCaml"

text \<open>
  Acceptance regression A (no-call global self-feedback, task #39): no procedure, no call,
  just one global write that reads its own prior value through the flow-insensitive global
  summary, plus one independent base-case write. Isolates global-summary widening on its own,
  without any interprocedural (\<open>dgs_enter\<close>/\<open>dgs_combine\<close>) machinery in play at all --- this is
  the minimal case that first proved the call/return summary was never the actual hazard.
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
     [(Statement 2, Less (N 0) (V (STR ''total'')), Check_Unknown)]"
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
  \<open>x\<close> is local (no \<open>global\<close> declaration). \<open>analyse_sign_report_for_code\<close>
  builds the per-point environment as
  \<open>combine_env_abs gs (fun_of_exec_dg_st_for gs (locals (sol (Inl (v, ())))))
     (fun_of_exec_dg_st_for gs (globs (sol (Inr ()))))\<close>,
  routing every name to the one component that actually owns it: local
  names read the local unknown, global names read the global/side unknown.
  \<open>x\<close> is local, so it reads \<open>locals\<close>' own precise \<open>SPos\<close> directly, never
  touching the global/side unknown's unrelated \<open>STop\<close> default for a name
  it never tracks.
\<close>

lemma state_wiring_ex_sign_at_check:
  "(let (_, _, _, f) = hd (filter (\<lambda>(u, _, _, _). u = Statement 1)
                             (analyse_with_state Sign_Analysis state_wiring_ex_prog))
    in f (STR ''x'')) = SignValue SPos"
  by eval

lemma state_wiring_ex_interval_at_check:
  "(let (_, _, _, f) = hd (filter (\<lambda>(u, _, _, _). u = Statement 1)
                             (analyse_with_state Interval_Analysis state_wiring_ex_prog))
    in f (STR ''x'')) = IntervalValue (Ivl (Fin 5) (Fin 5))"
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
  "fun_of_exec_dg_st_for (declared_global no_call_two_step_prog)
     (locals (snd (analyse_sign_for (declared_global no_call_two_step_prog)
       no_call_two_step_prog) (Inl (Statement 2, ())))) (STR ''x'') = SPos"
  by eval

text \<open>
  The same fix carries across an actual call boundary: \<open>foo\<close> neither reads
  nor writes the caller-local \<open>x\<close>, and \<open>x\<close> now stays precise at the check
  after the call, for exactly the same reason (the call's own combine step,
  \<open>unit_combine_step_st_env\<close>, routes the caller's locals from \<open>dc\<close> directly
  instead of joining them against \<open>g\<close>). Kept as a second, more realistic
  witness alongside \<open>no_call_two_step_prog_locals_precise\<close>, which isolates
  the same mechanism without any interprocedural machinery at all.
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

lemma dg_probe_prog_locals_proved_global_unknown:
  "analyse Sign_Analysis dg_probe_prog =
     [(Statement 5, Less (N 0) (V (STR ''x'')), Check_Proved),
      (Statement 6, Less (N 0) (V (STR ''g'')), Check_Unknown),
      (Statement 7, Less (N 0) (V (STR ''y'')), Check_Proved)]"
  by eval

text \<open>
  \<open>dg_probe_prog\<close>'s \<open>g\<close> above is \<open>Check_Unknown\<close> not because any D/G routing
  loses precision, but because \<^const>\<open>cinit_sign_st\<close> seeds every declared
  global at \<open>SZero\<close> (\<^theory>\<open>Voblint_Analysis.Sign_Exec\<close>), and the
  flow-insensitive global summary (\<^const>\<open>TD_side_always_join_Interp_solve\<close>,
  the \<open>join\<close> discipline) folds that seed in as a real contribution alongside
  every \<open>Side\<close> a write publishes --- it cannot tell "before this write" from
  "after" apart, so soundness requires covering both. \<open>join_sign SZero SPos =
  SNonNeg\<close>, and \<open>0 < g\<close> is genuinely undecided at \<open>SNonNeg\<close>: this is the
  flow-insensitive model working as designed, not a residual gap in the same
  fix as \<open>no_call_two_step_prog\<close>/\<open>dg_probe_prog\<close> above. The witness below pins
  the actual semantic reason (the joined summary value itself), not merely
  the report's \<open>Check_Unknown\<close>, which follows from it.
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

lemma global_initial_value_remains_in_summary_prog_summary_nonneg:
  "fun_of_exec_dg_st_for (declared_global global_initial_value_remains_in_summary_prog)
     (globs (snd (analyse_sign_for (declared_global global_initial_value_remains_in_summary_prog)
       global_initial_value_remains_in_summary_prog) (Inr ()))) (STR ''g'') = SNonNeg"
  by eval

lemma global_initial_value_remains_in_summary_prog_check_unknown:
  "analyse Sign_Analysis global_initial_value_remains_in_summary_prog =
     [(Statement 1, Less (N 0) (V (STR ''g'')), Check_Unknown)]"
  by eval

end
