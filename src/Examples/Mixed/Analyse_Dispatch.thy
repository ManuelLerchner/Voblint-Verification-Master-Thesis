theory Analyse_Dispatch
  imports
    Example_Sign_Codegen
    Example_Interval_Codegen
    Example_Int_Codegen
    Voblint_Formalization.Interval_Exec_Ctx_Sound
    "HOL-Library.Code_Target_Numeral"
    "HOL-Library.Code_Abstract_Char"
begin

hide_const phase.N

section \<open>A unified, verified check-report API across domains\<close>

text \<open>
  \<open>analyse_sign_report\<close> (\<^theory>\<open>Voblint_Examples.Example_Sign_Codegen\<close>) and
  \<open>analyse_interval_td_report_for\<close>/\<open>analyse_interval_td_report\<close>
  (\<^theory>\<open>Voblint_Analysis.Interval_Checks\<close>) already share one observable
  result type, \<open>check_report_entry list\<close>
  (\<^theory>\<open>Voblint_Core.Abstract_Checks\<close>), even though the two domains'
  internal abstract states (\<open>sign abs_state\<close> vs \<open>ivl abs_state\<close>) genuinely
  differ. \<open>analyse\<close> below is therefore a thin dispatcher, not a new proof:
  each branch reuses the domain's own already-generic, already-sound report
  function unchanged.

  The \<open>Interval_Analysis\<close> branch dispatches to \<open>analyse_interval_td_report\<close>, the
  widening/warrowing-backed report, not the always-join \<open>analyse_interval_report\<close>: Interval's
  local carrier has infinite height (an unbounded integer bound), so a genuine loop that grows a
  local or global value without bound still needs widening for termination, warrowing's own
  guarantee, unlike plain join. Both reports now read through the same native Base-style D/G
  pipeline (\<^theory>\<open>Voblint_Analysis.Interval_Exec_Sound\<close>'s \<open>analyse_interval_dg_*\<close> family,
  mirroring Sign's own migration): VIMP globals live in the same reachability-lifted local unknown
  as locals, with no separate flow-insensitive summary at all, so \<open>Solver_Join\<close>'s own hazard is
  purely a loop-termination question now, not a global-specific one: a program whose global
  writes never occur inside a loop terminates identically under \<open>Solver_Join\<close> and
  \<open>Solver_Warrow\<close>, only a genuine unbounded loop still needs warrowing.
  \<open>analyse_interval_td_report\<close>'s soundness theorems (\<^theory>\<open>Voblint_Examples.Example_Interval_Codegen\<close>'s
  \<open>analyse_interval_td_report_sound_proved\<close>/\<open>_refuted\<close>, built on the \<open>base_dg_exec_analysis\<close>
  locale) make dispatching Interval's production default to the warrowing report a like-for-like
  swap for callers, not a precision or soundness downgrade.
\<close>

datatype analysis_kind = Sign_Analysis | Interval_Analysis | Int_Analysis

fun analyse :: "analysis_kind \<Rightarrow> imp_prog \<Rightarrow> check_report_entry list" where
  "analyse Sign_Analysis p = analyse_sign_report p"
| "analyse Interval_Analysis p = analyse_interval_td_report p"
| "analyse Int_Analysis p = analyse_int_report p"

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
| "analyse_ctx Int_Analysis Ctx_None p = Some (analyse_int_report p)"
| "analyse_ctx Int_Analysis Ctx_EntryState p = None"

text \<open>\<open>Ctx_None\<close> is exactly \<open>analyse\<close>, for both domains: the new dispatcher
  cannot silently drift from the one CLI/regression already exercises.\<close>

lemma analyse_ctx_none_eq_analyse: "analyse_ctx k Ctx_None p = Some (analyse k p)"
  by (cases k) simp_all

subsection \<open>Solver-choice dimension (experimental)\<close>

text \<open>
  The vendored side solver comes in several update-rule disciplines sharing
  one signature (\<^const>\<open>TD_side_always_join_Interp_solve\<close>,
  \<^const>\<open>TD_side_per_origin_Interp_solve\<close>,
  \<^const>\<open>TD_side_warrowing_apinis_Interp_solve\<close>): plain join, per-origin
  join, and Apinis warrowing. \<open>analyse_with_solver\<close> exposes this choice for
  experiments and regression comparisons on the same generated equation
  system, without touching \<open>analyse\<close>/\<open>analyse_ctx\<close> or any domain's
  production entry point (issue #131).

  Not every combination is meaningful: only \<open>ivl\<close> has a \<open>widen\<close> type-class
  instance (\<^theory>\<open>Voblint_Analysis.Interval_Warrowing\<close>), so \<open>Solver_Warrow\<close>
  does not even type-check against Sign -- adding a pointless \<open>widen\<close>
  instance for a finite-height domain that needs no widening would be
  scope creep, not a fix. \<open>analyse_with_solver\<close> is therefore a curated,
  explicit list of the five valid pairings, not a general
  compatibility predicate over an open solver/domain space: an
  unsupported pairing returns \<open>None\<close>, the same explicit-gap discipline
  \<open>analyse_ctx\<close> already uses for \<open>Sign_Analysis\<close>/\<open>Ctx_EntryState\<close>.

  Each domain's own production default is exactly one of these five pairs
  (\<open>Sign_Analysis\<close>/\<open>Solver_Join\<close>, \<open>Interval_Analysis\<close>/\<open>Solver_Warrow\<close>) --
  \<open>analyse_with_solver_sign_default\<close>/\<open>analyse_with_solver_interval_default\<close>
  below confirm those two reproduce \<open>analyse\<close> exactly, not just
  semantically.

  These three update-rule disciplines are convergence strategies, not
  alternative precision semantics: \<open>Exec_Ivl_Run\<close>'s
  \<open>loop_head_across_update_rules\<close> proves join, per-origin, and warrowing
  compute the identical result on a bounded local loop whenever all three
  terminate, since interval narrowing and the backward guard filter -- not
  the update rule -- carry that precision. Since the Base-style migration,
  a VIMP global lives in the same reachability-lifted local unknown as any
  local, so the choice is no longer global-specific either: any node the
  D/G solver revisits without a bounding narrowing phase --- a genuine
  loop, or a call site reached more than once --- needs warrowing for
  termination on Interval's infinite-height carrier; \<open>Solver_Join\<close> and
  \<open>Solver_PerOrigin\<close> have no such guarantee there. Termination, not
  precision, is therefore the axis on which this choice is observable.
\<close>

datatype solver_choice = Solver_Join | Solver_PerOrigin | Solver_Warrow

fun analyse_with_solver ::
    "analysis_kind \<Rightarrow> solver_choice \<Rightarrow> imp_prog \<Rightarrow> check_report_entry list option" where
  "analyse_with_solver Sign_Analysis Solver_Join p = Some (analyse_sign_report p)"
| "analyse_with_solver Sign_Analysis Solver_PerOrigin p = Some (analyse_sign_report_per_origin p)"
| "analyse_with_solver Sign_Analysis Solver_Warrow p = None"
| "analyse_with_solver Interval_Analysis Solver_Join p = Some (analyse_interval_report p)"
| "analyse_with_solver Interval_Analysis Solver_PerOrigin p = Some (analyse_interval_report_per_origin p)"
| "analyse_with_solver Interval_Analysis Solver_Warrow p = Some (analyse_interval_td_report p)"
| "analyse_with_solver Int_Analysis Solver_Join p = None"
| "analyse_with_solver Int_Analysis Solver_PerOrigin p = None"
| "analyse_with_solver Int_Analysis Solver_Warrow p = Some (analyse_int_report p)"

lemma analyse_with_solver_sign_default:
  "analyse_with_solver Sign_Analysis Solver_Join p = Some (analyse Sign_Analysis p)"
  by simp

lemma analyse_with_solver_interval_default:
  "analyse_with_solver Interval_Analysis Solver_Warrow p = Some (analyse Interval_Analysis p)"
  by simp

lemma analyse_with_solver_int_default:
  "analyse_with_solver Int_Analysis Solver_Warrow p = Some (analyse Int_Analysis p)"
  by simp

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

datatype abstract_value = SignValue sign | IntervalValue ivl | IntDomValue int_dom

fun analyse_with_state ::
    "analysis_kind \<Rightarrow> imp_prog \<Rightarrow> (pp \<times> exp \<times> check_result \<times> abstract_value abs_state) list" where
  "analyse_with_state Sign_Analysis p =
     map (\<lambda>(u, c, r, s). (u, c, r, SignValue \<circ> s)) (analyse_sign_report_with_state p)"
| "analyse_with_state Interval_Analysis p =
     map (\<lambda>(u, c, r, s). (u, c, r, IntervalValue \<circ> s)) (analyse_interval_td_report_with_state p)"
| "analyse_with_state Int_Analysis p =
     map (\<lambda>(u, c, r, s). (u, c, r, IntDomValue \<circ> s)) (analyse_int_report_with_state p)"

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
  reflection, as \<open>dispatch_demo_first_check_certified\<close>
  (regression theory \<open>Example_Analysis_Dispatch_Regression\<close>) does for one concrete instance.
  Consequently, a bare \<open>Check_Proved\<close>/\<open>Check_Refuted\<close> value \<open>analyse\<close> returns at runtime is not
  itself a discharged certificate: turning it into one requires supplying these two facts for the
  specific program and node.
\<close>

corollary analyse_interval_proved_sound:
  fixes p :: imp_prog and v :: pp and c :: exp
  assumes solve: "TD_side_warrowing_apinis_Interp_solve_c (analyse_interval_dg_eqs p)
                    (cfg_exit (prog_cfg prog_main_name p), ()) \<noteq> None"
      and wf: "wf_compile_input (declared_global p) (prog_table p) (prog_procs p) prog_main_name (prog_main p)"
      and cover_entry: "(cfg_entry (prog_cfg prog_main_name p), ()) \<in> fst (analyse_interval_dg p)"
      and cover_edge:
        "\<And>u a w. (u, a, w) \<in> intra (prog_cfg prog_main_name p) \<Longrightarrow> (w, ()) \<in> fst (analyse_interval_dg p)"
      and cover_enter:
        "\<And>c dst fs as q k. (c, CallEdge dst fs as, FunctionEntry q, k) \<in> calls (prog_cfg prog_main_name p)
           \<Longrightarrow> (FunctionEntry q, ()) \<in> fst (analyse_interval_dg p)"
      and cover_combine:
        "\<And>c dst fs as q k. (c, CallEdge dst fs as, FunctionEntry q, k) \<in> calls (prog_cfg prog_main_name p)
           \<Longrightarrow> (k, ()) \<in> fst (analyse_interval_dg p)"
      and mem: "(v, c, Check_Proved) \<in> set (analyse Interval_Analysis p)"
  shows "\<forall>s \<in> ltr_collect (declared_global p) (prog_cfg prog_main_name p) (cinit_stores (declared_global p)) v.
           truthy (aval c s)"
proof -
  have finI: "finite (intra (prog_cfg prog_main_name p))"
    unfolding prog_cfg_def using compile_prog_finite by simp
  have finC: "finite (calls (prog_cfg prog_main_name p))"
    unfolding prog_cfg_def using compile_prog_finite by simp
  show ?thesis
    by (rule analyse_interval_td_report_sound_proved
          [OF solve wf cover_entry cover_edge cover_enter cover_combine finI finC
              mem[unfolded analyse.simps]])
qed

corollary analyse_interval_refuted_sound:
  fixes p :: imp_prog and v :: pp and c :: exp
  assumes solve: "TD_side_warrowing_apinis_Interp_solve_c (analyse_interval_dg_eqs p)
                    (cfg_exit (prog_cfg prog_main_name p), ()) \<noteq> None"
      and wf: "wf_compile_input (declared_global p) (prog_table p) (prog_procs p) prog_main_name (prog_main p)"
      and cover_entry: "(cfg_entry (prog_cfg prog_main_name p), ()) \<in> fst (analyse_interval_dg p)"
      and cover_edge:
        "\<And>u a w. (u, a, w) \<in> intra (prog_cfg prog_main_name p) \<Longrightarrow> (w, ()) \<in> fst (analyse_interval_dg p)"
      and cover_enter:
        "\<And>c dst fs as q k. (c, CallEdge dst fs as, FunctionEntry q, k) \<in> calls (prog_cfg prog_main_name p)
           \<Longrightarrow> (FunctionEntry q, ()) \<in> fst (analyse_interval_dg p)"
      and cover_combine:
        "\<And>c dst fs as q k. (c, CallEdge dst fs as, FunctionEntry q, k) \<in> calls (prog_cfg prog_main_name p)
           \<Longrightarrow> (k, ()) \<in> fst (analyse_interval_dg p)"
      and mem: "(v, c, Check_Refuted) \<in> set (analyse Interval_Analysis p)"
  shows "\<forall>s \<in> ltr_collect (declared_global p) (prog_cfg prog_main_name p) (cinit_stores (declared_global p)) v.
           \<not> truthy (aval c s)"
proof -
  have finI: "finite (intra (prog_cfg prog_main_name p))"
    unfolding prog_cfg_def using compile_prog_finite by simp
  have finC: "finite (calls (prog_cfg prog_main_name p))"
    unfolding prog_cfg_def using compile_prog_finite by simp
  show ?thesis
    by (rule analyse_interval_td_report_sound_refuted
          [OF solve wf cover_entry cover_edge cover_enter cover_combine finI finC
              mem[unfolded analyse.simps]])
qed

corollary analyse_sign_proved_sound:
  fixes p :: imp_prog and v :: pp and c :: exp
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
  shows "\<forall>s \<in> ltr_collect (declared_global p) (prog_cfg prog_main_name p) (cinit_stores (declared_global p)) v. truthy (aval c s)"
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
  fixes p :: imp_prog and v :: pp and c :: exp
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
  shows "\<forall>s \<in> ltr_collect (declared_global p) (prog_cfg prog_main_name p) (cinit_stores (declared_global p)) v. \<not> truthy (aval c s)"
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
  unconditionally), so \<open>V\<close>/\<open>Assign\<close>/\<open>com.Call\<close>/\<open>FunctionEntry\<close>/
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

  \<open>string_of_exp\<close> is exported alongside the structured \<open>exp\<close> already in
  every \<open>check_report_entry\<close>: a consumer can pattern-match the AST directly,
  or call \<open>string_of_exp\<close> to render a check's condition as a native string
  without decoding it --- both stay available, not a replacement report type.
\<close>

text \<open>
  The codegen session imports this theory and uses the following
  \<open>code_identifier\<close> declaration to organize the generated OCaml. Without a
  \<open>module_name\<close>, the serializer distributes output over one module per
  contributing Isabelle theory --- around sixty of them here, most named
  after internal proof-repo theories (\<open>TD_side\<close>, \<open>Interval_Warrowing\<close>,
  \<open>DG_Framework\<close>, ...) meaningless to an external reader and irrelevant to
  \<open>analyse\<close>'s public surface. The remapping places every contributing
  theory in two named OCaml modules, so an external reader is not left
  staring at either one undifferentiated file or dozens of
  internal-theory names.

  OCaml's serializer emits one file per export regardless of
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
| code_module VIMP_Expr \<rightharpoonup> (OCaml) Core
| code_module VIMP_Proc \<rightharpoonup> (OCaml) Core
| code_module VIMP_Special \<rightharpoonup> (OCaml) Core
| code_module VIMP_Source_Print \<rightharpoonup> (OCaml) Core
| code_module VIMP_Syntax \<rightharpoonup> (OCaml) Core
| code_module CFG_Def \<rightharpoonup> (OCaml) Core
| code_module CFG_Enumeration \<rightharpoonup> (OCaml) Core
| code_module CFG_Prune \<rightharpoonup> (OCaml) Core
| code_module Compile_Invariants \<rightharpoonup> (OCaml) Core
| code_module VIMP_Proc_to_CFG \<rightharpoonup> (OCaml) Core
| code_module Abstract_Domain \<rightharpoonup> (OCaml) Core
| code_module Numeric_Ops \<rightharpoonup> (OCaml) Core
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
| code_module DG_Base_Exec \<rightharpoonup> (OCaml) Core
| code_module Sign_Arithmetic \<rightharpoonup> (OCaml) Core
| code_module Sign_Special \<rightharpoonup> (OCaml) Core
| code_module Sign_Backward \<rightharpoonup> (OCaml) Core
| code_module Sign_Checks \<rightharpoonup> (OCaml) Core
| code_module Sign_Exec \<rightharpoonup> (OCaml) Core
| code_module Sign_Exec_Sound \<rightharpoonup> (OCaml) Core
| code_module Sign_Lattice \<rightharpoonup> (OCaml) Core
| code_module Sign_Numeric_Queries \<rightharpoonup> (OCaml) Core
| code_module Interval_Arithmetic \<rightharpoonup> (OCaml) Core
| code_module Interval_Special \<rightharpoonup> (OCaml) Core
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
| code_module HOL \<rightharpoonup> (OCaml) Core
| code_module Multiset \<rightharpoonup> (OCaml) Core
| code_module Groups_List \<rightharpoonup> (OCaml) Core
| code_module GCD \<rightharpoonup> (OCaml) Core
| code_module Factorial_Ring \<rightharpoonup> (OCaml) Core
| code_module Euclidean_Algorithm \<rightharpoonup> (OCaml) Core
| code_module While_Combinator \<rightharpoonup> (OCaml) Core
| code_module Congruence_Domain \<rightharpoonup> (OCaml) Core
| code_module Congruence_Lattice \<rightharpoonup> (OCaml) Core
| code_module Congruence_Arithmetic \<rightharpoonup> (OCaml) Core
| code_module Congruence_Backward \<rightharpoonup> (OCaml) Core
| code_module Congruence_Warrowing \<rightharpoonup> (OCaml) Core
| code_module Parity_Domain \<rightharpoonup> (OCaml) Core
| code_module Parity_Special \<rightharpoonup> (OCaml) Core
| code_module Int_Domain \<rightharpoonup> (OCaml) Core
| code_module Int_Refinement \<rightharpoonup> (OCaml) Core
| code_module Int_Arithmetic \<rightharpoonup> (OCaml) Core
| code_module Int_Backward \<rightharpoonup> (OCaml) Core
| code_module Int_Warrowing \<rightharpoonup> (OCaml) Core
| code_module Int_Transfer \<rightharpoonup> (OCaml) Core
| code_module Int_Exec \<rightharpoonup> (OCaml) Core
| code_module Int_Exec_Sound \<rightharpoonup> (OCaml) Core
| code_module Int_Checks \<rightharpoonup> (OCaml) Core
| code_module Analyse_Dispatch \<rightharpoonup> (OCaml) Analyse




end
