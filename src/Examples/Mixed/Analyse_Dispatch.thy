theory Analyse_Dispatch
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
  current value (\<open>total := total + n\<close> is the minimal reproducer, isolated in
  the regression theory \<open>Example_Analysis_Dispatch_Regression\<close> to \<^emph>\<open>not\<close>
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
  reflection, as \<open>dispatch_demo_first_check_certified\<close>
  (regression theory \<open>Example_Analysis_Dispatch_Regression\<close>) does for one concrete instance.
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
| code_module Analyse_Dispatch \<rightharpoonup> (OCaml) Analyse


export_code
  analyse Sign_Analysis Interval_Analysis
  analyse_with_state SignValue IntervalValue
  analyse_ctx Ctx_None Ctx_EntryState
  mk_program proc_decl_of
  SKIP com.Call com.If Assign Seq While Restore Unwind Return Check
  N V Plus Minus Times
  Bc bexp.Not And Or Less bexp.Eq
  Check_Proved Check_Refuted Check_Unknown
  int_of_integer nat_of_integer integer_of_int integer_of_nat
  Statement FunctionEntry FunctionResult
  char_of_integer integer_of_char
  compile_program prog_main_name cfg_intra_list cfg_calls_list cfg_entry
  EA_Nop EA_Assign EA_Special EA_Assume EA_AssumeNot EA_Ret EA_Check CallEdge Nondet_Int
  string_of_bexp

export_code
  analyse Sign_Analysis Interval_Analysis
  analyse_with_state SignValue IntervalValue
  analyse_ctx Ctx_None Ctx_EntryState
  mk_program proc_decl_of
  SKIP com.Call com.If Assign Seq While Restore Unwind Return Check
  N V Plus Minus Times
  Bc bexp.Not And Or Less bexp.Eq
  Check_Proved Check_Refuted Check_Unknown
  int_of_integer nat_of_integer integer_of_int integer_of_nat
  Statement FunctionEntry FunctionResult
  char_of_integer integer_of_char
  compile_program prog_main_name cfg_intra_list cfg_calls_list cfg_entry
  EA_Nop EA_Assign EA_Special EA_Assume EA_AssumeNot EA_Ret EA_Check CallEdge Nondet_Int
  string_of_bexp
  in OCaml file_prefix "Voblint_Analyse_OCaml"

end
