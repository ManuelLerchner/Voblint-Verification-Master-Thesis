theory Analyse_Dispatch
  imports
    Voblint_Analysis_Sign.Sign_Entry
    Voblint_Analysis_Interval.Interval_Entry
    Voblint_Analysis_Int.Int_Entry
    Voblint_Analysis_Parity.Parity_Entry
    Voblint_Analysis_Interval.Interval_Analyses
    Voblint_Analysis_Sign.Sign_Analyses
    Voblint_Analysis_Int.Int_Analyses
    Voblint_Analysis_Base.Analysis_Config
    "HOL-Library.Code_Target_Numeral"
    "HOL-Library.Code_Abstract_Char"
begin

hide_const phase.N

section \<open>A unified, verified check-report API across domains\<close>

text \<open>
  \<open>analyse_sign_report\<close> (\<^theory>\<open>Voblint_Analysis_Sign.Sign_Entry\<close>) and
  \<open>analyse_interval_td_report_for\<close>/\<open>analyse_interval_td_report\<close>
  (\<^theory>\<open>Voblint_Analysis_Interval.Interval_Checks\<close>) already share one observable
  result type, \<open>check_report_entry list\<close>
  (\<^theory>\<open>Voblint_Framework.Abstract_Checks\<close>), even though the two domains'
  internal abstract states (\<open>sign abs_state\<close> vs \<open>ivl abs_state\<close>) genuinely
  differ. \<open>analyse\<close> below is therefore a thin dispatcher, not a new proof:
  each branch reuses the domain's own already-generic, already-sound report
  function unchanged.

  The \<open>Interval_Analysis\<close> branch dispatches to \<open>analyse_interval_td_report\<close>, the
  widening/warrowing-backed report, not the always-join \<open>analyse_interval_report\<close>: Interval's
  local carrier has infinite height (an unbounded integer bound), so a genuine loop that grows a
  local or global value without bound still needs widening for termination, warrowing's own
  guarantee, unlike plain join. All three reports (\<open>analyse_interval_td_report\<close>,
  \<open>analyse_interval_report\<close>, \<open>analyse_interval_report_per_origin\<close>) now read through the routed
  D/G spine (\<^theory>\<open>Voblint_Analysis_Interval.Interval_Analyses\<close>, mirroring Sign's own
  migration) instead of the Base-family \<open>analyse_interval_dg_*\<close> pipeline: VIMP globals live in a
  keyed seed slot rather than a separate flow-insensitive summary, so \<open>Solver_Join\<close>'s own hazard
  is purely a loop-termination question now, not a global-specific one: a program whose global
  writes never occur inside a loop terminates identically under \<open>Solver_Join\<close> and
  \<open>Solver_Warrow\<close>, only a genuine unbounded loop still needs warrowing.
  \<open>analyse_interval_td_report\<close>'s soundness theorems
  (\<^theory>\<open>Voblint_Analysis_Interval.Interval_Entry\<close>'s
  \<open>analyse_interval_td_report_sound_proved\<close>/\<open>_refuted\<close>, built on the routed spine's own
  \<open>interval_conf_result_node_sound_warrow\<close>) make dispatching Interval's production default to the
  warrowing report a like-for-like swap for callers, not a precision or soundness downgrade.
\<close>

fun analyse :: "analysis_domain \<Rightarrow> imp_prog \<Rightarrow> check_report_entry list" where
  "analyse Sign_Analysis p = analyse_sign_report p"
| "analyse Interval_Analysis p = analyse_interval_td_report p"
| "analyse Int_Analysis p = analyse_int_report p"
| "analyse Parity_Analysis p = analyse_parity_report p"

subsection \<open>Context-sensitivity dimension\<close>

text \<open>
  \<open>Ctx_None\<close> is today's flow-insensitive, call-site-insensitive behaviour;
  \<open>Ctx_EntryState\<close> selects the value-derived entry-state context analysis
  (\<^theory>\<open>Voblint_Analysis_Interval.Interval_Analyses\<close>, #108). Deliberately not
  a wider \<open>analyse\<close>: \<open>analyse\<close>/\<open>analyse_with_state\<close> stay untouched (the CLI's
  no-\<open>--context\<close> path, the GraphViz report, and every existing
  \<open>codegen/regression\<close> consumer already pin their exact two-argument shape as a
  trust boundary). \<open>analyse_config_ctx\<close> below is the entry point for this
  dimension; legality is decided once, by \<open>resolve_analysis_config\<close>, and an
  unsupported combination answers \<open>None\<close> there rather than falling back
  silently to context-insensitive behaviour.

  The report's verdict is a \<^typ>\<open>contextual_verdict\<close>, not a bare
  \<^typ>\<open>check_result\<close>, because a context-sensitive analysis genuinely has a
  fourth answer: a check every covered context finds unreachable is
  \<^const>\<open>Dead\<close>, and rendering it as any \<^typ>\<open>check_result\<close> either fabricates
  a proof or invents an undecided execution. The \<open>Ctx_None\<close> branches lift
  their existing reports through \<^const>\<open>decided_report\<close>: those reports carry
  one observation per check and no deadness channel of their own, so the lift
  adds no claim. The dead-code filter the context-insensitive text report
  applies at the CLI comes from \<open>analyse_with_state\<close>'s separate
  unreachability flag, not from this dispatcher.
\<close>

subsection \<open>Solver-choice dimension (experimental)\<close>

text \<open>
  The vendored side solver comes in several update-rule disciplines sharing
  one signature (\<^const>\<open>TD_side_always_join_Interp_solve\<close>,
  \<^const>\<open>TD_side_per_origin_Interp_solve\<close>,
  \<^const>\<open>TD_side_warrowing_apinis_Interp_solve\<close>): plain join, per-origin
  join, and Apinis warrowing. \<open>analyse_with_solver\<close> exposes this choice for
  experiments and regression comparisons on the same generated equation
  system, without touching \<open>analyse\<close> or any domain's production entry point.

  Not every combination is meaningful, and the reason is a missing proof rather
  than a missing instance. \<open>sign\<close> and \<open>parity\<close> are finite lattices that do carry
  a \<open>widen\<close> (\<open>widen = sup\<close>, from their \<open>warrowing\<close> instantiations, which
  \<open>int_dom\<close>'s own componentwise instance needs), so \<open>Solver_Warrow\<close> against them
  type-checks; what neither has is a solved table or a soundness corollary
  behind that rule, and exposing a pairing on the strength of the instance alone
  is exactly what this resolver refuses to do. \<open>analyse_with_solver\<close> is therefore a curated,
  explicit list of the valid pairings, not a general compatibility
  predicate over an open solver/domain space: an unsupported pairing
  returns \<open>None\<close>, the same explicit-gap discipline \<open>resolve_analysis_config\<close>
  applies on the context axis. \<open>int_dom\<close> carries the warrowing route through to
  a proved result (\<^theory>\<open>Voblint_Analysis_Int.Int_Warrowing\<close>, its own
  production default), so every \<open>int_dom\<close> pairing is supported. Of the sixteen
  \<open>analysis_domain \<times> solver_choice\<close> combinations the four \<open>None\<close>s are exactly the two
  widening rules against Sign and Parity, whose finite height means no analysis
  here has needed that route enough to prove it.

  Each domain's own production default is exactly one of these pairings
  (\<open>Sign_Analysis\<close>/\<open>Solver_Join\<close>, \<open>Interval_Analysis\<close>/\<open>Solver_Warrow\<close>,
  \<open>Int_Analysis\<close>/\<open>Solver_Warrow\<close>) -- \<open>analyse_with_solver_sign_default\<close>/
  \<open>analyse_with_solver_interval_default\<close>/\<open>analyse_with_solver_int_default\<close>
  below confirm all three reproduce \<open>analyse\<close> exactly, not just
  semantically.

  Among \<open>Solver_Join\<close>, \<open>Solver_PerOrigin\<close> and \<open>Solver_Warrow\<close> the choice is a convergence
  strategy: \<open>Exec_Interval_Run\<close>'s \<open>loop_head_join\<close>, \<open>loop_head_per_origin\<close> and
  \<open>loop_head_warrow\<close> prove all three compute the identical result on a bounded local loop
  whenever they terminate, since interval narrowing and the backward guard filter -- not
  the update rule -- carry that precision.
  Since the Base-style migration, a VIMP global lives in the same reachability-lifted local
  unknown as any local, so the choice is no longer global-specific either: any node the D/G
  solver revisits without a bounding narrowing phase --- a genuine loop, or a call site
  reached more than once --- needs warrowing for termination on Interval's infinite-height
  carrier; \<open>Solver_Join\<close> and \<open>Solver_PerOrigin\<close> have no such guarantee there.

  \<open>Solver_WarrowPerOrigin\<close> breaks that pattern, and is the reason this axis is not purely
  about termination. It widens each origin's own contribution and joins afterwards, where
  \<open>Solver_Warrow\<close> widens the value already joined across every origin. Both terminate;
  they can still disagree. \<open>Example_Per_Origin_Widening_Precision\<close> is the witness: two
  producers writing \<open>[1,1]\<close> and \<open>[2,2]\<close> to one global leave the joined rule at
  \<open>[1, +inf]\<close> --- the second write makes the joined upper bound grow, though neither
  producer's own contribution ever moved --- where the per-origin rule reads \<open>[1,2]\<close>.
\<close>

fun analyse_with_solver ::
    "analysis_domain \<Rightarrow> solver_choice \<Rightarrow> imp_prog \<Rightarrow> check_report_entry list option" where
  "analyse_with_solver Sign_Analysis Solver_Join p = Some (analyse_sign_report p)"
| "analyse_with_solver Sign_Analysis Solver_PerOrigin p = Some (analyse_sign_report_per_origin p)"
| "analyse_with_solver Sign_Analysis Solver_Warrow p = None"
| "analyse_with_solver Interval_Analysis Solver_Join p = Some (analyse_interval_report p)"
| "analyse_with_solver Interval_Analysis Solver_PerOrigin p = Some (analyse_interval_report_per_origin p)"
| "analyse_with_solver Interval_Analysis Solver_Warrow p = Some (analyse_interval_td_report p)"
| "analyse_with_solver Int_Analysis Solver_Join p = Some (analyse_int_report_join p)"
| "analyse_with_solver Int_Analysis Solver_PerOrigin p = Some (analyse_int_report_per_origin p)"
| "analyse_with_solver Int_Analysis Solver_Warrow p = Some (analyse_int_report p)"
| "analyse_with_solver Parity_Analysis Solver_Join p = Some (analyse_parity_report p)"
| "analyse_with_solver Parity_Analysis Solver_PerOrigin p = Some (analyse_parity_report_per_origin p)"
| "analyse_with_solver Parity_Analysis Solver_Warrow p = None"
| "analyse_with_solver Sign_Analysis Solver_WarrowPerOrigin p = None"
| "analyse_with_solver Interval_Analysis Solver_WarrowPerOrigin p = Some (analyse_interval_report_wpo p)"
| "analyse_with_solver Int_Analysis Solver_WarrowPerOrigin p = Some (analyse_int_report_wpo p)"
| "analyse_with_solver Parity_Analysis Solver_WarrowPerOrigin p = None"

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
  \<open>analyse_interval_td_report_with_state\<close> (\<^theory>\<open>Voblint_Analysis_Sign.Sign_Checks\<close>,
  \<^theory>\<open>Voblint_Analysis_Interval.Interval_Checks\<close>) unchanged, just as \<open>analyse\<close> reuses
  their state-free counterparts.
\<close>

datatype abstract_value =
  SignValue sign | IntervalValue ivl | IntDomValue int_dom | ParityValue parity

definition tag_states ::
    "('s \<Rightarrow> abstract_value) \<Rightarrow> (pp \<times> exp \<times> check_result \<times> bool \<times> 's abs_state) list
       \<Rightarrow> (pp \<times> exp \<times> check_result \<times> bool \<times> abstract_value abs_state) list" where
  "tag_states tag = map (\<lambda>(u, c, r, unreachable, s). (u, c, r, unreachable, tag \<circ> s))"

text \<open>
  One state-carrying report per \<open>analysis_domain \<times> solver_choice\<close> pairing that has a
  solved table, \<^const>\<open>None\<close> at the pairings \<^const>\<open>analyse_with_solver\<close> also rejects.
  Each domain's production default reads its own \<open>analyse_*_report_with_state\<close>
  constant unchanged; the other solved tables are read through their
  \<^locale>\<open>analysis_surface\<close> instance, which is the same \<^const>\<open>classify_checks_with_state\<close>
  assembly over the table that solver produced. This is what lets an explicit
  \<open>--solver\<close> keep the unreachable flag: a flat \<^const>\<open>analyse_with_solver\<close> report has
  no deadness channel, so a check inside an infeasible branch would print the
  bottom state's vacuous verdict instead of being suppressed.
\<close>

fun analyse_with_state ::
    "analysis_domain \<Rightarrow> solver_choice \<Rightarrow> imp_prog
       \<Rightarrow> (pp \<times> exp \<times> check_result \<times> bool \<times> abstract_value abs_state) list option" where
  "analyse_with_state Sign_Analysis Solver_Join p = Some (tag_states SignValue (analyse_sign_report_with_state p))"
| "analyse_with_state Sign_Analysis Solver_PerOrigin p = Some (tag_states SignValue (sign_per_origin.report_with_state p))"
| "analyse_with_state Sign_Analysis Solver_Warrow p = None"
| "analyse_with_state Sign_Analysis Solver_WarrowPerOrigin p = None"
| "analyse_with_state Interval_Analysis Solver_Join p = Some (tag_states IntervalValue (interval_join.report_with_state p))"
| "analyse_with_state Interval_Analysis Solver_PerOrigin p = Some (tag_states IntervalValue (interval_per_origin.report_with_state p))"
| "analyse_with_state Interval_Analysis Solver_Warrow p = Some (tag_states IntervalValue (analyse_interval_td_report_with_state p))"
| "analyse_with_state Interval_Analysis Solver_WarrowPerOrigin p = Some (tag_states IntervalValue (interval_wpo.report_with_state p))"
| "analyse_with_state Int_Analysis Solver_Join p = Some (tag_states IntDomValue (int_join.report_with_state p))"
| "analyse_with_state Int_Analysis Solver_PerOrigin p = Some (tag_states IntDomValue (int_per_origin.report_with_state p))"
| "analyse_with_state Int_Analysis Solver_Warrow p = Some (tag_states IntDomValue (analyse_int_report_with_state p))"
| "analyse_with_state Int_Analysis Solver_WarrowPerOrigin p = Some (tag_states IntDomValue (int_wpo.report_with_state p))"
| "analyse_with_state Parity_Analysis Solver_Join p = Some (tag_states ParityValue (analyse_parity_report_with_state p))"
| "analyse_with_state Parity_Analysis Solver_PerOrigin p = Some (tag_states ParityValue (parity_per_origin.report_with_state p))"
| "analyse_with_state Parity_Analysis Solver_Warrow p = None"
| "analyse_with_state Parity_Analysis Solver_WarrowPerOrigin p = None"

lemma analyse_with_state_some_iff_with_solver:
  "(analyse_with_state d s p = None) = (analyse_with_solver d s p = None)"
  by (cases d; cases s) simp_all

text \<open>
  Each domain's own production default, context-free -- the GraphViz renderers'
  one report per domain, with no solver axis of their own to expose. Its four
  equations are exactly \<^const>\<open>analyse_with_state\<close>'s at each domain's default
  solver (\<open>Solver_Join\<close> for Sign and Parity, \<open>Solver_Warrow\<close> for Interval and
  Int, matching \<^const>\<open>resolve_analysis_config\<close>'s own implicit-default choice),
  restated as a total function so a caller with no solver selection to offer
  does not have to discharge an \<open>option\<close> it already knows is \<^const>\<open>Some\<close>.
\<close>

fun analyse_with_state_default ::
    "analysis_domain \<Rightarrow> imp_prog \<Rightarrow> (pp \<times> exp \<times> check_result \<times> bool \<times> abstract_value abs_state) list" where
  "analyse_with_state_default Sign_Analysis p = tag_states SignValue (analyse_sign_report_with_state p)"
| "analyse_with_state_default Interval_Analysis p = tag_states IntervalValue (analyse_interval_td_report_with_state p)"
| "analyse_with_state_default Int_Analysis p = tag_states IntDomValue (analyse_int_report_with_state p)"
| "analyse_with_state_default Parity_Analysis p = tag_states ParityValue (analyse_parity_report_with_state p)"

lemma analyse_with_state_default_eq:
  "analyse_with_state Sign_Analysis Solver_Join p = Some (analyse_with_state_default Sign_Analysis p)"
  "analyse_with_state Interval_Analysis Solver_Warrow p = Some (analyse_with_state_default Interval_Analysis p)"
  "analyse_with_state Int_Analysis Solver_Warrow p = Some (analyse_with_state_default Int_Analysis p)"
  "analyse_with_state Parity_Analysis Solver_Join p = Some (analyse_with_state_default Parity_Analysis p)"
  by simp_all

subsection \<open>Public API: soundness corollaries stated over the runtime dispatcher\<close>

text \<open>
  \<open>analyse_interval_proved_sound\<close>/\<open>analyse_interval_refuted_sound\<close> restate
  \<open>analyse_interval_td_report_sound_proved\<close>/\<open>_refuted\<close> (\<open>Interval_Entry\<close>) over \<open>analyse\<close>,
  matching the routed-unit producer \<open>analyse Interval_Analysis\<close> now dispatches to: solver
  termination and coverage are stated over \<open>interval_conf_sol_prog_warrow\<close>/\<open>interval_conf_terminates_prog_warrow\<close>
  (\<open>Interval_Analyses\<close>) rather than the Base family's \<open>analyse_interval_dg\<close>/
  \<open>analyse_interval_dg_eqs\<close>. \<open>finite (intra (prog_cfg prog_main_name p))\<close>/
  \<open>finite (calls ...)\<close> are no longer separate hypotheses here: the routed spine's own
  soundness chain derives both unconditionally from \<open>compile_prog_finite\<close>, so unlike the
  Base-family route this corollary needs no finiteness premise of its own.

  \<open>analyse_sign_report_sound_proved\<close>/\<open>_refuted\<close>
  (\<^theory>\<open>Voblint_Analysis_Sign.Sign_Entry\<close>) are proved
  about \<open>analyse_sign_report\<close> --- the exact constant \<open>analyse\<close> pattern-matches to, one
  \<open>analyse.simps\<close> equation away. Restating both domains' corollaries directly over \<open>analyse\<close>,
  the constant \<open>export_code\<close> exports, means connecting a runtime verdict to its soundness
  theorem never requires unfolding the dispatcher by hand.

  The remaining hypotheses stay real per-program obligations, not free: solver termination
  and, for both domains, the checked node's reachability to \<open>cfg_exit\<close>. Nothing in this
  formalization proves that either solver terminates on every input program, so termination
  stays a genuine premise --- typically discharged \<open>by eval\<close> on a concrete program via
  \<open>interval_conf_terminates_prog_warrow_via_solve_c\<close> / \<open>TD_side_always_join_Interp_solve_c\<close> reflection,
  as \<open>dispatch_demo_first_check_certified\<close> (regression theory
  \<open>Example_Analysis_Dispatch_Regression\<close>) does for one concrete instance. Consequently, a bare
  \<open>Check_Proved\<close>/\<open>Check_Refuted\<close> value \<open>analyse\<close> returns at runtime is not itself a discharged
  certificate: turning it into one requires supplying these facts for the specific program and
  node.
\<close>

corollary analyse_interval_proved_sound:
  fixes p :: imp_prog and v :: pp and c :: exp
  assumes wf: "wf_compile_input (declared_global p) (prog_table p) (prog_procs p)"
      and solve: "interval_conf_terminates_prog_warrow (declared_global p) p"
      and entry_cov: "(cfg_entry (prog_cfg p), ()) \<in> fst (interval_conf_sol_prog_warrow (declared_global p) p)"
      and fwd_ok:
        "\<And>u a w ctx. (u, ctx) \<in> fst (interval_conf_sol_prog_warrow (declared_global p) p)
           \<Longrightarrow> (u, a, w) \<in> intra (prog_cfg p) \<Longrightarrow> (w, ctx) \<in> fst (interval_conf_sol_prog_warrow (declared_global p) p)"
      and call_fwd_ok:
        "\<And>u ctx dst fs as q k. (u, ctx) \<in> fst (interval_conf_sol_prog_warrow (declared_global p) p)
           \<Longrightarrow> (u, CallEdge dst fs as, FunctionEntry q, k) \<in> calls (prog_cfg p)
           \<Longrightarrow> (FunctionEntry q, ()) \<in> fst (interval_conf_sol_prog_warrow (declared_global p) p)"
      and comb_fwd_ok:
        "\<And>cl c1 dst fs as q k. (cl, c1) \<in> fst (interval_conf_sol_prog_warrow (declared_global p) p)
           \<Longrightarrow> (cl, CallEdge dst fs as, FunctionEntry q, k) \<in> calls (prog_cfg p)
           \<Longrightarrow> (k, c1) \<in> fst (interval_conf_sol_prog_warrow (declared_global p) p)"
      and mem: "(v, c, Check_Proved) \<in> set (analyse Interval_Analysis p)"
  shows "\<forall>s \<in> ltr_collect (declared_global p) (prog_cfg p) (cinit_stores (declared_global p)) v.
           truthy (aval c s)"
  by (rule analyse_interval_td_report_sound_proved
        [OF wf solve entry_cov fwd_ok call_fwd_ok comb_fwd_ok mem[unfolded analyse.simps]])

corollary analyse_interval_refuted_sound:
  fixes p :: imp_prog and v :: pp and c :: exp
  assumes wf: "wf_compile_input (declared_global p) (prog_table p) (prog_procs p)"
      and solve: "interval_conf_terminates_prog_warrow (declared_global p) p"
      and entry_cov: "(cfg_entry (prog_cfg p), ()) \<in> fst (interval_conf_sol_prog_warrow (declared_global p) p)"
      and fwd_ok:
        "\<And>u a w ctx. (u, ctx) \<in> fst (interval_conf_sol_prog_warrow (declared_global p) p)
           \<Longrightarrow> (u, a, w) \<in> intra (prog_cfg p) \<Longrightarrow> (w, ctx) \<in> fst (interval_conf_sol_prog_warrow (declared_global p) p)"
      and call_fwd_ok:
        "\<And>u ctx dst fs as q k. (u, ctx) \<in> fst (interval_conf_sol_prog_warrow (declared_global p) p)
           \<Longrightarrow> (u, CallEdge dst fs as, FunctionEntry q, k) \<in> calls (prog_cfg p)
           \<Longrightarrow> (FunctionEntry q, ()) \<in> fst (interval_conf_sol_prog_warrow (declared_global p) p)"
      and comb_fwd_ok:
        "\<And>cl c1 dst fs as q k. (cl, c1) \<in> fst (interval_conf_sol_prog_warrow (declared_global p) p)
           \<Longrightarrow> (cl, CallEdge dst fs as, FunctionEntry q, k) \<in> calls (prog_cfg p)
           \<Longrightarrow> (k, c1) \<in> fst (interval_conf_sol_prog_warrow (declared_global p) p)"
      and mem: "(v, c, Check_Refuted) \<in> set (analyse Interval_Analysis p)"
  shows "\<forall>s \<in> ltr_collect (declared_global p) (prog_cfg p) (cinit_stores (declared_global p)) v.
           \<not> truthy (aval c s)"
  by (rule analyse_interval_td_report_sound_refuted
        [OF wf solve entry_cov fwd_ok call_fwd_ok comb_fwd_ok mem[unfolded analyse.simps]])


text \<open>
  \<open>analyse_sign_proved_sound\<close>/\<open>analyse_sign_refuted_sound\<close> restate
  \<open>analyse_sign_report_sound_proved\<close>/\<open>_refuted\<close> (\<open>Sign_Entry\<close>) over \<open>analyse\<close>,
  matching the routed-unit producer \<open>analyse Sign_Analysis\<close> dispatches to: solver
  termination and coverage are stated over \<open>sctx_sol_prog\<close>/\<open>sctx_terminates_prog\<close>
  (\<open>Sign_Analyses\<close>). \<open>finite (intra (prog_cfg prog_main_name p))\<close>/
  \<open>finite (calls ...)\<close> are not separate hypotheses here: the routed spine's own
  soundness chain derives both unconditionally from \<open>compile_prog_finite\<close>, so this
  corollary needs no finiteness premise of its own.
\<close>

corollary analyse_sign_proved_sound:
  fixes p :: imp_prog and v :: pp and c :: exp
  assumes wf: "wf_compile_input (declared_global p) (prog_table p) (prog_procs p)"
      and solve: "sctx_terminates_prog (declared_global p) p"
      and entry_cov: "(cfg_entry (prog_cfg p), ()) \<in> fst (sctx_sol_prog (declared_global p) p)"
      and fwd_ok:
        "\<And>u a w ctx. (u, ctx) \<in> fst (sctx_sol_prog (declared_global p) p)
           \<Longrightarrow> (u, a, w) \<in> intra (prog_cfg p) \<Longrightarrow> (w, ctx) \<in> fst (sctx_sol_prog (declared_global p) p)"
      and call_fwd_ok:
        "\<And>u ctx dst fs as q k. (u, ctx) \<in> fst (sctx_sol_prog (declared_global p) p)
           \<Longrightarrow> (u, CallEdge dst fs as, FunctionEntry q, k) \<in> calls (prog_cfg p)
           \<Longrightarrow> (FunctionEntry q, ()) \<in> fst (sctx_sol_prog (declared_global p) p)"
      and comb_fwd_ok:
        "\<And>cl c1 dst fs as q k. (cl, c1) \<in> fst (sctx_sol_prog (declared_global p) p)
           \<Longrightarrow> (cl, CallEdge dst fs as, FunctionEntry q, k) \<in> calls (prog_cfg p)
           \<Longrightarrow> (k, c1) \<in> fst (sctx_sol_prog (declared_global p) p)"
      and mem: "(v, c, Check_Proved) \<in> set (analyse Sign_Analysis p)"
  shows "\<forall>s \<in> ltr_collect (declared_global p) (prog_cfg p) (cinit_stores (declared_global p)) v. truthy (aval c s)"
  by (rule analyse_sign_report_sound_proved
        [OF wf solve entry_cov fwd_ok call_fwd_ok comb_fwd_ok mem[unfolded analyse.simps]])

corollary analyse_sign_refuted_sound:
  fixes p :: imp_prog and v :: pp and c :: exp
  assumes wf: "wf_compile_input (declared_global p) (prog_table p) (prog_procs p)"
      and solve: "sctx_terminates_prog (declared_global p) p"
      and entry_cov: "(cfg_entry (prog_cfg p), ()) \<in> fst (sctx_sol_prog (declared_global p) p)"
      and fwd_ok:
        "\<And>u a w ctx. (u, ctx) \<in> fst (sctx_sol_prog (declared_global p) p)
           \<Longrightarrow> (u, a, w) \<in> intra (prog_cfg p) \<Longrightarrow> (w, ctx) \<in> fst (sctx_sol_prog (declared_global p) p)"
      and call_fwd_ok:
        "\<And>u ctx dst fs as q k. (u, ctx) \<in> fst (sctx_sol_prog (declared_global p) p)
           \<Longrightarrow> (u, CallEdge dst fs as, FunctionEntry q, k) \<in> calls (prog_cfg p)
           \<Longrightarrow> (FunctionEntry q, ()) \<in> fst (sctx_sol_prog (declared_global p) p)"
      and comb_fwd_ok:
        "\<And>cl c1 dst fs as q k. (cl, c1) \<in> fst (sctx_sol_prog (declared_global p) p)
           \<Longrightarrow> (cl, CallEdge dst fs as, FunctionEntry q, k) \<in> calls (prog_cfg p)
           \<Longrightarrow> (k, c1) \<in> fst (sctx_sol_prog (declared_global p) p)"
      and mem: "(v, c, Check_Refuted) \<in> set (analyse Sign_Analysis p)"
  shows "\<forall>s \<in> ltr_collect (declared_global p) (prog_cfg p) (cinit_stores (declared_global p)) v. \<not> truthy (aval c s)"
  by (rule analyse_sign_report_sound_refuted
        [OF wf solve entry_cov fwd_ok call_fwd_ok comb_fwd_ok mem[unfolded analyse.simps]])

text \<open>
  \<open>analyse_int_proved_sound\<close>/\<open>analyse_int_refuted_sound\<close> restate
  \<open>analyse_int_report_sound_proved\<close>/\<open>_refuted\<close> (\<open>Int_Entry\<close>) over \<open>analyse\<close>,
  matching the routed-unit producer \<open>analyse Int_Analysis\<close> now dispatches to: solver
  termination and coverage are stated over
  \<^const>\<open>int_conf_sol_prog_warrow\<close>/\<^const>\<open>int_conf_terminates_prog_warrow\<close>
  (\<^theory>\<open>Voblint_Analysis_Int.Int_Analyses\<close>), pinned at \<^const>\<open>Refine_Fixpoint\<close> --
  the CLI does not expose refinement mode as a separate axis -- rather than the Base
  family's \<open>analyse_int_dg\<close>/\<open>analyse_int_dg_eqs\<close>. \<open>int_conf_sol_prog_warrow\<close>/
  \<open>int_conf_terminates_prog_warrow\<close> need no qualification: each domain's
  configuration names carry their own prefix, so every domain's routed producer can
  be reachable from this one file without collision.
\<close>

corollary analyse_int_proved_sound:
  fixes p :: imp_prog and v :: pp and c :: exp
  assumes wf: "wf_compile_input (declared_global p) (prog_table p) (prog_procs p)"
      and solve: "int_conf_terminates_prog_warrow Refine_Fixpoint (declared_global p) p"
      and entry_cov: "(cfg_entry (prog_cfg p), ()) \<in> fst (int_conf_sol_prog_warrow Refine_Fixpoint (declared_global p) p)"
      and fwd_ok:
        "\<And>u a w ctx. (u, ctx) \<in> fst (int_conf_sol_prog_warrow Refine_Fixpoint (declared_global p) p)
           \<Longrightarrow> (u, a, w) \<in> intra (prog_cfg p) \<Longrightarrow> (w, ctx) \<in> fst (int_conf_sol_prog_warrow Refine_Fixpoint (declared_global p) p)"
      and call_fwd_ok:
        "\<And>u ctx dst fs as q k. (u, ctx) \<in> fst (int_conf_sol_prog_warrow Refine_Fixpoint (declared_global p) p)
           \<Longrightarrow> (u, CallEdge dst fs as, FunctionEntry q, k) \<in> calls (prog_cfg p)
           \<Longrightarrow> (FunctionEntry q, ()) \<in> fst (int_conf_sol_prog_warrow Refine_Fixpoint (declared_global p) p)"
      and comb_fwd_ok:
        "\<And>cl c1 dst fs as q k. (cl, c1) \<in> fst (int_conf_sol_prog_warrow Refine_Fixpoint (declared_global p) p)
           \<Longrightarrow> (cl, CallEdge dst fs as, FunctionEntry q, k) \<in> calls (prog_cfg p)
           \<Longrightarrow> (k, c1) \<in> fst (int_conf_sol_prog_warrow Refine_Fixpoint (declared_global p) p)"
      and mem: "(v, c, Check_Proved) \<in> set (analyse Int_Analysis p)"
  shows "\<forall>s \<in> ltr_collect (declared_global p) (prog_cfg p) (cinit_stores (declared_global p)) v.
           truthy (aval c s)"
  by (rule analyse_int_report_sound_proved
        [OF wf solve entry_cov fwd_ok call_fwd_ok comb_fwd_ok mem[unfolded analyse.simps]])

corollary analyse_int_refuted_sound:
  fixes p :: imp_prog and v :: pp and c :: exp
  assumes wf: "wf_compile_input (declared_global p) (prog_table p) (prog_procs p)"
      and solve: "int_conf_terminates_prog_warrow Refine_Fixpoint (declared_global p) p"
      and entry_cov: "(cfg_entry (prog_cfg p), ()) \<in> fst (int_conf_sol_prog_warrow Refine_Fixpoint (declared_global p) p)"
      and fwd_ok:
        "\<And>u a w ctx. (u, ctx) \<in> fst (int_conf_sol_prog_warrow Refine_Fixpoint (declared_global p) p)
           \<Longrightarrow> (u, a, w) \<in> intra (prog_cfg p) \<Longrightarrow> (w, ctx) \<in> fst (int_conf_sol_prog_warrow Refine_Fixpoint (declared_global p) p)"
      and call_fwd_ok:
        "\<And>u ctx dst fs as q k. (u, ctx) \<in> fst (int_conf_sol_prog_warrow Refine_Fixpoint (declared_global p) p)
           \<Longrightarrow> (u, CallEdge dst fs as, FunctionEntry q, k) \<in> calls (prog_cfg p)
           \<Longrightarrow> (FunctionEntry q, ()) \<in> fst (int_conf_sol_prog_warrow Refine_Fixpoint (declared_global p) p)"
      and comb_fwd_ok:
        "\<And>cl c1 dst fs as q k. (cl, c1) \<in> fst (int_conf_sol_prog_warrow Refine_Fixpoint (declared_global p) p)
           \<Longrightarrow> (cl, CallEdge dst fs as, FunctionEntry q, k) \<in> calls (prog_cfg p)
           \<Longrightarrow> (k, c1) \<in> fst (int_conf_sol_prog_warrow Refine_Fixpoint (declared_global p) p)"
      and mem: "(v, c, Check_Refuted) \<in> set (analyse Int_Analysis p)"
  shows "\<forall>s \<in> ltr_collect (declared_global p) (prog_cfg p) (cinit_stores (declared_global p)) v.
           \<not> truthy (aval c s)"
  by (rule analyse_int_report_sound_refuted
        [OF wf solve entry_cov fwd_ok call_fwd_ok comb_fwd_ok mem[unfolded analyse.simps]])

subsection \<open>One statement over the whole pipeline\<close>

text \<open>
  The corollaries above are per domain and carry the four coverage facts one by one.
  \<open>analyse_certified\<close> collapses both: it names, for each selectable domain, the two
  facts about that domain's own solve that nothing here proves in general --- the
  solver run completed, and it solved enough keys --- so a caller states one
  predicate instead of picking the right pair of constants per domain. Both
  conjuncts are decided per program by evaluation: \<^const>\<open>vars_cover\<close> through each
  domain's \<open>vars_cover_exec\<close> bridge, solver success through that domain's
  \<open>..._via_solve_c\<close> reflection.
\<close>

fun analyse_certified :: "analysis_domain \<Rightarrow> imp_prog \<Rightarrow> bool" where
  "analyse_certified Sign_Analysis p =
     (sctx_terminates_prog (declared_global p) p
        \<and> vars_cover (prog_cfg p) (fst (sctx_sol_prog (declared_global p) p)))"
| "analyse_certified Interval_Analysis p =
     (interval_conf_terminates_prog_warrow (declared_global p) p
        \<and> vars_cover (prog_cfg p)
             (fst (interval_conf_sol_prog_warrow (declared_global p) p)))"
| "analyse_certified Int_Analysis p =
     (int_conf_terminates_prog_warrow Refine_Fixpoint (declared_global p) p
        \<and> vars_cover (prog_cfg p)
             (fst (int_conf_sol_prog_warrow Refine_Fixpoint (declared_global p) p)))"
| "analyse_certified Parity_Analysis p =
     (pctx_terminates_prog (declared_global p) p
        \<and> vars_cover (prog_cfg p) (fst (pctx_sol_prog (declared_global p) p)))"

lemma analyse_proved_sound:
  fixes p :: imp_prog and v :: pp and c :: exp
  assumes wf: "wf_compile_input (declared_global p) (prog_table p) (prog_procs p)"
      and cert: "analyse_certified D p"
      and mem: "(v, c, Check_Proved) \<in> set (analyse D p)"
  shows "\<forall>s \<in> ltr_collect (declared_global p) (prog_cfg p) (cinit_stores (declared_global p)) v.
           truthy (aval c s)"
proof (cases D)
  case Sign_Analysis
  with cert have solve: "sctx_terminates_prog (declared_global p) p"
    and cover: "vars_cover (prog_cfg p) (fst (sctx_sol_prog (declared_global p) p))"
    by simp_all
  from mem Sign_Analysis have m: "(v, c, Check_Proved) \<in> set (analyse Sign_Analysis p)" by simp
  show ?thesis
    by (rule analyse_sign_proved_sound[OF wf solve _ _ _ _ m]) (use cover in auto)
next
  case Interval_Analysis
  with cert have solve: "interval_conf_terminates_prog_warrow (declared_global p) p"
    and cover: "vars_cover (prog_cfg p) (fst (interval_conf_sol_prog_warrow (declared_global p) p))"
    by simp_all
  from mem Interval_Analysis have m: "(v, c, Check_Proved) \<in> set (analyse Interval_Analysis p)"
    by simp
  show ?thesis
    by (rule analyse_interval_proved_sound[OF wf solve _ _ _ _ m]) (use cover in auto)
next
  case Int_Analysis
  with cert have solve: "int_conf_terminates_prog_warrow Refine_Fixpoint (declared_global p) p"
    and cover: "vars_cover (prog_cfg p)
                  (fst (int_conf_sol_prog_warrow Refine_Fixpoint (declared_global p) p))"
    by simp_all
  from mem Int_Analysis have m: "(v, c, Check_Proved) \<in> set (analyse Int_Analysis p)" by simp
  show ?thesis
    by (rule analyse_int_proved_sound[OF wf solve _ _ _ _ m]) (use cover in auto)
next
  case Parity_Analysis
  with cert have solve: "pctx_terminates_prog (declared_global p) p"
    and cover: "vars_cover (prog_cfg p) (fst (pctx_sol_prog (declared_global p) p))"
    by simp_all
  from mem Parity_Analysis have m: "(v, c, Check_Proved) \<in> set (analyse_parity_report p)" by simp
  show ?thesis
    by (rule analyse_parity_report_sound_proved[OF wf solve _ _ _ _ m]) (use cover in auto)
qed

lemma analyse_refuted_sound:
  fixes p :: imp_prog and v :: pp and c :: exp
  assumes wf: "wf_compile_input (declared_global p) (prog_table p) (prog_procs p)"
      and cert: "analyse_certified D p"
      and mem: "(v, c, Check_Refuted) \<in> set (analyse D p)"
  shows "\<forall>s \<in> ltr_collect (declared_global p) (prog_cfg p) (cinit_stores (declared_global p)) v.
           \<not> truthy (aval c s)"
proof (cases D)
  case Sign_Analysis
  with cert have solve: "sctx_terminates_prog (declared_global p) p"
    and cover: "vars_cover (prog_cfg p) (fst (sctx_sol_prog (declared_global p) p))"
    by simp_all
  from mem Sign_Analysis have m: "(v, c, Check_Refuted) \<in> set (analyse Sign_Analysis p)" by simp
  show ?thesis
    by (rule analyse_sign_refuted_sound[OF wf solve _ _ _ _ m]) (use cover in auto)
next
  case Interval_Analysis
  with cert have solve: "interval_conf_terminates_prog_warrow (declared_global p) p"
    and cover: "vars_cover (prog_cfg p) (fst (interval_conf_sol_prog_warrow (declared_global p) p))"
    by simp_all
  from mem Interval_Analysis have m: "(v, c, Check_Refuted) \<in> set (analyse Interval_Analysis p)"
    by simp
  show ?thesis
    by (rule analyse_interval_refuted_sound[OF wf solve _ _ _ _ m]) (use cover in auto)
next
  case Int_Analysis
  with cert have solve: "int_conf_terminates_prog_warrow Refine_Fixpoint (declared_global p) p"
    and cover: "vars_cover (prog_cfg p)
                  (fst (int_conf_sol_prog_warrow Refine_Fixpoint (declared_global p) p))"
    by simp_all
  from mem Int_Analysis have m: "(v, c, Check_Refuted) \<in> set (analyse Int_Analysis p)" by simp
  show ?thesis
    by (rule analyse_int_refuted_sound[OF wf solve _ _ _ _ m]) (use cover in auto)
next
  case Parity_Analysis
  with cert have solve: "pctx_terminates_prog (declared_global p) p"
    and cover: "vars_cover (prog_cfg p) (fst (pctx_sol_prog (declared_global p) p))"
    by simp_all
  from mem Parity_Analysis have m: "(v, c, Check_Refuted) \<in> set (analyse_parity_report p)" by simp
  show ?thesis
    by (rule analyse_parity_report_sound_refuted[OF wf solve _ _ _ _ m]) (use cover in auto)
qed

text \<open>
  The pipeline statement: compile the source program, generate its equations, solve
  them, read the report --- and then run the source program itself and stop wherever
  you like. The store in your hands sits at some graph node, and every verdict the
  report printed for that node holds of it: a \<^const>\<open>Check_Proved\<close> condition is
  true there, a \<^const>\<open>Check_Refuted\<close> one false. \<^const>\<open>csim\<close> is what names the
  node --- a partly executed command together with its frame stack sits at one ---
  so no separate reachability argument connects the run to the report.

  Everything domain-specific has been absorbed: \<open>D\<close> ranges over every selectable
  analysis, and the premises left are well-formed input, an initial store, and
  \<^const>\<open>analyse_certified\<close>. It is stated over \<^const>\<open>analyse\<close>, the constant
  \<open>export_code\<close> exports, so it constrains the analyzer's own output rather than an
  internal solved system.
\<close>

theorem analyse_source_sound:
  fixes p :: imp_prog and s0 s :: store
  assumes wf: "wf_compile_input (declared_global p) (prog_table p) (prog_procs p)"
      and cert: "analyse_certified D p"
      and s0: "s0 \<in> cinit_stores (declared_global p)"
      and run: "star (pstep (declared_global p) (prog_table p))
                  (main_body (prog_table p), s0, []) (residual, s, frs)"
  shows "\<exists>v stk. csim (prog_table p) (prog_cfg p) (residual, s, frs) (v, s, stk)
                 \<and> (\<forall>c. (v, c, Check_Proved) \<in> set (analyse D p) \<longrightarrow> truthy (aval c s))
                 \<and> (\<forall>c. (v, c, Check_Refuted) \<in> set (analyse D p) \<longrightarrow> \<not> truthy (aval c s))"
proof -
  have cfg: "prog_cfg p = compile_prog (prog_table p) (prog_procs p)"
    by (rule prog_cfg_def)
  from source_reaches_ltr_collect[OF wf s0 run]
  obtain v stk where m: "csim (prog_table p) (prog_cfg p) (residual, s, frs) (v, s, stk)"
    and mem: "s \<in> ltr_collect (declared_global p) (prog_cfg p)
                     (cinit_stores (declared_global p)) v"
    unfolding cfg by blast
  show ?thesis
    using m mem analyse_proved_sound[OF wf cert] analyse_refuted_sound[OF wf cert] by blast
qed

subsection \<open>Executable code generation\<close>

text \<open>
  \<open>analyse\<close> genuinely takes the domain choice and the program as runtime
  arguments, not constants baked in at export time. The raw AST constructors,
  \<open>imp_prog.make\<close>, and \<open>proc_decl_ext\<close> are exported alongside it so external
  OCaml code can build a fresh \<open>imp_prog\<close> and hand it to \<open>analyse\<close>.

  \<^typ>\<open>vname\<close>/\<^typ>\<open>pname\<close> are \<^typ>\<open>String.literal\<close>
  (\<^theory>\<open>Voblint_VIMP.VIMP_Syntax\<close>/\<^theory>\<open>Voblint_VIMP.VIMP_Globals\<close>), already
  the target language's native string (\<^verbatim>\<open>string\<close> in OCaml
  --- \<^theory>\<open>HOL.String\<close> ships that mapping
  unconditionally), so \<open>V\<close>/\<open>Assign\<close>/\<open>com.Call\<close>/\<open>FunctionEntry\<close>/
  \<open>FunctionResult\<close>/\<open>proc_decl_ext\<close>/\<open>imp_prog.make\<close> below already take and
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
  \<open>integer_of_char\<close> is that bridge; only the inspecting direction is exported,
  since nothing handwritten builds a \<open>char\<close> from an integer.

  \<open>string_of_exp\<close> is exported alongside the structured \<open>exp\<close> already in
  every \<open>check_report_entry\<close>: a consumer can pattern-match the AST directly,
  or call \<open>string_of_exp\<close> to render a check's condition as a native string
  without decoding it --- both stay available, not a replacement report type.
\<close>

section \<open>Config-driven dispatch\<close>

text \<open>
  \<^const>\<open>analyse\<close>/\<^const>\<open>analyse_with_solver\<close>/
  \<^const>\<open>analyse_with_state\<close> above each decide legality over exactly two of
  \<^type>\<open>analysis_config\<close>'s three axes at a time (domain+solver, ...) and stay
  the lower-level, typed entry points every consumer keeps using. \<^const>\<open>resolve_analysis_config\<close> (\<^theory>\<open>Voblint_Analysis_Base.Analysis_Config\<close>)
  is the one place all three axes' legality and defaults are decided
  together; the three wrappers below each consume its \<^type>\<open>analysis_plan\<close>
  result and pick the one existing dispatcher call that already produces
  their report shape, rather than re-deciding legality or re-implementing
  a domain/solver/context case split of their own. None of the three
  existing report shapes below is replaced by a fourth, artificially
  unified one: \<open>check_report_entry list\<close>, \<open>(pp \<times> exp \<times> contextual_verdict)
  list\<close>, and the \<^typ>\<open>abstract_value abs_state\<close>-carrying report genuinely
  differ, and forcing one shape on all three would either lose the
  \<^const>\<open>Dead\<close> distinction the contextual report exists for, or fabricate a
  per-variable state no flat report has ever carried.
\<close>

definition analyse_config :: "analysis_config \<Rightarrow> imp_prog \<Rightarrow> check_report_entry list option" where
  "analyse_config cfg p =
     (case resolve_analysis_config cfg of
        None \<Rightarrow> None
      | Some (Plan_Sign s) \<Rightarrow> analyse_with_solver Sign_Analysis s p
      | Some (Plan_Interval s) \<Rightarrow> analyse_with_solver Interval_Analysis s p
      | Some (Plan_Int s) \<Rightarrow> analyse_with_solver Int_Analysis s p
      | Some (Plan_Interval_EntryState _) \<Rightarrow> None
      | Some (Plan_Sign_EntryState _) \<Rightarrow> None
      | Some (Plan_Interval_CallString _ _) \<Rightarrow> None
      | Some (Plan_Sign_CallString _ _) \<Rightarrow> None
      | Some (Plan_Int_CallString _ _) \<Rightarrow> None
      | Some (Plan_Int_EntryState _) \<Rightarrow> None
      | Some (Plan_Parity s) \<Rightarrow> analyse_with_solver Parity_Analysis s p)"

text \<open>
  \<open>Plan_Interval_EntryState\<close> answers \<^const>\<open>None\<close> here on purpose: entry-state
  analysis has no flat, context-free \<open>check_report_entry list\<close> in the first
  place (a check can be \<^const>\<open>Dead\<close> in one context and decided in another,
  which \<^typ>\<open>check_result\<close> alone cannot express) -- \<open>analyse_config_ctx\<close>
  below is the wrapper a caller with an \<^type>\<open>analysis_plan\<close> resolving there
  should use instead, not a degraded flat view of the same result.
\<close>

definition analyse_config_ctx ::
    "analysis_config \<Rightarrow> imp_prog \<Rightarrow> (pp \<times> exp \<times> contextual_verdict) list option" where
  "analyse_config_ctx cfg p =
     (case resolve_analysis_config cfg of
        None \<Rightarrow> None
      | Some (Plan_Interval_EntryState Solver_Warrow) \<Rightarrow> Some (analyse_interval_entry_state p)
      | Some (Plan_Interval_EntryState Solver_Join) \<Rightarrow> Some (analyse_interval_entry_state_join p)
      | Some (Plan_Interval_EntryState Solver_PerOrigin) \<Rightarrow> Some (analyse_interval_entry_state_per_origin p)
      | Some (Plan_Interval_CallString Solver_Warrow k) \<Rightarrow> Some (analyse_interval_call_string_report k p)
      | Some (Plan_Interval_CallString Solver_Join k) \<Rightarrow> Some (analyse_interval_call_string_report_join k p)
      | Some (Plan_Interval_CallString Solver_PerOrigin k) \<Rightarrow> Some (analyse_interval_call_string_report_per_origin k p)
      | Some (Plan_Interval_EntryState Solver_WarrowPerOrigin) \<Rightarrow> Some (analyse_interval_entry_state_wpo p)
      | Some (Plan_Interval_CallString Solver_WarrowPerOrigin k) \<Rightarrow> Some (analyse_interval_call_string_report_wpo k p)
      | Some (Plan_Sign_CallString Solver_Join k) \<Rightarrow> Some (analyse_sign_call_string_report k p)
      | Some (Plan_Sign_CallString Solver_PerOrigin _) \<Rightarrow> None
      | Some (Plan_Sign_CallString Solver_Warrow _) \<Rightarrow> None
      | Some (Plan_Sign_CallString Solver_WarrowPerOrigin _) \<Rightarrow> None
      | Some (Plan_Sign_EntryState Solver_Join) \<Rightarrow> Some (analyse_sign_entry_state_report p)
      | Some (Plan_Sign_EntryState Solver_PerOrigin) \<Rightarrow> None
      | Some (Plan_Sign_EntryState Solver_Warrow) \<Rightarrow> None
      | Some (Plan_Sign_EntryState Solver_WarrowPerOrigin) \<Rightarrow> None
      | Some (Plan_Int_CallString Solver_Join k) \<Rightarrow> Some (analyse_int_call_string_report k p)
      | Some (Plan_Int_CallString Solver_PerOrigin _) \<Rightarrow> None
      | Some (Plan_Int_CallString Solver_Warrow k) \<Rightarrow> Some (analyse_int_call_string_report_warrow k p)
      | Some (Plan_Int_CallString Solver_WarrowPerOrigin _) \<Rightarrow> None
      | Some (Plan_Int_EntryState Solver_Join) \<Rightarrow> Some (analyse_int_entry_state_report p)
      | Some (Plan_Int_EntryState Solver_PerOrigin) \<Rightarrow> None
      | Some (Plan_Int_EntryState Solver_Warrow) \<Rightarrow> Some (analyse_int_entry_state_report_warrow p)
      | Some (Plan_Int_EntryState Solver_WarrowPerOrigin) \<Rightarrow> None
      | Some (Plan_Sign s) \<Rightarrow> map_option decided_report (analyse_with_solver Sign_Analysis s p)
      | Some (Plan_Interval s) \<Rightarrow> map_option decided_report (analyse_with_solver Interval_Analysis s p)
      | Some (Plan_Int s) \<Rightarrow> map_option decided_report (analyse_with_solver Int_Analysis s p)
      | Some (Plan_Parity s) \<Rightarrow> map_option decided_report (analyse_with_solver Parity_Analysis s p))"

text \<open>
  \<^const>\<open>analyse_with_state\<close> decides legality over the domain and solver axes
  only, so this wrapper is \<^const>\<open>Some\<close> at every context-free plan whose pairing
  has a solved table -- the implicit default and every explicit solver alike -- and
  \<^const>\<open>None\<close> at every context plan: a \<open>Ctx_EntryState\<close>/\<open>Ctx_CallString\<close>
  selection has a contextual report (\<open>analyse_config_ctx\<close>), not a flat
  state-carrying one, and is not silently degraded to it.
\<close>

fun analyse_config_with_state ::
    "analysis_config \<Rightarrow> imp_prog \<Rightarrow> (pp \<times> exp \<times> check_result \<times> bool \<times> abstract_value abs_state) list option"
where
  "analyse_config_with_state cfg p =
     (case resolve_analysis_config cfg of
        Some (Plan_Sign s) \<Rightarrow> analyse_with_state Sign_Analysis s p
      | Some (Plan_Interval s) \<Rightarrow> analyse_with_state Interval_Analysis s p
      | Some (Plan_Int s) \<Rightarrow> analyse_with_state Int_Analysis s p
      | Some (Plan_Parity s) \<Rightarrow> analyse_with_state Parity_Analysis s p
      | _ \<Rightarrow> None)"

subsection \<open>Config-driven dispatch agrees with each existing typed entry point\<close>

text \<open>
  The regression pattern \<open>new_dispatch cfg p = old_entry_point p\<close> at every
  currently-public configuration: config-driven dispatch is a routing
  layer over the untouched existing dispatchers, never a reimplementation
  that could silently drift from what the CLI already exercises.
\<close>

lemma analyse_config_sign_default:
  "analyse_config (default_config Sign_Analysis Ctx_None) p = Some (analyse Sign_Analysis p)"
  by (simp add: analyse_config_def default_config_def mk_analysis_config_def)

lemma analyse_config_interval_default:
  "analyse_config (default_config Interval_Analysis Ctx_None) p = Some (analyse Interval_Analysis p)"
  by (simp add: analyse_config_def default_config_def mk_analysis_config_def)

lemma analyse_config_int_default:
  "analyse_config (default_config Int_Analysis Ctx_None) p = Some (analyse Int_Analysis p)"
  by (simp add: analyse_config_def default_config_def mk_analysis_config_def)

lemma analyse_config_ctx_interval_entrystate:
  "analyse_config_ctx (default_config Interval_Analysis Ctx_EntryState) p
     = Some (analyse_interval_entry_state p)"
  by (simp add: analyse_config_ctx_def default_config_def mk_analysis_config_def)

text \<open>
  An explicit solver alongside \<open>Ctx_EntryState\<close> is a valid, routed selection:
  the routed equation system underneath is exactly as solver-independent as
  the flat one.
\<close>

lemma analyse_config_ctx_interval_entrystate_explicit_join_valid:
  "analyse_config_ctx \<lparr> cfg_domain = Interval_Analysis, cfg_solver = Some Solver_Join, cfg_context = Ctx_EntryState \<rparr> p
     = Some (analyse_interval_entry_state_join p)"
  by (simp add: analyse_config_ctx_def)

lemma analyse_config_ctx_interval_entrystate_explicit_per_origin_valid:
  "analyse_config_ctx \<lparr> cfg_domain = Interval_Analysis, cfg_solver = Some Solver_PerOrigin, cfg_context = Ctx_EntryState \<rparr> p
     = Some (analyse_interval_entry_state_per_origin p)"
  by (simp add: analyse_config_ctx_def)

lemma analyse_config_ctx_interval_entrystate_explicit_warrow_valid:
  "analyse_config_ctx \<lparr> cfg_domain = Interval_Analysis, cfg_solver = Some Solver_Warrow, cfg_context = Ctx_EntryState \<rparr> p
     = Some (analyse_interval_entry_state p)"
  by (simp add: analyse_config_ctx_def)

text \<open>
  The fourth discipline is pinned at both contexts because the resolver already
  accepts it there: a plan the resolver produces but this dispatcher does not
  match is a code-generated match failure, not a rejected configuration.
\<close>

lemma analyse_config_ctx_interval_entrystate_explicit_wpo_valid:
  "analyse_config_ctx \<lparr> cfg_domain = Interval_Analysis, cfg_solver = Some Solver_WarrowPerOrigin, cfg_context = Ctx_EntryState \<rparr> p
     = Some (analyse_interval_entry_state_wpo p)"
  by (simp add: analyse_config_ctx_def)

lemma analyse_config_ctx_interval_callstring_explicit_wpo_valid:
  "analyse_config_ctx \<lparr> cfg_domain = Interval_Analysis, cfg_solver = Some Solver_WarrowPerOrigin, cfg_context = Ctx_CallString (Suc k) \<rparr> p
     = Some (analyse_interval_call_string_report_wpo (Suc k) p)"
  by (simp add: analyse_config_ctx_def)

text \<open>
  Sign at \<open>Ctx_EntryState\<close>, pinned the same way \<open>Ctx_CallString\<close>'s own regressions are:
  valid at the implicit-default and explicit \<open>Solver_Join\<close> selections, invalid at the
  two solvers Sign's entry-state soundness does not prove.
\<close>

lemma analyse_config_ctx_sign_entrystate_default_valid:
  "analyse_config_ctx (default_config Sign_Analysis Ctx_EntryState) p
     = Some (analyse_sign_entry_state_report p)"
  by (simp add: analyse_config_ctx_def default_config_def mk_analysis_config_def)

lemma analyse_config_ctx_sign_entrystate_explicit_join_valid:
  "analyse_config_ctx
     \<lparr> cfg_domain = Sign_Analysis, cfg_solver = Some Solver_Join, cfg_context = Ctx_EntryState \<rparr> p
   = Some (analyse_sign_entry_state_report p)"
  by (simp add: analyse_config_ctx_def)

lemma analyse_config_ctx_sign_entrystate_per_origin_invalid:
  "analyse_config_ctx
     \<lparr> cfg_domain = Sign_Analysis, cfg_solver = Some Solver_PerOrigin, cfg_context = Ctx_EntryState \<rparr> p
   = None"
  by (simp add: analyse_config_ctx_def)

lemma analyse_config_ctx_sign_entrystate_warrow_invalid:
  "analyse_config_ctx
     \<lparr> cfg_domain = Sign_Analysis, cfg_solver = Some Solver_Warrow, cfg_context = Ctx_EntryState \<rparr> p
   = None"
  by (simp add: analyse_config_ctx_def)

text \<open>
  Parity, the fourth domain, on the config-driven path: supported at \<open>Ctx_None\<close> under the
  two solvers it has tables for, and genuinely \<^const>\<open>None\<close> at the contexts it has no
  routed instance for -- the config resolver decides both, with no CLI-side table.
\<close>

lemma analyse_config_parity_default:
  "analyse_config (default_config Parity_Analysis Ctx_None) p = Some (analyse Parity_Analysis p)"
  by (simp add: analyse_config_def default_config_def mk_analysis_config_def)

lemma analyse_config_parity_per_origin_valid:
  "analyse_config
     \<lparr> cfg_domain = Parity_Analysis, cfg_solver = Some Solver_PerOrigin, cfg_context = Ctx_None \<rparr> p
   = Some (analyse_parity_report_per_origin p)"
  by (simp add: analyse_config_def)

lemma analyse_config_parity_warrow_invalid:
  "analyse_config
     \<lparr> cfg_domain = Parity_Analysis, cfg_solver = Some Solver_Warrow, cfg_context = Ctx_None \<rparr> p
   = None"
  by (simp add: analyse_config_def)

lemma analyse_config_ctx_parity_entrystate_invalid:
  "analyse_config_ctx (default_config Parity_Analysis Ctx_EntryState) p = None"
  by (simp add: analyse_config_ctx_def default_config_def mk_analysis_config_def)

lemma analyse_config_ctx_parity_callstring_invalid:
  "analyse_config_ctx (default_config Parity_Analysis (Ctx_CallString k)) p = None"
  by (simp add: analyse_config_ctx_def default_config_def mk_analysis_config_def)

text \<open>
  Int at \<open>Ctx_EntryState\<close>: the implicit default routes to the warrowing report, the
  explicit \<open>Solver_Warrow\<close>/\<open>Solver_Join\<close> selections to theirs, and the two solvers
  Int's own entry-state soundness does not certify stay invalid.
\<close>

lemma analyse_config_ctx_int_entrystate_default_valid:
  "analyse_config_ctx (default_config Int_Analysis Ctx_EntryState) p
     = Some (analyse_int_entry_state_report_warrow p)"
  by (simp add: analyse_config_ctx_def default_config_def mk_analysis_config_def)

lemma analyse_config_ctx_int_entrystate_explicit_join_valid:
  "analyse_config_ctx
     \<lparr> cfg_domain = Int_Analysis, cfg_solver = Some Solver_Join, cfg_context = Ctx_EntryState \<rparr> p
   = Some (analyse_int_entry_state_report p)"
  by (simp add: analyse_config_ctx_def)

lemma analyse_config_ctx_int_entrystate_per_origin_invalid:
  "analyse_config_ctx
     \<lparr> cfg_domain = Int_Analysis, cfg_solver = Some Solver_PerOrigin, cfg_context = Ctx_EntryState \<rparr> p
   = None"
  by (simp add: analyse_config_ctx_def)

lemma analyse_config_ctx_int_entrystate_warrow_valid:
  "analyse_config_ctx
     \<lparr> cfg_domain = Int_Analysis, cfg_solver = Some Solver_Warrow, cfg_context = Ctx_EntryState \<rparr> p
   = Some (analyse_int_entry_state_report_warrow p)"
  by (simp add: analyse_config_ctx_def)

text \<open>
  Call-string: \<open>analyse_config_ctx\<close> at \<open>Ctx_CallString k\<close> is exactly
  \<^const>\<open>analyse_interval_call_string_report\<close> \<open>k\<close> -- the one generic,
  runtime-\<open>k\<close> pipeline, reachable through the public configuration path with
  no second implementation in between.
\<close>

lemma analyse_config_ctx_interval_callstring_eq_report:
  assumes "k \<noteq> 0"
  shows "analyse_config_ctx (default_config Interval_Analysis (Ctx_CallString k)) p
           = Some (analyse_interval_call_string_report k p)"
  using assms by (simp add: analyse_config_ctx_def default_config_def mk_analysis_config_def)

lemma analyse_config_ctx_interval_callstring_zero_invalid:
  "analyse_config_ctx (default_config Interval_Analysis (Ctx_CallString 0)) p = None"
  by (simp add: analyse_config_ctx_def default_config_def mk_analysis_config_def)

text \<open>
  An explicit solver alongside \<open>Ctx_CallString k\<close> (\<open>k \<ge> 1\<close>) is likewise a
  valid, routed selection now, mirroring \<open>Ctx_EntryState\<close>'s generalization
  above.
\<close>

lemma analyse_config_ctx_interval_callstring_explicit_warrow_valid:
  assumes "k \<noteq> 0"
  shows "analyse_config_ctx
           \<lparr> cfg_domain = Interval_Analysis, cfg_solver = Some Solver_Warrow, cfg_context = Ctx_CallString k \<rparr> p
         = Some (analyse_interval_call_string_report k p)"
  using assms by (simp add: analyse_config_ctx_def)

lemma analyse_config_ctx_interval_callstring_explicit_join_valid:
  assumes "k \<noteq> 0"
  shows "analyse_config_ctx
           \<lparr> cfg_domain = Interval_Analysis, cfg_solver = Some Solver_Join, cfg_context = Ctx_CallString k \<rparr> p
         = Some (analyse_interval_call_string_report_join k p)"
  using assms by (simp add: analyse_config_ctx_def)

lemma analyse_config_ctx_interval_callstring_explicit_per_origin_valid:
  assumes "k \<noteq> 0"
  shows "analyse_config_ctx
           \<lparr> cfg_domain = Interval_Analysis, cfg_solver = Some Solver_PerOrigin, cfg_context = Ctx_CallString k \<rparr> p
         = Some (analyse_interval_call_string_report_per_origin k p)"
  using assms by (simp add: analyse_config_ctx_def)

lemma analyse_config_ctx_interval_callstring_zero_explicit_solver_invalid:
  "analyse_config_ctx
     \<lparr> cfg_domain = Interval_Analysis, cfg_solver = Some Solver_Warrow, cfg_context = Ctx_CallString 0 \<rparr> p
   = None"
  by (simp add: analyse_config_ctx_def)

text \<open>
  Sign at \<open>Ctx_CallString\<close>, pinned the same way \<open>Analysis_Config\<close>'s own
  resolver regressions are: valid at \<open>k \<ge> 1\<close> under the implicit-default and
  explicit \<open>Solver_Join\<close> selections, invalid at \<open>k = 0\<close> and at the two
  solvers Sign's call-string soundness does not prove.
\<close>

lemma analyse_config_ctx_sign_callstring_k1_valid:
  "analyse_config_ctx (default_config Sign_Analysis (Ctx_CallString 1)) p
     = Some (analyse_sign_call_string_report 1 p)"
  by (simp add: analyse_config_ctx_def default_config_def mk_analysis_config_def)

lemma analyse_config_ctx_sign_callstring_k2_valid:
  "analyse_config_ctx (default_config Sign_Analysis (Ctx_CallString 2)) p
     = Some (analyse_sign_call_string_report 2 p)"
  by (simp add: analyse_config_ctx_def default_config_def mk_analysis_config_def)

lemma analyse_config_ctx_sign_callstring_zero_invalid:
  "analyse_config_ctx (default_config Sign_Analysis (Ctx_CallString 0)) p = None"
  by (simp add: analyse_config_ctx_def default_config_def mk_analysis_config_def)

lemma analyse_config_ctx_sign_callstring_explicit_join_valid:
  "analyse_config_ctx
     \<lparr> cfg_domain = Sign_Analysis, cfg_solver = Some Solver_Join, cfg_context = Ctx_CallString 2 \<rparr> p
   = Some (analyse_sign_call_string_report 2 p)"
  by (simp add: analyse_config_ctx_def)

lemma analyse_config_ctx_sign_callstring_per_origin_invalid:
  "analyse_config_ctx
     \<lparr> cfg_domain = Sign_Analysis, cfg_solver = Some Solver_PerOrigin, cfg_context = Ctx_CallString 2 \<rparr> p
   = None"
  by (simp add: analyse_config_ctx_def)

lemma analyse_config_ctx_sign_callstring_warrow_invalid:
  "analyse_config_ctx
     \<lparr> cfg_domain = Sign_Analysis, cfg_solver = Some Solver_Warrow, cfg_context = Ctx_CallString 2 \<rparr> p
   = None"
  by (simp add: analyse_config_ctx_def)

text \<open>
  Int at \<open>Ctx_CallString\<close>: valid at \<open>k \<ge> 1\<close> under the implicit default (the warrowing
  report) and the explicit \<open>Solver_Warrow\<close>/\<open>Solver_Join\<close> selections, invalid at \<open>k = 0\<close>
  and at the two solvers Int's own call-string soundness does not certify.
\<close>

lemma analyse_config_ctx_int_callstring_k1_valid:
  "analyse_config_ctx (default_config Int_Analysis (Ctx_CallString 1)) p
     = Some (analyse_int_call_string_report_warrow 1 p)"
  by (simp add: analyse_config_ctx_def default_config_def mk_analysis_config_def)

lemma analyse_config_ctx_int_callstring_k2_valid:
  "analyse_config_ctx (default_config Int_Analysis (Ctx_CallString 2)) p
     = Some (analyse_int_call_string_report_warrow 2 p)"
  by (simp add: analyse_config_ctx_def default_config_def mk_analysis_config_def)

lemma analyse_config_ctx_int_callstring_zero_invalid:
  "analyse_config_ctx (default_config Int_Analysis (Ctx_CallString 0)) p = None"
  by (simp add: analyse_config_ctx_def default_config_def mk_analysis_config_def)

lemma analyse_config_ctx_int_callstring_explicit_join_valid:
  "analyse_config_ctx
     \<lparr> cfg_domain = Int_Analysis, cfg_solver = Some Solver_Join, cfg_context = Ctx_CallString 2 \<rparr> p
   = Some (analyse_int_call_string_report 2 p)"
  by (simp add: analyse_config_ctx_def)

lemma analyse_config_ctx_int_callstring_per_origin_invalid:
  "analyse_config_ctx
     \<lparr> cfg_domain = Int_Analysis, cfg_solver = Some Solver_PerOrigin, cfg_context = Ctx_CallString 2 \<rparr> p
   = None"
  by (simp add: analyse_config_ctx_def)

lemma analyse_config_ctx_int_callstring_warrow_valid:
  "analyse_config_ctx
     \<lparr> cfg_domain = Int_Analysis, cfg_solver = Some Solver_Warrow, cfg_context = Ctx_CallString 2 \<rparr> p
   = Some (analyse_int_call_string_report_warrow 2 p)"
  by (simp add: analyse_config_ctx_def)

subsubsection \<open>Dispatcher-path parity with the direct generic CallString core\<close>

text \<open>
  The public path (through \<^const>\<open>resolve_analysis_config\<close> and
  \<^const>\<open>analyse_config_ctx\<close>) reaches the identical values the CS1--CS3
  parity theory (\<open>Example_Interval_Call_String_Generic_Parity\<close>)
  already pinned against the fixed \<open>k=1\<close>/\<open>k=2\<close> examples -- restated here as
  a report-level, not a solved-state-level, witness: the dispatcher does not
  reimplement or re-derive anything, it only routes.
\<close>

lemma analyse_config_ctx_interval_callstring_k1_reaches_generic_core:
  "analyse_config_ctx (default_config Interval_Analysis (Ctx_CallString 1)) p
     = Some (cs_call_string_verdict_report_prog 1 p)"
  by (simp add: analyse_config_ctx_def default_config_def mk_analysis_config_def
                analyse_interval_call_string_report_def)

lemma analyse_config_ctx_interval_callstring_k2_reaches_generic_core:
  "analyse_config_ctx (default_config Interval_Analysis (Ctx_CallString 2)) p
     = Some (cs_call_string_verdict_report_prog 2 p)"
  by (simp add: analyse_config_ctx_def default_config_def mk_analysis_config_def
                analyse_interval_call_string_report_def)

lemma analyse_config_with_state_sign_default:
  "analyse_config_with_state (default_config Sign_Analysis Ctx_None) p
     = Some (tag_states SignValue (analyse_sign_report_with_state p))"
  by (simp add: default_config_def mk_analysis_config_def)

lemma analyse_config_with_state_interval_default:
  "analyse_config_with_state (default_config Interval_Analysis Ctx_None) p
     = Some (tag_states IntervalValue (analyse_interval_td_report_with_state p))"
  by (simp add: default_config_def mk_analysis_config_def)

lemma analyse_config_with_state_int_default:
  "analyse_config_with_state (default_config Int_Analysis Ctx_None) p
     = Some (tag_states IntDomValue (analyse_int_report_with_state p))"
  by (simp add: default_config_def mk_analysis_config_def)

text \<open>
  An explicit solver at \<open>Ctx_None\<close> now answers with a state-carrying report of its
  own table, and a context selection still does not: the flat
  \<^const>\<open>analyse_config\<close> stays the only report shape for those callers that want
  one, never a degraded view of the contextual result.
\<close>

lemma analyse_config_with_state_interval_explicit_join:
  "analyse_config_with_state
     \<lparr> cfg_domain = Interval_Analysis, cfg_solver = Some Solver_Join, cfg_context = Ctx_None \<rparr> p
   = Some (tag_states IntervalValue (interval_join.report_with_state p))"
  by simp

lemma analyse_config_with_state_entrystate_none:
  "analyse_config_with_state (default_config Interval_Analysis Ctx_EntryState) p = None"
  by (simp add: default_config_def mk_analysis_config_def)



text \<open>
  \<open>Some Solver_Warrow\<close> alongside \<open>Ctx_EntryState\<close> is the case this migration
  is most likely to accidentally make valid: \<open>Solver_Warrow\<close> is the exact
  solver entry-state analysis already uses internally, so a resolver bug
  that special-cased "does the explicit solver already match the implicit
  one" would silently start accepting a combination the CLI has always
  rejected. Pinned above at the \<^const>\<open>resolve_analysis_config\<close> level, in
  \<open>Analysis_Config\<close>'s own resolver regressions, and again here through the
  wrapper actually reachable from the CLI.
\<close>

end
