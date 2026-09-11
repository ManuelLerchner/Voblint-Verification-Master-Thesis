theory Analyse_Dispatch
  imports
    Dispatch_Carrier
    "Voblint_CLI.Dispatch_Tables"
    "Voblint_CLI.Config_Tables"
    Voblint_Analysis_Sign.Sign_Entry
    Voblint_Analysis_Interval.Interval_Entry
    Voblint_Analysis_Int.Int_Entry
    Voblint_Analysis_Parity.Parity_Entry
    Voblint_Analysis_Interval.Interval_Analyses
    Voblint_Analysis_Interval.Interval_Solver_Analyses
    Voblint_Analysis_Sign.Sign_Analyses
    Voblint_Analysis_Int.Int_Analyses
    Voblint_Analysis_Congruence.Congruence_Analyses
    Voblint_Analysis_Parity.Parity_Analyses
    Analysis_Config
    "HOL-Library.Code_Target_Numeral"
    "HOL-Library.Code_Abstract_Char"
begin

hide_const phase.N

section \<open>A unified, verified check-report API across domains\<close>

text \<open>
  \<open>analyse_sign_report\<close> (\<^theory>\<open>Voblint_Analysis_Sign.Sign_Entry\<close>) and
  \<open>analyse_interval_report_for\<close>/\<open>analyse_interval_report\<close>
  (\<^theory>\<open>Voblint_Analysis_Interval.Interval_Checks\<close>) already share one observable
  result type, \<open>check_report_entry list\<close>
  (\<^theory>\<open>Voblint_Framework.Abstract_Checks\<close>), even though the two domains'
  internal abstract states (\<open>sign abs_state\<close> vs \<open>ivl abs_state\<close>) genuinely
  differ. \<open>analyse\<close> below is therefore a thin dispatcher, not a new proof:
  each branch reuses the domain's own already-generic, already-sound report
  function unchanged.

  The \<open>Interval_Analysis\<close> branch dispatches to \<open>analyse_interval_report\<close>, the
  widening/warrowing-backed report, not the always-join \<open>analyse_interval_report_join\<close>: Interval's
  local carrier has infinite height (an unbounded integer bound), so a genuine loop that grows a
  local or global value without bound still needs widening for termination, warrowing's own
  guarantee, unlike plain join. All three reports (\<open>analyse_interval_report\<close>,
  \<open>analyse_interval_report_join\<close>, \<open>analyse_interval_report_per_origin\<close>) read through the routed
  D/G spine (\<^theory>\<open>Voblint_Analysis_Interval.Interval_Analyses\<close>): VIMP globals live in a
  keyed seed slot rather than a separate flow-insensitive summary, so \<open>Solver_Join\<close>'s own hazard
  is purely a loop-termination question now, not a global-specific one: a program whose global
  writes never occur inside a loop terminates identically under \<open>Solver_Join\<close> and
  \<open>Solver_Warrow\<close>, only a genuine unbounded loop still needs warrowing.
  \<open>analyse_interval_report\<close>'s soundness theorems
  (\<^theory>\<open>Voblint_Analysis_Interval.Interval_Entry\<close>'s
  \<open>analyse_interval_report_sound_proved\<close>/\<open>_refuted\<close>, obtained from the shared
  assembly's own \<open>report_proved_sound_closure\<close>) make dispatching Interval's production default to the
  warrowing report a like-for-like swap for callers, not a precision or soundness downgrade.
\<close>

subsection \<open>Context-sensitivity dimension\<close>

text \<open>
  \<open>Ctx_None\<close> is today's flow-insensitive, call-site-insensitive behaviour;
  \<open>Ctx_EntryState\<close> selects the value-derived entry-state context analysis
  (\<^theory>\<open>Voblint_Analysis_Interval.Interval_Analyses\<close>, #108). Deliberately not
  a wider \<open>analyse\<close>: \<open>analyse\<close>/\<open>analyse_with_state\<close> stay untouched (the CLI's
  no-\<open>--context\<close> path, the GraphViz report, and every existing
  \<open>codegen/regression\<close> consumer already pin their exact two-argument shape as a
  trust boundary). \<open>analyse_config_ctx\<close> (\<open>Dispatch_Config\<close>) is the entry point for this
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
  A VIMP global lives in the same reachability-lifted local unknown as any local.
  Solver choice is therefore independent of variable ownership: any node the D/G solver
  revisits without a bounding narrowing phase --- a genuine loop, or a call site
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

subsection \<open>Domain-neutral state-carrying report\<close>

text \<open>
  \<open>abstract_value\<close> wraps each domain's own abstract state type once, so
  \<open>analyse_with_state\<close> can share one report type across branches the same
  way \<open>analyse\<close> already shares \<open>check_result\<close>. \<open>analyse\<close> itself stays
  untouched: external callers (the CLI design, this theory's own
  \<open>codegen/regression\<close> drivers) already pin its \<open>check_report_entry
  list\<close> shape as a trust boundary, so this is an additional export, not a
  replacement. Each branch reuses \<open>analyse_sign_report_with_state\<close>/
  \<open>analyse_interval_report_with_state\<close> (\<^theory>\<open>Voblint_Analysis_Sign.Sign_Checks\<close>,
  \<^theory>\<open>Voblint_Analysis_Interval.Interval_Checks\<close>) unchanged, just as \<open>analyse\<close> reuses
  their state-free counterparts.
\<close>

subsection \<open>Public API: soundness corollaries stated over the runtime dispatcher\<close>

text \<open>
  \<open>analyse_interval_proved_sound\<close>/\<open>analyse_interval_refuted_sound\<close> restate
  \<open>analyse_interval_report_sound_proved\<close>/\<open>_refuted\<close> (\<open>Interval_Entry\<close>) over \<open>analyse\<close>,
  matching the routed-unit producer of \<open>analyse Interval_Analysis\<close>: solver
  termination and coverage are stated over \<open>interval_conf_sol_prog_warrow\<close>/
  \<open>interval_conf_terminates_prog_warrow\<close> (\<open>Interval_Analyses\<close>). The finiteness of
  \<open>intra\<close> and \<open>calls\<close> need not appear as separate hypotheses: the routed soundness
  chain derives both from \<open>compile_prog_finite\<close>.

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
  assumes solve: "interval_conf_terminates_prog_warrow (declared_global p) p"
      and cover: "vars_cover (prog_cfg p)
                    (fst (interval_conf_sol_prog_warrow (declared_global p) p))"
      and mem: "(v, c, Check_Proved) \<in> set (analyse Interval_Analysis p)"
  shows "\<forall>s \<in> ltr_collect (declared_global p) (prog_cfg p) (cinit_stores (declared_global p)) v.
           truthy (aval c s)"
  by (rule analyse_interval_report_sound_proved
        [OF solve _ _ _ _ mem[unfolded analyse.simps]])
     (use cover in auto)

corollary analyse_interval_refuted_sound:
  fixes p :: imp_prog and v :: pp and c :: exp
  assumes solve: "interval_conf_terminates_prog_warrow (declared_global p) p"
      and cover: "vars_cover (prog_cfg p)
                    (fst (interval_conf_sol_prog_warrow (declared_global p) p))"
      and mem: "(v, c, Check_Refuted) \<in> set (analyse Interval_Analysis p)"
  shows "\<forall>s \<in> ltr_collect (declared_global p) (prog_cfg p) (cinit_stores (declared_global p)) v.
           \<not> truthy (aval c s)"
  by (rule analyse_interval_report_sound_refuted
        [OF solve _ _ _ _ mem[unfolded analyse.simps]])
     (use cover in auto)


text \<open>
  \<open>analyse_sign_proved_sound\<close>/\<open>analyse_sign_refuted_sound\<close> restate
  \<open>analyse_sign_report_sound_proved\<close>/\<open>_refuted\<close> (\<open>Sign_Entry\<close>) over \<open>analyse\<close>,
  matching the routed-unit producer \<open>analyse Sign_Analysis\<close> dispatches to: solver
  termination and coverage are stated over \<open>sign_conf_sol_prog\<close>/\<open>sign_conf_terminates_prog\<close>
  (\<open>Sign_Analyses\<close>). \<open>finite (intra (prog_cfg prog_main_name p))\<close>/
  \<open>finite (calls ...)\<close> are not separate hypotheses here: the routed spine's own
  soundness chain derives both unconditionally from \<open>compile_prog_finite\<close>, so this
  corollary needs no finiteness premise of its own.
\<close>

corollary analyse_sign_proved_sound:
  fixes p :: imp_prog and v :: pp and c :: exp
  assumes solve: "sign_conf_terminates_prog (declared_global p) p"
      and cover: "vars_cover (prog_cfg p) (fst (sign_conf_sol_prog (declared_global p) p))"
      and mem: "(v, c, Check_Proved) \<in> set (analyse Sign_Analysis p)"
  shows "\<forall>s \<in> ltr_collect (declared_global p) (prog_cfg p) (cinit_stores (declared_global p)) v.
           truthy (aval c s)"
  by (rule analyse_sign_report_sound_proved
        [OF solve _ _ _ _ mem[unfolded analyse.simps]])
     (use cover in auto)

corollary analyse_sign_refuted_sound:
  fixes p :: imp_prog and v :: pp and c :: exp
  assumes solve: "sign_conf_terminates_prog (declared_global p) p"
      and cover: "vars_cover (prog_cfg p) (fst (sign_conf_sol_prog (declared_global p) p))"
      and mem: "(v, c, Check_Refuted) \<in> set (analyse Sign_Analysis p)"
  shows "\<forall>s \<in> ltr_collect (declared_global p) (prog_cfg p) (cinit_stores (declared_global p)) v.
           \<not> truthy (aval c s)"
  by (rule analyse_sign_report_sound_refuted
        [OF solve _ _ _ _ mem[unfolded analyse.simps]])
     (use cover in auto)

text \<open>
  \<open>analyse_int_proved_sound\<close>/\<open>analyse_int_refuted_sound\<close> restate
  \<open>analyse_int_report_sound_proved\<close>/\<open>_refuted\<close> (\<open>Int_Entry\<close>) over \<open>analyse\<close>,
  matching the routed-unit producer \<open>analyse Int_Analysis\<close> now dispatches to: solver
  termination and coverage are stated over
  \<^const>\<open>int_conf_sol_prog_warrow\<close>/\<^const>\<open>int_conf_terminates_prog_warrow\<close>
  (\<^theory>\<open>Voblint_Analysis_Int.Int_Analyses\<close>), pinned at \<^const>\<open>Refine_Fixpoint\<close> --
  the CLI does not expose refinement mode as a separate axis. \<open>int_conf_sol_prog_warrow\<close>/
  \<open>int_conf_terminates_prog_warrow\<close> need no qualification: each domain's
  configuration names carry their own prefix, so every domain's routed producer can
  be reachable from this one file without collision.
\<close>

corollary analyse_int_proved_sound:
  fixes p :: imp_prog and v :: pp and c :: exp
  assumes wf: "wf_compile_input (declared_global p) (prog_table p) (prog_procs p)"
      and solve: "int_conf_terminates_prog_warrow Refine_Fixpoint (declared_global p) p"
      and cover: "vars_cover (prog_cfg p)
                    (fst (int_conf_sol_prog_warrow Refine_Fixpoint (declared_global p) p))"
      and mem: "(v, c, Check_Proved) \<in> set (analyse Int_Analysis p)"
  shows "\<forall>s \<in> ltr_collect (declared_global p) (prog_cfg p) (cinit_stores (declared_global p)) v.
           truthy (aval c s)"
  by (rule analyse_int_report_sound_proved
        [OF wf solve _ _ _ _ mem[unfolded analyse.simps]])
     (use cover in auto)

corollary analyse_int_refuted_sound:
  fixes p :: imp_prog and v :: pp and c :: exp
  assumes wf: "wf_compile_input (declared_global p) (prog_table p) (prog_procs p)"
      and solve: "int_conf_terminates_prog_warrow Refine_Fixpoint (declared_global p) p"
      and cover: "vars_cover (prog_cfg p)
                    (fst (int_conf_sol_prog_warrow Refine_Fixpoint (declared_global p) p))"
      and mem: "(v, c, Check_Refuted) \<in> set (analyse Int_Analysis p)"
  shows "\<forall>s \<in> ltr_collect (declared_global p) (prog_cfg p) (cinit_stores (declared_global p)) v.
           \<not> truthy (aval c s)"
  by (rule analyse_int_report_sound_refuted
        [OF wf solve _ _ _ _ mem[unfolded analyse.simps]])
     (use cover in auto)

text \<open>
  Parity's and Congruence's pairs, on the same reading as the three above. Both
  route at \<open>Solver_Join\<close> and neither carries a well-formedness premise, so each
  is the shortest form the shape allows: the solver ran, it covered the keys, the
  check is in the report.
\<close>

corollary analyse_parity_proved_sound:
  fixes p :: imp_prog and v :: pp and c :: exp
  assumes solve: "parity_conf_terminates_prog (declared_global p) p"
      and cover: "vars_cover (prog_cfg p) (fst (parity_conf_sol_prog (declared_global p) p))"
      and mem: "(v, c, Check_Proved) \<in> set (analyse Parity_Analysis p)"
  shows "\<forall>s \<in> ltr_collect (declared_global p) (prog_cfg p) (cinit_stores (declared_global p)) v.
           truthy (aval c s)"
  by (rule analyse_parity_report_sound_proved
        [OF solve _ _ _ _ mem[unfolded analyse.simps]])
     (use cover in auto)

corollary analyse_parity_refuted_sound:
  fixes p :: imp_prog and v :: pp and c :: exp
  assumes solve: "parity_conf_terminates_prog (declared_global p) p"
      and cover: "vars_cover (prog_cfg p) (fst (parity_conf_sol_prog (declared_global p) p))"
      and mem: "(v, c, Check_Refuted) \<in> set (analyse Parity_Analysis p)"
  shows "\<forall>s \<in> ltr_collect (declared_global p) (prog_cfg p) (cinit_stores (declared_global p)) v.
           \<not> truthy (aval c s)"
  by (rule analyse_parity_report_sound_refuted
        [OF solve _ _ _ _ mem[unfolded analyse.simps]])
     (use cover in auto)

corollary analyse_congruence_proved_sound:
  fixes p :: imp_prog and v :: pp and c :: exp
  assumes solve: "congruence_conf_terminates_prog (declared_global p) p"
      and cover: "vars_cover (prog_cfg p) (fst (congruence_conf_sol_prog (declared_global p) p))"
      and mem: "(v, c, Check_Proved) \<in> set (analyse Congruence_Analysis p)"
  shows "\<forall>s \<in> ltr_collect (declared_global p) (prog_cfg p) (cinit_stores (declared_global p)) v.
           truthy (aval c s)"
  by (rule analyse_congruence_report_sound_proved
        [OF solve _ _ _ _ mem[unfolded analyse.simps]])
     (use cover in auto)

corollary analyse_congruence_refuted_sound:
  fixes p :: imp_prog and v :: pp and c :: exp
  assumes solve: "congruence_conf_terminates_prog (declared_global p) p"
      and cover: "vars_cover (prog_cfg p) (fst (congruence_conf_sol_prog (declared_global p) p))"
      and mem: "(v, c, Check_Refuted) \<in> set (analyse Congruence_Analysis p)"
  shows "\<forall>s \<in> ltr_collect (declared_global p) (prog_cfg p) (cinit_stores (declared_global p)) v.
           \<not> truthy (aval c s)"
  by (rule analyse_congruence_report_sound_refuted
        [OF solve _ _ _ _ mem[unfolded analyse.simps]])
     (use cover in auto)
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
     (sign_conf_terminates_prog (declared_global p) p
        \<and> vars_cover (prog_cfg p) (fst (sign_conf_sol_prog (declared_global p) p)))"
| "analyse_certified Interval_Analysis p =
     (interval_conf_terminates_prog_warrow (declared_global p) p
        \<and> vars_cover (prog_cfg p)
             (fst (interval_conf_sol_prog_warrow (declared_global p) p)))"
| "analyse_certified Int_Analysis p =
     (int_conf_terminates_prog_warrow Refine_Fixpoint (declared_global p) p
        \<and> vars_cover (prog_cfg p)
             (fst (int_conf_sol_prog_warrow Refine_Fixpoint (declared_global p) p)))"
| "analyse_certified Parity_Analysis p =
     (parity_conf_terminates_prog (declared_global p) p
        \<and> vars_cover (prog_cfg p) (fst (parity_conf_sol_prog (declared_global p) p)))"
| "analyse_certified Congruence_Analysis p =
     (congruence_conf_terminates_prog (declared_global p) p
        \<and> vars_cover (prog_cfg p) (fst (congruence_conf_sol_prog (declared_global p) p)))"

lemma analyse_proved_sound:
  fixes p :: imp_prog and v :: pp and c :: exp
  assumes wf: "wf_compile_input (declared_global p) (prog_table p) (prog_procs p)"
      and cert: "analyse_certified D p"
      and mem: "(v, c, Check_Proved) \<in> set (analyse D p)"
  shows "\<forall>s \<in> ltr_collect (declared_global p) (prog_cfg p) (cinit_stores (declared_global p)) v.
           truthy (aval c s)"
proof (cases D)
  case Sign_Analysis
  with cert have solve: "sign_conf_terminates_prog (declared_global p) p"
    and cover: "vars_cover (prog_cfg p) (fst (sign_conf_sol_prog (declared_global p) p))"
    by simp_all
  from mem Sign_Analysis have m: "(v, c, Check_Proved) \<in> set (analyse Sign_Analysis p)" by simp
  show ?thesis by (rule analyse_sign_proved_sound[OF solve cover m])
next
  case Interval_Analysis
  with cert have solve: "interval_conf_terminates_prog_warrow (declared_global p) p"
    and cover: "vars_cover (prog_cfg p) (fst (interval_conf_sol_prog_warrow (declared_global p) p))"
    by simp_all
  from mem Interval_Analysis have m: "(v, c, Check_Proved) \<in> set (analyse Interval_Analysis p)"
    by simp
  show ?thesis by (rule analyse_interval_proved_sound[OF solve cover m])
next
  case Int_Analysis
  with cert have solve: "int_conf_terminates_prog_warrow Refine_Fixpoint (declared_global p) p"
    and cover: "vars_cover (prog_cfg p)
                  (fst (int_conf_sol_prog_warrow Refine_Fixpoint (declared_global p) p))"
    by simp_all
  from mem Int_Analysis have m: "(v, c, Check_Proved) \<in> set (analyse Int_Analysis p)" by simp
  show ?thesis by (rule analyse_int_proved_sound[OF wf solve cover m])
next
  case Parity_Analysis
  with cert have solve: "parity_conf_terminates_prog (declared_global p) p"
    and cover: "vars_cover (prog_cfg p) (fst (parity_conf_sol_prog (declared_global p) p))"
    by simp_all
  from mem Parity_Analysis have m: "(v, c, Check_Proved) \<in> set (analyse Parity_Analysis p)" by simp
  show ?thesis by (rule analyse_parity_proved_sound[OF solve cover m])
next
  case Congruence_Analysis
  with cert have solve: "congruence_conf_terminates_prog (declared_global p) p"
    and cover: "vars_cover (prog_cfg p) (fst (congruence_conf_sol_prog (declared_global p) p))"
    by simp_all
  from mem Congruence_Analysis
  have m: "(v, c, Check_Proved) \<in> set (analyse Congruence_Analysis p)" by simp
  show ?thesis by (rule analyse_congruence_proved_sound[OF solve cover m])
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
  with cert have solve: "sign_conf_terminates_prog (declared_global p) p"
    and cover: "vars_cover (prog_cfg p) (fst (sign_conf_sol_prog (declared_global p) p))"
    by simp_all
  from mem Sign_Analysis have m: "(v, c, Check_Refuted) \<in> set (analyse Sign_Analysis p)" by simp
  show ?thesis by (rule analyse_sign_refuted_sound[OF solve cover m])
next
  case Interval_Analysis
  with cert have solve: "interval_conf_terminates_prog_warrow (declared_global p) p"
    and cover: "vars_cover (prog_cfg p) (fst (interval_conf_sol_prog_warrow (declared_global p) p))"
    by simp_all
  from mem Interval_Analysis have m: "(v, c, Check_Refuted) \<in> set (analyse Interval_Analysis p)"
    by simp
  show ?thesis by (rule analyse_interval_refuted_sound[OF solve cover m])
next
  case Int_Analysis
  with cert have solve: "int_conf_terminates_prog_warrow Refine_Fixpoint (declared_global p) p"
    and cover: "vars_cover (prog_cfg p)
                  (fst (int_conf_sol_prog_warrow Refine_Fixpoint (declared_global p) p))"
    by simp_all
  from mem Int_Analysis have m: "(v, c, Check_Refuted) \<in> set (analyse Int_Analysis p)" by simp
  show ?thesis by (rule analyse_int_refuted_sound[OF wf solve cover m])
next
  case Parity_Analysis
  with cert have solve: "parity_conf_terminates_prog (declared_global p) p"
    and cover: "vars_cover (prog_cfg p) (fst (parity_conf_sol_prog (declared_global p) p))"
    by simp_all
  from mem Parity_Analysis have m: "(v, c, Check_Refuted) \<in> set (analyse Parity_Analysis p)" by simp
  show ?thesis by (rule analyse_parity_refuted_sound[OF solve cover m])
next
  case Congruence_Analysis
  with cert have solve: "congruence_conf_terminates_prog (declared_global p) p"
    and cover: "vars_cover (prog_cfg p) (fst (congruence_conf_sol_prog (declared_global p) p))"
    by simp_all
  from mem Congruence_Analysis
  have m: "(v, c, Check_Refuted) \<in> set (analyse Congruence_Analysis p)" by simp
  show ?thesis by (rule analyse_congruence_refuted_sound[OF solve cover m])
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

subsection \<open>What the solved table says about the store you are holding\<close>

text \<open>
  \<open>analyse_source_sound\<close> above carries the \<^emph>\<open>verdicts\<close> to a concrete run. This
  carries the \<^emph>\<open>states\<close>: the abstract state the analysis computed for a node
  contains every concrete store that reaches it. A verdict is a consequence of
  that containment, so the two are the same soundness read at two depths --- but
  only the containment says anything at a node with no check on it, which is most
  of them.

  The dispatch is a predicate rather than a returned state because a state's type
  is the domain's own carrier: \<^typ>\<open>sign\<close> for one selection, \<^typ>\<open>ivl\<close> for
  another. Nothing polymorphic can hold both, and \<^typ>\<open>abstract_value\<close> is a
  display projection with no concretization of its own, so the quantifier has to
  close over each domain separately. Each equation below is that domain's own
  published corollary, at its own \<open>gamma\<close>.
\<close>

fun analyse_state_covers :: "analysis_domain \<Rightarrow> imp_prog \<Rightarrow> pp \<Rightarrow> store \<Rightarrow> bool" where
  "analyse_state_covers Sign_Analysis p v s =
     (s \<in> \<lbrakk>case lookup_context (analyse_sign_result p) v () of
             Bot \<Rightarrow> bot | Lifted st \<Rightarrow> st\<rbrakk>)"
| "analyse_state_covers Interval_Analysis p v s =
     (s \<in> \<lbrakk>case lookup_context (analyse_interval_result p) v () of
             Bot \<Rightarrow> bot | Lifted st \<Rightarrow> st\<rbrakk>)"
| "analyse_state_covers Int_Analysis p v s =
     (s \<in> \<lbrakk>case lookup_context (analyse_int_result p) v () of
             Bot \<Rightarrow> bot | Lifted st \<Rightarrow> st\<rbrakk>)"
| "analyse_state_covers Parity_Analysis p v s =
     (s \<in> \<lbrakk>case lookup_context (analyse_parity_result p) v () of
             Bot \<Rightarrow> bot | Lifted st \<Rightarrow> st\<rbrakk>)"
| "analyse_state_covers Congruence_Analysis p v s =
     (s \<in> \<lbrakk>case lookup_context (analyse_congruence_result p) v () of
             Bot \<Rightarrow> bot | Lifted st \<Rightarrow> st\<rbrakk>)"

theorem analyse_state_sound:
  fixes p :: imp_prog and s0 s :: store
  assumes wf: "wf_compile_input (declared_global p) (prog_table p) (prog_procs p)"
      and cert: "analyse_certified D p"
      and s0: "s0 \<in> cinit_stores (declared_global p)"
      and run: "star (pstep (declared_global p) (prog_table p))
                  (main_body (prog_table p), s0, []) (residual, s, frs)"
  shows "\<exists>v stk. csim (prog_table p) (prog_cfg p) (residual, s, frs) (v, s, stk)
                 \<and> analyse_state_covers D p v s"
  using cert
  by (cases D)
     (use analyse_sign_source_sound [OF wf _ _ s0 run]
          analyse_interval_source_sound [OF wf _ _ s0 run]
          analyse_int_source_sound [OF wf _ _ s0 run]
          analyse_parity_source_sound [OF wf _ _ s0 run]
          analyse_congruence_source_sound [OF wf _ _ s0 run]
       in auto)

text \<open>
  The same containment without the existential, which is what composes: a caller
  that already knows \<^emph>\<open>which\<close> node a store sits at --- because it obtained one
  from \<^const>\<open>csim\<close> --- needs the table's claim about that node, not about some
  node. Each case is its own domain's node-soundness lemma at
  \<^const>\<open>declared_global\<close> \<open>p\<close>.
\<close>

text \<open>
  \<^const>\<open>wf_compile_input\<close> is a premise only Int consumes, through
  \<open>wf_compile_input_reserved_ret_var\<close>: its transfer reserves the return slot, so its
  node soundness needs to know the compiler kept that name free. The other four
  never look at it. It is asked for uniformly rather than per domain because a
  caller holding this lemma is already holding \<^const>\<open>wf_compile_input\<close> --- every
  statement it composes with needs it too.
\<close>

lemma analyse_state_node_sound:
  assumes wf: "wf_compile_input (declared_global p) (prog_table p) (prog_procs p)"
      and cert: "analyse_certified D p"
      and mem: "s \<in> ltr_collect (declared_global p) (prog_cfg p)
                      (cinit_stores (declared_global p)) v"
  shows "analyse_state_covers D p v s"
proof (cases D)
  case Sign_Analysis
  with cert have "sign_conf_terminates_prog (declared_global p) p"
    and "vars_cover (prog_cfg p) (fst (sign_conf_sol_prog (declared_global p) p))" by simp_all
  from analyse_sign_result_node_sound_of_cover [OF this] mem Sign_Analysis
  show ?thesis by (auto simp: analyse_sign_result_def)
next
  case Interval_Analysis
  with cert have "interval_conf_terminates_prog_warrow (declared_global p) p"
    and "vars_cover (prog_cfg p)
           (fst (interval_conf_sol_prog_warrow (declared_global p) p))" by simp_all
  from analyse_interval_result_node_sound_of_cover [OF this] mem Interval_Analysis
  show ?thesis by (auto simp: analyse_interval_result_def)
next
  case Int_Analysis
  with cert have "int_conf_terminates_prog_warrow Refine_Fixpoint (declared_global p) p"
    and "vars_cover (prog_cfg p)
           (fst (int_conf_sol_prog_warrow Refine_Fixpoint (declared_global p) p))" by simp_all
  from analyse_int_ctx_result_warrow_node_sound_of_cover
         [OF wf [THEN wf_compile_input_reserved_ret_var] this] mem Int_Analysis
  show ?thesis by (auto simp: analyse_int_result_def analyse_int_result_for_def)
next
  case Parity_Analysis
  with cert have "parity_conf_terminates_prog (declared_global p) p"
    and "vars_cover (prog_cfg p) (fst (parity_conf_sol_prog (declared_global p) p))" by simp_all
  from analyse_parity_result_node_sound_of_cover [OF this] mem Parity_Analysis
  show ?thesis by (auto simp: analyse_parity_result_def)
next
  case Congruence_Analysis
  with cert have "congruence_conf_terminates_prog (declared_global p) p"
    and "vars_cover (prog_cfg p)
           (fst (congruence_conf_sol_prog (declared_global p) p))" by simp_all
  from analyse_congruence_result_node_sound_of_cover [OF this] mem Congruence_Analysis
  show ?thesis by (auto simp: analyse_congruence_result_def)
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


end
