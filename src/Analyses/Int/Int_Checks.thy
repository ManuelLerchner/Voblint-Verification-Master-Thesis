theory Int_Checks
  imports Int_Classify Int_Solver_Analyses "Voblint_Analysis_Base.Analysis_Surface"
begin

hide_const phase.N

text \<open>
  The check-classification machinery (\<open>int_classify_check\<close> and its soundness directions)
  lives in \<open>Int_Classify\<close>, split out so the routed-spine producer below
  (\<^theory>\<open>Voblint_Analysis_Int.Int_Analyses\<close>) can depend on it without a cycle through this
  theory's own solved-result tables, which read that producer's routed output.
\<close>

subsection \<open>Solved-result table\<close>

text \<open>
  \<open>analyse_int_result_for\<close> is the canonical solved D/G system, read as a
  \<^typ>\<open>(unit, int_dom abs_state) analysis_result\<close>: a one-line partial application of
  \<^const>\<open>analyse_int_ctx_result_warrow_for\<close>
  (\<^theory>\<open>Voblint_Analysis_Int.Int_Analyses\<close>), fixed at \<^const>\<open>Refine_Fixpoint\<close> and
  \<^const>\<open>prog_main_name\<close>, which already binds the single routed-unit solve and
  canonicalizes/normalizes each local key -- Int's Apinis warrowing solver is its production
  default, mirroring \<open>Interval_Checks.analyse_interval_td_result_for\<close>. Every report below
  reads through a result table via \<^const>\<open>lookup_context\<close> rather than a raw solver-environment
  lookup.
\<close>

definition analyse_int_result_for ::
    "(vname \<Rightarrow> bool) \<Rightarrow> imp_prog \<Rightarrow> (unit, int_dom abs_state) analysis_result" where
  "analyse_int_result_for gs p = analyse_int_ctx_result_warrow_for Refine_Fixpoint gs p"

text \<open>Convenience instance at \<^const>\<open>declared_global\<close> \<open>p\<close>, matching
  \<open>analyse_int_report\<close>'s shape.\<close>

definition analyse_int_result ::
    "imp_prog \<Rightarrow> (unit, int_dom abs_state) analysis_result" where
  "analyse_int_result p = analyse_int_result_for (declared_global p) p"

subsection \<open>Solved-result table: always-join update rule\<close>

text \<open>
  \<open>analyse_int_join_result\<close> is \<^const>\<open>analyse_int_result\<close>'s sibling under the
  always-join update rule: a one-line partial application of
  \<^const>\<open>analyse_int_ctx_result_for\<close> (\<^theory>\<open>Voblint_Analysis_Int.Int_Analyses\<close>), fixed at
  \<^const>\<open>prog_main_name\<close>, reading \<^const>\<open>int_conf_sol_prog\<close> instead of
  \<^const>\<open>int_conf_sol_prog_warrow\<close>. The CLI does not expose refinement mode as a separate
  axis, so the convenience instance below stays pinned at \<^const>\<open>Refine_Fixpoint\<close> like
  every other exported \<open>int_dom\<close> entry point.
\<close>

definition analyse_int_join_result_for ::
    "refine_mode \<Rightarrow> (vname \<Rightarrow> bool) \<Rightarrow> imp_prog \<Rightarrow> (unit, int_dom abs_state) analysis_result" where
  "analyse_int_join_result_for mode gs p = analyse_int_ctx_result_for mode gs p"

definition analyse_int_join_result ::
    "imp_prog \<Rightarrow> (unit, int_dom abs_state) analysis_result" where
  "analyse_int_join_result p = analyse_int_join_result_for Refine_Fixpoint (declared_global p) p"

subsection \<open>Solved-result table: per-origin update rule\<close>

text \<open>
  \<open>analyse_int_per_origin_result\<close> mirrors \<^const>\<open>analyse_int_join_result\<close> exactly, a
  one-line partial application of \<^const>\<open>analyse_int_ctx_result_per_origin_for\<close>
  (\<^theory>\<open>Voblint_Analysis_Int.Int_Analyses\<close>), fixed at \<^const>\<open>prog_main_name\<close>, reading
  \<^const>\<open>int_conf_sol_prog_per_origin\<close> instead of \<^const>\<open>int_conf_sol_prog\<close>.
\<close>

definition analyse_int_per_origin_result_for ::
    "refine_mode \<Rightarrow> (vname \<Rightarrow> bool) \<Rightarrow> imp_prog \<Rightarrow> (unit, int_dom abs_state) analysis_result" where
  "analyse_int_per_origin_result_for mode gs p = analyse_int_ctx_result_per_origin_for mode gs p"

definition analyse_int_per_origin_result ::
    "imp_prog \<Rightarrow> (unit, int_dom abs_state) analysis_result" where
  "analyse_int_per_origin_result p = analyse_int_per_origin_result_for Refine_Fixpoint (declared_global p) p"

subsection \<open>Whole-program check report: the native D/G runtime API\<close>

text \<open>
  \<open>analyse_int_report_for\<close> is the report function the exported \<open>analyse\<close> API dispatches
  to for \<open>Int_Analysis\<close> (see \<open>Analyse_Dispatch\<close>, CLI session, downstream), fixed at
  \<open>prog_main_name\<close> and reading its per-node state through
  \<^const>\<open>analyse_int_ctx_result_warrow_for\<close> at that \<open>mode\<close> via \<^const>\<open>lookup_context\<close> --
  the same routed producer \<^const>\<open>analyse_int_result_for\<close> pins at
  \<^const>\<open>Refine_Fixpoint\<close> above -- but, unlike \<^const>\<open>analyse_int_result_for\<close>, keeping
  \<open>mode\<close> as a free parameter, matching the pre-migration definition's own generality
  (\<open>Int_Entry\<close> exercises both refinement modes through this same report function).
  \<open>r\<close> is bound once, outside \<^const>\<open>classify_checks\<close>'s per-check closure, so the single
  D/G solve performs is shared across every check in the report, classifying an
  \<^const>\<open>Bot\<close> point at \<^const>\<open>bot\<close> -- the same value \<^const>\<open>classify_checks\<close> always
  fed such a node -- rather than a fourth, \<open>Dead\<close> outcome \<open>check_result\<close> does not carry.
\<close>

definition analyse_int_report_for :: "refine_mode \<Rightarrow> (vname \<Rightarrow> bool) \<Rightarrow> imp_prog \<Rightarrow> check_report_entry list" where
  "analyse_int_report_for mode gs p =
     analysis_surface.report (analyse_int_ctx_result_warrow_for mode gs) bot
       int_classify_check p"

text \<open>
  Convenience instance at \<^const>\<open>declared_global\<close> \<open>p\<close>, pinned at \<open>Refine_Fixpoint\<close>
  like \<^const>\<open>analyse_int_result\<close>: this is the report the production \<open>analyse\<close>
  API reaches, matching \<open>analyse_interval_td_report\<close>'s shape.
\<close>

definition analyse_int_report :: "imp_prog \<Rightarrow> check_report_entry list" where
  "analyse_int_report p = analyse_int_report_for Refine_Fixpoint (declared_global p) p"

subsection \<open>Whole-program check report with state: the native D/G runtime API\<close>

text \<open>
  State-carrying sibling of \<open>analyse_int_report_for\<close>/\<open>analyse_int_report\<close>, via
  \<^const>\<open>classify_checks_with_state\<close>: same result table, with the per-check \<open>int_dom\<close>
  environment attached to each report entry instead of discarded -- needed so
  \<open>Analyse_Dispatch.analyse_with_state\<close> can stay total once \<open>Int_Analysis\<close> joins
  \<open>analysis_domain\<close>. An exact \<open>unreachable\<close> flag is read straight off
  \<^const>\<open>lookup_context\<close>'s \<^const>\<open>Bot\<close>/\<^const>\<open>Lifted\<close> case split -- exact because
  composing \<^const>\<open>canonicalize_lift\<close>'s witness-bottom collapse with
  \<^const>\<open>normalize_point\<close>'s readback agrees with the older
  \<^const>\<open>resolved_st_q_lifted_is_bot_for\<close> test on the same raw local unknown, the same
  argument \<open>analyse_sign_report_for_with_state\<close>'s Sign counterpart uses. Propagates the
  routed producer transitively through \<^const>\<open>analyse_int_result_for\<close>.
\<close>

definition analyse_int_report_for_with_state ::
    "(vname \<Rightarrow> bool) \<Rightarrow> imp_prog \<Rightarrow> (pp \<times> exp \<times> check_result \<times> bool \<times> int_dom abs_state) list" where
  "analyse_int_report_for_with_state gs p =
     (let r = analyse_int_result_for gs p
      in classify_checks_with_state (prog_cfg p)
           (\<lambda>v. case lookup_context r v () of
                  Bot \<Rightarrow> (True, bot)
                | Lifted st \<Rightarrow> (False, st))
           (\<lambda>c (_, s). int_classify_check c s))"

text \<open>Convenience instance at \<^const>\<open>declared_global\<close> \<open>p\<close>, matching
  \<open>analyse_int_report\<close>'s shape.\<close>

definition analyse_int_report_with_state ::
    "imp_prog \<Rightarrow> (pp \<times> exp \<times> check_result \<times> bool \<times> int_dom abs_state) list" where
  "analyse_int_report_with_state p = analyse_int_report_for_with_state (declared_global p) p"

subsection \<open>Solver-choice variants: always-join and per-origin update rules\<close>

text \<open>
  \<open>analyse_int_report_join_for\<close>'s sibling relationship to \<^const>\<open>analyse_int_report\<close>
  mirrors \<^const>\<open>analyse_int_join_result\<close>'s to \<^const>\<open>analyse_int_result\<close>: this route
  exists so \<open>analyse_with_solver\<close> can compare update rules on the identical equation
  system, mirroring \<open>Interval_Checks.analyse_interval_report_for\<close>/
  \<open>Sign_Checks.analyse_sign_report_for\<close>'s own always-join default. The CLI does not
  expose refinement mode as a separate axis, so this convenience instance stays pinned
  at \<open>Refine_Fixpoint\<close> like \<^const>\<open>analyse_int_report\<close>. Propagates the routed producer
  transitively through \<^const>\<open>analyse_int_join_result_for\<close>.
\<close>

definition analyse_int_report_join_for :: "refine_mode \<Rightarrow> (vname \<Rightarrow> bool) \<Rightarrow> imp_prog \<Rightarrow> check_report_entry list" where
  "analyse_int_report_join_for mode gs p =
     analysis_surface.report (analyse_int_join_result_for mode gs) bot int_classify_check p"

definition analyse_int_report_join :: "imp_prog \<Rightarrow> check_report_entry list" where
  "analyse_int_report_join p = analyse_int_report_join_for Refine_Fixpoint (declared_global p) p"

text \<open>
  \<open>analyse_int_report_per_origin_for\<close>'s sibling relationship to
  \<^const>\<open>analyse_int_report_join\<close> mirrors \<^const>\<open>analyse_int_per_origin_result\<close>'s to
  \<^const>\<open>analyse_int_join_result\<close>: keeping each write origin's contribution separate
  instead of folding every contribution into one join. Propagates the routed producer
  transitively through \<^const>\<open>analyse_int_per_origin_result_for\<close>.
\<close>

definition analyse_int_report_per_origin_for :: "refine_mode \<Rightarrow> (vname \<Rightarrow> bool) \<Rightarrow> imp_prog \<Rightarrow> check_report_entry list" where
  "analyse_int_report_per_origin_for mode gs p =
     analysis_surface.report (analyse_int_per_origin_result_for mode gs) bot
       int_classify_check p"

definition analyse_int_report_per_origin :: "imp_prog \<Rightarrow> check_report_entry list" where
  "analyse_int_report_per_origin p =
     analyse_int_report_per_origin_for Refine_Fixpoint (declared_global p) p"

subsection \<open>Solver-choice variant report: warrowing per origin\<close>

text \<open>
  The fourth update rule's report.  Both this and Apinis warrowing widen, so both terminate
  where \<open>join\<close>/\<open>per_origin\<close> need not; they differ in whether the join happens before or
  after the widening, which a global with two producers can observe.
\<close>

definition analyse_int_wpo_result_for ::
    "refine_mode \<Rightarrow> (vname \<Rightarrow> bool) \<Rightarrow> imp_prog \<Rightarrow> (unit, int_dom abs_state) analysis_result" where
  "analyse_int_wpo_result_for mode gs p = analyse_int_ctx_result_wpo_for mode gs p"

definition analyse_int_report_wpo_for :: "refine_mode \<Rightarrow> (vname \<Rightarrow> bool) \<Rightarrow> imp_prog \<Rightarrow> check_report_entry list" where
  "analyse_int_report_wpo_for mode gs p =
     analysis_surface.report (analyse_int_wpo_result_for mode gs) bot int_classify_check p"

definition analyse_int_report_wpo :: "imp_prog \<Rightarrow> check_report_entry list" where
  "analyse_int_report_wpo p =
     analyse_int_report_wpo_for Refine_Fixpoint (declared_global p) p"

text \<open>
  The solved table behind that report, at the same \<^const>\<open>Refine_Fixpoint\<close> mode and on the
  same \<^const>\<open>declared_global\<close> footing, so a caller reading states sees exactly what the
  report's verdicts were drawn from rather than a second, differently-configured solve.
\<close>

definition analyse_int_wpo_result ::
    "imp_prog \<Rightarrow> (unit, int_dom abs_state) analysis_result" where
  "analyse_int_wpo_result p =
     analyse_int_wpo_result_for Refine_Fixpoint (declared_global p) p"

subsection \<open>The published surface, one interpretation per discipline\<close>

text \<open>
  Int's four disciplines through the shared \<^locale>\<open>analysis_surface\<close>, each at
  \<^const>\<open>Refine_Fixpoint\<close> --- the production refinement mode its own report wrappers
  already fix --- so a state read here comes from the same solve the verdicts did, not a
  differently-configured one.
\<close>

interpretation int_join: analysis_surface
  analyse_int_join_result bot int_classify_check
  by unfold_locales

interpretation int_per_origin: analysis_surface
  analyse_int_per_origin_result bot int_classify_check
  by unfold_locales

interpretation int_warrow: analysis_surface
  analyse_int_result bot int_classify_check
  by unfold_locales

interpretation int_wpo: analysis_surface
  analyse_int_wpo_result bot int_classify_check
  by unfold_locales

lemma int_report_join_eq: "analyse_int_report_join p = int_join.report p"
  by (simp add: analyse_int_report_join_def analyse_int_report_join_for_def
      analyse_int_join_result_def surface_unfold)

lemma int_report_per_origin_eq:
  "analyse_int_report_per_origin p = int_per_origin.report p"
  by (simp add: analyse_int_report_per_origin_def analyse_int_report_per_origin_for_def
      analyse_int_per_origin_result_def surface_unfold)

lemma int_report_warrow_eq: "analyse_int_report p = int_warrow.report p"
  by (simp add: analyse_int_report_def analyse_int_report_for_def
      analyse_int_result_def analyse_int_result_for_def surface_unfold)

lemma int_report_wpo_eq: "analyse_int_report_wpo p = int_wpo.report p"
  by (simp add: analyse_int_report_wpo_def analyse_int_report_wpo_for_def
      analyse_int_wpo_result_def surface_unfold)

end

