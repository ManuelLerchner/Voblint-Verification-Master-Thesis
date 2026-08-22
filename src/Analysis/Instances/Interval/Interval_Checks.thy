theory Interval_Checks
  imports Interval_Classify Interval_Ctx_None_Sound
begin

hide_const phase.N

section \<open>Interval instance of the generic check-discharge interface\<close>

text \<open>
  The check-classification machinery (\<open>interval_classify_check\<close> and its
  soundness directions) lives in \<open>Interval_Classify\<close>, split out so the
  routed-spine producer below (\<open>Interval_Ctx_None_Sound\<close>) can depend
  on it without a cycle through this theory's own solved-result tables,
  which read that producer's routed output.
\<close>


subsection \<open>Solved-result table\<close>

text \<open>
  \<open>analyse_interval_td_result_for\<close> is the canonical solved D/G system under
  the Apinis warrowing update rule (Interval's infinite-height local
  lattice needs it for termination), read as a
  \<^typ>\<open>(unit, ivl abs_state) analysis_result\<close>: a one-line partial
  application of \<^const>\<open>analyse_interval_ctx_result_warrow_for\<close>
  (\<^theory>\<open>Voblint_Analysis.Interval_Ctx_None_Sound\<close>), fixed at
  \<^const>\<open>prog_main_name\<close>, which already binds the single routed-unit solve
  and canonicalizes/normalizes each local key. Every report below reads
  through a result table via \<^const>\<open>lookup_context\<close> rather than a raw
  solver-environment lookup.
\<close>

definition analyse_interval_td_result_for ::
    "(vname \<Rightarrow> bool) \<Rightarrow> imp_prog \<Rightarrow> (unit, ivl abs_state) analysis_result" where
  "analyse_interval_td_result_for gs p = analyse_interval_ctx_result_warrow_for gs prog_main_name p"

text \<open>Convenience instance at \<^const>\<open>declared_global\<close> \<open>p\<close>, matching
  \<open>analyse_interval_td_report\<close>'s shape.\<close>

definition analyse_interval_td_result ::
    "imp_prog \<Rightarrow> (unit, ivl abs_state) analysis_result" where
  "analyse_interval_td_result p = analyse_interval_td_result_for (declared_global p) p"

subsection \<open>Solved-result table: always-join update rule\<close>

text \<open>
  \<open>analyse_interval_join_result\<close> is \<^const>\<open>analyse_interval_td_result\<close>'s
  sibling under the always-join update rule: a one-line partial application
  of \<^const>\<open>analyse_interval_ctx_result_for\<close>
  (\<^theory>\<open>Voblint_Analysis.Interval_Ctx_None_Sound\<close>), fixed at
  \<^const>\<open>prog_main_name\<close>, reading \<^const>\<open>ictx_sol_prog\<close> instead of
  \<^const>\<open>ictx_sol_prog_warrow\<close>.
\<close>

definition analyse_interval_join_result_for ::
    "(vname \<Rightarrow> bool) \<Rightarrow> imp_prog \<Rightarrow> (unit, ivl abs_state) analysis_result" where
  "analyse_interval_join_result_for gs p = analyse_interval_ctx_result_for gs prog_main_name p"

definition analyse_interval_join_result ::
    "imp_prog \<Rightarrow> (unit, ivl abs_state) analysis_result" where
  "analyse_interval_join_result p = analyse_interval_join_result_for (declared_global p) p"

subsection \<open>Solved-result table: per-origin update rule\<close>

text \<open>
  \<open>analyse_interval_per_origin_result\<close> mirrors
  \<open>analyse_interval_join_result\<close> exactly, a one-line partial application of
  \<^const>\<open>analyse_interval_ctx_result_per_origin_for\<close>
  (\<^theory>\<open>Voblint_Analysis.Interval_Ctx_None_Sound\<close>), fixed at
  \<^const>\<open>prog_main_name\<close>, reading \<^const>\<open>ictx_sol_prog_per_origin\<close> instead
  of \<^const>\<open>ictx_sol_prog\<close>.
\<close>

definition analyse_interval_per_origin_result_for ::
    "(vname \<Rightarrow> bool) \<Rightarrow> imp_prog \<Rightarrow> (unit, ivl abs_state) analysis_result" where
  "analyse_interval_per_origin_result_for gs p = analyse_interval_ctx_result_per_origin_for gs prog_main_name p"

definition analyse_interval_per_origin_result ::
    "imp_prog \<Rightarrow> (unit, ivl abs_state) analysis_result" where
  "analyse_interval_per_origin_result p = analyse_interval_per_origin_result_for (declared_global p) p"

subsection \<open>Whole-program check report: the native D/G runtime API\<close>

text \<open>
  \<open>analyse_interval_td_report_for\<close> is the report function the exported
  \<open>analyse\<close> API actually dispatches to for \<open>Interval_Analysis\<close> (see
  \<open>Analyse_Dispatch\<close>, downstream in Examples), fixed at \<open>prog_main_name\<close>
  since \<^const>\<open>analyse_interval_td_result_for\<close> already is. It reads its
  per-node state through \<^const>\<open>analyse_interval_td_result_for\<close>'s
  \<^type>\<open>analysis_result\<close> table via \<^const>\<open>lookup_context\<close>, mirroring
  \<open>Sign_Checks\<close>'s \<open>analyse_sign_report_for\<close> exactly, including its choice to
  classify an \<^const>\<open>Unreachable\<close> point at \<^const>\<open>bot\<close> -- the same value
  \<^const>\<open>classify_checks\<close> always fed such a node -- rather than introducing a
  fourth, \<open>Dead\<close> outcome \<open>check_result\<close> does not carry. Reusing the exact
  same warrowing/\<open>analyse_interval_td\<close> naming keeps the still-live
  \<open>analyse_interval_td_at\<close>/\<open>analyse_interval_td_terminates\<close> family (the
  entry-state context analysis, the GraphViz state-report tooling) fully
  unchanged: only this report's own definition is repointed onto the
  result table.

  \<open>r\<close> is bound once, outside \<^const>\<open>classify_checks\<close>'s per-check closure, so
  the single D/G solve \<^const>\<open>analyse_interval_td_result_for\<close> performs is
  shared across every check in the report.
\<close>

definition analyse_interval_td_report_for :: "(vname \<Rightarrow> bool) \<Rightarrow> imp_prog \<Rightarrow> check_report_entry list" where
  "analyse_interval_td_report_for gs p =
     (let r = analyse_interval_td_result_for gs p
      in classify_checks (prog_cfg prog_main_name p)
           (\<lambda>v. case lookup_context r v () of Unreachable \<Rightarrow> bot | Reachable st \<Rightarrow> st)
           interval_classify_check)"

text \<open>
  Convenience instance at \<^const>\<open>declared_global\<close> \<open>p\<close>.
\<close>

definition analyse_interval_td_report :: "imp_prog \<Rightarrow> check_report_entry list" where
  "analyse_interval_td_report p = analyse_interval_td_report_for (declared_global p) p"

subsection \<open>Whole-program check report with state: the native D/G runtime API\<close>

text \<open>
  State-carrying sibling of \<open>analyse_interval_td_report_for\<close>/
  \<open>analyse_interval_td_report\<close>, via \<^const>\<open>classify_checks_with_state\<close>: same
  result table, with the per-check Interval environment attached to each
  report entry instead of discarded, and an exact \<open>unreachable\<close> flag read
  straight off \<^const>\<open>lookup_context\<close>'s \<^const>\<open>Unreachable\<close>/\<^const>\<open>Reachable\<close>
  case split -- exact because \<open>normalize_point_canonicalize_lift_eq_old\<close>
  (\<^theory>\<open>Voblint_Core.Analysis_Result\<close>) is precisely the fact that this
  reading agrees with the older \<^const>\<open>resolved_st_q_lifted_is_bot_for\<close>
  test on the same raw local unknown, the same argument
  \<open>analyse_sign_report_for_with_state\<close>'s Sign counterpart uses.
\<close>

definition analyse_interval_td_report_for_with_state ::
    "(vname \<Rightarrow> bool) \<Rightarrow> imp_prog \<Rightarrow> (pp \<times> exp \<times> check_result \<times> bool \<times> ivl abs_state) list" where
  "analyse_interval_td_report_for_with_state gs p =
     (let r = analyse_interval_td_result_for gs p
      in classify_checks_with_state (prog_cfg prog_main_name p)
           (\<lambda>v. case lookup_context r v () of
                  Unreachable \<Rightarrow> (True, bot)
                | Reachable st \<Rightarrow> (False, st))
           (\<lambda>c (_, s). interval_classify_check c s))"

text \<open>Convenience instance at \<^const>\<open>declared_global\<close> \<open>p\<close>, matching
  \<open>analyse_interval_td_report\<close>'s shape.\<close>

definition analyse_interval_td_report_with_state ::
    "imp_prog \<Rightarrow> (pp \<times> exp \<times> check_result \<times> bool \<times> ivl abs_state) list" where
  "analyse_interval_td_report_with_state p = analyse_interval_td_report_for_with_state (declared_global p) p"

subsection \<open>Solver-choice variant report: always-join update rule\<close>

text \<open>
  \<open>analyse_interval_report_for\<close>'s sibling relationship to
  \<^const>\<open>analyse_interval_td_report\<close> mirrors \<^const>\<open>analyse_interval_join_result\<close>'s
  to \<^const>\<open>analyse_interval_td_result\<close>: this route exists so
  \<open>analyse_with_solver\<close> can compare update rules on the identical equation
  system (issue #131), mirroring Sign's own always-join default
  (\<open>Sign_Checks.analyse_sign_report\<close>). Plain join has no widening, so it
  lacks warrowing's termination guarantee on a genuine local loop with
  unbounded growth -- production still dispatches to
  \<open>analyse_interval_td_report\<close>.
\<close>

definition analyse_interval_report_for :: "(vname \<Rightarrow> bool) \<Rightarrow> imp_prog \<Rightarrow> check_report_entry list" where
  "analyse_interval_report_for gs p =
     (let r = analyse_interval_join_result_for gs p
      in classify_checks (prog_cfg prog_main_name p)
           (\<lambda>v. case lookup_context r v () of Unreachable \<Rightarrow> bot | Reachable st \<Rightarrow> st)
           interval_classify_check)"

text \<open>
  Convenience instance at \<^const>\<open>declared_global\<close> \<open>p\<close>, matching
  \<open>analyse_interval_td_report\<close>'s shape.
\<close>

definition analyse_interval_report :: "imp_prog \<Rightarrow> check_report_entry list" where
  "analyse_interval_report p = analyse_interval_report_for (declared_global p) p"

subsection \<open>Solver-choice variant report: per-origin update rule\<close>
subsection \<open>Solver-choice variant report: per-origin update rule\<close>

text \<open>
  \<open>analyse_interval_report_per_origin_for\<close>'s sibling relationship to
  \<^const>\<open>analyse_interval_report\<close> mirrors
  \<^const>\<open>analyse_interval_per_origin_result\<close>'s to
  \<^const>\<open>analyse_interval_join_result\<close>: keeping each write origin's
  contribution separate instead of folding every contribution into one
  join, the same role Sign's \<open>analyse_sign_report_per_origin\<close> plays there.
\<close>

definition analyse_interval_report_per_origin_for :: "(vname \<Rightarrow> bool) \<Rightarrow> imp_prog \<Rightarrow> check_report_entry list" where
  "analyse_interval_report_per_origin_for gs p =
     (let r = analyse_interval_per_origin_result_for gs p
      in classify_checks (prog_cfg prog_main_name p)
           (\<lambda>v. case lookup_context r v () of Unreachable \<Rightarrow> bot | Reachable st \<Rightarrow> st)
           interval_classify_check)"

text \<open>Convenience instance at \<^const>\<open>declared_global\<close> \<open>p\<close>, matching \<open>analyse_interval_report\<close>'s
  shape.\<close>

definition analyse_interval_report_per_origin :: "imp_prog \<Rightarrow> check_report_entry list" where
  "analyse_interval_report_per_origin p =
     analyse_interval_report_per_origin_for (declared_global p) p"

subsection \<open>Solver-choice variant report: warrowing per origin\<close>

text \<open>
  The fourth update rule's report.  Unlike the \<open>join\<close>/\<open>per_origin\<close> pair, this one is not
  interchangeable with \<open>analyse_interval_td_report\<close>'s Apinis warrowing on every
  program: both widen, but this rule widens each origin's own contribution and joins
  afterwards, so a global with two producers can end up strictly more precise here.
\<close>

definition analyse_interval_wpo_result_for ::
    "(vname \<Rightarrow> bool) \<Rightarrow> imp_prog \<Rightarrow> (unit, ivl abs_state) analysis_result" where
  "analyse_interval_wpo_result_for gs p = analyse_interval_ctx_result_wpo_for gs prog_main_name p"

definition analyse_interval_report_wpo_for :: "(vname \<Rightarrow> bool) \<Rightarrow> imp_prog \<Rightarrow> check_report_entry list" where
  "analyse_interval_report_wpo_for gs p =
     (let r = analyse_interval_wpo_result_for gs p
      in classify_checks (prog_cfg prog_main_name p)
           (\<lambda>v. case lookup_context r v () of Unreachable \<Rightarrow> bot | Reachable st \<Rightarrow> st)
           interval_classify_check)"

definition analyse_interval_report_wpo :: "imp_prog \<Rightarrow> check_report_entry list" where
  "analyse_interval_report_wpo p =
     analyse_interval_report_wpo_for (declared_global p) p"

end



