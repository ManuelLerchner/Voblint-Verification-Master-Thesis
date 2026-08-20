theory Interval_Checks
  imports Interval_Numeric_Queries Interval_Backward "Voblint_Core.Abstract_Checks"
    "Voblint_Core.Analysis_Result" Interval_Exec_Sound
    "Voblint_Analysis.Monovariant_Analysis_Result"
begin

hide_const phase.N

section \<open>Interval instance of the generic check-discharge interface\<close>

text \<open>
  Only composition lives here, mirroring \<open>Sign_Checks\<close>: the Interval bound
  tables (\<open>interval_less_true\<close>/\<open>interval_less_false\<close>/\<open>interval_eq_true\<close>/
  \<open>interval_eq_false\<close>) and their \<open>Interval_Numeric_Queries\<close> interpretation of
  \<open>abstract_numeric_queries\<close> live in that theory. The Interval expression
  evaluator \<open>aval_ivl\<close> lives in \<open>Interval_Backward\<close>. The Boolean recursion over
  \<^typ>\<open>exp\<close> (\<open>Not\<close>, \<open>And\<close>, \<open>Or\<close>), the three-way classification, and the
  node-indexed bridge to \<^const>\<open>checks_proven\<close> come from interpreting
  \<open>abstract_check_domain\<close> once, below, reusing the numeric-query facts
  already proved sound in \<open>interval_numeric_queries\<close> rather than re-deriving
  the comparison tables --- the same way \<open>ivl_backward_domain\<close> in
  \<open>Interval_Backward.thy\<close> interprets \<open>backward_domain\<close> for guard narrowing.
\<close>

global_interpretation interval_check_domain:
  abstract_check_domain gamma_ivl interval_less_true interval_less_false interval_eq_true
    interval_eq_false gamma_state aval_ivl
  defines
    interval_check_true = interval_check_domain.check_true
    and interval_check_false = interval_check_domain.check_false
    and interval_classify_check = interval_check_domain.classify_check
    and interval_checks_proven = interval_check_domain.abstract_checks_proven
proof unfold_locales
  fix s :: store and e :: exp and \<sigma> :: "ivl abs_state"
  assume "s \<in> \<lbrakk>\<sigma>\<rbrakk>"
  then have "\<forall>x. s x \<in> gamma (\<sigma> x)" by (rule gamma_stateD)
  then have "\<forall>x. s x \<in> gamma_ivl (\<sigma> x)" by simp
  then show "aval e s \<in> gamma_ivl (aval_ivl e \<sigma>)" using aval_ivl_sound by blast
qed

text \<open>
  Only the consumer-facing aliases get a short Interval-prefixed name, the
  same choice \<open>Sign_Checks\<close> makes: \<open>classify_check\<close>'s two directions and the
  \<open>checks_proven\<close> bridge, both exercised by the worked example. The lower-
  level \<open>check_true_sound\<close>/\<open>check_false_sound\<close>/\<open>check_true_false_vacuous\<close>
  facts \<open>classify_check\<close>'s own soundness is built from stay reachable under
  the qualified \<open>interval_check_domain.\<close> name instead of a dedicated alias
  here.
\<close>

lemmas interval_classify_check_proved = interval_check_domain.classify_check_proved
lemmas interval_classify_check_refuted = interval_check_domain.classify_check_refuted
lemmas interval_checks_provenI = interval_check_domain.abstract_checks_provenI
lemmas interval_checks_proven_sound = interval_check_domain.abstract_checks_proven_sound

subsection \<open>Executable classification tests\<close>

text \<open>One state per test, built as an override of an otherwise-unconstrained
  (\<open>ivl_top\<close>) environment, so each test exercises exactly the comparison it
  names, and one showing the precision gain over Sign: a bounded range proves
  both a wider upper bound and a tighter lower bound in one classification,
  which Sign's four-value lattice cannot distinguish from \<open>STop\<close>.\<close>

definition test_env_bounded :: "ivl abs_state" where
  "test_env_bounded = (\<lambda>_. ivl_top)((STR ''x'') := Ivl (Fin 4) (Fin 7))"

lemma interval_classify_less_proved:
  "interval_classify_check (Less (V (STR ''x'')) (N 11)) test_env_bounded = Check_Proved"
  unfolding test_env_bounded_def by eval

lemma interval_classify_less_refuted:
  "interval_classify_check (Less (V (STR ''x'')) (N 0)) test_env_bounded = Check_Refuted"
  unfolding test_env_bounded_def by eval

lemma interval_classify_eq_unknown:
  "interval_classify_check (Eq (V (STR ''x'')) (N 5)) test_env_bounded = Check_Unknown"
  unfolding test_env_bounded_def by eval

text \<open>The precision gain over Sign: \<open>0 < x\<close> and \<open>x < 8\<close> both hold outright
  once \<open>x\<close> is known to lie strictly between \<open>3\<close> and \<open>8\<close> --- a fact only a
  domain that tracks numeric bounds can prove; Sign's \<open>SPos\<close>/\<open>SNonNeg\<close> would
  classify \<open>x < 8\<close> \<^term>\<open>Check_Unknown\<close> on the same information.\<close>

definition test_env_precision :: "ivl abs_state" where
  "test_env_precision = (\<lambda>_. ivl_top)((STR ''x'') := Ivl (Fin 4) (Fin 7))"

lemma interval_classify_precision_lower_proved:
  "interval_classify_check (Less (N 2) (V (STR ''x''))) test_env_precision = Check_Proved"
  unfolding test_env_precision_def by eval

lemma interval_classify_precision_upper_proved:
  "interval_classify_check (Less (V (STR ''x'')) (N 9)) test_env_precision = Check_Proved"
  unfolding test_env_precision_def by eval

subsection \<open>Whole-program check report\<close>

text \<open>Thin composition, mirroring \<open>sign_check_report\<close>: \<^const>\<open>classify_checks\<close>
  owns the traversal and ordering, \<^const>\<open>ivl_exec_prog_at\<close> owns the
  node-indexed Interval environment, and \<open>interval_classify_check\<close> owns the
  per-check classification.\<close>

definition interval_check_report ::
    "(vname \<Rightarrow> bool) \<Rightarrow> pname \<Rightarrow> imp_prog \<Rightarrow> check_report_entry list" where
  "interval_check_report gs mnm p =
     classify_checks (prog_cfg mnm p)
       (\<lambda>v. case_lifted bot (\<lambda>\<sigma>. \<sigma>) (ivl_exec_prog_at gs mnm p v))
       interval_classify_check"

text \<open>
  The definitional equation above unfolds \<^const>\<open>ivl_exec_prog_at\<close> at every
  check node, and that unfolding re-invokes \<^const>\<open>ivl_exec_raw\<close> (the
  actual solver run) each time --- so naive code generation would re-run the
  whole D/G solver once per check, for an \<open>N\<close>-check program, \<open>N\<close> solver
  runs instead of one. The \<open>[code]\<close> equation below is provably equal (a
  direct \<open>Let\<close>-unfold of the same definitions) but binds
  \<^term>\<open>ivl_exec_raw (resolved_st_q_is_bot_for (declared_global_vars p)) gs
        (prog_table p) (prog_procs p) mnm (prog_main p)\<close>
  once, outside the per-check closure \<^const>\<open>classify_checks\<close> applies; the
  target language compiles that \<open>let\<close> to a single shared thunk, so the
  generated OCaml computes the solved system exactly once per
  report, regardless of how many checks the program has. Mirrors the
  \<open>analyse_sign_report_for_code\<close> fix for the Sign counterpart of this
  report (\<open>Sign_Codegen\<close>, downstream of this theory).
\<close>

declare interval_check_report_def [code del]

lemma interval_check_report_code [code]:
  "interval_check_report gs mnm p =
     (let raw = ivl_exec_raw (resolved_st_q_is_bot_for (declared_global_vars p)) gs
                  (prog_table p) (prog_procs p) mnm (prog_main p)
      in classify_checks (prog_cfg mnm p)
           (\<lambda>v. case_lifted bot (\<lambda>\<sigma>. \<sigma>)
                  (side_env_lift_st gs (raw (Inl v)) (raw (Inr ()))))
           interval_classify_check)"
  unfolding interval_check_report_def ivl_exec_prog_at_def[abs_def] ivl_exec_at_def[abs_def] Let_def
            side_env_lift_st_eq_side_env_lift
  by (rule refl)

subsection \<open>Solved-result table\<close>

text \<open>
  \<open>analyse_interval_td_result_for\<close> is the canonical solved D/G system under
  the Apinis warrowing update rule (Interval's infinite-height local
  lattice needs it for termination), read as a
  \<^typ>\<open>(unit, ivl abs_state) analysis_result\<close>: a one-line partial
  application of \<open>monovariant_analysis_result_for\<close>
  (\<open>Monovariant_Analysis_Result.thy\<close>), mirroring \<open>Sign_Checks\<close>'s own
  \<open>analyse_sign_result_for\<close>. Every report below reads through a result
  table via \<^const>\<open>lookup_context\<close> rather than a raw solver-environment
  lookup.
\<close>

definition analyse_interval_td_result_for ::
    "(vname \<Rightarrow> bool) \<Rightarrow> imp_prog \<Rightarrow> (unit, ivl abs_state) analysis_result" where
  "analyse_interval_td_result_for gs p =
     monovariant_analysis_result_for
       (\<lambda>gs p. analyse_interval_dg_for (resolved_st_q_is_bot_for (declared_global_vars p)) gs p) gs p"

text \<open>Convenience instance at \<^const>\<open>declared_global\<close> \<open>p\<close>, matching
  \<open>analyse_interval_td_report\<close>'s shape.\<close>

definition analyse_interval_td_result ::
    "imp_prog \<Rightarrow> (unit, ivl abs_state) analysis_result" where
  "analyse_interval_td_result p = analyse_interval_td_result_for (declared_global p) p"

subsection \<open>Solved-result table: always-join update rule\<close>

text \<open>
  \<open>analyse_interval_join_result\<close> is \<^const>\<open>analyse_interval_td_result\<close>'s
  sibling under the always-join update rule: the same
  \<open>monovariant_analysis_result_for\<close> partial application, reading
  \<^const>\<open>analyse_interval_dg_join_for\<close> instead of \<^const>\<open>analyse_interval_dg_for\<close>.
\<close>

definition analyse_interval_join_result_for ::
    "(vname \<Rightarrow> bool) \<Rightarrow> imp_prog \<Rightarrow> (unit, ivl abs_state) analysis_result" where
  "analyse_interval_join_result_for gs p =
     monovariant_analysis_result_for
       (\<lambda>gs p. analyse_interval_dg_join_for (resolved_st_q_is_bot_for (declared_global_vars p)) gs p) gs p"

definition analyse_interval_join_result ::
    "imp_prog \<Rightarrow> (unit, ivl abs_state) analysis_result" where
  "analyse_interval_join_result p = analyse_interval_join_result_for (declared_global p) p"

subsection \<open>Solved-result table: per-origin update rule\<close>

text \<open>
  \<open>analyse_interval_per_origin_result\<close> mirrors
  \<open>analyse_interval_join_result\<close> exactly, reading
  \<^const>\<open>analyse_interval_dg_per_origin_for\<close> instead of
  \<^const>\<open>analyse_interval_dg_join_for\<close>.
\<close>

definition analyse_interval_per_origin_result_for ::
    "(vname \<Rightarrow> bool) \<Rightarrow> imp_prog \<Rightarrow> (unit, ivl abs_state) analysis_result" where
  "analyse_interval_per_origin_result_for gs p =
     monovariant_analysis_result_for
       (\<lambda>gs p. analyse_interval_dg_per_origin_for (resolved_st_q_is_bot_for (declared_global_vars p)) gs p) gs p"

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
  Convenience instance at \<^const>\<open>declared_global\<close> \<open>p\<close>, matching \<^const>\<open>analyse_interval\<close>'s shape.
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

text \<open>
  \<open>gamma_state_case_lifted\<close> stays: it is still the per-node soundness bridge for the older
  \<^const>\<open>ivl_exec_prog_at\<close>/\<^const>\<open>interval_check_report\<close> pipeline, which remains load-bearing for
  the entry-state context analysis and \<open>Example_Interval_Checks_Store_Only\<close>'s own worked example
  --- only the reports above moved off that pipeline, not \<^const>\<open>interval_check_report\<close> or its
  callers.
\<close>

lemma gamma_state_case_lifted:
  fixes x :: "'a::sound_domain abs_state lifted"
  shows "gamma_state (case_lifted bot (\<lambda>\<sigma>. \<sigma>) x) = gamma_state_lift x"
  by (cases x) (simp_all add: gamma_state_bot)

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

end



