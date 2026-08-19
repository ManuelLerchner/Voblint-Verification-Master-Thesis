theory Interval_Checks
  imports Interval_Numeric_Queries Interval_Backward "Voblint_Core.Abstract_Checks"
    "Voblint_Core.Analysis_Result" Interval_Exec_Sound
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
  report (\<open>Example_Sign_Codegen\<close>, downstream of this theory).
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

text \<open>
  \<open>analyse_interval_report_for\<close> mirrors \<open>analyse_interval_td_report_for\<close> exactly, reading through
  \<^const>\<open>analyse_interval_dg_join_env_for\<close> (the native D/G pipeline under the always-join update
  rule, \<^theory>\<open>Voblint_Analysis.Interval_Exec_Sound\<close>) instead of \<^const>\<open>analyse_interval_dg_env_for\<close>
  (Apinis warrowing) --- this is the report function the exported \<open>analyse_with_solver\<close> API
  dispatches to for \<open>Interval_Analysis\<close>/\<open>Solver_Join\<close> (\<open>Analyse_Dispatch\<close>, downstream in
  Examples), not Interval's production default (\<open>analyse\<close>/\<open>analyse_with_solver Interval_Analysis
  Solver_Warrow\<close> both still dispatch to \<open>analyse_interval_td_report\<close>): plain join has no widening,
  so it lacks warrowing's termination guarantee on a genuine local loop with unbounded growth.
  This route exists so \<open>analyse_with_solver\<close> can compare update rules on the identical equation
  system (issue #131), mirroring Sign's own always-join default (\<open>Sign_Checks.analyse_sign_report\<close>).
\<close>

definition analyse_interval_report_for :: "(vname \<Rightarrow> bool) \<Rightarrow> imp_prog \<Rightarrow> check_report_entry list" where
  "analyse_interval_report_for gs p =
     classify_checks (prog_cfg prog_main_name p)
       (analyse_interval_dg_join_env_for (resolved_st_q_is_bot_for (declared_global_vars p)) gs p)
       interval_classify_check"

text \<open>
  Same single-solve-per-report fix as \<open>analyse_interval_td_report_for_code\<close>: bind
  \<^term>\<open>snd (analyse_interval_dg_join_for (resolved_st_q_is_bot_for (declared_global_vars p)) gs p)\<close>
  once, outside \<^const>\<open>classify_checks\<close>'s per-check closure, so the generated OCaml solves the
  D/G equation system exactly once per report rather than once per check.
\<close>

declare analyse_interval_report_for_def [code del]

lemma analyse_interval_report_for_code [code]:
  "analyse_interval_report_for gs p =
     (let sol = snd (analyse_interval_dg_join_for (resolved_st_q_is_bot_for (declared_global_vars p)) gs p)
      in classify_checks (prog_cfg prog_main_name p)
           (\<lambda>v. case map_lift (fun_of_exec_dg_st_for gs) (locals (sol (Inl (v, ()))))
                of Bot \<Rightarrow> bot | Lifted s \<Rightarrow> s)
           interval_classify_check)"
  unfolding analyse_interval_report_for_def analyse_interval_dg_join_env_for_def[abs_def] Let_def
  by (rule refl)

text \<open>
  Convenience instance at \<^const>\<open>declared_global\<close> \<open>p\<close>, matching \<open>analyse_interval_td_report\<close>'s
  shape. Soundness (\<open>analyse_interval_report_sound_proved\<close>/\<open>_refuted\<close>) needs the
  \<open>base_dg_exec_analysis\<close> locale interpretation, one session later than Analysis in the locked
  six-session chain, so it stays downstream in \<open>Example_Interval_Codegen\<close> (Examples), mirroring
  the same split \<open>analyse_interval_td_report\<close> (below) and \<open>Sign_Checks\<close>/\<open>Example_Sign_Codegen\<close> use.
\<close>

definition analyse_interval_report :: "imp_prog \<Rightarrow> check_report_entry list" where
  "analyse_interval_report p = analyse_interval_report_for (declared_global p) p"

text \<open>
  \<open>gamma_state_case_lifted\<close> stays: it is still the per-node soundness bridge for the older
  \<^const>\<open>ivl_exec_prog_at\<close>/\<^const>\<open>interval_check_report\<close> pipeline, which remains load-bearing for
  the entry-state context analysis and \<open>Example_Interval_Checks_Store_Only\<close>'s own worked example
  --- only \<open>analyse_interval_report\<close> itself moved off that pipeline, not
  \<^const>\<open>interval_check_report\<close> or its callers.
\<close>

lemma gamma_state_case_lifted:
  fixes x :: "'a::sound_domain abs_state lifted"
  shows "gamma_state (case_lifted bot (\<lambda>\<sigma>. \<sigma>) x) = gamma_state_lift x"
  by (cases x) (simp_all add: gamma_state_bot)

subsection \<open>Whole-program check report: the native D/G runtime API\<close>

text \<open>
  \<open>analyse_interval_td_report_for\<close> mirrors \<open>interval_check_report\<close> exactly, reading through
  \<^const>\<open>analyse_interval_dg_env_for\<close> (the native D/G pipeline, warrowing-backed for
  termination on Interval's infinite-height local lattice) instead of \<^const>\<open>ivl_exec_prog_at\<close>
  (the always-join, VIMP-global-split \<open>side_cfg_T_eff_st\<close> pipeline) --- this is the report
  function the exported \<open>analyse\<close> API actually dispatches to for \<open>Interval_Analysis\<close> (see
  \<open>Analyse_Dispatch\<close>, downstream in Examples), fixed at \<open>prog_main_name\<close> rather than an
  arbitrary \<open>mnm\<close> since \<^const>\<open>analyse_interval_dg_env_for\<close> already is, mirroring
  \<open>Sign_Checks\<close>'s \<open>analyse_sign_report_for\<close>. Reusing the exact same warrowing/\<open>analyse_interval_td\<close>
  naming keeps the still-live \<open>analyse_interval_td_at\<close>/\<open>analyse_interval_td_terminates\<close> family
  (the entry-state context analysis, the GraphViz state-report tooling) fully unchanged: only
  this report's own definition is repointed onto the new pipeline.
\<close>

definition analyse_interval_td_report_for :: "(vname \<Rightarrow> bool) \<Rightarrow> imp_prog \<Rightarrow> check_report_entry list" where
  "analyse_interval_td_report_for gs p =
     classify_checks (prog_cfg prog_main_name p)
       (analyse_interval_dg_env_for (resolved_st_q_is_bot_for (declared_global_vars p)) gs p)
       interval_classify_check"

text \<open>
  Same single-solve-per-report fix as \<open>analyse_sign_report_for_code\<close>: bind
  \<^term>\<open>snd (analyse_interval_dg_for (resolved_st_q_is_bot_for (declared_global_vars p)) gs p)\<close>
  once, outside \<^const>\<open>classify_checks\<close>'s per-check closure, so the generated OCaml solves the
  D/G equation system exactly once per report rather than once per check.
\<close>

declare analyse_interval_td_report_for_def [code del]

lemma analyse_interval_td_report_for_code [code]:
  "analyse_interval_td_report_for gs p =
     (let sol = snd (analyse_interval_dg_for (resolved_st_q_is_bot_for (declared_global_vars p)) gs p)
      in classify_checks (prog_cfg prog_main_name p)
           (\<lambda>v. case map_lift (fun_of_exec_dg_st_for gs) (locals (sol (Inl (v, ()))))
                of Bot \<Rightarrow> bot | Lifted s \<Rightarrow> s)
           interval_classify_check)"
  unfolding analyse_interval_td_report_for_def analyse_interval_dg_env_for_def[abs_def] Let_def
  by (rule refl)

text \<open>
  Convenience instance at \<^const>\<open>declared_global\<close> \<open>p\<close>, matching \<^const>\<open>analyse_interval\<close>'s
  shape. Soundness (\<open>analyse_interval_td_report_sound_proved\<close>/\<open>_refuted\<close>) needs the
  \<open>base_dg_exec_analysis\<close> locale interpretation, one session later than Analysis in the locked
  six-session chain, so it stays downstream in \<open>Example_Interval_Codegen\<close> (Examples), mirroring
  \<open>Sign_Checks\<close>/\<open>Example_Sign_Codegen\<close>.
\<close>

definition analyse_interval_td_report :: "imp_prog \<Rightarrow> check_report_entry list" where
  "analyse_interval_td_report p = analyse_interval_td_report_for (declared_global p) p"

subsection \<open>Whole-program check report with state: the native D/G runtime API\<close>

text \<open>
  State-carrying sibling of \<open>analyse_interval_td_report_for\<close>/\<open>analyse_interval_td_report\<close>, via
  \<^const>\<open>classify_checks_with_state\<close>: same native D/G pipeline, same environment, with the
  per-check Interval environment attached to each report entry instead of discarded. The
  \<open>[code]\<close> rewrite mirrors the one above for the same single-solve-per-report reason.
\<close>

text \<open>
  Each entry also carries an exact \<open>unreachable\<close> flag,
  \<^const>\<open>resolved_st_q_lifted_is_bot_for\<close> read off the very same local unknown
  \<^const>\<open>analyse_interval_dg_env_for\<close> collapses to \<^term>\<open>bot\<close> --
  see \<open>analyse_sign_report_for_with_state\<close>'s Sign counterpart for the
  argument (solver-level \<open>Bot\<close> and a componentwise-bottom \<open>Lifted\<close> state
  both set it) and \<^theory>\<open>Voblint_Core.Exec_St\<close>'s
  \<open>resolved_st_q_lifted_is_bot_for_iff\<close> for the exactness.
\<close>

definition analyse_interval_td_report_for_with_state ::
    "(vname \<Rightarrow> bool) \<Rightarrow> imp_prog \<Rightarrow> (pp \<times> exp \<times> check_result \<times> bool \<times> ivl abs_state) list" where
  "analyse_interval_td_report_for_with_state gs p =
     classify_checks_with_state (prog_cfg prog_main_name p)
       (\<lambda>v. (resolved_st_q_lifted_is_bot_for (declared_global_vars p)
               (locals (snd (analyse_interval_dg_for (resolved_st_q_is_bot_for (declared_global_vars p)) gs p)
                          (Inl (v, ())))),
             analyse_interval_dg_env_for (resolved_st_q_is_bot_for (declared_global_vars p)) gs p v))
       (\<lambda>c (_, s). interval_classify_check c s)"

declare analyse_interval_td_report_for_with_state_def [code del]

lemma analyse_interval_td_report_for_with_state_code [code]:
  "analyse_interval_td_report_for_with_state gs p =
     (let sol = snd (analyse_interval_dg_for (resolved_st_q_is_bot_for (declared_global_vars p)) gs p)
      in classify_checks_with_state (prog_cfg prog_main_name p)
           (\<lambda>v. let st = locals (sol (Inl (v, ())))
                in (resolved_st_q_lifted_is_bot_for (declared_global_vars p) st,
                    case map_lift (fun_of_exec_dg_st_for gs) st of Bot \<Rightarrow> bot | Lifted s \<Rightarrow> s))
           (\<lambda>c (_, s). interval_classify_check c s))"
  unfolding analyse_interval_td_report_for_with_state_def analyse_interval_dg_env_for_def[abs_def] Let_def
  by (rule refl)

text \<open>Convenience instance at \<^const>\<open>declared_global\<close> \<open>p\<close>, matching
  \<open>analyse_interval_td_report\<close>'s shape.\<close>

definition analyse_interval_td_report_with_state ::
    "imp_prog \<Rightarrow> (pp \<times> exp \<times> check_result \<times> bool \<times> ivl abs_state) list" where
  "analyse_interval_td_report_with_state p = analyse_interval_td_report_for_with_state (declared_global p) p"

subsection \<open>Solver-choice variant: per-origin update rule\<close>

text \<open>
  \<open>analyse_interval_report_per_origin_for\<close> mirrors \<open>analyse_interval_report_for\<close> exactly, reading
  through \<^const>\<open>analyse_interval_dg_per_origin_env_for\<close> (the native D/G pipeline under the
  per-origin update rule, \<^theory>\<open>Voblint_Analysis.Interval_Exec_Sound\<close>) instead of
  \<^const>\<open>analyse_interval_dg_join_env_for\<close> --- keeping each write origin's contribution separate
  instead of folding every contribution into one join. Reuses
  \<^const>\<open>analyse_interval_dg_eqs_for\<close> unchanged, only the solve call differs; this definition
  exists so \<open>Analyse_Dispatch\<close>'s \<open>analyse_with_solver\<close> can compare update rules on the identical
  equation system (issue #131), the same role Sign's \<open>analyse_sign_report_per_origin\<close> plays there.
\<close>

definition analyse_interval_report_per_origin_for :: "(vname \<Rightarrow> bool) \<Rightarrow> imp_prog \<Rightarrow> check_report_entry list" where
  "analyse_interval_report_per_origin_for gs p =
     classify_checks (prog_cfg prog_main_name p)
       (analyse_interval_dg_per_origin_env_for (resolved_st_q_is_bot_for (declared_global_vars p)) gs p)
       interval_classify_check"

text \<open>Same single-solve-per-report fix as \<open>analyse_interval_report_for_code\<close>.\<close>

declare analyse_interval_report_per_origin_for_def [code del]

lemma analyse_interval_report_per_origin_for_code [code]:
  "analyse_interval_report_per_origin_for gs p =
     (let sol = snd (analyse_interval_dg_per_origin_for (resolved_st_q_is_bot_for (declared_global_vars p)) gs p)
      in classify_checks (prog_cfg prog_main_name p)
           (\<lambda>v. case map_lift (fun_of_exec_dg_st_for gs) (locals (sol (Inl (v, ()))))
                of Bot \<Rightarrow> bot | Lifted s \<Rightarrow> s)
           interval_classify_check)"
  unfolding analyse_interval_report_per_origin_for_def analyse_interval_dg_per_origin_env_for_def[abs_def] Let_def
  by (rule refl)

text \<open>Convenience instance at \<^const>\<open>declared_global\<close> \<open>p\<close>, matching \<open>analyse_interval_report\<close>'s
  shape; soundness (\<open>analyse_interval_report_per_origin_sound_proved\<close>/\<open>_refuted\<close>) stays downstream
  in \<open>Example_Interval_Codegen\<close> (Examples) for the same locale-interpretation reason.\<close>

definition analyse_interval_report_per_origin :: "imp_prog \<Rightarrow> check_report_entry list" where
  "analyse_interval_report_per_origin p =
     analyse_interval_report_per_origin_for (declared_global p) p"

subsection \<open>Solved-result table\<close>

text \<open>
  The same solved D/G system as \<^const>\<open>analyse_interval_td_report_for\<close>, read
  as a \<^typ>\<open>(unit, ivl abs_state) analysis_result\<close> instead of as a check
  report, mirroring \<open>Sign_Checks\<close>'s own \<open>analyse_sign_result_for\<close>: the
  covered local keys the solver already returns as the first component, and
  \<^const>\<open>normalize_point\<close> applied to each local unknown. Monovariant, so the
  context type is \<^typ>\<open>unit\<close>; only \<open>Inl\<close>-shaped local keys are covered, never
  the solver's own \<open>Inr\<close> global unknown.

  The \<open>[code]\<close> rewrite is the same single-solve fix as
  \<open>analyse_interval_td_report_for_code\<close>: binding \<open>sol\<close> once outside the
  per-key closure compiles to a single shared thunk, so a lookup never
  re-solves.
\<close>

definition analyse_interval_td_result_for ::
    "(vname \<Rightarrow> bool) \<Rightarrow> imp_prog \<Rightarrow> (unit, ivl abs_state) analysis_result" where
  "analyse_interval_td_result_for gs p =
     Analysis_Result
       (fst (analyse_interval_dg_for (resolved_st_q_is_bot_for (declared_global_vars p)) gs p))
       (\<lambda>v ctx. normalize_point (declared_global_vars p) gs
                  (locals (snd (analyse_interval_dg_for
                                  (resolved_st_q_is_bot_for (declared_global_vars p)) gs p)
                             (Inl (v, ctx)))))"

declare analyse_interval_td_result_for_def [code del]

lemma analyse_interval_td_result_for_code [code]:
  "analyse_interval_td_result_for gs p =
     (let sol = analyse_interval_dg_for (resolved_st_q_is_bot_for (declared_global_vars p)) gs p
      in Analysis_Result (fst sol)
           (\<lambda>v ctx. normalize_point (declared_global_vars p) gs
                      (locals (snd sol (Inl (v, ctx))))))"
  unfolding analyse_interval_td_result_for_def Let_def by (rule refl)

text \<open>Convenience instance at \<^const>\<open>declared_global\<close> \<open>p\<close>, matching
  \<open>analyse_interval_td_report\<close>'s shape.\<close>

definition analyse_interval_td_result ::
    "imp_prog \<Rightarrow> (unit, ivl abs_state) analysis_result" where
  "analyse_interval_td_result p = analyse_interval_td_result_for (declared_global p) p"

end
