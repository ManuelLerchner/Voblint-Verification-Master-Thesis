theory Sign_Checks
  imports Sign_Numeric_Queries "Voblint_Core.Abstract_Checks"
    "Voblint_Core.Analysis_Result" Sign_Exec_Sound
    "Voblint_Analysis.Monovariant_Analysis_Result"
    "Voblint_Core.DG_Analysis_Adapter"
    Sign_Exec_Ctx_Sound
begin

hide_const phase.N

section \<open>Sign instance of the generic check-discharge interface\<close>

text \<open>
  Only composition lives here: the Sign lattice comparison tables
  (\<open>sign_less_true\<close>/\<open>sign_less_false\<close>/\<open>sign_eq_true\<close>/\<open>sign_eq_false\<close>) and their
  \<^theory>\<open>Voblint_Analysis.Sign_Numeric_Queries\<close> interpretation of
  \<open>abstract_numeric_queries\<close> live in that theory. The Sign expression
  evaluator \<open>aval_sign\<close> lives in \<^theory>\<open>Voblint_Analysis.Sign_Arithmetic\<close>. The
  Boolean recursion over \<^typ>\<open>exp\<close> (\<open>Not\<close>, \<open>And\<close>, \<open>Or\<close>), the three-way
  classification, and the node-indexed bridge to \<^const>\<open>checks_proven\<close> come
  from interpreting \<open>abstract_check_domain\<close> (\<^theory>\<open>Voblint_Core.Abstract_Checks\<close>)
  once, below, reusing the numeric-query facts already proved sound in
  \<open>sign_numeric_queries\<close> rather than re-deriving the comparison tables ---
  the same way \<open>sign_backward_domain\<close> in \<open>Sign_Backward.thy\<close> interprets
  \<open>backward_domain\<close> for guard narrowing.
\<close>

global_interpretation sign_check_domain:
  abstract_check_domain gamma_sign sign_less_true sign_less_false sign_eq_true sign_eq_false
    gamma_state aval_sign
  defines
    sign_check_true = sign_check_domain.check_true
    and sign_check_false = sign_check_domain.check_false
    and sign_classify_check = sign_check_domain.classify_check
    and sign_checks_proven = sign_check_domain.abstract_checks_proven
proof unfold_locales
  fix s :: store and e :: exp and \<sigma> :: "sign abs_state"
  assume "s \<in> \<lbrakk>\<sigma>\<rbrakk>"
  then have "\<forall>x. s x \<in> gamma (\<sigma> x)" by (rule gamma_stateD)
  then have "\<forall>x. s x \<in> gamma_sign (\<sigma> x)" by simp
  then show "aval e s \<in> gamma_sign (aval_sign e \<sigma>)" using aval_sign_sound by blast
qed

text \<open>
  Only the consumer-facing aliases get a short Sign-prefixed name:
  \<open>classify_check\<close>'s two directions and the \<open>checks_proven\<close> bridge, both
  exercised below and by \<open>Example_Checks_Store_Only\<close>.
  \<open>sign_check_domain.check_true_sound\<close>/\<open>check_false_sound\<close>/
  \<open>check_true_false_vacuous\<close> are the lower-level facts \<open>classify_check\<close>'s
  own soundness is built from; no caller needs them directly, so they stay
  reachable under the qualified \<open>sign_check_domain.\<close> name instead of a
  dedicated alias here.
\<close>

lemmas sign_classify_check_proved = sign_check_domain.classify_check_proved
lemmas sign_classify_check_refuted = sign_check_domain.classify_check_refuted
lemmas sign_checks_provenI = sign_check_domain.abstract_checks_provenI
lemmas sign_checks_proven_sound = sign_check_domain.abstract_checks_proven_sound

subsection \<open>The generic report adapter, at the routed-unit context\<close>

text \<open>
  Interpreting \<^locale>\<open>dg_analysis_adapter\<close> at \<open>Sign_Exec_Ctx_Sound\<close>'s own routed-unit
  solved system reuses every obligation that theory's own \<open>sctx_dg\<close>/\<open>sctx_routed\<close>
  interpretations already discharge: the five \<^locale>\<open>dg_ctx_activation_base\<close> obligations
  are exactly \<open>sctx_dg\<close>'s own (cited here via the exported \<open>sctx_pp_abs\<close>/\<open>sctx_sg_covered\<close>/
  \<open>sctx_sg_uncovered_empty\<close>/\<open>sctx_fin\<close>), and the routed obligations collapse the same way
  \<^locale>\<open>unit_routed_context\<close>'s did, at \<^const>\<open>route_unit\<close>/\<^const>\<open>enterc_unit\<close>. Only
  \<open>classify_proved\<close>/\<open>classify_refuted\<close> are genuinely new here, discharged by
  \<open>sign_classify_check_proved\<close>/\<open>sign_classify_check_refuted\<close> above. This context re-opens
  \<open>Sign_Exec_Ctx_Sound\<close>'s own six coverage hypotheses (\<open>solves\<close>/\<open>exact\<close>/\<open>entry_cov\<close>/
  \<open>fwd_ok\<close>/\<open>call_fwd_ok\<close>/\<open>comb_fwd_ok\<close>) rather than reusing that theory's context directly,
  since the classify obligations need \<open>sign_classify_check_proved\<close>/\<open>sign_classify_check_refuted\<close>,
  which live in this theory, downstream of \<open>Sign_Exec_Ctx_Sound\<close>.
\<close>

context
  fixes gs :: "vname \<Rightarrow> bool" and is_bot_pred :: "sign exec_dg_st \<Rightarrow> bool"
    and Pi :: proc_table and ps :: "pname list" and mnm :: pname and main :: com
  assumes solves: "sctx_terminates gs is_bot_pred Pi ps mnm main"
    and exact: "\<And>s. is_bot_pred s = is_bot_state (fun_of_resolved_st_q_for gs s)"
    and entry_cov: "(cfg_entry (compile_prog Pi ps mnm main), ()) \<in> fst (sctx_sol gs is_bot_pred Pi ps mnm main)"
    and fwd_ok: "\<And>u a v ctx. (u, ctx) \<in> fst (sctx_sol gs is_bot_pred Pi ps mnm main)
                   \<Longrightarrow> (u, a, v) \<in> intra (compile_prog Pi ps mnm main)
                   \<Longrightarrow> (v, ctx) \<in> fst (sctx_sol gs is_bot_pred Pi ps mnm main)"
    and call_fwd_ok: "\<And>u ctx dst pars args p cont.
        (u, ctx) \<in> fst (sctx_sol gs is_bot_pred Pi ps mnm main)
        \<Longrightarrow> (u, CallEdge dst pars args, FunctionEntry p, cont) \<in> calls (compile_prog Pi ps mnm main)
        \<Longrightarrow> (FunctionEntry p, ()) \<in> fst (sctx_sol gs is_bot_pred Pi ps mnm main)"
    and comb_fwd_ok: "\<And>cl c1 dst pars args p cont.
        (cl, c1) \<in> fst (sctx_sol gs is_bot_pred Pi ps mnm main)
        \<Longrightarrow> (cl, CallEdge dst pars args, FunctionEntry p, cont) \<in> calls (compile_prog Pi ps mnm main)
        \<Longrightarrow> (cont, c1) \<in> fst (sctx_sol gs is_bot_pred Pi ps mnm main)"
begin

interpretation sctx_dg_base: sound_dg_spec "sctx_abs_spec gs" gamma_dg_base gs
  unfolding sctx_abs_spec_def
  by (rule base_dg_spec_sound[OF sign_is_sound_transfer_for is_bot_state_gamma_state_empty])

interpretation sctx_adapter: dg_analysis_adapter enterc_unit "sctx_abs_spec gs" gs
    "compile_prog Pi ps mnm main" Global route_unit
    "map_lift (fun_of_resolved_st_q_for gs) (Bot::sign exec_dg_st lifted)"
    "map_lift (fun_of_resolved_st_q_for gs) (Lifted cinit_sign_st)"
    "map_lift (fun_of_resolved_st_q_for gs) (Bot::sign exec_dg_st lifted)"
    "sctx_sigma_abs gs is_bot_pred Pi ps mnm main" "fst (sctx_sol gs is_bot_pred Pi ps mnm main)"
    "(cfg_exit (compile_prog Pi ps mnm main), ())" "sctx_sg gs is_bot_pred Pi ps mnm main"
    Seed sign_classify_check
proof (unfold_locales, goal_cases FinE PP SgCov SgUncov Fwd FinC SeedKey RouteEnterc CallFwd CombFwd EnterAgree ClProved ClRefuted)
  case FinE show ?case
    using compile_prog_finite by auto
next
  case PP show ?case
    by (simp only: sctx_sigma_abs_def[OF solves exact entry_cov fwd_ok call_fwd_ok comb_fwd_ok]
        sctx_sigma_abs_exec_def)
      (rule sctx_pp_abs[OF solves exact])
next
  case (SgCov v c)
  note mem = this
  have eq1: "sctx_sg gs is_bot_pred Pi ps mnm main (Inl (v, c))
               = locals (sctx_sigma_abs gs is_bot_pred Pi ps mnm main (Inl (v, c)))"
    by (rule sctx_sg_covered[OF solves exact entry_cov fwd_ok call_fwd_ok comb_fwd_ok mem])
  show ?case
    using eq1 gamma_dg_base_def by auto
next
  case (SgUncov v c)
  note nmem = this
  show ?case
    by (rule sctx_sg_uncovered_empty[OF solves exact entry_cov fwd_ok call_fwd_ok comb_fwd_ok nmem])
next
  case (Fwd u a v c)
  thus ?case by (rule fwd_ok)
next
  case FinC show ?case
    by (simp add: compile_prog_finite)
next
  case (SeedKey p ctx) show ?case by simp
next
  case (RouteEnterc u ctx dst pars args p cont s)
  show ?case by (simp add: route_unit_def enterc_unit_def)
next
  case (CallFwd u ctx dst pars args p cont)
  show ?case
    using CallFwd(1,2) call_fwd_ok unfolding route_unit_def by blast
next
  case (CombFwd cl c1 dst pars args p cont)
  show ?case using CombFwd(1,2) comb_fwd_ok by blast
next
  case (EnterAgree cl s es dst pars args p cont)
  note ces = EnterAgree(1) and ce = EnterAgree(2)
  obtain dst' pars' args' p' cont' where
      ce': "(cl, CallEdge dst' pars' args', FunctionEntry p', cont') \<in> calls (compile_prog Pi ps mnm main)"
    and es_eq: "es = call_enter gs (CallEdge dst' pars' args') s"
    using ces unfolding call_enter_store_def by blast
  have "CallEdge dst' pars' args' = CallEdge dst pars args"
    using compile_prog_calls_source_unique[OF ce' ce] by simp
  thus ?case using es_eq by simp
next
  case (ClProved c d s)
  thus ?case by (rule sign_classify_check_proved)
next
  case (ClRefuted c d s)
  thus ?case by (rule sign_classify_check_refuted)
qed

text \<open>
  The two generic soundness corollaries \<^locale>\<open>dg_analysis_adapter\<close> derives once and for
  all, re-exported here so a caller cites them without naming the interpretation.
\<close>

lemmas sctx_report_ctx_proved_sound = sctx_adapter.analyse_report_ctx_proved_sound
lemmas sctx_report_ctx_refuted_sound = sctx_adapter.analyse_report_ctx_refuted_sound

end

subsection \<open>Executable classification tests\<close>

text \<open>One state per test, built as an override of an otherwise-unconstrained
  (\<open>STop\<close>) environment, so each test exercises exactly the comparison it names.\<close>

definition test_env_pos :: "sign abs_state" where
  "test_env_pos = (\<lambda>_. STop)((STR ''x'') := SPos)"

lemma sign_classify_less_proved:
  "sign_classify_check (Less (N 0) (V (STR ''x''))) test_env_pos = Check_Proved"
  unfolding test_env_pos_def by eval

lemma sign_classify_less_refuted:
  "sign_classify_check (Less (V (STR ''x'')) (N 0)) test_env_pos = Check_Refuted"
  unfolding test_env_pos_def by eval

lemma sign_classify_eq_unknown:
  "sign_classify_check (Eq (V (STR ''x'')) (N 1)) test_env_pos = Check_Unknown"
  unfolding test_env_pos_def by eval

text \<open>Negation: \<open>!(x < 0)\<close> is provable under \<open>SNonNeg\<close>, going through
  \<open>check_false\<close> on the un-negated \<open>x < 0\<close> rather than a one-sided
  negation of \<open>check_true\<close>.\<close>

definition test_env_nonneg :: "sign abs_state" where
  "test_env_nonneg = (\<lambda>_. STop)((STR ''x'') := SNonNeg)"

lemma sign_classify_not_proved:
  "sign_classify_check (Not (Less (V (STR ''x'')) (N 0))) test_env_nonneg = Check_Proved"
  unfolding test_env_nonneg_def by eval

text \<open>Nested \<open>And\<close>/\<open>Or\<close>: proved through the \<open>And\<close> branch alone, and unknown
  when neither branch resolves.\<close>

definition test_env_nested_proved :: "sign abs_state" where
  "test_env_nested_proved = (\<lambda>_. STop)((STR ''x'') := SPos, (STR ''y'') := SPos)"

lemma sign_classify_nested_proved:
  "sign_classify_check
     (Or (And (Less (N 0) (V (STR ''x''))) (Less (N 0) (V (STR ''y'')))) (Eq (V (STR ''z'')) (N 1)))
     test_env_nested_proved = Check_Proved"
  unfolding test_env_nested_proved_def by eval

definition test_env_nested_unknown :: "sign abs_state" where
  "test_env_nested_unknown = (\<lambda>_. STop)((STR ''x'') := SNonNeg, (STR ''y'') := SPos)"

lemma sign_classify_nested_unknown:
  "sign_classify_check
     (Or (And (Less (N 0) (V (STR ''x''))) (Less (N 0) (V (STR ''y'')))) (Eq (V (STR ''z'')) (N 1)))
     test_env_nested_unknown = Check_Unknown"
  unfolding test_env_nested_unknown_def by eval

subsection \<open>Whole-program check report\<close>

text \<open>
  Thin composition, not a restatement: \<^const>\<open>classify_checks\<close> already owns
  the executable traversal and ordering, \<^const>\<open>sign_exec_prog_at\<close> already
  owns the node-indexed Sign environment, and \<open>sign_classify_check\<close> above
  already owns the per-check classification. This wrapper only feeds a
  compiled program's own three projections through them, the same way
  \<^const>\<open>sign_exec_prog\<close> feeds them through \<^const>\<open>sign_exec_at\<close>.
\<close>

definition sign_check_report ::
    "(vname \<Rightarrow> bool) \<Rightarrow> pname \<Rightarrow> imp_prog \<Rightarrow> check_report_entry list" where
  "sign_check_report gs mnm p =
     classify_checks (prog_cfg mnm p)
       (\<lambda>v. case_lifted bot (\<lambda>\<sigma>. \<sigma>) (sign_exec_prog_at gs mnm p v))
       sign_classify_check"

subsection \<open>Solved-result table\<close>

text \<open>
  \<open>analyse_sign_result_for\<close> is the canonical solved D/G system, read as a
  \<^typ>\<open>(unit, sign abs_state) analysis_result\<close>: a one-line partial
  application of \<open>monovariant_analysis_result_for\<close>
  (\<open>Monovariant_Analysis_Result.thy\<close>), which already binds the single
  solve and canonicalizes/normalizes each local key -- see that theory for
  why no separate \<open>[code]\<close> single-solve rewrite is needed here. Every
  report below reads through this table via \<^const>\<open>lookup_context\<close> rather
  than a raw solver-environment lookup.
\<close>

definition analyse_sign_result_for ::
    "(vname \<Rightarrow> bool) \<Rightarrow> imp_prog \<Rightarrow> (unit, sign abs_state) analysis_result" where
  "analyse_sign_result_for gs p =
     monovariant_analysis_result_for
       (\<lambda>gs p. analyse_sign_for (resolved_st_q_is_bot_for (declared_global_vars p)) gs p) gs p"

text \<open>Convenience instance at \<^const>\<open>declared_global\<close> \<open>p\<close>, matching
  \<open>analyse_sign_report\<close>'s shape.\<close>

definition analyse_sign_result :: "imp_prog \<Rightarrow> (unit, sign abs_state) analysis_result" where
  "analyse_sign_result p = analyse_sign_result_for (declared_global p) p"

subsection \<open>Solved-result table: per-origin update rule\<close>

text \<open>
  \<open>analyse_sign_for_per_origin\<close> solves under the per-origin update rule
  (\<^const>\<open>TD_side_per_origin_Interp_solve\<close>, keeping each write origin's
  contribution separate instead of folding every contribution into one
  join) instead of the always-join rule production uses. Experimental: no
  dedicated soundness theorem is proved for this combination here --
  \<open>analyse\<close> and its soundness corollaries are unaffected, and this
  definition exists solely so \<open>Analyse_Dispatch\<close>'s \<open>analyse_with_solver\<close>
  can compare solver choices on the same equation system (issue #131).

  \<open>analyse_sign_result_per_origin\<close> is \<^const>\<open>analyse_sign_result\<close>'s sibling
  under this rule: the same \<open>monovariant_analysis_result_for\<close> partial
  application, reading \<open>analyse_sign_for_per_origin\<close> instead of
  \<^const>\<open>analyse_sign_for\<close>.
\<close>

definition analyse_sign_for_per_origin ::
    "(vname \<Rightarrow> bool) \<Rightarrow> imp_prog \<Rightarrow>
       (pp \<times> unit) set \<times> (pp \<times> unit + unit \<Rightarrow> (sign exec_dg_st lifted, sign exec_dg_st lifted) dg_state)" where
  "analyse_sign_for_per_origin gs p =
     TD_side_per_origin_Interp_solve (analyse_sign_eqs_for (resolved_st_q_is_bot_for (declared_global_vars p)) gs p)
       (cfg_exit (prog_cfg prog_main_name p), ())"

definition analyse_sign_result_per_origin_for ::
    "(vname \<Rightarrow> bool) \<Rightarrow> imp_prog \<Rightarrow> (unit, sign abs_state) analysis_result" where
  "analyse_sign_result_per_origin_for gs p =
     monovariant_analysis_result_for analyse_sign_for_per_origin gs p"

definition analyse_sign_result_per_origin :: "imp_prog \<Rightarrow> (unit, sign abs_state) analysis_result" where
  "analyse_sign_result_per_origin p = analyse_sign_result_per_origin_for (declared_global p) p"

subsection \<open>Whole-program check report: the native D/G runtime API\<close>

text \<open>
  \<open>analyse_sign_report_for\<close> is the report function the exported \<open>analyse\<close>
  API actually dispatches to (see \<open>Analyse_Dispatch\<close>, downstream in
  Examples), fixed at \<open>prog_main_name\<close> since \<^const>\<open>analyse_sign_result_for\<close>
  already is. It reads its per-node state through
  \<^const>\<open>analyse_sign_result_for\<close>'s \<^type>\<open>analysis_result\<close> table --
  \<^const>\<open>lookup_context\<close>, not a raw solver-environment lookup -- so a
  \<^const>\<open>Reachable\<close> point classifies at its projected state exactly as
  before, and an \<^const>\<open>Unreachable\<close> one (dead or never covered; the two are
  no longer distinguishable, matching \<^const>\<open>classify_checks\<close>'s original
  \<^const>\<open>Bot\<close>-collapsing \<open>env\<close> reads) classifies at \<^const>\<open>bot\<close>, the same
  value \<^const>\<open>classify_checks\<close> always fed it for such a node: this
  preserves \<open>check_result\<close>'s existing three-way verdict exactly, rather
  than introducing a fourth, \<open>Dead\<close> outcome the type does not carry (that
  distinction belongs to \<^const>\<open>classify_checks_verdicts\<close>/\<open>contextual_verdict\<close>,
  the shape the entry-state check report already uses).

  \<open>r\<close> is bound once, outside \<^const>\<open>classify_checks\<close>'s per-check closure, so
  the single D/G solve \<^const>\<open>analyse_sign_result_for\<close> performs is shared
  across every check in the report rather than repeated per check.
\<close>

definition analyse_sign_report_for :: "(vname \<Rightarrow> bool) \<Rightarrow> imp_prog \<Rightarrow> check_report_entry list" where
  "analyse_sign_report_for gs p =
     (let r = analyse_sign_result_for gs p
      in classify_checks (prog_cfg prog_main_name p)
           (\<lambda>v. case lookup_context r v () of Unreachable \<Rightarrow> bot | Reachable st \<Rightarrow> st)
           sign_classify_check)"

text \<open>
  Convenience instance at \<^const>\<open>declared_global\<close> \<open>p\<close>, matching \<^const>\<open>analyse_sign\<close>'s shape.
\<close>

definition analyse_sign_report :: "imp_prog \<Rightarrow> check_report_entry list" where
  "analyse_sign_report p = analyse_sign_report_for (declared_global p) p"

subsection \<open>Solver-choice variant report: per-origin update rule\<close>

text \<open>
  \<open>analyse_sign_report_per_origin\<close>'s sibling relationship to
  \<^const>\<open>analyse_sign_report\<close> mirrors \<^const>\<open>analyse_sign_result_per_origin\<close>'s
  to \<^const>\<open>analyse_sign_result\<close>: same report shape, reading through the
  per-origin result table instead of the default one.
\<close>

definition analyse_sign_report_per_origin :: "imp_prog \<Rightarrow> check_report_entry list" where
  "analyse_sign_report_per_origin p =
     (let r = analyse_sign_result_per_origin p
      in classify_checks (prog_cfg prog_main_name p)
           (\<lambda>v. case lookup_context r v () of Unreachable \<Rightarrow> bot | Reachable st \<Rightarrow> st)
           sign_classify_check)"

subsection \<open>Whole-program check report with state\<close>

text \<open>
  State-carrying sibling of \<open>analyse_sign_report_for\<close>/\<open>analyse_sign_report\<close>,
  via \<^const>\<open>classify_checks_with_state\<close>: same result table, with the
  per-check Sign environment attached to each report entry instead of
  discarded, and an exact \<open>unreachable\<close> flag read straight off
  \<^const>\<open>lookup_context\<close>'s \<^const>\<open>Unreachable\<close>/\<^const>\<open>Reachable\<close> case split --
  exact because \<open>normalize_point_canonicalize_lift_eq_old\<close>
  (\<^theory>\<open>Voblint_Core.Analysis_Result\<close>) is precisely the fact that this
  reading agrees with the older \<^const>\<open>resolved_st_q_lifted_is_bot_for\<close>
  test on the same raw local unknown.
\<close>

definition analyse_sign_report_for_with_state ::
    "(vname \<Rightarrow> bool) \<Rightarrow> imp_prog \<Rightarrow> (pp \<times> exp \<times> check_result \<times> bool \<times> (vname \<Rightarrow> sign)) list" where
  "analyse_sign_report_for_with_state gs p =
     (let r = analyse_sign_result_for gs p
      in classify_checks_with_state (prog_cfg prog_main_name p)
           (\<lambda>v. case lookup_context r v () of
                  Unreachable \<Rightarrow> (True, bot)
                | Reachable st \<Rightarrow> (False, st))
           (\<lambda>c (_, s). sign_classify_check c s))"

text \<open>Convenience instance at \<^const>\<open>declared_global\<close> \<open>p\<close>, matching
  \<open>analyse_sign_report\<close>'s shape.\<close>

definition analyse_sign_report_with_state ::
    "imp_prog \<Rightarrow> (pp \<times> exp \<times> check_result \<times> bool \<times> (vname \<Rightarrow> sign)) list" where
  "analyse_sign_report_with_state p = analyse_sign_report_for_with_state (declared_global p) p"

end

