theory Parity_Checks
  imports Parity_Numeric_Queries "Voblint_Core.Abstract_Checks" "Voblint_Core.Check_Report" Parity_Exec
    "Voblint_Core.Analysis_Result"
    "Voblint_Core.DG_Analysis_Adapter"
    "Voblint_Exec.Monovariant_Analysis_Result"
    Parity_Ctx_None_Sound
begin

hide_const phase.N

section \<open>Parity instance of the generic check-discharge interface\<close>

text \<open>
  Only composition lives here, exactly as Voblint_Analysis.Sign_Checks
  and Voblint_Analysis.Interval_Checks: the Parity lattice comparison
  tables (\<open>parity_less_true\<close>/\<open>parity_less_false\<close>/\<open>parity_eq_true\<close>/
  \<open>parity_eq_false\<close>) and their
  \<^theory>\<open>Voblint_Analysis.Parity_Numeric_Queries\<close> interpretation of
  \<open>abstract_numeric_queries\<close> live in that theory. The Parity expression
  evaluator \<open>aval_parity\<close> lives in \<^theory>\<open>Voblint_Analysis.Parity_Domain\<close>. The
  Boolean recursion over \<^typ>\<open>exp\<close>, the three-way classification, and the
  node-indexed bridge to \<^const>\<open>checks_proven\<close> come from interpreting
  \<open>abstract_check_domain\<close> (\<^theory>\<open>Voblint_Core.Abstract_Checks\<close>) once, below,
  reusing the numeric-query facts already proved sound in
  \<open>parity_numeric_queries\<close> --- no Boolean recursion or classification logic
  is restated.
\<close>

global_interpretation parity_check_domain:
  abstract_check_domain parity_less parity_eq gamma_state aval_parity
  defines
    parity_truthy_query = parity_check_domain.truthy_query
    and parity_check_query = parity_check_domain.check_query
    and parity_classify_check = parity_check_domain.classify_check
    and parity_checks_proven = parity_check_domain.abstract_checks_proven
proof unfold_locales
  fix s :: store and e :: exp and \<sigma> :: "parity abs_state"
  assume "s \<in> \<lbrakk>\<sigma>\<rbrakk>"
  then have "\<forall>x. s x \<in> gamma (\<sigma> x)" by blast
  then have "\<forall>x. s x \<in> gamma_parity (\<sigma> x)" by simp
  then show "aval e s \<in> gamma (aval_parity e \<sigma>)" using aval_parity_sound by fastforce
qed

text \<open>
  Only the consumer-facing aliases get a short Parity-prefixed name, matching
  Voblint_Analysis.Sign_Checks naming convention:
  \<open>classify_check\<close>'s two directions and the \<open>checks_proven\<close> bridge, both
  exercised below and by the worked check-discharge example. The lower-level
  facts \<open>classify_check\<close>'s own soundness is built from stay reachable under
  the qualified \<open>parity_check_domain.\<close> name.
\<close>

lemmas parity_classify_check_proved = parity_check_domain.classify_check_proved
lemmas parity_classify_check_refuted = parity_check_domain.classify_check_refuted
lemmas parity_checks_provenI = parity_check_domain.abstract_checks_provenI
lemmas parity_checks_proven_sound = parity_check_domain.abstract_checks_proven_sound

subsection \<open>Executable classification tests\<close>

text \<open>One state per test, built as an override of an otherwise-unconstrained
  (\<open>PTop\<close>) environment, so each test exercises exactly the comparison it
  names.\<close>

definition test_env_eo :: "parity abs_state" where
  "test_env_eo = (\<lambda>_. PTop)((STR ''x'') := PEven, (STR ''y'') := POdd)"

text \<open>Disjoint parity classes: the direct equality is refuted, and its
  negation is proved --- going through \<open>check_query\<close>'s \<open>Not\<close> case on the
  un-negated equality, not a one-sided reading of the positive answer.\<close>

lemma parity_classify_eq_refuted:
  "parity_classify_check (Eq (V (STR ''x'')) (V (STR ''y''))) test_env_eo = Check_Refuted"
  unfolding test_env_eo_def by eval

lemma parity_classify_not_eq_proved:
  "parity_classify_check (Not (Eq (V (STR ''x'')) (V (STR ''y'')))) test_env_eo = Check_Proved"
  unfolding test_env_eo_def by eval

text \<open>Same abstract value on both sides: \<open>x\<close> is \<open>PEven\<close> and the literal \<open>4\<close>
  is also \<open>PEven\<close>, but Parity has no singleton representation, so the
  equality stays unknown rather than falsely proved.\<close>

lemma parity_classify_eq_unknown:
  "parity_classify_check (Eq (V (STR ''x'')) (N 4)) test_env_eo = Check_Unknown"
  unfolding test_env_eo_def by eval

text \<open>Nested \<open>Or\<close>: proved through the negated-equality branch alone.\<close>

definition test_env_nested_proved :: "parity abs_state" where
  "test_env_nested_proved = (\<lambda>_. PTop)((STR ''x'') := PEven, (STR ''y'') := POdd)"

lemma parity_classify_nested_proved:
  "parity_classify_check
     (Or (Not (Eq (V (STR ''x'')) (V (STR ''y'')))) (Eq (V (STR ''z'')) (N 1)))
     test_env_nested_proved = Check_Proved"
  unfolding test_env_nested_proved_def by eval

text \<open>Nested \<open>Or\<close>, unknown: neither branch resolves when both sides share a
  parity class.\<close>

definition test_env_nested_unknown :: "parity abs_state" where
  "test_env_nested_unknown = (\<lambda>_. PTop)((STR ''x'') := PEven, (STR ''y'') := PEven)"

lemma parity_classify_nested_unknown:
  "parity_classify_check
     (Or (Not (Eq (V (STR ''x'')) (V (STR ''y'')))) (Eq (V (STR ''z'')) (N 1)))
     test_env_nested_unknown = Check_Unknown"
  unfolding test_env_nested_unknown_def by eval

section \<open>The generic report adapter, at the routed-unit context\<close>
section \<open>The generic report adapter, at the routed-unit context\<close>

text \<open>
  Interpreting \<^locale>\<open>dg_analysis_adapter\<close> at \<open>Parity_Ctx_None_Sound\<close>'s own routed-unit
  solved system, mirroring \<open>Sign_Checks\<close>'s own interpretation exactly. Every obligation is
  either one that theory's \<open>pctx_routed\<close> interpretation already discharges, or
  one that collapses at \<^const>\<open>route_unit\<close>/\<^const>\<open>enterc_unit\<close>; only
  \<open>classify_proved\<close>/\<open>classify_refuted\<close> are Parity's own, and both are the pre-existing
  \<^const>\<open>parity_classify_check\<close> soundness facts above. No Parity-specific result, report,
  or node-soundness construction appears anywhere below --- the adapter derives all three
  generically.
\<close>

context
  fixes gs :: "vname \<Rightarrow> bool" and empty_pred :: "parity exec_dg_st \<Rightarrow> bool"
    and Pi :: proc_table and ps :: "pname list"
  assumes solves: "pctx_terminates gs empty_pred Pi ps"
    and exact: "\<And>s. empty_pred s = is_empty_state (fun_of_resolved_st_q_for gs s)"
    and entry_cov: "(cfg_entry (compile_prog Pi ps), ())
                      \<in> fst (pctx_sol gs empty_pred Pi ps)"
    and fwd_ok: "\<And>u a v ctx. (u, ctx) \<in> fst (pctx_sol gs empty_pred Pi ps)
                   \<Longrightarrow> (u, a, v) \<in> intra (compile_prog Pi ps)
                   \<Longrightarrow> (v, ctx) \<in> fst (pctx_sol gs empty_pred Pi ps)"
    and call_fwd_ok: "\<And>u ctx dst pars args p cont.
        (u, ctx) \<in> fst (pctx_sol gs empty_pred Pi ps)
        \<Longrightarrow> (u, CallEdge dst pars args, FunctionEntry p, cont) \<in> calls (compile_prog Pi ps)
        \<Longrightarrow> (FunctionEntry p, ()) \<in> fst (pctx_sol gs empty_pred Pi ps)"
    and comb_fwd_ok: "\<And>cl c1 dst pars args p cont.
        (cl, c1) \<in> fst (pctx_sol gs empty_pred Pi ps)
        \<Longrightarrow> (cl, CallEdge dst pars args, FunctionEntry p, cont) \<in> calls (compile_prog Pi ps)
        \<Longrightarrow> (cont, c1) \<in> fst (pctx_sol gs empty_pred Pi ps)"
begin

interpretation pctx_dg_base: sound_dg_spec "pctx_spec gs empty_pred" "pctx_gamma gs" gs
  by (rule pctx_sound_exec[OF exact])

interpretation pctx_adapter: dg_analysis_adapter "pctx_spec gs empty_pred" "pctx_gamma gs" gs
    "compile_prog Pi ps" Global route_unit Bot "Lifted cinit_parity_st" Bot
    "snd (pctx_sol gs empty_pred Pi ps)" "fst (pctx_sol gs empty_pred Pi ps)"
    "(cfg_exit (compile_prog Pi ps), ())" "pctx_sg_st gs empty_pred Pi ps"
    Seed "\<lambda>m. gamma_state_lift (map_lift (fun_of_resolved_st_q_for gs) m)" enterc_unit
    "map_lift (fun_of_resolved_st_q_for gs)" parity_classify_check
proof (unfold_locales, goal_cases FinE PP SgCov SgUncov Fwd FinC SeedKey ResolveSound
    RouteEnterc CallFwd CombFwd EnterAgree GammaRd ClProved ClRefuted)
  case FinE show ?case
    using compile_prog_finite by auto
next
  case PP show ?case by (rule pctx_pp_routed[OF solves exact])
next
  case (SgCov v c)
  thus ?case by (simp add: pctx_sg_st_def pctx_gamma_def)
next
  case (SgUncov v c)
  thus ?case by (simp add: pctx_sg_st_def)
next
  case (Fwd u a v c)
  thus ?case by (rule fwd_ok)
next
  case FinC show ?case
    by (simp add: compile_prog_finite)
next
  case (SeedKey p ctx) show ?case by simp
next
  case (ResolveSound u ctx dst pars args p cont s)
  thus ?case by (simp add: static_resolve_iff compile_prog_finite)
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
      ce': "(cl, CallEdge dst' pars' args', FunctionEntry p', cont')
              \<in> calls (compile_prog Pi ps)"
    and es_eq: "es = call_enter gs (CallEdge dst' pars' args') s"
    using ces unfolding call_enter_store_def by blast
  have "CallEdge dst' pars' args' = CallEdge dst pars args"
    using compile_prog_calls_source_unique[OF ce' ce] by simp
  thus ?case using es_eq by simp
next
  case (GammaRd d g')
  show ?case by (simp add: pctx_gamma_def)
next
  case (ClProved c d s)
  thus ?case by (rule parity_classify_check_proved)
next
  case (ClRefuted c d s)
  thus ?case by (rule parity_classify_check_refuted)
qed

text \<open>
  The generic soundness corollaries \<^locale>\<open>dg_analysis_adapter\<close> derives once and for all,
  re-exported so a caller cites them without naming the interpretation.
\<close>

lemmas pctx_report_ctx_proved_sound = pctx_adapter.analyse_report_ctx_proved_sound
lemmas pctx_report_ctx_refuted_sound = pctx_adapter.analyse_report_ctx_refuted_sound
lemmas pctx_result_node_sound = pctx_adapter.analyse_result_node_sound

text \<open>
  \<open>pctx_analyse_result_eq\<close> identifies the adapter's own result reading with the
  raw-tuple shape \<^const>\<open>analyse_parity_ctx_result_for\<close> (\<open>Parity_Ctx_None_Sound\<close>)
  builds directly from \<^const>\<open>normalize_point\<close>/\<^const>\<open>canonicalize_lift\<close>: both
  collapse the same \<^const>\<open>Bot\<close>/\<^const>\<open>Lifted\<close> case split on the same projected
  local unknown, one via \<open>is_empty_state\<close> after projecting, the other via
  \<open>empty_pred\<close> before projecting -- \<open>exact\<close> is what identifies the two orders.
  Composing it with \<open>pctx_result_node_sound\<close> gives
  \<^const>\<open>analyse_parity_ctx_result_for\<close>'s node-soundness bridge without
  re-deriving \<open>routed_context_base_hetero\<close>'s coverage argument.
\<close>

lemma pctx_analyse_result_eq:
  "lookup_context pctx_adapter.analyse_result v ctx =
     (if (v, ctx) \<in> fst (pctx_sol gs empty_pred Pi ps)
      then normalize_point gs
             (canonicalize_lift empty_pred (locals (snd (pctx_sol gs empty_pred Pi ps) (Inl (v, ctx)))))
      else Bot)"
  unfolding pctx_adapter.lookup_context_analyse_result
  by (cases "locals (snd (pctx_sol gs empty_pred Pi ps) (Inl (v, ctx)))")
     (simp_all add: exact normalize_lift_def)

end

section \<open>Solved-result table and whole-program check report\<close>

text \<open>
  The public surface, in the same shape Sign's own
  \<open>analyse_sign_result_for\<close>/\<open>analyse_sign_report_for\<close> take: one-line partial
  applications of \<open>Parity_Ctx_None_Sound\<close>'s tables at \<^const>\<open>prog_main_name\<close>, and a report
  reading per-node state through \<^const>\<open>lookup_context\<close> rather than a raw
  solver-environment lookup. An \<^const>\<open>Bot\<close> point classifies at \<^const>\<open>bot\<close>, the
  same value \<^const>\<open>classify_checks\<close> always fed such a node, so \<open>check_result\<close>'s existing
  three-way verdict is preserved rather than gaining a fourth outcome.
\<close>

definition analyse_parity_result_for ::
    "(vname \<Rightarrow> bool) \<Rightarrow> imp_prog \<Rightarrow> (unit, parity abs_state) analysis_result" where
  "analyse_parity_result_for gs p = analyse_parity_ctx_result_for gs p"

definition analyse_parity_result :: "imp_prog \<Rightarrow> (unit, parity abs_state) analysis_result" where
  "analyse_parity_result p = analyse_parity_result_for (declared_global p) p"

definition analyse_parity_result_per_origin_for ::
    "(vname \<Rightarrow> bool) \<Rightarrow> imp_prog \<Rightarrow> (unit, parity abs_state) analysis_result" where
  "analyse_parity_result_per_origin_for gs p =
     analyse_parity_ctx_result_per_origin_for gs p"

definition analyse_parity_result_per_origin ::
    "imp_prog \<Rightarrow> (unit, parity abs_state) analysis_result" where
  "analyse_parity_result_per_origin p = analyse_parity_result_per_origin_for (declared_global p) p"

text \<open>\<open>r\<close> is bound once, outside \<^const>\<open>classify_checks\<close>'s per-check closure, so the single
  routed solve is shared across every check rather than repeated per check.\<close>

definition analyse_parity_report_for ::
    "(vname \<Rightarrow> bool) \<Rightarrow> imp_prog \<Rightarrow> check_report_entry list" where
  "analyse_parity_report_for gs p =
     analysis_surface.report (analyse_parity_result_for gs) bot parity_classify_check p"

definition analyse_parity_report :: "imp_prog \<Rightarrow> check_report_entry list" where
  "analyse_parity_report p = analyse_parity_report_for (declared_global p) p"

definition analyse_parity_report_per_origin_for ::
    "(vname \<Rightarrow> bool) \<Rightarrow> imp_prog \<Rightarrow> check_report_entry list" where
  "analyse_parity_report_per_origin_for gs p =
     analysis_surface.report (analyse_parity_result_per_origin_for gs) bot
       parity_classify_check p"

definition analyse_parity_report_per_origin :: "imp_prog \<Rightarrow> check_report_entry list" where
  "analyse_parity_report_per_origin p =
     analyse_parity_report_per_origin_for (declared_global p) p"

subsection \<open>The published surface, one interpretation per discipline\<close>

text \<open>
  Parity's two disciplines through the shared \<^locale>\<open>analysis_surface\<close>. Like Sign, it has
  no warrowing interpretation: the four-element lattice has finite height, so widening has
  nothing to accelerate and no solved table of its own.
\<close>

interpretation parity_join: analysis_surface
  analyse_parity_result bot parity_classify_check
  by unfold_locales

interpretation parity_per_origin: analysis_surface
  analyse_parity_result_per_origin bot parity_classify_check
  by unfold_locales

lemma parity_report_join_eq: "analyse_parity_report p = parity_join.report p"
  by (simp add: analyse_parity_report_def analyse_parity_report_for_def
      analyse_parity_result_def surface_unfold)

lemma parity_report_per_origin_eq:
  "analyse_parity_report_per_origin p = parity_per_origin.report p"
  by (simp add: analyse_parity_report_per_origin_def
      analyse_parity_report_per_origin_for_def analyse_parity_result_per_origin_def
      surface_unfold)

text \<open>
  State-carrying sibling, via \<^const>\<open>classify_checks_with_state\<close>: the same result table,
  with the per-check Parity environment attached to each entry instead of discarded, and
  an exact \<open>unreachable\<close> flag read straight off \<^const>\<open>lookup_context\<close>'s
  \<^const>\<open>Bot\<close>/\<^const>\<open>Lifted\<close> case split. Mirrors
  \<open>analyse_sign_report_for_with_state\<close> exactly.
\<close>

definition analyse_parity_report_for_with_state ::
    "(vname \<Rightarrow> bool) \<Rightarrow> imp_prog \<Rightarrow> (pp \<times> exp \<times> check_result \<times> bool \<times> (vname \<Rightarrow> parity)) list" where
  "analyse_parity_report_for_with_state gs p =
     (let r = analyse_parity_result_for gs p
      in classify_checks_with_state (prog_cfg p)
           (\<lambda>v. case lookup_context r v () of
                  Bot \<Rightarrow> (True, bot)
                | Lifted st \<Rightarrow> (False, st))
           (\<lambda>c (_, s). parity_classify_check c s))"

definition analyse_parity_report_with_state ::
    "imp_prog \<Rightarrow> (pp \<times> exp \<times> check_result \<times> bool \<times> (vname \<Rightarrow> parity)) list" where
  "analyse_parity_report_with_state p = analyse_parity_report_for_with_state (declared_global p) p"

end
