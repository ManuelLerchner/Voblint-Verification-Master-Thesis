theory Sign_Checks
  imports Sign_Classify
    "Voblint_Framework.Check_Report"
    "Voblint_Framework.DG_Analysis_Adapter"
    Analysis_Surface
    Sign_Analyses
begin

section \<open>What a whole-program Sign run reports\<close>

text \<open>
  The three-way classifier itself is \<^theory>\<open>Voblint_Analysis.Sign_Classify\<close>'s and says
  nothing about how the program was solved. This theory pairs it with one particular
  solved system -- the context-insensitive routed-unit run -- and publishes the result
  tables and check reports a caller consumes.

  A context-sensitive run pairs the same classifier with a different solved system
  instead, so it needs \<open>Sign_Classify\<close> alone and not the tables below.
\<close>

subsection \<open>The generic report adapter, at the routed-unit context\<close>

text \<open>
  Interpreting \<^locale>\<open>dg_analysis_adapter\<close> at \<open>Sign_Analyses\<close>'s own routed-unit
  solved system reuses every obligation that theory's own \<open>sctx_routed\<close>
  interpretation already discharges, at the executable carrier: the five
  \<^locale>\<open>dg_ctx_activation_base\<close> obligations are exactly its own (cited here via the exported
  \<open>sctx_pp_routed\<close>/\<open>sctx_sg_st_uncovered_empty\<close>), and the routed obligations collapse the same way
  \<^locale>\<open>unit_routed_context\<close>'s did, at \<^const>\<open>route_unit\<close>/\<^const>\<open>enterc_unit\<close>. Only
  \<open>classify_proved\<close>/\<open>classify_refuted\<close> are genuinely new here, discharged by
  \<open>sign_classify_check_proved\<close>/\<open>sign_classify_check_refuted\<close> above. This context re-opens
  \<open>Sign_Analyses\<close>'s own six coverage hypotheses (\<open>solves\<close>/\<open>exact\<close>/\<open>entry_cov\<close>/
  \<open>fwd_ok\<close>/\<open>call_fwd_ok\<close>/\<open>comb_fwd_ok\<close>) rather than reusing that theory's context directly,
  since the classify obligations need \<open>sign_classify_check_proved\<close>/\<open>sign_classify_check_refuted\<close>,
  which live in this theory, downstream of \<open>Sign_Analyses\<close>.
\<close>

context
  fixes gs :: "vname \<Rightarrow> bool" and empty_pred :: "sign exec_dg_st \<Rightarrow> bool"
    and Pi :: proc_table and ps :: "pname list"
  assumes solves: "sctx_terminates gs empty_pred Pi ps"
    and exact: "\<And>s. empty_pred s = is_empty_state (fun_of_resolved_st_q_for gs s)"
    and entry_cov: "(cfg_entry (compile_prog Pi ps), ()) \<in> fst (sctx_sol gs empty_pred Pi ps)"
    and fwd_ok: "\<And>u a v ctx. (u, ctx) \<in> fst (sctx_sol gs empty_pred Pi ps)
                   \<Longrightarrow> (u, a, v) \<in> intra (compile_prog Pi ps)
                   \<Longrightarrow> (v, ctx) \<in> fst (sctx_sol gs empty_pred Pi ps)"
    and call_fwd_ok: "\<And>u ctx dst pars args p cont.
        (u, ctx) \<in> fst (sctx_sol gs empty_pred Pi ps)
        \<Longrightarrow> (u, CallEdge dst pars args, FunctionEntry p, cont) \<in> calls (compile_prog Pi ps)
        \<Longrightarrow> (FunctionEntry p, ()) \<in> fst (sctx_sol gs empty_pred Pi ps)"
    and comb_fwd_ok: "\<And>cl c1 dst pars args p cont.
        (cl, c1) \<in> fst (sctx_sol gs empty_pred Pi ps)
        \<Longrightarrow> (cl, CallEdge dst pars args, FunctionEntry p, cont) \<in> calls (compile_prog Pi ps)
        \<Longrightarrow> (cont, c1) \<in> fst (sctx_sol gs empty_pred Pi ps)"
begin

interpretation sctx_dg_base: sound_dg_spec_core "sctx_spec gs empty_pred" "sctx_gamma gs" gs
  by (rule sctx_sound_exec[OF exact])

interpretation sctx_adapter: routed_analysis_sound
    "sctx_spec gs empty_pred" "sctx_gamma gs" gs
    "compile_prog Pi ps" "Analysis_Global ()" route_unit Bot "Lifted cinit_sign_st" Bot
    "snd (sctx_sol gs empty_pred Pi ps)" "fst (sctx_sol gs empty_pred Pi ps)"
    "(cfg_exit (compile_prog Pi ps), ())"
    Activation_Seed "\<lambda>d. d = Bot" enterc_unit
    "map_lift (fun_of_resolved_st_q_for gs)" sign_classify_check
proof (unfold_locales, goal_cases FinE PP SgCov SgUncov Fwd FinC SeedKey
    IsBotBot IsBotSound ResolveSound
    EnterCover CombFwd EnterAgree GammaRd ClProved ClRefuted)
  case FinE show ?case
    using compile_prog_finite by auto
next
  case PP show ?case by (rule sctx_pp_routed[OF solves exact])
next
  case (SgCov v c)
  thus ?case by (simp add: sctx_gamma_def)
next
  case (SgUncov v c)
  thus ?case by simp
next
  case (Fwd u a v c)
  thus ?case by (rule fwd_ok)
next
  case FinC show ?case
    by (simp add: compile_prog_finite)
next
  case (SeedKey p ctx) show ?case by simp
next
  case IsBotBot show ?case by simp
next
  case (IsBotSound d g') then show ?case by (simp add: sctx_gamma_def)
next
  case (ResolveSound u ctx dst pars args p cont s)
  thus ?case by (simp add: static_resolve_iff compile_prog_finite)
next
  case (EnterCover u ctx dst pars args p cont s)
  let ?ci = "call_info_of (CallEdge dst pars args) p"
  let ?caller = "locals (snd (sctx_sol gs empty_pred Pi ps) (Inl (u, ctx)))"
  have cov: "entry_pairs_cover
      (\<lambda>d. sctx_gamma gs d
             (globs (snd (sctx_sol gs empty_pred Pi ps) (Inr (Analysis_Global ())))))
      s (call_enter gs (CallEdge dst pars args) s)
      [(?caller, transfer_lift empty_pred (sign_enter_st_for gs ?ci) ?caller)]"
    using sctx_entry_cover_exec[OF exact EnterCover(3), where ci = ?ci] by simp
  show ?case
    unfolding sctx_spec_def dgs_enter_local_state_st_for_lifted
    using enter_runs_local_enter_transfer enter_deps_local_enter_transfer cov
          call_fwd_ok[OF EnterCover(1,2)]
    by (fastforce simp: entry_pairs_cover_def route_unit_def enterc_unit_def)
next
  case (CombFwd cl c1 dst pars args p cont)
  show ?case using CombFwd(1,2) comb_fwd_ok by blast
next
  case (EnterAgree cl s es dst pars args p cont)
  note ces = EnterAgree(1) and ce = EnterAgree(2)
  obtain dst' pars' args' p' cont' where
      ce': "(cl, CallEdge dst' pars' args', FunctionEntry p', cont') \<in> calls (compile_prog Pi ps)"
    and es_eq: "es = call_enter gs (CallEdge dst' pars' args') s"
    using ces unfolding call_enter_store_def by blast
  have "CallEdge dst' pars' args' = CallEdge dst pars args"
    using compile_prog_calls_source_unique[OF ce' ce] by simp
  thus ?case using es_eq by simp
next
  case (GammaRd d g')
  show ?case by (simp add: sctx_gamma_def)
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

text \<open>
  \<open>sctx_result_node_sound\<close> re-exports the adapter's generic node-soundness bridge
  (\<^theory>\<open>Voblint_Framework.DG_Analysis_Adapter\<close>), phrased against \<open>sctx_adapter.analyse_result\<close>.
  \<open>sctx_analyse_result_eq\<close> identifies that reading with the raw-tuple shape
  \<^const>\<open>analyse_sign_ctx_result_for\<close> (\<open>Sign_Analyses\<close>) already builds by hand from
  \<^const>\<open>normalize_point\<close>/\<^const>\<open>canonicalize_lift\<close> directly: both collapse the same
  \<^const>\<open>Bot\<close>/\<^const>\<open>Lifted\<close> case split on the same projected local unknown, one via
  \<open>is_empty_state\<close> after projecting (the adapter), the other via \<open>empty_pred\<close> before
  projecting (\<open>analyse_sign_ctx_result_for\<close>) --- \<open>exact\<close> is exactly what identifies the
  two orders. A caller composing \<open>sctx_result_node_sound\<close> with \<open>sctx_analyse_result_eq\<close>
  gets \<^const>\<open>analyse_sign_ctx_result_for\<close>'s own node-soundness bridge without
  re-deriving \<open>routed_context_base_hetero\<close>'s coverage argument by hand.
\<close>

lemmas sctx_result_node_sound = sctx_adapter.analyse_result_node_sound

lemma sctx_analyse_result_eq:
  "lookup_context sctx_adapter.analyse_result v ctx =
     (if (v, ctx) \<in> fst (sctx_sol gs empty_pred Pi ps)
      then normalize_point gs
             (canonicalize_lift empty_pred (locals (snd (sctx_sol gs empty_pred Pi ps) (Inl (v, ctx)))))
      else Bot)"
  unfolding sctx_adapter.lookup_context_analyse_result
  by (cases "locals (snd (sctx_sol gs empty_pred Pi ps) (Inl (v, ctx)))")
     (simp_all add: exact normalize_lift_def)

end

subsection \<open>Solved-result table\<close>
subsection \<open>Solved-result table\<close>

text \<open>
  \<open>analyse_sign_result_for\<close> is the canonical solved D/G system, read as a
  \<^typ>\<open>(unit, sign abs_state) analysis_result\<close>: a one-line partial
  application of \<^const>\<open>analyse_sign_ctx_result_for\<close>
  (\<^theory>\<open>Voblint_Analysis.Sign_Analyses\<close>), fixed at \<^const>\<open>prog_main_name\<close>,
  which already binds the single routed-unit solve and
  canonicalizes/normalizes each local key. Every report below reads
  through this table via \<^const>\<open>lookup_context\<close> rather than a raw
  solver-environment lookup.
\<close>

definition analyse_sign_result_for ::
    "(vname \<Rightarrow> bool) \<Rightarrow> imp_prog \<Rightarrow> (unit, sign abs_state) analysis_result" where
  "analyse_sign_result_for gs p = analyse_sign_ctx_result_for gs p"

text \<open>Convenience instance at \<^const>\<open>declared_global\<close> \<open>p\<close>, matching
  \<open>analyse_sign_report\<close>'s shape.\<close>

definition analyse_sign_result :: "imp_prog \<Rightarrow> (unit, sign abs_state) analysis_result" where
  "analyse_sign_result p = analyse_sign_result_for (declared_global p) p"

subsection \<open>Solved-result table: per-origin update rule\<close>

text \<open>
  \<open>analyse_sign_result_per_origin_for\<close> is \<^const>\<open>analyse_sign_result_for\<close>'s
  sibling under the per-origin rule: a one-line partial application of
  \<^const>\<open>analyse_sign_ctx_result_per_origin_for\<close>
  (\<^theory>\<open>Voblint_Analysis.Sign_Analyses\<close>), fixed at \<^const>\<open>prog_main_name\<close>,
  reading \<^const>\<open>sctx_sol_prog_per_origin\<close> instead of \<^const>\<open>sctx_sol_prog\<close>.
  Experimental: no dedicated soundness theorem is proved for this
  combination here -- \<open>analyse\<close> and its soundness corollaries are
  unaffected, and this definition exists solely so \<open>Analyse_Dispatch\<close>'s
  \<open>analyse_with_solver\<close> can compare solver choices on the routed-unit
  equation system.
\<close>

definition analyse_sign_result_per_origin_for ::
    "(vname \<Rightarrow> bool) \<Rightarrow> imp_prog \<Rightarrow> (unit, sign abs_state) analysis_result" where
  "analyse_sign_result_per_origin_for gs p =
     analyse_sign_ctx_result_per_origin_for gs p"

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
  \<^const>\<open>Lifted\<close> point classifies at its projected state exactly as
  before, and an \<^const>\<open>Bot\<close> one (dead or never covered; the two are
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
     analysis_surface.report (analyse_sign_result_for gs) bot sign_classify_check p"

text \<open>
  Convenience instance at \<^const>\<open>declared_global\<close> \<open>p\<close>, the classifier every
  caller with only an \<^typ>\<open>imp_prog\<close> in hand recomputes anyway.
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
     analysis_surface.report analyse_sign_result_per_origin bot sign_classify_check p"

subsection \<open>The published surface, one interpretation per discipline\<close>

text \<open>
  Sign's two disciplines through the shared \<^locale>\<open>analysis_surface\<close>. There is no
  warrowing interpretation because there is no warrowing table to name: Sign's carrier has
  finite height and carries no widen instance, so warrowing has nothing to accelerate and
  no solved table of its own. The absent interpretation and the absent solver route agree
  by construction rather than by a separately maintained legality table.
\<close>

interpretation sign_join: analysis_surface
  analyse_sign_result bot sign_classify_check
  by unfold_locales

interpretation sign_per_origin: analysis_surface
  analyse_sign_result_per_origin bot sign_classify_check
  by unfold_locales

lemma sign_report_join_eq: "analyse_sign_report p = sign_join.report p"
  by (simp add: analyse_sign_report_def analyse_sign_report_for_def
      analyse_sign_result_def surface_unfold)

lemma sign_report_per_origin_eq:
  "analyse_sign_report_per_origin p = sign_per_origin.report p"
  by (simp add: analyse_sign_report_per_origin_def surface_unfold)

subsection \<open>Whole-program check report with state\<close>

text \<open>
  State-carrying sibling of \<open>analyse_sign_report_for\<close>/\<open>analyse_sign_report\<close>,
  via \<^const>\<open>classify_checks_with_state\<close>: same result table, with the
  per-check Sign environment attached to each report entry instead of
  discarded, and an exact \<open>unreachable\<close> flag read straight off
  \<^const>\<open>lookup_context\<close>'s \<^const>\<open>Bot\<close>/\<^const>\<open>Lifted\<close> case split --
  exact because composing \<^const>\<open>canonicalize_lift\<close>'s witness-bottom
  collapse with \<^const>\<open>normalize_point\<close>'s readback agrees with the older
  \<^const>\<open>resolved_st_q_lifted_is_bot_for\<close> test on the same raw local
  unknown.
\<close>

definition analyse_sign_report_for_with_state ::
    "(vname \<Rightarrow> bool) \<Rightarrow> imp_prog \<Rightarrow> (pp \<times> exp \<times> check_result \<times> bool \<times> (vname \<Rightarrow> sign)) list" where
  "analyse_sign_report_for_with_state gs p =
     (let r = analyse_sign_result_for gs p
      in classify_checks_with_state (prog_cfg p)
           (\<lambda>v. case lookup_context r v () of
                  Bot \<Rightarrow> (True, bot)
                | Lifted st \<Rightarrow> (False, st))
           (\<lambda>c (_, s). sign_classify_check c s))"

text \<open>Convenience instance at \<^const>\<open>declared_global\<close> \<open>p\<close>, matching
  \<open>analyse_sign_report\<close>'s shape.\<close>

definition analyse_sign_report_with_state ::
    "imp_prog \<Rightarrow> (pp \<times> exp \<times> check_result \<times> bool \<times> (vname \<Rightarrow> sign)) list" where
  "analyse_sign_report_with_state p = analyse_sign_report_for_with_state (declared_global p) p"

end

