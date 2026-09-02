theory Interval_Ctx_None_Sound
  imports
    "Voblint_Exec.Routed_Domain_Exec"
    "Voblint_Core.DG_LTR_Sound"
    "Voblint_Analysis.Interval_Transfer"
    "Voblint_Analysis.Interval_Exec_Sound"
    "Voblint_Analysis.Interval_Sound"
    "Voblint_Analysis.Interval_Classify"
    "Voblint_Core.Routed_Context"
    "Voblint_Core.Routed_Context_Unit"
    "Voblint_Core.DG_Analysis_Adapter"
    "Voblint_Solver.TD_Solver_Menu"
    "Voblint_VIMP.VIMP_Program"
begin

section \<open>Interval at the routed spine, instantiated at the unit context\<close>

text \<open>
  Redirects Interval's production Base-family (\<open>dg_gen_of\<close>) analysis onto the
  routed D/G spine (\<^locale>\<open>dg_ctx_activation_base\<close>, \<^locale>\<open>unit_routed_context\<close>)
  that Interval's own entry-state and call-string context analyses already use.
  The context here is \<^typ>\<open>unit\<close>: \<^locale>\<open>unit_routed_context\<close>
  (\<^theory>\<open>Voblint_Core.Routed_Context_Unit\<close>) fixes \<^const>\<open>route_unit\<close>, so every
  routing-agreement obligation a non-trivial routed instance must prove from its
  own transfer facts collapses here to a free lemma about the constant function
  \<^const>\<open>route_unit\<close> --- exactly the collapse Sign's own unit-context instance
  (\<open>Sign_Ctx_None_Sound\<close>) already exercises.

  Soundness below is derived directly from \<^locale>\<open>dg_ctx_activation_base\<close>'s
  generic machinery against the collecting semantics, exactly as Interval's
  entry-state analysis is derived. No comparison to Interval's Base-family
  production result is attempted or needed: \<^const>\<open>dg_gen_of\<close> never appears in
  this development.
\<close>

subsection \<open>Global key: real globals vs callee-entry seed slots\<close>

text \<open>
  \<^typ>\<open>unit\<close> context, so the seed constructor's second field is \<^typ>\<open>unit\<close> rather
  than an interesting per-context payload: exactly one seed slot per callee entry.
\<close>

datatype gk = Global | Seed (seed_pp: pp) (seed_ctx: unit)

subsection \<open>The routed unit-context D/G spec\<close>

text \<open>
  The same Base-style whole-state specification Interval's own production
  \<^const>\<open>analyse_interval_dg_eqs_for\<close> already solves over
  (\<^theory>\<open>Voblint_Analysis.Interval_Exec_Sound\<close>), at the same
  \<^const>\<open>ivl_tf_st_for\<close>/\<^const>\<open>ivl_enter_st_for\<close> primitives -- byte-for-byte the
  term \<open>base_dg_spec_st_for_lifted gs empty_pred (ivl_tf_st_for gs) (ivl_enter_st_for gs)\<close>
  that \<^const>\<open>analyse_interval_dg_eqs_for\<close> feeds \<^const>\<open>dg_gen_of\<close>. Only the
  equation-generator wrapped around this spec changes (\<open>dg_gen_of\<close> there, the
  routed keyed-seed generator here) --- the spec itself, and every domain-transfer
  soundness fact about it, is untouched.
\<close>

subsection \<open>The routed equation system and its executable solution\<close>

text \<open>
  Solved under the always-join update rule, mirroring Sign's own choice: the
  minimal solver instance needed to prove direct soundness once. Interval's
  production route needs Apinis warrowing for termination on an unbounded local
  loop (\<^theory>\<open>Voblint_Analysis.Interval_Exec_Sound\<close>'s own
  \<open>analyse_interval_dg_for\<close>); that solver choice is orthogonal to this context
  (commit \<open>c38efade\<close>) and is future work here, not attempted.
\<close>

definition ictx_eqs ::
    "(vname \<Rightarrow> bool) \<Rightarrow> (ivl exec_dg_st \<Rightarrow> bool) \<Rightarrow> proc_table \<Rightarrow> pname list \<Rightarrow> (pp \<times> unit, gk, (ivl exec_dg_st lifted, ivl exec_dg_st lifted) dg_state) eqsT" where
  "ictx_eqs gs empty_pred Pi ps =
     side_cfg_T_eff_keyed_seed_dg_buffered intra_predecessor_addr_list (\<lambda>_. Global)
       route_unit
       (\<lambda>ctx' src a. dg_spec_edge_tree (ictx_spec gs empty_pred) a src (\<lambda>_. Global))
       (routed_cmb_g (ictx_spec gs empty_pred) Global Seed
          (static_resolve (compile_prog Pi ps)))
       (routed_extra_g Seed Global)
       (compile_prog Pi ps) Bot (Lifted cinit_ivl_st) Bot"

definition ictx_sol ::
    "(vname \<Rightarrow> bool) \<Rightarrow> (ivl exec_dg_st \<Rightarrow> bool) \<Rightarrow> proc_table \<Rightarrow> pname list \<Rightarrow> (pp \<times> unit) set \<times> (pp \<times> unit + gk \<Rightarrow> (ivl exec_dg_st lifted, ivl exec_dg_st lifted) dg_state)" where
  "ictx_sol gs empty_pred Pi ps =
     TD_side_always_join_Interp_solve (ictx_eqs gs empty_pred Pi ps)
       (cfg_exit (compile_prog Pi ps), ())"

definition ictx_terminates ::
    "(vname \<Rightarrow> bool) \<Rightarrow> (ivl exec_dg_st \<Rightarrow> bool) \<Rightarrow> proc_table \<Rightarrow> pname list \<Rightarrow> bool" where
  "ictx_terminates gs empty_pred Pi ps =
     TD_side_always_join_Interp.solve_dom TYPE(gk) TYPE((ivl exec_dg_st lifted, ivl exec_dg_st lifted) dg_state)
       (ictx_eqs gs empty_pred Pi ps) (cfg_exit (compile_prog Pi ps), ())"

lemma ictx_terminates_via_solve_c:
  assumes "TD_side_always_join_Interp_solve_c (ictx_eqs gs empty_pred Pi ps)
             (cfg_exit (compile_prog Pi ps), ()) \<noteq> None"
  shows "ictx_terminates gs empty_pred Pi ps"
  unfolding ictx_terminates_def
  by (rule TD_side_always_join_Interp.solve_dom_of_solve_c[OF assms])

subsection \<open>Domain commute facts, at the routed unit spec\<close>
text \<open>
  The whole of Interval's obligation to the routed spine, in one interpretation.
  \<^locale>\<open>routed_domain_exec\<close> adds only the seed-key pair, its distinctness, and the
  two routing functions on top of \<^locale>\<open>routed_dg_domain_exec\<close>, so the interpretation
  carries no Interval mathematics: the first three obligations are Interval's own
  pre-existing commute lemmas, cited unchanged, and the last two are datatype
  distinctness for \<^type>\<open>gk\<close> and the free routing agreement \<^const>\<open>route_unit\<close> enjoys
  by ignoring its \<open>'D\<close> argument outright.
\<close>

text \<open>The concretization the executable-carrier interpretation below uses: a local
  unknown means \<^const>\<open>gamma_state_lift\<close> of its readback, the global slot is ignored as
  in \<^const>\<open>gamma_dg_base\<close>. Named at top level so a downstream theory can state it.\<close>

context
  fixes gs :: "vname \<Rightarrow> bool" and empty_pred :: "ivl exec_dg_st \<Rightarrow> bool"
  assumes exact: "\<And>s. empty_pred s = is_empty_state (fun_of_resolved_st_q_for gs s)"
begin

interpretation ivl_unit: routed_domain_exec
  gs empty_pred "ivl_tf_st_for gs" "ivl_enter_st_for gs" "ivl_tf_for gs"
  Global Seed route_unit route_unit static_resolve static_resolve
  by unfold_locales
     (rule ivl_tf_st_for_commute, rule ivl_enter_st_for_commute, rule exact, simp, simp,
      simp add: static_resolve_def)

lemmas ivl_pp_st_gen = ivl_unit.pp_st

end


lemma seed_ne_global [simp]: "Seed p ctx \<noteq> Global"
  by simp

section \<open>The solver-generic instantiation\<close>

text \<open>
  Everything downstream of the executable post-solution reaches the solver through exactly one
  fact: that the solved pair is a \<^const>\<open>part_post_solution\<close> of \<^const>\<open>ictx_eqs\<close>.  The update
  rule itself never appears again.  \<open>ictx_solved\<close> therefore fixes the solved pair and its
  termination predicate and assumes that single fact, so each update rule contributes an
  interpretation rather than a copy of the development.

  The obligation is cheap at every instance because \<^locale>\<open>TD_side_upd_rule\<close> proves
  \<open>partial_post_solution\<close> once, inside the locale, for every update rule.
\<close>

locale ictx_solved =
  fixes sol :: "(vname \<Rightarrow> bool) \<Rightarrow> (ivl exec_dg_st \<Rightarrow> bool) \<Rightarrow> proc_table \<Rightarrow> pname list \<Rightarrow> (pp \<times> unit) set
                     \<times> (pp \<times> unit + gk \<Rightarrow> (ivl exec_dg_st lifted, ivl exec_dg_st lifted) dg_state)"
    and terminates :: "(vname \<Rightarrow> bool) \<Rightarrow> (ivl exec_dg_st \<Rightarrow> bool) \<Rightarrow> proc_table \<Rightarrow> pname list
                         \<Rightarrow> bool"
  assumes pp_st:
    "terminates gs empty_pred Pi ps
       \<Longrightarrow> part_post_solution (ictx_eqs gs empty_pred Pi ps)
             (cfg_exit (compile_prog Pi ps), ())
             (snd (sol gs empty_pred Pi ps))
             (fst (sol gs empty_pred Pi ps))"
begin

text \<open>The solver's post-solution, for the unbuffered routed generator at the executable
  spec: the shape \<^locale>\<open>dg_ctx_activation_base\<close> consumes directly.\<close>

theorem pp_routed:
  assumes solves: "terminates gs empty_pred Pi ps"
    and exact: "\<And>s. empty_pred s = is_empty_state (fun_of_resolved_st_q_for gs s)"
  shows
  "part_post_solution
     (side_cfg_T_eff_keyed_seed_dg intra_predecessor_addr_list (\<lambda>_. Global) route_unit
        (\<lambda>ctx' src a. dg_spec_edge_tree (ictx_spec gs empty_pred) a src (\<lambda>_. Global))
        (routed_cmb_g (ictx_spec gs empty_pred) Global Seed (static_resolve (compile_prog Pi ps)))
        (routed_extra_g Seed Global)
        (compile_prog Pi ps) Bot (Lifted cinit_ivl_st) Bot)
     (cfg_exit (compile_prog Pi ps), ())
     (snd (sol gs empty_pred Pi ps)) (fst (sol gs empty_pred Pi ps))"
  using pp_st[OF solves] unfolding ictx_eqs_def ictx_spec_def by (rule ivl_pp_st_gen[OF exact])

subsection \<open>Activation-indexed collecting soundness, generic per compiled program\<close>

text \<open>
  The routed spine is interpreted at Interval's executable carrier and fed the solver's own
  table: a local unknown concretizes to \<^const>\<open>gamma_state_lift\<close> of its readback, the
  covered reader \<open>sg_st\<close> hands the table's local slot through unchanged, and no solved
  system is transported between carriers.
\<close>

definition sg_st ::
    "(vname \<Rightarrow> bool) \<Rightarrow> (ivl exec_dg_st \<Rightarrow> bool) \<Rightarrow> proc_table \<Rightarrow> pname list
       \<Rightarrow> pp \<times> unit + gk \<Rightarrow> ivl exec_dg_st lifted" where
  "sg_st gs empty_pred Pi ps k =
     (case k of
        Inl (v, ctx) \<Rightarrow>
          (if (v, ctx) \<in> fst (sol gs empty_pred Pi ps)
           then locals (snd (sol gs empty_pred Pi ps) (Inl (v, ctx)))
           else Bot)
      | Inr _ \<Rightarrow> Bot)"

context
  fixes gs :: "vname \<Rightarrow> bool" and empty_pred :: "ivl exec_dg_st \<Rightarrow> bool"
    and Pi :: proc_table and ps :: "pname list"
  assumes solves: "terminates gs empty_pred Pi ps"
    and exact: "\<And>s. empty_pred s = is_empty_state (fun_of_resolved_st_q_for gs s)"
    and entry_cov: "(cfg_entry (compile_prog Pi ps), ()) \<in> fst (sol gs empty_pred Pi ps)"
    and fwd_ok: "\<And>u a v ctx. (u, ctx) \<in> fst (sol gs empty_pred Pi ps)
                   \<Longrightarrow> (u, a, v) \<in> intra (compile_prog Pi ps)
                   \<Longrightarrow> (v, ctx) \<in> fst (sol gs empty_pred Pi ps)"
    and call_fwd_ok: "\<And>u ctx dst pars args p cont.
        (u, ctx) \<in> fst (sol gs empty_pred Pi ps)
        \<Longrightarrow> (u, CallEdge dst pars args, FunctionEntry p, cont) \<in> calls (compile_prog Pi ps)
        \<Longrightarrow> (FunctionEntry p, ()) \<in> fst (sol gs empty_pred Pi ps)"
    and comb_fwd_ok: "\<And>cl c1 dst pars args p cont.
        (cl, c1) \<in> fst (sol gs empty_pred Pi ps)
        \<Longrightarrow> (cl, CallEdge dst pars args, FunctionEntry p, cont) \<in> calls (compile_prog Pi ps)
        \<Longrightarrow> (cont, c1) \<in> fst (sol gs empty_pred Pi ps)"
begin

subsubsection \<open>The solver's table as the solved system\<close>

interpretation ivl_compiled: compiled_cfg Pi ps "compile_prog Pi ps"
  by (unfold_locales; simp add: compile_prog_finite)

lemmas fin = ivl_compiled.finite_intra
lemmas finC = ivl_compiled.finite_calls

lemma sg_st_covered:
  "(v, ctx) \<in> fst (sol gs empty_pred Pi ps)
   \<Longrightarrow> sg_st gs empty_pred Pi ps (Inl (v, ctx))
         = locals (snd (sol gs empty_pred Pi ps) (Inl (v, ctx)))"
  by (simp add: sg_st_def)

lemma sg_st_uncovered_empty:
  "(v, ctx) \<notin> fst (sol gs empty_pred Pi ps)
     \<Longrightarrow> gamma_state_lift (map_lift (fun_of_resolved_st_q_for gs)
           (sg_st gs empty_pred Pi ps (Inl (v, ctx)))) = {}"
  by (simp add: sg_st_def)

subsubsection \<open>Instantiating the generic DG-native activation discharge\<close>

interpretation dg_base: sound_dg_spec "ictx_spec gs empty_pred" "ictx_gamma gs" gs
  by (rule ictx_sound_exec[OF exact])

interpretation routed: unit_routed_context "ictx_spec gs empty_pred" "ictx_gamma gs" gs
    "compile_prog Pi ps" Global Bot "Lifted cinit_ivl_st" Bot
    "snd (sol gs empty_pred Pi ps)" "fst (sol gs empty_pred Pi ps)"
    "(cfg_exit (compile_prog Pi ps), ())" "sg_st gs empty_pred Pi ps" Seed
    "\<lambda>m. gamma_state_lift (map_lift (fun_of_resolved_st_q_for gs) m)"
proof (unfold_locales, goal_cases FinE PP SgCov SgUncov Fwd FinC SeedKey CallFwd CombFwd EnterAgree)
  case FinE show ?case by (rule fin)
next
  case PP show ?case by (rule pp_routed[OF solves exact])
next
  case (SgCov v ctx) then show ?case
    by (simp add: sg_st_def ictx_gamma_def)
next
  case (SgUncov v ctx) then show ?case by (rule sg_st_uncovered_empty)
next
  case (Fwd u a v ctx) then show ?case by (rule fwd_ok)
next
  case FinC show ?case by (rule finC)
next
  case (SeedKey p ctx) show ?case by simp
next
  case (CallFwd u ctx dst pars args p cont)
  show ?case using CallFwd(1,2) call_fwd_ok unfolding route_unit_def by blast
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
qed

subsubsection \<open>Activation-indexed collecting soundness\<close>

lemma cinit_le_cinit_ivl_st:
  "cinit_stores gs \<subseteq> ictx_gamma gs (Lifted cinit_ivl_st) Bot"
  by (auto simp: ictx_gamma_def cinit_stores_def gamma_state_def fun_of_resolved_st_q_for_def
                 fun_of_st_cinit_ivl_st)

subsubsection \<open>The generic report adapter\<close>

text \<open>
  Interpreting \<^locale>\<open>dg_analysis_adapter\<close> at this context's own solved
  system reuses every obligation already discharged for \<open>dg\<close>/\<open>routed\<close>
  above: the five \<^locale>\<open>dg_ctx_activation_base\<close> obligations are exactly
  \<open>dg\<close>'s own, and the routed obligations collapse the same way
  \<^locale>\<open>unit_routed_context\<close>'s did, at \<^const>\<open>route_unit\<close>/\<^const>\<open>enterc_unit\<close>.
  Only \<open>classify_proved\<close>/\<open>classify_refuted\<close> are genuinely new, discharged by
  Interval's own \<open>interval_classify_check_proved\<close>/\<open>interval_classify_check_refuted\<close>
  (\<^theory>\<open>Voblint_Analysis.Interval_Classify\<close>).
\<close>

interpretation adapter: dg_analysis_adapter "ictx_spec gs empty_pred" "ictx_gamma gs" gs
    "compile_prog Pi ps" Global route_unit Bot "Lifted cinit_ivl_st" Bot
    "snd (sol gs empty_pred Pi ps)" "fst (sol gs empty_pred Pi ps)"
    "(cfg_exit (compile_prog Pi ps), ())" "sg_st gs empty_pred Pi ps"
    Seed "\<lambda>m. gamma_state_lift (map_lift (fun_of_resolved_st_q_for gs) m)" enterc_unit
    "map_lift (fun_of_resolved_st_q_for gs)" interval_classify_check
proof (unfold_locales, goal_cases FinE PP SgCov SgUncov Fwd FinC SeedKey ResolveSound
    RouteEnterc CallFwd CombFwd EnterAgree GammaRd ClProved ClRefuted)
  case FinE show ?case by (rule fin)
next
  case PP show ?case by (rule pp_routed[OF solves exact])
next
  case (SgCov v c)
  thus ?case by (simp add: sg_st_def ictx_gamma_def)
next
  case (SgUncov v c)
  thus ?case by (simp add: sg_st_def)
next
  case (Fwd u a v c)
  thus ?case by (rule fwd_ok)
next
  case FinC show ?case by (rule finC)
next
  case (SeedKey p ctx) show ?case by simp
next
  case (ResolveSound u ctx dst pars args p cont s)
  thus ?case by (simp add: static_resolve_iff[OF finC])
next
  case (RouteEnterc u ctx dst pars args p cont s)
  show ?case by simp
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
      ce': "(cl, CallEdge dst' pars' args', FunctionEntry p', cont') \<in> calls (compile_prog Pi ps)"
    and es_eq: "es = call_enter gs (CallEdge dst' pars' args') s"
    using ces unfolding call_enter_store_def by blast
  have "CallEdge dst' pars' args' = CallEdge dst pars args"
    using compile_prog_calls_source_unique[OF ce' ce] by simp
  thus ?case using es_eq by simp
next
  case (GammaRd d g')
  show ?case by (simp add: ictx_gamma_def)
next
  case (ClProved c d s)
  thus ?case by (rule interval_classify_check_proved)
next
  case (ClRefuted c d s)
  thus ?case by (rule interval_classify_check_refuted)
qed

text \<open>
  The two generic soundness corollaries \<^locale>\<open>dg_analysis_adapter\<close> derives
  once and for all -- \<open>adapter.analyse_report_ctx_proved_sound\<close>,
  \<open>adapter.analyse_report_ctx_refuted_sound\<close> -- are available here without
  any further proof: an improvement over Sign's own file, which predates this
  locale and hand-rolls a report table with no soundness theorem attached.
\<close>

lemmas report_ctx_proved_sound = adapter.analyse_report_ctx_proved_sound
lemmas report_ctx_refuted_sound = adapter.analyse_report_ctx_refuted_sound

text \<open>
  \<open>result_node_sound\<close> re-exports the adapter's generic node-soundness bridge
  (\<^theory>\<open>Voblint_Core.DG_Analysis_Adapter\<close>). \<open>analyse_result_eq\<close> identifies that
  reading with the raw-tuple shape \<open>analyse_interval_ctx_result_for\<close> (defined below)
  already builds by hand, identical for every update rule.
\<close>

lemmas result_node_sound = adapter.analyse_result_node_sound

lemma analyse_result_eq:
  "lookup_context adapter.analyse_result v ctx =
     (if (v, ctx) \<in> fst (sol gs empty_pred Pi ps)
      then normalize_point gs
             (canonicalize_lift empty_pred (locals (snd (sol gs empty_pred Pi ps) (Inl (v, ctx)))))
      else Bot)"
  unfolding adapter.lookup_context_analyse_result
  by (cases "locals (snd (sol gs empty_pred Pi ps) (Inl (v, ctx)))")
     (simp_all add: exact normalize_lift_def)

end

end

text \<open>The always-join rule as an instance.  \<open>partial_post_solution\<close> is the whole obligation,
  and \<^locale>\<open>TD_side_upd_rule\<close> already carries it.\<close>

lemma ictx_join_pp_st:
  "ictx_terminates gs empty_pred Pi ps
     \<Longrightarrow> part_post_solution (ictx_eqs gs empty_pred Pi ps)
           (cfg_exit (compile_prog Pi ps), ())
           (snd (ictx_sol gs empty_pred Pi ps))
           (fst (ictx_sol gs empty_pred Pi ps))"
  unfolding ictx_sol_def ictx_terminates_def
  by (rule TD_side_always_join_Interp.partial_post_solution[OF _ surjective_pairing])

global_interpretation ictx_join: ictx_solved ictx_sol ictx_terminates
  by unfold_locales (rule ictx_join_pp_st)

lemmas ictx_result_node_sound = ictx_join.result_node_sound
lemmas ictx_analyse_result_eq = ictx_join.analyse_result_eq
lemmas ictx_cinit_le_cinit_ivl_st = ictx_join.cinit_le_cinit_ivl_st
lemmas ictx_report_ctx_proved_sound = ictx_join.report_ctx_proved_sound
lemmas ictx_report_ctx_refuted_sound = ictx_join.report_ctx_refuted_sound

section \<open>PerOrigin solver instantiation, at the same routed unit-context spec\<close>

text \<open>
  Mirrors the always-join instantiation above (\<open>ictx_eqs\<close>/\<open>ictx_sol\<close>/\<open>ictx_terminates\<close>)
  under \<^const>\<open>TD_side_per_origin_Interp_solve\<close> instead, solving the exact same
  \<open>ictx_eqs\<close> equation system -- mirroring how Interval's own Base family
  (\<^theory>\<open>Voblint_Analysis.Interval_Exec_Sound\<close>) already solves
  \<open>analyse_interval_dg_eqs_for\<close> under three interchangeable update rules. Genuinely
  sound: \<^locale>\<open>TD_side_upd_rule\<close>'s \<open>solve_dom\<close>/\<open>partial_post_solution\<close> are
  locale-generic over the update rule, so \<open>TD_side_per_origin_Interp\<close>'s own
  \<open>partial_post_solution\<close> instance discharges the same obligation \<open>TD_side_always_join_Interp\<close>'s
  \<open>partial_post_solution\<close> did above, with no extra premises.
\<close>

definition ictx_sol_per_origin ::
    "(vname \<Rightarrow> bool) \<Rightarrow> (ivl exec_dg_st \<Rightarrow> bool) \<Rightarrow> proc_table \<Rightarrow> pname list \<Rightarrow> (pp \<times> unit) set \<times> (pp \<times> unit + gk \<Rightarrow> (ivl exec_dg_st lifted, ivl exec_dg_st lifted) dg_state)" where
  "ictx_sol_per_origin gs empty_pred Pi ps =
     TD_side_per_origin_Interp_solve (ictx_eqs gs empty_pred Pi ps)
       (cfg_exit (compile_prog Pi ps), ())"

definition ictx_terminates_per_origin ::
    "(vname \<Rightarrow> bool) \<Rightarrow> (ivl exec_dg_st \<Rightarrow> bool) \<Rightarrow> proc_table \<Rightarrow> pname list \<Rightarrow> bool" where
  "ictx_terminates_per_origin gs empty_pred Pi ps =
     TD_side_per_origin_Interp.solve_dom TYPE(gk) TYPE((ivl exec_dg_st lifted, ivl exec_dg_st lifted) dg_state)
       (ictx_eqs gs empty_pred Pi ps) (cfg_exit (compile_prog Pi ps), ())"

lemma ictx_terminates_per_origin_via_solve_c:
  assumes "TD_side_per_origin_Interp_solve_c (ictx_eqs gs empty_pred Pi ps)
             (cfg_exit (compile_prog Pi ps), ()) \<noteq> None"
  shows "ictx_terminates_per_origin gs empty_pred Pi ps"
  unfolding ictx_terminates_per_origin_def
  by (rule TD_side_per_origin_Interp.solve_dom_of_solve_c[OF assms])

subsection \<open>The PerOrigin instance\<close>

lemma ictx_per_origin_pp_st:
  "ictx_terminates_per_origin gs empty_pred Pi ps
     \<Longrightarrow> part_post_solution (ictx_eqs gs empty_pred Pi ps)
           (cfg_exit (compile_prog Pi ps), ())
           (snd (ictx_sol_per_origin gs empty_pred Pi ps))
           (fst (ictx_sol_per_origin gs empty_pred Pi ps))"
  unfolding ictx_sol_per_origin_def ictx_terminates_per_origin_def
  by (rule TD_side_per_origin_Interp.partial_post_solution[OF _ surjective_pairing])

global_interpretation ictx_po: ictx_solved ictx_sol_per_origin ictx_terminates_per_origin
  by unfold_locales (rule ictx_per_origin_pp_st)

lemmas ictx_result_node_sound_per_origin = ictx_po.result_node_sound
lemmas ictx_analyse_result_eq_per_origin = ictx_po.analyse_result_eq
lemmas ictx_cinit_le_cinit_ivl_st_per_origin = ictx_po.cinit_le_cinit_ivl_st
lemmas ictx_report_ctx_proved_sound_per_origin = ictx_po.report_ctx_proved_sound
lemmas ictx_report_ctx_refuted_sound_per_origin = ictx_po.report_ctx_refuted_sound

section \<open>Apinis warrowing solver instantiation, at the same routed unit-context spec\<close>

text \<open>
  Interval production's default solver: mirrors the always-join instantiation above under
  \<^const>\<open>TD_side_warrowing_apinis_Interp_solve\<close> instead, solving the exact same \<open>ictx_eqs\<close>
  equation system -- exactly as Interval's own entry-state contextual mode
  (\<open>Interval_Ctx_Entry_State_Sound\<close>) already does. That file's own soundness derivation needs
  no separate globally-restricted-slot bookkeeping the way the Base family's flow-insensitive
  global slot once did (\<^theory>\<open>Voblint_Analysis.Interval_Exec_Sound\<close>): the routed spine's
  keyed-seed \<open>Global\<close>/\<open>Seed\<close> globals replace that mechanism outright. \<open>TD_side_upd_rule\<close>'s
  \<open>solve_dom\<close>/\<open>partial_post_solution\<close> being locale-generic over the update rule (as for
  PerOrigin above) is exactly what makes this a mechanical solver-call swap here too.
\<close>

definition ictx_sol_warrow ::
    "(vname \<Rightarrow> bool) \<Rightarrow> (ivl exec_dg_st \<Rightarrow> bool) \<Rightarrow> proc_table \<Rightarrow> pname list \<Rightarrow> (pp \<times> unit) set \<times> (pp \<times> unit + gk \<Rightarrow> (ivl exec_dg_st lifted, ivl exec_dg_st lifted) dg_state)" where
  "ictx_sol_warrow gs empty_pred Pi ps =
     TD_side_warrowing_apinis_Interp_solve (ictx_eqs gs empty_pred Pi ps)
       (cfg_exit (compile_prog Pi ps), ())"

definition ictx_terminates_warrow ::
    "(vname \<Rightarrow> bool) \<Rightarrow> (ivl exec_dg_st \<Rightarrow> bool) \<Rightarrow> proc_table \<Rightarrow> pname list \<Rightarrow> bool" where
  "ictx_terminates_warrow gs empty_pred Pi ps =
     TD_side_warrowing_apinis_Interp.solve_dom TYPE(gk) TYPE((ivl exec_dg_st lifted, ivl exec_dg_st lifted) dg_state)
       (ictx_eqs gs empty_pred Pi ps) (cfg_exit (compile_prog Pi ps), ())"

lemma ictx_terminates_warrow_via_solve_c:
  assumes "TD_side_warrowing_apinis_Interp_solve_c (ictx_eqs gs empty_pred Pi ps)
             (cfg_exit (compile_prog Pi ps), ()) \<noteq> None"
  shows "ictx_terminates_warrow gs empty_pred Pi ps"
  unfolding ictx_terminates_warrow_def
  by (rule TD_side_warrowing_apinis_Interp.solve_dom_of_solve_c[OF assms])

subsection \<open>The Apinis warrowing instance\<close>

lemma ictx_warrow_pp_st:
  "ictx_terminates_warrow gs empty_pred Pi ps
     \<Longrightarrow> part_post_solution (ictx_eqs gs empty_pred Pi ps)
           (cfg_exit (compile_prog Pi ps), ())
           (snd (ictx_sol_warrow gs empty_pred Pi ps))
           (fst (ictx_sol_warrow gs empty_pred Pi ps))"
  unfolding ictx_sol_warrow_def ictx_terminates_warrow_def
  by (rule TD_side_warrowing_apinis_Interp.partial_post_solution[OF _ surjective_pairing])

global_interpretation ictx_wa: ictx_solved ictx_sol_warrow ictx_terminates_warrow
  by unfold_locales (rule ictx_warrow_pp_st)

lemmas ictx_result_node_sound_warrow = ictx_wa.result_node_sound
lemmas ictx_analyse_result_eq_warrow = ictx_wa.analyse_result_eq
lemmas ictx_cinit_le_cinit_ivl_st_warrow = ictx_wa.cinit_le_cinit_ivl_st
lemmas ictx_report_ctx_proved_sound_warrow = ictx_wa.report_ctx_proved_sound
lemmas ictx_report_ctx_refuted_sound_warrow = ictx_wa.report_ctx_refuted_sound

section \<open>Warrowing-per-origin solver instantiation\<close>

text \<open>
  The fourth update rule, and the reason the development above is a locale rather than a
  copied block: \<^const>\<open>update_global_warrowing_per_origin\<close> widens each origin's own
  contribution and joins afterwards, where \<^const>\<open>update_global_warrowing_apinis\<close> widens
  the value already joined across every origin.  Two producers writing different constants
  to one global separate the two.
\<close>

definition ictx_sol_wpo ::
    "(vname \<Rightarrow> bool) \<Rightarrow> (ivl exec_dg_st \<Rightarrow> bool) \<Rightarrow> proc_table \<Rightarrow> pname list \<Rightarrow> (pp \<times> unit) set \<times> (pp \<times> unit + gk \<Rightarrow> (ivl exec_dg_st lifted, ivl exec_dg_st lifted) dg_state)" where
  "ictx_sol_wpo gs empty_pred Pi ps =
     TD_side_warrowing_per_origin_Interp_solve (ictx_eqs gs empty_pred Pi ps)
       (cfg_exit (compile_prog Pi ps), ())"

definition ictx_terminates_wpo ::
    "(vname \<Rightarrow> bool) \<Rightarrow> (ivl exec_dg_st \<Rightarrow> bool) \<Rightarrow> proc_table \<Rightarrow> pname list \<Rightarrow> bool" where
  "ictx_terminates_wpo gs empty_pred Pi ps =
     TD_side_warrowing_per_origin_Interp.solve_dom TYPE(gk)
       TYPE((ivl exec_dg_st lifted, ivl exec_dg_st lifted) dg_state)
       (ictx_eqs gs empty_pred Pi ps) (cfg_exit (compile_prog Pi ps), ())"

lemma ictx_terminates_wpo_via_solve_c:
  assumes "TD_side_warrowing_per_origin_Interp_solve_c (ictx_eqs gs empty_pred Pi ps)
             (cfg_exit (compile_prog Pi ps), ()) \<noteq> None"
  shows "ictx_terminates_wpo gs empty_pred Pi ps"
  unfolding ictx_terminates_wpo_def
  by (rule TD_side_warrowing_per_origin_Interp.solve_dom_of_solve_c[OF assms])

lemma ictx_wpo_pp_st:
  "ictx_terminates_wpo gs empty_pred Pi ps
     \<Longrightarrow> part_post_solution (ictx_eqs gs empty_pred Pi ps)
           (cfg_exit (compile_prog Pi ps), ())
           (snd (ictx_sol_wpo gs empty_pred Pi ps))
           (fst (ictx_sol_wpo gs empty_pred Pi ps))"
  unfolding ictx_sol_wpo_def ictx_terminates_wpo_def
  by (rule TD_side_warrowing_per_origin_Interp.partial_post_solution[OF _ surjective_pairing])

global_interpretation ictx_wpo: ictx_solved ictx_sol_wpo ictx_terminates_wpo
  by unfold_locales (rule ictx_wpo_pp_st)

lemmas ictx_result_node_sound_wpo = ictx_wpo.result_node_sound
lemmas ictx_analyse_result_eq_wpo = ictx_wpo.analyse_result_eq
lemmas ictx_cinit_le_cinit_ivl_st_wpo = ictx_wpo.cinit_le_cinit_ivl_st
lemmas ictx_report_ctx_proved_sound_wpo = ictx_wpo.report_ctx_proved_sound
lemmas ictx_report_ctx_refuted_sound_wpo = ictx_wpo.report_ctx_refuted_sound

section \<open>Solved-result table\<close>

text \<open>
  Whole-program convenience layer, interpreting \<^locale>\<open>dg_analysis_adapter\<close>
  directly rather than hand-rolling a temporary adapter the way Sign's own file (predating that
  locale) had to. \<open>ictx_eqs_prog\<close>/\<open>ictx_sol_prog\<close>/\<open>ictx_terminates_prog\<close> mirror
  Interval's own \<open>entry_state_eqs_prog\<close>/\<open>entry_state_sol_prog\<close>/
  \<open>entry_state_terminates_prog\<close>.
\<close>

definition ictx_eqs_prog ::
    "(vname \<Rightarrow> bool) \<Rightarrow> imp_prog
       \<Rightarrow> (pp \<times> unit, gk, (ivl exec_dg_st lifted, ivl exec_dg_st lifted) dg_state) eqsT" where
  "ictx_eqs_prog gs p =
     ictx_eqs gs (resolved_st_q_is_bot_for (declared_global_vars p))
       (prog_table p) (prog_procs p)"

definition ictx_sol_prog ::
    "(vname \<Rightarrow> bool) \<Rightarrow> imp_prog
       \<Rightarrow> (pp \<times> unit) set \<times> (pp \<times> unit + gk \<Rightarrow> (ivl exec_dg_st lifted, ivl exec_dg_st lifted) dg_state)" where
  "ictx_sol_prog gs p =
     TD_side_always_join_Interp_solve (ictx_eqs_prog gs p) (cfg_exit (prog_cfg p), ())"

definition ictx_terminates_prog :: "(vname \<Rightarrow> bool) \<Rightarrow> imp_prog \<Rightarrow> bool" where
  "ictx_terminates_prog gs p =
     ictx_terminates gs (resolved_st_q_is_bot_for (declared_global_vars p))
       (prog_table p) (prog_procs p)"

lemma ictx_terminates_prog_via_solve_c:
  assumes "TD_side_always_join_Interp_solve_c
             (ictx_eqs gs (resolved_st_q_is_bot_for (declared_global_vars p))
                (prog_table p) (prog_procs p))
             (cfg_exit (compile_prog (prog_table p) (prog_procs p)), ()) \<noteq> None"
  shows "ictx_terminates_prog gs p"
  unfolding ictx_terminates_prog_def
  using assms by (rule ictx_terminates_via_solve_c)

definition analyse_interval_ctx_result_for ::
    "(vname \<Rightarrow> bool) \<Rightarrow> imp_prog \<Rightarrow> (unit, ivl abs_state) analysis_result" where
  "analyse_interval_ctx_result_for gs p =
     Analysis_Result
       (fst (ictx_sol_prog gs p))
       (\<lambda>v ctx. normalize_point gs
                  (canonicalize_lift (resolved_st_q_is_bot_for (declared_global_vars p))
                    (locals (snd (ictx_sol_prog gs p) (Inl (v, ctx))))))"

declare analyse_interval_ctx_result_for_def [code del]

lemma analyse_interval_ctx_result_for_code [code]:
  "analyse_interval_ctx_result_for gs p =
     (let sol = ictx_sol_prog gs p; gl = declared_global_vars p
      in Analysis_Result (fst sol)
           (\<lambda>v ctx. normalize_point gs
                      (canonicalize_lift (resolved_st_q_is_bot_for gl)
                        (locals (snd sol (Inl (v, ctx)))))))"
  unfolding analyse_interval_ctx_result_for_def Let_def by (rule refl)

definition analyse_interval_ctx_result :: "imp_prog \<Rightarrow> (unit, ivl abs_state) analysis_result" where
  "analyse_interval_ctx_result p =
     analyse_interval_ctx_result_for (declared_global p) p"

subsection \<open>Solved-result tables: PerOrigin and Apinis warrowing siblings\<close>

text \<open>
  Mirror \<open>ictx_sol_prog\<close>/\<open>ictx_terminates_prog\<close>/\<open>analyse_interval_ctx_result_for\<close> (the Join
  table above) at the PerOrigin and Apinis warrowing solvers, reading the same
  \<open>ictx_eqs_prog\<close> equation system: the three-solver orthogonality Interval's Base family
  already has (\<open>analyse_interval_dg_for\<close>/\<open>_join_for\<close>/\<open>_per_origin_for\<close>,
  \<^theory>\<open>Voblint_Analysis.Interval_Exec_Sound\<close>) now also holds at the routed spine.
\<close>

definition ictx_sol_prog_per_origin ::
    "(vname \<Rightarrow> bool) \<Rightarrow> imp_prog
       \<Rightarrow> (pp \<times> unit) set \<times> (pp \<times> unit + gk \<Rightarrow> (ivl exec_dg_st lifted, ivl exec_dg_st lifted) dg_state)" where
  "ictx_sol_prog_per_origin gs p =
     TD_side_per_origin_Interp_solve (ictx_eqs_prog gs p) (cfg_exit (prog_cfg p), ())"

definition ictx_terminates_prog_per_origin :: "(vname \<Rightarrow> bool) \<Rightarrow> imp_prog \<Rightarrow> bool" where
  "ictx_terminates_prog_per_origin gs p =
     ictx_terminates_per_origin gs (resolved_st_q_is_bot_for (declared_global_vars p))
       (prog_table p) (prog_procs p)"

lemma ictx_terminates_prog_per_origin_via_solve_c:
  assumes "TD_side_per_origin_Interp_solve_c
             (ictx_eqs gs (resolved_st_q_is_bot_for (declared_global_vars p))
                (prog_table p) (prog_procs p))
             (cfg_exit (compile_prog (prog_table p) (prog_procs p)), ()) \<noteq> None"
  shows "ictx_terminates_prog_per_origin gs p"
  unfolding ictx_terminates_prog_per_origin_def
  using assms by (rule ictx_terminates_per_origin_via_solve_c)

definition analyse_interval_ctx_result_per_origin_for ::
    "(vname \<Rightarrow> bool) \<Rightarrow> imp_prog \<Rightarrow> (unit, ivl abs_state) analysis_result" where
  "analyse_interval_ctx_result_per_origin_for gs p =
     Analysis_Result
       (fst (ictx_sol_prog_per_origin gs p))
       (\<lambda>v ctx. normalize_point gs
                  (canonicalize_lift (resolved_st_q_is_bot_for (declared_global_vars p))
                    (locals (snd (ictx_sol_prog_per_origin gs p) (Inl (v, ctx))))))"

declare analyse_interval_ctx_result_per_origin_for_def [code del]

lemma analyse_interval_ctx_result_per_origin_for_code [code]:
  "analyse_interval_ctx_result_per_origin_for gs p =
     (let sol = ictx_sol_prog_per_origin gs p; gl = declared_global_vars p
      in Analysis_Result (fst sol)
           (\<lambda>v ctx. normalize_point gs
                      (canonicalize_lift (resolved_st_q_is_bot_for gl)
                        (locals (snd sol (Inl (v, ctx)))))))"
  unfolding analyse_interval_ctx_result_per_origin_for_def Let_def by (rule refl)

definition analyse_interval_ctx_result_per_origin :: "imp_prog \<Rightarrow> (unit, ivl abs_state) analysis_result" where
  "analyse_interval_ctx_result_per_origin p =
     analyse_interval_ctx_result_per_origin_for (declared_global p) p"

definition ictx_sol_prog_warrow ::
    "(vname \<Rightarrow> bool) \<Rightarrow> imp_prog
       \<Rightarrow> (pp \<times> unit) set \<times> (pp \<times> unit + gk \<Rightarrow> (ivl exec_dg_st lifted, ivl exec_dg_st lifted) dg_state)" where
  "ictx_sol_prog_warrow gs p =
     TD_side_warrowing_apinis_Interp_solve (ictx_eqs_prog gs p) (cfg_exit (prog_cfg p), ())"

definition ictx_terminates_prog_warrow :: "(vname \<Rightarrow> bool) \<Rightarrow> imp_prog \<Rightarrow> bool" where
  "ictx_terminates_prog_warrow gs p =
     ictx_terminates_warrow gs (resolved_st_q_is_bot_for (declared_global_vars p))
       (prog_table p) (prog_procs p)"

lemma ictx_terminates_prog_warrow_via_solve_c:
  assumes "TD_side_warrowing_apinis_Interp_solve_c
             (ictx_eqs gs (resolved_st_q_is_bot_for (declared_global_vars p))
                (prog_table p) (prog_procs p))
             (cfg_exit (compile_prog (prog_table p) (prog_procs p)), ()) \<noteq> None"
  shows "ictx_terminates_prog_warrow gs p"
  unfolding ictx_terminates_prog_warrow_def
  using assms by (rule ictx_terminates_warrow_via_solve_c)

definition analyse_interval_ctx_result_warrow_for ::
    "(vname \<Rightarrow> bool) \<Rightarrow> imp_prog \<Rightarrow> (unit, ivl abs_state) analysis_result" where
  "analyse_interval_ctx_result_warrow_for gs p =
     Analysis_Result
       (fst (ictx_sol_prog_warrow gs p))
       (\<lambda>v ctx. normalize_point gs
                  (canonicalize_lift (resolved_st_q_is_bot_for (declared_global_vars p))
                    (locals (snd (ictx_sol_prog_warrow gs p) (Inl (v, ctx))))))"

declare analyse_interval_ctx_result_warrow_for_def [code del]

lemma analyse_interval_ctx_result_warrow_for_code [code]:
  "analyse_interval_ctx_result_warrow_for gs p =
     (let sol = ictx_sol_prog_warrow gs p; gl = declared_global_vars p
      in Analysis_Result (fst sol)
           (\<lambda>v ctx. normalize_point gs
                      (canonicalize_lift (resolved_st_q_is_bot_for gl)
                        (locals (snd sol (Inl (v, ctx)))))))"
  unfolding analyse_interval_ctx_result_warrow_for_def Let_def by (rule refl)

definition analyse_interval_ctx_result_warrow :: "imp_prog \<Rightarrow> (unit, ivl abs_state) analysis_result" where
  "analyse_interval_ctx_result_warrow p =
     analyse_interval_ctx_result_warrow_for (declared_global p) p"

subsection \<open>The global unknowns the same solve side-effects\<close>

text \<open>
  \<^const>\<open>ctx_solved_for\<close> at this domain's warrowing solve, with \<^const>\<open>Global\<close> and
  \<^const>\<open>Seed\<close> handed to \<^const>\<open>seed_global_keys\<close> the way \<^const>\<open>routed_extra_g\<close>
  already takes them. Nothing here is domain-specific but the solve and the two
  constructors.
\<close>

definition analyse_interval_ctx_solved_warrow_for ::
    "(vname \<Rightarrow> bool) \<Rightarrow> imp_prog
     \<Rightarrow> (unit, ivl abs_state) analysis_result
          \<times> (String.literal \<times> ivl abs_state lifted) list" where
  "analyse_interval_ctx_solved_warrow_for =
     ctx_solved_for ictx_sol_prog_warrow (unit_seed_global_keys Global Seed)"

lemma fst_analyse_interval_ctx_solved_warrow_for:
  "fst (analyse_interval_ctx_solved_warrow_for gs p)
     = analyse_interval_ctx_result_warrow_for gs p"
  by (simp add: analyse_interval_ctx_solved_warrow_for_def fst_ctx_solved_for
      analyse_interval_ctx_result_warrow_for_def Let_def)

subsection \<open>Solved-result table: warrowing per origin\<close>

definition ictx_sol_prog_wpo ::
    "(vname \<Rightarrow> bool) \<Rightarrow> imp_prog
       \<Rightarrow> (pp \<times> unit) set \<times> (pp \<times> unit + gk \<Rightarrow> (ivl exec_dg_st lifted, ivl exec_dg_st lifted) dg_state)" where
  "ictx_sol_prog_wpo gs p =
     TD_side_warrowing_per_origin_Interp_solve (ictx_eqs_prog gs p) (cfg_exit (prog_cfg p), ())"

definition ictx_terminates_prog_wpo :: "(vname \<Rightarrow> bool) \<Rightarrow> imp_prog \<Rightarrow> bool" where
  "ictx_terminates_prog_wpo gs p =
     ictx_terminates_wpo gs (resolved_st_q_is_bot_for (declared_global_vars p))
       (prog_table p) (prog_procs p)"

lemma ictx_terminates_prog_wpo_via_solve_c:
  assumes "TD_side_warrowing_per_origin_Interp_solve_c
             (ictx_eqs gs (resolved_st_q_is_bot_for (declared_global_vars p))
                (prog_table p) (prog_procs p))
             (cfg_exit (compile_prog (prog_table p) (prog_procs p)), ()) \<noteq> None"
  shows "ictx_terminates_prog_wpo gs p"
  unfolding ictx_terminates_prog_wpo_def
  using assms by (rule ictx_terminates_wpo_via_solve_c)

definition analyse_interval_ctx_result_wpo_for ::
    "(vname \<Rightarrow> bool) \<Rightarrow> imp_prog \<Rightarrow> (unit, ivl abs_state) analysis_result" where
  "analyse_interval_ctx_result_wpo_for gs p =
     Analysis_Result
       (fst (ictx_sol_prog_wpo gs p))
       (\<lambda>v ctx. normalize_point gs
                  (canonicalize_lift (resolved_st_q_is_bot_for (declared_global_vars p))
                    (locals (snd (ictx_sol_prog_wpo gs p) (Inl (v, ctx))))))"

declare analyse_interval_ctx_result_wpo_for_def [code del]

lemma analyse_interval_ctx_result_wpo_for_code [code]:
  "analyse_interval_ctx_result_wpo_for gs p =
     (let sol = ictx_sol_prog_wpo gs p; gl = declared_global_vars p
      in Analysis_Result (fst sol)
           (\<lambda>v ctx. normalize_point gs
                      (canonicalize_lift (resolved_st_q_is_bot_for gl)
                        (locals (snd sol (Inl (v, ctx)))))))"
  unfolding analyse_interval_ctx_result_wpo_for_def Let_def by (rule refl)

definition analyse_interval_ctx_result_wpo :: "imp_prog \<Rightarrow> (unit, ivl abs_state) analysis_result" where
  "analyse_interval_ctx_result_wpo p =
     analyse_interval_ctx_result_wpo_for (declared_global p) p"
end
