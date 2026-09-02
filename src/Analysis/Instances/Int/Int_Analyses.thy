theory Int_Analyses
  imports
    "Voblint_Analysis.Int_Sound"
    "Voblint_Analysis.Int_Classify"
    "Voblint_Analysis.Int_Exec"
    "Voblint_Exec.Monovariant_Analysis_Result"
    "Voblint_Exec.Routed_Domain_Exec"
    "Voblint_Exec.DG_Local_State_Exec"
    "Voblint_Framework.DG_Local_State_Spec"
    "Voblint_Framework.DG_LTR_Sound"
    "Voblint_Framework.Routed_Analysis_Sound"
    "Voblint_Framework.Routed_Context"
    "Voblint_Framework.Routed_Context_Unit"
    "Voblint_Framework.Activation_Backbone"
    "Voblint_Framework.Analysis_Result"
    "Voblint_Framework.Call_String_Context"
    "Voblint_Solver.TD_Solver_Menu"
    "Voblint_Compile.Compile_Invariants"
    "Voblint_CFG.CFG_Prune"
    "Voblint_VIMP.VIMP_Program"
    "TD.TD_side_upd_rule"
    Call_String_Routed_Context
    Entry_State_Routed_Context
begin

chapter \<open>How the Int product is run under each supported context policy\<close>

text \<open>
  The Int product's analysis package -- specification, concretization and
  soundness -- lives in \<^theory>\<open>Voblint_Analysis.Int_Sound\<close> and mentions no
  context. This theory supplies the configurations: for each supported context
  policy, the equation system that pairing generates, its solved table, the
  coverage premises the solver's reachable set must satisfy, and the result and
  report tables a caller consumes.

  Like Interval, Int carries a second axis: besides the default always-join
  solver, the same configurations are instantiated at the PerOrigin,
  Apinis-warrowing and warrowing-per-origin disciplines, and each is further
  parameterised by a \<^typ>\<open>refine_mode\<close>. Which solver runs an equation system
  is independent of which context policy generated it.

  Global keys are \<^type>\<open>routed_gk\<close>, with \<^const>\<open>Analysis_Global\<close> at
  \<^typ>\<open>unit\<close> since Int publishes no named global of its own; the call-string
  configuration uses the shared \<^typ>\<open>call_string_gk\<close>.
\<close>

section \<open>Int at the routed spine, instantiated at the unit context\<close>

text \<open>
  Redirects the composite integer domain's production Base-family (\<^const>\<open>dg_gen_of\<close>)
  analysis onto the routed D/G spine (\<^locale>\<open>dg_ctx_activation_base\<close>,
  \<^locale>\<open>unit_routed_context\<close>) that Interval's own entry-state and call-string context
  analyses already use, mirroring Sign's own routed-unit-context production cutover
  exactly. The context here is \<^typ>\<open>unit\<close>:
  \<^locale>\<open>unit_routed_context\<close> (\<^theory>\<open>Voblint_Framework.Routed_Context_Unit\<close>) fixes
  \<^const>\<open>route_unit\<close>, so every routing-agreement obligation that Interval's
  formals-context instance must prove from its own transfer facts collapses here
  to a free lemma about the constant function \<^const>\<open>route_unit\<close>.

  Unlike Sign and Interval, \<^typ>\<open>int_dom\<close> threads a \<^typ>\<open>refine_mode\<close> parameter
  (\<^const>\<open>int_tf_st_for\<close>, \<^const>\<open>int_dom_enter_st_for\<close>, both fixed here as a genuine
  ``mode'' argument rather than pinned to \<^const>\<open>Refine_Fixpoint\<close>): every commute and
  soundness fact this development needs is already split per mode in
  \<^theory>\<open>Voblint_Analysis.Int_Exec\<close>, so recombining them into one mode-generic
  fact is a three-way \<open>cases mode\<close> citing an existing lemma per branch, not new
  proof content.

  Soundness below is derived directly from \<^locale>\<open>dg_ctx_activation_base\<close>'s generic
  machinery against the collecting semantics, exactly as Sign's and Interval's own
  routed analyses are derived. No comparison to Int's Base-family production result is
  attempted or needed: \<^const>\<open>dg_gen_of\<close> never appears in this development.

  The public result/report table (Section 7) interprets \<^locale>\<open>dg_analysis_adapter\<close>
  directly instead of hand-rolling one: Sign's own file predates that locale.
\<close>

subsection \<open>Global key: real globals vs callee-entry seed slots\<close>

text \<open>
  \<^typ>\<open>unit\<close> context, so the seed constructor's second field is \<^typ>\<open>unit\<close> rather
  than an interesting per-context payload: exactly one seed slot per callee entry.
\<close>


subsection \<open>The routed unit-context D/G spec\<close>

text \<open>
  The same Base-style whole-state specification the production
  \<^const>\<open>analyse_int_dg_eqs_for\<close> already solves over
  (\<^theory>\<open>Voblint_Analysis.Int_Exec_Sound\<close>), at the same
  \<^const>\<open>int_tf_st_for\<close>/\<^const>\<open>int_dom_enter_st_for\<close> primitives, \<open>mode\<close> included.
  Only the equation-generator wrapped around this spec changes (\<^const>\<open>dg_gen_of\<close>
  there, the routed keyed-seed generator here) --- the spec itself, and every
  domain-transfer soundness fact about it, is untouched. Argument order (\<open>mode\<close>,
  \<open>empty_pred\<close>, \<open>gs\<close>) matches \<^const>\<open>analyse_int_dg_eqs_for\<close>'s own.
\<close>

subsection \<open>The routed equation system and its executable solution\<close>

definition ictx_eqs ::
    "refine_mode \<Rightarrow> (int_dom exec_dg_st \<Rightarrow> bool) \<Rightarrow> (vname \<Rightarrow> bool) \<Rightarrow> proc_table \<Rightarrow> pname list \<Rightarrow> (pp \<times> unit, (unit, unit) routed_gk, (int_dom exec_dg_st lifted, int_dom exec_dg_st lifted) dg_state) eqsT" where
  "ictx_eqs mode empty_pred gs Pi ps =
     side_cfg_T_eff_keyed_seed_dg_buffered intra_predecessor_addr_list (\<lambda>_. Analysis_Global ())
       route_unit
       (\<lambda>ctx' src a. dg_spec_edge_tree (int_dom_spec mode empty_pred gs) a src (\<lambda>_. Analysis_Global ()))
       (routed_cmb_g (int_dom_spec mode empty_pred gs) (Analysis_Global ()) Activation_Seed
          (static_resolve (compile_prog Pi ps)))
       (routed_extra_g Activation_Seed (Analysis_Global ()))
       (compile_prog Pi ps) Bot (Lifted cinit_int_dom_st) Bot"

definition ictx_sol ::
    "refine_mode \<Rightarrow> (int_dom exec_dg_st \<Rightarrow> bool) \<Rightarrow> (vname \<Rightarrow> bool) \<Rightarrow> proc_table \<Rightarrow> pname list \<Rightarrow> (pp \<times> unit) set \<times> (pp \<times> unit + (unit, unit) routed_gk \<Rightarrow> (int_dom exec_dg_st lifted, int_dom exec_dg_st lifted) dg_state)" where
  "ictx_sol mode empty_pred gs Pi ps =
     TD_side_always_join_Interp_solve (ictx_eqs mode empty_pred gs Pi ps)
       (cfg_exit (compile_prog Pi ps), ())"

definition ictx_terminates ::
    "refine_mode \<Rightarrow> (int_dom exec_dg_st \<Rightarrow> bool) \<Rightarrow> (vname \<Rightarrow> bool) \<Rightarrow> proc_table \<Rightarrow> pname list \<Rightarrow> bool" where
  "ictx_terminates mode empty_pred gs Pi ps =
     TD_side_always_join_Interp.solve_dom TYPE((unit, unit) routed_gk) TYPE((int_dom exec_dg_st lifted, int_dom exec_dg_st lifted) dg_state)
       (ictx_eqs mode empty_pred gs Pi ps) (cfg_exit (compile_prog Pi ps), ())"

lemma ictx_terminates_via_solve_c:
  assumes "TD_side_always_join_Interp_solve_c (ictx_eqs mode empty_pred gs Pi ps)
             (cfg_exit (compile_prog Pi ps), ()) \<noteq> None"
  shows "ictx_terminates mode empty_pred gs Pi ps"
  unfolding ictx_terminates_def
  by (rule TD_side_always_join_Interp.solve_dom_of_solve_c[OF assms])

subsection \<open>Route agreement collapses to a free lemma\<close>


subsection \<open>Domain commute facts, at the routed unit spec\<close>

text \<open>
  \<open>int_tf_st_for\<close>/\<open>int_dom_enter_st_for\<close> are themselves defined by a case split on
  \<open>mode\<close> (\<^theory>\<open>Voblint_Analysis.Int_Exec_Sound\<close>), so the mode-generic commute facts
  below are the same case split, citing each mode's own commute theorem
  (\<open>int_tf_st_never_for_commute\<close> etc., \<^theory>\<open>Voblint_Analysis.Int_Exec\<close>) unchanged.
\<close>

text \<open>
  \<^locale>\<open>routed_domain_exec\<close> derives exactly this shape once, generic in a domain:
  an interpretation at Int's own mode-generic commute facts just above replaces what used
  to be Int's own copy of the derivation. It adds only the seed-key pair, its
  distinctness, and the two routing functions on top of
  \<^locale>\<open>routed_dg_domain_exec\<close>, so the interpretation carries no Int mathematics.
  \<^const>\<open>route_unit\<close> ignores its \<open>'D\<close> argument outright, so routing agreement is free
  inside the locale rather than an Int obligation at all.
\<close>

text \<open>
  The abstract-carrier soundness of the spec, generic in \<open>mode\<close>: a three-way case split
  citing Int's own per-mode transfer-soundness facts.  The executable-carrier soundness
  \<open>int_dom_sound_exec\<close> below pulls it back along the readback.
\<close>

text \<open>The concretization the executable-carrier interpretations below use: a local
  unknown means \<^const>\<open>gamma_state_lift\<close> of its readback, the global slot is ignored as
  in \<^const>\<open>gamma_dg_local_state\<close>. Named at top level so a downstream theory can state it.\<close>

context
  fixes gs :: "vname \<Rightarrow> bool" and empty_pred :: "int_dom exec_dg_st \<Rightarrow> bool" and mode :: refine_mode
  assumes exact: "\<And>s. empty_pred s = is_empty_state (fun_of_resolved_st_q_for gs s)"
begin

interpretation int_unit: routed_domain_exec
  gs empty_pred "int_tf_st_for mode gs" "int_dom_enter_st_for mode gs" "int_tf_for mode gs"
  "Analysis_Global ()" Activation_Seed route_unit route_unit static_resolve static_resolve
  by unfold_locales
     (rule int_tf_st_for_commute, rule int_dom_enter_st_for_commute, rule exact, simp, simp,
      simp add: static_resolve_def)

lemmas int_pp_st_gen = int_unit.pp_st

end

section \<open>The solver-generic instantiation\<close>

text \<open>
  Everything downstream of the executable post-solution reaches the solver through exactly one
  fact: that the solved pair is a \<^const>\<open>part_post_solution\<close> of \<^const>\<open>ictx_eqs\<close>.  The update
  rule itself never appears again.  \<open>ictx_solved\<close> therefore fixes the solved pair and its
  termination predicate and assumes that single fact, so each update rule contributes an
  interpretation rather than a copy of the development.
\<close>

locale ictx_solved =
  fixes ictx_sol :: "refine_mode \<Rightarrow> (int_dom exec_dg_st \<Rightarrow> bool) \<Rightarrow> (vname \<Rightarrow> bool) \<Rightarrow> proc_table
                  \<Rightarrow> pname list \<Rightarrow> (pp \<times> unit) set
                     \<times> (pp \<times> unit + (unit, unit) routed_gk \<Rightarrow> (int_dom exec_dg_st lifted, int_dom exec_dg_st lifted) dg_state)"
    and ictx_terminates :: "refine_mode \<Rightarrow> (int_dom exec_dg_st \<Rightarrow> bool) \<Rightarrow> (vname \<Rightarrow> bool) \<Rightarrow> proc_table
                         \<Rightarrow> pname list \<Rightarrow> bool"
  assumes pp_st:
    "ictx_terminates mode empty_pred gs Pi ps
       \<Longrightarrow> part_post_solution (ictx_eqs mode empty_pred gs Pi ps)
             (cfg_exit (compile_prog Pi ps), ())
             (snd (ictx_sol mode empty_pred gs Pi ps))
             (fst (ictx_sol mode empty_pred gs Pi ps))"
begin

text \<open>The solver's post-solution, for the unbuffered routed generator at the executable
  spec: the shape \<^locale>\<open>dg_ctx_activation_base\<close> consumes directly.\<close>

theorem ictx_pp_routed:
  assumes solves: "ictx_terminates mode empty_pred gs Pi ps"
    and exact: "\<And>s. empty_pred s = is_empty_state (fun_of_resolved_st_q_for gs s)"
  shows
  "part_post_solution
     (side_cfg_T_eff_keyed_seed_dg intra_predecessor_addr_list (\<lambda>_. Analysis_Global ()) route_unit
        (\<lambda>ctx' src a. dg_spec_edge_tree (int_dom_spec mode empty_pred gs) a src (\<lambda>_. Analysis_Global ()))
        (routed_cmb_g (int_dom_spec mode empty_pred gs) (Analysis_Global ()) Activation_Seed
           (static_resolve (compile_prog Pi ps)))
        (routed_extra_g Activation_Seed (Analysis_Global ()))
        (compile_prog Pi ps) Bot (Lifted cinit_int_dom_st) Bot)
     (cfg_exit (compile_prog Pi ps), ())
     (snd (ictx_sol mode empty_pred gs Pi ps)) (fst (ictx_sol mode empty_pred gs Pi ps))"
  using pp_st[OF solves] unfolding ictx_eqs_def int_dom_spec_def by (rule int_pp_st_gen[OF exact])

text \<open>
  The routed spine is interpreted at Int's executable carrier and fed the solver's own
  table: a local unknown concretizes to \<^const>\<open>gamma_state_lift\<close> of its readback, the
  covered reader \<open>ictx_sg_st\<close> hands the table's local slot through unchanged, and no
  solved system is transported between carriers.
\<close>

definition ictx_sg_st ::
    "refine_mode \<Rightarrow> (int_dom exec_dg_st \<Rightarrow> bool) \<Rightarrow> (vname \<Rightarrow> bool) \<Rightarrow> proc_table
       \<Rightarrow> pname list \<Rightarrow> pp \<times> unit + (unit, unit) routed_gk \<Rightarrow> int_dom exec_dg_st lifted" where
  "ictx_sg_st mode empty_pred gs Pi ps k =
     (case k of
        Inl (v, ctx) \<Rightarrow>
          (if (v, ctx) \<in> fst (ictx_sol mode empty_pred gs Pi ps)
           then locals (snd (ictx_sol mode empty_pred gs Pi ps) (Inl (v, ctx)))
           else Bot)
      | Inr _ \<Rightarrow> Bot)"

context
  fixes mode :: refine_mode and empty_pred :: "int_dom exec_dg_st \<Rightarrow> bool" and gs :: "vname \<Rightarrow> bool"
    and Pi :: proc_table and ps :: "pname list"
  assumes solves: "ictx_terminates mode empty_pred gs Pi ps"
    and exact: "\<And>s. empty_pred s = is_empty_state (fun_of_resolved_st_q_for gs s)"
    and entry_cov: "(cfg_entry (compile_prog Pi ps), ()) \<in> fst (ictx_sol mode empty_pred gs Pi ps)"
    and fwd_ok: "\<And>u a v ctx. (u, ctx) \<in> fst (ictx_sol mode empty_pred gs Pi ps)
                   \<Longrightarrow> (u, a, v) \<in> intra (compile_prog Pi ps)
                   \<Longrightarrow> (v, ctx) \<in> fst (ictx_sol mode empty_pred gs Pi ps)"
    and call_fwd_ok: "\<And>u ctx dst pars args p cont.
        (u, ctx) \<in> fst (ictx_sol mode empty_pred gs Pi ps)
        \<Longrightarrow> (u, CallEdge dst pars args, FunctionEntry p, cont) \<in> calls (compile_prog Pi ps)
        \<Longrightarrow> (FunctionEntry p, ()) \<in> fst (ictx_sol mode empty_pred gs Pi ps)"
    and comb_fwd_ok: "\<And>cl c1 dst pars args p cont.
        (cl, c1) \<in> fst (ictx_sol mode empty_pred gs Pi ps)
        \<Longrightarrow> (cl, CallEdge dst pars args, FunctionEntry p, cont) \<in> calls (compile_prog Pi ps)
        \<Longrightarrow> (cont, c1) \<in> fst (ictx_sol mode empty_pred gs Pi ps)"
begin

subsection \<open>The solver's table as the solved system\<close>

interpretation ictx_compiled: compiled_cfg Pi ps "compile_prog Pi ps"
  by (unfold_locales; simp add: compile_prog_finite)

lemmas ictx_fin = ictx_compiled.finite_intra
lemmas ictx_finC = ictx_compiled.finite_calls

lemma ictx_sg_st_covered:
  "(v, ctx) \<in> fst (ictx_sol mode empty_pred gs Pi ps)
   \<Longrightarrow> ictx_sg_st mode empty_pred gs Pi ps (Inl (v, ctx))
         = locals (snd (ictx_sol mode empty_pred gs Pi ps) (Inl (v, ctx)))"
  by (simp add: ictx_sg_st_def)

lemma ictx_sg_st_uncovered_empty:
  "(v, ctx) \<notin> fst (ictx_sol mode empty_pred gs Pi ps)
     \<Longrightarrow> gamma_state_lift (map_lift (fun_of_resolved_st_q_for gs)
           (ictx_sg_st mode empty_pred gs Pi ps (Inl (v, ctx)))) = {}"
  by (simp add: ictx_sg_st_def)

subsection \<open>Instantiating the generic DG-native activation discharge\<close>

interpretation ictx_dg_base: sound_dg_spec "int_dom_spec mode empty_pred gs" "int_dom_gamma gs" gs
  by (rule int_dom_sound_exec[OF exact])

interpretation ictx_routed: unit_routed_context "int_dom_spec mode empty_pred gs" "int_dom_gamma gs" gs
    "compile_prog Pi ps" "Analysis_Global ()" Bot "Lifted cinit_int_dom_st" Bot
    "snd (ictx_sol mode empty_pred gs Pi ps)" "fst (ictx_sol mode empty_pred gs Pi ps)"
    "(cfg_exit (compile_prog Pi ps), ())" "ictx_sg_st mode empty_pred gs Pi ps" Activation_Seed
    "\<lambda>m. gamma_state_lift (map_lift (fun_of_resolved_st_q_for gs) m)"
proof (unfold_locales, goal_cases FinE PP SgCov SgUncov Fwd FinC SeedKey CallFwd CombFwd EnterAgree)
  case FinE show ?case by (rule ictx_fin)
next
  case PP show ?case by (rule ictx_pp_routed[OF solves exact])
next
  case (SgCov v ctx) then show ?case
    by (simp add: ictx_sg_st_def int_dom_gamma_def)
next
  case (SgUncov v ctx) then show ?case by (rule ictx_sg_st_uncovered_empty)
next
  case (Fwd u a v ctx) then show ?case by (rule fwd_ok)
next
  case FinC show ?case by (rule ictx_finC)
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

subsection \<open>Activation-indexed collecting soundness\<close>

lemma ictx_cinit_le_cinit_int_dom_st:
  "cinit_stores gs \<subseteq> int_dom_gamma gs (Lifted cinit_int_dom_st) Bot"
  by (auto simp: int_dom_gamma_def cinit_stores_def gamma_state_def fun_of_resolved_st_q_for_def
                 fun_of_st_cinit_int_dom_st_for gamma_int_dom_top)
subsection \<open>The public result/report table, via the generic adapter locale\<close>

text \<open>
  \<^locale>\<open>dg_analysis_adapter\<close> at the same executable solved system as
  \<open>ictx_routed\<close> above, handed the readback as \<open>rd\<close>; the classifier obligations are
  \<open>int_classify_check_proved\<close>/\<open>int_classify_check_refuted\<close>
  (\<^theory>\<open>Voblint_Analysis.Int_Classify\<close>).
\<close>

interpretation ictx_adapter: dg_analysis_adapter "int_dom_spec mode empty_pred gs" "int_dom_gamma gs" gs
    "compile_prog Pi ps" "Analysis_Global ()" route_unit Bot "Lifted cinit_int_dom_st" Bot
    "snd (ictx_sol mode empty_pred gs Pi ps)" "fst (ictx_sol mode empty_pred gs Pi ps)"
    "(cfg_exit (compile_prog Pi ps), ())" "ictx_sg_st mode empty_pred gs Pi ps"
    Activation_Seed "\<lambda>m. gamma_state_lift (map_lift (fun_of_resolved_st_q_for gs) m)" enterc_unit
    "map_lift (fun_of_resolved_st_q_for gs)" int_classify_check
proof (unfold_locales, goal_cases FinE PP SgCov SgUncov Fwd FinC SeedKey ResolveSound
    RouteEnterc CallFwd CombFwd EnterAgree GammaRd ClProved ClRefuted)
  case FinE show ?case by (rule ictx_fin)
next
  case PP show ?case by (rule ictx_pp_routed[OF solves exact])
next
  case (SgCov v c)
  thus ?case by (simp add: ictx_sg_st_def int_dom_gamma_def)
next
  case (SgUncov v c)
  thus ?case by (simp add: ictx_sg_st_def)
next
  case (Fwd u a v c)
  thus ?case by (rule fwd_ok)
next
  case FinC show ?case by (rule ictx_finC)
next
  case (SeedKey p ctx) show ?case by simp
next
  case (ResolveSound u ctx dst pars args p cont s)
  thus ?case by (simp add: static_resolve_iff[OF ictx_finC])
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
      ce': "(cl, CallEdge dst' pars' args', FunctionEntry p', cont')
              \<in> calls (compile_prog Pi ps)"
    and es_eq: "es = call_enter gs (CallEdge dst' pars' args') s"
    using ces unfolding call_enter_store_def by blast
  have "CallEdge dst' pars' args' = CallEdge dst pars args"
    using compile_prog_calls_source_unique[OF ce' ce] by simp
  thus ?case using es_eq by simp
next
  case (GammaRd d g')
  show ?case by (simp add: int_dom_gamma_def)
next
  case (ClProved c d s)
  thus ?case by (rule int_classify_check_proved)
next
  case (ClRefuted c d s)
  thus ?case by (rule int_classify_check_refuted)
qed

lemmas ictx_analyse_result_def = ictx_adapter.analyse_result_def
lemmas ictx_analyse_report_ctx_def = ictx_adapter.analyse_report_ctx_def
lemmas ictx_analyse_report_def = ictx_adapter.analyse_report_def
lemmas ictx_analyse_report_ctx_proved_sound = ictx_adapter.analyse_report_ctx_proved_sound
lemmas ictx_analyse_report_ctx_refuted_sound = ictx_adapter.analyse_report_ctx_refuted_sound

text \<open>
  \<open>ictx_result_node_sound\<close> re-exports the adapter's generic node-soundness bridge
  (\<^theory>\<open>Voblint_Framework.DG_Analysis_Adapter\<close>). \<open>ictx_analyse_result_eq\<close> identifies that
  reading with the raw-tuple shape \<open>analyse_int_ctx_result_for\<close> (defined below)
  already builds by hand, mirroring \<open>Interval_Analyses.ictx_analyse_result_eq\<close>.
\<close>

lemmas ictx_result_node_sound = ictx_adapter.analyse_result_node_sound
lemmas ictx_activation_collect_sound = ictx_routed.routed.activation_collect_dg_sound

lemma ictx_analyse_result_eq:
  "lookup_context ictx_adapter.analyse_result v ctx =
     (if (v, ctx) \<in> fst (ictx_sol mode empty_pred gs Pi ps)
      then normalize_point gs
             (canonicalize_lift empty_pred (locals (snd (ictx_sol mode empty_pred gs Pi ps) (Inl (v, ctx)))))
      else Bot)"
  unfolding ictx_adapter.lookup_context_analyse_result
  by (cases "locals (snd (ictx_sol mode empty_pred gs Pi ps) (Inl (v, ctx)))")
     (simp_all add: exact normalize_lift_def)

end

end

section \<open>The four update-rule instances\<close>

text \<open>Each rule's entire obligation is \<open>partial_post_solution\<close>, which
  \<^locale>\<open>TD_side_upd_rule\<close> proves once for every update rule.\<close>

lemma ictx_join_pp_st:
  "ictx_terminates mode empty_pred gs Pi ps
     \<Longrightarrow> part_post_solution (ictx_eqs mode empty_pred gs Pi ps)
           (cfg_exit (compile_prog Pi ps), ())
           (snd (ictx_sol mode empty_pred gs Pi ps))
           (fst (ictx_sol mode empty_pred gs Pi ps))"
  unfolding ictx_sol_def ictx_terminates_def
  by (rule TD_side_always_join_Interp.partial_post_solution[OF _ surjective_pairing])

global_interpretation ictx_join: ictx_solved ictx_sol ictx_terminates
  by unfold_locales (rule ictx_join_pp_st)

lemmas ictx_result_node_sound = ictx_join.ictx_result_node_sound
lemmas ictx_analyse_result_eq = ictx_join.ictx_analyse_result_eq
lemmas ictx_cinit_le_cinit_int_dom_st = ictx_join.ictx_cinit_le_cinit_int_dom_st
lemmas ictx_activation_collect_sound = ictx_join.ictx_activation_collect_sound
lemmas ictx_analyse_report_ctx_proved_sound = ictx_join.ictx_analyse_report_ctx_proved_sound
lemmas ictx_analyse_report_ctx_refuted_sound = ictx_join.ictx_analyse_report_ctx_refuted_sound
lemmas ictx_analyse_result_def = ictx_join.ictx_analyse_result_def
lemmas ictx_analyse_report_ctx_def = ictx_join.ictx_analyse_report_ctx_def
lemmas ictx_analyse_report_def = ictx_join.ictx_analyse_report_def

section \<open>Whole-program convenience layer\<close>

text \<open>
  Mirrors Sign's own \<open>sctx_eqs_prog\<close>/\<open>sctx_sol_prog\<close>/\<open>sctx_terminates_prog\<close>: the
  same per-program instances at \<^const>\<open>declared_global_vars\<close>/\<^const>\<open>declared_global\<close>,
  so a caller supplies only \<open>mode\<close>, \<open>gs\<close>, and the \<^typ>\<open>imp_prog\<close> value.
\<close>

definition ictx_eqs_prog ::
    "refine_mode \<Rightarrow> (vname \<Rightarrow> bool) \<Rightarrow> imp_prog
       \<Rightarrow> (pp \<times> unit, (unit, unit) routed_gk, (int_dom exec_dg_st lifted, int_dom exec_dg_st lifted) dg_state) eqsT" where
  "ictx_eqs_prog mode gs p =
     ictx_eqs mode (resolved_st_q_is_bot_for (declared_global_vars p))
       gs (prog_table p) (prog_procs p)"

definition ictx_sol_prog ::
    "refine_mode \<Rightarrow> (vname \<Rightarrow> bool) \<Rightarrow> imp_prog
       \<Rightarrow> (pp \<times> unit) set \<times> (pp \<times> unit + (unit, unit) routed_gk \<Rightarrow> (int_dom exec_dg_st lifted, int_dom exec_dg_st lifted) dg_state)" where
  "ictx_sol_prog mode gs p =
     TD_side_always_join_Interp_solve (ictx_eqs_prog mode gs p) (cfg_exit (prog_cfg p), ())"

definition ictx_terminates_prog :: "refine_mode \<Rightarrow> (vname \<Rightarrow> bool) \<Rightarrow> imp_prog \<Rightarrow> bool" where
  "ictx_terminates_prog mode gs p =
     ictx_terminates mode (resolved_st_q_is_bot_for (declared_global_vars p))
       gs (prog_table p) (prog_procs p)"

lemma ictx_terminates_prog_via_solve_c:
  assumes "TD_side_always_join_Interp_solve_c
             (ictx_eqs mode (resolved_st_q_is_bot_for (declared_global_vars p))
                gs (prog_table p) (prog_procs p))
             (cfg_exit (compile_prog (prog_table p) (prog_procs p)), ()) \<noteq> None"
  shows "ictx_terminates_prog mode gs p"
  unfolding ictx_terminates_prog_def
  using assms by (rule ictx_terminates_via_solve_c)

text \<open>
  \<open>analyse_int_ctx_result_for\<close> is the routed-spine, always-join solved-result table,
  read as a \<^typ>\<open>(unit, int_dom abs_state) analysis_result\<close>: mirrors
  \<open>Interval_Analyses.analyse_interval_ctx_result_for\<close> exactly, at the
  same \<open>ictx_sol_prog\<close> instance above, generic in \<open>mode\<close> to match
  \<open>ictx_sol_prog\<close>'s own signature. The \<open>[code]\<close> swap avoids re-solving per
  lookup: \<^const>\<open>ictx_sol_prog\<close> is bound once as \<open>sol\<close>, then read pointwise via
  \<^const>\<open>normalize_point\<close>/\<^const>\<open>canonicalize_lift\<close>, exactly as
  \<open>monovariant_analysis_result_for\<close> does internally.
\<close>

definition analyse_int_ctx_result_for ::
    "refine_mode \<Rightarrow> (vname \<Rightarrow> bool) \<Rightarrow> imp_prog \<Rightarrow> (unit, int_dom abs_state) analysis_result" where
  "analyse_int_ctx_result_for mode gs p =
     Analysis_Result
       (fst (ictx_sol_prog mode gs p))
       (\<lambda>v ctx. normalize_point gs
                  (canonicalize_lift (resolved_st_q_is_bot_for (declared_global_vars p))
                    (locals (snd (ictx_sol_prog mode gs p) (Inl (v, ctx))))))"

declare analyse_int_ctx_result_for_def [code del]

lemma analyse_int_ctx_result_for_code [code]:
  "analyse_int_ctx_result_for mode gs p =
     (let sol = ictx_sol_prog mode gs p; gl = declared_global_vars p
      in Analysis_Result (fst sol)
           (\<lambda>v ctx. normalize_point gs
                      (canonicalize_lift (resolved_st_q_is_bot_for gl)
                        (locals (snd sol (Inl (v, ctx)))))))"
  unfolding analyse_int_ctx_result_for_def Let_def by (rule refl)

section \<open>Int at the routed spine, instantiated at the call-string context\<close>

text \<open>
  The call-string instance of the Int analysis package in
  \<^theory>\<open>Voblint_Analysis.Int_Sound\<close>, alongside its
  routed-unit-context instance, mirroring \<open>Sign_Analyses\<close>'s own
  derivation for a second domain: same \<^const>\<open>int_dom_spec\<close>/\<^const>\<open>int_dom_abs_spec\<close>
  D/G specification and the same domain-commute facts Int's own routed-unit
  instance already interprets (\<^locale>\<open>routed_dg_domain_exec\<close>,
  \<^theory>\<open>Voblint_Exec.DG_Local_State_Exec\<close>) -- nothing here re-derives them, and the
  \<^typ>\<open>refine_mode\<close> parameter Int threads throughout stays a genuine fixed
  argument exactly as it already is at Int's own \<^const>\<open>int_dom_spec\<close>. Only the
  routing policy changes, from \<^const>\<open>route_unit\<close> to
  \<^const>\<open>Call_String_Context.cs_route\<close> at a runtime bound \<open>k\<close>, and the routed-context
  locale interpreted changes from \<^locale>\<open>unit_routed_context\<close> to
  \<^locale>\<open>call_string_routed_context\<close> (\<^theory>\<open>Voblint_Analysis.Call_String_Routed_Context\<close>),
  exactly as Sign's own call-string derivation already uses.

  This is the mission's stretch-goal acceptance test at a third domain: a second
  context for Int, exposed from the existing generic routed-domain interpretation
  and the existing generic call-string context locale, with no new Int-domain
  mathematics.
\<close>

subsection \<open>The routed equation system and its executable solution\<close>

definition ics_eqs ::
    "nat \<Rightarrow> refine_mode \<Rightarrow> (vname \<Rightarrow> bool) \<Rightarrow> (int_dom exec_dg_st \<Rightarrow> bool) \<Rightarrow> proc_table \<Rightarrow> pname list
       \<Rightarrow> (pp \<times> call_string, call_string_gk, (int_dom exec_dg_st lifted, int_dom exec_dg_st lifted) dg_state) eqsT" where
  "ics_eqs k mode gs empty_pred Pi ps =
     side_cfg_T_eff_keyed_seed_dg_buffered intra_predecessor_addr_list (\<lambda>_. Call_String_Context.Global)
       (cs_route k)
       (\<lambda>ctx' src a. dg_spec_edge_tree (int_dom_spec mode empty_pred gs) a src
          (\<lambda>_. Call_String_Context.Global))
       (routed_cmb_g (int_dom_spec mode empty_pred gs)
          Call_String_Context.Global Call_String_Context.Seed
          (static_resolve (compile_prog Pi ps)))
       (routed_extra_g Call_String_Context.Seed Call_String_Context.Global)
       (compile_prog Pi ps) Bot (Lifted cinit_int_dom_st) Bot"

definition ics_sol ::
    "nat \<Rightarrow> refine_mode \<Rightarrow> (vname \<Rightarrow> bool) \<Rightarrow> (int_dom exec_dg_st \<Rightarrow> bool) \<Rightarrow> proc_table \<Rightarrow> pname list
       \<Rightarrow> (pp \<times> call_string) set \<times> (pp \<times> call_string + call_string_gk \<Rightarrow> (int_dom exec_dg_st lifted, int_dom exec_dg_st lifted) dg_state)" where
  "ics_sol k mode gs empty_pred Pi ps =
     TD_side_always_join_Interp_solve (ics_eqs k mode gs empty_pred Pi ps)
       (cfg_exit (compile_prog Pi ps), [])"

definition ics_terminates ::
    "nat \<Rightarrow> refine_mode \<Rightarrow> (vname \<Rightarrow> bool) \<Rightarrow> (int_dom exec_dg_st \<Rightarrow> bool) \<Rightarrow> proc_table \<Rightarrow> pname list
       \<Rightarrow> bool" where
  "ics_terminates k mode gs empty_pred Pi ps =
     TD_side_always_join_Interp.solve_dom TYPE(call_string_gk) TYPE((int_dom exec_dg_st lifted, int_dom exec_dg_st lifted) dg_state)
       (ics_eqs k mode gs empty_pred Pi ps) (cfg_exit (compile_prog Pi ps), [])"

lemma ics_terminates_via_solve_c:
  assumes "TD_side_always_join_Interp_solve_c (ics_eqs k mode gs empty_pred Pi ps)
             (cfg_exit (compile_prog Pi ps), []) \<noteq> None"
  shows "ics_terminates k mode gs empty_pred Pi ps"
  unfolding ics_terminates_def
  by (rule TD_side_always_join_Interp.solve_dom_of_solve_c[OF assms])

text \<open>
  The same routed system under Apinis warrowing, Int's production default at
  \<open>Ctx_None\<close>. Always-join has no termination guarantee on the interval component:
  a call string that collapses a recursion's contexts feeds the callee entry its
  own decremented formals, and a join-only solve descends that chain forever.
  \<^locale>\<open>TD_side_upd_rule\<close>'s \<open>solve_dom\<close>/\<open>partial_post_solution\<close> are generic over
  the update rule, so the certificate below is the join one with the solver
  swapped, exactly as the context-insensitive instance does.
\<close>

definition ics_sol_warrow ::
    "nat \<Rightarrow> refine_mode \<Rightarrow> (vname \<Rightarrow> bool) \<Rightarrow> (int_dom exec_dg_st \<Rightarrow> bool) \<Rightarrow> proc_table \<Rightarrow> pname list
       \<Rightarrow> (pp \<times> call_string) set \<times> (pp \<times> call_string + call_string_gk \<Rightarrow> (int_dom exec_dg_st lifted, int_dom exec_dg_st lifted) dg_state)" where
  "ics_sol_warrow k mode gs empty_pred Pi ps =
     TD_side_warrowing_apinis_Interp_solve (ics_eqs k mode gs empty_pred Pi ps)
       (cfg_exit (compile_prog Pi ps), [])"

definition ics_terminates_warrow ::
    "nat \<Rightarrow> refine_mode \<Rightarrow> (vname \<Rightarrow> bool) \<Rightarrow> (int_dom exec_dg_st \<Rightarrow> bool) \<Rightarrow> proc_table \<Rightarrow> pname list
       \<Rightarrow> bool" where
  "ics_terminates_warrow k mode gs empty_pred Pi ps =
     TD_side_warrowing_apinis_Interp.solve_dom TYPE(call_string_gk) TYPE((int_dom exec_dg_st lifted, int_dom exec_dg_st lifted) dg_state)
       (ics_eqs k mode gs empty_pred Pi ps) (cfg_exit (compile_prog Pi ps), [])"

lemma ics_terminates_warrow_via_solve_c:
  assumes "TD_side_warrowing_apinis_Interp_solve_c (ics_eqs k mode gs empty_pred Pi ps)
             (cfg_exit (compile_prog Pi ps), []) \<noteq> None"
  shows "ics_terminates_warrow k mode gs empty_pred Pi ps"
  unfolding ics_terminates_warrow_def
  by (rule TD_side_warrowing_apinis_Interp.solve_dom_of_solve_c[OF assms])

subsection \<open>Domain commute facts, at the call-string routed spec\<close>

text \<open>
  \<^const>\<open>Call_String_Context.cs_route\<close> is polymorphic in its \<open>'d\<close> argument and ignores
  it outright, exactly as \<^const>\<open>route_unit\<close> does, so the routing-agreement obligation
  \<^locale>\<open>routed_domain_exec\<close> takes as a parameter is true unconditionally here.
  Everything else in the interpretation is Int's own mode-generic commute facts,
  cited unchanged: switching context policy is a different instantiation of one
  derivation, not a second one.
\<close>

context
  fixes mode :: refine_mode and gs :: "vname \<Rightarrow> bool"
    and empty_pred :: "int_dom exec_dg_st \<Rightarrow> bool" and k :: nat
  assumes exact: "\<And>s. empty_pred s = is_empty_state (fun_of_resolved_st_q_for gs s)"
begin

interpretation int_cs: routed_domain_exec
  gs empty_pred "int_tf_st_for mode gs" "int_dom_enter_st_for mode gs" "int_tf_for mode gs"
  Call_String_Context.Global Call_String_Context.Seed "cs_route k" "cs_route k"
  static_resolve static_resolve
  by unfold_locales
     (rule int_tf_st_for_commute, rule int_dom_enter_st_for_commute, rule exact, simp,
      rule cs_route_indep_of_data, simp add: static_resolve_def)

lemmas int_cs_pp_st_gen = int_cs.pp_st

end

subsection \<open>The certified executable post-solution, generic per compiled program\<close>

context
  fixes mode :: refine_mode and gs :: "vname \<Rightarrow> bool" and empty_pred :: "int_dom exec_dg_st \<Rightarrow> bool"
    and Pi :: proc_table and ps :: "pname list" and k :: nat
  assumes solves: "ics_terminates k mode gs empty_pred Pi ps"
    and exact: "\<And>s. empty_pred s = is_empty_state (fun_of_resolved_st_q_for gs s)"
begin

lemma ics_solve_dom:
  "TD_side_always_join_Interp.solve_dom TYPE(call_string_gk) TYPE((int_dom exec_dg_st lifted, int_dom exec_dg_st lifted) dg_state)
     (ics_eqs k mode gs empty_pred Pi ps) (cfg_exit (compile_prog Pi ps), [])"
  using solves[unfolded ics_terminates_def] .

lemma ics_pp_st:
  "part_post_solution (ics_eqs k mode gs empty_pred Pi ps) (cfg_exit (compile_prog Pi ps), [])
     (snd (ics_sol k mode gs empty_pred Pi ps)) (fst (ics_sol k mode gs empty_pred Pi ps))"
  using TD_side_always_join_Interp.partial_post_solution
          [OF ics_solve_dom, of "fst (ics_sol k mode gs empty_pred Pi ps)"
             "snd (ics_sol k mode gs empty_pred Pi ps)"]
  unfolding ics_sol_def by simp

text \<open>The solver's post-solution, for the unbuffered routed generator at the executable
  spec: the shape \<^locale>\<open>call_string_routed_context\<close> consumes directly.\<close>

theorem ics_pp_routed:
  "part_post_solution
     (side_cfg_T_eff_keyed_seed_dg intra_predecessor_addr_list (\<lambda>_. Call_String_Context.Global)
        (cs_route k)
        (\<lambda>ctx' src a. dg_spec_edge_tree (int_dom_spec mode empty_pred gs) a src
           (\<lambda>_. Call_String_Context.Global))
        (routed_cmb_g (int_dom_spec mode empty_pred gs) Call_String_Context.Global
           Call_String_Context.Seed (static_resolve (compile_prog Pi ps)))
        (routed_extra_g Call_String_Context.Seed Call_String_Context.Global)
        (compile_prog Pi ps) Bot (Lifted cinit_int_dom_st) Bot)
     (cfg_exit (compile_prog Pi ps), [])
     (snd (ics_sol k mode gs empty_pred Pi ps)) (fst (ics_sol k mode gs empty_pred Pi ps))"
  using ics_pp_st unfolding ics_eqs_def int_dom_spec_def by (rule int_cs_pp_st_gen[OF exact])
end

subsection \<open>Whole-program convenience layer\<close>

text \<open>
  Fixed at \<^const>\<open>Refine_Fixpoint\<close>, matching Int's own production default
  (\<open>Int_Entry\<close>'s own \<open>analyse_int_report\<close>): \<open>mode\<close> stays a
  genuine parameter through every lemma above, exactly as Int's own routed-unit
  file threads it, and is only pinned here where the public, config-driven
  surface needs one concrete choice.
\<close>

definition ics_eqs_prog ::
    "nat \<Rightarrow> (vname \<Rightarrow> bool) \<Rightarrow> imp_prog
       \<Rightarrow> (pp \<times> call_string, call_string_gk, (int_dom exec_dg_st lifted, int_dom exec_dg_st lifted) dg_state) eqsT" where
  "ics_eqs_prog k gs p =
     ics_eqs k Refine_Fixpoint gs (resolved_st_q_is_bot_for (declared_global_vars p))
       (prog_table p) (prog_procs p)"

definition ics_sol_prog ::
    "nat \<Rightarrow> (vname \<Rightarrow> bool) \<Rightarrow> imp_prog
       \<Rightarrow> (pp \<times> call_string) set \<times> (pp \<times> call_string + call_string_gk \<Rightarrow> (int_dom exec_dg_st lifted, int_dom exec_dg_st lifted) dg_state)" where
  "ics_sol_prog k gs p =
     ics_sol k Refine_Fixpoint gs (resolved_st_q_is_bot_for (declared_global_vars p))
       (prog_table p) (prog_procs p)"

definition ics_terminates_prog :: "nat \<Rightarrow> (vname \<Rightarrow> bool) \<Rightarrow> imp_prog \<Rightarrow> bool" where
  "ics_terminates_prog k gs p =
     ics_terminates k Refine_Fixpoint gs (resolved_st_q_is_bot_for (declared_global_vars p))
       (prog_table p) (prog_procs p)"

lemma ics_terminates_prog_via_solve_c:
  assumes "TD_side_always_join_Interp_solve_c
             (ics_eqs_prog k gs p)
             (cfg_exit (compile_prog (prog_table p) (prog_procs p)), []) \<noteq> None"
  shows "ics_terminates_prog k gs p"
  using assms
  unfolding ics_terminates_prog_def ics_eqs_prog_def
  by (rule ics_terminates_via_solve_c)

definition ics_sol_prog_warrow ::
    "nat \<Rightarrow> (vname \<Rightarrow> bool) \<Rightarrow> imp_prog
       \<Rightarrow> (pp \<times> call_string) set \<times> (pp \<times> call_string + call_string_gk \<Rightarrow> (int_dom exec_dg_st lifted, int_dom exec_dg_st lifted) dg_state)" where
  "ics_sol_prog_warrow k gs p =
     ics_sol_warrow k Refine_Fixpoint gs (resolved_st_q_is_bot_for (declared_global_vars p))
       (prog_table p) (prog_procs p)"

definition ics_terminates_prog_warrow :: "nat \<Rightarrow> (vname \<Rightarrow> bool) \<Rightarrow> imp_prog \<Rightarrow> bool" where
  "ics_terminates_prog_warrow k gs p =
     ics_terminates_warrow k Refine_Fixpoint gs (resolved_st_q_is_bot_for (declared_global_vars p))
       (prog_table p) (prog_procs p)"

lemma ics_terminates_prog_warrow_via_solve_c:
  assumes "TD_side_warrowing_apinis_Interp_solve_c
             (ics_eqs_prog k gs p)
             (cfg_exit (compile_prog (prog_table p) (prog_procs p)), []) \<noteq> None"
  shows "ics_terminates_prog_warrow k gs p"
  using assms
  unfolding ics_terminates_prog_warrow_def ics_eqs_prog_def
  by (rule ics_terminates_warrow_via_solve_c)

section \<open>Solved-result table\<close>

text \<open>
  The solved call-string D/G system, read as a \<^typ>\<open>(call_string, int_dom abs_state)
  analysis_result\<close> -- the exact construction Sign's and Interval's own call-string
  result tables already use, at Int's own solve. The covered-key set is the
  solver's own, never an enumerated theoretical context space.
\<close>

definition analyse_int_call_string_result_for ::
    "nat \<Rightarrow> (vname \<Rightarrow> bool) \<Rightarrow> imp_prog \<Rightarrow> (call_string, int_dom abs_state) analysis_result" where
  "analyse_int_call_string_result_for k gs p =
     Analysis_Result
       (fst (ics_sol_prog k gs p))
       (\<lambda>v ctx. normalize_point gs
                  (canonicalize_lift (resolved_st_q_is_bot_for (declared_global_vars p))
                    (locals (snd (ics_sol_prog k gs p) (Inl (v, ctx))))))"

declare analyse_int_call_string_result_for_def [code del]

lemma analyse_int_call_string_result_for_code [code]:
  "analyse_int_call_string_result_for k gs p =
     (let sol = ics_sol_prog k gs p; gl = declared_global_vars p
      in Analysis_Result (fst sol)
           (\<lambda>v ctx. normalize_point gs
                      (canonicalize_lift (resolved_st_q_is_bot_for gl)
                        (locals (snd sol (Inl (v, ctx)))))))"
  unfolding analyse_int_call_string_result_for_def Let_def by (rule refl)

text \<open>Convenience instance at \<^const>\<open>declared_global\<close> \<open>p\<close> and \<^const>\<open>prog_main_name\<close>,
  matching Sign's own \<open>analyse_sign_call_string_result\<close>'s shape, with \<open>k\<close> as an
  explicit leading runtime argument.\<close>

definition analyse_int_call_string_result ::
    "nat \<Rightarrow> imp_prog \<Rightarrow> (call_string, int_dom abs_state) analysis_result" where
  "analyse_int_call_string_result k p =
     analyse_int_call_string_result_for k (declared_global p) p"

section \<open>Contextual check report\<close>

text \<open>
  Reuses \<^const>\<open>classify_checks_ctx\<close>/\<^const>\<open>classify_checks_verdicts\<close> unchanged --
  both are generic in the context type already, so nothing call-string-specific
  is needed here beyond supplying the call-string result table and Int's own
  \<^const>\<open>int_classify_check\<close>, exactly mirroring Sign's own
  \<open>scs_check_projection\<close>/\<open>scs_verdict_report_prog\<close>.
\<close>

definition ics_check_projection ::
    "nat \<Rightarrow> imp_prog \<Rightarrow> (pp \<times> exp \<times> (call_string \<times> contextual_verdict) set) list" where
  "ics_check_projection k p =
     classify_checks_ctx (prog_cfg p)
       (analyse_int_call_string_result_for k (declared_global p) p)
       int_classify_check"

definition ics_verdict_report_prog ::
    "nat \<Rightarrow> imp_prog \<Rightarrow> (pp \<times> exp \<times> contextual_verdict) list" where
  "ics_verdict_report_prog k p =
     map (\<lambda>(u, c, vs). (u, c, aggregate_verdicts (snd ` vs)))
       (ics_check_projection k p)"

lemma ics_verdict_report_prog_eq:
  "ics_verdict_report_prog k p =
     classify_checks_verdicts (prog_cfg p)
       (analyse_int_call_string_result_for k (declared_global p) p)
       int_classify_check"
  unfolding ics_verdict_report_prog_def ics_check_projection_def
  by (rule classify_checks_verdicts_proj)

definition analyse_int_call_string_report ::
    "nat \<Rightarrow> imp_prog \<Rightarrow> (pp \<times> exp \<times> contextual_verdict) list" where
  "analyse_int_call_string_report k p = ics_verdict_report_prog k p"

section \<open>Int at the routed spine, instantiated at the entry-state context\<close>

text \<open>
  The entry-state sibling of Int's own routed-unit-context instance
  (\<^theory>\<open>Voblint_Analysis.Int_Sound\<close>), and the fourth architecture-milestone
  acceptance test, after Sign's own call-string and entry-state derivations and Int's
  own call-string derivation: same \<^const>\<open>int_dom_spec\<close>/\<^const>\<open>int_dom_abs_spec\<close> D/G
  specification and the same domain-commute facts Int already interprets
  (\<^locale>\<open>routed_dg_domain_exec\<close>, \<^theory>\<open>Voblint_Exec.DG_Local_State_Exec\<close>) -- nothing here
  re-derives them, and the \<^typ>\<open>refine_mode\<close> parameter Int threads throughout stays a
  genuine fixed argument exactly as it already is at Int's own \<^const>\<open>int_dom_spec\<close>. The
  routing policy is the same generic entry-state construction
  (\<open>entry_exec_route_gen\<close>/\<^const>\<open>formals_route_lifted_gen\<close>,
  \<^theory>\<open>Voblint_Exec.DG_Local_State_Exec\<close>/\<^theory>\<open>Voblint_Framework.Routed_Context\<close>) Sign's own
  entry-state instance already uses: it needed only \<^locale>\<open>routed_dg_domain_exec\<close>'s
  own three primitive commute facts, which Int's own routed-unit instance has already
  established, so no new Int-domain mathematics is needed here either.
  \<^locale>\<open>entry_state_routed_context\<close> (\<^theory>\<open>Voblint_Analysis.Entry_State_Routed_Context\<close>) is
  the generic context-side counterpart, discharging \<open>FinC\<close>/\<open>RouteAgree\<close>/\<open>EnterAgree\<close>
  once and for all instances.

  This development goes one section further than Int's own call-string instance, to
  activation-indexed collecting soundness -- matching Sign's own entry-state pipeline's
  scope, which in turn matches Interval's own entry-state pipeline's scope.
\<close>


subsection \<open>The routed equation system's own route, generic per compiled program\<close>

text \<open>
  Int's own executable-carrier route, mirroring Sign's own
  \<open>sctx_entry_route\<close>/\<open>sctx_entry_route_gen\<close> exactly, at Int's own
  \<open>int_dom_enter_st_for mode gs\<close> instead of Sign's \<open>sign_enter_st_for gs\<close> -- this is
  precisely \<^locale>\<open>routed_dg_domain_exec\<close>'s own \<open>entry_exec_route\<close>/
  \<open>entry_exec_route_gen\<close> (\<^theory>\<open>Voblint_Exec.DG_Local_State_Exec\<close>), restated here as
  unconditional top-level definitions so the equation-system definitions below need no
  \<open>exact\<close> premise to be stated, matching every other routed instance's convention. The
  routed generator enters the callee frame before it routes, so the route itself only
  projects the formals out of the state it is handed.
\<close>

definition ictx_entry_route ::
    "refine_mode \<Rightarrow> (vname \<Rightarrow> bool) \<Rightarrow> (int_dom exec_dg_st \<Rightarrow> bool)
       \<Rightarrow> int_dom exec_dg_st lifted \<Rightarrow> call_action \<Rightarrow> int_dom list" where
  "ictx_entry_route mode gs empty_pred d ca =
     (case ca of CallEdge dst pars args \<Rightarrow>
        formals_context pars (fun_of_resolved_st_q_for gs
          (case d of Bot \<Rightarrow> bot | Lifted d0 \<Rightarrow> d0)))"

definition ictx_entry_route_gen ::
    "refine_mode \<Rightarrow> (vname \<Rightarrow> bool) \<Rightarrow> (int_dom exec_dg_st \<Rightarrow> bool)
       \<Rightarrow> pp \<Rightarrow> int_dom list \<Rightarrow> int_dom exec_dg_st lifted \<Rightarrow> call_action \<Rightarrow> int_dom list" where
  "ictx_entry_route_gen mode gs empty_pred u ctx d ca = ictx_entry_route mode gs empty_pred d ca"

subsection \<open>The routed equation system and its executable solution\<close>

definition ictx_entry_eqs ::
    "refine_mode \<Rightarrow> (vname \<Rightarrow> bool) \<Rightarrow> (int_dom exec_dg_st \<Rightarrow> bool) \<Rightarrow> proc_table \<Rightarrow> pname list
       \<Rightarrow> (pp \<times> int_dom list, (unit, int_dom list) routed_gk, (int_dom exec_dg_st lifted, int_dom exec_dg_st lifted) dg_state) eqsT" where
  "ictx_entry_eqs mode gs empty_pred Pi ps =
     side_cfg_T_eff_keyed_seed_dg_buffered intra_predecessor_addr_list (\<lambda>_. Analysis_Global ())
       (ictx_entry_route_gen mode gs empty_pred)
       (\<lambda>ctx' src a. dg_spec_edge_tree (int_dom_spec mode empty_pred gs) a src (\<lambda>_. Analysis_Global ()))
       (routed_cmb_g (int_dom_spec mode empty_pred gs) (Analysis_Global ()) Activation_Seed
          (static_resolve (compile_prog Pi ps)))
       (routed_extra_g Activation_Seed (Analysis_Global ()))
       (compile_prog Pi ps) Bot (Lifted cinit_int_dom_st) Bot"

definition ictx_entry_sol ::
    "refine_mode \<Rightarrow> (vname \<Rightarrow> bool) \<Rightarrow> (int_dom exec_dg_st \<Rightarrow> bool) \<Rightarrow> proc_table \<Rightarrow> pname list
       \<Rightarrow> (pp \<times> int_dom list) set \<times> (pp \<times> int_dom list + (unit, int_dom list) routed_gk \<Rightarrow> (int_dom exec_dg_st lifted, int_dom exec_dg_st lifted) dg_state)" where
  "ictx_entry_sol mode gs empty_pred Pi ps =
     TD_side_always_join_Interp_solve (ictx_entry_eqs mode gs empty_pred Pi ps)
       (cfg_exit (compile_prog Pi ps), [])"

definition ictx_entry_terminates ::
    "refine_mode \<Rightarrow> (vname \<Rightarrow> bool) \<Rightarrow> (int_dom exec_dg_st \<Rightarrow> bool) \<Rightarrow> proc_table \<Rightarrow> pname list
       \<Rightarrow> bool" where
  "ictx_entry_terminates mode gs empty_pred Pi ps =
     TD_side_always_join_Interp.solve_dom TYPE((unit, int_dom list) routed_gk) TYPE((int_dom exec_dg_st lifted, int_dom exec_dg_st lifted) dg_state)
       (ictx_entry_eqs mode gs empty_pred Pi ps) (cfg_exit (compile_prog Pi ps), [])"

lemma ictx_entry_terminates_via_solve_c:
  assumes "TD_side_always_join_Interp_solve_c (ictx_entry_eqs mode gs empty_pred Pi ps)
             (cfg_exit (compile_prog Pi ps), []) \<noteq> None"
  shows "ictx_entry_terminates mode gs empty_pred Pi ps"
  unfolding ictx_entry_terminates_def
  by (rule TD_side_always_join_Interp.solve_dom_of_solve_c[OF assms])

text \<open>
  The same routed system under Apinis warrowing, Int's production default at
  \<open>Ctx_None\<close>. Always-join has no termination guarantee on the interval component,
  so it is offered only as an explicit selection; the certificate is the join one
  with the solver swapped, as the context-insensitive instance does.
\<close>

definition ictx_entry_sol_warrow ::
    "refine_mode \<Rightarrow> (vname \<Rightarrow> bool) \<Rightarrow> (int_dom exec_dg_st \<Rightarrow> bool) \<Rightarrow> proc_table \<Rightarrow> pname list
       \<Rightarrow> (pp \<times> int_dom list) set \<times> (pp \<times> int_dom list + (unit, int_dom list) routed_gk \<Rightarrow> (int_dom exec_dg_st lifted, int_dom exec_dg_st lifted) dg_state)" where
  "ictx_entry_sol_warrow mode gs empty_pred Pi ps =
     TD_side_warrowing_apinis_Interp_solve (ictx_entry_eqs mode gs empty_pred Pi ps)
       (cfg_exit (compile_prog Pi ps), [])"

definition ictx_entry_terminates_warrow ::
    "refine_mode \<Rightarrow> (vname \<Rightarrow> bool) \<Rightarrow> (int_dom exec_dg_st \<Rightarrow> bool) \<Rightarrow> proc_table \<Rightarrow> pname list
       \<Rightarrow> bool" where
  "ictx_entry_terminates_warrow mode gs empty_pred Pi ps =
     TD_side_warrowing_apinis_Interp.solve_dom TYPE((unit, int_dom list) routed_gk) TYPE((int_dom exec_dg_st lifted, int_dom exec_dg_st lifted) dg_state)
       (ictx_entry_eqs mode gs empty_pred Pi ps) (cfg_exit (compile_prog Pi ps), [])"

lemma ictx_entry_terminates_warrow_via_solve_c:
  assumes "TD_side_warrowing_apinis_Interp_solve_c (ictx_entry_eqs mode gs empty_pred Pi ps)
             (cfg_exit (compile_prog Pi ps), []) \<noteq> None"
  shows "ictx_entry_terminates_warrow mode gs empty_pred Pi ps"
  unfolding ictx_entry_terminates_warrow_def
  by (rule TD_side_warrowing_apinis_Interp.solve_dom_of_solve_c[OF assms])

subsection \<open>Route agreement: the one genuinely domain-specific commute fact\<close>

context
  fixes mode :: refine_mode and gs :: "vname \<Rightarrow> bool" and empty_pred :: "int_dom exec_dg_st \<Rightarrow> bool"
  assumes exact: "\<And>s. empty_pred s = is_empty_state (fun_of_resolved_st_q_for gs s)"
begin

interpretation int_domain: routed_dg_domain_exec
  gs empty_pred "int_tf_st_for mode gs" "int_dom_enter_st_for mode gs" "int_tf_for mode gs"
  by unfold_locales (rule int_tf_st_for_commute, rule int_dom_enter_st_for_commute, rule exact)

lemma ictx_entry_route_gen_eq_generic:
  "ictx_entry_route_gen mode gs empty_pred u ctx d ca = int_domain.entry_exec_route_gen u ctx d ca"
  unfolding ictx_entry_route_gen_def int_domain.entry_exec_route_gen_def
    ictx_entry_route_def int_domain.entry_exec_route_def
  by (rule refl)

lemma ictx_entry_route_gen_commute:
  "formals_route_lifted_gen u ctx (map_lift (fun_of_resolved_st_q_for gs) d) ca
     = ictx_entry_route_gen mode gs empty_pred u ctx d ca"
  unfolding ictx_entry_route_gen_eq_generic
  by (rule int_domain.entry_exec_route_gen_commute)

end

subsection \<open>Per-tree transport commutation\<close>

text \<open>
  The same interpretation Int's unit-context and call-string instances make, at the
  entry-state routing policy. Here the routing-agreement obligation
  \<^locale>\<open>routed_domain_exec\<close> takes as a parameter is not free --- the route reads the
  entered state --- but it is exactly the fact just proved.
\<close>

context
  fixes mode :: refine_mode and gs :: "vname \<Rightarrow> bool"
    and empty_pred :: "int_dom exec_dg_st \<Rightarrow> bool"
  assumes exact: "\<And>s. empty_pred s = is_empty_state (fun_of_resolved_st_q_for gs s)"
begin

interpretation int_es: routed_domain_exec
  gs empty_pred "int_tf_st_for mode gs" "int_dom_enter_st_for mode gs" "int_tf_for mode gs"
  "Analysis_Global ()" Activation_Seed "ictx_entry_route_gen mode gs empty_pred"
  formals_route_lifted_gen
  static_resolve static_resolve
  by unfold_locales
     (rule int_tf_st_for_commute, rule int_dom_enter_st_for_commute, rule exact, simp,
      rule ictx_entry_route_gen_commute[OF exact, symmetric],
      simp add: static_resolve_def)

lemmas int_es_pp_st_gen = int_es.pp_st

end

subsection \<open>The certified executable post-solution, generic per compiled program\<close>

context
  fixes mode :: refine_mode and gs :: "vname \<Rightarrow> bool" and empty_pred :: "int_dom exec_dg_st \<Rightarrow> bool"
    and Pi :: proc_table and ps :: "pname list"
  assumes solves: "ictx_entry_terminates mode gs empty_pred Pi ps"
    and exact: "\<And>s. empty_pred s = is_empty_state (fun_of_resolved_st_q_for gs s)"
begin

lemma ictx_entry_solve_dom:
  "TD_side_always_join_Interp.solve_dom TYPE((unit, int_dom list) routed_gk) TYPE((int_dom exec_dg_st lifted, int_dom exec_dg_st lifted) dg_state)
     (ictx_entry_eqs mode gs empty_pred Pi ps) (cfg_exit (compile_prog Pi ps), [])"
  using solves[unfolded ictx_entry_terminates_def] .

lemma ictx_entry_pp_st:
  "part_post_solution (ictx_entry_eqs mode gs empty_pred Pi ps) (cfg_exit (compile_prog Pi ps), [])
     (snd (ictx_entry_sol mode gs empty_pred Pi ps)) (fst (ictx_entry_sol mode gs empty_pred Pi ps))"
  using TD_side_always_join_Interp.partial_post_solution
          [OF ictx_entry_solve_dom, of "fst (ictx_entry_sol mode gs empty_pred Pi ps)"
             "snd (ictx_entry_sol mode gs empty_pred Pi ps)"]
  unfolding ictx_entry_sol_def by simp

text \<open>The solver's post-solution, for the unbuffered routed generator at the executable
  spec and Int's executable route: the shape \<^locale>\<open>dg_ctx_activation_base\<close> consumes.\<close>

theorem ictx_entry_pp_routed:
  "part_post_solution
     (side_cfg_T_eff_keyed_seed_dg intra_predecessor_addr_list (\<lambda>_. Analysis_Global ())
        (ictx_entry_route_gen mode gs empty_pred)
        (\<lambda>ctx' src a. dg_spec_edge_tree (int_dom_spec mode empty_pred gs) a src (\<lambda>_. Analysis_Global ()))
        (routed_cmb_g (int_dom_spec mode empty_pred gs) (Analysis_Global ()) Activation_Seed
           (static_resolve (compile_prog Pi ps)))
        (routed_extra_g Activation_Seed (Analysis_Global ()))
        (compile_prog Pi ps) Bot (Lifted cinit_int_dom_st) Bot)
     (cfg_exit (compile_prog Pi ps), [])
     (snd (ictx_entry_sol mode gs empty_pred Pi ps)) (fst (ictx_entry_sol mode gs empty_pred Pi ps))"
  using ictx_entry_pp_st unfolding ictx_entry_eqs_def int_dom_spec_def
  by (rule int_es_pp_st_gen[OF exact])

end

section \<open>Activation-indexed collecting soundness, generic per compiled program\<close>

text \<open>
  The routed spine is interpreted at Int's executable carrier and fed the solver's own
  table, as the context-insensitive instance does: a local unknown concretizes
  to \<^const>\<open>gamma_state_lift\<close> of its readback (\<^const>\<open>int_dom_gamma\<close>), the covered reader
  \<open>ictx_entry_sg_st\<close> hands the table's local slot through unchanged, and the route is
  Int's own executable \<^const>\<open>ictx_entry_route_gen\<close>.
\<close>

definition ictx_entry_sg_st ::
    "refine_mode \<Rightarrow> (vname \<Rightarrow> bool) \<Rightarrow> (int_dom exec_dg_st \<Rightarrow> bool) \<Rightarrow> proc_table \<Rightarrow> pname list
       \<Rightarrow> pp \<times> int_dom list + (unit, int_dom list) routed_gk \<Rightarrow> int_dom exec_dg_st lifted" where
  "ictx_entry_sg_st mode gs empty_pred Pi ps k =
     (case k of
        Inl (v, ctx) \<Rightarrow>
          (if (v, ctx) \<in> fst (ictx_entry_sol mode gs empty_pred Pi ps)
           then locals (snd (ictx_entry_sol mode gs empty_pred Pi ps) (Inl (v, ctx)))
           else Bot)
      | Inr _ \<Rightarrow> Bot)"

context
  fixes mode :: refine_mode and gs :: "vname \<Rightarrow> bool" and empty_pred :: "int_dom exec_dg_st \<Rightarrow> bool"
    and Pi :: proc_table and ps :: "pname list"
  assumes solves: "ictx_entry_terminates mode gs empty_pred Pi ps"
    and exact: "\<And>s. empty_pred s = is_empty_state (fun_of_resolved_st_q_for gs s)"
    and entry_cov: "(cfg_entry (compile_prog Pi ps), []) \<in> fst (ictx_entry_sol mode gs empty_pred Pi ps)"
    and fwd_ok: "\<And>u a v ctx. (u, ctx) \<in> fst (ictx_entry_sol mode gs empty_pred Pi ps)
                    \<Longrightarrow> (u, a, v) \<in> intra (compile_prog Pi ps)
                    \<Longrightarrow> (v, ctx) \<in> fst (ictx_entry_sol mode gs empty_pred Pi ps)"
    and call_fwd_ok: "\<And>u ctx dst pars args p cont.
        (u, ctx) \<in> fst (ictx_entry_sol mode gs empty_pred Pi ps)
        \<Longrightarrow> (u, CallEdge dst pars args, FunctionEntry p, cont) \<in> calls (compile_prog Pi ps)
        \<Longrightarrow> (FunctionEntry p,
               ictx_entry_route_gen mode gs empty_pred u ctx
                 (entered (int_dom_spec mode empty_pred gs) (Analysis_Global ())
                    (snd (ictx_entry_sol mode gs empty_pred Pi ps))
                    (call_info_of (CallEdge dst pars args) p) (Inl (u, ctx)))
                 (CallEdge dst pars args))
             \<in> fst (ictx_entry_sol mode gs empty_pred Pi ps)"
    and comb_fwd_ok: "\<And>cl c1 dst pars args p cont.
        (cl, c1) \<in> fst (ictx_entry_sol mode gs empty_pred Pi ps)
        \<Longrightarrow> (cl, CallEdge dst pars args, FunctionEntry p, cont) \<in> calls (compile_prog Pi ps)
        \<Longrightarrow> (cont, c1) \<in> fst (ictx_entry_sol mode gs empty_pred Pi ps)"
begin

subsection \<open>The solver's table as the solved system\<close>

interpretation ictx_entry_compiled: compiled_cfg Pi ps "compile_prog Pi ps"
  by (unfold_locales; simp add: compile_prog_finite)

lemmas ictx_entry_fin = ictx_entry_compiled.finite_intra
lemmas ictx_entry_finC = ictx_entry_compiled.finite_calls

lemma ictx_entry_sg_st_covered:
  "(v, ctx) \<in> fst (ictx_entry_sol mode gs empty_pred Pi ps)
   \<Longrightarrow> ictx_entry_sg_st mode gs empty_pred Pi ps (Inl (v, ctx))
         = locals (snd (ictx_entry_sol mode gs empty_pred Pi ps) (Inl (v, ctx)))"
  by (simp add: ictx_entry_sg_st_def)

lemma ictx_entry_sg_st_uncovered_empty:
  "(v, ctx) \<notin> fst (ictx_entry_sol mode gs empty_pred Pi ps)
     \<Longrightarrow> gamma_state_lift (map_lift (fun_of_resolved_st_q_for gs)
           (ictx_entry_sg_st mode gs empty_pred Pi ps (Inl (v, ctx)))) = {}"
  by (simp add: ictx_entry_sg_st_def)

subsection \<open>Instantiating the generic routed-context locale\<close>

interpretation ictx_entry_dg_base: sound_dg_spec "int_dom_spec mode empty_pred gs" "int_dom_gamma gs" gs
  by (rule int_dom_sound_exec[OF exact])

interpretation ictx_entry_routed: entry_state_routed_context "int_dom_spec mode empty_pred gs"
    "int_dom_gamma gs" gs Pi ps "Analysis_Global ()" "ictx_entry_route_gen mode gs empty_pred"
    Bot "Lifted cinit_int_dom_st" Bot
    "snd (ictx_entry_sol mode gs empty_pred Pi ps)" "fst (ictx_entry_sol mode gs empty_pred Pi ps)"
    "(cfg_exit (compile_prog Pi ps), [])" "ictx_entry_sg_st mode gs empty_pred Pi ps" Activation_Seed
    "\<lambda>m. gamma_state_lift (map_lift (fun_of_resolved_st_q_for gs) m)"
proof (unfold_locales, goal_cases FinE PP SgCov SgUncov Fwd SeedNe CallFwd CombFwd)
  case FinE show ?case by (rule ictx_entry_fin)
next
  case PP show ?case by (rule ictx_entry_pp_routed[OF solves exact])
next
  case (SgCov v ctx) then show ?case
    by (simp add: ictx_entry_sg_st_def int_dom_gamma_def)
next
  case (SgUncov v ctx) then show ?case by (rule ictx_entry_sg_st_uncovered_empty)
next
  case (Fwd u a v ctx) then show ?case by (rule fwd_ok)
next
  case (SeedNe p ctx) show ?case by simp
next
  case (CallFwd u ctx dst pars args p cont)
  show ?case using CallFwd(1,2) by (rule call_fwd_ok)
next
  case (CombFwd cl c1 dst pars args p cont)
  show ?case using CombFwd(1,2) by (rule comb_fwd_ok)
qed

subsection \<open>Activation-indexed collecting soundness\<close>

lemma ictx_entry_cinit_le_cinit_int_dom_st:
  "cinit_stores gs \<subseteq> int_dom_gamma gs (Lifted cinit_int_dom_st) Bot"
  by (auto simp: int_dom_gamma_def cinit_stores_def gamma_state_def fun_of_resolved_st_q_for_def
                 fun_of_st_cinit_int_dom_st_for gamma_int_dom_top)

text \<open>The trace-semantic context function the routed table induces: at a call site it
  routes the entered store's abstraction, read from the solver's own table.\<close>

definition ictx_entry_enterc :: "cfg_node \<Rightarrow> int_dom list \<Rightarrow> store \<Rightarrow> int_dom list" where
  "ictx_entry_enterc u ctx s =
     route_enterc_of_sigma (int_dom_spec mode empty_pred gs)
       (ictx_entry_route_gen mode gs empty_pred) (snd (ictx_entry_sol mode gs empty_pred Pi ps))
       (Analysis_Global ()) (compile_prog Pi ps) u ctx s"

lemmas ictx_entry_routed_context_call =
  ictx_entry_routed.routed_context_call[folded ictx_entry_enterc_def]
lemmas ictx_entry_routed_context_comb =
  ictx_entry_routed.routed_context_comb[folded ictx_entry_enterc_def]

text \<open>
  \<^locale>\<open>dg_analysis_adapter\<close> at the same executable solved system, handed the readback
  as \<open>rd\<close> and Int's classifier; its activation-collect soundness is the entry-state
  soundness theorem, stated against the routed local unknown read back through
  \<^const>\<open>gamma_state_lift\<close>.
\<close>

interpretation ictx_entry_adapter: dg_analysis_adapter "int_dom_spec mode empty_pred gs"
    "int_dom_gamma gs" gs "compile_prog Pi ps" "Analysis_Global ()" "ictx_entry_route_gen mode gs empty_pred"
    Bot "Lifted cinit_int_dom_st" Bot
    "snd (ictx_entry_sol mode gs empty_pred Pi ps)" "fst (ictx_entry_sol mode gs empty_pred Pi ps)"
    "(cfg_exit (compile_prog Pi ps), [])" "ictx_entry_sg_st mode gs empty_pred Pi ps"
    Activation_Seed "\<lambda>m. gamma_state_lift (map_lift (fun_of_resolved_st_q_for gs) m)" ictx_entry_enterc
    "map_lift (fun_of_resolved_st_q_for gs)" int_classify_check
proof (unfold_locales, goal_cases FinE PP SgCov SgUncov Fwd FinC SeedKey ResolveSound
    RouteEnterc CallFwd CombFwd EnterAgree GammaRd ClProved ClRefuted)
  case FinE show ?case by (rule ictx_entry_fin)
next
  case PP show ?case by (rule ictx_entry_pp_routed[OF solves exact])
next
  case (SgCov v c)
  thus ?case by (simp add: ictx_entry_sg_st_def int_dom_gamma_def)
next
  case (SgUncov v c)
  thus ?case by (simp add: ictx_entry_sg_st_def)
next
  case (Fwd u a v c)
  thus ?case by (rule fwd_ok)
next
  case FinC show ?case by (rule ictx_entry_finC)
next
  case (SeedKey p ctx) show ?case by simp
next
  case (ResolveSound u ctx dst pars args p cont s)
  thus ?case by (simp add: static_resolve_iff[OF ictx_entry_finC])
next
  case (RouteEnterc u ctx dst pars args p cont s)
  show ?case unfolding ictx_entry_enterc_def
    by (rule route_enterc_of_sigma_agree[OF ictx_entry_finC compile_prog_calls_source_unique
                                              RouteEnterc(2)])
next
  case (CallFwd u ctx dst pars args p cont)
  show ?case using CallFwd(1,2) by (rule call_fwd_ok)
next
  case (CombFwd cl c1 dst pars args p cont)
  show ?case using CombFwd(1,2) by (rule comb_fwd_ok)
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
  show ?case by (simp add: int_dom_gamma_def)
next
  case (ClProved c d s)
  thus ?case by (rule int_classify_check_proved)
next
  case (ClRefuted c d s)
  thus ?case by (rule int_classify_check_refuted)
qed

theorem ictx_entry_activation_collect_sound:
  "activation_collect gs ictx_entry_enterc [] (compile_prog Pi ps) (cinit_stores gs) v ctx
     \<subseteq> gamma_state_lift (map_lift (fun_of_resolved_st_q_for gs)
           (ictx_entry_sg_st mode gs empty_pred Pi ps (Inl (v, ctx))))"
  by (rule ictx_entry_adapter.activation_collect_dg_sound
             [OF entry_cov ictx_entry_cinit_le_cinit_int_dom_st])

end

subsection \<open>Whole-program convenience layer\<close>

text \<open>
  Fixed at \<^const>\<open>Refine_Fixpoint\<close>, matching Int's own production default and Int's
  own call-string instance's posture: \<open>mode\<close> stays a genuine parameter through every
  lemma above, and is only pinned here where the public, config-driven surface needs
  one concrete choice.
\<close>

definition ictx_entry_eqs_prog ::
    "(vname \<Rightarrow> bool) \<Rightarrow> imp_prog
       \<Rightarrow> (pp \<times> int_dom list, (unit, int_dom list) routed_gk, (int_dom exec_dg_st lifted, int_dom exec_dg_st lifted) dg_state) eqsT" where
  "ictx_entry_eqs_prog gs p =
     ictx_entry_eqs Refine_Fixpoint gs (resolved_st_q_is_bot_for (declared_global_vars p))
       (prog_table p) (prog_procs p)"

definition ictx_entry_sol_prog ::
    "(vname \<Rightarrow> bool) \<Rightarrow> imp_prog
       \<Rightarrow> (pp \<times> int_dom list) set \<times> (pp \<times> int_dom list + (unit, int_dom list) routed_gk \<Rightarrow> (int_dom exec_dg_st lifted, int_dom exec_dg_st lifted) dg_state)" where
  "ictx_entry_sol_prog gs p =
     ictx_entry_sol Refine_Fixpoint gs (resolved_st_q_is_bot_for (declared_global_vars p))
       (prog_table p) (prog_procs p)"

definition ictx_entry_terminates_prog :: "(vname \<Rightarrow> bool) \<Rightarrow> imp_prog \<Rightarrow> bool" where
  "ictx_entry_terminates_prog gs p =
     ictx_entry_terminates Refine_Fixpoint gs (resolved_st_q_is_bot_for (declared_global_vars p))
       (prog_table p) (prog_procs p)"

lemma ictx_entry_terminates_prog_via_solve_c:
  assumes "TD_side_always_join_Interp_solve_c
             (ictx_entry_eqs_prog gs p)
             (cfg_exit (compile_prog (prog_table p) (prog_procs p)), []) \<noteq> None"
  shows "ictx_entry_terminates_prog gs p"
  using assms
  unfolding ictx_entry_terminates_prog_def ictx_entry_eqs_prog_def
  by (rule ictx_entry_terminates_via_solve_c)

definition ictx_entry_sol_prog_warrow ::
    "(vname \<Rightarrow> bool) \<Rightarrow> imp_prog
       \<Rightarrow> (pp \<times> int_dom list) set \<times> (pp \<times> int_dom list + (unit, int_dom list) routed_gk \<Rightarrow> (int_dom exec_dg_st lifted, int_dom exec_dg_st lifted) dg_state)" where
  "ictx_entry_sol_prog_warrow gs p =
     ictx_entry_sol_warrow Refine_Fixpoint gs (resolved_st_q_is_bot_for (declared_global_vars p))
       (prog_table p) (prog_procs p)"

definition ictx_entry_terminates_prog_warrow :: "(vname \<Rightarrow> bool) \<Rightarrow> imp_prog \<Rightarrow> bool" where
  "ictx_entry_terminates_prog_warrow gs p =
     ictx_entry_terminates_warrow Refine_Fixpoint gs (resolved_st_q_is_bot_for (declared_global_vars p))
       (prog_table p) (prog_procs p)"

lemma ictx_entry_terminates_prog_warrow_via_solve_c:
  assumes "TD_side_warrowing_apinis_Interp_solve_c
             (ictx_entry_eqs_prog gs p)
             (cfg_exit (compile_prog (prog_table p) (prog_procs p)), []) \<noteq> None"
  shows "ictx_entry_terminates_prog_warrow gs p"
  using assms
  unfolding ictx_entry_terminates_prog_warrow_def ictx_entry_eqs_prog_def
  by (rule ictx_entry_terminates_warrow_via_solve_c)

section \<open>Solved-result table\<close>

text \<open>
  The solved entry-state D/G system, read as a \<^typ>\<open>(int_dom list, int_dom abs_state)
  analysis_result\<close> -- the exact construction Sign's and Interval's own entry-state
  result tables already use, at Int's own solve. The covered-key set is the solver's
  own, never an enumerated theoretical context space.
\<close>

definition analyse_int_entry_state_result_for ::
    "(vname \<Rightarrow> bool) \<Rightarrow> imp_prog \<Rightarrow> (int_dom list, int_dom abs_state) analysis_result" where
  "analyse_int_entry_state_result_for gs p =
     Analysis_Result
       (fst (ictx_entry_sol_prog gs p))
       (\<lambda>v ctx. normalize_point gs
                  (canonicalize_lift (resolved_st_q_is_bot_for (declared_global_vars p))
                    (locals (snd (ictx_entry_sol_prog gs p) (Inl (v, ctx))))))"

declare analyse_int_entry_state_result_for_def [code del]

lemma analyse_int_entry_state_result_for_code [code]:
  "analyse_int_entry_state_result_for gs p =
     (let sol = ictx_entry_sol_prog gs p; gl = declared_global_vars p
      in Analysis_Result (fst sol)
           (\<lambda>v ctx. normalize_point gs
                      (canonicalize_lift (resolved_st_q_is_bot_for gl)
                        (locals (snd sol (Inl (v, ctx)))))))"
  unfolding analyse_int_entry_state_result_for_def Let_def by (rule refl)

text \<open>Convenience instance at \<^const>\<open>declared_global\<close> \<open>p\<close> and \<^const>\<open>prog_main_name\<close>,
  matching \<open>analyse_int_call_string_result\<close>'s shape.\<close>

definition analyse_int_entry_state_result :: "imp_prog \<Rightarrow> (int_dom list, int_dom abs_state) analysis_result" where
  "analyse_int_entry_state_result p =
     analyse_int_entry_state_result_for (declared_global p) p"

section \<open>Contextual check report\<close>

text \<open>
  Reuses \<^const>\<open>classify_checks_ctx\<close>/\<^const>\<open>classify_checks_verdicts\<close> unchanged --
  both are generic in the context type already, so nothing entry-state-specific is
  needed here beyond supplying the entry-state result table and Int's own
  \<^const>\<open>int_classify_check\<close>.
\<close>

definition ictx_entry_check_projection ::
    "imp_prog \<Rightarrow> (pp \<times> exp \<times> (int_dom list \<times> contextual_verdict) set) list" where
  "ictx_entry_check_projection p =
     classify_checks_ctx (prog_cfg p)
       (analyse_int_entry_state_result_for (declared_global p) p)
       int_classify_check"

definition ictx_entry_verdict_report_prog ::
    "imp_prog \<Rightarrow> (pp \<times> exp \<times> contextual_verdict) list" where
  "ictx_entry_verdict_report_prog p =
     map (\<lambda>(u, c, vs). (u, c, aggregate_verdicts (snd ` vs)))
       (ictx_entry_check_projection p)"

lemma ictx_entry_verdict_report_prog_eq:
  "ictx_entry_verdict_report_prog p =
     classify_checks_verdicts (prog_cfg p)
       (analyse_int_entry_state_result_for (declared_global p) p)
       int_classify_check"
  unfolding ictx_entry_verdict_report_prog_def ictx_entry_check_projection_def
  by (rule classify_checks_verdicts_proj)

definition analyse_int_entry_state_report :: "imp_prog \<Rightarrow> (pp \<times> exp \<times> contextual_verdict) list" where
  "analyse_int_entry_state_report p = ictx_entry_verdict_report_prog p"

end
