theory Parity_Ctx_Entry_State_Sound
  imports
    "Voblint_Analysis.Parity_Sound"
    "Voblint_Analysis.Parity_Checks"
    "Voblint_Core.Routed_Analysis_Sound"
    Entry_State_Routed_Context
begin

section \<open>Parity at the routed spine, instantiated at the entry-state context\<close>

text \<open>
  The entry-state run of the Parity analysis, and the harder of Parity's two
  context-sensitive runs: unlike a call string, this route reads the value it is
  handed, so the routing-agreement obligation is not free. It is discharged from
  \<^locale>\<open>routed_dg_domain_exec\<close>'s own three primitive commute facts, which
  \<^theory>\<open>Voblint_Analysis.Parity_Sound\<close> already establishes -- no fact about parity
  arithmetic or parity transfer is restated here either.

  A context is the list of abstract values the formals hold on entry, so two calls
  reaching a procedure with the same entered frame share a local unknown and any
  other pair does not. The routed generator enters the callee frame before it routes,
  so \<open>pctx_entry_route\<close> below only projects the formals out of the state it is given.

  The global keys are \<^typ>\<open>(unit, parity list) routed_gk\<close>: \<^const>\<open>Analysis_Global\<close> at
  \<^typ>\<open>unit\<close>, since Parity publishes no named global of its own, and
  \<^const>\<open>Activation_Seed\<close> carrying the callee entry point with the routed context.
\<close>

subsection \<open>The routed equation system's own route, generic per compiled program\<close>

text \<open>
  Parity's executable-carrier route: this is \<^locale>\<open>routed_dg_domain_exec\<close>'s own
  \<open>entry_exec_route\<close>/\<open>entry_exec_route_gen\<close> (\<^theory>\<open>Voblint_Exec.DG_Base_Exec\<close>),
  restated as unconditional top-level definitions rather than reached through an
  interpretation, so the equation-system definitions below need no \<open>exact\<close> premise in
  order to be stated.
\<close>

definition pctx_entry_route ::
    "(vname \<Rightarrow> bool) \<Rightarrow> (parity exec_dg_st \<Rightarrow> bool) \<Rightarrow> parity exec_dg_st lifted \<Rightarrow> call_action \<Rightarrow> parity list" where
  "pctx_entry_route gs empty_pred d ca =
     (case ca of CallEdge dst pars args \<Rightarrow>
        formals_context pars (fun_of_resolved_st_q_for gs
          (case d of Bot \<Rightarrow> bot | Lifted d0 \<Rightarrow> d0)))"

definition pctx_entry_route_gen ::
    "(vname \<Rightarrow> bool) \<Rightarrow> (parity exec_dg_st \<Rightarrow> bool) \<Rightarrow> pp \<Rightarrow> parity list \<Rightarrow> parity exec_dg_st lifted \<Rightarrow> call_action \<Rightarrow> parity list" where
  "pctx_entry_route_gen gs empty_pred u ctx d ca = pctx_entry_route gs empty_pred d ca"

subsection \<open>The routed equation system and its executable solution\<close>

definition pctx_entry_eqs ::
    "(vname \<Rightarrow> bool) \<Rightarrow> (parity exec_dg_st \<Rightarrow> bool) \<Rightarrow> proc_table \<Rightarrow> pname list \<Rightarrow> (pp \<times> parity list, (unit, parity list) routed_gk, (parity exec_dg_st lifted, parity exec_dg_st lifted) dg_state) eqsT" where
  "pctx_entry_eqs gs empty_pred Pi ps =
     side_cfg_T_eff_keyed_seed_dg_buffered intra_predecessor_addr_list (\<lambda>_. Analysis_Global ())
       (pctx_entry_route_gen gs empty_pred)
       (\<lambda>ctx' src a. dg_spec_edge_tree (pctx_spec gs empty_pred) a src (\<lambda>_. Analysis_Global ()))
       (routed_cmb_g (pctx_spec gs empty_pred) (Analysis_Global ()) Activation_Seed
          (static_resolve (compile_prog Pi ps)))
       (routed_extra_g Activation_Seed (Analysis_Global ()))
       (compile_prog Pi ps) Bot (Lifted cinit_parity_st) Bot"

definition pctx_entry_sol ::
    "(vname \<Rightarrow> bool) \<Rightarrow> (parity exec_dg_st \<Rightarrow> bool) \<Rightarrow> proc_table \<Rightarrow> pname list \<Rightarrow> (pp \<times> parity list) set \<times> (pp \<times> parity list + (unit, parity list) routed_gk \<Rightarrow> (parity exec_dg_st lifted, parity exec_dg_st lifted) dg_state)" where
  "pctx_entry_sol gs empty_pred Pi ps =
     TD_side_always_join_Interp_solve (pctx_entry_eqs gs empty_pred Pi ps)
       (cfg_exit (compile_prog Pi ps), [])"

definition pctx_entry_terminates ::
    "(vname \<Rightarrow> bool) \<Rightarrow> (parity exec_dg_st \<Rightarrow> bool) \<Rightarrow> proc_table \<Rightarrow> pname list \<Rightarrow> bool" where
  "pctx_entry_terminates gs empty_pred Pi ps =
     TD_side_always_join_Interp.solve_dom TYPE((unit, parity list) routed_gk) TYPE((parity exec_dg_st lifted, parity exec_dg_st lifted) dg_state)
       (pctx_entry_eqs gs empty_pred Pi ps) (cfg_exit (compile_prog Pi ps), [])"

lemma pctx_entry_terminates_via_solve_c:
  assumes "TD_side_always_join_Interp_solve_c (pctx_entry_eqs gs empty_pred Pi ps)
             (cfg_exit (compile_prog Pi ps), []) \<noteq> None"
  shows "pctx_entry_terminates gs empty_pred Pi ps"
  unfolding pctx_entry_terminates_def
  by (rule TD_side_always_join_Interp.solve_dom_of_solve_c[OF assms])

subsection \<open>Route agreement: the one genuinely domain-specific commute fact\<close>

context
  fixes gs :: "vname \<Rightarrow> bool" and empty_pred :: "parity exec_dg_st \<Rightarrow> bool"
  assumes exact: "\<And>s. empty_pred s = is_empty_state (fun_of_resolved_st_q_for gs s)"
begin

interpretation parity_domain: routed_dg_domain_exec
  gs empty_pred "parity_tf_st_for gs" "parity_enter_st_for gs" "parity_tf_for gs"
  by unfold_locales (rule parity_tf_st_for_commute, rule parity_enter_st_for_commute, rule exact)

lemma pctx_entry_route_gen_eq_generic:
  "pctx_entry_route_gen gs empty_pred u ctx d ca = parity_domain.entry_exec_route_gen u ctx d ca"
  unfolding pctx_entry_route_gen_def parity_domain.entry_exec_route_gen_def
    pctx_entry_route_def parity_domain.entry_exec_route_def
  by (rule refl)

lemma pctx_entry_route_gen_commute:
  "formals_route_lifted_gen u ctx (map_lift (fun_of_resolved_st_q_for gs) d) ca
     = pctx_entry_route_gen gs empty_pred u ctx d ca"
  unfolding pctx_entry_route_gen_eq_generic
  by (rule parity_domain.entry_exec_route_gen_commute)

end

subsection \<open>Per-tree transport commutation\<close>

text \<open>
  The same interpretation Parity's unit-context run makes, at the entry-state routing
  policy. \<^locale>\<open>routed_domain_exec\<close> takes the routing-agreement fact as a parameter,
  so switching context policy stays a different instantiation of one derivation.
\<close>

context
  fixes gs :: "vname \<Rightarrow> bool" and empty_pred :: "parity exec_dg_st \<Rightarrow> bool"
  assumes exact: "\<And>s. empty_pred s = is_empty_state (fun_of_resolved_st_q_for gs s)"
begin

interpretation parity_es: routed_domain_exec
  gs empty_pred "parity_tf_st_for gs" "parity_enter_st_for gs" "parity_tf_for gs"
  "Analysis_Global ()" Activation_Seed "pctx_entry_route_gen gs empty_pred"
  formals_route_lifted_gen
  static_resolve static_resolve
  by unfold_locales
     (rule parity_tf_st_for_commute, rule parity_enter_st_for_commute, rule exact, simp,
      rule pctx_entry_route_gen_commute[OF exact, symmetric],
      simp add: static_resolve_def)

lemmas parity_es_pp_st_gen = parity_es.pp_st

end

subsection \<open>The certified executable post-solution, generic per compiled program\<close>

context
  fixes gs :: "vname \<Rightarrow> bool" and empty_pred :: "parity exec_dg_st \<Rightarrow> bool"
    and Pi :: proc_table and ps :: "pname list"
  assumes solves: "pctx_entry_terminates gs empty_pred Pi ps"
    and exact: "\<And>s. empty_pred s = is_empty_state (fun_of_resolved_st_q_for gs s)"
begin

lemma pctx_entry_solve_dom:
  "TD_side_always_join_Interp.solve_dom TYPE((unit, parity list) routed_gk) TYPE((parity exec_dg_st lifted, parity exec_dg_st lifted) dg_state)
     (pctx_entry_eqs gs empty_pred Pi ps) (cfg_exit (compile_prog Pi ps), [])"
  using solves[unfolded pctx_entry_terminates_def] .

lemma pctx_entry_pp_st:
  "part_post_solution (pctx_entry_eqs gs empty_pred Pi ps) (cfg_exit (compile_prog Pi ps), [])
     (snd (pctx_entry_sol gs empty_pred Pi ps)) (fst (pctx_entry_sol gs empty_pred Pi ps))"
  using TD_side_always_join_Interp.partial_post_solution
          [OF pctx_entry_solve_dom, of "fst (pctx_entry_sol gs empty_pred Pi ps)"
             "snd (pctx_entry_sol gs empty_pred Pi ps)"]
  unfolding pctx_entry_sol_def by simp

text \<open>The solver's post-solution, for the unbuffered routed generator at the executable
  spec and Parity's executable route.\<close>

theorem pctx_entry_pp_routed:
  "part_post_solution
     (side_cfg_T_eff_keyed_seed_dg intra_predecessor_addr_list (\<lambda>_. Analysis_Global ())
        (pctx_entry_route_gen gs empty_pred)
        (\<lambda>ctx' src a. dg_spec_edge_tree (pctx_spec gs empty_pred) a src (\<lambda>_. Analysis_Global ()))
        (routed_cmb_g (pctx_spec gs empty_pred) (Analysis_Global ()) Activation_Seed
           (static_resolve (compile_prog Pi ps)))
        (routed_extra_g Activation_Seed (Analysis_Global ()))
        (compile_prog Pi ps) Bot (Lifted cinit_parity_st) Bot)
     (cfg_exit (compile_prog Pi ps), [])
     (snd (pctx_entry_sol gs empty_pred Pi ps)) (fst (pctx_entry_sol gs empty_pred Pi ps))"
  using pctx_entry_pp_st unfolding pctx_entry_eqs_def pctx_spec_def
  by (rule parity_es_pp_st_gen[OF exact])

end

section \<open>Activation-indexed collecting soundness, generic per compiled program\<close>

definition pctx_entry_sg_st ::
    "(vname \<Rightarrow> bool) \<Rightarrow> (parity exec_dg_st \<Rightarrow> bool) \<Rightarrow> proc_table \<Rightarrow> pname list
       \<Rightarrow> pp \<times> parity list + (unit, parity list) routed_gk \<Rightarrow> parity exec_dg_st lifted" where
  "pctx_entry_sg_st gs empty_pred Pi ps =
     solved_local_reader (fst (pctx_entry_sol gs empty_pred Pi ps))
                         (snd (pctx_entry_sol gs empty_pred Pi ps))"

context
  fixes gs :: "vname \<Rightarrow> bool" and empty_pred :: "parity exec_dg_st \<Rightarrow> bool"
    and Pi :: proc_table and ps :: "pname list"
  assumes solves: "pctx_entry_terminates gs empty_pred Pi ps"
    and exact: "\<And>s. empty_pred s = is_empty_state (fun_of_resolved_st_q_for gs s)"
    and entry_cov: "(cfg_entry (compile_prog Pi ps), []) \<in> fst (pctx_entry_sol gs empty_pred Pi ps)"
    and fwd_ok: "\<And>u a v ctx. (u, ctx) \<in> fst (pctx_entry_sol gs empty_pred Pi ps)
                   \<Longrightarrow> (u, a, v) \<in> intra (compile_prog Pi ps)
                   \<Longrightarrow> (v, ctx) \<in> fst (pctx_entry_sol gs empty_pred Pi ps)"
    and call_fwd_ok: "\<And>u ctx dst pars args p cont.
        (u, ctx) \<in> fst (pctx_entry_sol gs empty_pred Pi ps)
        \<Longrightarrow> (u, CallEdge dst pars args, FunctionEntry p, cont) \<in> calls (compile_prog Pi ps)
        \<Longrightarrow> (FunctionEntry p,
               pctx_entry_route_gen gs empty_pred u ctx
                 (entered (pctx_spec gs empty_pred) (Analysis_Global ())
                    (snd (pctx_entry_sol gs empty_pred Pi ps))
                    (call_info_of (CallEdge dst pars args) p) (Inl (u, ctx)))
                 (CallEdge dst pars args))
             \<in> fst (pctx_entry_sol gs empty_pred Pi ps)"
    and comb_fwd_ok: "\<And>cl c1 dst pars args p cont.
        (cl, c1) \<in> fst (pctx_entry_sol gs empty_pred Pi ps)
        \<Longrightarrow> (cl, CallEdge dst pars args, FunctionEntry p, cont) \<in> calls (compile_prog Pi ps)
        \<Longrightarrow> (cont, c1) \<in> fst (pctx_entry_sol gs empty_pred Pi ps)"
begin

subsection \<open>The solver's table as the solved system\<close>

interpretation pctx_entry_compiled: compiled_cfg Pi ps "compile_prog Pi ps"
  by (unfold_locales; simp add: compile_prog_finite)

lemmas pctx_entry_fin = pctx_entry_compiled.finite_intra
lemmas pctx_entry_finC = pctx_entry_compiled.finite_calls

lemma pctx_entry_sg_st_covered:
  "(v, ctx) \<in> fst (pctx_entry_sol gs empty_pred Pi ps)
   \<Longrightarrow> pctx_entry_sg_st gs empty_pred Pi ps (Inl (v, ctx))
         = locals (snd (pctx_entry_sol gs empty_pred Pi ps) (Inl (v, ctx)))"
  by (simp add: pctx_entry_sg_st_def)

lemma pctx_entry_sg_st_uncovered_empty:
  "(v, ctx) \<notin> fst (pctx_entry_sol gs empty_pred Pi ps)
     \<Longrightarrow> gamma_state_lift (map_lift (fun_of_resolved_st_q_for gs)
           (pctx_entry_sg_st gs empty_pred Pi ps (Inl (v, ctx)))) = {}"
  by (simp add: pctx_entry_sg_st_def)

subsection \<open>Instantiating the generic routed-context locale\<close>

interpretation pctx_entry_dg_base: sound_dg_spec "pctx_spec gs empty_pred" "pctx_gamma gs" gs
  by (rule pctx_sound_exec[OF exact])

interpretation pctx_entry_routed: entry_state_routed_context "pctx_spec gs empty_pred"
    "pctx_gamma gs" gs Pi ps "Analysis_Global ()" "pctx_entry_route_gen gs empty_pred"
    Bot "Lifted cinit_parity_st" Bot
    "snd (pctx_entry_sol gs empty_pred Pi ps)" "fst (pctx_entry_sol gs empty_pred Pi ps)"
    "(cfg_exit (compile_prog Pi ps), [])" "pctx_entry_sg_st gs empty_pred Pi ps" Activation_Seed
    "\<lambda>m. gamma_state_lift (map_lift (fun_of_resolved_st_q_for gs) m)"
proof (unfold_locales, goal_cases FinE PP SgCov SgUncov Fwd SeedNe CallFwd CombFwd)
  case FinE show ?case by (rule pctx_entry_fin)
next
  case PP show ?case by (rule pctx_entry_pp_routed[OF solves exact])
next
  case (SgCov v ctx) then show ?case
    by (simp add: pctx_entry_sg_st_def pctx_gamma_def)
next
  case (SgUncov v ctx) then show ?case by (rule pctx_entry_sg_st_uncovered_empty)
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

lemma pctx_entry_cinit_le_cinit_parity_st:
  "cinit_stores gs \<subseteq> pctx_gamma gs (Lifted cinit_parity_st) Bot"
  by (auto simp: pctx_gamma_def cinit_stores_def gamma_state_def fun_of_resolved_st_q_for_def
                 fun_of_st_cinit_parity_st_for)

text \<open>The trace-semantic context function the routed table induces: at a call site it
  routes the entered store's abstraction, read from the solver's own table.\<close>

definition pctx_entry_enterc :: "cfg_node \<Rightarrow> parity list \<Rightarrow> store \<Rightarrow> parity list" where
  "pctx_entry_enterc u ctx s =
     route_enterc_of_sigma (pctx_spec gs empty_pred)
       (pctx_entry_route_gen gs empty_pred) (snd (pctx_entry_sol gs empty_pred Pi ps))
       (Analysis_Global ()) (compile_prog Pi ps) u ctx s"

lemmas pctx_entry_routed_context_call =
  pctx_entry_routed.routed_context_call[folded pctx_entry_enterc_def]
lemmas pctx_entry_routed_context_comb =
  pctx_entry_routed.routed_context_comb[folded pctx_entry_enterc_def]

interpretation pctx_entry_adapter: routed_analysis_sound
    "pctx_spec gs empty_pred" "pctx_gamma gs" gs
    "compile_prog Pi ps" "Analysis_Global ()" "pctx_entry_route_gen gs empty_pred"
    Bot "Lifted cinit_parity_st" Bot
    "snd (pctx_entry_sol gs empty_pred Pi ps)" "fst (pctx_entry_sol gs empty_pred Pi ps)"
    "(cfg_exit (compile_prog Pi ps), [])"
    Activation_Seed pctx_entry_enterc
    "map_lift (fun_of_resolved_st_q_for gs)" parity_classify_check
proof (unfold_locales, goal_cases FinE PP SgCov SgUncov Fwd FinC SeedKey ResolveSound
    RouteEnterc CallFwd CombFwd EnterAgree GammaRd ClProved ClRefuted)
  case FinE show ?case by (rule pctx_entry_fin)
next
  case PP show ?case by (rule pctx_entry_pp_routed[OF solves exact])
next
  case (SgCov v c)
  thus ?case by (simp add: pctx_gamma_def)
next
  case (SgUncov v c)
  thus ?case by simp
next
  case (Fwd u a v c)
  thus ?case by (rule fwd_ok)
next
  case FinC show ?case by (rule pctx_entry_finC)
next
  case (SeedKey p ctx) show ?case by simp
next
  case (ResolveSound u ctx dst pars args p cont s)
  thus ?case by (simp add: static_resolve_iff[OF pctx_entry_finC])
next
  case (RouteEnterc u ctx dst pars args p cont s)
  show ?case unfolding pctx_entry_enterc_def
    by (rule route_enterc_of_sigma_agree[OF pctx_entry_finC compile_prog_calls_source_unique
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
  show ?case by (simp add: pctx_gamma_def)
next
  case (ClProved c d s)
  thus ?case by (rule parity_classify_check_proved)
next
  case (ClRefuted c d s)
  thus ?case by (rule parity_classify_check_refuted)
qed

theorem pctx_entry_activation_collect_sound:
  "activation_collect gs pctx_entry_enterc [] (compile_prog Pi ps) (cinit_stores gs) v ctx
     \<subseteq> gamma_state_lift (map_lift (fun_of_resolved_st_q_for gs)
           (pctx_entry_sg_st gs empty_pred Pi ps (Inl (v, ctx))))"
  unfolding pctx_entry_sg_st_def
  by (rule pctx_entry_adapter.routed_activation_collect_sound
        [OF entry_cov pctx_entry_cinit_le_cinit_parity_st])
end

subsection \<open>Whole-program convenience layer\<close>

definition pctx_entry_eqs_prog ::
    "(vname \<Rightarrow> bool) \<Rightarrow> imp_prog
       \<Rightarrow> (pp \<times> parity list, (unit, parity list) routed_gk, (parity exec_dg_st lifted, parity exec_dg_st lifted) dg_state) eqsT" where
  "pctx_entry_eqs_prog gs p =
     pctx_entry_eqs gs (resolved_st_q_is_bot_for (declared_global_vars p))
       (prog_table p) (prog_procs p)"

definition pctx_entry_sol_prog ::
    "(vname \<Rightarrow> bool) \<Rightarrow> imp_prog
       \<Rightarrow> (pp \<times> parity list) set \<times> (pp \<times> parity list + (unit, parity list) routed_gk \<Rightarrow> (parity exec_dg_st lifted, parity exec_dg_st lifted) dg_state)" where
  "pctx_entry_sol_prog gs p =
     pctx_entry_sol gs (resolved_st_q_is_bot_for (declared_global_vars p))
       (prog_table p) (prog_procs p)"

definition pctx_entry_terminates_prog :: "(vname \<Rightarrow> bool) \<Rightarrow> imp_prog \<Rightarrow> bool" where
  "pctx_entry_terminates_prog gs p =
     pctx_entry_terminates gs (resolved_st_q_is_bot_for (declared_global_vars p))
       (prog_table p) (prog_procs p)"

lemma pctx_entry_terminates_prog_via_solve_c:
  assumes "TD_side_always_join_Interp_solve_c
             (pctx_entry_eqs_prog gs p)
             (cfg_exit (compile_prog (prog_table p) (prog_procs p)), []) \<noteq> None"
  shows "pctx_entry_terminates_prog gs p"
  using assms
  unfolding pctx_entry_terminates_prog_def pctx_entry_eqs_prog_def
  by (rule pctx_entry_terminates_via_solve_c)

section \<open>Solved-result table\<close>

definition analyse_parity_entry_state_result_for ::
    "(vname \<Rightarrow> bool) \<Rightarrow> imp_prog \<Rightarrow> (parity list, parity abs_state) analysis_result" where
  "analyse_parity_entry_state_result_for gs p =
     Analysis_Result
       (fst (pctx_entry_sol_prog gs p))
       (\<lambda>v ctx. normalize_point gs
                  (canonicalize_lift (resolved_st_q_is_bot_for (declared_global_vars p))
                    (locals (snd (pctx_entry_sol_prog gs p) (Inl (v, ctx))))))"

declare analyse_parity_entry_state_result_for_def [code del]

lemma analyse_parity_entry_state_result_for_code [code]:
  "analyse_parity_entry_state_result_for gs p =
     (let sol = pctx_entry_sol_prog gs p; gl = declared_global_vars p
      in Analysis_Result (fst sol)
           (\<lambda>v ctx. normalize_point gs
                      (canonicalize_lift (resolved_st_q_is_bot_for gl)
                        (locals (snd sol (Inl (v, ctx)))))))"
  unfolding analyse_parity_entry_state_result_for_def Let_def by (rule refl)

definition analyse_parity_entry_state_result ::
    "imp_prog \<Rightarrow> (parity list, parity abs_state) analysis_result" where
  "analyse_parity_entry_state_result p =
     analyse_parity_entry_state_result_for (declared_global p) p"

section \<open>Contextual check report\<close>

definition pctx_entry_check_projection ::
    "imp_prog \<Rightarrow> (pp \<times> exp \<times> (parity list \<times> contextual_verdict) set) list" where
  "pctx_entry_check_projection p =
     classify_checks_ctx (prog_cfg p)
       (analyse_parity_entry_state_result_for (declared_global p) p)
       parity_classify_check"

definition pctx_entry_verdict_report_prog ::
    "imp_prog \<Rightarrow> (pp \<times> exp \<times> contextual_verdict) list" where
  "pctx_entry_verdict_report_prog p =
     map (\<lambda>(u, c, vs). (u, c, aggregate_verdicts (snd ` vs)))
       (pctx_entry_check_projection p)"

lemma pctx_entry_verdict_report_prog_eq:
  "pctx_entry_verdict_report_prog p =
     classify_checks_verdicts (prog_cfg p)
       (analyse_parity_entry_state_result_for (declared_global p) p)
       parity_classify_check"
  unfolding pctx_entry_verdict_report_prog_def pctx_entry_check_projection_def
  by (rule classify_checks_verdicts_proj)

definition analyse_parity_entry_state_report ::
    "imp_prog \<Rightarrow> (pp \<times> exp \<times> contextual_verdict) list" where
  "analyse_parity_entry_state_report p = pctx_entry_verdict_report_prog p"

end
