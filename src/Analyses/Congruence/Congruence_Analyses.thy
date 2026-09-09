theory Congruence_Analyses
  imports
    Congruence_Assembly
    Congruence_Sound
    "Voblint_Routing.Compiled_Routed_Equations"
    Congruence_Classify
    Congruence_Exec
    "Voblint_Result.DG_Result_Construction"
    "Voblint_Framework.CFG_Enumeration"
    "Voblint_Exec.Routed_Exec_Refinement"
    "Voblint_Exec.DG_Local_State_Exec_Refinement"
    "Voblint_Framework.DG_Local_State_Spec"
    "Voblint_Framework.Routed_Analysis_Sound"
    "Voblint_Framework.Routed_Context"
    "Voblint_Framework.Routed_Context_Unit"
    "Voblint_Framework.Activation_Backbone"
    "Voblint_Framework.Analysis_Result"
    "Voblint_Framework.Call_String_Context"
    "Voblint_Solver.TD_Solver_Bridge"
    "Voblint_Compile.Compile_Invariants"
    "Voblint_CFG.CFG_Prune"
    "Voblint_VIMP.VIMP_Program"
    "TD.TD_side_upd_rule"
    "Voblint_Routing.Call_String_Routed_Context"
    "Voblint_Routing.Entry_State_Routed_Context"
begin

chapter \<open>How Congruence is run under each supported context policy\<close>

text \<open>
  Congruence's analysis package -- specification, concretization and soundness --
  lives in \<^theory>\<open>Voblint_Analysis_Congruence.Congruence_Sound\<close> and mentions no
  context. This theory supplies the configurations: for each supported context
  policy, the equation system that pairing generates, its solved table, the
  coverage premises the solver's reachable set must satisfy, and the result and
  report tables a caller consumes.

  The two configurations here are independent of one another and both name the
  same \<open>cctx_spec\<close> and \<open>cctx_sound_exec\<close>; neither derives a fact about modular
  arithmetic. Global keys are \<^type>\<open>routed_gk\<close>, with \<^const>\<open>Analysis_Global\<close> at
  \<^typ>\<open>unit\<close> since Congruence publishes no named global of its own; the
  call-string configuration uses the shared \<^typ>\<open>call_string_gk\<close>.

  The unit context is not among them. That configuration lives in
  \<^theory>\<open>Voblint_Analysis_Congruence.Congruence_Assembly\<close>, as interpretations of
  the shared \<^locale>\<open>unit_dg_analysis\<close> --- one per solver discipline. What remains
  here are the two configurations that route calls to more than one context,
  which the assembly's fixed unit route cannot express.
\<close>


section \<open>Congruence at the routed spine, instantiated at the call-string context\<close>

text \<open>
  The call-string run. Everything about Congruence it needs -- the specification
  \<^const>\<open>cctx_spec\<close>, its concretization \<^const>\<open>cctx_gamma\<close>, and the soundness of
  one against the other -- is taken from
  \<^theory>\<open>Voblint_Analysis_Congruence.Congruence_Sound\<close> and used as it stands.

  What this section supplies is the other half: a routing policy.
  \<^const>\<open>cs_route\<close> computes a callee's context by pushing the call site onto the
  caller's string and truncating to a runtime bound \<open>k\<close>, and
  \<^locale>\<open>call_string_routed_context\<close> already discharges four of the six routing
  obligations for any compiled program and any domain.
\<close>

subsection \<open>The routed equation system and its executable solution\<close>

definition ccs_eqs ::
    "nat \<Rightarrow> (vname \<Rightarrow> bool) \<Rightarrow> (congruence exec_dg_st \<Rightarrow> bool) \<Rightarrow> proc_table \<Rightarrow> pname list
       \<Rightarrow> (pp \<times> call_string, call_string_gk,
            (congruence exec_dg_st lifted, congruence exec_dg_st lifted) dg_state) eqsT" where
  "ccs_eqs k gs empty_pred Pi ps =
     call_string_eqs_for k (cctx_spec gs empty_pred)
       (compile_prog Pi ps) (Lifted cinit_congruence_st)"

definition ccs_sol ::
    "nat \<Rightarrow> (vname \<Rightarrow> bool) \<Rightarrow> (congruence exec_dg_st \<Rightarrow> bool) \<Rightarrow> proc_table \<Rightarrow> pname list
       \<Rightarrow> (pp \<times> call_string) set
            \<times> (pp \<times> call_string + call_string_gk
                 \<Rightarrow> (congruence exec_dg_st lifted, congruence exec_dg_st lifted) dg_state)" where
  "ccs_sol k gs empty_pred Pi ps =
     TD_side_always_join_Interp_solve (ccs_eqs k gs empty_pred Pi ps)
       (cfg_exit (compile_prog Pi ps), [])"

definition ccs_terminates ::
    "nat \<Rightarrow> (vname \<Rightarrow> bool) \<Rightarrow> (congruence exec_dg_st \<Rightarrow> bool) \<Rightarrow> proc_table \<Rightarrow> pname list
       \<Rightarrow> bool" where
  "ccs_terminates k gs empty_pred Pi ps =
     TD_side_always_join_Interp.solve_dom TYPE(call_string_gk)
       TYPE((congruence exec_dg_st lifted, congruence exec_dg_st lifted) dg_state)
       (ccs_eqs k gs empty_pred Pi ps) (cfg_exit (compile_prog Pi ps), [])"

lemma ccs_terminates_via_solve_c:
  assumes "TD_side_always_join_Interp_solve_c (ccs_eqs k gs empty_pred Pi ps)
             (cfg_exit (compile_prog Pi ps), []) \<noteq> None"
  shows "ccs_terminates k gs empty_pred Pi ps"
  unfolding ccs_terminates_def
  by (rule TD_side_always_join_Interp.solve_dom_of_solve_c[OF assms])

lemma ccs_vars_finite:
  assumes "ccs_terminates k gs empty_pred Pi ps"
  shows "finite (fst (ccs_sol k gs empty_pred Pi ps))"
  using TD_side_always_join_Interp.finite_stabl_solve[
      OF assms[unfolded ccs_terminates_def]]
  unfolding ccs_sol_def TD_side_always_join_Interp_solve_def
  by simp

subsection \<open>Domain commute facts, at the call-string routed spec\<close>

text \<open>
  \<^locale>\<open>routed_domain_exec\<close> takes the routing functions as parameters, so this is
  the same interpretation Congruence's unit-context run makes, at a different
  instantiation. \<^const>\<open>cs_route\<close> reads only the call site and the incoming
  string, never the incoming abstract value, so the routing-agreement obligation
  is free. The extra \<open>assumption\<close> step is Congruence's liveness premise: its
  guard transfer is a backward filter, so its commutation holds on a live state.
\<close>

context
  fixes gs :: "vname \<Rightarrow> bool" and empty_pred :: "congruence exec_dg_st \<Rightarrow> bool" and k :: nat
  assumes exact: "\<And>s. empty_pred s = is_empty_state (fun_of_resolved_st_q_for gs s)"
begin

interpretation congruence_cs: routed_domain_exec
  gs empty_pred "congruence_tf_st_for gs" "congruence_enter_st_for gs"
  skip_congruence assign_congruence special_congruence branch_congruence
  body_congruence return_congruence "enter_congruence_ci_for gs" event_congruence
  Call_String_Context.Global Call_String_Context.Seed "cs_route k" "cs_route k"
  static_resolve static_resolve
  by unfold_locales
     (rule congruence_tf_st_for_commute[unfolded congruence_tf_abs_def], assumption,
      rule congruence_enter_st_for_commute, rule exact, simp,

      rule cs_route_indep_of_data, simp add: static_resolve_def)

lemmas congruence_cs_pp_st_gen = congruence_cs.pp_st

end

subsection \<open>The certified executable post-solution, generic per compiled program\<close>

context
  fixes gs :: "vname \<Rightarrow> bool" and empty_pred :: "congruence exec_dg_st \<Rightarrow> bool"
    and Pi :: proc_table and ps :: "pname list" and k :: nat
  assumes solves: "ccs_terminates k gs empty_pred Pi ps"
    and exact: "\<And>s. empty_pred s = is_empty_state (fun_of_resolved_st_q_for gs s)"
begin

lemma ccs_solve_dom:
  "TD_side_always_join_Interp.solve_dom TYPE(call_string_gk)
     TYPE((congruence exec_dg_st lifted, congruence exec_dg_st lifted) dg_state)
     (ccs_eqs k gs empty_pred Pi ps) (cfg_exit (compile_prog Pi ps), [])"
  using solves[unfolded ccs_terminates_def] .

lemma ccs_pp_st:
  "part_post_solution (ccs_eqs k gs empty_pred Pi ps) (cfg_exit (compile_prog Pi ps), [])
     (snd (ccs_sol k gs empty_pred Pi ps)) (fst (ccs_sol k gs empty_pred Pi ps))"
  using TD_side_always_join_Interp.partial_post_solution
          [OF ccs_solve_dom, of "fst (ccs_sol k gs empty_pred Pi ps)"
             "snd (ccs_sol k gs empty_pred Pi ps)"]
  unfolding ccs_sol_def by simp

text \<open>The solver's post-solution, for the unbuffered routed generator at the
  executable spec: the shape \<^locale>\<open>call_string_routed_context\<close> consumes directly.\<close>

theorem ccs_pp_routed:
  "part_post_solution
     (routed_node_rhs intra_predecessor_addr_list (\<lambda>_. Call_String_Context.Global)
        (cs_route k)
        (\<lambda>ctx' src a. dg_spec_edge_tree (cctx_spec gs empty_pred) a src
           (\<lambda>_. Call_String_Context.Global))
        (routed_call_tree (cctx_spec gs empty_pred) Call_String_Context.Global
           Call_String_Context.Seed (static_resolve (compile_prog Pi ps)) (\<lambda>d. d = Bot))
        (routed_entry_seed_tree Call_String_Context.Seed)
        (compile_prog Pi ps) Bot (Lifted cinit_congruence_st) Bot)
     (cfg_exit (compile_prog Pi ps), [])
     (snd (ccs_sol k gs empty_pred Pi ps)) (fst (ccs_sol k gs empty_pred Pi ps))"
  using ccs_pp_st
  unfolding ccs_eqs_def call_string_eqs_for_def compiled_routed_eqs_for_def cctx_spec_def
    bot_lifted_eq
  by (rule congruence_cs_pp_st_gen[OF exact])
end

subsection \<open>The analysis-level result at the call-string context\<close>

definition ccs_sg_st ::
    "nat \<Rightarrow> (vname \<Rightarrow> bool) \<Rightarrow> (congruence exec_dg_st \<Rightarrow> bool) \<Rightarrow> proc_table \<Rightarrow> pname list
       \<Rightarrow> pp \<times> call_string + call_string_gk \<Rightarrow> congruence exec_dg_st lifted" where
  "ccs_sg_st k gs empty_pred Pi ps =
     solved_local_reader (fst (ccs_sol k gs empty_pred Pi ps))
                         (snd (ccs_sol k gs empty_pred Pi ps))"

context
  fixes gs :: "vname \<Rightarrow> bool" and empty_pred :: "congruence exec_dg_st \<Rightarrow> bool"
    and Pi :: proc_table and ps :: "pname list" and k :: nat
  assumes solves: "ccs_terminates k gs empty_pred Pi ps"
    and exact: "\<And>s. empty_pred s = is_empty_state (fun_of_resolved_st_q_for gs s)"
    and entry_cov:
      "(cfg_entry (compile_prog Pi ps), []) \<in> fst (ccs_sol k gs empty_pred Pi ps)"
    and fwd_ok: "\<And>u a v ctx. (u, ctx) \<in> fst (ccs_sol k gs empty_pred Pi ps)
                   \<Longrightarrow> (u, a, v) \<in> intra (compile_prog Pi ps)
                   \<Longrightarrow> (v, ctx) \<in> fst (ccs_sol k gs empty_pred Pi ps)"
    and call_fwd_ok: "\<And>u ctx dst pars args p cont d.
        (u, ctx) \<in> fst (ccs_sol k gs empty_pred Pi ps)
        \<Longrightarrow> (u, CallEdge dst pars args, FunctionEntry p, cont) \<in> calls (compile_prog Pi ps)
        \<Longrightarrow> (FunctionEntry p, cs_route k u ctx d (CallEdge dst pars args))
              \<in> fst (ccs_sol k gs empty_pred Pi ps)"
    and comb_fwd_ok: "\<And>cl c1 dst pars args p cont.
        (cl, c1) \<in> fst (ccs_sol k gs empty_pred Pi ps)
        \<Longrightarrow> (cl, CallEdge dst pars args, FunctionEntry p, cont) \<in> calls (compile_prog Pi ps)
        \<Longrightarrow> (cont, c1) \<in> fst (ccs_sol k gs empty_pred Pi ps)"
begin

lemma ccs_cinit_le_cinit_congruence_st:
  "cinit_stores gs \<subseteq> cctx_gamma gs (Lifted cinit_congruence_st) Bot"
  by (auto simp: cctx_gamma_def cinit_stores_def gamma_state_def
                 fun_of_resolved_st_q_for_def fun_of_st_cinit_congruence_st_for)

interpretation ccs_dg_base: sound_dg_spec_core "cctx_spec gs empty_pred" "cctx_gamma gs" gs
  by (rule cctx_sound_exec[OF exact])

interpretation ccs_adapter: routed_analysis_sound
    "cctx_spec gs empty_pred" "cctx_gamma gs" gs
    "compile_prog Pi ps" Call_String_Context.Global "cs_route k"
    Bot "Lifted cinit_congruence_st" Bot
    "snd (ccs_sol k gs empty_pred Pi ps)" "fst (ccs_sol k gs empty_pred Pi ps)"
    "(cfg_exit (compile_prog Pi ps), [])"
    Call_String_Context.Seed "\<lambda>d. d = Bot" "call_context_rel_of_fun (cs_context k)"
    "map_lift (fun_of_resolved_st_q_for gs)" congruence_classify_check
proof (unfold_locales, goal_cases FinE PP SgCov SgUncov Fwd FinC CallsUnique SeedKey
    IsBotBot IsBotSound ResolveSound
    EnterCover EnterTotal CombFwd GammaRd ClProved ClRefuted VarsFin)
  case FinE show ?case using compile_prog_finite by auto
next
  case PP show ?case by (rule ccs_pp_routed[OF solves exact])
next
  case (SgCov v c)
  thus ?case by (simp add: cctx_gamma_def)
next
  case (SgUncov v c)
  thus ?case by simp
next
  case (Fwd u a v c)
  thus ?case by (rule fwd_ok)
next
  case FinC show ?case by (simp add: compile_prog_finite)
next
  case CallsUnique show ?case
    unfolding calls_source_unique_def using compile_prog_calls_source_unique by blast
next
  case (SeedKey p ctx) show ?case by simp
next
  case IsBotBot show ?case by simp
next
  case (IsBotSound d g') then show ?case by (simp add: cctx_gamma_def)
next
  case (ResolveSound u ctx dst pars args p cont s)
  thus ?case by (simp add: compile_prog_finite)
next
  case (EnterCover u ctx dst pars args p cont s ctx')
  let ?ci = "call_info_of (CallEdge dst pars args) p"
  let ?caller = "locals (snd (ccs_sol k gs empty_pred Pi ps) (Inl (u, ctx)))"
  have cov: "entry_pairs_cover
      (\<lambda>d. cctx_gamma gs d
             (globs (snd (ccs_sol k gs empty_pred Pi ps) (Inr Call_String_Context.Global))))
      s (call_enter gs (CallEdge dst pars args) s)
      [(?caller, transfer_lift empty_pred (congruence_enter_st_for gs ?ci) ?caller)]"
    using cctx_entry_cover_exec[OF exact EnterCover(3), where ci = ?ci] by simp
  have req: "cs_route k u ctx entry (CallEdge dst pars args) = ctx'"
    for entry :: "congruence exec_dg_st lifted"
    using EnterCover(4)[unfolded call_context_rel_of_fun_iff]
    by (simp add: cs_route_context_agree)
  show ?case
    unfolding cctx_spec_def dgs_enter_local_state_st_for_lifted
    using enter_runs_local_enter_transfer enter_deps_local_enter_transfer cov
          req call_fwd_ok[OF EnterCover(1,2)]
    by (fastforce simp: entry_pairs_cover_def cs_route_def)
next
  case (EnterTotal u ctx dst pars args p cont s)
  show ?case by simp
next
  case (CombFwd cl c1 dst pars args p cont)
  show ?case using CombFwd(1,2) by (rule comb_fwd_ok)
next
  case (GammaRd d g') show ?case by (simp add: cctx_gamma_def)
next
  case (ClProved c d s) thus ?case by (rule congruence_classify_check_proved)
next
  case (ClRefuted c d s) thus ?case by (rule congruence_classify_check_refuted)
next
  case VarsFin show ?case by (rule ccs_vars_finite[OF solves])
qed

theorem ccs_activation_collect_sound:
  "activation_collect gs (call_context_rel_of_fun (cs_context k)) [] (compile_prog Pi ps)
       (cinit_stores gs) v ctx
     \<subseteq> gamma_state_lift (map_lift (fun_of_resolved_st_q_for gs)
           (ccs_sg_st k gs empty_pred Pi ps (Inl (v, ctx))))"
  unfolding ccs_sg_st_def
  by (rule ccs_adapter.routed_activation_collect_sound
        [OF entry_cov ccs_cinit_le_cinit_congruence_st])

end

subsection \<open>Whole-program convenience layer\<close>

definition ccs_eqs_prog ::
    "nat \<Rightarrow> (vname \<Rightarrow> bool) \<Rightarrow> imp_prog
       \<Rightarrow> (pp \<times> call_string, call_string_gk,
            (congruence exec_dg_st lifted, congruence exec_dg_st lifted) dg_state) eqsT" where
  "ccs_eqs_prog k gs p =
     ccs_eqs k gs (resolved_st_q_is_bot_for (declared_global_vars p))
       (prog_table p) (prog_procs p)"

definition ccs_sol_prog ::
    "nat \<Rightarrow> (vname \<Rightarrow> bool) \<Rightarrow> imp_prog
       \<Rightarrow> (pp \<times> call_string) set
            \<times> (pp \<times> call_string + call_string_gk
                 \<Rightarrow> (congruence exec_dg_st lifted, congruence exec_dg_st lifted) dg_state)" where
  "ccs_sol_prog k gs p =
     ccs_sol k gs (resolved_st_q_is_bot_for (declared_global_vars p))
       (prog_table p) (prog_procs p)"

definition ccs_terminates_prog :: "nat \<Rightarrow> (vname \<Rightarrow> bool) \<Rightarrow> imp_prog \<Rightarrow> bool" where
  "ccs_terminates_prog k gs p =
     ccs_terminates k gs (resolved_st_q_is_bot_for (declared_global_vars p))
       (prog_table p) (prog_procs p)"

lemma ccs_terminates_prog_via_solve_c:
  assumes "TD_side_always_join_Interp_solve_c
             (ccs_eqs_prog k gs p)
             (cfg_exit (compile_prog (prog_table p) (prog_procs p)), []) \<noteq> None"
  shows "ccs_terminates_prog k gs p"
  using assms
  unfolding ccs_terminates_prog_def ccs_eqs_prog_def
  by (rule ccs_terminates_via_solve_c)

section \<open>Solved-result table at the call-string context\<close>

text \<open>
  The solved call-string D/G system, read as a
  \<^typ>\<open>(call_string, congruence abs_state) analysis_result\<close>. The covered-key set is
  the solver's own, never an enumerated theoretical context space.
\<close>

definition analyse_congruence_call_string_result_for ::
    "nat \<Rightarrow> (vname \<Rightarrow> bool) \<Rightarrow> imp_prog
       \<Rightarrow> (call_string, congruence abs_state) analysis_result" where
  "analyse_congruence_call_string_result_for k gs p =
     dg_result_for gs (declared_global_vars p) (ccs_sol_prog k gs p)"

definition analyse_congruence_call_string_result ::
    "nat \<Rightarrow> imp_prog \<Rightarrow> (call_string, congruence abs_state) analysis_result" where
  "analyse_congruence_call_string_result k p =
     analyse_congruence_call_string_result_for k (declared_global p) p"

section \<open>Contextual check report at the call-string context\<close>

definition ccs_check_projection ::
    "nat \<Rightarrow> imp_prog \<Rightarrow> (pp \<times> exp \<times> (call_string \<times> contextual_verdict) set) list" where
  "ccs_check_projection k p =
     classify_checks_ctx (prog_cfg p)
       (analyse_congruence_call_string_result_for k (declared_global p) p)
       congruence_classify_check"

definition ccs_verdict_report_prog ::
    "nat \<Rightarrow> imp_prog \<Rightarrow> (pp \<times> exp \<times> contextual_verdict) list" where
  "ccs_verdict_report_prog k p =
     map (\<lambda>(u, c, vs). (u, c, aggregate_verdicts (snd ` vs)))
       (ccs_check_projection k p)"

lemma ccs_verdict_report_prog_eq:
  "ccs_verdict_report_prog k p =
     classify_checks_verdicts (prog_cfg p)
       (analyse_congruence_call_string_result_for k (declared_global p) p)
       congruence_classify_check"
  unfolding ccs_verdict_report_prog_def ccs_check_projection_def
  by (rule classify_checks_verdicts_proj)

definition analyse_congruence_call_string_report ::
    "nat \<Rightarrow> imp_prog \<Rightarrow> (pp \<times> exp \<times> contextual_verdict) list" where
  "analyse_congruence_call_string_report k p = ccs_verdict_report_prog k p"


section \<open>Congruence at the routed spine, instantiated at the entry-state context\<close>

text \<open>
  The entry-state run, and the harder of Congruence's two context-sensitive runs:
  unlike a call string, this route reads the value it is handed, so the
  routing-agreement obligation is not free. It is discharged from
  \<^locale>\<open>routed_dg_domain_exec\<close>'s own three primitive commute facts, which
  \<^theory>\<open>Voblint_Analysis_Congruence.Congruence_Sound\<close> already establishes.

  A context is the list of abstract values the formals hold on entry, so two calls
  reaching a procedure with the same entered frame share a local unknown and any
  other pair does not. For Congruence this is a genuinely finer partition than for
  Parity: two calls passing \<open>4\<close> and \<open>6\<close> are separated here, where a parity context
  would merge them.

  The global keys are \<^typ>\<open>(unit, congruence list) routed_gk\<close>.
\<close>

subsection \<open>The routed equation system's own route, generic per compiled program\<close>

definition cctx_entry_route ::
    "(vname \<Rightarrow> bool) \<Rightarrow> (congruence exec_dg_st \<Rightarrow> bool) \<Rightarrow> congruence exec_dg_st lifted
       \<Rightarrow> call_action \<Rightarrow> congruence list" where
  "cctx_entry_route gs empty_pred d ca =
     (case ca of CallEdge dst pars args \<Rightarrow>
        formals_context pars (fun_of_resolved_st_q_for gs
          (case d of Bot \<Rightarrow> bot | Lifted d0 \<Rightarrow> d0)))"

definition cctx_entry_route_gen ::
    "(vname \<Rightarrow> bool) \<Rightarrow> (congruence exec_dg_st \<Rightarrow> bool) \<Rightarrow> pp \<Rightarrow> congruence list
       \<Rightarrow> congruence exec_dg_st lifted \<Rightarrow> call_action \<Rightarrow> congruence list" where
  "cctx_entry_route_gen gs empty_pred u ctx d ca = cctx_entry_route gs empty_pred d ca"

subsection \<open>The routed equation system and its executable solution\<close>

definition cctx_entry_eqs ::
    "(vname \<Rightarrow> bool) \<Rightarrow> (congruence exec_dg_st \<Rightarrow> bool) \<Rightarrow> proc_table \<Rightarrow> pname list
       \<Rightarrow> (pp \<times> congruence list, (unit, congruence list) routed_gk,
            (congruence exec_dg_st lifted, congruence exec_dg_st lifted) dg_state) eqsT" where
  "cctx_entry_eqs gs empty_pred Pi ps =
     compiled_routed_eqs_for (Analysis_Global ()) Activation_Seed
       (cctx_entry_route_gen gs empty_pred) (cctx_spec gs empty_pred)
       (compile_prog Pi ps) (Lifted cinit_congruence_st)"

definition cctx_entry_sol ::
    "(vname \<Rightarrow> bool) \<Rightarrow> (congruence exec_dg_st \<Rightarrow> bool) \<Rightarrow> proc_table \<Rightarrow> pname list
       \<Rightarrow> (pp \<times> congruence list) set
            \<times> (pp \<times> congruence list + (unit, congruence list) routed_gk
                 \<Rightarrow> (congruence exec_dg_st lifted, congruence exec_dg_st lifted) dg_state)" where
  "cctx_entry_sol gs empty_pred Pi ps =
     TD_side_always_join_Interp_solve (cctx_entry_eqs gs empty_pred Pi ps)
       (cfg_exit (compile_prog Pi ps), [])"

definition cctx_entry_terminates ::
    "(vname \<Rightarrow> bool) \<Rightarrow> (congruence exec_dg_st \<Rightarrow> bool) \<Rightarrow> proc_table \<Rightarrow> pname list
       \<Rightarrow> bool" where
  "cctx_entry_terminates gs empty_pred Pi ps =
     TD_side_always_join_Interp.solve_dom TYPE((unit, congruence list) routed_gk)
       TYPE((congruence exec_dg_st lifted, congruence exec_dg_st lifted) dg_state)
       (cctx_entry_eqs gs empty_pred Pi ps) (cfg_exit (compile_prog Pi ps), [])"

lemma cctx_entry_terminates_via_solve_c:
  assumes "TD_side_always_join_Interp_solve_c (cctx_entry_eqs gs empty_pred Pi ps)
             (cfg_exit (compile_prog Pi ps), []) \<noteq> None"
  shows "cctx_entry_terminates gs empty_pred Pi ps"
  unfolding cctx_entry_terminates_def
  by (rule TD_side_always_join_Interp.solve_dom_of_solve_c[OF assms])

text \<open>Finiteness of the entry-state key set, from the solver's own invariant. Nothing
  here depends on the context type, which is what makes the entry-state case available
  at all: its contexts are \<^typ>\<open>congruence list\<close> values, not a space any bound could
  enumerate.\<close>

lemma cctx_entry_vars_finite:
  assumes "cctx_entry_terminates gs empty_pred Pi ps"
  shows "finite (fst (cctx_entry_sol gs empty_pred Pi ps))"
  using TD_side_always_join_Interp.finite_stabl_solve[
      OF assms[unfolded cctx_entry_terminates_def]]
  unfolding cctx_entry_sol_def TD_side_always_join_Interp_solve_def
  by simp

subsection \<open>Route agreement: the one genuinely domain-specific commute fact\<close>

context
  fixes gs :: "vname \<Rightarrow> bool" and empty_pred :: "congruence exec_dg_st \<Rightarrow> bool"
  assumes exact: "\<And>s. empty_pred s = is_empty_state (fun_of_resolved_st_q_for gs s)"
begin

interpretation congruence_domain: routed_dg_domain_exec
  gs empty_pred "congruence_tf_st_for gs" "congruence_enter_st_for gs"
  skip_congruence assign_congruence special_congruence branch_congruence
  body_congruence return_congruence "enter_congruence_ci_for gs" event_congruence
  by unfold_locales
     (rule congruence_tf_st_for_commute[unfolded congruence_tf_abs_def], assumption,
      rule congruence_enter_st_for_commute, rule exact)

lemma cctx_entry_route_gen_eq_generic:
  "cctx_entry_route_gen gs empty_pred u ctx d ca
     = congruence_domain.entry_exec_route_gen u ctx d ca"
  unfolding cctx_entry_route_gen_def congruence_domain.entry_exec_route_gen_def
    cctx_entry_route_def congruence_domain.entry_exec_route_def
  by (rule refl)

lemma cctx_entry_route_gen_commute:
  "formals_route_lifted_gen u ctx (map_lift (fun_of_resolved_st_q_for gs) d) ca
     = cctx_entry_route_gen gs empty_pred u ctx d ca"
  unfolding cctx_entry_route_gen_eq_generic
  by (rule congruence_domain.entry_exec_route_gen_commute)

end

subsection \<open>Per-tree transport commutation\<close>

context
  fixes gs :: "vname \<Rightarrow> bool" and empty_pred :: "congruence exec_dg_st \<Rightarrow> bool"
  assumes exact: "\<And>s. empty_pred s = is_empty_state (fun_of_resolved_st_q_for gs s)"
begin

interpretation congruence_es: routed_domain_exec
  gs empty_pred "congruence_tf_st_for gs" "congruence_enter_st_for gs"
  skip_congruence assign_congruence special_congruence branch_congruence
  body_congruence return_congruence "enter_congruence_ci_for gs" event_congruence
  "Analysis_Global ()" Activation_Seed "cctx_entry_route_gen gs empty_pred"
  formals_route_lifted_gen
  static_resolve static_resolve
  by unfold_locales
     (rule congruence_tf_st_for_commute[unfolded congruence_tf_abs_def], assumption,
      rule congruence_enter_st_for_commute, rule exact, simp,

      rule cctx_entry_route_gen_commute[OF exact, symmetric],
      simp add: static_resolve_def)

lemmas congruence_es_pp_st_gen = congruence_es.pp_st

end

subsection \<open>The certified executable post-solution, generic per compiled program\<close>

context
  fixes gs :: "vname \<Rightarrow> bool" and empty_pred :: "congruence exec_dg_st \<Rightarrow> bool"
    and Pi :: proc_table and ps :: "pname list"
  assumes solves: "cctx_entry_terminates gs empty_pred Pi ps"
    and exact: "\<And>s. empty_pred s = is_empty_state (fun_of_resolved_st_q_for gs s)"
begin

lemma cctx_entry_solve_dom:
  "TD_side_always_join_Interp.solve_dom TYPE((unit, congruence list) routed_gk)
     TYPE((congruence exec_dg_st lifted, congruence exec_dg_st lifted) dg_state)
     (cctx_entry_eqs gs empty_pred Pi ps) (cfg_exit (compile_prog Pi ps), [])"
  using solves[unfolded cctx_entry_terminates_def] .

lemma cctx_entry_pp_st:
  "part_post_solution (cctx_entry_eqs gs empty_pred Pi ps)
     (cfg_exit (compile_prog Pi ps), [])
     (snd (cctx_entry_sol gs empty_pred Pi ps)) (fst (cctx_entry_sol gs empty_pred Pi ps))"
  using TD_side_always_join_Interp.partial_post_solution
          [OF cctx_entry_solve_dom, of "fst (cctx_entry_sol gs empty_pred Pi ps)"
             "snd (cctx_entry_sol gs empty_pred Pi ps)"]
  unfolding cctx_entry_sol_def by simp

theorem cctx_entry_pp_routed:
  "part_post_solution
     (routed_node_rhs intra_predecessor_addr_list (\<lambda>_. Analysis_Global ())
        (cctx_entry_route_gen gs empty_pred)
        (\<lambda>ctx' src a. dg_spec_edge_tree (cctx_spec gs empty_pred) a src
           (\<lambda>_. Analysis_Global ()))
        (routed_call_tree (cctx_spec gs empty_pred) (Analysis_Global ()) Activation_Seed
           (static_resolve (compile_prog Pi ps)) (\<lambda>d. d = Bot))
        (routed_entry_seed_tree Activation_Seed)
        (compile_prog Pi ps) Bot (Lifted cinit_congruence_st) Bot)
     (cfg_exit (compile_prog Pi ps), [])
     (snd (cctx_entry_sol gs empty_pred Pi ps)) (fst (cctx_entry_sol gs empty_pred Pi ps))"
  using cctx_entry_pp_st
  unfolding cctx_entry_eqs_def compiled_routed_eqs_for_def cctx_spec_def bot_lifted_eq
  by (rule congruence_es_pp_st_gen[OF exact])

end

section \<open>Activation-indexed collecting soundness, generic per compiled program\<close>

definition cctx_entry_sg_st ::
    "(vname \<Rightarrow> bool) \<Rightarrow> (congruence exec_dg_st \<Rightarrow> bool) \<Rightarrow> proc_table \<Rightarrow> pname list
       \<Rightarrow> pp \<times> congruence list + (unit, congruence list) routed_gk
       \<Rightarrow> congruence exec_dg_st lifted" where
  "cctx_entry_sg_st gs empty_pred Pi ps =
     solved_local_reader (fst (cctx_entry_sol gs empty_pred Pi ps))
                         (snd (cctx_entry_sol gs empty_pred Pi ps))"

context
  fixes gs :: "vname \<Rightarrow> bool" and empty_pred :: "congruence exec_dg_st \<Rightarrow> bool"
    and Pi :: proc_table and ps :: "pname list"
  assumes solves: "cctx_entry_terminates gs empty_pred Pi ps"
    and exact: "\<And>s. empty_pred s = is_empty_state (fun_of_resolved_st_q_for gs s)"
    and entry_cov:
      "(cfg_entry (compile_prog Pi ps), []) \<in> fst (cctx_entry_sol gs empty_pred Pi ps)"
    and fwd_ok: "\<And>u a v ctx. (u, ctx) \<in> fst (cctx_entry_sol gs empty_pred Pi ps)
                   \<Longrightarrow> (u, a, v) \<in> intra (compile_prog Pi ps)
                   \<Longrightarrow> (v, ctx) \<in> fst (cctx_entry_sol gs empty_pred Pi ps)"
    and call_fwd_ok: "\<And>u ctx dst pars args p cont.
        (u, ctx) \<in> fst (cctx_entry_sol gs empty_pred Pi ps)
        \<Longrightarrow> (u, CallEdge dst pars args, FunctionEntry p, cont) \<in> calls (compile_prog Pi ps)
        \<Longrightarrow> (FunctionEntry p,
               cctx_entry_route_gen gs empty_pred u ctx
                 (transfer_lift empty_pred
                    (congruence_enter_st_for gs (call_info_of (CallEdge dst pars args) p))
                    (locals (snd (cctx_entry_sol gs empty_pred Pi ps) (Inl (u, ctx)))))
                 (CallEdge dst pars args))
             \<in> fst (cctx_entry_sol gs empty_pred Pi ps)"
    and comb_fwd_ok: "\<And>cl c1 dst pars args p cont.
        (cl, c1) \<in> fst (cctx_entry_sol gs empty_pred Pi ps)
        \<Longrightarrow> (cl, CallEdge dst pars args, FunctionEntry p, cont) \<in> calls (compile_prog Pi ps)
        \<Longrightarrow> (cont, c1) \<in> fst (cctx_entry_sol gs empty_pred Pi ps)"
begin

subsection \<open>The solver's table as the solved system\<close>

interpretation cctx_entry_compiled: compiled_cfg Pi ps "compile_prog Pi ps"
  by (unfold_locales; simp add: compile_prog_finite)

lemmas cctx_entry_fin = cctx_entry_compiled.finite_intra
lemmas cctx_entry_finC = cctx_entry_compiled.finite_calls

lemma cctx_entry_sg_st_covered:
  "(v, ctx) \<in> fst (cctx_entry_sol gs empty_pred Pi ps)
   \<Longrightarrow> cctx_entry_sg_st gs empty_pred Pi ps (Inl (v, ctx))
         = locals (snd (cctx_entry_sol gs empty_pred Pi ps) (Inl (v, ctx)))"
  by (simp add: cctx_entry_sg_st_def)

lemma cctx_entry_sg_st_uncovered_empty:
  "(v, ctx) \<notin> fst (cctx_entry_sol gs empty_pred Pi ps)
     \<Longrightarrow> gamma_state_lift (map_lift (fun_of_resolved_st_q_for gs)
           (cctx_entry_sg_st gs empty_pred Pi ps (Inl (v, ctx)))) = {}"
  by (simp add: cctx_entry_sg_st_def)

subsection \<open>Instantiating the generic routed-context locale\<close>

interpretation cctx_entry_dg_base: sound_dg_spec_core
    "cctx_spec gs empty_pred" "cctx_gamma gs" gs
  by (rule cctx_sound_exec[OF exact])

interpretation cctx_entry_routed: pure_entry_routed_context "cctx_spec gs empty_pred"
    "cctx_gamma gs" gs Pi ps "Analysis_Global ()" "cctx_entry_route_gen gs empty_pred"
    Bot "Lifted cinit_congruence_st" Bot
    "snd (cctx_entry_sol gs empty_pred Pi ps)" "fst (cctx_entry_sol gs empty_pred Pi ps)"
    "(cfg_exit (compile_prog Pi ps), [])" "cctx_entry_sg_st gs empty_pred Pi ps"
    Activation_Seed
    "\<lambda>d. d = Bot" "\<lambda>m. gamma_state_lift (map_lift (fun_of_resolved_st_q_for gs) m)"
    "\<lambda>ci d. [(d, transfer_lift empty_pred (congruence_enter_st_for gs ci) d)]"
proof (unfold_locales, goal_cases FinE PP SgCov SgUncov Fwd SeedNe
    IsBotBot IsBotSound EnterPure EnterCover CallFwd CombFwd)
  case FinE show ?case by (rule cctx_entry_fin)
next
  case PP show ?case by (rule cctx_entry_pp_routed[OF solves exact])
next
  case (SgCov v ctx) then show ?case
    by (simp add: cctx_entry_sg_st_def cctx_gamma_def)
next
  case (SgUncov v ctx) then show ?case by (rule cctx_entry_sg_st_uncovered_empty)
next
  case (Fwd u a v ctx) then show ?case by (rule fwd_ok)
next
  case (SeedNe p ctx) show ?case by simp
next
  case IsBotBot show ?case by simp
next
  case (IsBotSound d gv) then show ?case by (simp add: cctx_gamma_def)
next
  case (EnterPure ci) show ?case
    unfolding cctx_spec_def dgs_enter_local_state_st_for_lifted by (rule refl)
next
  case (EnterCover u ctx dst pars args p cont s)
  show ?case
    using cctx_entry_cover_exec[OF exact EnterCover(3),
        where ci = "call_info_of (CallEdge dst pars args) p"]
    by simp
next
  case (CallFwd u ctx dst pars args p cont cont' entry)
  then have "entry = transfer_lift empty_pred
               (congruence_enter_st_for gs (call_info_of (CallEdge dst pars args) p))
               (locals (snd (cctx_entry_sol gs empty_pred Pi ps) (Inl (u, ctx))))"
    by simp
  with CallFwd(1,2) show ?case using call_fwd_ok by simp
next
  case (CombFwd cl c1 dst pars args p cont)
  show ?case using CombFwd(1,2) by (rule comb_fwd_ok)
qed

subsection \<open>Activation-indexed collecting soundness\<close>

lemma cctx_entry_cinit_le_cinit_congruence_st:
  "cinit_stores gs \<subseteq> cctx_gamma gs (Lifted cinit_congruence_st) Bot"
  by (auto simp: cctx_gamma_def cinit_stores_def gamma_state_def
                 fun_of_resolved_st_q_for_def fun_of_st_cinit_congruence_st_for)

text \<open>The context relation the routed table induces: a concrete call is admitted at
  every context some covering alternative of the entry answer routes to.\<close>

abbreviation cctx_entry_context_rel :: "congruence list call_context_rel" where
  "cctx_entry_context_rel \<equiv> cctx_entry_routed.entry_context_rel"

lemmas cctx_entry_routed_context_call = cctx_entry_routed.routed_context_call
lemmas cctx_entry_routed_context_comb = cctx_entry_routed.routed_context_comb

interpretation cctx_entry_adapter: routed_analysis_sound
    "cctx_spec gs empty_pred" "cctx_gamma gs" gs
    "compile_prog Pi ps" "Analysis_Global ()" "cctx_entry_route_gen gs empty_pred"
    Bot "Lifted cinit_congruence_st" Bot
    "snd (cctx_entry_sol gs empty_pred Pi ps)" "fst (cctx_entry_sol gs empty_pred Pi ps)"
    "(cfg_exit (compile_prog Pi ps), [])"
    Activation_Seed "\<lambda>d. d = Bot" cctx_entry_context_rel
    "map_lift (fun_of_resolved_st_q_for gs)" congruence_classify_check
proof (unfold_locales, goal_cases FinE PP SgCov SgUncov Fwd FinC CallsUnique SeedKey
    IsBotBot IsBotSound ResolveSound
    EnterCover EnterTotal CombFwd GammaRd ClProved ClRefuted VarsFin)
  case FinE show ?case by (rule cctx_entry_fin)
next
  case PP show ?case by (rule cctx_entry_pp_routed[OF solves exact])
next
  case (SgCov v c)
  thus ?case by (simp add: cctx_gamma_def)
next
  case (SgUncov v c)
  thus ?case by simp
next
  case (Fwd u a v c)
  thus ?case by (rule fwd_ok)
next
  case FinC show ?case by (rule cctx_entry_finC)
next
  case CallsUnique show ?case
    unfolding calls_source_unique_def using compile_prog_calls_source_unique by blast
next
  case (SeedKey p ctx) show ?case by simp
next
  case IsBotBot show ?case by simp
next
  case (IsBotSound d g') then show ?case by (simp add: cctx_gamma_def)
next
  case (ResolveSound u ctx dst pars args p cont s)
  thus ?case by (simp add: static_resolve_iff[OF cctx_entry_finC])
next
  case (EnterCover u ctx dst pars args p cont s ctx')
  show ?case
    using cctx_entry_routed.routed.routed_entry_cover[OF EnterCover(1,2,3,4)] .
next
  case (EnterTotal u ctx dst pars args p cont s)
  show ?case
    using cctx_entry_routed.routed.routed_entry_total[OF EnterTotal(1,2,3)] .
next
  case (CombFwd cl c1 dst pars args p cont)
  show ?case using CombFwd(1,2) by (rule comb_fwd_ok)
next
  case (GammaRd d g')
  show ?case by (simp add: cctx_gamma_def)
next
  case (ClProved c d s)
  thus ?case by (rule congruence_classify_check_proved)
next
  case (ClRefuted c d s)
  thus ?case by (rule congruence_classify_check_refuted)
next
  case VarsFin show ?case by (rule cctx_entry_vars_finite[OF solves])
qed

theorem cctx_entry_activation_collect_sound:
  "activation_collect gs cctx_entry_context_rel [] (compile_prog Pi ps) (cinit_stores gs) v ctx
     \<subseteq> gamma_state_lift (map_lift (fun_of_resolved_st_q_for gs)
           (cctx_entry_sg_st gs empty_pred Pi ps (Inl (v, ctx))))"
  unfolding cctx_entry_sg_st_def
  by (rule cctx_entry_adapter.routed_activation_collect_sound
        [OF entry_cov cctx_entry_cinit_le_cinit_congruence_st])
end

subsection \<open>Whole-program convenience layer\<close>

definition cctx_entry_eqs_prog ::
    "(vname \<Rightarrow> bool) \<Rightarrow> imp_prog
       \<Rightarrow> (pp \<times> congruence list, (unit, congruence list) routed_gk,
            (congruence exec_dg_st lifted, congruence exec_dg_st lifted) dg_state) eqsT" where
  "cctx_entry_eqs_prog gs p =
     cctx_entry_eqs gs (resolved_st_q_is_bot_for (declared_global_vars p))
       (prog_table p) (prog_procs p)"

definition cctx_entry_sol_prog ::
    "(vname \<Rightarrow> bool) \<Rightarrow> imp_prog
       \<Rightarrow> (pp \<times> congruence list) set
            \<times> (pp \<times> congruence list + (unit, congruence list) routed_gk
                 \<Rightarrow> (congruence exec_dg_st lifted, congruence exec_dg_st lifted) dg_state)" where
  "cctx_entry_sol_prog gs p =
     cctx_entry_sol gs (resolved_st_q_is_bot_for (declared_global_vars p))
       (prog_table p) (prog_procs p)"

definition cctx_entry_terminates_prog :: "(vname \<Rightarrow> bool) \<Rightarrow> imp_prog \<Rightarrow> bool" where
  "cctx_entry_terminates_prog gs p =
     cctx_entry_terminates gs (resolved_st_q_is_bot_for (declared_global_vars p))
       (prog_table p) (prog_procs p)"

lemma cctx_entry_terminates_prog_via_solve_c:
  assumes "TD_side_always_join_Interp_solve_c
             (cctx_entry_eqs_prog gs p)
             (cfg_exit (compile_prog (prog_table p) (prog_procs p)), []) \<noteq> None"
  shows "cctx_entry_terminates_prog gs p"
  using assms
  unfolding cctx_entry_terminates_prog_def cctx_entry_eqs_prog_def
  by (rule cctx_entry_terminates_via_solve_c)

section \<open>Solved-result table at the entry-state context\<close>

definition analyse_congruence_entry_state_result_for ::
    "(vname \<Rightarrow> bool) \<Rightarrow> imp_prog
       \<Rightarrow> (congruence list, congruence abs_state) analysis_result" where
  "analyse_congruence_entry_state_result_for gs p =
     dg_result_for gs (declared_global_vars p) (cctx_entry_sol_prog gs p)"

definition analyse_congruence_entry_state_result ::
    "imp_prog \<Rightarrow> (congruence list, congruence abs_state) analysis_result" where
  "analyse_congruence_entry_state_result p =
     analyse_congruence_entry_state_result_for (declared_global p) p"

section \<open>Contextual check report at the entry-state context\<close>

definition cctx_entry_check_projection ::
    "imp_prog \<Rightarrow> (pp \<times> exp \<times> (congruence list \<times> contextual_verdict) set) list" where
  "cctx_entry_check_projection p =
     classify_checks_ctx (prog_cfg p)
       (analyse_congruence_entry_state_result_for (declared_global p) p)
       congruence_classify_check"

definition cctx_entry_verdict_report_prog ::
    "imp_prog \<Rightarrow> (pp \<times> exp \<times> contextual_verdict) list" where
  "cctx_entry_verdict_report_prog p =
     map (\<lambda>(u, c, vs). (u, c, aggregate_verdicts (snd ` vs)))
       (cctx_entry_check_projection p)"

lemma cctx_entry_verdict_report_prog_eq:
  "cctx_entry_verdict_report_prog p =
     classify_checks_verdicts (prog_cfg p)
       (analyse_congruence_entry_state_result_for (declared_global p) p)
       congruence_classify_check"
  unfolding cctx_entry_verdict_report_prog_def cctx_entry_check_projection_def
  by (rule classify_checks_verdicts_proj)

definition analyse_congruence_entry_state_report ::
    "imp_prog \<Rightarrow> (pp \<times> exp \<times> contextual_verdict) list" where
  "analyse_congruence_entry_state_report p = cctx_entry_verdict_report_prog p"

end
