theory Sign_Ctx_Entry_State_Sound
  imports
    "Voblint_Analysis.Sign_Sound"
    "Voblint_Analysis.Sign_Checks"
    "Voblint_Core.Routed_Analysis_Sound"
    Entry_State_Routed_Context
begin

section \<open>Sign at the routed spine, instantiated at the entry-state context\<close>

text \<open>
  The entry-state instance of the Sign analysis package in
  \<^theory>\<open>Voblint_Analysis.Sign_Sound\<close>, and the second architecture-milestone acceptance test
  after \<open>Sign_Ctx_Call_String_Sound\<close>: same \<^const>\<open>sctx_spec\<close>/\<^const>\<open>sctx_abs_spec\<close>  D/G specification and the same domain-commute facts Sign already interprets
  (\<^locale>\<open>routed_dg_domain_exec\<close>, \<^theory>\<open>Voblint_Exec.DG_Base_Exec\<close>) -- nothing here
  re-derives them. The routing policy is Interval's own entry-state construction
  (\<open>entry_exec_route_gen\<close>/\<^const>\<open>formals_route_lifted_gen\<close>,
  \<^theory>\<open>Voblint_Exec.DG_Base_Exec\<close>/\<^theory>\<open>Voblint_Core.Routed_Context\<close>), already
  generalized in a domain -- unlike \<open>cs_route\<close>, this route genuinely depends on
  its caller-state argument (the entered callee frame), which is exactly the "small
  additional domain capability" the routed-domain milestone anticipated for EntryState;
  it needed only \<open>routed_dg_domain_exec\<close>'s own three primitive commute facts, no new
  Sign-domain mathematics. \<^locale>\<open>entry_state_routed_context\<close>
  (\<^theory>\<open>Voblint_Analysis.Entry_State_Routed_Context\<close>) is the generic context-side counterpart,
  discharging \<open>FinC\<close>/\<open>RouteAgree\<close>/\<open>EnterAgree\<close> once and for all instances.

  Unlike Sign's own routed-unit-context and call-string instances, this development goes
  one section further, to activation-indexed collecting soundness -- matching Interval's
  own EntryState pipeline's scope exactly (Interval's own CallString pipeline stops at the
  executable result/report table, the same place \<open>Sign_Ctx_Call_String_Sound\<close> stops).
\<close>

subsection \<open>Global key: real globals vs callee-entry seed slots\<close>

datatype gk = Global | Seed (seed_pp: pp) (seed_ctx: "sign list")

subsection \<open>The routed equation system's own route, generic per compiled program\<close>

text \<open>
  Sign's own executable-carrier route, mirroring Interval's \<open>entry_state_route\<close>/
  \<open>entry_state_route_gen\<close> (\<open>Interval_Ctx_Entry_State_Sound\<close>) exactly, at
  Sign's own \<open>sign_enter_st_for\<close> instead of Interval's \<open>ivl_enter_st_for\<close> -- this is
  precisely \<^locale>\<open>routed_dg_domain_exec\<close>'s own \<open>entry_exec_route\<close>/
  \<open>entry_exec_route_gen\<close> (\<^theory>\<open>Voblint_Exec.DG_Base_Exec\<close>), restated here as
  unconditional top-level definitions (rather than reached through an interpretation) so
  the equation-system definitions below need no \<open>exact\<close> premise to be stated, matching
  every other routed instance's convention. The routed generator enters the callee
  frame before it routes, so the route itself only projects the formals out of the
  state it is handed.
\<close>

definition sctx_entry_route ::
    "(vname \<Rightarrow> bool) \<Rightarrow> (sign exec_dg_st \<Rightarrow> bool) \<Rightarrow> sign exec_dg_st lifted \<Rightarrow> call_action \<Rightarrow> sign list" where
  "sctx_entry_route gs empty_pred d ca =
     (case ca of CallEdge dst pars args \<Rightarrow>
        formals_context pars (fun_of_resolved_st_q_for gs
          (case d of Bot \<Rightarrow> bot | Lifted d0 \<Rightarrow> d0)))"

definition sctx_entry_route_gen ::
    "(vname \<Rightarrow> bool) \<Rightarrow> (sign exec_dg_st \<Rightarrow> bool) \<Rightarrow> pp \<Rightarrow> sign list \<Rightarrow> sign exec_dg_st lifted \<Rightarrow> call_action \<Rightarrow> sign list" where
  "sctx_entry_route_gen gs empty_pred u ctx d ca = sctx_entry_route gs empty_pred d ca"

subsection \<open>The routed equation system and its executable solution\<close>

definition sctx_entry_eqs ::
    "(vname \<Rightarrow> bool) \<Rightarrow> (sign exec_dg_st \<Rightarrow> bool) \<Rightarrow> proc_table \<Rightarrow> pname list \<Rightarrow> (pp \<times> sign list, gk, (sign exec_dg_st lifted, sign exec_dg_st lifted) dg_state) eqsT" where
  "sctx_entry_eqs gs empty_pred Pi ps =
     side_cfg_T_eff_keyed_seed_dg_buffered intra_predecessor_addr_list (\<lambda>_. Global)
       (sctx_entry_route_gen gs empty_pred)
       (\<lambda>ctx' src a. dg_spec_edge_tree (sctx_spec gs empty_pred) a src (\<lambda>_. Global))
       (routed_cmb_g (sctx_spec gs empty_pred) Global Seed
          (static_resolve (compile_prog Pi ps)))
       (routed_extra_g Seed Global)
       (compile_prog Pi ps) Bot (Lifted cinit_sign_st) Bot"

definition sctx_entry_sol ::
    "(vname \<Rightarrow> bool) \<Rightarrow> (sign exec_dg_st \<Rightarrow> bool) \<Rightarrow> proc_table \<Rightarrow> pname list \<Rightarrow> (pp \<times> sign list) set \<times> (pp \<times> sign list + gk \<Rightarrow> (sign exec_dg_st lifted, sign exec_dg_st lifted) dg_state)" where
  "sctx_entry_sol gs empty_pred Pi ps =
     TD_side_always_join_Interp_solve (sctx_entry_eqs gs empty_pred Pi ps)
       (cfg_exit (compile_prog Pi ps), [])"

definition sctx_entry_terminates ::
    "(vname \<Rightarrow> bool) \<Rightarrow> (sign exec_dg_st \<Rightarrow> bool) \<Rightarrow> proc_table \<Rightarrow> pname list \<Rightarrow> bool" where
  "sctx_entry_terminates gs empty_pred Pi ps =
     TD_side_always_join_Interp.solve_dom TYPE(gk) TYPE((sign exec_dg_st lifted, sign exec_dg_st lifted) dg_state)
       (sctx_entry_eqs gs empty_pred Pi ps) (cfg_exit (compile_prog Pi ps), [])"

lemma sctx_entry_terminates_via_solve_c:
  assumes "TD_side_always_join_Interp_solve_c (sctx_entry_eqs gs empty_pred Pi ps)
             (cfg_exit (compile_prog Pi ps), []) \<noteq> None"
  shows "sctx_entry_terminates gs empty_pred Pi ps"
  unfolding sctx_entry_terminates_def
  by (rule TD_side_always_join_Interp.solve_dom_of_solve_c[OF assms])

subsection \<open>Route agreement: the one genuinely domain-specific commute fact\<close>

context
  fixes gs :: "vname \<Rightarrow> bool" and empty_pred :: "sign exec_dg_st \<Rightarrow> bool"
  assumes exact: "\<And>s. empty_pred s = is_empty_state (fun_of_resolved_st_q_for gs s)"
begin

interpretation sign_domain: routed_dg_domain_exec
  gs empty_pred "sign_tf_st_for gs" "sign_enter_st_for gs" "sign_tf_for gs"
  by unfold_locales (rule sign_tf_st_for_commute, rule sign_enter_st_for_commute, rule exact)

lemma sctx_entry_route_gen_eq_generic:
  "sctx_entry_route_gen gs empty_pred u ctx d ca = sign_domain.entry_exec_route_gen u ctx d ca"
  unfolding sctx_entry_route_gen_def sign_domain.entry_exec_route_gen_def
    sctx_entry_route_def sign_domain.entry_exec_route_def
  by (rule refl)

lemma sctx_entry_route_gen_commute:
  "formals_route_lifted_gen u ctx (map_lift (fun_of_resolved_st_q_for gs) d) ca
     = sctx_entry_route_gen gs empty_pred u ctx d ca"
  unfolding sctx_entry_route_gen_eq_generic
  by (rule sign_domain.entry_exec_route_gen_commute)

end

subsection \<open>Per-tree transport commutation\<close>

text \<open>
  The same interpretation Sign's unit-context instance makes, at the entry-state
  routing policy. Here the routing-agreement obligation is not free --- the route reads
  the entered state --- but it is exactly the fact just proved, and
  \<^locale>\<open>routed_domain_exec\<close> takes it as a parameter, so switching context policy stays
  a different instantiation of one derivation rather than a second one.
\<close>

context
  fixes gs :: "vname \<Rightarrow> bool" and empty_pred :: "sign exec_dg_st \<Rightarrow> bool"
  assumes exact: "\<And>s. empty_pred s = is_empty_state (fun_of_resolved_st_q_for gs s)"
begin

interpretation sign_es: routed_domain_exec
  gs empty_pred "sign_tf_st_for gs" "sign_enter_st_for gs" "sign_tf_for gs"
  Global Seed "sctx_entry_route_gen gs empty_pred"
  formals_route_lifted_gen
  static_resolve static_resolve
  by unfold_locales
     (rule sign_tf_st_for_commute, rule sign_enter_st_for_commute, rule exact, simp,
      rule sctx_entry_route_gen_commute[OF exact, symmetric],
      simp add: static_resolve_def)

lemmas sign_es_pp_st_gen = sign_es.pp_st

end

subsection \<open>The certified executable post-solution, generic per compiled program\<close>

context
  fixes gs :: "vname \<Rightarrow> bool" and empty_pred :: "sign exec_dg_st \<Rightarrow> bool"
    and Pi :: proc_table and ps :: "pname list"
  assumes solves: "sctx_entry_terminates gs empty_pred Pi ps"
    and exact: "\<And>s. empty_pred s = is_empty_state (fun_of_resolved_st_q_for gs s)"
begin

lemma sctx_entry_solve_dom:
  "TD_side_always_join_Interp.solve_dom TYPE(gk) TYPE((sign exec_dg_st lifted, sign exec_dg_st lifted) dg_state)
     (sctx_entry_eqs gs empty_pred Pi ps) (cfg_exit (compile_prog Pi ps), [])"
  using solves[unfolded sctx_entry_terminates_def] .

lemma sctx_entry_pp_st:
  "part_post_solution (sctx_entry_eqs gs empty_pred Pi ps) (cfg_exit (compile_prog Pi ps), [])
     (snd (sctx_entry_sol gs empty_pred Pi ps)) (fst (sctx_entry_sol gs empty_pred Pi ps))"
  using TD_side_always_join_Interp.partial_post_solution
          [OF sctx_entry_solve_dom, of "fst (sctx_entry_sol gs empty_pred Pi ps)"
             "snd (sctx_entry_sol gs empty_pred Pi ps)"]
  unfolding sctx_entry_sol_def by simp

text \<open>The solver's post-solution, for the unbuffered routed generator at the executable
  spec and Sign's executable route: the shape \<^locale>\<open>dg_ctx_activation_base\<close> consumes.\<close>

theorem sctx_entry_pp_routed:
  "part_post_solution
     (side_cfg_T_eff_keyed_seed_dg intra_predecessor_addr_list (\<lambda>_. Global)
        (sctx_entry_route_gen gs empty_pred)
        (\<lambda>ctx' src a. dg_spec_edge_tree (sctx_spec gs empty_pred) a src (\<lambda>_. Global))
        (routed_cmb_g (sctx_spec gs empty_pred) Global Seed (static_resolve (compile_prog Pi ps)))
        (routed_extra_g Seed Global)
        (compile_prog Pi ps) Bot (Lifted cinit_sign_st) Bot)
     (cfg_exit (compile_prog Pi ps), [])
     (snd (sctx_entry_sol gs empty_pred Pi ps)) (fst (sctx_entry_sol gs empty_pred Pi ps))"
  using sctx_entry_pp_st unfolding sctx_entry_eqs_def sctx_spec_def
  by (rule sign_es_pp_st_gen[OF exact])

end

section \<open>Activation-indexed collecting soundness, generic per compiled program\<close>

text \<open>
  The routed spine is interpreted at Sign's executable carrier and fed the solver's own
  table, as \<open>Sign_Ctx_None_Sound\<close> does at the unit context: a local unknown concretizes
  to \<^const>\<open>gamma_state_lift\<close> of its readback (\<^const>\<open>sctx_gamma\<close>), the covered reader
  \<open>sctx_entry_sg_st\<close> hands the table's local slot through unchanged, and the route is
  Sign's own executable \<^const>\<open>sctx_entry_route_gen\<close>.
\<close>

definition sctx_entry_sg_st ::
    "(vname \<Rightarrow> bool) \<Rightarrow> (sign exec_dg_st \<Rightarrow> bool) \<Rightarrow> proc_table \<Rightarrow> pname list
       \<Rightarrow> pp \<times> sign list + gk \<Rightarrow> sign exec_dg_st lifted" where
  "sctx_entry_sg_st gs empty_pred Pi ps =
     solved_local_reader (fst (sctx_entry_sol gs empty_pred Pi ps))
                         (snd (sctx_entry_sol gs empty_pred Pi ps))"

context
  fixes gs :: "vname \<Rightarrow> bool" and empty_pred :: "sign exec_dg_st \<Rightarrow> bool"
    and Pi :: proc_table and ps :: "pname list"
  assumes solves: "sctx_entry_terminates gs empty_pred Pi ps"
    and exact: "\<And>s. empty_pred s = is_empty_state (fun_of_resolved_st_q_for gs s)"
    and entry_cov: "(cfg_entry (compile_prog Pi ps), []) \<in> fst (sctx_entry_sol gs empty_pred Pi ps)"
    and fwd_ok: "\<And>u a v ctx. (u, ctx) \<in> fst (sctx_entry_sol gs empty_pred Pi ps)
                   \<Longrightarrow> (u, a, v) \<in> intra (compile_prog Pi ps)
                   \<Longrightarrow> (v, ctx) \<in> fst (sctx_entry_sol gs empty_pred Pi ps)"
    and call_fwd_ok: "\<And>u ctx dst pars args p cont.
        (u, ctx) \<in> fst (sctx_entry_sol gs empty_pred Pi ps)
        \<Longrightarrow> (u, CallEdge dst pars args, FunctionEntry p, cont) \<in> calls (compile_prog Pi ps)
        \<Longrightarrow> (FunctionEntry p,
               sctx_entry_route_gen gs empty_pred u ctx
                 (entered (sctx_spec gs empty_pred) Global
                    (snd (sctx_entry_sol gs empty_pred Pi ps))
                    (call_info_of (CallEdge dst pars args) p) (Inl (u, ctx)))
                 (CallEdge dst pars args))
             \<in> fst (sctx_entry_sol gs empty_pred Pi ps)"
    and comb_fwd_ok: "\<And>cl c1 dst pars args p cont.
        (cl, c1) \<in> fst (sctx_entry_sol gs empty_pred Pi ps)
        \<Longrightarrow> (cl, CallEdge dst pars args, FunctionEntry p, cont) \<in> calls (compile_prog Pi ps)
        \<Longrightarrow> (cont, c1) \<in> fst (sctx_entry_sol gs empty_pred Pi ps)"
begin

subsection \<open>The solver's table as the solved system\<close>

interpretation sctx_entry_compiled: compiled_cfg Pi ps "compile_prog Pi ps"
  by (unfold_locales; simp add: compile_prog_finite)

lemmas sctx_entry_fin = sctx_entry_compiled.finite_intra
lemmas sctx_entry_finC = sctx_entry_compiled.finite_calls

lemma sctx_entry_sg_st_covered:
  "(v, ctx) \<in> fst (sctx_entry_sol gs empty_pred Pi ps)
   \<Longrightarrow> sctx_entry_sg_st gs empty_pred Pi ps (Inl (v, ctx))
         = locals (snd (sctx_entry_sol gs empty_pred Pi ps) (Inl (v, ctx)))"
  by (simp add: sctx_entry_sg_st_def)

lemma sctx_entry_sg_st_uncovered_empty:
  "(v, ctx) \<notin> fst (sctx_entry_sol gs empty_pred Pi ps)
     \<Longrightarrow> gamma_state_lift (map_lift (fun_of_resolved_st_q_for gs)
           (sctx_entry_sg_st gs empty_pred Pi ps (Inl (v, ctx)))) = {}"
  by (simp add: sctx_entry_sg_st_def)

subsection \<open>Instantiating the generic routed-context locale\<close>

interpretation sctx_entry_dg_base: sound_dg_spec "sctx_spec gs empty_pred" "sctx_gamma gs" gs
  by (rule sctx_sound_exec[OF exact])


interpretation sctx_entry_routed: entry_state_routed_context "sctx_spec gs empty_pred"
    "sctx_gamma gs" gs Pi ps Global "sctx_entry_route_gen gs empty_pred"
    Bot "Lifted cinit_sign_st" Bot
    "snd (sctx_entry_sol gs empty_pred Pi ps)" "fst (sctx_entry_sol gs empty_pred Pi ps)"
    "(cfg_exit (compile_prog Pi ps), [])" "sctx_entry_sg_st gs empty_pred Pi ps" Seed
    "\<lambda>m. gamma_state_lift (map_lift (fun_of_resolved_st_q_for gs) m)"
proof (unfold_locales, goal_cases FinE PP SgCov SgUncov Fwd SeedNe CallFwd CombFwd)
  case FinE show ?case by (rule sctx_entry_fin)
next
  case PP show ?case by (rule sctx_entry_pp_routed[OF solves exact])
next
  case (SgCov v ctx) then show ?case
    by (simp add: sctx_entry_sg_st_def sctx_gamma_def)
next
  case (SgUncov v ctx) then show ?case by (rule sctx_entry_sg_st_uncovered_empty)
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

lemma sctx_entry_cinit_le_cinit_sign_st:
  "cinit_stores gs \<subseteq> sctx_gamma gs (Lifted cinit_sign_st) Bot"
  by (auto simp: sctx_gamma_def cinit_stores_def gamma_state_def fun_of_resolved_st_q_for_def
                 fun_of_st_cinit_sign_st_for)

text \<open>The trace-semantic context function the routed table induces: at a call site it
  routes the entered store's abstraction, read from the solver's own table.\<close>

definition sctx_entry_enterc :: "cfg_node \<Rightarrow> sign list \<Rightarrow> store \<Rightarrow> sign list" where
  "sctx_entry_enterc u ctx s =
     route_enterc_of_sigma (sctx_spec gs empty_pred)
       (sctx_entry_route_gen gs empty_pred) (snd (sctx_entry_sol gs empty_pred Pi ps)) Global
       (compile_prog Pi ps) u ctx s"

lemmas sctx_entry_routed_context_call =
  sctx_entry_routed.routed_context_call[folded sctx_entry_enterc_def]
lemmas sctx_entry_routed_context_comb =
  sctx_entry_routed.routed_context_comb[folded sctx_entry_enterc_def]

text \<open>
  \<^locale>\<open>dg_analysis_adapter\<close> at the same executable solved system, handed the readback
  as \<open>rd\<close> and Sign's classifier; its activation-collect soundness is the entry-state
  soundness theorem, stated against the routed local unknown read back through
  \<^const>\<open>gamma_state_lift\<close>.
\<close>

interpretation sctx_entry_adapter: routed_analysis_sound
    "sctx_spec gs empty_pred" "sctx_gamma gs" gs
    "compile_prog Pi ps" Global "sctx_entry_route_gen gs empty_pred" Bot "Lifted cinit_sign_st" Bot
    "snd (sctx_entry_sol gs empty_pred Pi ps)" "fst (sctx_entry_sol gs empty_pred Pi ps)"
    "(cfg_exit (compile_prog Pi ps), [])"
    Seed sctx_entry_enterc
    "map_lift (fun_of_resolved_st_q_for gs)" sign_classify_check
proof (unfold_locales, goal_cases FinE PP SgCov SgUncov Fwd FinC SeedKey ResolveSound
    RouteEnterc CallFwd CombFwd EnterAgree GammaRd ClProved ClRefuted)
  case FinE show ?case by (rule sctx_entry_fin)
next
  case PP show ?case by (rule sctx_entry_pp_routed[OF solves exact])
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
  case FinC show ?case by (rule sctx_entry_finC)
next
  case (SeedKey p ctx) show ?case by simp
next
  case (ResolveSound u ctx dst pars args p cont s)
  thus ?case by (simp add: static_resolve_iff[OF sctx_entry_finC])
next
  case (RouteEnterc u ctx dst pars args p cont s)
  show ?case unfolding sctx_entry_enterc_def
    by (rule route_enterc_of_sigma_agree[OF sctx_entry_finC compile_prog_calls_source_unique
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
  show ?case by (simp add: sctx_gamma_def)
next
  case (ClProved c d s)
  thus ?case by (rule sign_classify_check_proved)
next
  case (ClRefuted c d s)
  thus ?case by (rule sign_classify_check_refuted)
qed

theorem sctx_entry_activation_collect_sound:
  "activation_collect gs sctx_entry_enterc [] (compile_prog Pi ps) (cinit_stores gs) v ctx
     \<subseteq> gamma_state_lift (map_lift (fun_of_resolved_st_q_for gs)
           (sctx_entry_sg_st gs empty_pred Pi ps (Inl (v, ctx))))"
  unfolding sctx_entry_sg_st_def
  by (rule sctx_entry_adapter.routed_activation_collect_sound
        [OF entry_cov sctx_entry_cinit_le_cinit_sign_st])
end

subsection \<open>Whole-program convenience layer\<close>

definition sctx_entry_eqs_prog ::
    "(vname \<Rightarrow> bool) \<Rightarrow> imp_prog
       \<Rightarrow> (pp \<times> sign list, gk, (sign exec_dg_st lifted, sign exec_dg_st lifted) dg_state) eqsT" where
  "sctx_entry_eqs_prog gs p =
     sctx_entry_eqs gs (resolved_st_q_is_bot_for (declared_global_vars p))
       (prog_table p) (prog_procs p)"

definition sctx_entry_sol_prog ::
    "(vname \<Rightarrow> bool) \<Rightarrow> imp_prog
       \<Rightarrow> (pp \<times> sign list) set \<times> (pp \<times> sign list + gk \<Rightarrow> (sign exec_dg_st lifted, sign exec_dg_st lifted) dg_state)" where
  "sctx_entry_sol_prog gs p =
     sctx_entry_sol gs (resolved_st_q_is_bot_for (declared_global_vars p))
       (prog_table p) (prog_procs p)"

definition sctx_entry_terminates_prog :: "(vname \<Rightarrow> bool) \<Rightarrow> imp_prog \<Rightarrow> bool" where
  "sctx_entry_terminates_prog gs p =
     sctx_entry_terminates gs (resolved_st_q_is_bot_for (declared_global_vars p))
       (prog_table p) (prog_procs p)"

lemma sctx_entry_terminates_prog_via_solve_c:
  assumes "TD_side_always_join_Interp_solve_c
             (sctx_entry_eqs_prog gs p)
             (cfg_exit (compile_prog (prog_table p) (prog_procs p)), []) \<noteq> None"
  shows "sctx_entry_terminates_prog gs p"
  using assms
  unfolding sctx_entry_terminates_prog_def sctx_entry_eqs_prog_def
  by (rule sctx_entry_terminates_via_solve_c)

section \<open>Solved-result table\<close>

text \<open>
  The solved entry-state D/G system, read as a \<^typ>\<open>(sign list, sign abs_state)
  analysis_result\<close> -- the exact construction Interval's own entry-state result table
  already uses (\<open>Interval_Ctx_Entry_State_Sound\<close>), at Sign's own solve instead of
  Interval's. The covered-key set is the solver's own, never an enumerated theoretical
  context space, matching Interval's own posture.
\<close>

definition analyse_sign_entry_state_result_for ::
    "(vname \<Rightarrow> bool) \<Rightarrow> imp_prog \<Rightarrow> (sign list, sign abs_state) analysis_result" where
  "analyse_sign_entry_state_result_for gs p =
     Analysis_Result
       (fst (sctx_entry_sol_prog gs p))
       (\<lambda>v ctx. normalize_point gs
                  (canonicalize_lift (resolved_st_q_is_bot_for (declared_global_vars p))
                    (locals (snd (sctx_entry_sol_prog gs p) (Inl (v, ctx))))))"

declare analyse_sign_entry_state_result_for_def [code del]

lemma analyse_sign_entry_state_result_for_code [code]:
  "analyse_sign_entry_state_result_for gs p =
     (let sol = sctx_entry_sol_prog gs p; gl = declared_global_vars p
      in Analysis_Result (fst sol)
           (\<lambda>v ctx. normalize_point gs
                      (canonicalize_lift (resolved_st_q_is_bot_for gl)
                        (locals (snd sol (Inl (v, ctx)))))))"
  unfolding analyse_sign_entry_state_result_for_def Let_def by (rule refl)

text \<open>Convenience instance at \<^const>\<open>declared_global\<close> \<open>p\<close> and \<^const>\<open>prog_main_name\<close>,
  matching \<open>analyse_sign_call_string_result\<close>'s shape.\<close>

definition analyse_sign_entry_state_result :: "imp_prog \<Rightarrow> (sign list, sign abs_state) analysis_result" where
  "analyse_sign_entry_state_result p =
     analyse_sign_entry_state_result_for (declared_global p) p"

section \<open>Contextual check report\<close>

text \<open>
  Reuses \<^const>\<open>classify_checks_ctx\<close>/\<^const>\<open>classify_checks_verdicts\<close> unchanged --
  both are generic in the context type already, so nothing entry-state-specific is
  needed here beyond supplying the entry-state result table and Sign's own
  \<open>sign_classify_check\<close>.
\<close>

definition sctx_entry_check_projection ::
    "imp_prog \<Rightarrow> (pp \<times> exp \<times> (sign list \<times> contextual_verdict) set) list" where
  "sctx_entry_check_projection p =
     classify_checks_ctx (prog_cfg p)
       (analyse_sign_entry_state_result_for (declared_global p) p)
       sign_classify_check"

definition sctx_entry_verdict_report_prog ::
    "imp_prog \<Rightarrow> (pp \<times> exp \<times> contextual_verdict) list" where
  "sctx_entry_verdict_report_prog p =
     map (\<lambda>(u, c, vs). (u, c, aggregate_verdicts (snd ` vs)))
       (sctx_entry_check_projection p)"

lemma sctx_entry_verdict_report_prog_eq:
  "sctx_entry_verdict_report_prog p =
     classify_checks_verdicts (prog_cfg p)
       (analyse_sign_entry_state_result_for (declared_global p) p)
       sign_classify_check"
  unfolding sctx_entry_verdict_report_prog_def sctx_entry_check_projection_def
  by (rule classify_checks_verdicts_proj)

definition analyse_sign_entry_state_report :: "imp_prog \<Rightarrow> (pp \<times> exp \<times> contextual_verdict) list" where
  "analyse_sign_entry_state_report p = sctx_entry_verdict_report_prog p"

end

