theory Int_Ctx_Entry_State_Sound
  imports
    "Voblint_Analysis.Int_Ctx_None_Sound"
    "Voblint_Analysis.Int_Classify"
    Entry_State_Routed_Context
begin

section \<open>Int at the routed spine, instantiated at the entry-state context\<close>

text \<open>
  The entry-state sibling of Int's own routed-unit-context instance
  (\<^theory>\<open>Voblint_Analysis.Int_Ctx_None_Sound\<close>), and the fourth architecture-milestone
  acceptance test, after Sign's own call-string and entry-state derivations and Int's
  own call-string derivation: same \<^const>\<open>ictx_spec\<close>/\<^const>\<open>ictx_abs_spec\<close> D/G
  specification and the same domain-commute facts Int already interprets
  (\<^locale>\<open>routed_dg_domain_exec\<close>, \<^theory>\<open>Voblint_Exec.DG_Base_Exec\<close>) -- nothing here
  re-derives them, and the \<^typ>\<open>refine_mode\<close> parameter Int threads throughout stays a
  genuine fixed argument exactly as it already is at Int's own \<^const>\<open>ictx_spec\<close>. The
  routing policy is the same generic entry-state construction
  (\<open>entry_exec_route_gen\<close>/\<^const>\<open>formals_route_lifted_gen\<close>,
  \<^theory>\<open>Voblint_Exec.DG_Base_Exec\<close>/\<^theory>\<open>Voblint_Core.Routed_Context\<close>) Sign's own
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

subsection \<open>Global key: real globals vs callee-entry seed slots\<close>

datatype gk = Global | Seed (seed_pp: pp) (seed_ctx: "int_dom list")

subsection \<open>The routed equation system's own route, generic per compiled program\<close>

text \<open>
  Int's own executable-carrier route, mirroring Sign's own
  \<open>sctx_entry_route\<close>/\<open>sctx_entry_route_gen\<close> exactly, at Int's own
  \<open>int_dom_enter_st_for mode gs\<close> instead of Sign's \<open>sign_enter_st_for gs\<close> -- this is
  precisely \<^locale>\<open>routed_dg_domain_exec\<close>'s own \<open>entry_exec_route\<close>/
  \<open>entry_exec_route_gen\<close> (\<^theory>\<open>Voblint_Exec.DG_Base_Exec\<close>), restated here as
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
       \<Rightarrow> (pp \<times> int_dom list, gk, (int_dom exec_dg_st lifted, int_dom exec_dg_st lifted) dg_state) eqsT" where
  "ictx_entry_eqs mode gs empty_pred Pi ps =
     side_cfg_T_eff_keyed_seed_dg_buffered intra_predecessor_addr_list (\<lambda>_. Global)
       (ictx_entry_route_gen mode gs empty_pred)
       (\<lambda>ctx' src a. dg_spec_edge_tree (ictx_spec mode empty_pred gs) a src Global)
       (routed_cmb_g (ictx_spec mode empty_pred gs) Global Seed
          (static_resolve (compile_prog Pi ps)))
       (routed_extra_g Seed Global)
       (compile_prog Pi ps) Bot (Lifted cinit_int_dom_st) Bot"

definition ictx_entry_sol ::
    "refine_mode \<Rightarrow> (vname \<Rightarrow> bool) \<Rightarrow> (int_dom exec_dg_st \<Rightarrow> bool) \<Rightarrow> proc_table \<Rightarrow> pname list
       \<Rightarrow> (pp \<times> int_dom list) set \<times> (pp \<times> int_dom list + gk \<Rightarrow> (int_dom exec_dg_st lifted, int_dom exec_dg_st lifted) dg_state)" where
  "ictx_entry_sol mode gs empty_pred Pi ps =
     TD_side_always_join_Interp_solve (ictx_entry_eqs mode gs empty_pred Pi ps)
       (cfg_exit (compile_prog Pi ps), [])"

definition ictx_entry_terminates ::
    "refine_mode \<Rightarrow> (vname \<Rightarrow> bool) \<Rightarrow> (int_dom exec_dg_st \<Rightarrow> bool) \<Rightarrow> proc_table \<Rightarrow> pname list
       \<Rightarrow> bool" where
  "ictx_entry_terminates mode gs empty_pred Pi ps =
     TD_side_always_join_Interp.solve_dom TYPE(gk) TYPE((int_dom exec_dg_st lifted, int_dom exec_dg_st lifted) dg_state)
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
  with the solver swapped, as \<^theory>\<open>Voblint_Analysis.Int_Ctx_None_Sound\<close> does.
\<close>

definition ictx_entry_sol_warrow ::
    "refine_mode \<Rightarrow> (vname \<Rightarrow> bool) \<Rightarrow> (int_dom exec_dg_st \<Rightarrow> bool) \<Rightarrow> proc_table \<Rightarrow> pname list
       \<Rightarrow> (pp \<times> int_dom list) set \<times> (pp \<times> int_dom list + gk \<Rightarrow> (int_dom exec_dg_st lifted, int_dom exec_dg_st lifted) dg_state)" where
  "ictx_entry_sol_warrow mode gs empty_pred Pi ps =
     TD_side_warrowing_apinis_Interp_solve (ictx_entry_eqs mode gs empty_pred Pi ps)
       (cfg_exit (compile_prog Pi ps), [])"

definition ictx_entry_terminates_warrow ::
    "refine_mode \<Rightarrow> (vname \<Rightarrow> bool) \<Rightarrow> (int_dom exec_dg_st \<Rightarrow> bool) \<Rightarrow> proc_table \<Rightarrow> pname list
       \<Rightarrow> bool" where
  "ictx_entry_terminates_warrow mode gs empty_pred Pi ps =
     TD_side_warrowing_apinis_Interp.solve_dom TYPE(gk) TYPE((int_dom exec_dg_st lifted, int_dom exec_dg_st lifted) dg_state)
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
  Global Seed "ictx_entry_route_gen mode gs empty_pred"
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
  "TD_side_always_join_Interp.solve_dom TYPE(gk) TYPE((int_dom exec_dg_st lifted, int_dom exec_dg_st lifted) dg_state)
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
     (side_cfg_T_eff_keyed_seed_dg intra_predecessor_addr_list (\<lambda>_. Global)
        (ictx_entry_route_gen mode gs empty_pred)
        (\<lambda>ctx' src a. dg_spec_edge_tree (ictx_spec mode empty_pred gs) a src Global)
        (routed_cmb_g (ictx_spec mode empty_pred gs) Global Seed
           (static_resolve (compile_prog Pi ps)))
        (routed_extra_g Seed Global)
        (compile_prog Pi ps) Bot (Lifted cinit_int_dom_st) Bot)
     (cfg_exit (compile_prog Pi ps), [])
     (snd (ictx_entry_sol mode gs empty_pred Pi ps)) (fst (ictx_entry_sol mode gs empty_pred Pi ps))"
  using ictx_entry_pp_st unfolding ictx_entry_eqs_def ictx_spec_def
  by (rule int_es_pp_st_gen[OF exact])

end

subsection \<open>The certified executable post-solution under warrowing\<close>

context
  fixes mode :: refine_mode and gs :: "vname \<Rightarrow> bool" and empty_pred :: "int_dom exec_dg_st \<Rightarrow> bool"
    and Pi :: proc_table and ps :: "pname list"
  assumes solves: "ictx_entry_terminates_warrow mode gs empty_pred Pi ps"
    and exact: "\<And>s. empty_pred s = is_empty_state (fun_of_resolved_st_q_for gs s)"
begin

lemma ictx_entry_solve_dom_warrow:
  "TD_side_warrowing_apinis_Interp.solve_dom TYPE(gk) TYPE((int_dom exec_dg_st lifted, int_dom exec_dg_st lifted) dg_state)
     (ictx_entry_eqs mode gs empty_pred Pi ps) (cfg_exit (compile_prog Pi ps), [])"
  using solves[unfolded ictx_entry_terminates_warrow_def] .

lemma ictx_entry_pp_st_warrow:
  "part_post_solution (ictx_entry_eqs mode gs empty_pred Pi ps) (cfg_exit (compile_prog Pi ps), [])
     (snd (ictx_entry_sol_warrow mode gs empty_pred Pi ps)) (fst (ictx_entry_sol_warrow mode gs empty_pred Pi ps))"
  using TD_side_warrowing_apinis_Interp.partial_post_solution
          [OF ictx_entry_solve_dom_warrow, of "fst (ictx_entry_sol_warrow mode gs empty_pred Pi ps)"
             "snd (ictx_entry_sol_warrow mode gs empty_pred Pi ps)"]
  unfolding ictx_entry_sol_warrow_def by simp

theorem ictx_entry_pp_routed_warrow:
  "part_post_solution
     (side_cfg_T_eff_keyed_seed_dg intra_predecessor_addr_list (\<lambda>_. Global)
        (ictx_entry_route_gen mode gs empty_pred)
        (\<lambda>ctx' src a. dg_spec_edge_tree (ictx_spec mode empty_pred gs) a src Global)
        (routed_cmb_g (ictx_spec mode empty_pred gs) Global Seed
           (static_resolve (compile_prog Pi ps)))
        (routed_extra_g Seed Global)
        (compile_prog Pi ps) Bot (Lifted cinit_int_dom_st) Bot)
     (cfg_exit (compile_prog Pi ps), [])
     (snd (ictx_entry_sol_warrow mode gs empty_pred Pi ps))
     (fst (ictx_entry_sol_warrow mode gs empty_pred Pi ps))"
  using ictx_entry_pp_st_warrow unfolding ictx_entry_eqs_def ictx_spec_def
  by (rule int_es_pp_st_gen[OF exact])

end

section \<open>Activation-indexed collecting soundness, generic per compiled program\<close>

text \<open>
  The routed spine is interpreted at Int's executable carrier and fed the solver's own
  table, as \<open>Int_Ctx_None_Sound\<close> does at the unit context: a local unknown concretizes
  to \<^const>\<open>gamma_state_lift\<close> of its readback (\<^const>\<open>ictx_gamma\<close>), the covered reader
  \<open>ictx_entry_sg_st\<close> hands the table's local slot through unchanged, and the route is
  Int's own executable \<^const>\<open>ictx_entry_route_gen\<close>.
\<close>

definition ictx_entry_sg_st ::
    "refine_mode \<Rightarrow> (vname \<Rightarrow> bool) \<Rightarrow> (int_dom exec_dg_st \<Rightarrow> bool) \<Rightarrow> proc_table \<Rightarrow> pname list
       \<Rightarrow> pp \<times> int_dom list + gk \<Rightarrow> int_dom exec_dg_st lifted" where
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
                 (entered (ictx_spec mode empty_pred gs) Global
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

interpretation ictx_entry_dg_base: sound_dg_spec "ictx_spec mode empty_pred gs" "ictx_gamma gs" gs
  by (rule ictx_sound_exec[OF exact])

interpretation ictx_entry_routed: entry_state_routed_context "ictx_spec mode empty_pred gs"
    "ictx_gamma gs" gs Pi ps Global "ictx_entry_route_gen mode gs empty_pred"
    Bot "Lifted cinit_int_dom_st" Bot
    "snd (ictx_entry_sol mode gs empty_pred Pi ps)" "fst (ictx_entry_sol mode gs empty_pred Pi ps)"
    "(cfg_exit (compile_prog Pi ps), [])" "ictx_entry_sg_st mode gs empty_pred Pi ps" Seed
    "\<lambda>m. gamma_state_lift (map_lift (fun_of_resolved_st_q_for gs) m)"
proof (unfold_locales, goal_cases FinE PP SgCov SgUncov Fwd SeedNe CallFwd CombFwd)
  case FinE show ?case by (rule ictx_entry_fin)
next
  case PP show ?case by (rule ictx_entry_pp_routed[OF solves exact])
next
  case (SgCov v ctx) then show ?case
    by (simp add: ictx_entry_sg_st_def ictx_gamma_def)
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
  "cinit_stores gs \<subseteq> ictx_gamma gs (Lifted cinit_int_dom_st) Bot"
  by (auto simp: ictx_gamma_def cinit_stores_def gamma_state_def fun_of_resolved_st_q_for_def
                 fun_of_st_cinit_int_dom_st_for gamma_int_dom_top)

text \<open>The trace-semantic context function the routed table induces: at a call site it
  routes the entered store's abstraction, read from the solver's own table.\<close>

definition ictx_entry_enterc :: "cfg_node \<Rightarrow> int_dom list \<Rightarrow> store \<Rightarrow> int_dom list" where
  "ictx_entry_enterc u ctx s =
     route_enterc_of_sigma (ictx_spec mode empty_pred gs)
       (ictx_entry_route_gen mode gs empty_pred) (snd (ictx_entry_sol mode gs empty_pred Pi ps))
       Global (compile_prog Pi ps) u ctx s"

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

interpretation ictx_entry_adapter: dg_analysis_adapter "ictx_spec mode empty_pred gs"
    "ictx_gamma gs" gs "compile_prog Pi ps" Global "ictx_entry_route_gen mode gs empty_pred"
    Bot "Lifted cinit_int_dom_st" Bot
    "snd (ictx_entry_sol mode gs empty_pred Pi ps)" "fst (ictx_entry_sol mode gs empty_pred Pi ps)"
    "(cfg_exit (compile_prog Pi ps), [])" "ictx_entry_sg_st mode gs empty_pred Pi ps"
    Seed "\<lambda>m. gamma_state_lift (map_lift (fun_of_resolved_st_q_for gs) m)" ictx_entry_enterc
    "map_lift (fun_of_resolved_st_q_for gs)" int_classify_check
proof (unfold_locales, goal_cases FinE PP SgCov SgUncov Fwd FinC SeedKey ResolveSound
    RouteEnterc CallFwd CombFwd EnterAgree GammaRd ClProved ClRefuted)
  case FinE show ?case by (rule ictx_entry_fin)
next
  case PP show ?case by (rule ictx_entry_pp_routed[OF solves exact])
next
  case (SgCov v c)
  thus ?case by (simp add: ictx_entry_sg_st_def ictx_gamma_def)
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
  show ?case by (simp add: ictx_gamma_def)
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
       \<Rightarrow> (pp \<times> int_dom list, gk, (int_dom exec_dg_st lifted, int_dom exec_dg_st lifted) dg_state) eqsT" where
  "ictx_entry_eqs_prog gs p =
     ictx_entry_eqs Refine_Fixpoint gs (resolved_st_q_is_bot_for (declared_global_vars p))
       (prog_table p) (prog_procs p)"

definition ictx_entry_sol_prog ::
    "(vname \<Rightarrow> bool) \<Rightarrow> imp_prog
       \<Rightarrow> (pp \<times> int_dom list) set \<times> (pp \<times> int_dom list + gk \<Rightarrow> (int_dom exec_dg_st lifted, int_dom exec_dg_st lifted) dg_state)" where
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
       \<Rightarrow> (pp \<times> int_dom list) set \<times> (pp \<times> int_dom list + gk \<Rightarrow> (int_dom exec_dg_st lifted, int_dom exec_dg_st lifted) dg_state)" where
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

subsection \<open>Result table and report under warrowing\<close>

definition analyse_int_entry_state_result_for_warrow ::
    "(vname \<Rightarrow> bool) \<Rightarrow> imp_prog \<Rightarrow> (int_dom list, int_dom abs_state) analysis_result" where
  "analyse_int_entry_state_result_for_warrow gs p =
     Analysis_Result
       (fst (ictx_entry_sol_prog_warrow gs p))
       (\<lambda>v ctx. normalize_point gs
                  (canonicalize_lift (resolved_st_q_is_bot_for (declared_global_vars p))
                    (locals (snd (ictx_entry_sol_prog_warrow gs p) (Inl (v, ctx))))))"

declare analyse_int_entry_state_result_for_warrow_def [code del]

lemma analyse_int_entry_state_result_for_warrow_code [code]:
  "analyse_int_entry_state_result_for_warrow gs p =
     (let sol = ictx_entry_sol_prog_warrow gs p; gl = declared_global_vars p
      in Analysis_Result (fst sol)
           (\<lambda>v ctx. normalize_point gs
                      (canonicalize_lift (resolved_st_q_is_bot_for gl)
                        (locals (snd sol (Inl (v, ctx)))))))"
  unfolding analyse_int_entry_state_result_for_warrow_def Let_def by (rule refl)

definition analyse_int_entry_state_result_warrow ::
    "imp_prog \<Rightarrow> (int_dom list, int_dom abs_state) analysis_result" where
  "analyse_int_entry_state_result_warrow p =
     analyse_int_entry_state_result_for_warrow (declared_global p) p"

definition ictx_entry_verdict_report_prog_warrow ::
    "imp_prog \<Rightarrow> (pp \<times> exp \<times> contextual_verdict) list" where
  "ictx_entry_verdict_report_prog_warrow p =
     classify_checks_verdicts (prog_cfg p)
       (analyse_int_entry_state_result_for_warrow (declared_global p) p)
       int_classify_check"

definition analyse_int_entry_state_report_warrow ::
    "imp_prog \<Rightarrow> (pp \<times> exp \<times> contextual_verdict) list" where
  "analyse_int_entry_state_report_warrow p = ictx_entry_verdict_report_prog_warrow p"

end
