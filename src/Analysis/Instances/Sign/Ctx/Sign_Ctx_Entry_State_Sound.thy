theory Sign_Ctx_Entry_State_Sound
  imports
    "Voblint_Analysis.Sign_Ctx_None_Sound"
    "Voblint_Analysis.Sign_Checks"
    "Voblint_Core.Entry_State_Routed_Context"
begin

section \<open>Sign at the routed spine, instantiated at the entry-state context\<close>

text \<open>
  The entry-state sibling of \<^theory>\<open>Voblint_Analysis.Sign_Ctx_None_Sound\<close>'s own
  routed-unit-context instance, and the second architecture-milestone acceptance test
  after \<open>Sign_Ctx_Call_String_Sound\<close>: same \<^const>\<open>sctx_spec\<close>/\<^const>\<open>sctx_abs_spec\<close>  D/G specification and the same domain-commute facts Sign already interprets
  (\<^locale>\<open>routed_dg_domain_exec\<close>, \<^theory>\<open>Voblint_Core.DG_Base_Exec\<close>) -- nothing here
  re-derives them. The routing policy is Interval's own entry-state construction
  (\<open>entry_exec_route_gen\<close>/\<^const>\<open>formals_route_lifted_gen\<close>,
  \<^theory>\<open>Voblint_Core.DG_Base_Exec\<close>/\<^theory>\<open>Voblint_Core.Routed_Context\<close>), already
  generalized in a domain -- unlike \<open>cs_route\<close>, this route genuinely depends on
  its caller-state argument (the entered callee frame), which is exactly the "small
  additional domain capability" the routed-domain milestone anticipated for EntryState;
  it needed only \<open>routed_dg_domain_exec\<close>'s own three primitive commute facts, no new
  Sign-domain mathematics. \<^locale>\<open>entry_state_routed_context\<close>
  (\<^theory>\<open>Voblint_Core.Entry_State_Routed_Context\<close>) is the generic context-side counterpart,
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
  \<open>entry_exec_route_gen\<close> (\<^theory>\<open>Voblint_Core.DG_Base_Exec\<close>), restated here as
  unconditional top-level definitions (rather than reached through an interpretation) so
  the equation-system definitions below need no \<open>exact\<close> premise to be stated, matching
  every other routed instance's convention. The routed generator enters the callee
  frame before it routes, so the route itself only projects the formals out of the
  state it is handed.
\<close>

definition sctx_entry_route ::
    "(vname \<Rightarrow> bool) \<Rightarrow> (sign exec_dg_st \<Rightarrow> bool) \<Rightarrow> sign exec_dg_st lifted \<Rightarrow> call_action \<Rightarrow> sign list" where
  "sctx_entry_route gs is_bot_pred d ca =
     (case ca of CallEdge dst pars args \<Rightarrow>
        formals_context pars (fun_of_resolved_st_q_for gs
          (case d of Bot \<Rightarrow> bot | Lifted d0 \<Rightarrow> d0)))"

definition sctx_entry_route_gen ::
    "(vname \<Rightarrow> bool) \<Rightarrow> (sign exec_dg_st \<Rightarrow> bool) \<Rightarrow> pp \<Rightarrow> sign list \<Rightarrow> sign exec_dg_st lifted \<Rightarrow> call_action \<Rightarrow> sign list" where
  "sctx_entry_route_gen gs is_bot_pred u ctx d ca = sctx_entry_route gs is_bot_pred d ca"

subsection \<open>The routed equation system and its executable solution\<close>

definition sctx_entry_eqs ::
    "(vname \<Rightarrow> bool) \<Rightarrow> tyenv \<Rightarrow> (sign exec_dg_st \<Rightarrow> bool) \<Rightarrow> proc_table \<Rightarrow> pname list \<Rightarrow> pname \<Rightarrow> com
       \<Rightarrow> (pp \<times> sign list, gk, (sign exec_dg_st lifted, sign exec_dg_st lifted) dg_state) eqsT" where
  "sctx_entry_eqs gs \<Gamma> is_bot_pred Pi ps mnm main =
     side_cfg_T_eff_keyed_seed_dg_buffered intra_predecessor_addr_list (\<lambda>_. Global)
       (sctx_entry_route_gen gs is_bot_pred)
       (routed_cmb_g_contribution (sctx_spec gs is_bot_pred) Global Seed
          (static_resolve (compile_prog \<Gamma> Pi ps mnm main)))
       (routed_extra_g Seed Global)
       (compile_prog \<Gamma> Pi ps mnm main) (sctx_spec gs is_bot_pred) Bot (Lifted cinit_sign_st) Bot"

definition sctx_entry_sol ::
    "(vname \<Rightarrow> bool) \<Rightarrow> tyenv \<Rightarrow> (sign exec_dg_st \<Rightarrow> bool) \<Rightarrow> proc_table \<Rightarrow> pname list \<Rightarrow> pname \<Rightarrow> com
       \<Rightarrow> (pp \<times> sign list) set \<times> (pp \<times> sign list + gk \<Rightarrow> (sign exec_dg_st lifted, sign exec_dg_st lifted) dg_state)" where
  "sctx_entry_sol gs \<Gamma> is_bot_pred Pi ps mnm main =
     TD_side_always_join_Interp_solve (sctx_entry_eqs gs \<Gamma> is_bot_pred Pi ps mnm main)
       (cfg_exit (compile_prog \<Gamma> Pi ps mnm main), [])"

definition sctx_entry_terminates ::
    "(vname \<Rightarrow> bool) \<Rightarrow> tyenv \<Rightarrow> (sign exec_dg_st \<Rightarrow> bool) \<Rightarrow> proc_table \<Rightarrow> pname list \<Rightarrow> pname \<Rightarrow> com \<Rightarrow> bool" where
  "sctx_entry_terminates gs \<Gamma> is_bot_pred Pi ps mnm main =
     TD_side_always_join_Interp.solve_dom TYPE(gk) TYPE((sign exec_dg_st lifted, sign exec_dg_st lifted) dg_state)
       (sctx_entry_eqs gs \<Gamma> is_bot_pred Pi ps mnm main) (cfg_exit (compile_prog \<Gamma> Pi ps mnm main), [])"

lemma sctx_entry_terminates_via_solve_c:
  assumes "TD_side_always_join_Interp_solve_c (sctx_entry_eqs gs \<Gamma> is_bot_pred Pi ps mnm main)
             (cfg_exit (compile_prog \<Gamma> Pi ps mnm main), []) \<noteq> None"
  shows "sctx_entry_terminates gs \<Gamma> is_bot_pred Pi ps mnm main"
  unfolding sctx_entry_terminates_def
  by (rule TD_side_always_join_Interp.solve_dom_of_solve_c[OF assms])

subsection \<open>Route agreement: the one genuinely domain-specific commute fact\<close>

context
  fixes gs :: "vname \<Rightarrow> bool" and \<Gamma> :: tyenv and is_bot_pred :: "sign exec_dg_st \<Rightarrow> bool"
  assumes exact: "\<And>s. is_bot_pred s = is_bot_state (fun_of_resolved_st_q_for gs s)"
begin

interpretation sign_domain: routed_dg_domain_exec
  gs is_bot_pred "sign_tf_st_for gs" "sign_enter_st_for gs" "sign_tf_for gs"
  by unfold_locales (rule sign_tf_st_for_commute, rule sign_enter_st_for_commute, rule exact)

lemma sctx_entry_route_gen_eq_generic:
  "sctx_entry_route_gen gs is_bot_pred u ctx d ca = sign_domain.entry_exec_route_gen u ctx d ca"
  unfolding sctx_entry_route_gen_def sign_domain.entry_exec_route_gen_def
    sctx_entry_route_def sign_domain.entry_exec_route_def
  by (rule refl)

lemma sctx_entry_route_gen_commute:
  "formals_route_lifted_gen (sctx_abs_spec gs) u ctx (map_lift (fun_of_resolved_st_q_for gs) d) ca
     = sctx_entry_route_gen gs is_bot_pred u ctx d ca"
  unfolding sctx_entry_route_gen_eq_generic sctx_abs_spec_def
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
  fixes gs :: "vname \<Rightarrow> bool" and \<Gamma> :: tyenv and is_bot_pred :: "sign exec_dg_st \<Rightarrow> bool"
  assumes exact: "\<And>s. is_bot_pred s = is_bot_state (fun_of_resolved_st_q_for gs s)"
begin

interpretation sign_es: routed_domain_exec
  gs is_bot_pred "sign_tf_st_for gs" "sign_enter_st_for gs" "sign_tf_for gs"
  Global Seed "sctx_entry_route_gen gs is_bot_pred"
  "formals_route_lifted_gen (sctx_abs_spec gs)"
  static_resolve static_resolve
  by unfold_locales
     (rule sign_tf_st_for_commute, rule sign_enter_st_for_commute, rule exact, simp,
      rule sctx_entry_route_gen_commute[OF exact, symmetric],
      simp add: static_resolve_def)

lemmas sign_es_pp_abs_gen = sign_es.pp_abs

end

subsection \<open>The certified executable post-solution, generic per compiled program\<close>

context
  fixes gs :: "vname \<Rightarrow> bool" and \<Gamma> :: tyenv and is_bot_pred :: "sign exec_dg_st \<Rightarrow> bool"
    and Pi :: proc_table and ps :: "pname list" and mnm :: pname and main :: com
  assumes solves: "sctx_entry_terminates gs \<Gamma> is_bot_pred Pi ps mnm main"
    and exact: "\<And>s. is_bot_pred s = is_bot_state (fun_of_resolved_st_q_for gs s)"
begin

lemma sctx_entry_solve_dom:
  "TD_side_always_join_Interp.solve_dom TYPE(gk) TYPE((sign exec_dg_st lifted, sign exec_dg_st lifted) dg_state)
     (sctx_entry_eqs gs \<Gamma> is_bot_pred Pi ps mnm main) (cfg_exit (compile_prog \<Gamma> Pi ps mnm main), [])"
  using solves[unfolded sctx_entry_terminates_def] .

lemma sctx_entry_pp_st:
  "part_post_solution (sctx_entry_eqs gs \<Gamma> is_bot_pred Pi ps mnm main) (cfg_exit (compile_prog \<Gamma> Pi ps mnm main), [])
     (snd (sctx_entry_sol gs \<Gamma> is_bot_pred Pi ps mnm main)) (fst (sctx_entry_sol gs \<Gamma> is_bot_pred Pi ps mnm main))"
  using TD_side_always_join_Interp.partial_post_solution
          [OF sctx_entry_solve_dom, of "fst (sctx_entry_sol gs \<Gamma> is_bot_pred Pi ps mnm main)"
             "snd (sctx_entry_sol gs \<Gamma> is_bot_pred Pi ps mnm main)"]
  unfolding sctx_entry_sol_def by simp

theorem sctx_entry_pp_abs:
  "part_post_solution
     (side_cfg_T_eff_keyed_seed_dg intra_predecessor_addr_list (\<lambda>_. Global)
        (formals_route_lifted_gen (sctx_abs_spec gs))
        (routed_cmb_g (sctx_abs_spec gs) Global Seed
           (static_resolve (compile_prog \<Gamma> Pi ps mnm main)))
        (routed_extra_g Seed Global)
        (compile_prog \<Gamma> Pi ps mnm main) (sctx_abs_spec gs)
        (map_lift (fun_of_resolved_st_q_for gs) (Bot::sign exec_dg_st lifted))
        (map_lift (fun_of_resolved_st_q_for gs) (Lifted cinit_sign_st))
        (map_lift (fun_of_resolved_st_q_for gs) (Bot::sign exec_dg_st lifted)))
     (cfg_exit (compile_prog \<Gamma> Pi ps mnm main), [])
     (fun_of_dg_st_gen (map_lift (fun_of_resolved_st_q_for gs)) (map_lift (fun_of_resolved_st_q_for gs))
        \<circ> snd (sctx_entry_sol gs \<Gamma> is_bot_pred Pi ps mnm main))
     (fst (sctx_entry_sol gs \<Gamma> is_bot_pred Pi ps mnm main))"
proof -
  have pp_buf: "part_post_solution
       (side_cfg_T_eff_keyed_seed_dg_buffered intra_predecessor_addr_list (\<lambda>_. Global)
          (sctx_entry_route_gen gs is_bot_pred)
          (routed_cmb_g_contribution (sctx_spec gs is_bot_pred) Global Seed
             (static_resolve (compile_prog \<Gamma> Pi ps mnm main)))
          (routed_extra_g Seed Global)
          (compile_prog \<Gamma> Pi ps mnm main) (sctx_spec gs is_bot_pred) Bot (Lifted cinit_sign_st) Bot)
       (cfg_exit (compile_prog \<Gamma> Pi ps mnm main), [])
       (snd (sctx_entry_sol gs \<Gamma> is_bot_pred Pi ps mnm main))
       (fst (sctx_entry_sol gs \<Gamma> is_bot_pred Pi ps mnm main))"
    using sctx_entry_pp_st unfolding sctx_entry_eqs_def by simp
  show ?thesis
    using pp_buf unfolding sctx_spec_def
    by (rule sign_es_pp_abs_gen[OF exact, folded sctx_abs_spec_def])
qed

end

section \<open>Activation-indexed collecting soundness, generic per compiled program\<close>

text \<open>
  Executable twins of the context's own \<open>sctx_entry_sigma_abs\<close>/\<open>sctx_entry_sg\<close> (below),
  defined before that context so their equations are unconditional -- mirrors Interval's
  own \<open>entry_state_sigma_abs_exec\<close>/\<open>entry_state_sg_exec\<close> convention exactly.
\<close>

definition sctx_entry_sigma_abs_exec ::
    "(vname \<Rightarrow> bool) \<Rightarrow> tyenv \<Rightarrow> (sign exec_dg_st \<Rightarrow> bool) \<Rightarrow> proc_table \<Rightarrow> pname list \<Rightarrow> pname \<Rightarrow> com
       \<Rightarrow> pp \<times> sign list + gk \<Rightarrow> (sign abs_state lifted, sign abs_state lifted) dg_state" where
  "sctx_entry_sigma_abs_exec gs \<Gamma> is_bot_pred Pi ps mnm main =
     fun_of_dg_st_gen (map_lift (fun_of_resolved_st_q_for gs)) (map_lift (fun_of_resolved_st_q_for gs))
       \<circ> snd (sctx_entry_sol gs \<Gamma> is_bot_pred Pi ps mnm main)"

definition sctx_entry_sg_exec ::
    "(vname \<Rightarrow> bool) \<Rightarrow> tyenv \<Rightarrow> (sign exec_dg_st \<Rightarrow> bool) \<Rightarrow> proc_table \<Rightarrow> pname list \<Rightarrow> pname \<Rightarrow> com
       \<Rightarrow> pp \<times> sign list + gk \<Rightarrow> sign abs_state lifted" where
  "sctx_entry_sg_exec gs \<Gamma> is_bot_pred Pi ps mnm main k =
     (case k of
        Inl (v, ctx) \<Rightarrow>
          (if (v, ctx) \<in> fst (sctx_entry_sol gs \<Gamma> is_bot_pred Pi ps mnm main)
           then locals (sctx_entry_sigma_abs_exec gs \<Gamma> is_bot_pred Pi ps mnm main (Inl (v, ctx)))
           else Bot)
      | Inr _ \<Rightarrow> Bot)"

context
  fixes gs :: "vname \<Rightarrow> bool" and \<Gamma> :: tyenv and is_bot_pred :: "sign exec_dg_st \<Rightarrow> bool"
    and Pi :: proc_table and ps :: "pname list" and mnm :: pname and main :: com
  assumes solves: "sctx_entry_terminates gs \<Gamma> is_bot_pred Pi ps mnm main"
    and exact: "\<And>s. is_bot_pred s = is_bot_state (fun_of_resolved_st_q_for gs s)"
    and entry_cov: "(cfg_entry (compile_prog \<Gamma> Pi ps mnm main), []) \<in> fst (sctx_entry_sol gs \<Gamma> is_bot_pred Pi ps mnm main)"
    and fwd_ok: "\<And>u a v ctx. (u, ctx) \<in> fst (sctx_entry_sol gs \<Gamma> is_bot_pred Pi ps mnm main)
                   \<Longrightarrow> (u, a, v) \<in> intra (compile_prog \<Gamma> Pi ps mnm main)
                   \<Longrightarrow> (v, ctx) \<in> fst (sctx_entry_sol gs \<Gamma> is_bot_pred Pi ps mnm main)"
    and call_fwd_ok: "\<And>u ctx dst pars args p cont.
        (u, ctx) \<in> fst (sctx_entry_sol gs \<Gamma> is_bot_pred Pi ps mnm main)
        \<Longrightarrow> (u, CallEdge dst pars args, FunctionEntry p, cont) \<in> calls (compile_prog \<Gamma> Pi ps mnm main)
        \<Longrightarrow> (FunctionEntry p,
               formals_route_lifted_gen (sctx_abs_spec gs) u ctx
                 (enter_local (sctx_abs_spec gs) pars args
                    (locals (sctx_entry_sigma_abs_exec gs \<Gamma> is_bot_pred Pi ps mnm main (Inl (u, ctx))))
                    (globs (sctx_entry_sigma_abs_exec gs \<Gamma> is_bot_pred Pi ps mnm main (Inr Global))))
                 (CallEdge dst pars args))
             \<in> fst (sctx_entry_sol gs \<Gamma> is_bot_pred Pi ps mnm main)"
    and comb_fwd_ok: "\<And>cl c1 dst pars args p cont.
        (cl, c1) \<in> fst (sctx_entry_sol gs \<Gamma> is_bot_pred Pi ps mnm main)
        \<Longrightarrow> (cl, CallEdge dst pars args, FunctionEntry p, cont) \<in> calls (compile_prog \<Gamma> Pi ps mnm main)
        \<Longrightarrow> (cont, c1) \<in> fst (sctx_entry_sol gs \<Gamma> is_bot_pred Pi ps mnm main)"
begin

subsection \<open>The semantic solution projection\<close>

definition sctx_entry_sigma_abs :: "pp \<times> sign list + gk \<Rightarrow> (sign abs_state lifted, sign abs_state lifted) dg_state" where
  "sctx_entry_sigma_abs = sctx_entry_sigma_abs_exec gs \<Gamma> is_bot_pred Pi ps mnm main"

definition sctx_entry_sg :: "pp \<times> sign list + gk \<Rightarrow> sign abs_state lifted" where
  "sctx_entry_sg = sctx_entry_sg_exec gs \<Gamma> is_bot_pred Pi ps mnm main"

lemma sctx_entry_fin: "finite (intra (compile_prog \<Gamma> Pi ps mnm main))"
  using compile_prog_finite by blast

lemma sctx_entry_finC: "finite (calls (compile_prog \<Gamma> Pi ps mnm main))"
  using compile_prog_finite by blast

lemma sctx_entry_sg_covered:
  "(v, ctx) \<in> fst (sctx_entry_sol gs \<Gamma> is_bot_pred Pi ps mnm main)
   \<Longrightarrow> sctx_entry_sg (Inl (v, ctx)) = locals (sctx_entry_sigma_abs (Inl (v, ctx)))"
  by (simp add: sctx_entry_sg_def sctx_entry_sg_exec_def sctx_entry_sigma_abs_def sctx_entry_sigma_abs_exec_def)

lemma sctx_entry_sg_uncovered_empty:
  "(v, ctx) \<notin> fst (sctx_entry_sol gs \<Gamma> is_bot_pred Pi ps mnm main)
     \<Longrightarrow> gamma_state_lift (sctx_entry_sg (Inl (v, ctx))) = {}"
  by (simp add: sctx_entry_sg_def sctx_entry_sg_exec_def)

subsection \<open>Instantiating the generic routed-context locale\<close>

lemma sctx_entry_cinit_le_cinit_sign_st:
  "cinit_stores gs \<subseteq> gamma_state_lift (map_lift (fun_of_resolved_st_q_for gs) (Lifted cinit_sign_st))"
  by (auto simp: cinit_stores_def gamma_state_def fun_of_resolved_st_q_for_def fun_of_st_cinit_sign_st_for)

interpretation sctx_entry_dg_base: sound_dg_spec "sctx_abs_spec gs" gamma_dg_base gs
  unfolding sctx_abs_spec_def
  by (rule base_dg_spec_sound[OF sign_is_sound_transfer_for is_bot_state_gamma_state_empty])

interpretation sctx_entry_routed: entry_state_routed_context "sctx_abs_spec gs" gs \<Gamma>
    Pi ps mnm main Global
    "map_lift (fun_of_resolved_st_q_for gs) (Bot::sign exec_dg_st lifted)"
    "map_lift (fun_of_resolved_st_q_for gs) (Lifted cinit_sign_st)"
    "map_lift (fun_of_resolved_st_q_for gs) (Bot::sign exec_dg_st lifted)"
    sctx_entry_sigma_abs "fst (sctx_entry_sol gs \<Gamma> is_bot_pred Pi ps mnm main)"
    "(cfg_exit (compile_prog \<Gamma> Pi ps mnm main), [])" sctx_entry_sg
    Seed
proof unfold_locales
  show "finite (intra (compile_prog \<Gamma> Pi ps mnm main))" by (rule sctx_entry_fin)
next
  show "part_post_solution
          (side_cfg_T_eff_keyed_seed_dg intra_predecessor_addr_list (\<lambda>_. Global)
             (formals_route_lifted_gen (sctx_abs_spec gs))
             (routed_cmb_g (sctx_abs_spec gs) Global Seed
                (static_resolve (compile_prog \<Gamma> Pi ps mnm main)))
             (routed_extra_g Seed Global)
             (compile_prog \<Gamma> Pi ps mnm main) (sctx_abs_spec gs)
             (map_lift (fun_of_resolved_st_q_for gs) (Bot::sign exec_dg_st lifted))
             (map_lift (fun_of_resolved_st_q_for gs) (Lifted cinit_sign_st))
             (map_lift (fun_of_resolved_st_q_for gs) (Bot::sign exec_dg_st lifted)))
          (cfg_exit (compile_prog \<Gamma> Pi ps mnm main), []) sctx_entry_sigma_abs
          (fst (sctx_entry_sol gs \<Gamma> is_bot_pred Pi ps mnm main))"
    unfolding sctx_entry_sigma_abs_def sctx_entry_sigma_abs_exec_def
    by (rule sctx_entry_pp_abs[OF solves exact])
next
  fix v ctx assume "(v, ctx) \<in> fst (sctx_entry_sol gs \<Gamma> is_bot_pred Pi ps mnm main)"
  thus "gamma_state_lift (sctx_entry_sg (Inl (v, ctx)))
          = gamma_dg_base (locals (sctx_entry_sigma_abs (Inl (v, ctx)))) (globs (sctx_entry_sigma_abs (Inr Global)))"
    by (simp add: sctx_entry_sg_covered gamma_dg_base_def)
next
  fix v ctx assume "(v, ctx) \<notin> fst (sctx_entry_sol gs \<Gamma> is_bot_pred Pi ps mnm main)"
  thus "gamma_state_lift (sctx_entry_sg (Inl (v, ctx))) = {}"
    by (rule sctx_entry_sg_uncovered_empty)
next
  fix u a v ctx assume "(u, ctx) \<in> fst (sctx_entry_sol gs \<Gamma> is_bot_pred Pi ps mnm main)" "(u, a, v) \<in> intra (compile_prog \<Gamma> Pi ps mnm main)"
  thus "(v, ctx) \<in> fst (sctx_entry_sol gs \<Gamma> is_bot_pred Pi ps mnm main)" by (rule fwd_ok)
next
  show "\<And>p ctx. Seed p ctx \<noteq> Global" by simp
next
  fix u ctx dst pars args p cont
  assume mem: "(u, ctx) \<in> fst (sctx_entry_sol gs \<Gamma> is_bot_pred Pi ps mnm main)"
    and ce: "(u, CallEdge dst pars args, FunctionEntry p, cont) \<in> calls (compile_prog \<Gamma> Pi ps mnm main)"
  show "(FunctionEntry p,
           formals_route_lifted_gen (sctx_abs_spec gs) u ctx
             (enter_local (sctx_abs_spec gs) pars args
                (locals (sctx_entry_sigma_abs (Inl (u, ctx))))
                (globs (sctx_entry_sigma_abs (Inr Global)))) (CallEdge dst pars args))
          \<in> fst (sctx_entry_sol gs \<Gamma> is_bot_pred Pi ps mnm main)"
    unfolding sctx_entry_sigma_abs_def
    using mem ce call_fwd_ok by blast
next
  fix cl c1 dst pars args p cont
  assume mem: "(cl, c1) \<in> fst (sctx_entry_sol gs \<Gamma> is_bot_pred Pi ps mnm main)"
    and ce: "(cl, CallEdge dst pars args, FunctionEntry p, cont) \<in> calls (compile_prog \<Gamma> Pi ps mnm main)"
  show "(cont, c1) \<in> fst (sctx_entry_sol gs \<Gamma> is_bot_pred Pi ps mnm main)"
    using mem ce by (rule comb_fwd_ok)
qed

lemma sctx_entry_locals_ge_s0d:
  "map_lift (fun_of_resolved_st_q_for gs) (Lifted cinit_sign_st)
     \<le> locals (sctx_entry_sigma_abs (Inl (cfg_entry (compile_prog \<Gamma> Pi ps mnm main), [])))"
proof -
  have "map_lift (fun_of_resolved_st_q_for gs) (Lifted cinit_sign_st)
      \<le> locals (eq sctx_entry_routed.Gen (cfg_entry (compile_prog \<Gamma> Pi ps mnm main), []) sctx_entry_sigma_abs)"
    by (simp add: eq_side_cfg_T_eff_keyed_seed_dg)
       (rule order_trans[OF _ side_acc_dg_ge_acc], simp add: le_supI2)
  also have "\<dots> \<le> locals (sctx_entry_sigma_abs (Inl (cfg_entry (compile_prog \<Gamma> Pi ps mnm main), [])))"
    using sctx_entry_routed.pp_eq_bound[OF entry_cov] by (simp add: less_eq_dg_state_def)
  finally show ?thesis .
qed

definition sctx_entry_enterc ::
    "cfg_node \<Rightarrow> sign list \<Rightarrow> store \<Rightarrow> sign list" where
  "sctx_entry_enterc = route_enterc_of_sigma (sctx_abs_spec gs)
     (formals_route_lifted_gen (sctx_abs_spec gs)) sctx_entry_sigma_abs Global
     (compile_prog \<Gamma> Pi ps mnm main)"

lemmas sctx_entry_routed_context_call =
  sctx_entry_routed.routed_context_call[folded sctx_entry_enterc_def]
lemmas sctx_entry_routed_context_comb =
  sctx_entry_routed.routed_context_comb[folded sctx_entry_enterc_def]

theorem sctx_entry_activation_collect_sound:
  "activation_collect \<Gamma> gs (admiss_exact sctx_entry_enterc) [] (compile_prog \<Gamma> Pi ps mnm main) (cinit_stores gs) v ctx
     \<subseteq> gamma_state_lift (sctx_entry_sg (Inl (v, ctx)))"
proof (rule activation_collect_sound_gen[where sg = sctx_entry_sg and gammaM = gamma_state_lift
        and admiss = "admiss_exact sctx_entry_enterc"
        and startcontext = "[]" and S = "cinit_stores gs" and g = "compile_prog \<Gamma> Pi ps mnm main" and gs = gs])
  fix s assume "s \<in> cinit_stores gs"
  hence "s \<in> gamma_state_lift (map_lift (fun_of_resolved_st_q_for gs) (Lifted cinit_sign_st))"
    using sctx_entry_cinit_le_cinit_sign_st by blast
  also have "gamma_state_lift (map_lift (fun_of_resolved_st_q_for gs) (Lifted cinit_sign_st))
        = gamma_dg_base (map_lift (fun_of_resolved_st_q_for gs) (Lifted cinit_sign_st))
            (map_lift (fun_of_resolved_st_q_for gs) (Bot::sign exec_dg_st lifted))"
    by (simp add: gamma_dg_base_def)
  also have "\<dots> \<subseteq> gamma_dg_base (locals (sctx_entry_sigma_abs (Inl (cfg_entry (compile_prog \<Gamma> Pi ps mnm main), []))))
                   (globs (sctx_entry_sigma_abs (Inr Global)))"
    by (rule gamma_dg_base_mono[OF sctx_entry_locals_ge_s0d sctx_entry_routed.pp_entry_s0g_bound[OF entry_cov]])
  also have "\<dots> = gamma_state_lift (sctx_entry_sg (Inl (cfg_entry (compile_prog \<Gamma> Pi ps mnm main), [])))"
    unfolding sctx_entry_sg_covered[OF entry_cov] gamma_dg_base_def by (rule refl)
  finally show "s \<in> gamma_state_lift (sctx_entry_sg (Inl (cfg_entry (compile_prog \<Gamma> Pi ps mnm main), [])))" .
next
  show "\<And>u a v c s s'. (u, a, v) \<in> intra (compile_prog \<Gamma> Pi ps mnm main)
        \<Longrightarrow> s \<in> gamma_state_lift (sctx_entry_sg (Inl (u, c))) \<Longrightarrow> s' \<in> edge_step a s
        \<Longrightarrow> s' \<in> gamma_state_lift (sctx_entry_sg (Inl (v, c)))"
    by (rule sctx_entry_routed.dg_ctx_act_edge)
next
  show "\<And>u c s. \<exists>c'. admiss_exact sctx_entry_enterc u c s c'"
    by (simp add: admiss_exact_def)
next
  fix u dst pars args p cont c s c'
  assume ce: "(u, CallEdge dst pars args, FunctionEntry p, cont) \<in> calls (compile_prog \<Gamma> Pi ps mnm main)"
    and sm: "s \<in> gamma_state_lift (sctx_entry_sg (Inl (u, c)))"
    and adm: "admiss_exact sctx_entry_enterc u c (call_enter gs (CallEdge dst pars args) s) c'"
  show "call_enter gs (CallEdge dst pars args) s \<in> gamma_state_lift (sctx_entry_sg (Inl (FunctionEntry p, c')))"
    using adm sctx_entry_routed_context_call[OF ce sm] by (simp add: admiss_exact_def)
next
  fix cl dst pars args p cont c1 c2 s t es
  assume ce: "(cl, CallEdge dst pars args, FunctionEntry p, cont) \<in> calls (compile_prog \<Gamma> Pi ps mnm main)"
    and sm: "s \<in> gamma_state_lift (sctx_entry_sg (Inl (cl, c1)))"
    and adm: "admiss_exact sctx_entry_enterc cl c1 es c2"
    and tm: "t \<in> gamma_state_lift (sctx_entry_sg (Inl (FunctionResult p, c2)))"
    and ces: "call_enter_store \<Gamma> gs (compile_prog \<Gamma> Pi ps mnm main) cl s es"  show "combine_collect gs dst s t \<in> gamma_state_lift (sctx_entry_sg (Inl (cont, c1)))"
    using adm tm sctx_entry_routed_context_comb[OF ce sm _ ces] by (simp add: admiss_exact_def)
qed

end

subsection \<open>Whole-program convenience layer\<close>

definition sctx_entry_eqs_prog ::
    "(vname \<Rightarrow> bool) \<Rightarrow> pname \<Rightarrow> imp_prog
       \<Rightarrow> (pp \<times> sign list, gk, (sign exec_dg_st lifted, sign exec_dg_st lifted) dg_state) eqsT" where
  "sctx_entry_eqs_prog gs mnm p =
     sctx_entry_eqs gs (prog_tyenv p) (resolved_st_q_is_bot_for (declared_global_vars p))
       (prog_table p) (prog_procs p) mnm (prog_main p)"

definition sctx_entry_sol_prog ::
    "(vname \<Rightarrow> bool) \<Rightarrow> pname \<Rightarrow> imp_prog
       \<Rightarrow> (pp \<times> sign list) set \<times> (pp \<times> sign list + gk \<Rightarrow> (sign exec_dg_st lifted, sign exec_dg_st lifted) dg_state)" where
  "sctx_entry_sol_prog gs mnm p =
     sctx_entry_sol gs (prog_tyenv p) (resolved_st_q_is_bot_for (declared_global_vars p))
       (prog_table p) (prog_procs p) mnm (prog_main p)"

definition sctx_entry_terminates_prog :: "(vname \<Rightarrow> bool) \<Rightarrow> pname \<Rightarrow> imp_prog \<Rightarrow> bool" where
  "sctx_entry_terminates_prog gs mnm p =
     sctx_entry_terminates gs (prog_tyenv p) (resolved_st_q_is_bot_for (declared_global_vars p))
       (prog_table p) (prog_procs p) mnm (prog_main p)"

lemma sctx_entry_terminates_prog_via_solve_c:
  assumes "TD_side_always_join_Interp_solve_c
             (sctx_entry_eqs_prog gs mnm p)
             (cfg_exit (compile_prog (prog_tyenv p) (prog_table p) (prog_procs p) mnm (prog_main p)), []) \<noteq> None"
  shows "sctx_entry_terminates_prog gs mnm p"
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
    "(vname \<Rightarrow> bool) \<Rightarrow> pname \<Rightarrow> imp_prog \<Rightarrow> (sign list, sign abs_state) analysis_result" where
  "analyse_sign_entry_state_result_for gs mnm p =
     Analysis_Result
       (fst (sctx_entry_sol_prog gs mnm p))
       (\<lambda>v ctx. normalize_point gs
                  (canonicalize_lift (resolved_st_q_is_bot_for (declared_global_vars p))
                    (locals (snd (sctx_entry_sol_prog gs mnm p) (Inl (v, ctx))))))"

declare analyse_sign_entry_state_result_for_def [code del]

lemma analyse_sign_entry_state_result_for_code [code]:
  "analyse_sign_entry_state_result_for gs mnm p =
     (let sol = sctx_entry_sol_prog gs mnm p; gl = declared_global_vars p
      in Analysis_Result (fst sol)
           (\<lambda>v ctx. normalize_point gs
                      (canonicalize_lift (resolved_st_q_is_bot_for gl)
                        (locals (snd sol (Inl (v, ctx)))))))"
  unfolding analyse_sign_entry_state_result_for_def Let_def by (rule refl)

text \<open>Convenience instance at \<^const>\<open>declared_global\<close> \<open>p\<close> and \<^const>\<open>prog_main_name\<close>,
  matching \<open>analyse_sign_call_string_result\<close>'s shape.\<close>

definition analyse_sign_entry_state_result :: "imp_prog \<Rightarrow> (sign list, sign abs_state) analysis_result" where
  "analyse_sign_entry_state_result p =
     analyse_sign_entry_state_result_for (declared_global p) prog_main_name p"

section \<open>Contextual check report\<close>

text \<open>
  Reuses \<^const>\<open>classify_checks_ctx\<close>/\<^const>\<open>classify_checks_verdicts\<close> unchanged --
  both are generic in the context type already, so nothing entry-state-specific is
  needed here beyond supplying the entry-state result table and Sign's own
  \<open>sign_classify_check\<close>.
\<close>

definition sctx_entry_check_projection ::
    "pname \<Rightarrow> imp_prog \<Rightarrow> (pp \<times> texp \<times> (sign list \<times> contextual_verdict) set) list" where
  "sctx_entry_check_projection mnm p =
     classify_checks_ctx (prog_cfg mnm p)
       (analyse_sign_entry_state_result_for (declared_global p) mnm p)
       sign_classify_check"

definition sctx_entry_verdict_report_prog ::
    "pname \<Rightarrow> imp_prog \<Rightarrow> (pp \<times> texp \<times> contextual_verdict) list" where
  "sctx_entry_verdict_report_prog mnm p =
     map (\<lambda>(u, c, vs). (u, c, aggregate_verdicts (snd ` vs)))
       (sctx_entry_check_projection mnm p)"

lemma sctx_entry_verdict_report_prog_eq:
  "sctx_entry_verdict_report_prog mnm p =
     classify_checks_verdicts (prog_cfg mnm p)
       (analyse_sign_entry_state_result_for (declared_global p) mnm p)
       sign_classify_check"
  unfolding sctx_entry_verdict_report_prog_def sctx_entry_check_projection_def
  by (rule classify_checks_verdicts_proj)

definition analyse_sign_entry_state_report :: "imp_prog \<Rightarrow> (pp \<times> texp \<times> contextual_verdict) list" where
  "analyse_sign_entry_state_report p = sctx_entry_verdict_report_prog prog_main_name p"

end

