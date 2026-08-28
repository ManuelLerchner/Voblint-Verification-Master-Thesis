theory Int_Ctx_Entry_State_Sound
  imports
    "Voblint_Analysis.Int_Ctx_None_Sound"
    "Voblint_Analysis.Int_Classify"
    "Voblint_Core.Entry_State_Routed_Context"
begin

section \<open>Int at the routed spine, instantiated at the entry-state context\<close>

text \<open>
  The entry-state sibling of Int's own routed-unit-context instance
  (\<^theory>\<open>Voblint_Analysis.Int_Ctx_None_Sound\<close>), and the fourth architecture-milestone
  acceptance test, after Sign's own call-string and entry-state derivations and Int's
  own call-string derivation: same \<^const>\<open>ictx_spec\<close>/\<^const>\<open>ictx_abs_spec\<close> D/G
  specification and the same domain-commute facts Int already interprets
  (\<^locale>\<open>routed_dg_domain_exec\<close>, \<^theory>\<open>Voblint_Core.DG_Base_Exec\<close>) -- nothing here
  re-derives them, and the \<^typ>\<open>refine_mode\<close> parameter Int threads throughout stays a
  genuine fixed argument exactly as it already is at Int's own \<^const>\<open>ictx_spec\<close>. The
  routing policy is the same generic entry-state construction
  (\<open>entry_exec_route_gen\<close>/\<^const>\<open>formals_route_lifted_gen\<close>,
  \<^theory>\<open>Voblint_Core.DG_Base_Exec\<close>/\<^theory>\<open>Voblint_Core.Routed_Context\<close>) Sign's own
  entry-state instance already uses: it needed only \<^locale>\<open>routed_dg_domain_exec\<close>'s
  own three primitive commute facts, which Int's own routed-unit instance has already
  established, so no new Int-domain mathematics is needed here either.
  \<^locale>\<open>entry_state_routed_context\<close> (\<^theory>\<open>Voblint_Core.Entry_State_Routed_Context\<close>) is
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
  \<open>entry_exec_route_gen\<close> (\<^theory>\<open>Voblint_Core.DG_Base_Exec\<close>), restated here as
  unconditional top-level definitions so the equation-system definitions below need no
  \<open>exact\<close> premise to be stated, matching every other routed instance's convention. The
  routed generator enters the callee frame before it routes, so the route itself only
  projects the formals out of the state it is handed.
\<close>

definition ictx_entry_route ::
    "refine_mode \<Rightarrow> (vname \<Rightarrow> bool) \<Rightarrow> (int_dom exec_dg_st \<Rightarrow> bool)
       \<Rightarrow> int_dom exec_dg_st lifted \<Rightarrow> call_action \<Rightarrow> int_dom list" where
  "ictx_entry_route mode gs is_bot_pred d ca =
     (case ca of CallEdge dst pars args \<Rightarrow>
        formals_context pars (fun_of_resolved_st_q_for gs
          (case d of Bot \<Rightarrow> bot | Lifted d0 \<Rightarrow> d0)))"

definition ictx_entry_route_gen ::
    "refine_mode \<Rightarrow> (vname \<Rightarrow> bool) \<Rightarrow> (int_dom exec_dg_st \<Rightarrow> bool)
       \<Rightarrow> pp \<Rightarrow> int_dom list \<Rightarrow> int_dom exec_dg_st lifted \<Rightarrow> call_action \<Rightarrow> int_dom list" where
  "ictx_entry_route_gen mode gs is_bot_pred u ctx d ca = ictx_entry_route mode gs is_bot_pred d ca"

subsection \<open>The routed equation system and its executable solution\<close>

definition ictx_entry_eqs ::
    "refine_mode \<Rightarrow> (vname \<Rightarrow> bool) \<Rightarrow> (int_dom exec_dg_st \<Rightarrow> bool) \<Rightarrow> proc_table \<Rightarrow> pname list
       \<Rightarrow> pname \<Rightarrow> com
       \<Rightarrow> (pp \<times> int_dom list, gk, (int_dom exec_dg_st lifted, int_dom exec_dg_st lifted) dg_state) eqsT" where
  "ictx_entry_eqs mode gs is_bot_pred Pi ps mnm main =
     side_cfg_T_eff_keyed_seed_dg_buffered intra_predecessor_addr_list (\<lambda>_. Global)
       (ictx_entry_route_gen mode gs is_bot_pred)
       (routed_cmb_g_contribution (ictx_spec mode is_bot_pred gs) Global Seed
          (static_resolve (compile_prog Pi ps mnm main)))
       (routed_extra_g Seed Global)
       (compile_prog Pi ps mnm main) (ictx_spec mode is_bot_pred gs) Bot (Lifted cinit_int_dom_st) Bot"

definition ictx_entry_sol ::
    "refine_mode \<Rightarrow> (vname \<Rightarrow> bool) \<Rightarrow> (int_dom exec_dg_st \<Rightarrow> bool) \<Rightarrow> proc_table \<Rightarrow> pname list
       \<Rightarrow> pname \<Rightarrow> com
       \<Rightarrow> (pp \<times> int_dom list) set \<times> (pp \<times> int_dom list + gk \<Rightarrow> (int_dom exec_dg_st lifted, int_dom exec_dg_st lifted) dg_state)" where
  "ictx_entry_sol mode gs is_bot_pred Pi ps mnm main =
     TD_side_always_join_Interp_solve (ictx_entry_eqs mode gs is_bot_pred Pi ps mnm main)
       (cfg_exit (compile_prog Pi ps mnm main), [])"

definition ictx_entry_terminates ::
    "refine_mode \<Rightarrow> (vname \<Rightarrow> bool) \<Rightarrow> (int_dom exec_dg_st \<Rightarrow> bool) \<Rightarrow> proc_table \<Rightarrow> pname list
       \<Rightarrow> pname \<Rightarrow> com \<Rightarrow> bool" where
  "ictx_entry_terminates mode gs is_bot_pred Pi ps mnm main =
     TD_side_always_join_Interp.solve_dom TYPE(gk) TYPE((int_dom exec_dg_st lifted, int_dom exec_dg_st lifted) dg_state)
       (ictx_entry_eqs mode gs is_bot_pred Pi ps mnm main) (cfg_exit (compile_prog Pi ps mnm main), [])"

lemma ictx_entry_terminates_via_solve_c:
  assumes "TD_side_always_join_Interp_solve_c (ictx_entry_eqs mode gs is_bot_pred Pi ps mnm main)
             (cfg_exit (compile_prog Pi ps mnm main), []) \<noteq> None"
  shows "ictx_entry_terminates mode gs is_bot_pred Pi ps mnm main"
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
       \<Rightarrow> pname \<Rightarrow> com
       \<Rightarrow> (pp \<times> int_dom list) set \<times> (pp \<times> int_dom list + gk \<Rightarrow> (int_dom exec_dg_st lifted, int_dom exec_dg_st lifted) dg_state)" where
  "ictx_entry_sol_warrow mode gs is_bot_pred Pi ps mnm main =
     TD_side_warrowing_apinis_Interp_solve (ictx_entry_eqs mode gs is_bot_pred Pi ps mnm main)
       (cfg_exit (compile_prog Pi ps mnm main), [])"

definition ictx_entry_terminates_warrow ::
    "refine_mode \<Rightarrow> (vname \<Rightarrow> bool) \<Rightarrow> (int_dom exec_dg_st \<Rightarrow> bool) \<Rightarrow> proc_table \<Rightarrow> pname list
       \<Rightarrow> pname \<Rightarrow> com \<Rightarrow> bool" where
  "ictx_entry_terminates_warrow mode gs is_bot_pred Pi ps mnm main =
     TD_side_warrowing_apinis_Interp.solve_dom TYPE(gk) TYPE((int_dom exec_dg_st lifted, int_dom exec_dg_st lifted) dg_state)
       (ictx_entry_eqs mode gs is_bot_pred Pi ps mnm main) (cfg_exit (compile_prog Pi ps mnm main), [])"

lemma ictx_entry_terminates_warrow_via_solve_c:
  assumes "TD_side_warrowing_apinis_Interp_solve_c (ictx_entry_eqs mode gs is_bot_pred Pi ps mnm main)
             (cfg_exit (compile_prog Pi ps mnm main), []) \<noteq> None"
  shows "ictx_entry_terminates_warrow mode gs is_bot_pred Pi ps mnm main"
  unfolding ictx_entry_terminates_warrow_def
  by (rule TD_side_warrowing_apinis_Interp.solve_dom_of_solve_c[OF assms])

subsection \<open>Route agreement: the one genuinely domain-specific commute fact\<close>

context
  fixes mode :: refine_mode and gs :: "vname \<Rightarrow> bool" and is_bot_pred :: "int_dom exec_dg_st \<Rightarrow> bool"
  assumes exact: "\<And>s. is_bot_pred s = is_bot_state (fun_of_resolved_st_q_for gs s)"
begin

interpretation int_domain: routed_dg_domain_exec
  gs is_bot_pred "int_tf_st_for mode gs" "int_dom_enter_st_for mode gs" "int_tf_for mode gs"
  by unfold_locales (rule int_tf_st_for_commute, rule int_dom_enter_st_for_commute, rule exact)

lemma ictx_entry_route_gen_eq_generic:
  "ictx_entry_route_gen mode gs is_bot_pred u ctx d ca = int_domain.entry_exec_route_gen u ctx d ca"
  unfolding ictx_entry_route_gen_def int_domain.entry_exec_route_gen_def
    ictx_entry_route_def int_domain.entry_exec_route_def
  by (rule refl)

lemma ictx_entry_route_gen_commute:
  "formals_route_lifted_gen (ictx_abs_spec mode gs) u ctx (map_lift (fun_of_resolved_st_q_for gs) d) ca
     = ictx_entry_route_gen mode gs is_bot_pred u ctx d ca"
  unfolding ictx_entry_route_gen_eq_generic ictx_abs_spec_def
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
    and is_bot_pred :: "int_dom exec_dg_st \<Rightarrow> bool"
  assumes exact: "\<And>s. is_bot_pred s = is_bot_state (fun_of_resolved_st_q_for gs s)"
begin

interpretation int_es: routed_domain_exec
  gs is_bot_pred "int_tf_st_for mode gs" "int_dom_enter_st_for mode gs" "int_tf_for mode gs"
  Global Seed "ictx_entry_route_gen mode gs is_bot_pred"
  "formals_route_lifted_gen (ictx_abs_spec mode gs)"
  static_resolve static_resolve
  by unfold_locales
     (rule int_tf_st_for_commute, rule int_dom_enter_st_for_commute, rule exact, simp,
      rule ictx_entry_route_gen_commute[OF exact, symmetric],
      simp add: static_resolve_def)

lemmas int_es_pp_abs_gen = int_es.pp_abs

end

subsection \<open>The certified executable post-solution, generic per compiled program\<close>

context
  fixes mode :: refine_mode and gs :: "vname \<Rightarrow> bool" and is_bot_pred :: "int_dom exec_dg_st \<Rightarrow> bool"
    and Pi :: proc_table and ps :: "pname list" and mnm :: pname and main :: com
  assumes solves: "ictx_entry_terminates mode gs is_bot_pred Pi ps mnm main"
    and exact: "\<And>s. is_bot_pred s = is_bot_state (fun_of_resolved_st_q_for gs s)"
begin

lemma ictx_entry_solve_dom:
  "TD_side_always_join_Interp.solve_dom TYPE(gk) TYPE((int_dom exec_dg_st lifted, int_dom exec_dg_st lifted) dg_state)
     (ictx_entry_eqs mode gs is_bot_pred Pi ps mnm main) (cfg_exit (compile_prog Pi ps mnm main), [])"
  using solves[unfolded ictx_entry_terminates_def] .

lemma ictx_entry_pp_st:
  "part_post_solution (ictx_entry_eqs mode gs is_bot_pred Pi ps mnm main) (cfg_exit (compile_prog Pi ps mnm main), [])
     (snd (ictx_entry_sol mode gs is_bot_pred Pi ps mnm main)) (fst (ictx_entry_sol mode gs is_bot_pred Pi ps mnm main))"
  using TD_side_always_join_Interp.partial_post_solution
          [OF ictx_entry_solve_dom, of "fst (ictx_entry_sol mode gs is_bot_pred Pi ps mnm main)"
             "snd (ictx_entry_sol mode gs is_bot_pred Pi ps mnm main)"]
  unfolding ictx_entry_sol_def by simp

theorem ictx_entry_pp_abs:
  "part_post_solution
     (side_cfg_T_eff_keyed_seed_dg intra_predecessor_addr_list (\<lambda>_. Global)
        (formals_route_lifted_gen (ictx_abs_spec mode gs))
        (routed_cmb_g (ictx_abs_spec mode gs) Global Seed
           (static_resolve (compile_prog Pi ps mnm main)))
        (routed_extra_g Seed Global)
        (compile_prog Pi ps mnm main) (ictx_abs_spec mode gs)
        (map_lift (fun_of_resolved_st_q_for gs) (Bot::int_dom exec_dg_st lifted))
        (map_lift (fun_of_resolved_st_q_for gs) (Lifted cinit_int_dom_st))
        (map_lift (fun_of_resolved_st_q_for gs) (Bot::int_dom exec_dg_st lifted)))
     (cfg_exit (compile_prog Pi ps mnm main), [])
     (fun_of_dg_st_gen (map_lift (fun_of_resolved_st_q_for gs)) (map_lift (fun_of_resolved_st_q_for gs))
        \<circ> snd (ictx_entry_sol mode gs is_bot_pred Pi ps mnm main))
     (fst (ictx_entry_sol mode gs is_bot_pred Pi ps mnm main))"
proof -
  have pp_buf: "part_post_solution
       (side_cfg_T_eff_keyed_seed_dg_buffered intra_predecessor_addr_list (\<lambda>_. Global)
          (ictx_entry_route_gen mode gs is_bot_pred)
          (routed_cmb_g_contribution (ictx_spec mode is_bot_pred gs) Global Seed
             (static_resolve (compile_prog Pi ps mnm main)))
          (routed_extra_g Seed Global)
          (compile_prog Pi ps mnm main) (ictx_spec mode is_bot_pred gs)
          Bot (Lifted cinit_int_dom_st) Bot)
       (cfg_exit (compile_prog Pi ps mnm main), [])
       (snd (ictx_entry_sol mode gs is_bot_pred Pi ps mnm main))
       (fst (ictx_entry_sol mode gs is_bot_pred Pi ps mnm main))"
    using ictx_entry_pp_st unfolding ictx_entry_eqs_def by simp
  show ?thesis
    using pp_buf unfolding ictx_spec_def
    by (rule int_es_pp_abs_gen[OF exact, folded ictx_abs_spec_def])
qed

end

subsection \<open>The certified executable post-solution under warrowing\<close>

context
  fixes mode :: refine_mode and gs :: "vname \<Rightarrow> bool" and is_bot_pred :: "int_dom exec_dg_st \<Rightarrow> bool"
    and Pi :: proc_table and ps :: "pname list" and mnm :: pname and main :: com
  assumes solves: "ictx_entry_terminates_warrow mode gs is_bot_pred Pi ps mnm main"
    and exact: "\<And>s. is_bot_pred s = is_bot_state (fun_of_resolved_st_q_for gs s)"
begin

lemma ictx_entry_solve_dom_warrow:
  "TD_side_warrowing_apinis_Interp.solve_dom TYPE(gk) TYPE((int_dom exec_dg_st lifted, int_dom exec_dg_st lifted) dg_state)
     (ictx_entry_eqs mode gs is_bot_pred Pi ps mnm main) (cfg_exit (compile_prog Pi ps mnm main), [])"
  using solves[unfolded ictx_entry_terminates_warrow_def] .

lemma ictx_entry_pp_st_warrow:
  "part_post_solution (ictx_entry_eqs mode gs is_bot_pred Pi ps mnm main) (cfg_exit (compile_prog Pi ps mnm main), [])
     (snd (ictx_entry_sol_warrow mode gs is_bot_pred Pi ps mnm main)) (fst (ictx_entry_sol_warrow mode gs is_bot_pred Pi ps mnm main))"
  using TD_side_warrowing_apinis_Interp.partial_post_solution
          [OF ictx_entry_solve_dom_warrow, of "fst (ictx_entry_sol_warrow mode gs is_bot_pred Pi ps mnm main)"
             "snd (ictx_entry_sol_warrow mode gs is_bot_pred Pi ps mnm main)"]
  unfolding ictx_entry_sol_warrow_def by simp

theorem ictx_entry_pp_abs_warrow:
  "part_post_solution
     (side_cfg_T_eff_keyed_seed_dg intra_predecessor_addr_list (\<lambda>_. Global)
        (formals_route_lifted_gen (ictx_abs_spec mode gs))
        (routed_cmb_g (ictx_abs_spec mode gs) Global Seed
           (static_resolve (compile_prog Pi ps mnm main)))
        (routed_extra_g Seed Global)
        (compile_prog Pi ps mnm main) (ictx_abs_spec mode gs)
        (map_lift (fun_of_resolved_st_q_for gs) (Bot::int_dom exec_dg_st lifted))
        (map_lift (fun_of_resolved_st_q_for gs) (Lifted cinit_int_dom_st))
        (map_lift (fun_of_resolved_st_q_for gs) (Bot::int_dom exec_dg_st lifted)))
     (cfg_exit (compile_prog Pi ps mnm main), [])
     (fun_of_dg_st_gen (map_lift (fun_of_resolved_st_q_for gs)) (map_lift (fun_of_resolved_st_q_for gs))
        \<circ> snd (ictx_entry_sol_warrow mode gs is_bot_pred Pi ps mnm main))
     (fst (ictx_entry_sol_warrow mode gs is_bot_pred Pi ps mnm main))"
proof -
  have pp_buf: "part_post_solution
       (side_cfg_T_eff_keyed_seed_dg_buffered intra_predecessor_addr_list (\<lambda>_. Global)
          (ictx_entry_route_gen mode gs is_bot_pred)
          (routed_cmb_g_contribution (ictx_spec mode is_bot_pred gs) Global Seed
             (static_resolve (compile_prog Pi ps mnm main)))
          (routed_extra_g Seed Global)
          (compile_prog Pi ps mnm main) (ictx_spec mode is_bot_pred gs)
          Bot (Lifted cinit_int_dom_st) Bot)
       (cfg_exit (compile_prog Pi ps mnm main), [])
       (snd (ictx_entry_sol_warrow mode gs is_bot_pred Pi ps mnm main))
       (fst (ictx_entry_sol_warrow mode gs is_bot_pred Pi ps mnm main))"
    using ictx_entry_pp_st_warrow unfolding ictx_entry_eqs_def by simp
  show ?thesis
    using pp_buf unfolding ictx_spec_def
    by (rule int_es_pp_abs_gen[OF exact, folded ictx_abs_spec_def])
qed

end

section \<open>Activation-indexed collecting soundness, generic per compiled program\<close>

text \<open>
  Executable twins of the context's own \<open>ictx_entry_sigma_abs\<close>/\<open>ictx_entry_sg\<close>
  (below), defined before that context so their equations are unconditional -- mirrors
  Sign's own \<open>sctx_entry_sigma_abs_exec\<close>/\<open>sctx_entry_sg_exec\<close> convention exactly.
\<close>

definition ictx_entry_sigma_abs_exec ::
    "refine_mode \<Rightarrow> (vname \<Rightarrow> bool) \<Rightarrow> (int_dom exec_dg_st \<Rightarrow> bool) \<Rightarrow> proc_table \<Rightarrow> pname list \<Rightarrow> pname \<Rightarrow> com
       \<Rightarrow> pp \<times> int_dom list + gk \<Rightarrow> (int_dom abs_state lifted, int_dom abs_state lifted) dg_state" where
  "ictx_entry_sigma_abs_exec mode gs is_bot_pred Pi ps mnm main =
     fun_of_dg_st_gen (map_lift (fun_of_resolved_st_q_for gs)) (map_lift (fun_of_resolved_st_q_for gs))
       \<circ> snd (ictx_entry_sol mode gs is_bot_pred Pi ps mnm main)"

definition ictx_entry_sg_exec ::
    "refine_mode \<Rightarrow> (vname \<Rightarrow> bool) \<Rightarrow> (int_dom exec_dg_st \<Rightarrow> bool) \<Rightarrow> proc_table \<Rightarrow> pname list \<Rightarrow> pname \<Rightarrow> com
       \<Rightarrow> pp \<times> int_dom list + gk \<Rightarrow> int_dom abs_state lifted" where
  "ictx_entry_sg_exec mode gs is_bot_pred Pi ps mnm main k =
     (case k of
        Inl (v, ctx) \<Rightarrow>
          (if (v, ctx) \<in> fst (ictx_entry_sol mode gs is_bot_pred Pi ps mnm main)
           then locals (ictx_entry_sigma_abs_exec mode gs is_bot_pred Pi ps mnm main (Inl (v, ctx)))
           else Bot)
      | Inr _ \<Rightarrow> Bot)"

context
  fixes mode :: refine_mode and gs :: "vname \<Rightarrow> bool" and is_bot_pred :: "int_dom exec_dg_st \<Rightarrow> bool"
    and Pi :: proc_table and ps :: "pname list" and mnm :: pname and main :: com
  assumes solves: "ictx_entry_terminates mode gs is_bot_pred Pi ps mnm main"
    and exact: "\<And>s. is_bot_pred s = is_bot_state (fun_of_resolved_st_q_for gs s)"
    and entry_cov: "(cfg_entry (compile_prog Pi ps mnm main), []) \<in> fst (ictx_entry_sol mode gs is_bot_pred Pi ps mnm main)"
    and fwd_ok: "\<And>u a v ctx. (u, ctx) \<in> fst (ictx_entry_sol mode gs is_bot_pred Pi ps mnm main)
                    \<Longrightarrow> (u, a, v) \<in> intra (compile_prog Pi ps mnm main)
                    \<Longrightarrow> (v, ctx) \<in> fst (ictx_entry_sol mode gs is_bot_pred Pi ps mnm main)"
    and call_fwd_ok: "\<And>u ctx dst pars args p cont.
        (u, ctx) \<in> fst (ictx_entry_sol mode gs is_bot_pred Pi ps mnm main)
        \<Longrightarrow> (u, CallEdge dst pars args, FunctionEntry p, cont) \<in> calls (compile_prog Pi ps mnm main)
        \<Longrightarrow> (FunctionEntry p,
               formals_route_lifted_gen (ictx_abs_spec mode gs) u ctx
                 (enter_local (ictx_abs_spec mode gs) pars args
                    (locals (ictx_entry_sigma_abs_exec mode gs is_bot_pred Pi ps mnm main (Inl (u, ctx))))
                    (globs (ictx_entry_sigma_abs_exec mode gs is_bot_pred Pi ps mnm main (Inr Global))))
                 (CallEdge dst pars args))
             \<in> fst (ictx_entry_sol mode gs is_bot_pred Pi ps mnm main)"
    and comb_fwd_ok: "\<And>cl c1 dst pars args p cont.
        (cl, c1) \<in> fst (ictx_entry_sol mode gs is_bot_pred Pi ps mnm main)
        \<Longrightarrow> (cl, CallEdge dst pars args, FunctionEntry p, cont) \<in> calls (compile_prog Pi ps mnm main)
        \<Longrightarrow> (cont, c1) \<in> fst (ictx_entry_sol mode gs is_bot_pred Pi ps mnm main)"
begin

subsection \<open>The semantic solution projection\<close>

definition ictx_entry_sigma_abs :: "pp \<times> int_dom list + gk \<Rightarrow> (int_dom abs_state lifted, int_dom abs_state lifted) dg_state" where
  "ictx_entry_sigma_abs = ictx_entry_sigma_abs_exec mode gs is_bot_pred Pi ps mnm main"

definition ictx_entry_sg :: "pp \<times> int_dom list + gk \<Rightarrow> int_dom abs_state lifted" where
  "ictx_entry_sg = ictx_entry_sg_exec mode gs is_bot_pred Pi ps mnm main"

lemma ictx_entry_fin: "finite (intra (compile_prog Pi ps mnm main))"
  using compile_prog_finite by blast

lemma ictx_entry_finC: "finite (calls (compile_prog Pi ps mnm main))"
  using compile_prog_finite by blast

lemma ictx_entry_sg_covered:
  "(v, ctx) \<in> fst (ictx_entry_sol mode gs is_bot_pred Pi ps mnm main)
   \<Longrightarrow> ictx_entry_sg (Inl (v, ctx)) = locals (ictx_entry_sigma_abs (Inl (v, ctx)))"
  by (simp add: ictx_entry_sg_def ictx_entry_sg_exec_def ictx_entry_sigma_abs_def ictx_entry_sigma_abs_exec_def)

lemma ictx_entry_sg_uncovered_empty:
  "(v, ctx) \<notin> fst (ictx_entry_sol mode gs is_bot_pred Pi ps mnm main)
     \<Longrightarrow> gamma_state_lift (ictx_entry_sg (Inl (v, ctx))) = {}"
  by (simp add: ictx_entry_sg_def ictx_entry_sg_exec_def)

subsection \<open>Instantiating the generic routed-context locale\<close>

interpretation ictx_entry_dg_base: sound_dg_spec "ictx_abs_spec mode gs" gamma_dg_base gs
  by (rule ictx_abs_spec_sound)

interpretation ictx_entry_routed: entry_state_routed_context "ictx_abs_spec mode gs" gs
    Pi ps mnm main Global
    "map_lift (fun_of_resolved_st_q_for gs) (Bot::int_dom exec_dg_st lifted)"
    "map_lift (fun_of_resolved_st_q_for gs) (Lifted cinit_int_dom_st)"
    "map_lift (fun_of_resolved_st_q_for gs) (Bot::int_dom exec_dg_st lifted)"
    ictx_entry_sigma_abs "fst (ictx_entry_sol mode gs is_bot_pred Pi ps mnm main)"
    "(cfg_exit (compile_prog Pi ps mnm main), [])" ictx_entry_sg
    Seed
proof unfold_locales
  show "finite (intra (compile_prog Pi ps mnm main))" by (rule ictx_entry_fin)
next
  show "part_post_solution
          (side_cfg_T_eff_keyed_seed_dg intra_predecessor_addr_list (\<lambda>_. Global)
             (formals_route_lifted_gen (ictx_abs_spec mode gs))
             (routed_cmb_g (ictx_abs_spec mode gs) Global Seed
                (static_resolve (compile_prog Pi ps mnm main)))
             (routed_extra_g Seed Global)
             (compile_prog Pi ps mnm main) (ictx_abs_spec mode gs)
             (map_lift (fun_of_resolved_st_q_for gs) (Bot::int_dom exec_dg_st lifted))
             (map_lift (fun_of_resolved_st_q_for gs) (Lifted cinit_int_dom_st))
             (map_lift (fun_of_resolved_st_q_for gs) (Bot::int_dom exec_dg_st lifted)))
          (cfg_exit (compile_prog Pi ps mnm main), []) ictx_entry_sigma_abs
          (fst (ictx_entry_sol mode gs is_bot_pred Pi ps mnm main))"
    unfolding ictx_entry_sigma_abs_def ictx_entry_sigma_abs_exec_def
    by (rule ictx_entry_pp_abs[OF solves exact])
next
  fix v ctx assume "(v, ctx) \<in> fst (ictx_entry_sol mode gs is_bot_pred Pi ps mnm main)"
  thus "gamma_state_lift (ictx_entry_sg (Inl (v, ctx)))
          = gamma_dg_base (locals (ictx_entry_sigma_abs (Inl (v, ctx)))) (globs (ictx_entry_sigma_abs (Inr Global)))"
    by (simp add: ictx_entry_sg_covered gamma_dg_base_def)
next
  fix v ctx assume "(v, ctx) \<notin> fst (ictx_entry_sol mode gs is_bot_pred Pi ps mnm main)"
  thus "gamma_state_lift (ictx_entry_sg (Inl (v, ctx))) = {}"
    by (rule ictx_entry_sg_uncovered_empty)
next
  fix u a v ctx assume "(u, ctx) \<in> fst (ictx_entry_sol mode gs is_bot_pred Pi ps mnm main)" "(u, a, v) \<in> intra (compile_prog Pi ps mnm main)"
  thus "(v, ctx) \<in> fst (ictx_entry_sol mode gs is_bot_pred Pi ps mnm main)" by (rule fwd_ok)
next
  show "\<And>p ctx. Seed p ctx \<noteq> Global" by simp
next
  fix u ctx dst pars args p cont
  assume mem: "(u, ctx) \<in> fst (ictx_entry_sol mode gs is_bot_pred Pi ps mnm main)"
    and ce: "(u, CallEdge dst pars args, FunctionEntry p, cont) \<in> calls (compile_prog Pi ps mnm main)"
  show "(FunctionEntry p,
           formals_route_lifted_gen (ictx_abs_spec mode gs) u ctx
             (enter_local (ictx_abs_spec mode gs) pars args
                (locals (ictx_entry_sigma_abs (Inl (u, ctx))))
                (globs (ictx_entry_sigma_abs (Inr Global)))) (CallEdge dst pars args))
          \<in> fst (ictx_entry_sol mode gs is_bot_pred Pi ps mnm main)"
    unfolding ictx_entry_sigma_abs_def
    using mem ce call_fwd_ok by blast
next
  fix cl c1 dst pars args p cont
  assume mem: "(cl, c1) \<in> fst (ictx_entry_sol mode gs is_bot_pred Pi ps mnm main)"
    and ce: "(cl, CallEdge dst pars args, FunctionEntry p, cont) \<in> calls (compile_prog Pi ps mnm main)"
  show "(cont, c1) \<in> fst (ictx_entry_sol mode gs is_bot_pred Pi ps mnm main)"
    using mem ce by (rule comb_fwd_ok)
qed

subsection \<open>Activation-indexed collecting soundness\<close>

lemma ictx_entry_cinit_le_cinit_int_dom_st:
  "cinit_stores gs \<subseteq> gamma_state_lift (map_lift (fun_of_resolved_st_q_for gs) (Lifted cinit_int_dom_st))"
  by (auto simp: cinit_stores_def gamma_state_def fun_of_resolved_st_q_for_def fun_of_st_cinit_int_dom_st_for
                 gamma_int_dom_top)

lemma ictx_entry_locals_ge_s0d:
  "map_lift (fun_of_resolved_st_q_for gs) (Lifted cinit_int_dom_st)
     \<le> locals (ictx_entry_sigma_abs (Inl (cfg_entry (compile_prog Pi ps mnm main), [])))"
proof -
  have "map_lift (fun_of_resolved_st_q_for gs) (Lifted cinit_int_dom_st)
      \<le> locals (eq ictx_entry_routed.Gen (cfg_entry (compile_prog Pi ps mnm main), []) ictx_entry_sigma_abs)"
    by (simp add: eq_side_cfg_T_eff_keyed_seed_dg)
       (rule order_trans[OF _ side_acc_dg_ge_acc], simp add: le_supI2)
  also have "\<dots> \<le> locals (ictx_entry_sigma_abs (Inl (cfg_entry (compile_prog Pi ps mnm main), [])))"
    using ictx_entry_routed.pp_eq_bound[OF entry_cov] by (simp add: less_eq_dg_state_def)
  finally show ?thesis .
qed

definition ictx_entry_enterc ::
    "cfg_node \<Rightarrow> int_dom list \<Rightarrow> store \<Rightarrow> int_dom list" where
  "ictx_entry_enterc = route_enterc_of_sigma (ictx_abs_spec mode gs)
     (formals_route_lifted_gen (ictx_abs_spec mode gs)) ictx_entry_sigma_abs Global
     (compile_prog Pi ps mnm main)"

lemmas ictx_entry_routed_context_call =
  ictx_entry_routed.routed_context_call[folded ictx_entry_enterc_def]
lemmas ictx_entry_routed_context_comb =
  ictx_entry_routed.routed_context_comb[folded ictx_entry_enterc_def]

theorem ictx_entry_activation_collect_sound:
  "activation_collect gs ictx_entry_enterc [] (compile_prog Pi ps mnm main) (cinit_stores gs) v ctx
     \<subseteq> gamma_state_lift (ictx_entry_sg (Inl (v, ctx)))"
proof (rule activation_collect_sound_gen[where sg = ictx_entry_sg and gammaM = gamma_state_lift
        and enterc = "ictx_entry_enterc"
        and startcontext = "[]" and S = "cinit_stores gs" and g = "compile_prog Pi ps mnm main" and gs = gs])
  fix s assume "s \<in> cinit_stores gs"
  hence "s \<in> gamma_state_lift (map_lift (fun_of_resolved_st_q_for gs) (Lifted cinit_int_dom_st))"
    using ictx_entry_cinit_le_cinit_int_dom_st by blast
  also have "gamma_state_lift (map_lift (fun_of_resolved_st_q_for gs) (Lifted cinit_int_dom_st))
        = gamma_dg_base (map_lift (fun_of_resolved_st_q_for gs) (Lifted cinit_int_dom_st))
            (map_lift (fun_of_resolved_st_q_for gs) (Bot::int_dom exec_dg_st lifted))"
    by (simp add: gamma_dg_base_def)
  also have "\<dots> \<subseteq> gamma_dg_base (locals (ictx_entry_sigma_abs (Inl (cfg_entry (compile_prog Pi ps mnm main), []))))
                   (globs (ictx_entry_sigma_abs (Inr Global)))"
    by (rule gamma_dg_base_mono[OF ictx_entry_locals_ge_s0d ictx_entry_routed.pp_entry_s0g_bound[OF entry_cov]])
  also have "\<dots> = gamma_state_lift (ictx_entry_sg (Inl (cfg_entry (compile_prog Pi ps mnm main), [])))"
    unfolding ictx_entry_sg_covered[OF entry_cov] gamma_dg_base_def by (rule refl)
  finally show "s \<in> gamma_state_lift (ictx_entry_sg (Inl (cfg_entry (compile_prog Pi ps mnm main), [])))" .
next
  show "\<And>u a v c s s'. (u, a, v) \<in> intra (compile_prog Pi ps mnm main)
        \<Longrightarrow> s \<in> gamma_state_lift (ictx_entry_sg (Inl (u, c))) \<Longrightarrow> s' \<in> edge_step a s
        \<Longrightarrow> s' \<in> gamma_state_lift (ictx_entry_sg (Inl (v, c)))"
    by (rule ictx_entry_routed.dg_ctx_act_edge)
next
  fix u dst pars args p cont c s
  assume ce: "(u, CallEdge dst pars args, FunctionEntry p, cont) \<in> calls (compile_prog Pi ps mnm main)"
    and sm: "s \<in> gamma_state_lift (ictx_entry_sg (Inl (u, c)))"
  show "call_enter gs (CallEdge dst pars args) s
          \<in> gamma_state_lift
              (ictx_entry_sg (Inl (FunctionEntry p, ictx_entry_enterc u c (call_enter gs (CallEdge dst pars args) s))))"
    using ictx_entry_routed_context_call[OF ce sm] .
next
  fix cl dst pars args p cont c1 s t es
  assume ce: "(cl, CallEdge dst pars args, FunctionEntry p, cont) \<in> calls (compile_prog Pi ps mnm main)"
    and sm: "s \<in> gamma_state_lift (ictx_entry_sg (Inl (cl, c1)))"
    and tm: "t \<in> gamma_state_lift (ictx_entry_sg (Inl (FunctionResult p, ictx_entry_enterc cl c1 es)))"
    and ces: "call_enter_store gs (compile_prog Pi ps mnm main) cl s es"
  show "combine_collect gs dst s t \<in> gamma_state_lift (ictx_entry_sg (Inl (cont, c1)))"
    using tm ictx_entry_routed_context_comb[OF ce sm _ ces] by blast
qed

end

subsection \<open>Whole-program convenience layer\<close>

text \<open>
  Fixed at \<^const>\<open>Refine_Fixpoint\<close>, matching Int's own production default and Int's
  own call-string instance's posture: \<open>mode\<close> stays a genuine parameter through every
  lemma above, and is only pinned here where the public, config-driven surface needs
  one concrete choice.
\<close>

definition ictx_entry_eqs_prog ::
    "(vname \<Rightarrow> bool) \<Rightarrow> pname \<Rightarrow> imp_prog
       \<Rightarrow> (pp \<times> int_dom list, gk, (int_dom exec_dg_st lifted, int_dom exec_dg_st lifted) dg_state) eqsT" where
  "ictx_entry_eqs_prog gs mnm p =
     ictx_entry_eqs Refine_Fixpoint gs (resolved_st_q_is_bot_for (declared_global_vars p))
       (prog_table p) (prog_procs p) mnm (prog_main p)"

definition ictx_entry_sol_prog ::
    "(vname \<Rightarrow> bool) \<Rightarrow> pname \<Rightarrow> imp_prog
       \<Rightarrow> (pp \<times> int_dom list) set \<times> (pp \<times> int_dom list + gk \<Rightarrow> (int_dom exec_dg_st lifted, int_dom exec_dg_st lifted) dg_state)" where
  "ictx_entry_sol_prog gs mnm p =
     ictx_entry_sol Refine_Fixpoint gs (resolved_st_q_is_bot_for (declared_global_vars p))
       (prog_table p) (prog_procs p) mnm (prog_main p)"

definition ictx_entry_terminates_prog :: "(vname \<Rightarrow> bool) \<Rightarrow> pname \<Rightarrow> imp_prog \<Rightarrow> bool" where
  "ictx_entry_terminates_prog gs mnm p =
     ictx_entry_terminates Refine_Fixpoint gs (resolved_st_q_is_bot_for (declared_global_vars p))
       (prog_table p) (prog_procs p) mnm (prog_main p)"

lemma ictx_entry_terminates_prog_via_solve_c:
  assumes "TD_side_always_join_Interp_solve_c
             (ictx_entry_eqs_prog gs mnm p)
             (cfg_exit (compile_prog (prog_table p) (prog_procs p) mnm (prog_main p)), []) \<noteq> None"
  shows "ictx_entry_terminates_prog gs mnm p"
  using assms
  unfolding ictx_entry_terminates_prog_def ictx_entry_eqs_prog_def
  by (rule ictx_entry_terminates_via_solve_c)

definition ictx_entry_sol_prog_warrow ::
    "(vname \<Rightarrow> bool) \<Rightarrow> pname \<Rightarrow> imp_prog
       \<Rightarrow> (pp \<times> int_dom list) set \<times> (pp \<times> int_dom list + gk \<Rightarrow> (int_dom exec_dg_st lifted, int_dom exec_dg_st lifted) dg_state)" where
  "ictx_entry_sol_prog_warrow gs mnm p =
     ictx_entry_sol_warrow Refine_Fixpoint gs (resolved_st_q_is_bot_for (declared_global_vars p))
       (prog_table p) (prog_procs p) mnm (prog_main p)"

definition ictx_entry_terminates_prog_warrow :: "(vname \<Rightarrow> bool) \<Rightarrow> pname \<Rightarrow> imp_prog \<Rightarrow> bool" where
  "ictx_entry_terminates_prog_warrow gs mnm p =
     ictx_entry_terminates_warrow Refine_Fixpoint gs (resolved_st_q_is_bot_for (declared_global_vars p))
       (prog_table p) (prog_procs p) mnm (prog_main p)"

lemma ictx_entry_terminates_prog_warrow_via_solve_c:
  assumes "TD_side_warrowing_apinis_Interp_solve_c
             (ictx_entry_eqs_prog gs mnm p)
             (cfg_exit (compile_prog (prog_table p) (prog_procs p) mnm (prog_main p)), []) \<noteq> None"
  shows "ictx_entry_terminates_prog_warrow gs mnm p"
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
    "(vname \<Rightarrow> bool) \<Rightarrow> pname \<Rightarrow> imp_prog \<Rightarrow> (int_dom list, int_dom abs_state) analysis_result" where
  "analyse_int_entry_state_result_for gs mnm p =
     Analysis_Result
       (fst (ictx_entry_sol_prog gs mnm p))
       (\<lambda>v ctx. normalize_point gs
                  (canonicalize_lift (resolved_st_q_is_bot_for (declared_global_vars p))
                    (locals (snd (ictx_entry_sol_prog gs mnm p) (Inl (v, ctx))))))"

declare analyse_int_entry_state_result_for_def [code del]

lemma analyse_int_entry_state_result_for_code [code]:
  "analyse_int_entry_state_result_for gs mnm p =
     (let sol = ictx_entry_sol_prog gs mnm p; gl = declared_global_vars p
      in Analysis_Result (fst sol)
           (\<lambda>v ctx. normalize_point gs
                      (canonicalize_lift (resolved_st_q_is_bot_for gl)
                        (locals (snd sol (Inl (v, ctx)))))))"
  unfolding analyse_int_entry_state_result_for_def Let_def by (rule refl)

text \<open>Convenience instance at \<^const>\<open>declared_global\<close> \<open>p\<close> and \<^const>\<open>prog_main_name\<close>,
  matching \<open>analyse_int_call_string_result\<close>'s shape.\<close>

definition analyse_int_entry_state_result :: "imp_prog \<Rightarrow> (int_dom list, int_dom abs_state) analysis_result" where
  "analyse_int_entry_state_result p =
     analyse_int_entry_state_result_for (declared_global p) prog_main_name p"

section \<open>Contextual check report\<close>

text \<open>
  Reuses \<^const>\<open>classify_checks_ctx\<close>/\<^const>\<open>classify_checks_verdicts\<close> unchanged --
  both are generic in the context type already, so nothing entry-state-specific is
  needed here beyond supplying the entry-state result table and Int's own
  \<^const>\<open>int_classify_check\<close>.
\<close>

definition ictx_entry_check_projection ::
    "pname \<Rightarrow> imp_prog \<Rightarrow> (pp \<times> exp \<times> (int_dom list \<times> contextual_verdict) set) list" where
  "ictx_entry_check_projection mnm p =
     classify_checks_ctx (prog_cfg mnm p)
       (analyse_int_entry_state_result_for (declared_global p) mnm p)
       int_classify_check"

definition ictx_entry_verdict_report_prog ::
    "pname \<Rightarrow> imp_prog \<Rightarrow> (pp \<times> exp \<times> contextual_verdict) list" where
  "ictx_entry_verdict_report_prog mnm p =
     map (\<lambda>(u, c, vs). (u, c, aggregate_verdicts (snd ` vs)))
       (ictx_entry_check_projection mnm p)"

lemma ictx_entry_verdict_report_prog_eq:
  "ictx_entry_verdict_report_prog mnm p =
     classify_checks_verdicts (prog_cfg mnm p)
       (analyse_int_entry_state_result_for (declared_global p) mnm p)
       int_classify_check"
  unfolding ictx_entry_verdict_report_prog_def ictx_entry_check_projection_def
  by (rule classify_checks_verdicts_proj)

definition analyse_int_entry_state_report :: "imp_prog \<Rightarrow> (pp \<times> exp \<times> contextual_verdict) list" where
  "analyse_int_entry_state_report p = ictx_entry_verdict_report_prog prog_main_name p"

subsection \<open>Result table and report under warrowing\<close>

definition analyse_int_entry_state_result_for_warrow ::
    "(vname \<Rightarrow> bool) \<Rightarrow> pname \<Rightarrow> imp_prog \<Rightarrow> (int_dom list, int_dom abs_state) analysis_result" where
  "analyse_int_entry_state_result_for_warrow gs mnm p =
     Analysis_Result
       (fst (ictx_entry_sol_prog_warrow gs mnm p))
       (\<lambda>v ctx. normalize_point gs
                  (canonicalize_lift (resolved_st_q_is_bot_for (declared_global_vars p))
                    (locals (snd (ictx_entry_sol_prog_warrow gs mnm p) (Inl (v, ctx))))))"

declare analyse_int_entry_state_result_for_warrow_def [code del]

lemma analyse_int_entry_state_result_for_warrow_code [code]:
  "analyse_int_entry_state_result_for_warrow gs mnm p =
     (let sol = ictx_entry_sol_prog_warrow gs mnm p; gl = declared_global_vars p
      in Analysis_Result (fst sol)
           (\<lambda>v ctx. normalize_point gs
                      (canonicalize_lift (resolved_st_q_is_bot_for gl)
                        (locals (snd sol (Inl (v, ctx)))))))"
  unfolding analyse_int_entry_state_result_for_warrow_def Let_def by (rule refl)

definition analyse_int_entry_state_result_warrow ::
    "imp_prog \<Rightarrow> (int_dom list, int_dom abs_state) analysis_result" where
  "analyse_int_entry_state_result_warrow p =
     analyse_int_entry_state_result_for_warrow (declared_global p) prog_main_name p"

definition ictx_entry_verdict_report_prog_warrow ::
    "pname \<Rightarrow> imp_prog \<Rightarrow> (pp \<times> exp \<times> contextual_verdict) list" where
  "ictx_entry_verdict_report_prog_warrow mnm p =
     classify_checks_verdicts (prog_cfg mnm p)
       (analyse_int_entry_state_result_for_warrow (declared_global p) mnm p)
       int_classify_check"

definition analyse_int_entry_state_report_warrow ::
    "imp_prog \<Rightarrow> (pp \<times> exp \<times> contextual_verdict) list" where
  "analyse_int_entry_state_report_warrow p = ictx_entry_verdict_report_prog_warrow prog_main_name p"

end
