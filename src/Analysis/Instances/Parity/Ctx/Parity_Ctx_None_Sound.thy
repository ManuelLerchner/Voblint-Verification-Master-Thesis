theory Parity_Ctx_None_Sound
  imports
    "Voblint_Core.Exec_DG_Bridge"
    "Voblint_Core.Routed_Domain_Exec"
    "Voblint_Analysis.Parity_Base_DG"
    "Voblint_Analysis.Parity_Exec"
    "Voblint_CFG.Compile_Invariants"
    "Voblint_CFG.CFG_Prune"
    "Voblint_Core.Solver_Side_RG"
    "TD.TD_side_upd_rule"
    "Voblint_Core.Routed_Context"
    "Voblint_Core.Routed_Context_Unit"
    "Voblint_Core.Solver_Menu"
    "Voblint_Core.Analysis_Result"
    "Voblint_VIMP.VIMP_Notation"
    "Voblint_Core.Activation_Backbone"
begin

section \<open>Parity at the routed spine, instantiated at the unit context\<close>

text \<open>
  Parity's routed-unit-context instance, the fourth domain on the shared spine after
  Sign, Interval and Int. It is also the architecture's own extensibility test: Parity
  arrived with a complete domain stack --- lattice, transfer, numeric queries, checks,
  a D/G specification and executable soundness --- but no routed-capability bridge, so
  what this file needs to supply is exactly the measure of how much a mature domain
  still owes the framework.

  The answer is: the two primitive commute facts it already had.
  \<^const>\<open>parity_tf_st_for\<close>/\<^const>\<open>parity_enter_st_for\<close>'s own
  \<open>parity_tf_st_for_commute\<close>/\<open>parity_enter_st_for_commute\<close>
  (\<^theory>\<open>Voblint_Analysis.Parity_Exec\<close>) already have precisely the shape
  \<^locale>\<open>routed_dg_domain_exec\<close> assumes, so the interpretation below discharges by
  citing them, and every Hstep/Henter/Hcomb fact the routed spine needs follows from the
  locale rather than from new Parity mathematics. Nothing in this file reasons about
  parity arithmetic at all.
\<close>

subsection \<open>Global key: real globals vs callee-entry seed slots\<close>

datatype gk = Global | Seed (seed_pp: pp) (seed_ctx: unit)

subsection \<open>The routed unit-context D/G spec\<close>

text \<open>
  A Base-style whole-state specification over
  \<^const>\<open>parity_tf_st_for\<close>/\<^const>\<open>parity_enter_st_for\<close>
  (\<^theory>\<open>Voblint_Analysis.Parity_Exec\<close>): the routed generator wraps around the
  spec, and every domain-transfer soundness fact about the spec is untouched by
  that wrapping.
\<close>

definition pctx_spec ::
  "(vname \<Rightarrow> bool) \<Rightarrow> (parity exec_dg_st \<Rightarrow> bool)
     \<Rightarrow> (parity exec_dg_st lifted, parity exec_dg_st lifted) dg_spec"
where
  "pctx_spec gs is_bot_pred =
     base_dg_spec_st_for_lifted gs is_bot_pred (parity_tf_st_for gs) (parity_enter_st_for gs)"

definition pctx_abs_spec ::
    "(vname \<Rightarrow> bool) \<Rightarrow> (parity abs_state lifted, parity abs_state lifted) dg_spec" where
  "pctx_abs_spec gs = base_dg_spec_for_lifted gs is_bot_state (parity_tf_for gs)"

subsection \<open>The routed equation system and its executable solution\<close>

definition pctx_eqs ::
    "(vname \<Rightarrow> bool) \<Rightarrow> (parity exec_dg_st \<Rightarrow> bool) \<Rightarrow> proc_table \<Rightarrow> pname list \<Rightarrow> pname \<Rightarrow> com
       \<Rightarrow> (pp \<times> unit, gk, (parity exec_dg_st lifted, parity exec_dg_st lifted) dg_state) eqsT" where
  "pctx_eqs gs is_bot_pred Pi ps mnm main =
     side_cfg_T_eff_keyed_seed_dg_buffered intra_predecessor_list (\<lambda>_. Global)
       route_unit
       (routed_cmb_g_contribution (pctx_spec gs is_bot_pred) Global Seed)
       (routed_extra_g Seed Global)
       (compile_prog Pi ps mnm main) (pctx_spec gs is_bot_pred) Bot (Lifted cinit_parity_st) Bot"

definition pctx_sol ::
    "(vname \<Rightarrow> bool) \<Rightarrow> (parity exec_dg_st \<Rightarrow> bool) \<Rightarrow> proc_table \<Rightarrow> pname list \<Rightarrow> pname \<Rightarrow> com
       \<Rightarrow> (pp \<times> unit) set
          \<times> (pp \<times> unit + gk \<Rightarrow> (parity exec_dg_st lifted, parity exec_dg_st lifted) dg_state)" where
  "pctx_sol gs is_bot_pred Pi ps mnm main =
     TD_side_always_join_Interp_solve (pctx_eqs gs is_bot_pred Pi ps mnm main)
       (cfg_exit (compile_prog Pi ps mnm main), ())"

definition pctx_terminates ::
    "(vname \<Rightarrow> bool) \<Rightarrow> (parity exec_dg_st \<Rightarrow> bool) \<Rightarrow> proc_table \<Rightarrow> pname list \<Rightarrow> pname \<Rightarrow> com
       \<Rightarrow> bool" where
  "pctx_terminates gs is_bot_pred Pi ps mnm main =
     TD_side_always_join_Interp.solve_dom TYPE(gk)
       TYPE((parity exec_dg_st lifted, parity exec_dg_st lifted) dg_state)
       (pctx_eqs gs is_bot_pred Pi ps mnm main) (cfg_exit (compile_prog Pi ps mnm main), ())"

lemma pctx_terminates_via_solve_c:
  assumes "TD_side_always_join_Interp_solve_c (pctx_eqs gs is_bot_pred Pi ps mnm main)
             (cfg_exit (compile_prog Pi ps mnm main), ()) \<noteq> None"
  shows "pctx_terminates gs is_bot_pred Pi ps mnm main"
  unfolding pctx_terminates_def TD_side_always_join_Interp.term_equivalence
            TD_side_always_join_Interp.solve_c_dom_def
  using assms by simp

subsection \<open>Domain commute facts, at the routed unit spec\<close>

text \<open>
  The whole of Parity's obligation to the routed spine, in one interpretation.
  \<^locale>\<open>routed_domain_exec\<close> adds only the seed-key pair, its distinctness, and the
  two routing functions on top of \<^locale>\<open>routed_dg_domain_exec\<close>, so the interpretation
  carries no Parity mathematics: the first three obligations are Parity's own
  pre-existing commute lemmas, cited unchanged, and the last two are datatype
  distinctness for \<^type>\<open>gk\<close> and the free routing agreement \<^const>\<open>route_unit\<close> enjoys
  by ignoring its \<open>'D\<close> argument outright.
\<close>

context
  fixes gs :: "vname \<Rightarrow> bool" and is_bot_pred :: "parity exec_dg_st \<Rightarrow> bool"
  assumes exact: "\<And>s. is_bot_pred s = is_bot_state (fun_of_resolved_st_q_for gs s)"
begin

interpretation parity_unit: routed_domain_exec
  gs is_bot_pred "parity_tf_st_for gs" "parity_enter_st_for gs" "parity_tf_for gs"
  Global Seed route_unit route_unit
  by unfold_locales
     (rule parity_tf_st_for_commute, rule parity_enter_st_for_commute, rule exact, simp, simp)

lemmas parity_pp_abs_gen = parity_unit.pp_abs

end

subsection \<open>The certified executable post-solution, generic per compiled program\<close>

context
  fixes gs :: "vname \<Rightarrow> bool" and is_bot_pred :: "parity exec_dg_st \<Rightarrow> bool"
    and Pi :: proc_table and ps :: "pname list" and mnm :: pname and main :: com
  assumes solves: "pctx_terminates gs is_bot_pred Pi ps mnm main"
    and exact: "\<And>s. is_bot_pred s = is_bot_state (fun_of_resolved_st_q_for gs s)"
begin

lemma pctx_solve_dom:
  "TD_side_always_join_Interp.solve_dom TYPE(gk)
     TYPE((parity exec_dg_st lifted, parity exec_dg_st lifted) dg_state)
     (pctx_eqs gs is_bot_pred Pi ps mnm main) (cfg_exit (compile_prog Pi ps mnm main), ())"
  using solves
  unfolding pctx_terminates_def TD_side_always_join_Interp.term_equivalence
            TD_side_always_join_Interp.solve_c_dom_def
  by simp

lemma pctx_pp_st:
  "part_post_solution (pctx_eqs gs is_bot_pred Pi ps mnm main)
     (cfg_exit (compile_prog Pi ps mnm main), ())
     (snd (pctx_sol gs is_bot_pred Pi ps mnm main)) (fst (pctx_sol gs is_bot_pred Pi ps mnm main))"
  using TD_side_always_join_Interp.partial_post_solution
          [OF pctx_solve_dom, of "fst (pctx_sol gs is_bot_pred Pi ps mnm main)"
             "snd (pctx_sol gs is_bot_pred Pi ps mnm main)"]
  unfolding pctx_sol_def by simp

theorem pctx_pp_abs:
  "part_post_solution
     (side_cfg_T_eff_keyed_seed_dg intra_predecessor_list (\<lambda>_. Global) route_unit
        (routed_cmb_g (pctx_abs_spec gs) Global Seed)
        (routed_extra_g Seed Global)
        (compile_prog Pi ps mnm main) (pctx_abs_spec gs)
        (map_lift (fun_of_resolved_st_q_for gs) (Bot::parity exec_dg_st lifted))
        (map_lift (fun_of_resolved_st_q_for gs) (Lifted cinit_parity_st))
        (map_lift (fun_of_resolved_st_q_for gs) (Bot::parity exec_dg_st lifted)))
     (cfg_exit (compile_prog Pi ps mnm main), ())
     (fun_of_dg_st_gen (map_lift (fun_of_resolved_st_q_for gs)) (map_lift (fun_of_resolved_st_q_for gs))
        \<circ> snd (pctx_sol gs is_bot_pred Pi ps mnm main))
     (fst (pctx_sol gs is_bot_pred Pi ps mnm main))"
proof -
  have pp_buf: "part_post_solution
       (side_cfg_T_eff_keyed_seed_dg_buffered intra_predecessor_list (\<lambda>_. Global)
          route_unit
          (routed_cmb_g_contribution (pctx_spec gs is_bot_pred) Global Seed)
          (routed_extra_g Seed Global)
          (compile_prog Pi ps mnm main) (pctx_spec gs is_bot_pred) Bot (Lifted cinit_parity_st) Bot)
       (cfg_exit (compile_prog Pi ps mnm main), ())
       (snd (pctx_sol gs is_bot_pred Pi ps mnm main)) (fst (pctx_sol gs is_bot_pred Pi ps mnm main))"
    using pctx_pp_st unfolding pctx_eqs_def by simp
  show ?thesis
    unfolding pctx_abs_spec_def
    using pp_buf unfolding pctx_spec_def by (rule parity_pp_abs_gen[OF exact])
qed

end

section \<open>Activation-indexed collecting soundness, generic per compiled program\<close>

definition pctx_sigma_abs_exec ::
    "(vname \<Rightarrow> bool) \<Rightarrow> (parity exec_dg_st \<Rightarrow> bool) \<Rightarrow> proc_table \<Rightarrow> pname list \<Rightarrow> pname \<Rightarrow> com
       \<Rightarrow> pp \<times> unit + gk \<Rightarrow> (parity abs_state lifted, parity abs_state lifted) dg_state" where
  "pctx_sigma_abs_exec gs is_bot_pred Pi ps mnm main =
     fun_of_dg_st_gen (map_lift (fun_of_resolved_st_q_for gs)) (map_lift (fun_of_resolved_st_q_for gs))
       \<circ> snd (pctx_sol gs is_bot_pred Pi ps mnm main)"

definition pctx_sg_exec ::
    "(vname \<Rightarrow> bool) \<Rightarrow> (parity exec_dg_st \<Rightarrow> bool) \<Rightarrow> proc_table \<Rightarrow> pname list \<Rightarrow> pname \<Rightarrow> com
       \<Rightarrow> pp \<times> unit + gk \<Rightarrow> parity abs_state lifted" where
  "pctx_sg_exec gs is_bot_pred Pi ps mnm main k =
     (case k of
        Inl (v, ctx) \<Rightarrow>
          (if (v, ctx) \<in> fst (pctx_sol gs is_bot_pred Pi ps mnm main)
           then locals (pctx_sigma_abs_exec gs is_bot_pred Pi ps mnm main (Inl (v, ctx)))
           else Bot)
      | Inr _ \<Rightarrow> Bot)"

context
  fixes gs :: "vname \<Rightarrow> bool" and is_bot_pred :: "parity exec_dg_st \<Rightarrow> bool"
    and Pi :: proc_table and ps :: "pname list" and mnm :: pname and main :: com
  assumes solves: "pctx_terminates gs is_bot_pred Pi ps mnm main"
    and exact: "\<And>s. is_bot_pred s = is_bot_state (fun_of_resolved_st_q_for gs s)"
    and entry_cov: "(cfg_entry (compile_prog Pi ps mnm main), ())
                      \<in> fst (pctx_sol gs is_bot_pred Pi ps mnm main)"
    and fwd_ok: "\<And>u a v ctx. (u, ctx) \<in> fst (pctx_sol gs is_bot_pred Pi ps mnm main)
                   \<Longrightarrow> (u, a, v) \<in> intra (compile_prog Pi ps mnm main)
                   \<Longrightarrow> (v, ctx) \<in> fst (pctx_sol gs is_bot_pred Pi ps mnm main)"
    and call_fwd_ok: "\<And>u ctx dst pars args p cont.
        (u, ctx) \<in> fst (pctx_sol gs is_bot_pred Pi ps mnm main)
        \<Longrightarrow> (u, CallEdge dst pars args, FunctionEntry p, cont) \<in> calls (compile_prog Pi ps mnm main)
        \<Longrightarrow> (FunctionEntry p, ()) \<in> fst (pctx_sol gs is_bot_pred Pi ps mnm main)"
    and comb_fwd_ok: "\<And>cl c1 dst pars args p cont.
        (cl, c1) \<in> fst (pctx_sol gs is_bot_pred Pi ps mnm main)
        \<Longrightarrow> (cl, CallEdge dst pars args, FunctionEntry p, cont) \<in> calls (compile_prog Pi ps mnm main)
        \<Longrightarrow> (cont, c1) \<in> fst (pctx_sol gs is_bot_pred Pi ps mnm main)"
begin

subsection \<open>The semantic solution projection\<close>

definition pctx_sigma_abs ::
    "pp \<times> unit + gk \<Rightarrow> (parity abs_state lifted, parity abs_state lifted) dg_state" where
  "pctx_sigma_abs = pctx_sigma_abs_exec gs is_bot_pred Pi ps mnm main"

definition pctx_sg :: "pp \<times> unit + gk \<Rightarrow> parity abs_state lifted" where
  "pctx_sg = pctx_sg_exec gs is_bot_pred Pi ps mnm main"

lemma pctx_fin: "finite (intra (compile_prog Pi ps mnm main))"
  using compile_prog_finite by blast

lemma pctx_finC: "finite (calls (compile_prog Pi ps mnm main))"
  using compile_prog_finite by blast

lemma pctx_sg_covered:
  "(v, ctx) \<in> fst (pctx_sol gs is_bot_pred Pi ps mnm main)
   \<Longrightarrow> pctx_sg (Inl (v, ctx)) = locals (pctx_sigma_abs (Inl (v, ctx)))"
  by (simp add: pctx_sg_def pctx_sg_exec_def pctx_sigma_abs_def pctx_sigma_abs_exec_def)

lemma pctx_sg_uncovered_empty:
  "(v, ctx) \<notin> fst (pctx_sol gs is_bot_pred Pi ps mnm main)
     \<Longrightarrow> gamma_state_lift (pctx_sg (Inl (v, ctx))) = {}"
  by (simp add: pctx_sg_def pctx_sg_exec_def)

subsection \<open>Instantiating the generic DG-native activation discharge\<close>

interpretation pctx_dg_base: sound_dg_spec "pctx_abs_spec gs" gamma_dg_base gs
  unfolding pctx_abs_spec_def
  by (rule base_dg_spec_sound[OF parity_is_sound_transfer_for is_bot_state_gamma_state_empty])

interpretation pctx_dg: dg_ctx_activation_base "pctx_abs_spec gs" gamma_dg_base gs
    "compile_prog Pi ps mnm main" Global route_unit
    "routed_cmb_g (pctx_abs_spec gs) Global Seed"
    "routed_extra_g Seed Global"
    "map_lift (fun_of_resolved_st_q_for gs) (Bot::parity exec_dg_st lifted)"
    "map_lift (fun_of_resolved_st_q_for gs) (Lifted cinit_parity_st)"
    "map_lift (fun_of_resolved_st_q_for gs) (Bot::parity exec_dg_st lifted)"
    pctx_sigma_abs "fst (pctx_sol gs is_bot_pred Pi ps mnm main)"
    "(cfg_exit (compile_prog Pi ps mnm main), ())" pctx_sg gamma_state_lift
proof unfold_locales
  show "finite (intra (compile_prog Pi ps mnm main))" by (rule pctx_fin)
next
  show "part_post_solution
          (side_cfg_T_eff_keyed_seed_dg intra_predecessor_list (\<lambda>_. Global) route_unit
             (routed_cmb_g (pctx_abs_spec gs) Global Seed)
             (routed_extra_g Seed Global)
             (compile_prog Pi ps mnm main) (pctx_abs_spec gs)
             (map_lift (fun_of_resolved_st_q_for gs) (Bot::parity exec_dg_st lifted))
             (map_lift (fun_of_resolved_st_q_for gs) (Lifted cinit_parity_st))
             (map_lift (fun_of_resolved_st_q_for gs) (Bot::parity exec_dg_st lifted)))
          (cfg_exit (compile_prog Pi ps mnm main), ()) pctx_sigma_abs
          (fst (pctx_sol gs is_bot_pred Pi ps mnm main))"
    unfolding pctx_sigma_abs_def pctx_sigma_abs_exec_def
    by (rule pctx_pp_abs[OF solves exact])
next
  fix v ctx assume "(v, ctx) \<in> fst (pctx_sol gs is_bot_pred Pi ps mnm main)"
  thus "gamma_state_lift (pctx_sg (Inl (v, ctx)))
          = gamma_dg_base (locals (pctx_sigma_abs (Inl (v, ctx)))) (globs (pctx_sigma_abs (Inr Global)))"
    by (simp add: pctx_sg_covered gamma_dg_base_def)
next
  fix v ctx assume "(v, ctx) \<notin> fst (pctx_sol gs is_bot_pred Pi ps mnm main)"
  thus "gamma_state_lift (pctx_sg (Inl (v, ctx))) = {}"
    by (rule pctx_sg_uncovered_empty)
next
  fix u a v ctx assume "(u, ctx) \<in> fst (pctx_sol gs is_bot_pred Pi ps mnm main)"
    "(u, a, v) \<in> intra (compile_prog Pi ps mnm main)"
  thus "(v, ctx) \<in> fst (pctx_sol gs is_bot_pred Pi ps mnm main)" by (rule fwd_ok)
qed

subsection \<open>The routed interpretation and its CALL/COMB corollaries\<close>

interpretation pctx_routed: unit_routed_context "pctx_abs_spec gs" gamma_dg_base gs
    "compile_prog Pi ps mnm main" Global
    "map_lift (fun_of_resolved_st_q_for gs) (Bot::parity exec_dg_st lifted)"
    "map_lift (fun_of_resolved_st_q_for gs) (Lifted cinit_parity_st)"
    "map_lift (fun_of_resolved_st_q_for gs) (Bot::parity exec_dg_st lifted)"
    pctx_sigma_abs "fst (pctx_sol gs is_bot_pred Pi ps mnm main)"
    "(cfg_exit (compile_prog Pi ps mnm main), ())" pctx_sg
    Seed gamma_state_lift
proof (unfold_locales, goal_cases FinC SeedKey CallFwd CombFwd EnterAgree)
  case FinC show ?case by (rule pctx_finC)
next
  case (SeedKey p ctx) show ?case by simp
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
              \<in> calls (compile_prog Pi ps mnm main)"
    and es_eq: "es = call_enter gs (CallEdge dst' pars' args') s"
    using ces unfolding call_enter_store_def by blast
  have "CallEdge dst' pars' args' = CallEdge dst pars args"
    using compile_prog_calls_source_unique[OF ce' ce] by simp
  thus ?case using es_eq by simp
qed

subsection \<open>Activation-indexed collecting soundness\<close>

lemma pctx_cinit_le_cinit_parity_st:
  "cinit_stores gs \<subseteq> gamma_state_lift (map_lift (fun_of_resolved_st_q_for gs) (Lifted cinit_parity_st))"
  by (auto simp: cinit_stores_def gamma_state_def fun_of_resolved_st_q_for_def
                 fun_of_st_cinit_parity_st_for)

end

section \<open>Solved-result table\<close>

text \<open>
  The whole-program convenience layer, reading the raw executable solve through the same
  \<^const>\<open>canonicalize_lift\<close>/\<^const>\<open>normalize_point\<close> boundary every other domain's result
  table already uses. Nothing here is Parity-specific beyond the domain name: these are
  the thin monomorphic aliases the public API needs, not a second result construction.
\<close>

definition pctx_eqs_prog ::
    "(vname \<Rightarrow> bool) \<Rightarrow> pname \<Rightarrow> imp_prog
       \<Rightarrow> (pp \<times> unit, gk, (parity exec_dg_st lifted, parity exec_dg_st lifted) dg_state) eqsT" where
  "pctx_eqs_prog gs mnm p =
     pctx_eqs gs (resolved_st_q_is_bot_for (declared_global_vars p))
       (prog_table p) (prog_procs p) mnm (prog_main p)"

definition pctx_sol_prog ::
    "(vname \<Rightarrow> bool) \<Rightarrow> pname \<Rightarrow> imp_prog
       \<Rightarrow> (pp \<times> unit) set
          \<times> (pp \<times> unit + gk \<Rightarrow> (parity exec_dg_st lifted, parity exec_dg_st lifted) dg_state)" where
  "pctx_sol_prog gs mnm p =
     TD_side_always_join_Interp_solve (pctx_eqs_prog gs mnm p) (cfg_exit (prog_cfg mnm p), ())"

definition pctx_sol_prog_per_origin ::
    "(vname \<Rightarrow> bool) \<Rightarrow> pname \<Rightarrow> imp_prog
       \<Rightarrow> (pp \<times> unit) set
          \<times> (pp \<times> unit + gk \<Rightarrow> (parity exec_dg_st lifted, parity exec_dg_st lifted) dg_state)" where
  "pctx_sol_prog_per_origin gs mnm p =
     TD_side_per_origin_Interp_solve (pctx_eqs_prog gs mnm p) (cfg_exit (prog_cfg mnm p), ())"

definition pctx_terminates_prog :: "(vname \<Rightarrow> bool) \<Rightarrow> pname \<Rightarrow> imp_prog \<Rightarrow> bool" where
  "pctx_terminates_prog gs mnm p =
     pctx_terminates gs (resolved_st_q_is_bot_for (declared_global_vars p))
       (prog_table p) (prog_procs p) mnm (prog_main p)"

lemma pctx_terminates_prog_via_solve_c:
  assumes "TD_side_always_join_Interp_solve_c
             (pctx_eqs gs (resolved_st_q_is_bot_for (declared_global_vars p))
                (prog_table p) (prog_procs p) mnm (prog_main p))
             (cfg_exit (compile_prog (prog_table p) (prog_procs p) mnm (prog_main p)), ()) \<noteq> None"
  shows "pctx_terminates_prog gs mnm p"
  unfolding pctx_terminates_prog_def
  using assms by (rule pctx_terminates_via_solve_c)

definition analyse_parity_ctx_result_for ::
    "(vname \<Rightarrow> bool) \<Rightarrow> pname \<Rightarrow> imp_prog \<Rightarrow> (unit, parity abs_state) analysis_result" where
  "analyse_parity_ctx_result_for gs mnm p =
     Analysis_Result
       (fst (pctx_sol_prog gs mnm p))
       (\<lambda>v ctx. normalize_point gs
                  (canonicalize_lift (resolved_st_q_is_bot_for (declared_global_vars p))
                    (locals (snd (pctx_sol_prog gs mnm p) (Inl (v, ctx))))))"

declare analyse_parity_ctx_result_for_def [code del]

lemma analyse_parity_ctx_result_for_code [code]:
  "analyse_parity_ctx_result_for gs mnm p =
     (let sol = pctx_sol_prog gs mnm p; gl = declared_global_vars p
      in Analysis_Result (fst sol)
           (\<lambda>v ctx. normalize_point gs
                      (canonicalize_lift (resolved_st_q_is_bot_for gl)
                        (locals (snd sol (Inl (v, ctx)))))))"
  unfolding analyse_parity_ctx_result_for_def Let_def by (rule refl)

definition analyse_parity_ctx_result :: "imp_prog \<Rightarrow> (unit, parity abs_state) analysis_result" where
  "analyse_parity_ctx_result p =
     analyse_parity_ctx_result_for (declared_global p) prog_main_name p"

text \<open>Per-origin sibling, reading \<^const>\<open>pctx_sol_prog_per_origin\<close>.\<close>

definition analyse_parity_ctx_result_per_origin_for ::
    "(vname \<Rightarrow> bool) \<Rightarrow> pname \<Rightarrow> imp_prog \<Rightarrow> (unit, parity abs_state) analysis_result" where
  "analyse_parity_ctx_result_per_origin_for gs mnm p =
     Analysis_Result
       (fst (pctx_sol_prog_per_origin gs mnm p))
       (\<lambda>v ctx. normalize_point gs
                  (canonicalize_lift (resolved_st_q_is_bot_for (declared_global_vars p))
                    (locals (snd (pctx_sol_prog_per_origin gs mnm p) (Inl (v, ctx))))))"

declare analyse_parity_ctx_result_per_origin_for_def [code del]

lemma analyse_parity_ctx_result_per_origin_for_code [code]:
  "analyse_parity_ctx_result_per_origin_for gs mnm p =
     (let sol = pctx_sol_prog_per_origin gs mnm p; gl = declared_global_vars p
      in Analysis_Result (fst sol)
           (\<lambda>v ctx. normalize_point gs
                      (canonicalize_lift (resolved_st_q_is_bot_for gl)
                        (locals (snd sol (Inl (v, ctx)))))))"
  unfolding analyse_parity_ctx_result_per_origin_for_def Let_def by (rule refl)

definition analyse_parity_ctx_result_per_origin ::
    "imp_prog \<Rightarrow> (unit, parity abs_state) analysis_result" where
  "analyse_parity_ctx_result_per_origin p =
     analyse_parity_ctx_result_per_origin_for (declared_global p) prog_main_name p"

end
