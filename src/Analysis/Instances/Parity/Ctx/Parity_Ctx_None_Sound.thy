theory Parity_Ctx_None_Sound
  imports
    "Voblint_Exec.Monovariant_Analysis_Result"
    "Voblint_Exec.Routed_Domain_Exec"
    "Voblint_Core.DG_Base"
    "Voblint_Exec.DG_Base_Exec"
    "Voblint_Analysis.Parity_Exec"
    "Voblint_Analysis.Parity_Sound"
    "Voblint_Compile.Compile_Invariants"
    "Voblint_CFG.CFG_Prune"
    "TD.TD_side_upd_rule"
    "Voblint_Core.Routed_Context"
    "Voblint_Core.Routed_Context_Unit"
    "Voblint_Solver.TD_Solver_Menu"
    "Voblint_Core.Analysis_Result"
    "Voblint_VIMP.VIMP_Program"
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

subsection \<open>The routed equation system and its executable solution\<close>

definition pctx_eqs ::
    "(vname \<Rightarrow> bool) \<Rightarrow> (parity exec_dg_st \<Rightarrow> bool) \<Rightarrow> proc_table \<Rightarrow> pname list \<Rightarrow> (pp \<times> unit, gk, (parity exec_dg_st lifted, parity exec_dg_st lifted) dg_state) eqsT" where
  "pctx_eqs gs empty_pred Pi ps =
     side_cfg_T_eff_keyed_seed_dg_buffered intra_predecessor_addr_list (\<lambda>_. Global)
       route_unit
       (\<lambda>ctx' src a. dg_spec_edge_tree (pctx_spec gs empty_pred) a src (\<lambda>_. Global))
       (routed_cmb_g (pctx_spec gs empty_pred) Global Seed
          (static_resolve (compile_prog Pi ps)))
       (routed_extra_g Seed Global)
       (compile_prog Pi ps) Bot (Lifted cinit_parity_st) Bot"

definition pctx_sol ::
    "(vname \<Rightarrow> bool) \<Rightarrow> (parity exec_dg_st \<Rightarrow> bool) \<Rightarrow> proc_table \<Rightarrow> pname list \<Rightarrow> (pp \<times> unit) set
          \<times> (pp \<times> unit + gk \<Rightarrow> (parity exec_dg_st lifted, parity exec_dg_st lifted) dg_state)" where
  "pctx_sol gs empty_pred Pi ps =
     TD_side_always_join_Interp_solve (pctx_eqs gs empty_pred Pi ps)
       (cfg_exit (compile_prog Pi ps), ())"

definition pctx_terminates ::
    "(vname \<Rightarrow> bool) \<Rightarrow> (parity exec_dg_st \<Rightarrow> bool) \<Rightarrow> proc_table \<Rightarrow> pname list \<Rightarrow> bool" where
  "pctx_terminates gs empty_pred Pi ps =
     TD_side_always_join_Interp.solve_dom TYPE(gk)
       TYPE((parity exec_dg_st lifted, parity exec_dg_st lifted) dg_state)
       (pctx_eqs gs empty_pred Pi ps) (cfg_exit (compile_prog Pi ps), ())"

lemma pctx_terminates_via_solve_c:
  assumes "TD_side_always_join_Interp_solve_c (pctx_eqs gs empty_pred Pi ps)
             (cfg_exit (compile_prog Pi ps), ()) \<noteq> None"
  shows "pctx_terminates gs empty_pred Pi ps"
  unfolding pctx_terminates_def
  by (rule TD_side_always_join_Interp.solve_dom_of_solve_c[OF assms])

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
  fixes gs :: "vname \<Rightarrow> bool" and empty_pred :: "parity exec_dg_st \<Rightarrow> bool"
  assumes exact: "\<And>s. empty_pred s = is_empty_state (fun_of_resolved_st_q_for gs s)"
begin

interpretation parity_unit: routed_domain_exec
  gs empty_pred "parity_tf_st_for gs" "parity_enter_st_for gs" "parity_tf_for gs"
  Global Seed route_unit route_unit static_resolve static_resolve
  by unfold_locales
     (rule parity_tf_st_for_commute, rule parity_enter_st_for_commute, rule exact, simp, simp,
      simp add: static_resolve_def)

lemmas parity_pp_st_gen = parity_unit.pp_st

end

subsection \<open>The certified executable post-solution, generic per compiled program\<close>

context
  fixes gs :: "vname \<Rightarrow> bool" and empty_pred :: "parity exec_dg_st \<Rightarrow> bool"
    and Pi :: proc_table and ps :: "pname list"
  assumes solves: "pctx_terminates gs empty_pred Pi ps"
    and exact: "\<And>s. empty_pred s = is_empty_state (fun_of_resolved_st_q_for gs s)"
begin

lemma pctx_solve_dom:
  "TD_side_always_join_Interp.solve_dom TYPE(gk)
     TYPE((parity exec_dg_st lifted, parity exec_dg_st lifted) dg_state)
     (pctx_eqs gs empty_pred Pi ps) (cfg_exit (compile_prog Pi ps), ())"
  using solves[unfolded pctx_terminates_def] .

lemma pctx_pp_st:
  "part_post_solution (pctx_eqs gs empty_pred Pi ps)
     (cfg_exit (compile_prog Pi ps), ())
     (snd (pctx_sol gs empty_pred Pi ps)) (fst (pctx_sol gs empty_pred Pi ps))"
  using TD_side_always_join_Interp.partial_post_solution
          [OF pctx_solve_dom, of "fst (pctx_sol gs empty_pred Pi ps)"
             "snd (pctx_sol gs empty_pred Pi ps)"]
  unfolding pctx_sol_def by simp

text \<open>The solver's post-solution, for the unbuffered routed generator at the executable
  spec: the shape \<^locale>\<open>dg_ctx_activation_base\<close> consumes directly.\<close>

theorem pctx_pp_routed:
  "part_post_solution
     (side_cfg_T_eff_keyed_seed_dg intra_predecessor_addr_list (\<lambda>_. Global) route_unit
        (\<lambda>ctx' src a. dg_spec_edge_tree (pctx_spec gs empty_pred) a src (\<lambda>_. Global))
        (routed_cmb_g (pctx_spec gs empty_pred) Global Seed (static_resolve (compile_prog Pi ps)))
        (routed_extra_g Seed Global)
        (compile_prog Pi ps) Bot (Lifted cinit_parity_st) Bot)
     (cfg_exit (compile_prog Pi ps), ())
     (snd (pctx_sol gs empty_pred Pi ps)) (fst (pctx_sol gs empty_pred Pi ps))"
  using pctx_pp_st unfolding pctx_eqs_def pctx_spec_def by (rule parity_pp_st_gen[OF exact])
end

section \<open>Activation-indexed collecting soundness, generic per compiled program\<close>

text \<open>
  The routed spine is interpreted at Parity's executable carrier and fed the solver's own
  table: a local unknown concretizes to \<^const>\<open>gamma_state_lift\<close> of its readback, the
  covered reader \<open>pctx_sg_st\<close> hands the table's local slot through unchanged, and no
  solved system is transported between carriers. \<open>pctx_gamma\<close> names that
  concretization outside the interpretation so a downstream theory can state it.
\<close>

definition pctx_sg_st ::
    "(vname \<Rightarrow> bool) \<Rightarrow> (parity exec_dg_st \<Rightarrow> bool) \<Rightarrow> proc_table \<Rightarrow> pname list
       \<Rightarrow> pp \<times> unit + gk \<Rightarrow> parity exec_dg_st lifted" where
  "pctx_sg_st gs empty_pred Pi ps k =
     (case k of
        Inl (v, ctx) \<Rightarrow>
          (if (v, ctx) \<in> fst (pctx_sol gs empty_pred Pi ps)
           then locals (snd (pctx_sol gs empty_pred Pi ps) (Inl (v, ctx)))
           else Bot)
      | Inr _ \<Rightarrow> Bot)"

context
  fixes gs :: "vname \<Rightarrow> bool" and empty_pred :: "parity exec_dg_st \<Rightarrow> bool"
  assumes exact: "\<And>s. empty_pred s = is_empty_state (fun_of_resolved_st_q_for gs s)"
begin

interpretation parity_unit: routed_domain_exec
  gs empty_pred "parity_tf_st_for gs" "parity_enter_st_for gs" "parity_tf_for gs"
  Global Seed route_unit route_unit static_resolve static_resolve
  by unfold_locales
     (rule parity_tf_st_for_commute, rule parity_enter_st_for_commute, rule exact, simp, simp,
      simp add: static_resolve_def)

end

context
  fixes gs :: "vname \<Rightarrow> bool" and empty_pred :: "parity exec_dg_st \<Rightarrow> bool"
    and Pi :: proc_table and ps :: "pname list"
  assumes solves: "pctx_terminates gs empty_pred Pi ps"
    and exact: "\<And>s. empty_pred s = is_empty_state (fun_of_resolved_st_q_for gs s)"
    and entry_cov: "(cfg_entry (compile_prog Pi ps), ()) \<in> fst (pctx_sol gs empty_pred Pi ps)"
    and fwd_ok: "\<And>u a v ctx. (u, ctx) \<in> fst (pctx_sol gs empty_pred Pi ps)
                   \<Longrightarrow> (u, a, v) \<in> intra (compile_prog Pi ps)
                   \<Longrightarrow> (v, ctx) \<in> fst (pctx_sol gs empty_pred Pi ps)"
    and call_fwd_ok: "\<And>u ctx dst pars args p cont.
        (u, ctx) \<in> fst (pctx_sol gs empty_pred Pi ps)
        \<Longrightarrow> (u, CallEdge dst pars args, FunctionEntry p, cont) \<in> calls (compile_prog Pi ps)
        \<Longrightarrow> (FunctionEntry p, ()) \<in> fst (pctx_sol gs empty_pred Pi ps)"
    and comb_fwd_ok: "\<And>cl c1 dst pars args p cont.
        (cl, c1) \<in> fst (pctx_sol gs empty_pred Pi ps)
        \<Longrightarrow> (cl, CallEdge dst pars args, FunctionEntry p, cont) \<in> calls (compile_prog Pi ps)
        \<Longrightarrow> (cont, c1) \<in> fst (pctx_sol gs empty_pred Pi ps)"
begin

interpretation pctx_compiled: compiled_cfg Pi ps "compile_prog Pi ps"
  by (unfold_locales; simp add: compile_prog_finite)

lemmas pctx_fin = pctx_compiled.finite_intra
lemmas pctx_finC = pctx_compiled.finite_calls

lemma pctx_sg_st_covered:
  "(v, ctx) \<in> fst (pctx_sol gs empty_pred Pi ps)
   \<Longrightarrow> pctx_sg_st gs empty_pred Pi ps (Inl (v, ctx))
         = locals (snd (pctx_sol gs empty_pred Pi ps) (Inl (v, ctx)))"
  by (simp add: pctx_sg_st_def)

lemma pctx_sg_st_uncovered_empty:
  "(v, ctx) \<notin> fst (pctx_sol gs empty_pred Pi ps)
     \<Longrightarrow> gamma_state_lift (map_lift (fun_of_resolved_st_q_for gs)
           (pctx_sg_st gs empty_pred Pi ps (Inl (v, ctx)))) = {}"
  by (simp add: pctx_sg_st_def)

subsection \<open>Instantiating the generic DG-native activation discharge\<close>

interpretation pctx_dg_base: sound_dg_spec "pctx_spec gs empty_pred" "pctx_gamma gs" gs
  by (rule pctx_sound_exec[OF exact])

interpretation pctx_routed: unit_routed_context "pctx_spec gs empty_pred" "pctx_gamma gs" gs
    "compile_prog Pi ps" Global Bot "Lifted cinit_parity_st" Bot
    "snd (pctx_sol gs empty_pred Pi ps)" "fst (pctx_sol gs empty_pred Pi ps)"
    "(cfg_exit (compile_prog Pi ps), ())" "pctx_sg_st gs empty_pred Pi ps" Seed
    "\<lambda>m. gamma_state_lift (map_lift (fun_of_resolved_st_q_for gs) m)"
proof (unfold_locales, goal_cases FinE PP SgCov SgUncov Fwd FinC SeedKey CallFwd CombFwd EnterAgree)
  case FinE show ?case by (rule pctx_fin)
next
  case PP show ?case by (rule pctx_pp_routed[OF solves exact])
next
  case (SgCov v ctx) then show ?case
    by (simp add: pctx_sg_st_def pctx_gamma_def)
next
  case (SgUncov v ctx) then show ?case by (rule pctx_sg_st_uncovered_empty)
next
  case (Fwd u a v ctx) then show ?case by (rule fwd_ok)
next
  case FinC show ?case by (rule pctx_finC)
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

lemma pctx_cinit_le_cinit_parity_st:
  "cinit_stores gs \<subseteq> pctx_gamma gs (Lifted cinit_parity_st) Bot"
  by (auto simp: pctx_gamma_def cinit_stores_def gamma_state_def fun_of_resolved_st_q_for_def
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
    "(vname \<Rightarrow> bool) \<Rightarrow> imp_prog
       \<Rightarrow> (pp \<times> unit, gk, (parity exec_dg_st lifted, parity exec_dg_st lifted) dg_state) eqsT" where
  "pctx_eqs_prog gs p =
     pctx_eqs gs (resolved_st_q_is_bot_for (declared_global_vars p))
       (prog_table p) (prog_procs p)"

definition pctx_sol_prog ::
    "(vname \<Rightarrow> bool) \<Rightarrow> imp_prog
       \<Rightarrow> (pp \<times> unit) set
          \<times> (pp \<times> unit + gk \<Rightarrow> (parity exec_dg_st lifted, parity exec_dg_st lifted) dg_state)" where
  "pctx_sol_prog gs p =
     TD_side_always_join_Interp_solve (pctx_eqs_prog gs p) (cfg_exit (prog_cfg p), ())"

definition pctx_sol_prog_per_origin ::
    "(vname \<Rightarrow> bool) \<Rightarrow> imp_prog
       \<Rightarrow> (pp \<times> unit) set
          \<times> (pp \<times> unit + gk \<Rightarrow> (parity exec_dg_st lifted, parity exec_dg_st lifted) dg_state)" where
  "pctx_sol_prog_per_origin gs p =
     TD_side_per_origin_Interp_solve (pctx_eqs_prog gs p) (cfg_exit (prog_cfg p), ())"

definition pctx_terminates_prog :: "(vname \<Rightarrow> bool) \<Rightarrow> imp_prog \<Rightarrow> bool" where
  "pctx_terminates_prog gs p =
     pctx_terminates gs (resolved_st_q_is_bot_for (declared_global_vars p))
       (prog_table p) (prog_procs p)"

lemma pctx_terminates_prog_via_solve_c:
  assumes "TD_side_always_join_Interp_solve_c
             (pctx_eqs gs (resolved_st_q_is_bot_for (declared_global_vars p))
                (prog_table p) (prog_procs p))
             (cfg_exit (compile_prog (prog_table p) (prog_procs p)), ()) \<noteq> None"
  shows "pctx_terminates_prog gs p"
  unfolding pctx_terminates_prog_def
  using assms by (rule pctx_terminates_via_solve_c)

definition analyse_parity_ctx_result_for ::
    "(vname \<Rightarrow> bool) \<Rightarrow> imp_prog \<Rightarrow> (unit, parity abs_state) analysis_result" where
  "analyse_parity_ctx_result_for gs p =
     Analysis_Result
       (fst (pctx_sol_prog gs p))
       (\<lambda>v ctx. normalize_point gs
                  (canonicalize_lift (resolved_st_q_is_bot_for (declared_global_vars p))
                    (locals (snd (pctx_sol_prog gs p) (Inl (v, ctx))))))"

text \<open>\<^const>\<open>ctx_solved_for\<close> at this domain's solve, with \<^const>\<open>Global\<close> and
  \<^const>\<open>Seed\<close> handed to \<^const>\<open>seed_global_keys\<close> the way \<^const>\<open>routed_extra_g\<close>
  already takes them.\<close>

definition analyse_parity_ctx_solved_for ::
    "(vname \<Rightarrow> bool) \<Rightarrow> imp_prog
     \<Rightarrow> (unit, parity abs_state) analysis_result
          \<times> (String.literal \<times> parity abs_state lifted) list" where
  "analyse_parity_ctx_solved_for = ctx_solved_for pctx_sol_prog (unit_seed_global_keys Global Seed)"

lemma fst_analyse_parity_ctx_solved_for:
  "fst (analyse_parity_ctx_solved_for gs p) = analyse_parity_ctx_result_for gs p"
  by (simp add: analyse_parity_ctx_solved_for_def fst_ctx_solved_for
      analyse_parity_ctx_result_for_def Let_def)

declare analyse_parity_ctx_result_for_def [code del]

lemma analyse_parity_ctx_result_for_code [code]:
  "analyse_parity_ctx_result_for gs p =
     (let sol = pctx_sol_prog gs p; gl = declared_global_vars p
      in Analysis_Result (fst sol)
           (\<lambda>v ctx. normalize_point gs
                      (canonicalize_lift (resolved_st_q_is_bot_for gl)
                        (locals (snd sol (Inl (v, ctx)))))))"
  unfolding analyse_parity_ctx_result_for_def Let_def by (rule refl)

definition analyse_parity_ctx_result :: "imp_prog \<Rightarrow> (unit, parity abs_state) analysis_result" where
  "analyse_parity_ctx_result p =
     analyse_parity_ctx_result_for (declared_global p) p"

text \<open>Per-origin sibling, reading \<^const>\<open>pctx_sol_prog_per_origin\<close>.\<close>

definition analyse_parity_ctx_result_per_origin_for ::
    "(vname \<Rightarrow> bool) \<Rightarrow> imp_prog \<Rightarrow> (unit, parity abs_state) analysis_result" where
  "analyse_parity_ctx_result_per_origin_for gs p =
     Analysis_Result
       (fst (pctx_sol_prog_per_origin gs p))
       (\<lambda>v ctx. normalize_point gs
                  (canonicalize_lift (resolved_st_q_is_bot_for (declared_global_vars p))
                    (locals (snd (pctx_sol_prog_per_origin gs p) (Inl (v, ctx))))))"

declare analyse_parity_ctx_result_per_origin_for_def [code del]

lemma analyse_parity_ctx_result_per_origin_for_code [code]:
  "analyse_parity_ctx_result_per_origin_for gs p =
     (let sol = pctx_sol_prog_per_origin gs p; gl = declared_global_vars p
      in Analysis_Result (fst sol)
           (\<lambda>v ctx. normalize_point gs
                      (canonicalize_lift (resolved_st_q_is_bot_for gl)
                        (locals (snd sol (Inl (v, ctx)))))))"
  unfolding analyse_parity_ctx_result_per_origin_for_def Let_def by (rule refl)

definition analyse_parity_ctx_result_per_origin ::
    "imp_prog \<Rightarrow> (unit, parity abs_state) analysis_result" where
  "analyse_parity_ctx_result_per_origin p =
     analyse_parity_ctx_result_per_origin_for (declared_global p) p"

end
