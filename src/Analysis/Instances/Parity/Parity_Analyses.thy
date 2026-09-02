theory Parity_Analyses
  imports
    "Voblint_Analysis.Parity_Sound"
    "Voblint_Analysis.Parity_Classify"
    "Voblint_Analysis.Parity_Exec"
    "Voblint_Exec.Monovariant_Analysis_Result"
    "Voblint_Exec.Routed_Domain_Exec"
    "Voblint_Exec.DG_Local_State_Exec"
    "Voblint_Framework.DG_Local_State_Spec"
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

chapter \<open>How Parity is run under each supported context policy\<close>

text \<open>
  Parity's analysis package -- specification, concretization and soundness --
  lives in \<^theory>\<open>Voblint_Analysis.Parity_Sound\<close> and mentions no context.
  This theory supplies the configurations: for each supported context policy,
  the equation system that pairing generates, its solved table, the coverage
  premises the solver's reachable set must satisfy, and the result and report
  tables a caller consumes.

  The three configurations are independent of one another and all name the same
  \<open>pctx_spec\<close> and \<open>pctx_sound_exec\<close>; none derives a fact about parity
  arithmetic. Global keys are \<^type>\<open>routed_gk\<close>, with
  \<^const>\<open>Analysis_Global\<close> at \<^typ>\<open>unit\<close> since Parity publishes no named
  global of its own; the call-string configuration uses the shared
  \<^typ>\<open>call_string_gk\<close>.
\<close>

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
    "(vname \<Rightarrow> bool) \<Rightarrow> (parity exec_dg_st \<Rightarrow> bool) \<Rightarrow> proc_table \<Rightarrow> pname list \<Rightarrow> (pp \<times> unit, (unit, unit) routed_gk, (parity exec_dg_st lifted, parity exec_dg_st lifted) dg_state) eqsT" where
  "pctx_eqs gs empty_pred Pi ps =
     side_cfg_T_eff_keyed_seed_dg_buffered intra_predecessor_addr_list (\<lambda>_. Analysis_Global ())
       route_unit
       (\<lambda>ctx' src a. dg_spec_edge_tree (pctx_spec gs empty_pred) a src (\<lambda>_. Analysis_Global ()))
       (routed_cmb_g (pctx_spec gs empty_pred) (Analysis_Global ()) Activation_Seed
          (static_resolve (compile_prog Pi ps)))
       (routed_extra_g Activation_Seed (Analysis_Global ()))
       (compile_prog Pi ps) Bot (Lifted cinit_parity_st) Bot"

definition pctx_sol ::
    "(vname \<Rightarrow> bool) \<Rightarrow> (parity exec_dg_st \<Rightarrow> bool) \<Rightarrow> proc_table \<Rightarrow> pname list \<Rightarrow> (pp \<times> unit) set
          \<times> (pp \<times> unit + (unit, unit) routed_gk \<Rightarrow> (parity exec_dg_st lifted, parity exec_dg_st lifted) dg_state)" where
  "pctx_sol gs empty_pred Pi ps =
     TD_side_always_join_Interp_solve (pctx_eqs gs empty_pred Pi ps)
       (cfg_exit (compile_prog Pi ps), ())"

definition pctx_terminates ::
    "(vname \<Rightarrow> bool) \<Rightarrow> (parity exec_dg_st \<Rightarrow> bool) \<Rightarrow> proc_table \<Rightarrow> pname list \<Rightarrow> bool" where
  "pctx_terminates gs empty_pred Pi ps =
     TD_side_always_join_Interp.solve_dom TYPE((unit, unit) routed_gk)
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
  distinctness for \<^type>\<open>routed_gk\<close> and the free routing agreement \<^const>\<open>route_unit\<close> enjoys
  by ignoring its \<open>'D\<close> argument outright.
\<close>

context
  fixes gs :: "vname \<Rightarrow> bool" and empty_pred :: "parity exec_dg_st \<Rightarrow> bool"
  assumes exact: "\<And>s. empty_pred s = is_empty_state (fun_of_resolved_st_q_for gs s)"
begin

interpretation parity_unit: routed_domain_exec
  gs empty_pred "parity_tf_st_for gs" "parity_enter_st_for gs" "parity_tf_for gs"
  "Analysis_Global ()" Activation_Seed route_unit route_unit static_resolve static_resolve
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
  "TD_side_always_join_Interp.solve_dom TYPE((unit, unit) routed_gk)
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
     (side_cfg_T_eff_keyed_seed_dg intra_predecessor_addr_list (\<lambda>_. Analysis_Global ()) route_unit
        (\<lambda>ctx' src a. dg_spec_edge_tree (pctx_spec gs empty_pred) a src (\<lambda>_. Analysis_Global ()))
        (routed_cmb_g (pctx_spec gs empty_pred) (Analysis_Global ()) Activation_Seed (static_resolve (compile_prog Pi ps)))
        (routed_extra_g Activation_Seed (Analysis_Global ()))
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
       \<Rightarrow> pp \<times> unit + (unit, unit) routed_gk \<Rightarrow> parity exec_dg_st lifted" where
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
  "Analysis_Global ()" Activation_Seed route_unit route_unit static_resolve static_resolve
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
    "compile_prog Pi ps" "Analysis_Global ()" Bot "Lifted cinit_parity_st" Bot
    "snd (pctx_sol gs empty_pred Pi ps)" "fst (pctx_sol gs empty_pred Pi ps)"
    "(cfg_exit (compile_prog Pi ps), ())" "pctx_sg_st gs empty_pred Pi ps" Activation_Seed
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
       \<Rightarrow> (pp \<times> unit, (unit, unit) routed_gk, (parity exec_dg_st lifted, parity exec_dg_st lifted) dg_state) eqsT" where
  "pctx_eqs_prog gs p =
     pctx_eqs gs (resolved_st_q_is_bot_for (declared_global_vars p))
       (prog_table p) (prog_procs p)"

definition pctx_sol_prog ::
    "(vname \<Rightarrow> bool) \<Rightarrow> imp_prog
       \<Rightarrow> (pp \<times> unit) set
          \<times> (pp \<times> unit + (unit, unit) routed_gk \<Rightarrow> (parity exec_dg_st lifted, parity exec_dg_st lifted) dg_state)" where
  "pctx_sol_prog gs p =
     TD_side_always_join_Interp_solve (pctx_eqs_prog gs p) (cfg_exit (prog_cfg p), ())"

definition pctx_sol_prog_per_origin ::
    "(vname \<Rightarrow> bool) \<Rightarrow> imp_prog
       \<Rightarrow> (pp \<times> unit) set
          \<times> (pp \<times> unit + (unit, unit) routed_gk \<Rightarrow> (parity exec_dg_st lifted, parity exec_dg_st lifted) dg_state)" where
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

text \<open>\<^const>\<open>ctx_solved_for\<close> at this domain's solve, with \<^const>\<open>Analysis_Global\<close> and
  \<^const>\<open>Activation_Seed\<close> handed to \<^const>\<open>seed_global_keys\<close> the way \<^const>\<open>routed_extra_g\<close>
  already takes them.\<close>

definition analyse_parity_ctx_solved_for ::
    "(vname \<Rightarrow> bool) \<Rightarrow> imp_prog
     \<Rightarrow> (unit, parity abs_state) analysis_result
          \<times> (String.literal \<times> parity abs_state lifted) list" where
  "analyse_parity_ctx_solved_for = ctx_solved_for pctx_sol_prog (unit_seed_global_keys (Analysis_Global ()) Activation_Seed)"

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


section \<open>Parity at the routed spine, instantiated at the call-string context\<close>

text \<open>
  The call-string run of the Parity analysis. Everything about Parity it needs --
  the specification \<^const>\<open>pctx_spec\<close>, its concretization \<^const>\<open>pctx_gamma\<close>, and the
  soundness of one against the other -- is taken from
  \<^theory>\<open>Voblint_Analysis.Parity_Sound\<close> and used as it stands; no fact about parity
  arithmetic, parity transfer or parity readback is restated or reproved here.

  What this theory supplies is the other half: a routing policy. \<^const>\<open>cs_route\<close>
  computes a callee's context by pushing the call site onto the caller's string and
  truncating to a runtime bound \<open>k\<close>, and \<^locale>\<open>call_string_routed_context\<close> already
  discharges four of the six routing obligations for any compiled program and any
  domain. What is left is the equation system this pairing generates, its solved
  table, and the two coverage premises the solver's own reachable set must satisfy.

  The global keys are \<^typ>\<open>call_string_gk\<close> from
  \<^theory>\<open>Voblint_Framework.Call_String_Context\<close>, shared with every other call-string-keyed
  instance rather than declared again per domain.
\<close>

subsection \<open>The routed equation system and its executable solution\<close>

definition pcs_eqs ::
    "nat \<Rightarrow> (vname \<Rightarrow> bool) \<Rightarrow> (parity exec_dg_st \<Rightarrow> bool) \<Rightarrow> proc_table \<Rightarrow> pname list \<Rightarrow> (pp \<times> call_string, call_string_gk, (parity exec_dg_st lifted, parity exec_dg_st lifted) dg_state) eqsT" where
  "pcs_eqs k gs empty_pred Pi ps =
     side_cfg_T_eff_keyed_seed_dg_buffered intra_predecessor_addr_list (\<lambda>_. Call_String_Context.Global)
       (cs_route k)
       (\<lambda>ctx' src a. dg_spec_edge_tree (pctx_spec gs empty_pred) a src
          (\<lambda>_. Call_String_Context.Global))
       (routed_cmb_g (pctx_spec gs empty_pred)
          Call_String_Context.Global Call_String_Context.Seed
          (static_resolve (compile_prog Pi ps)))
       (routed_extra_g Call_String_Context.Seed Call_String_Context.Global)
       (compile_prog Pi ps) Bot (Lifted cinit_parity_st) Bot"

definition pcs_sol ::
    "nat \<Rightarrow> (vname \<Rightarrow> bool) \<Rightarrow> (parity exec_dg_st \<Rightarrow> bool) \<Rightarrow> proc_table \<Rightarrow> pname list \<Rightarrow> (pp \<times> call_string) set \<times> (pp \<times> call_string + call_string_gk \<Rightarrow> (parity exec_dg_st lifted, parity exec_dg_st lifted) dg_state)" where
  "pcs_sol k gs empty_pred Pi ps =
     TD_side_always_join_Interp_solve (pcs_eqs k gs empty_pred Pi ps)
       (cfg_exit (compile_prog Pi ps), [])"

definition pcs_terminates ::
    "nat \<Rightarrow> (vname \<Rightarrow> bool) \<Rightarrow> (parity exec_dg_st \<Rightarrow> bool) \<Rightarrow> proc_table \<Rightarrow> pname list \<Rightarrow> bool" where
  "pcs_terminates k gs empty_pred Pi ps =
     TD_side_always_join_Interp.solve_dom TYPE(call_string_gk) TYPE((parity exec_dg_st lifted, parity exec_dg_st lifted) dg_state)
       (pcs_eqs k gs empty_pred Pi ps) (cfg_exit (compile_prog Pi ps), [])"

lemma pcs_terminates_via_solve_c:
  assumes "TD_side_always_join_Interp_solve_c (pcs_eqs k gs empty_pred Pi ps)
             (cfg_exit (compile_prog Pi ps), []) \<noteq> None"
  shows "pcs_terminates k gs empty_pred Pi ps"
  unfolding pcs_terminates_def
  by (rule TD_side_always_join_Interp.solve_dom_of_solve_c[OF assms])

subsection \<open>Domain commute facts, at the call-string routed spec\<close>

text \<open>
  \<^locale>\<open>routed_domain_exec\<close> takes the routing functions as parameters, so this is the
  same interpretation Parity's unit-context run makes, at a different instantiation.
  \<^const>\<open>cs_route\<close> reads only the call site and the incoming string, never the incoming
  abstract value, so the routing-agreement obligation is free.
\<close>

context
  fixes gs :: "vname \<Rightarrow> bool" and empty_pred :: "parity exec_dg_st \<Rightarrow> bool" and k :: nat
  assumes exact: "\<And>s. empty_pred s = is_empty_state (fun_of_resolved_st_q_for gs s)"
begin

interpretation parity_cs: routed_domain_exec
  gs empty_pred "parity_tf_st_for gs" "parity_enter_st_for gs" "parity_tf_for gs"
  Call_String_Context.Global Call_String_Context.Seed "cs_route k" "cs_route k"
  static_resolve static_resolve
  by unfold_locales
     (rule parity_tf_st_for_commute, rule parity_enter_st_for_commute, rule exact, simp,
      rule cs_route_indep_of_data, simp add: static_resolve_def)

lemmas parity_cs_pp_st_gen = parity_cs.pp_st

end

subsection \<open>The certified executable post-solution, generic per compiled program\<close>

context
  fixes gs :: "vname \<Rightarrow> bool" and empty_pred :: "parity exec_dg_st \<Rightarrow> bool"
    and Pi :: proc_table and ps :: "pname list" and k :: nat
  assumes solves: "pcs_terminates k gs empty_pred Pi ps"
    and exact: "\<And>s. empty_pred s = is_empty_state (fun_of_resolved_st_q_for gs s)"
begin

lemma pcs_solve_dom:
  "TD_side_always_join_Interp.solve_dom TYPE(call_string_gk) TYPE((parity exec_dg_st lifted, parity exec_dg_st lifted) dg_state)
     (pcs_eqs k gs empty_pred Pi ps) (cfg_exit (compile_prog Pi ps), [])"
  using solves[unfolded pcs_terminates_def] .

lemma pcs_pp_st:
  "part_post_solution (pcs_eqs k gs empty_pred Pi ps) (cfg_exit (compile_prog Pi ps), [])
     (snd (pcs_sol k gs empty_pred Pi ps)) (fst (pcs_sol k gs empty_pred Pi ps))"
  using TD_side_always_join_Interp.partial_post_solution
          [OF pcs_solve_dom, of "fst (pcs_sol k gs empty_pred Pi ps)"
             "snd (pcs_sol k gs empty_pred Pi ps)"]
  unfolding pcs_sol_def by simp

text \<open>The solver's post-solution, for the unbuffered routed generator at the executable
  spec: the shape \<^locale>\<open>call_string_routed_context\<close> consumes directly.\<close>

theorem pcs_pp_routed:
  "part_post_solution
     (side_cfg_T_eff_keyed_seed_dg intra_predecessor_addr_list (\<lambda>_. Call_String_Context.Global)
        (cs_route k)
        (\<lambda>ctx' src a. dg_spec_edge_tree (pctx_spec gs empty_pred) a src
           (\<lambda>_. Call_String_Context.Global))
        (routed_cmb_g (pctx_spec gs empty_pred) Call_String_Context.Global
           Call_String_Context.Seed (static_resolve (compile_prog Pi ps)))
        (routed_extra_g Call_String_Context.Seed Call_String_Context.Global)
        (compile_prog Pi ps) Bot (Lifted cinit_parity_st) Bot)
     (cfg_exit (compile_prog Pi ps), [])
     (snd (pcs_sol k gs empty_pred Pi ps)) (fst (pcs_sol k gs empty_pred Pi ps))"
  using pcs_pp_st unfolding pcs_eqs_def pctx_spec_def by (rule parity_cs_pp_st_gen[OF exact])
end

subsection \<open>The analysis-level result at the call-string context\<close>

text \<open>
  Nothing below is call-string-specific beyond the routing pair
  \<^const>\<open>cs_route\<close>/\<^const>\<open>cs_context\<close> and the seed-key encoding: the solved-table
  reader, its two coverage obligations and the published result all come from the
  generic composition, which is why this context reaches the same activation-collect
  theorem the unit context reaches.
\<close>

definition pcs_sg_st ::
    "nat \<Rightarrow> (vname \<Rightarrow> bool) \<Rightarrow> (parity exec_dg_st \<Rightarrow> bool) \<Rightarrow> proc_table \<Rightarrow> pname list
       \<Rightarrow> pp \<times> call_string + call_string_gk \<Rightarrow> parity exec_dg_st lifted" where
  "pcs_sg_st k gs empty_pred Pi ps =
     solved_local_reader (fst (pcs_sol k gs empty_pred Pi ps))
                         (snd (pcs_sol k gs empty_pred Pi ps))"

context
  fixes gs :: "vname \<Rightarrow> bool" and empty_pred :: "parity exec_dg_st \<Rightarrow> bool"
    and Pi :: proc_table and ps :: "pname list" and k :: nat
  assumes solves: "pcs_terminates k gs empty_pred Pi ps"
    and exact: "\<And>s. empty_pred s = is_empty_state (fun_of_resolved_st_q_for gs s)"
    and entry_cov:
      "(cfg_entry (compile_prog Pi ps), []) \<in> fst (pcs_sol k gs empty_pred Pi ps)"
    and fwd_ok: "\<And>u a v ctx. (u, ctx) \<in> fst (pcs_sol k gs empty_pred Pi ps)
                   \<Longrightarrow> (u, a, v) \<in> intra (compile_prog Pi ps)
                   \<Longrightarrow> (v, ctx) \<in> fst (pcs_sol k gs empty_pred Pi ps)"
    and call_fwd_ok: "\<And>u ctx dst pars args p cont d.
        (u, ctx) \<in> fst (pcs_sol k gs empty_pred Pi ps)
        \<Longrightarrow> (u, CallEdge dst pars args, FunctionEntry p, cont) \<in> calls (compile_prog Pi ps)
        \<Longrightarrow> (FunctionEntry p, cs_route k u ctx d (CallEdge dst pars args))
              \<in> fst (pcs_sol k gs empty_pred Pi ps)"
    and comb_fwd_ok: "\<And>cl c1 dst pars args p cont.
        (cl, c1) \<in> fst (pcs_sol k gs empty_pred Pi ps)
        \<Longrightarrow> (cl, CallEdge dst pars args, FunctionEntry p, cont) \<in> calls (compile_prog Pi ps)
        \<Longrightarrow> (cont, c1) \<in> fst (pcs_sol k gs empty_pred Pi ps)"
begin

lemma pcs_cinit_le_cinit_parity_st:
  "cinit_stores gs \<subseteq> pctx_gamma gs (Lifted cinit_parity_st) Bot"
  by (auto simp: pctx_gamma_def cinit_stores_def gamma_state_def
                 fun_of_resolved_st_q_for_def fun_of_st_cinit_parity_st_for)

interpretation pcs_dg_base: sound_dg_spec "pctx_spec gs empty_pred" "pctx_gamma gs" gs
  by (rule pctx_sound_exec[OF exact])

interpretation pcs_adapter: routed_analysis_sound
    "pctx_spec gs empty_pred" "pctx_gamma gs" gs
    "compile_prog Pi ps" Call_String_Context.Global "cs_route k"
    Bot "Lifted cinit_parity_st" Bot
    "snd (pcs_sol k gs empty_pred Pi ps)" "fst (pcs_sol k gs empty_pred Pi ps)"
    "(cfg_exit (compile_prog Pi ps), [])"
    Call_String_Context.Seed "cs_context k"
    "map_lift (fun_of_resolved_st_q_for gs)" parity_classify_check
proof (unfold_locales, goal_cases FinE PP SgCov SgUncov Fwd FinC SeedKey ResolveSound
    RouteEnterc CallFwd CombFwd EnterAgree GammaRd ClProved ClRefuted)
  case FinE show ?case using compile_prog_finite by auto
next
  case PP show ?case by (rule pcs_pp_routed[OF solves exact])
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
  case FinC show ?case by (simp add: compile_prog_finite)
next
  case (SeedKey p ctx) show ?case by simp
next
  case (ResolveSound u ctx dst pars args p cont s)
  thus ?case by (simp add: static_resolve_iff compile_prog_finite)
next
  case (RouteEnterc u ctx dst pars args p cont s)
  show ?case by (rule cs_route_context_agree)
next
  case (CallFwd u ctx dst pars args p cont)
  show ?case using call_fwd_ok[OF CallFwd(1,2)] by (simp add: cs_route_def)
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
  case (GammaRd d g') show ?case by (simp add: pctx_gamma_def)
next
  case (ClProved c d s) thus ?case by (rule parity_classify_check_proved)
next
  case (ClRefuted c d s) thus ?case by (rule parity_classify_check_refuted)
qed

theorem pcs_activation_collect_sound:
  "activation_collect gs (cs_context k) [] (compile_prog Pi ps) (cinit_stores gs) v ctx
     \<subseteq> gamma_state_lift (map_lift (fun_of_resolved_st_q_for gs)
           (pcs_sg_st k gs empty_pred Pi ps (Inl (v, ctx))))"
  unfolding pcs_sg_st_def
  by (rule pcs_adapter.routed_activation_collect_sound
        [OF entry_cov pcs_cinit_le_cinit_parity_st])

end

subsection \<open>Whole-program convenience layer\<close>

definition pcs_eqs_prog ::
    "nat \<Rightarrow> (vname \<Rightarrow> bool) \<Rightarrow> imp_prog
       \<Rightarrow> (pp \<times> call_string, call_string_gk, (parity exec_dg_st lifted, parity exec_dg_st lifted) dg_state) eqsT" where
  "pcs_eqs_prog k gs p =
     pcs_eqs k gs (resolved_st_q_is_bot_for (declared_global_vars p))
       (prog_table p) (prog_procs p)"

definition pcs_sol_prog ::
    "nat \<Rightarrow> (vname \<Rightarrow> bool) \<Rightarrow> imp_prog
       \<Rightarrow> (pp \<times> call_string) set \<times> (pp \<times> call_string + call_string_gk \<Rightarrow> (parity exec_dg_st lifted, parity exec_dg_st lifted) dg_state)" where
  "pcs_sol_prog k gs p =
     pcs_sol k gs (resolved_st_q_is_bot_for (declared_global_vars p))
       (prog_table p) (prog_procs p)"

definition pcs_terminates_prog :: "nat \<Rightarrow> (vname \<Rightarrow> bool) \<Rightarrow> imp_prog \<Rightarrow> bool" where
  "pcs_terminates_prog k gs p =
     pcs_terminates k gs (resolved_st_q_is_bot_for (declared_global_vars p))
       (prog_table p) (prog_procs p)"

lemma pcs_terminates_prog_via_solve_c:
  assumes "TD_side_always_join_Interp_solve_c
             (pcs_eqs_prog k gs p)
             (cfg_exit (compile_prog (prog_table p) (prog_procs p)), []) \<noteq> None"
  shows "pcs_terminates_prog k gs p"
  using assms
  unfolding pcs_terminates_prog_def pcs_eqs_prog_def
  by (rule pcs_terminates_via_solve_c)

section \<open>Solved-result table\<close>

text \<open>
  The solved call-string D/G system, read as a \<^typ>\<open>(call_string, parity abs_state)
  analysis_result\<close>. The covered-key set is the solver's own, never an enumerated
  theoretical context space.
\<close>

definition analyse_parity_call_string_result_for ::
    "nat \<Rightarrow> (vname \<Rightarrow> bool) \<Rightarrow> imp_prog \<Rightarrow> (call_string, parity abs_state) analysis_result" where
  "analyse_parity_call_string_result_for k gs p =
     Analysis_Result
       (fst (pcs_sol_prog k gs p))
       (\<lambda>v ctx. normalize_point gs
                  (canonicalize_lift (resolved_st_q_is_bot_for (declared_global_vars p))
                    (locals (snd (pcs_sol_prog k gs p) (Inl (v, ctx))))))"

declare analyse_parity_call_string_result_for_def [code del]

lemma analyse_parity_call_string_result_for_code [code]:
  "analyse_parity_call_string_result_for k gs p =
     (let sol = pcs_sol_prog k gs p; gl = declared_global_vars p
      in Analysis_Result (fst sol)
           (\<lambda>v ctx. normalize_point gs
                      (canonicalize_lift (resolved_st_q_is_bot_for gl)
                        (locals (snd sol (Inl (v, ctx)))))))"
  unfolding analyse_parity_call_string_result_for_def Let_def by (rule refl)

definition analyse_parity_call_string_result ::
    "nat \<Rightarrow> imp_prog \<Rightarrow> (call_string, parity abs_state) analysis_result" where
  "analyse_parity_call_string_result k p =
     analyse_parity_call_string_result_for k (declared_global p) p"

section \<open>Contextual check report\<close>

text \<open>
  \<^const>\<open>classify_checks_ctx\<close>/\<^const>\<open>classify_checks_verdicts\<close> are generic in the
  context type already, so nothing call-string-specific is needed here beyond supplying
  the call-string result table and Parity's own \<open>parity_classify_check\<close>.
\<close>

definition pcs_check_projection ::
    "nat \<Rightarrow> imp_prog \<Rightarrow> (pp \<times> exp \<times> (call_string \<times> contextual_verdict) set) list" where
  "pcs_check_projection k p =
     classify_checks_ctx (prog_cfg p)
       (analyse_parity_call_string_result_for k (declared_global p) p)
       parity_classify_check"

definition pcs_verdict_report_prog ::
    "nat \<Rightarrow> imp_prog \<Rightarrow> (pp \<times> exp \<times> contextual_verdict) list" where
  "pcs_verdict_report_prog k p =
     map (\<lambda>(u, c, vs). (u, c, aggregate_verdicts (snd ` vs)))
       (pcs_check_projection k p)"

lemma pcs_verdict_report_prog_eq:
  "pcs_verdict_report_prog k p =
     classify_checks_verdicts (prog_cfg p)
       (analyse_parity_call_string_result_for k (declared_global p) p)
       parity_classify_check"
  unfolding pcs_verdict_report_prog_def pcs_check_projection_def
  by (rule classify_checks_verdicts_proj)

definition analyse_parity_call_string_report ::
    "nat \<Rightarrow> imp_prog \<Rightarrow> (pp \<times> exp \<times> contextual_verdict) list" where
  "analyse_parity_call_string_report k p = pcs_verdict_report_prog k p"


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
  \<open>entry_exec_route\<close>/\<open>entry_exec_route_gen\<close> (\<^theory>\<open>Voblint_Exec.DG_Local_State_Exec\<close>),
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
