theory Interval_Analyses
  imports
    "Voblint_Analysis.Interval_Sound"
    "Voblint_Analysis.Interval_Classify"
    "Voblint_Analysis.Interval_Transfer"
    "Voblint_Analysis.Interval_Exec_Sound"
    "Voblint_Exec.Result_Normalization"
    "Voblint_Exec.Routed_Domain_Exec"
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
    Call_String_Routed_Context
    Entry_State_Routed_Context
begin
chapter \<open>How Interval is run under each supported context policy\<close>

text \<open>
  Interval's analysis package -- specification, concretization and soundness --
  lives in \<^theory>\<open>Voblint_Analysis.Interval_Sound\<close> and mentions no context.
  This theory supplies the configurations: for each supported context policy,
  the equation system that pairing generates, its solved table, the coverage
  premises the solver's reachable set must satisfy, and the result and report
  tables a caller consumes.

  Interval carries a second axis the other domains do not: besides the default
  always-join solver, the same configurations are instantiated at the PerOrigin,
  Apinis-warrowing and warrowing-per-origin disciplines. Which solver runs an
  equation system is independent of which context policy generated it, and both
  axes appear here.

  Global keys are \<^type>\<open>routed_gk\<close>, with \<^const>\<open>Analysis_Global\<close> at
  \<^typ>\<open>unit\<close> since Interval publishes no named global of its own; the
  call-string configuration uses the shared \<^typ>\<open>call_string_gk\<close>.
\<close>

section \<open>Interval at the routed spine, instantiated at the unit context\<close>

text \<open>
  A second soundness derivation at the routed D/G spine
  (\<^locale>\<open>dg_ctx_activation_base\<close>, \<^locale>\<open>unit_routed_context\<close>) that Interval's own
  entry-state and call-string context analyses already use, going directly
  through that generic machinery rather than through a packaged registration
  locale (Interval's production route, \<open>Interval_Exec_Sound\<close>, goes the packaged
  way instead). The context here is \<^typ>\<open>unit\<close>: \<^locale>\<open>unit_routed_context\<close>
  (\<^theory>\<open>Voblint_Framework.Routed_Context_Unit\<close>) fixes \<^const>\<open>route_unit\<close>, so every
  routing-agreement obligation a non-trivial routed instance must prove from its
  own transfer facts collapses here to a free lemma about the constant function
  \<^const>\<open>route_unit\<close> --- exactly the collapse Sign's own unit-context instance
  (\<open>Sign_Analyses\<close>) already exercises.

  Soundness below is derived directly from \<^locale>\<open>dg_ctx_activation_base\<close>'s
  generic machinery against the collecting semantics, exactly as Interval's
  entry-state analysis is derived.
\<close>

text \<open>
  \<^typ>\<open>unit\<close> context, so the seed constructor's second field is \<^typ>\<open>unit\<close> rather
  than an interesting per-context payload: exactly one seed slot per callee entry.
\<close>


subsection \<open>The routed unit-context D/G spec\<close>

text \<open>
  The same Base-style whole-state specification Interval's own production
  \<^const>\<open>analyse_interval_dg_eqs_for\<close> already solves over
  (\<^theory>\<open>Voblint_Analysis.Interval_Exec_Sound\<close>), at the same
  \<^const>\<open>ivl_tf_st_for\<close>/\<^const>\<open>ivl_enter_st_for\<close> primitives -- byte-for-byte the
  term \<open>local_state_dg_spec_st_for_lifted gs empty_pred (ivl_tf_st_for gs) (ivl_enter_st_for gs)\<close>
  \<^const>\<open>analyse_interval_dg_eqs_for\<close> feeds \<^const>\<open>unit_routed_eqs\<close>. Only the
  routed generator variant wrapping this spec changes: the unbuffered
  \<^const>\<open>unit_routed_eqs\<close> there, the buffered
  \<^const>\<open>routed_node_rhs_buffered\<close> here (deduplicating repeated
  writes to one key within a single RHS evaluation) --- the spec itself, and
  every domain-transfer soundness fact about it, is untouched.
\<close>

subsection \<open>The routed equation system and its executable solution\<close>

text \<open>
  Solved under the always-join update rule, mirroring Sign's own choice: the
  minimal solver instance needed to prove direct soundness once. Interval's
  production route needs Apinis warrowing for termination on an unbounded local
  loop (\<^theory>\<open>Voblint_Analysis.Interval_Exec_Sound\<close>'s own
  \<open>analyse_interval_dg_for\<close>); that solver choice is orthogonal to this context
  (commit \<open>c38efade\<close>) and is future work here, not attempted.
\<close>

definition interval_conf_eqs ::
    "(vname \<Rightarrow> bool) \<Rightarrow> (ivl exec_dg_st \<Rightarrow> bool) \<Rightarrow> proc_table \<Rightarrow> pname list \<Rightarrow> (pp \<times> unit, (unit, unit) routed_gk, (ivl exec_dg_st lifted, ivl exec_dg_st lifted) dg_state) eqsT" where
  "interval_conf_eqs gs empty_pred Pi ps =
     routed_node_rhs_buffered intra_predecessor_addr_list (\<lambda>_. Analysis_Global ())
       route_unit
       (\<lambda>ctx' src a. dg_spec_edge_tree (interval_spec gs empty_pred) a src (\<lambda>_. Analysis_Global ()))
       (routed_call_tree (interval_spec gs empty_pred) (Analysis_Global ()) Activation_Seed
          (static_resolve (compile_prog Pi ps)) (\<lambda>d. d = Bot))
       (routed_entry_seed_tree Activation_Seed)
       (compile_prog Pi ps) Bot (Lifted cinit_ivl_st) Bot"

definition interval_conf_sol ::
    "(vname \<Rightarrow> bool) \<Rightarrow> (ivl exec_dg_st \<Rightarrow> bool) \<Rightarrow> proc_table \<Rightarrow> pname list \<Rightarrow> (pp \<times> unit) set \<times> (pp \<times> unit + (unit, unit) routed_gk \<Rightarrow> (ivl exec_dg_st lifted, ivl exec_dg_st lifted) dg_state)" where
  "interval_conf_sol gs empty_pred Pi ps =
     TD_side_always_join_Interp_solve (interval_conf_eqs gs empty_pred Pi ps)
       (cfg_exit (compile_prog Pi ps), ())"

definition interval_conf_terminates ::
    "(vname \<Rightarrow> bool) \<Rightarrow> (ivl exec_dg_st \<Rightarrow> bool) \<Rightarrow> proc_table \<Rightarrow> pname list \<Rightarrow> bool" where
  "interval_conf_terminates gs empty_pred Pi ps =
     TD_side_always_join_Interp.solve_dom TYPE((unit, unit) routed_gk) TYPE((ivl exec_dg_st lifted, ivl exec_dg_st lifted) dg_state)
       (interval_conf_eqs gs empty_pred Pi ps) (cfg_exit (compile_prog Pi ps), ())"

lemma interval_conf_terminates_via_solve_c:
  assumes "TD_side_always_join_Interp_solve_c (interval_conf_eqs gs empty_pred Pi ps)
             (cfg_exit (compile_prog Pi ps), ()) \<noteq> None"
  shows "interval_conf_terminates gs empty_pred Pi ps"
  unfolding interval_conf_terminates_def
  by (rule TD_side_always_join_Interp.solve_dom_of_solve_c[OF assms])

lemma interval_conf_vars_finite:
  assumes "interval_conf_terminates gs empty_pred Pi ps"
  shows "finite (fst (interval_conf_sol gs empty_pred Pi ps))"
  using TD_side_always_join_Interp.finite_stabl_solve[
      OF assms[unfolded interval_conf_terminates_def]]
  unfolding interval_conf_sol_def TD_side_always_join_Interp_solve_def
  by simp

subsection \<open>Domain commute facts, at the routed unit spec\<close>
text \<open>
  The whole of Interval's obligation to the routed spine, in one interpretation.
  \<^locale>\<open>routed_domain_exec\<close> adds only the seed-key pair, its distinctness, and the
  two routing functions on top of \<^locale>\<open>routed_dg_domain_exec\<close>, so the interpretation
  carries no Interval mathematics: the first three obligations are Interval's own
  pre-existing commute lemmas, cited unchanged, and the last two are datatype
  distinctness for \<^type>\<open>routed_gk\<close> and the free routing agreement \<^const>\<open>route_unit\<close> enjoys
  by ignoring its \<open>'D\<close> argument outright.
\<close>

text \<open>The concretization the executable-carrier interpretation below uses: a local
  unknown means \<^const>\<open>gamma_state_lift\<close> of its readback, the global slot is ignored as
  in \<^const>\<open>gamma_dg_local_state\<close>. Named at top level so a downstream theory can state it.\<close>

context
  fixes gs :: "vname \<Rightarrow> bool" and empty_pred :: "ivl exec_dg_st \<Rightarrow> bool"
  assumes exact: "\<And>s. empty_pred s = is_empty_state (fun_of_resolved_st_q_for gs s)"
begin

interpretation ivl_unit: routed_domain_exec
  gs empty_pred "ivl_tf_st_for gs" "ivl_enter_st_for gs"
  skip_ivl assign_ivl special_ivl branch_ivl body_ivl return_ivl
  "enter_ivl_ci_for gs" event_ivl
  "Analysis_Global ()" Activation_Seed route_unit route_unit static_resolve static_resolve
  by unfold_locales
     (rule ivl_tf_st_for_commute[unfolded ivl_tf_abs_def], assumption,
      rule ivl_enter_st_for_commute, rule exact, simp, simp,

      simp add: static_resolve_def)

lemmas ivl_pp_st_gen = ivl_unit.pp_st

end


section \<open>The solver-generic instantiation\<close>

text \<open>
  Everything downstream of the executable post-solution reaches the solver through exactly one
  fact: that the solved pair is a \<^const>\<open>part_post_solution\<close> of \<^const>\<open>interval_conf_eqs\<close>.  The update
  rule itself never appears again.  \<open>interval_conf_solved\<close> therefore fixes the solved pair and its
  termination predicate and assumes that single fact, so each update rule contributes an
  interpretation rather than a copy of the development.

  The obligation is cheap at every instance because \<^locale>\<open>TD_side_upd_rule\<close> proves
  \<open>partial_post_solution\<close> once, inside the locale, for every update rule.
\<close>

locale interval_conf_solved =
  fixes sol :: "(vname \<Rightarrow> bool) \<Rightarrow> (ivl exec_dg_st \<Rightarrow> bool) \<Rightarrow> proc_table \<Rightarrow> pname list \<Rightarrow> (pp \<times> unit) set
                     \<times> (pp \<times> unit + (unit, unit) routed_gk \<Rightarrow> (ivl exec_dg_st lifted, ivl exec_dg_st lifted) dg_state)"
    and terminates :: "(vname \<Rightarrow> bool) \<Rightarrow> (ivl exec_dg_st \<Rightarrow> bool) \<Rightarrow> proc_table \<Rightarrow> pname list
                         \<Rightarrow> bool"
  assumes pp_st:
    "terminates gs empty_pred Pi ps
       \<Longrightarrow> part_post_solution (interval_conf_eqs gs empty_pred Pi ps)
             (cfg_exit (compile_prog Pi ps), ())
             (snd (sol gs empty_pred Pi ps))
             (fst (sol gs empty_pred Pi ps))"
    and vars_fin:
    "terminates gs empty_pred Pi ps \<Longrightarrow> finite (fst (sol gs empty_pred Pi ps))"
begin

text \<open>The solver's post-solution, for the unbuffered routed generator at the executable
  spec: the shape \<^locale>\<open>dg_ctx_activation_base\<close> consumes directly.\<close>

theorem pp_routed:
  assumes solves: "terminates gs empty_pred Pi ps"
    and exact: "\<And>s. empty_pred s = is_empty_state (fun_of_resolved_st_q_for gs s)"
  shows
  "part_post_solution
     (routed_node_rhs intra_predecessor_addr_list (\<lambda>_. Analysis_Global ()) route_unit
        (\<lambda>ctx' src a. dg_spec_edge_tree (interval_spec gs empty_pred) a src (\<lambda>_. Analysis_Global ()))
        (routed_call_tree (interval_spec gs empty_pred) (Analysis_Global ()) Activation_Seed (static_resolve (compile_prog Pi ps)) (\<lambda>d. d = Bot))
        (routed_entry_seed_tree Activation_Seed)
        (compile_prog Pi ps) Bot (Lifted cinit_ivl_st) Bot)
     (cfg_exit (compile_prog Pi ps), ())
     (snd (sol gs empty_pred Pi ps)) (fst (sol gs empty_pred Pi ps))"
  using pp_st[OF solves] unfolding interval_conf_eqs_def interval_spec_def by (rule ivl_pp_st_gen[OF exact])

subsection \<open>Activation-indexed collecting soundness, generic per compiled program\<close>

text \<open>
  The routed spine is interpreted at Interval's executable carrier and fed the solver's own
  table: a local unknown concretizes to \<^const>\<open>gamma_state_lift\<close> of its readback, the
  covered reader \<open>sg_st\<close> hands the table's local slot through unchanged, and no solved
  system is transported between carriers.
\<close>

definition sg_st ::
    "(vname \<Rightarrow> bool) \<Rightarrow> (ivl exec_dg_st \<Rightarrow> bool) \<Rightarrow> proc_table \<Rightarrow> pname list
       \<Rightarrow> pp \<times> unit + (unit, unit) routed_gk \<Rightarrow> ivl exec_dg_st lifted" where
  "sg_st gs empty_pred Pi ps =
     solved_local_reader (fst (sol gs empty_pred Pi ps)) (snd (sol gs empty_pred Pi ps))"

context
  fixes gs :: "vname \<Rightarrow> bool" and empty_pred :: "ivl exec_dg_st \<Rightarrow> bool"
    and Pi :: proc_table and ps :: "pname list"
  assumes solves: "terminates gs empty_pred Pi ps"
    and exact: "\<And>s. empty_pred s = is_empty_state (fun_of_resolved_st_q_for gs s)"
    and entry_cov: "(cfg_entry (compile_prog Pi ps), ()) \<in> fst (sol gs empty_pred Pi ps)"
    and fwd_ok: "\<And>u a v ctx. (u, ctx) \<in> fst (sol gs empty_pred Pi ps)
                   \<Longrightarrow> (u, a, v) \<in> intra (compile_prog Pi ps)
                   \<Longrightarrow> (v, ctx) \<in> fst (sol gs empty_pred Pi ps)"
    and call_fwd_ok: "\<And>u ctx dst pars args p cont.
        (u, ctx) \<in> fst (sol gs empty_pred Pi ps)
        \<Longrightarrow> (u, CallEdge dst pars args, FunctionEntry p, cont) \<in> calls (compile_prog Pi ps)
        \<Longrightarrow> (FunctionEntry p, ()) \<in> fst (sol gs empty_pred Pi ps)"
    and comb_fwd_ok: "\<And>cl c1 dst pars args p cont.
        (cl, c1) \<in> fst (sol gs empty_pred Pi ps)
        \<Longrightarrow> (cl, CallEdge dst pars args, FunctionEntry p, cont) \<in> calls (compile_prog Pi ps)
        \<Longrightarrow> (cont, c1) \<in> fst (sol gs empty_pred Pi ps)"
begin

subsubsection \<open>The solver's table as the solved system\<close>

interpretation ivl_compiled: compiled_cfg Pi ps "compile_prog Pi ps"
  by (unfold_locales; simp add: compile_prog_finite)

lemmas fin = ivl_compiled.finite_intra
lemmas finC = ivl_compiled.finite_calls

lemma sg_st_covered:
  "(v, ctx) \<in> fst (sol gs empty_pred Pi ps)
   \<Longrightarrow> sg_st gs empty_pred Pi ps (Inl (v, ctx))
         = locals (snd (sol gs empty_pred Pi ps) (Inl (v, ctx)))"
  by (simp add: sg_st_def)

lemma sg_st_uncovered_empty:
  "(v, ctx) \<notin> fst (sol gs empty_pred Pi ps)
     \<Longrightarrow> gamma_state_lift (map_lift (fun_of_resolved_st_q_for gs)
           (sg_st gs empty_pred Pi ps (Inl (v, ctx)))) = {}"
  by (simp add: sg_st_def)

subsubsection \<open>Instantiating the generic DG-native activation discharge\<close>

interpretation dg_base: sound_dg_spec_core "interval_spec gs empty_pred" "interval_gamma gs" gs
  by (rule interval_sound_exec[OF exact])

interpretation routed: unit_routed_context "interval_spec gs empty_pred" "interval_gamma gs" gs
    "compile_prog Pi ps" "Analysis_Global ()" Bot "Lifted cinit_ivl_st" Bot
    "snd (sol gs empty_pred Pi ps)" "fst (sol gs empty_pred Pi ps)"
    "(cfg_exit (compile_prog Pi ps), ())" "sg_st gs empty_pred Pi ps" Activation_Seed
    "\<lambda>d. d = Bot" "\<lambda>m. gamma_state_lift (map_lift (fun_of_resolved_st_q_for gs) m)"
proof (unfold_locales, goal_cases FinE PP SgCov SgUncov Fwd FinC CallsUnique SeedKey
    IsBotBot IsBotSound EnterComplete CallFwd CombFwd)
  case FinE show ?case by (rule fin)
next
  case PP show ?case by (rule pp_routed[OF solves exact])
next
  case (SgCov v ctx) then show ?case
    by (simp add: sg_st_def interval_gamma_def)
next
  case (SgUncov v ctx) then show ?case by (rule sg_st_uncovered_empty)
next
  case (Fwd u a v ctx) then show ?case by (rule fwd_ok)
next
  case FinC show ?case by (rule finC)
next
  case CallsUnique
  show ?case unfolding calls_source_unique_def using compile_prog_calls_source_unique by blast
next
  case (SeedKey p ctx) show ?case by simp
next
  case IsBotBot show ?case by simp
next
  case (IsBotSound d gv) then show ?case by simp
next
  case (EnterComplete u ctx dst pars args p cont s)
  let ?ci = "call_info_of (CallEdge dst pars args) p"
  let ?caller = "locals (snd (sol gs empty_pred Pi ps) (Inl (u, ctx)))"
  have cov: "entry_pairs_cover
      (\<lambda>d. interval_gamma gs d (globs (snd (sol gs empty_pred Pi ps) (Inr (Analysis_Global ())))))
      s (call_enter gs (CallEdge dst pars args) s)
      [(?caller, transfer_lift empty_pred (ivl_enter_st_for gs ?ci) ?caller)]"
    using interval_entry_cover_exec[OF exact EnterComplete(3), where ci = ?ci] by simp
  show ?case
    unfolding interval_spec_def dgs_enter_local_state_st_for_lifted
    using enter_runs_local_enter_transfer enter_deps_local_enter_transfer cov by fastforce
next
  case (CallFwd u ctx dst pars args p cont)
  show ?case using CallFwd(1,2) call_fwd_ok unfolding route_unit_def by blast
next
  case (CombFwd cl c1 dst pars args p cont)
  show ?case using CombFwd(1,2) comb_fwd_ok by blast
qed

subsubsection \<open>Activation-indexed collecting soundness\<close>


subsubsection \<open>Activation-indexed collecting soundness\<close>

lemma cinit_le_cinit_ivl_st:
  "cinit_stores gs \<subseteq> interval_gamma gs (Lifted cinit_ivl_st) Bot"
  by (auto simp: interval_gamma_def cinit_stores_def gamma_state_def fun_of_resolved_st_q_for_def
                 fun_of_st_cinit_ivl_st)

subsubsection \<open>The generic report adapter\<close>

text \<open>
  Interpreting \<^locale>\<open>dg_analysis_adapter\<close> at this context's own solved
  system reuses every obligation already discharged for \<open>dg\<close>/\<open>routed\<close>
  above: the five \<^locale>\<open>dg_ctx_activation_base\<close> obligations are exactly
  \<open>dg\<close>'s own, and the routed obligations collapse the same way
  \<^locale>\<open>unit_routed_context\<close>'s did, at \<^const>\<open>route_unit\<close>/\<^const>\<open>enterc_unit\<close>.
  Only \<open>classify_proved\<close>/\<open>classify_refuted\<close> are genuinely new, discharged by
  Interval's own \<open>interval_classify_check_proved\<close>/\<open>interval_classify_check_refuted\<close>
  (\<^theory>\<open>Voblint_Analysis.Interval_Classify\<close>).
\<close>

interpretation adapter: dg_analysis_adapter "interval_spec gs empty_pred" "interval_gamma gs" gs
    "compile_prog Pi ps" "Analysis_Global ()" route_unit Bot "Lifted cinit_ivl_st" Bot
    "snd (sol gs empty_pred Pi ps)" "fst (sol gs empty_pred Pi ps)"
    "(cfg_exit (compile_prog Pi ps), ())" "sg_st gs empty_pred Pi ps"
    Activation_Seed "\<lambda>d. d = Bot"
    "\<lambda>m. gamma_state_lift (map_lift (fun_of_resolved_st_q_for gs) m)"
    "call_context_rel_of_fun enterc_unit"
    "map_lift (fun_of_resolved_st_q_for gs)" interval_classify_check
proof (unfold_locales, goal_cases FinE PP SgCov SgUncov Fwd FinC CallsUnique SeedKey
    IsBotBot IsBotSound ResolveSound
    EnterCover EnterTotal CombFwd GammaRd ClProved ClRefuted VarsFin)
  case FinE show ?case by (rule fin)
next
  case PP show ?case by (rule pp_routed[OF solves exact])
next
  case (SgCov v c)
  thus ?case by (simp add: sg_st_def interval_gamma_def)
next
  case (SgUncov v c)
  thus ?case by (simp add: sg_st_def)
next
  case (Fwd u a v c)
  thus ?case by (rule fwd_ok)
next
  case FinC show ?case by (rule finC)
next
  case CallsUnique
  show ?case unfolding calls_source_unique_def using compile_prog_calls_source_unique by blast
next
  case (SeedKey p ctx) show ?case by simp
next
  case IsBotBot show ?case by simp
next
  case (IsBotSound d g') then show ?case by simp
next
  case (ResolveSound u ctx dst pars args p cont s)
  thus ?case by (simp add: static_resolve_iff[OF finC])
next
  case (EnterCover u ctx dst pars args p cont s ctx')
  have ctx'_eq: "ctx' = ()" by simp
  let ?ci = "call_info_of (CallEdge dst pars args) p"
  let ?caller = "locals (snd (sol gs empty_pred Pi ps) (Inl (u, ctx)))"
  have cov: "entry_pairs_cover
      (\<lambda>d. interval_gamma gs d (globs (snd (sol gs empty_pred Pi ps) (Inr (Analysis_Global ())))))
      s (call_enter gs (CallEdge dst pars args) s)
      [(?caller, transfer_lift empty_pred (ivl_enter_st_for gs ?ci) ?caller)]"
    using interval_entry_cover_exec[OF exact EnterCover(3), where ci = ?ci] by simp
  show ?case
    unfolding interval_spec_def dgs_enter_local_state_st_for_lifted ctx'_eq
    using enter_runs_local_enter_transfer enter_deps_local_enter_transfer cov
          call_fwd_ok[OF EnterCover(1,2)]
    by (fastforce simp: entry_pairs_cover_def)
next
  case (EnterTotal u ctx dst pars args p cont s)
  show ?case by simp
next
  case (CombFwd cl c1 dst pars args p cont)
  show ?case using CombFwd(1,2) comb_fwd_ok by blast
next
  case (GammaRd d g')
  show ?case by (simp add: interval_gamma_def)
next
  case (ClProved c d s)
  thus ?case by (rule interval_classify_check_proved)
next
  case (ClRefuted c d s)
  thus ?case by (rule interval_classify_check_refuted)
next
  case VarsFin show ?case by (rule vars_fin[OF solves])
qed

text \<open>
  The two generic soundness corollaries \<^locale>\<open>dg_analysis_adapter\<close> derives
  once and for all -- \<open>adapter.analyse_report_ctx_proved_sound\<close>,
  \<open>adapter.analyse_report_ctx_refuted_sound\<close> -- are available here without
  any further proof: an improvement over Sign's own file, which predates this
  locale and hand-rolls a report table with no soundness theorem attached.
\<close>

lemmas report_ctx_proved_sound = adapter.analyse_report_ctx_proved_sound
lemmas report_ctx_refuted_sound = adapter.analyse_report_ctx_refuted_sound

text \<open>
  \<open>result_node_sound\<close> re-exports the adapter's generic node-soundness bridge
  (\<^theory>\<open>Voblint_Framework.DG_Analysis_Adapter\<close>). \<open>analyse_result_eq\<close> identifies that
  reading with the raw-tuple shape \<open>analyse_interval_ctx_result_for\<close> (defined below)
  already builds by hand, identical for every update rule.
\<close>

lemmas result_node_sound = adapter.analyse_result_node_sound

lemma analyse_result_eq:
  "lookup_context adapter.analyse_result v ctx =
     (if (v, ctx) \<in> fst (sol gs empty_pred Pi ps)
      then normalize_point gs
             (canonicalize_lift empty_pred (locals (snd (sol gs empty_pred Pi ps) (Inl (v, ctx)))))
      else Bot)"
  unfolding adapter.lookup_context_analyse_result
  by (cases "locals (snd (sol gs empty_pred Pi ps) (Inl (v, ctx)))")
     (simp_all add: exact normalize_lift_def)

end

end

text \<open>The always-join rule as an instance.  \<open>partial_post_solution\<close> is the whole obligation,
  and \<^locale>\<open>TD_side_upd_rule\<close> already carries it.\<close>

lemma interval_conf_join_pp_st:
  "interval_conf_terminates gs empty_pred Pi ps
     \<Longrightarrow> part_post_solution (interval_conf_eqs gs empty_pred Pi ps)
           (cfg_exit (compile_prog Pi ps), ())
           (snd (interval_conf_sol gs empty_pred Pi ps))
           (fst (interval_conf_sol gs empty_pred Pi ps))"
  unfolding interval_conf_sol_def interval_conf_terminates_def
  by (rule TD_side_always_join_Interp.partial_post_solution[OF _ surjective_pairing])

global_interpretation interval_conf_join: interval_conf_solved interval_conf_sol interval_conf_terminates
proof (unfold_locales, goal_cases PpSt VarsFin)
  case (PpSt gs empty_pred Pi ps) thus ?case by (rule interval_conf_join_pp_st)
next
  case (VarsFin gs empty_pred Pi ps) thus ?case by (rule interval_conf_vars_finite)
qed

lemmas interval_conf_result_node_sound = interval_conf_join.result_node_sound
lemmas interval_conf_analyse_result_eq = interval_conf_join.analyse_result_eq
lemmas interval_conf_cinit_le_cinit_ivl_st = interval_conf_join.cinit_le_cinit_ivl_st
lemmas interval_conf_report_ctx_proved_sound = interval_conf_join.report_ctx_proved_sound
lemmas interval_conf_report_ctx_refuted_sound = interval_conf_join.report_ctx_refuted_sound

section \<open>Solved-result table\<close>

text \<open>
  Whole-program convenience layer, interpreting \<^locale>\<open>dg_analysis_adapter\<close>
  directly rather than hand-rolling a temporary adapter the way Sign's own file (predating that
  locale) had to. \<open>interval_conf_eqs_prog\<close>/\<open>interval_conf_sol_prog\<close>/\<open>interval_conf_terminates_prog\<close> mirror
  Interval's own \<open>entry_state_eqs_prog\<close>/\<open>entry_state_sol_prog\<close>/
  \<open>entry_state_terminates_prog\<close>.
\<close>

definition interval_conf_eqs_prog ::
    "(vname \<Rightarrow> bool) \<Rightarrow> imp_prog
       \<Rightarrow> (pp \<times> unit, (unit, unit) routed_gk, (ivl exec_dg_st lifted, ivl exec_dg_st lifted) dg_state) eqsT" where
  "interval_conf_eqs_prog gs p =
     interval_conf_eqs gs (resolved_st_q_is_bot_for (declared_global_vars p))
       (prog_table p) (prog_procs p)"

definition interval_conf_sol_prog ::
    "(vname \<Rightarrow> bool) \<Rightarrow> imp_prog
       \<Rightarrow> (pp \<times> unit) set \<times> (pp \<times> unit + (unit, unit) routed_gk \<Rightarrow> (ivl exec_dg_st lifted, ivl exec_dg_st lifted) dg_state)" where
  "interval_conf_sol_prog gs p =
     TD_side_always_join_Interp_solve (interval_conf_eqs_prog gs p) (cfg_exit (prog_cfg p), ())"

definition interval_conf_terminates_prog :: "(vname \<Rightarrow> bool) \<Rightarrow> imp_prog \<Rightarrow> bool" where
  "interval_conf_terminates_prog gs p =
     interval_conf_terminates gs (resolved_st_q_is_bot_for (declared_global_vars p))
       (prog_table p) (prog_procs p)"

lemma interval_conf_terminates_prog_via_solve_c:
  assumes "TD_side_always_join_Interp_solve_c
             (interval_conf_eqs gs (resolved_st_q_is_bot_for (declared_global_vars p))
                (prog_table p) (prog_procs p))
             (cfg_exit (compile_prog (prog_table p) (prog_procs p)), ()) \<noteq> None"
  shows "interval_conf_terminates_prog gs p"
  unfolding interval_conf_terminates_prog_def
  using assms by (rule interval_conf_terminates_via_solve_c)

definition analyse_interval_ctx_result_for ::
    "(vname \<Rightarrow> bool) \<Rightarrow> imp_prog \<Rightarrow> (unit, ivl abs_state) analysis_result" where
  "analyse_interval_ctx_result_for gs p =
     Analysis_Result
       (fst (interval_conf_sol_prog gs p))
       (\<lambda>v ctx. normalize_point gs
                  (canonicalize_lift (resolved_st_q_is_bot_for (declared_global_vars p))
                    (locals (snd (interval_conf_sol_prog gs p) (Inl (v, ctx))))))"

declare analyse_interval_ctx_result_for_def [code del]

lemma analyse_interval_ctx_result_for_code [code]:
  "analyse_interval_ctx_result_for gs p =
     (let sol = interval_conf_sol_prog gs p; gl = declared_global_vars p
      in Analysis_Result (fst sol)
           (\<lambda>v ctx. normalize_point gs
                      (canonicalize_lift (resolved_st_q_is_bot_for gl)
                        (locals (snd sol (Inl (v, ctx)))))))"
  unfolding analyse_interval_ctx_result_for_def Let_def by (rule refl)

definition analyse_interval_ctx_result :: "imp_prog \<Rightarrow> (unit, ivl abs_state) analysis_result" where
  "analyse_interval_ctx_result p =
     analyse_interval_ctx_result_for (declared_global p) p"

section \<open>Generic executable call-string context analysis for Interval\<close>

text \<open>
  The call-string sibling of the entry-state configuration below's entry-state pipeline:
  same \<open>interval_spec\<close> D/G specification, same executable Warrow solve, routed at
  \<^const>\<open>Call_String_Context.cs_route\<close> with a runtime bound \<open>k\<close> instead of at the
  entered callee formals. The packaging-correspondence facts the entry-state
  pipeline needs come from interpreting \<^locale>\<open>routed_domain_exec\<close> once, as
  \<open>ivl_es\<close>, giving \<open>ivl_es.sound_dg_spec_core_st\<close> directly at the executable
  carrier; that interpretation is already generic in the routing policy, so
  nothing here re-derives it.

  This covers only the executable/result/report path, mirroring exactly what
  the entry-state configuration below's own unconditional section
  (\<open>analyse_interval_entry_state_result_for\<close> onward) provides: no premise here
  needs \<open>call_fwd\<close>/\<open>comb_fwd\<close> (\<open>Call_String_Routed_Context\<close>),
  matching the entry-state pipeline's own current posture, where the shipped
  \<open>analyse_interval_entry_state_result_for\<close> is likewise unconditional and
  the generic activation-collecting-soundness theorem is separate, open work.
\<close>

subsection \<open>The routed equation system and its executable solution\<close>

text \<open>
  \<^const>\<open>Call_String_Context.cs_route\<close>, applied to \<open>k\<close>, is already exactly the
  four-argument \<open>pp \<Rightarrow> call_string \<Rightarrow> 'd \<Rightarrow> call_action \<Rightarrow> call_string\<close> route
  \<open>routed_node_rhs_buffered\<close> wants -- unlike entry-state's own
  \<open>entry_state_route_gen\<close>, no wrapper is needed to reach that shape.
\<close>

definition cs_call_string_eqs ::
    "nat \<Rightarrow> (vname \<Rightarrow> bool) \<Rightarrow> (ivl exec_dg_st \<Rightarrow> bool) \<Rightarrow> proc_table \<Rightarrow> pname list \<Rightarrow> (pp \<times> call_string, call_string_gk, (ivl exec_dg_st lifted, ivl exec_dg_st lifted) dg_state) eqsT" where
  "cs_call_string_eqs k gs empty_pred Pi ps =
     routed_node_rhs_buffered intra_predecessor_addr_list (\<lambda>_. Call_String_Context.Global)
       (cs_route k)
       (\<lambda>ctx' src a. dg_spec_edge_tree (interval_spec gs empty_pred) a src
          (\<lambda>_. Call_String_Context.Global))
       (routed_call_tree (interval_spec gs empty_pred)
          Call_String_Context.Global Call_String_Context.Seed
          (static_resolve (compile_prog Pi ps)) (\<lambda>d. d = Bot))
       (routed_entry_seed_tree Call_String_Context.Seed)
       (compile_prog Pi ps) Bot (Lifted cinit_ivl_st) Bot"

definition cs_call_string_sol ::
    "nat \<Rightarrow> (vname \<Rightarrow> bool) \<Rightarrow> (ivl exec_dg_st \<Rightarrow> bool) \<Rightarrow> proc_table \<Rightarrow> pname list \<Rightarrow> (pp \<times> call_string) set \<times> (pp \<times> call_string + call_string_gk \<Rightarrow> (ivl exec_dg_st lifted, ivl exec_dg_st lifted) dg_state)" where
  "cs_call_string_sol k gs empty_pred Pi ps =
     TD_side_warrowing_apinis_Interp_solve (cs_call_string_eqs k gs empty_pred Pi ps)
       (cfg_exit (compile_prog Pi ps), [])"

definition cs_call_string_terminates ::
    "nat \<Rightarrow> (vname \<Rightarrow> bool) \<Rightarrow> (ivl exec_dg_st \<Rightarrow> bool) \<Rightarrow> proc_table \<Rightarrow> pname list \<Rightarrow> bool" where
  "cs_call_string_terminates k gs empty_pred Pi ps =
     TD_side_warrowing_apinis_Interp.solve_dom TYPE(call_string_gk) TYPE((ivl exec_dg_st lifted, ivl exec_dg_st lifted) dg_state)
       (cs_call_string_eqs k gs empty_pred Pi ps) (cfg_exit (compile_prog Pi ps), [])"

lemma cs_call_string_terminates_via_solve_c:
  assumes "TD_side_warrowing_apinis_Interp_solve_c (cs_call_string_eqs k gs empty_pred Pi ps)
             (cfg_exit (compile_prog Pi ps), []) \<noteq> None"
  shows "cs_call_string_terminates k gs empty_pred Pi ps"
  unfolding cs_call_string_terminates_def
  by (rule TD_side_warrowing_apinis_Interp.solve_dom_of_solve_c[OF assms])

lemma cs_call_string_vars_finite:
  assumes "cs_call_string_terminates k gs empty_pred Pi ps"
  shows "finite (fst (cs_call_string_sol k gs empty_pred Pi ps))"
  using TD_side_warrowing_apinis_Interp.finite_stabl_solve[
      OF assms[unfolded cs_call_string_terminates_def]]
  unfolding cs_call_string_sol_def TD_side_warrowing_apinis_Interp_solve_def
  by simp

subsection \<open>Whole-program convenience layer\<close>

definition cs_call_string_eqs_prog ::
    "nat \<Rightarrow> (vname \<Rightarrow> bool) \<Rightarrow> imp_prog
       \<Rightarrow> (pp \<times> call_string, call_string_gk, (ivl exec_dg_st lifted, ivl exec_dg_st lifted) dg_state) eqsT" where
  "cs_call_string_eqs_prog k gs p =
     cs_call_string_eqs k gs (resolved_st_q_is_bot_for (declared_global_vars p))
       (prog_table p) (prog_procs p)"

definition cs_call_string_sol_prog ::
    "nat \<Rightarrow> (vname \<Rightarrow> bool) \<Rightarrow> imp_prog
       \<Rightarrow> (pp \<times> call_string) set \<times> (pp \<times> call_string + call_string_gk \<Rightarrow> (ivl exec_dg_st lifted, ivl exec_dg_st lifted) dg_state)" where
  "cs_call_string_sol_prog k gs p =
     cs_call_string_sol k gs (resolved_st_q_is_bot_for (declared_global_vars p))
       (prog_table p) (prog_procs p)"

definition cs_call_string_terminates_prog :: "nat \<Rightarrow> (vname \<Rightarrow> bool) \<Rightarrow> imp_prog \<Rightarrow> bool" where
  "cs_call_string_terminates_prog k gs p =
     cs_call_string_terminates k gs (resolved_st_q_is_bot_for (declared_global_vars p))
       (prog_table p) (prog_procs p)"

lemma cs_call_string_terminates_prog_via_solve_c:
  assumes "TD_side_warrowing_apinis_Interp_solve_c
             (cs_call_string_eqs_prog k gs p)
             (cfg_exit (compile_prog (prog_table p) (prog_procs p)), []) \<noteq> None"
  shows "cs_call_string_terminates_prog k gs p"
  using assms
  unfolding cs_call_string_terminates_prog_def cs_call_string_eqs_prog_def
  by (rule cs_call_string_terminates_via_solve_c)

section \<open>Solved-result table\<close>

text \<open>
  The solved call-string D/G system, read as a
  \<^typ>\<open>(call_string, ivl abs_state) analysis_result\<close> -- the exact construction
  \<open>analyse_interval_entry_state_result_for\<close> already uses, at the
  call-string solve instead of the entry-state one. \<open>result_keys\<close> is the
  solver's own covered-key set, never an enumerated theoretical context space:
  call-string contexts are dynamic and discovered, not statically bounded, the
  same reason entry-state's own key set is solver-discovered rather than
  enumerated.
\<close>

definition analyse_interval_call_string_result_for ::
    "nat \<Rightarrow> (vname \<Rightarrow> bool) \<Rightarrow> imp_prog \<Rightarrow> (call_string, ivl abs_state) analysis_result" where
  "analyse_interval_call_string_result_for k gs p =
     Analysis_Result
       (fst (cs_call_string_sol_prog k gs p))
       (\<lambda>v ctx. normalize_point gs
                  (canonicalize_lift (resolved_st_q_is_bot_for (declared_global_vars p))
                    (locals (snd (cs_call_string_sol_prog k gs p) (Inl (v, ctx))))))"

declare analyse_interval_call_string_result_for_def [code del]

lemma analyse_interval_call_string_result_for_code [code]:
  "analyse_interval_call_string_result_for k gs p =
     (let sol = cs_call_string_sol_prog k gs p; gl = declared_global_vars p
      in Analysis_Result (fst sol)
           (\<lambda>v ctx. normalize_point gs
                      (canonicalize_lift (resolved_st_q_is_bot_for gl)
                        (locals (snd sol (Inl (v, ctx)))))))"
  unfolding analyse_interval_call_string_result_for_def Let_def by (rule refl)

text \<open>Convenience instance at \<^const>\<open>declared_global\<close> \<open>p\<close> and
  \<^const>\<open>prog_main_name\<close>, matching \<open>analyse_interval_entry_state_result\<close>'s
  shape, with \<open>k\<close> as an explicit leading runtime argument.\<close>

definition analyse_interval_call_string_result ::
    "nat \<Rightarrow> imp_prog \<Rightarrow> (call_string, ivl abs_state) analysis_result" where
  "analyse_interval_call_string_result k p =
     analyse_interval_call_string_result_for k (declared_global p) p"

section \<open>Contextual check report\<close>

text \<open>
  Reuses \<^const>\<open>classify_checks_ctx\<close>/\<^const>\<open>classify_checks_verdicts\<close> unchanged
  -- both are generic in the context type already, so nothing call-string-specific
  is needed here beyond supplying the call-string result table, exactly mirroring
  \<open>entry_state_check_projection\<close>/\<open>entry_state_verdict_report_prog\<close>.
\<close>

definition cs_call_string_check_projection ::
    "nat \<Rightarrow> imp_prog \<Rightarrow> (pp \<times> exp \<times> (call_string \<times> contextual_verdict) set) list" where
  "cs_call_string_check_projection k p =
     classify_checks_ctx (prog_cfg p)
       (analyse_interval_call_string_result_for k (declared_global p) p)
       interval_classify_check"

definition cs_call_string_verdict_report_prog ::
    "nat \<Rightarrow> imp_prog \<Rightarrow> (pp \<times> exp \<times> contextual_verdict) list" where
  "cs_call_string_verdict_report_prog k p =
     map (\<lambda>(u, c, vs). (u, c, aggregate_verdicts (snd ` vs)))
       (cs_call_string_check_projection k p)"

lemma cs_call_string_verdict_report_prog_eq:
  "cs_call_string_verdict_report_prog k p =
     classify_checks_verdicts (prog_cfg p)
       (analyse_interval_call_string_result_for k (declared_global p) p)
       interval_classify_check"
  unfolding cs_call_string_verdict_report_prog_def cs_call_string_check_projection_def
  by (rule classify_checks_verdicts_proj)

definition analyse_interval_call_string_report ::
    "nat \<Rightarrow> imp_prog \<Rightarrow> (pp \<times> exp \<times> contextual_verdict) list" where
  "analyse_interval_call_string_report k p = cs_call_string_verdict_report_prog k p"

section \<open>Generic executable entry-state context analysis for Interval\<close>

text \<open>
  Promotes the routed D/G machinery a fixed-program example (an entry-state
  acceptance case such as \<open>void p(a) { return a }\<close> / \<open>void main() { x := __voblint_nondet_int();
  y := p(x) }\<close>) exercises to an executable analysis over an arbitrary
  \<^type>\<open>imp_prog\<close>: the context at a call is the entered abstract value of the
  callee's declared formals (\<^const>\<open>formals_context\<close>),
  never call-site history, so a call whose argument is unconstrained (e.g.
  \<open>__voblint_nondet_int()\<close>) is analyzed once under one wide context rather than diverging over
  every concrete value. Mirrors \<^theory>\<open>Voblint_Analysis.Interval_Exec_Sound\<close>'s
  \<open>analyse_interval_td\<close> family and naming convention, adding one context
  dimension: every quantity here is keyed on \<^typ>\<open>pp \<times> ivl list\<close>, not \<^typ>\<open>pp\<close>
  alone.
\<close>

subsection \<open>Global key: real globals vs callee-entry seed slots\<close>


subsection \<open>The routed context hooks, generic over the compiled program\<close>

text \<open>
  The one D/G spec every hook below shares.
\<close>

text \<open>
  \<open>interval_spec\<close> is the Base-style whole-state specification
  (\<^const>\<open>local_state_dg_spec_st_for_lifted\<close>), the same one context-insensitive Interval already
  solves over in \<^const>\<open>analyse_interval_dg_eqs_for\<close>, at the same
  \<^const>\<open>ivl_tf_st_for\<close>/\<^const>\<open>ivl_enter_st_for\<close> primitives: the local unknown
  \<^typ>\<open>ivl exec_dg_st lifted\<close> carries every VIMP variable, global and local alike, so a
  global is read and written exactly where a local is. The solver-global carrier stays
  diagonal at \<^typ>\<open>ivl exec_dg_st lifted\<close> -- the type the keyed generator and its
  warrowing solver instance already fix -- but is inert: every field of
  \<^const>\<open>local_state_dg_spec_st_for_lifted\<close> threads its incoming \<open>g\<close> through unchanged, so
  \<open>Inr (Analysis_Global ())\<close> is never read back to reconstruct program state.

  \<open>interval_spec\<close> carries an explicit executable bottom predicate and solves over the lifted
  carrier, mirroring \<open>interval_conf_eqs\<close>'s convention
  (\<^theory>\<open>Voblint_Analysis.Interval_Exec_Sound\<close>) of taking \<open>empty_pred\<close> as a
  caller-supplied parameter rather than deriving it internally. Callers with a concrete
  program supply \<open>resolved_st_q_is_bot_for (declared_global_vars p)\<close>, exact for
  \<^const>\<open>is_empty_state\<close> (\<open>resolved_st_q_is_bot_for_iff\<close>).\<close>

text \<open>
  \<^const>\<open>formals_context\<close> (\<^theory>\<open>Voblint_Framework.Routed_Context\<close>)
  reads the entered callee formals off an arbitrary \<^const>\<open>CallEdge\<close> generically,
  but only at the semantic \<^typ>\<open>'a abs_state\<close> carrier, not the executable
  \<^typ>\<open>'a exec_dg_st\<close> one this equation system solves over: the entered callee
  store is materialized here by the same \<^const>\<open>ivl_enter_st_for\<close> primitive
  \<open>interval_spec\<close>'s own \<open>dgs_enter\<close> field applies and read back through
  \<^const>\<open>lookup_resolved_st_q\<close>, then \<^const>\<open>formals_context\<close> -- the same generic
  per-variable projection -- reads off the formals. The caller's whole state, globals
  included, feeds that entry, so a call argument mentioning a global is routed at the
  global's own abstract value rather than at \<open>bot\<close>.
\<close>

definition entry_state_enter_exec ::
    "(vname \<Rightarrow> bool) \<Rightarrow> call_action \<Rightarrow> ivl exec_dg_st \<Rightarrow> ivl exec_dg_st" where
  "entry_state_enter_exec gs ca s =
     bind_formals_resolved_q gs (ce_formals ca)
       (map (\<lambda>e. aval_ivl e (fun_of_resolved_st_q_for gs s)) (ce_args ca))
       (enter_frame_D_resolved_q ivl_top s)"

lemma ivl_enter_st_for_call_info_of_eq_entry_state_enter_exec:
  "ivl_enter_st_for gs (call_info_of ca p) s = entry_state_enter_exec gs ca s"
  unfolding entry_state_enter_exec_def by simp

definition entry_state_enter_abs ::
    "(vname \<Rightarrow> bool) \<Rightarrow> call_action \<Rightarrow> ivl abs_state \<Rightarrow> ivl abs_state" where
  "entry_state_enter_abs gs ca s =
     enter_ivl_for gs (ce_formals ca) (ce_args ca) s"

lemma enter_ivl_ci_for_call_info_of_eq_entry_state_enter_abs:
  "enter_ivl_ci_for gs (call_info_of ca p) s = entry_state_enter_abs gs ca s"
  unfolding entry_state_enter_abs_def enter_ivl_ci_for_def enter_ivl_for_def
  by simp

definition entry_state_entered ::
    "(vname \<Rightarrow> bool) \<Rightarrow> (ivl exec_dg_st \<Rightarrow> bool) \<Rightarrow> ivl exec_dg_st lifted \<Rightarrow> call_action \<Rightarrow> ivl exec_dg_st lifted" where
  "entry_state_entered gs empty_pred d ca =
     transfer_lift empty_pred (entry_state_enter_exec gs ca) d"

lemma enter_st_interval_eq_entry_state_entered:
  "transfer_lift empty_pred (ivl_enter_st_for gs (call_info_of ca p)) d =
   entry_state_entered gs empty_pred d ca"
  unfolding entry_state_entered_def
  by (cases d)
     (simp_all add: transfer_lift_def normalize_lift_def entry_state_enter_exec_def)

definition entry_state_route ::
    "(vname \<Rightarrow> bool) \<Rightarrow> (ivl exec_dg_st \<Rightarrow> bool) \<Rightarrow> ivl exec_dg_st lifted \<Rightarrow> call_action \<Rightarrow> ivl list" where
  "entry_state_route gs empty_pred d ca =
     (case ca of CallEdge dst pars args \<Rightarrow>
        formals_context pars
          (\<lambda>x. lookup_resolved_st_q
                 (case d of Bot \<Rightarrow> bot | Lifted d0 \<Rightarrow> d0)
                 (location_of gs x)))"

definition entry_state_route_gen ::
    "(vname \<Rightarrow> bool) \<Rightarrow> (ivl exec_dg_st \<Rightarrow> bool) \<Rightarrow> pp \<Rightarrow> ivl list \<Rightarrow> ivl exec_dg_st lifted \<Rightarrow> call_action \<Rightarrow> ivl list" where
  "entry_state_route_gen gs empty_pred u ctx d ca = entry_state_route gs empty_pred d ca"

text \<open>
  The same routing decision taken on a caller state that has already left the
  executable substrate: the argument is the \<^typ>\<open>ivl abs_state\<close> a
  \<^const>\<open>Lifted\<close> point of an \<^type>\<open>analysis_result\<close> hands out, so a
  consumer of a solved table can recompute a call's callee context without
  reopening the solver's own solution map.

  The type is \<^typ>\<open>ivl abs_state\<close>, not \<^typ>\<open>ivl abs_state lifted\<close>, on
  purpose: reachability is the caller's case split, decided once by
  \<^const>\<open>normalize_point\<close> when the table was built, and an \<^const>\<open>Bot\<close>
  point has no call edge to route at all.

  A live caller can still enter a callee frame that is itself semantically
  empty, e.g. an actual argument whose abstract value is already bottom. In
  that case \<^const>\<open>entry_state_route\<close> does not skip routing: it reports the
  all-\<^const>\<open>bot\<close> formal context the solver actually materialized a (dead)
  callee activation under, and that all-\<^const>\<open>bot\<close> context is a real,
  distinct context, never the empty list \<open>[]\<close>, which is a legitimate root
  or zero-formal context in its own right and must not double as a sentinel
  for "no route". So \<open>entry_state_callee_ctx\<close> answers \<^const>\<open>None\<close> exactly
  on this case, restricting the bottom test that decides it to the finite
  list of formals \<open>entered_is_bot_for\<close> below, rather than repeating the
  non-executable whole-state test \<^const>\<open>is_empty_state\<close> quantifies over all
  of \<^typ>\<open>vname\<close>, which is what keeps \<open>entry_state_route_abs\<close> non-executable.

  It routes on the static \<^const>\<open>CallEdge\<close> and the entered caller state alone,
  matching \<^const>\<open>entry_state_route_gen\<close>'s own independence of the caller's
  identity, \<open>entry_state_route_gen_def\<close>: the callee context is a function of
  what is passed, never of who passes it.
\<close>

definition entered_is_bot_for :: "vname list \<Rightarrow> ivl abs_state \<Rightarrow> bool" where
  "entered_is_bot_for pars ent = list_ex (\<lambda>x. is_empty (ent x)) pars"

text \<open>
  Restricting \<^const>\<open>is_empty_state\<close>'s witness search to the formals is exact,
  not merely a heuristic: \<^const>\<open>enter_frame\<close> resets every non-global
  variable to \<^const>\<open>ivl_top\<close> and leaves every global at the caller's own
  value, so no name outside the formals can ever witness bottomness once the
  caller itself is not \<^const>\<open>is_empty_state\<close> -- \<open>entered_is_bot_for_correct\<close>
  below states this precisely.
\<close>

lemma entered_is_bot_for_correct:
  assumes not_bot: "\<not> is_empty_state st"
  shows "entered_is_bot_for pars (entry_state_enter_abs gs (CallEdge dst pars args) st) =
         is_empty_state (entry_state_enter_abs gs (CallEdge dst pars args) st)"
proof -
  define frame where "frame = enter_frame gs ivl_top st"
  define entered where "entered = bind_formals pars (map (\<lambda>e. aval_ivl e st) args) frame"
  have unfold: "entry_state_enter_abs gs (CallEdge dst pars args) st = entered"
    unfolding entry_state_enter_abs_def
    by (simp add: enter_ivl_for_def enter_binding_def entered_def frame_def)
  have frame_not_bot: "\<not> is_empty (frame x)" for x
  proof (cases "gs x")
    case True
    then have "frame x = st x" by (simp add: frame_def enter_frame_def)
    with not_bot show ?thesis by (auto simp: is_empty_state_def)
  next
    case False
    then have "frame x = ivl_top" by (simp add: frame_def enter_frame_def)
    then show ?thesis by (simp add: ivl_top_def is_bottom_ivl_def)
  qed

  have off_pars_generic: "\<And>ps as (\<tau>::vname \<Rightarrow> ivl) x. x \<notin> set ps
      \<Longrightarrow> fold (\<lambda>(x, a) \<tau>. \<tau>(x := a)) (zip ps as) \<tau> x = \<tau> x"
  proof -
    fix ps show "\<And>as (\<tau>::vname \<Rightarrow> ivl) x. x \<notin> set ps
        \<Longrightarrow> fold (\<lambda>(x, a) \<tau>. \<tau>(x := a)) (zip ps as) \<tau> x = \<tau> x"
    proof (induction ps)
      case Nil
      then show ?case by simp
    next
      case (Cons p ps)
      show ?case
      proof (cases as)
        case Nil
        then show ?thesis by simp
      next
        case (Cons a as')
        have neq: "x \<noteq> p" using Cons.prems by simp
        have notin: "x \<notin> set ps" using Cons.prems by simp
        show ?thesis
          unfolding local.Cons
          using Cons.IH[where as = as' and \<tau> = "\<tau>(p := a)" and x = x] notin neq
          by simp
      qed
    qed
  qed
  have off_pars: "x \<notin> set pars \<Longrightarrow> entered x = frame x" for x
    unfolding entered_def
    using off_pars_generic by blast
  have "is_empty_state entered \<longleftrightarrow> (\<exists>x. is_empty (entered x))"
    by (simp add: is_empty_state_def)
  also have "\<dots> \<longleftrightarrow> (\<exists>x \<in> set pars. is_empty (entered x))"
    using off_pars frame_not_bot by metis
  also have "\<dots> \<longleftrightarrow> list_ex (\<lambda>x. is_empty (entered x)) pars"
    by (simp add: list_ex_iff)
  finally show ?thesis
    unfolding unfold entered_is_bot_for_def by (simp add: unfold)
qed

definition entry_state_callee_ctx ::
    "(vname \<Rightarrow> bool) \<Rightarrow> call_action \<Rightarrow> ivl abs_state \<Rightarrow> ivl list option" where
  "entry_state_callee_ctx gs ca st =
     (case ca of CallEdge dst pars args \<Rightarrow>
        (let entered = entry_state_enter_abs gs ca st
         in if entered_is_bot_for pars entered then None
            else Some (formals_context pars entered)))"

subsection \<open>The routed equation system and its executable solution\<close>

definition entry_state_eqs ::
    "(vname \<Rightarrow> bool) \<Rightarrow> (ivl exec_dg_st \<Rightarrow> bool) \<Rightarrow> proc_table \<Rightarrow> pname list \<Rightarrow> (pp \<times> ivl list, (unit, ivl list) routed_gk, (ivl exec_dg_st lifted, ivl exec_dg_st lifted) dg_state) eqsT" where
  "entry_state_eqs gs empty_pred Pi ps =
     routed_node_rhs_buffered intra_predecessor_addr_list (\<lambda>_. Analysis_Global ())
       (entry_state_route_gen gs empty_pred)
       (\<lambda>ctx' src a. dg_spec_edge_tree (interval_spec gs empty_pred) a src (\<lambda>_. Analysis_Global ()))
       (routed_call_tree (interval_spec gs empty_pred) (Analysis_Global ()) Activation_Seed
          (static_resolve (compile_prog Pi ps)) (\<lambda>d. d = Bot))
       (routed_entry_seed_tree Activation_Seed)
       (compile_prog Pi ps) Bot (Lifted cinit_ivl_st) Bot"

definition entry_state_sol ::
    "(vname \<Rightarrow> bool) \<Rightarrow> (ivl exec_dg_st \<Rightarrow> bool) \<Rightarrow> proc_table \<Rightarrow> pname list \<Rightarrow> (pp \<times> ivl list) set \<times> (pp \<times> ivl list + (unit, ivl list) routed_gk \<Rightarrow> (ivl exec_dg_st lifted, ivl exec_dg_st lifted) dg_state)" where
  "entry_state_sol gs empty_pred Pi ps =
     TD_side_warrowing_apinis_Interp_solve (entry_state_eqs gs empty_pred Pi ps)
       (cfg_exit (compile_prog Pi ps), [])"

definition entry_state_terminates ::
    "(vname \<Rightarrow> bool) \<Rightarrow> (ivl exec_dg_st \<Rightarrow> bool) \<Rightarrow> proc_table \<Rightarrow> pname list \<Rightarrow> bool" where
  "entry_state_terminates gs empty_pred Pi ps =
     TD_side_warrowing_apinis_Interp.solve_dom TYPE((unit, ivl list) routed_gk) TYPE((ivl exec_dg_st lifted, ivl exec_dg_st lifted) dg_state)
       (entry_state_eqs gs empty_pred Pi ps) (cfg_exit (compile_prog Pi ps), [])"

text \<open>
  Discharging termination by execution, exactly as
  \<open>interval_conf_terminates_prog_via_solve_c\<close> discharges
  \<open>interval_conf_terminates_prog\<close>.
\<close>

lemma entry_state_terminates_via_solve_c:
  assumes "TD_side_warrowing_apinis_Interp_solve_c (entry_state_eqs gs empty_pred Pi ps)
             (cfg_exit (compile_prog Pi ps), []) \<noteq> None"
  shows "entry_state_terminates gs empty_pred Pi ps"
  unfolding entry_state_terminates_def
  by (rule TD_side_warrowing_apinis_Interp.solve_dom_of_solve_c[OF assms])

text \<open>Finiteness of the entry-state key set, from the solver's own invariant
  (\<open>finite_stabl_solve\<close>, \<^theory>\<open>Voblint_Solver.TD_Solver_Bridge\<close>). That invariant
  is proved for the \<open>TD_side_upd_rule\<close> locale rather than per update rule, so it
  applies to Apinis warrowing here exactly as it does to always-join elsewhere.
  It also depends on nothing about the context type, which is what makes the
  entry-state case available at all: its contexts are \<^typ>\<open>ivl list\<close> values, a
  space no bound could enumerate.\<close>

lemma entry_state_vars_finite:
  assumes "entry_state_terminates gs empty_pred Pi ps"
  shows "finite (fst (entry_state_sol gs empty_pred Pi ps))"
  using TD_side_warrowing_apinis_Interp.finite_stabl_solve[
      OF assms[unfolded entry_state_terminates_def]]
  unfolding entry_state_sol_def TD_side_warrowing_apinis_Interp_solve_def
  by simp

subsection \<open>Whole-program convenience layer\<close>

text \<open>
  \<open>Pi ps\<close> alone give no @{type imp_prog} to read a declared-global list off of, so
  \<open>entry_state_eqs\<close> and friends keep \<open>empty_pred\<close> as an explicit parameter, mirroring
  the context-insensitive run's own \<open>interval_conf_eqs\<close>. The \<open>_prog\<close> wrappers do
  have a program and instantiate \<open>empty_pred\<close> to \<^const>\<open>resolved_st_q_is_bot_for\<close> at its own
  \<^const>\<open>declared_global_vars\<close>, mirroring \<open>interval_conf_sol_prog\<close>.
\<close>

definition entry_state_eqs_prog ::
    "(vname \<Rightarrow> bool) \<Rightarrow> imp_prog
       \<Rightarrow> (pp \<times> ivl list, (unit, ivl list) routed_gk, (ivl exec_dg_st lifted, ivl exec_dg_st lifted) dg_state) eqsT" where
  "entry_state_eqs_prog gs p =
     entry_state_eqs gs (resolved_st_q_is_bot_for (declared_global_vars p))
       (prog_table p) (prog_procs p)"

definition entry_state_sol_prog ::
    "(vname \<Rightarrow> bool) \<Rightarrow> imp_prog
       \<Rightarrow> (pp \<times> ivl list) set \<times> (pp \<times> ivl list + (unit, ivl list) routed_gk \<Rightarrow> (ivl exec_dg_st lifted, ivl exec_dg_st lifted) dg_state)" where
  "entry_state_sol_prog gs p =
     entry_state_sol gs (resolved_st_q_is_bot_for (declared_global_vars p))
       (prog_table p) (prog_procs p)"

definition entry_state_terminates_prog :: "(vname \<Rightarrow> bool) \<Rightarrow> imp_prog \<Rightarrow> bool" where
  "entry_state_terminates_prog gs p =
     entry_state_terminates gs (resolved_st_q_is_bot_for (declared_global_vars p))
       (prog_table p) (prog_procs p)"

lemma entry_state_terminates_prog_via_solve_c:
  assumes "TD_side_warrowing_apinis_Interp_solve_c
             (entry_state_eqs_prog gs p)
             (cfg_exit (compile_prog (prog_table p) (prog_procs p)), []) \<noteq> None"
  shows "entry_state_terminates_prog gs p"
  using assms
  unfolding entry_state_terminates_prog_def entry_state_eqs_prog_def
  by (rule entry_state_terminates_via_solve_c)

section \<open>The abstract-carrier route witness\<close>

text \<open>
  \<open>interval_abs_spec\<close> is the abstract-carrier half of the \<open>route\<close>/\<open>resolve\<close> pair
  \<^locale>\<open>routed_context_base_hetero\<close> requires: its \<open>route_agree\<close> assumption
  needs both an executable-carrier route and an abstract-carrier one it
  agrees with along the readback, so this witness stays even once the
  interpretation below runs entirely at the executable carrier.
\<close>


definition entered_state_abs ::
    "(vname \<Rightarrow> bool) \<Rightarrow> ivl abs_state lifted \<Rightarrow> call_action \<Rightarrow> ivl abs_state lifted" where
  "entered_state_abs gs d ca =
     transfer_lift is_empty_state (entry_state_enter_abs gs ca) d"

definition entry_state_route_abs ::
    "(vname \<Rightarrow> bool) \<Rightarrow> ivl abs_state lifted \<Rightarrow> call_action \<Rightarrow> ivl list" where
  "entry_state_route_abs gs d ca =
     (case ca of CallEdge dst pars args \<Rightarrow>
        formals_context pars (case d of Bot \<Rightarrow> bot | Lifted d0 \<Rightarrow> d0))"

definition entry_state_route_abs_gen ::
    "(vname \<Rightarrow> bool) \<Rightarrow> pp \<Rightarrow> ivl list \<Rightarrow> ivl abs_state lifted \<Rightarrow> call_action \<Rightarrow> ivl list" where
  "entry_state_route_abs_gen gs u ctx d ca = entry_state_route_abs gs d ca"

text \<open>
  \<open>entry_state_route_abs\<close>/\<open>entry_state_route_abs_gen\<close> are exactly
  \<^theory>\<open>Voblint_Framework.Routed_Context\<close>'s \<open>formals_route_lifted\<close>/\<open>formals_route_lifted_gen\<close>,
  generalized so any domain interprets them instead of restating them: both case-split
  the same \<^const>\<open>CallEdge\<close> and read the same entered-frame Bot/Lifted collapse, and
  the action-only entry primitive used by entered_state_abs agrees with the entered frame
  interval_abs_spec's own enter transfer produces. Kept as their own named
  definitions -- rather than replaced outright -- because both are cited by name from the
  regression examples
  (\<open>Example_Interval_DG_Ctx_Collect\<close>, \<open>Example_Interval_DG_EntryState_Collect\<close>); this
  identity is what lets the routed interpretation below use the generic Core locale while
  every existing citation of these two names keeps working unchanged.
\<close>

lemma entry_state_route_abs_gen_eq_formals_route_lifted_gen:
  "entry_state_route_abs_gen gs = formals_route_lifted_gen"
proof (intro ext)
  fix u ctx d ca
  show "entry_state_route_abs_gen gs u ctx d ca = formals_route_lifted_gen u ctx d ca"
    unfolding entry_state_route_abs_gen_def formals_route_lifted_gen_def
      entry_state_route_abs_def formals_route_lifted_def
    by (cases ca) simp_all
qed

subsection \<open>The route-consistency core\<close>

lemma entry_state_entered_commute:
  assumes exact: "\<And>s. empty_pred s = is_empty_state (fun_of_resolved_st_q_for gs s)"
  shows "map_lift (fun_of_resolved_st_q_for gs) (entry_state_entered gs empty_pred s ca)
     = entered_state_abs gs (map_lift (fun_of_resolved_st_q_for gs) s) ca"
proof -
  fix p :: pname
  have commute: "\<And>d. fun_of_resolved_st_q_for gs (entry_state_enter_exec gs ca d) =
      entry_state_enter_abs gs ca (fun_of_resolved_st_q_for gs d)"
  proof -
    fix d
    have "fun_of_resolved_st_q_for gs
        (ivl_enter_st_for gs (call_info_of ca p) d) =
        enter_ivl_ci_for gs (call_info_of ca p) (fun_of_resolved_st_q_for gs d)"
      by (rule ivl_enter_st_for_commute)
    then show "fun_of_resolved_st_q_for gs (entry_state_enter_exec gs ca d) =
        entry_state_enter_abs gs ca (fun_of_resolved_st_q_for gs d)"
      by (simp only: ivl_enter_st_for_call_info_of_eq_entry_state_enter_exec
          enter_ivl_ci_for_call_info_of_eq_entry_state_enter_abs)
  qed
  show ?thesis
    unfolding entry_state_entered_def entered_state_abs_def
    by (rule transfer_lift_commute
          [where phi = "fun_of_resolved_st_q_for gs"
             and f = "entry_state_enter_exec gs ca"
             and F = "entry_state_enter_abs gs ca"
             and empty_pred = empty_pred
             and empty_pred' = is_empty_state, OF commute exact])
qed

lemma entry_state_route_commute:
  assumes exact: "\<And>s. empty_pred s = is_empty_state (fun_of_resolved_st_q_for gs s)"
  shows "entry_state_route_abs gs (map_lift (fun_of_resolved_st_q_for gs) s) ca
           = entry_state_route gs empty_pred s ca"
  by (cases ca; cases s)
     (simp_all add: entry_state_route_abs_def entry_state_route_def
                    formals_context_def fun_of_resolved_st_q_for_def)

lemma entry_state_route_commute_gen:
  assumes exact: "\<And>s. empty_pred s = is_empty_state (fun_of_resolved_st_q_for gs s)"
  shows "entry_state_route_gen gs empty_pred u ctx s ca
           = entry_state_route_abs_gen gs u ctx (map_lift (fun_of_resolved_st_q_for gs) s) ca"
  by (simp add: entry_state_route_gen_def entry_state_route_abs_gen_def entry_state_route_commute[OF exact])

text \<open>
  Presentation-side routing agrees with the routing that built the equation
  system, on both outcomes. A caller point the table answers \<^const>\<open>Lifted\<close>
  either routes to the same callee context the solved system was built with,
  or is exactly the case that context is dead: \<open>entry_state_callee_ctx\<close>
  answers \<^const>\<open>None\<close> iff the entered callee frame is itself
  \<^const>\<open>is_empty_state\<close>, which is precisely when \<^const>\<open>entry_state_route_abs\<close>'s
  own bottom collapse fires. There is no unaddressed case left over: unlike
  the earlier single-outcome fact this replaces, this theorem needs no \<open>live\<close>
  side condition, because it states what happens on both branches instead of
  assuming the live one.

  \<open>reach\<close> says the normalized state is the reader's image of the solved local
  unknown -- what \<^const>\<open>normalize_point\<close> supplies for any point a result
  table answered \<^const>\<open>Lifted\<close>. \<open>not_bot\<close> says that
  normalized state is not itself \<^const>\<open>is_empty_state\<close>, which
  \<open>normalize_point\<close>'s own witness-bottom test already guarantees for every
  \<^const>\<open>Lifted\<close> point a table built through it can produce.
\<close>

theorem entry_state_callee_ctx_eq_route_partial:
  assumes exact: "\<And>s. empty_pred s = is_empty_state (fun_of_resolved_st_q_for gs s)"
    and reach: "map_lift (fun_of_resolved_st_q_for gs) d = Lifted st"
    and not_bot: "\<not> is_empty_state st"
  shows "entry_state_callee_ctx gs ca st =
    (if entered_state_abs gs (Lifted st) ca = Bot
     then None
     else Some (entry_state_route gs empty_pred (entry_state_entered gs empty_pred d ca) ca))"
proof (cases ca)
  case (CallEdge dst pars args)
  define entered where "entered = entry_state_enter_abs gs ca st"
  have entered_state_eq: "entered_state_abs gs (Lifted st) ca =
      (if entered_is_bot_for pars entered then Bot else Lifted entered)"
    unfolding entered_state_abs_def CallEdge entered_def
    by (simp add: normalize_lift_def entered_is_bot_for_correct[OF not_bot])
  have callee_ctx_eq: "entry_state_callee_ctx gs ca st =
      (if entered_is_bot_for pars entered then None else Some (formals_context pars entered))"
    unfolding entry_state_callee_ctx_def CallEdge Let_def entered_def by simp
  show ?thesis
  proof (cases "entered_is_bot_for pars entered")
    case True
    with entered_state_eq callee_ctx_eq show ?thesis by simp
  next
    case False
    have "entry_state_route gs empty_pred (entry_state_entered gs empty_pred d ca) ca
        = entry_state_route_abs gs
            (map_lift (fun_of_resolved_st_q_for gs) (entry_state_entered gs empty_pred d ca)) ca"
      by (simp add: entry_state_route_commute[OF exact])
    also have "\<dots> = entry_state_route_abs gs (entered_state_abs gs (Lifted st) ca) ca"
      using entry_state_entered_commute[OF exact] reach by simp
    also have "\<dots> = formals_context pars entered"
      unfolding entry_state_route_abs_def
      using entered_state_eq False CallEdge by simp
    finally have "entry_state_route gs empty_pred (entry_state_entered gs empty_pred d ca) ca
        = formals_context pars entered" .
    with False entered_state_eq callee_ctx_eq show ?thesis by simp
  qed
qed

subsection \<open>Per-tree transport commutation\<close>

text \<open>
  The same interpretation Interval's unit-context instance makes, at the entry-state
  routing policy. \<^locale>\<open>routed_domain_exec\<close> takes the routing functions and their
  agreement as parameters; here the agreement is the route-consistency core just
  proved, since the entry-state route reads the entered state.
\<close>

text \<open>The concretization the executable-carrier interpretations below use: a local
  unknown means \<^const>\<open>gamma_state_lift\<close> of its readback, the global slot is ignored as
  in \<^const>\<open>gamma_dg_local_state\<close>. Named at top level so a downstream theory can state it.\<close>

context
  fixes gs :: "vname \<Rightarrow> bool" and empty_pred :: "ivl exec_dg_st \<Rightarrow> bool"
  assumes exact: "\<And>s. empty_pred s = is_empty_state (fun_of_resolved_st_q_for gs s)"
begin

interpretation ivl_es: routed_domain_exec
  gs empty_pred "ivl_tf_st_for gs" "ivl_enter_st_for gs"
  skip_ivl assign_ivl special_ivl branch_ivl body_ivl return_ivl
  "enter_ivl_ci_for gs" event_ivl
  "Analysis_Global ()" Activation_Seed "entry_state_route_gen gs empty_pred" "entry_state_route_abs_gen gs"
  static_resolve static_resolve
  by unfold_locales
     (rule ivl_tf_st_for_commute[unfolded ivl_tf_abs_def], assumption,
      rule ivl_enter_st_for_commute, rule exact, simp,

      rule entry_state_route_commute_gen[OF exact], simp add: static_resolve_def)

lemmas ivl_es_pp_st_gen = ivl_es.pp_st


end


subsection \<open>The certified executable post-solution, generic per compiled program\<close>

context
  fixes gs :: "vname \<Rightarrow> bool" and empty_pred :: "ivl exec_dg_st \<Rightarrow> bool"
    and Pi :: proc_table and ps :: "pname list"
  assumes solves: "entry_state_terminates gs empty_pred Pi ps"
    and exact: "\<And>s. empty_pred s = is_empty_state (fun_of_resolved_st_q_for gs s)"
begin

lemma entry_state_solve_dom:
  "TD_side_warrowing_apinis_Interp.solve_dom TYPE((unit, ivl list) routed_gk) TYPE((ivl exec_dg_st lifted, ivl exec_dg_st lifted) dg_state)
     (entry_state_eqs gs empty_pred Pi ps) (cfg_exit (compile_prog Pi ps), [])"
  using solves[unfolded entry_state_terminates_def] .

lemma entry_state_pp_st:
  "part_post_solution (entry_state_eqs gs empty_pred Pi ps) (cfg_exit (compile_prog Pi ps), [])
     (snd (entry_state_sol gs empty_pred Pi ps)) (fst (entry_state_sol gs empty_pred Pi ps))"
  using TD_side_warrowing_apinis_Interp.partial_post_solution
          [OF entry_state_solve_dom, of "fst (entry_state_sol gs empty_pred Pi ps)"
             "snd (entry_state_sol gs empty_pred Pi ps)"]
  unfolding entry_state_sol_def by simp

text \<open>The solver's post-solution, for the unbuffered routed generator at the executable
  spec and Interval's executable route: the shape \<^locale>\<open>dg_ctx_activation_base\<close>
  consumes.\<close>

theorem entry_state_pp_routed:
  "part_post_solution
     (routed_node_rhs intra_predecessor_addr_list (\<lambda>_. Analysis_Global ())
        (entry_state_route_gen gs empty_pred)
        (\<lambda>ctx' src a. dg_spec_edge_tree (interval_spec gs empty_pred) a src (\<lambda>_. Analysis_Global ()))
        (routed_call_tree (interval_spec gs empty_pred) (Analysis_Global ()) Activation_Seed (static_resolve (compile_prog Pi ps)) (\<lambda>d. d = Bot))
        (routed_entry_seed_tree Activation_Seed)
        (compile_prog Pi ps) Bot (Lifted cinit_ivl_st) Bot)
     (cfg_exit (compile_prog Pi ps), [])
     (snd (entry_state_sol gs empty_pred Pi ps)) (fst (entry_state_sol gs empty_pred Pi ps))"
  using entry_state_pp_st unfolding entry_state_eqs_def interval_spec_def
  by (rule ivl_es_pp_st_gen[OF exact])


end


section \<open>Activation-indexed collecting soundness, generic per compiled program\<close>

text \<open>
  The routed spine is interpreted at Interval's executable carrier and fed the solver's
  own table: a local unknown concretizes to \<^const>\<open>gamma_state_lift\<close> of its readback
  (\<^const>\<open>interval_gamma\<close>), the covered reader \<open>entry_state_sg_st\<close> hands the table's local
  slot through unchanged, and the route is Interval's own executable
  \<^const>\<open>entry_state_route_gen\<close>. The reader is unconditional so the code generator and
  the examples can evaluate it; the soundness obligations below are hypotheses of the
  context, not of the reader.
\<close>

definition entry_state_sg_st ::
    "(vname \<Rightarrow> bool) \<Rightarrow> (ivl exec_dg_st \<Rightarrow> bool) \<Rightarrow> proc_table \<Rightarrow> pname list
       \<Rightarrow> pp \<times> ivl list + (unit, ivl list) routed_gk \<Rightarrow> ivl exec_dg_st lifted" where
  "entry_state_sg_st gs empty_pred Pi ps =
     solved_local_reader (fst (entry_state_sol gs empty_pred Pi ps))
                          (snd (entry_state_sol gs empty_pred Pi ps))"

context
  fixes gs :: "vname \<Rightarrow> bool" and empty_pred :: "ivl exec_dg_st \<Rightarrow> bool"
    and Pi :: proc_table and ps :: "pname list"
  assumes solves: "entry_state_terminates gs empty_pred Pi ps"
    and exact: "\<And>s. empty_pred s = is_empty_state (fun_of_resolved_st_q_for gs s)"
    and entry_cov: "(cfg_entry (compile_prog Pi ps), []) \<in> fst (entry_state_sol gs empty_pred Pi ps)"
    and fwd_ok: "\<And>u a v ctx. (u, ctx) \<in> fst (entry_state_sol gs empty_pred Pi ps)
                   \<Longrightarrow> (u, a, v) \<in> intra (compile_prog Pi ps)
                   \<Longrightarrow> (v, ctx) \<in> fst (entry_state_sol gs empty_pred Pi ps)"
    and call_fwd_ok: "\<And>u ctx dst pars args p cont.
        (u, ctx) \<in> fst (entry_state_sol gs empty_pred Pi ps)
        \<Longrightarrow> (u, CallEdge dst pars args, FunctionEntry p, cont) \<in> calls (compile_prog Pi ps)
        \<Longrightarrow> (FunctionEntry p,
              entry_state_route_gen gs empty_pred u ctx
                (transfer_lift empty_pred
                   (ivl_enter_st_for gs (call_info_of (CallEdge dst pars args) p))
                   (locals (snd (entry_state_sol gs empty_pred Pi ps) (Inl (u, ctx)))))
                (CallEdge dst pars args))
            \<in> fst (entry_state_sol gs empty_pred Pi ps)"
    and comb_fwd_ok: "\<And>cl c1 dst pars args p cont.
        (cl, c1) \<in> fst (entry_state_sol gs empty_pred Pi ps)
        \<Longrightarrow> (cl, CallEdge dst pars args, FunctionEntry p, cont) \<in> calls (compile_prog Pi ps)
        \<Longrightarrow> (cont, c1) \<in> fst (entry_state_sol gs empty_pred Pi ps)"
begin

subsection \<open>The solver's table as the solved system\<close>


interpretation entry_state_compiled: compiled_cfg Pi ps "compile_prog Pi ps"
  by (unfold_locales; simp add: compile_prog_finite)

lemmas entry_state_fin = entry_state_compiled.finite_intra
lemmas entry_state_finC = entry_state_compiled.finite_calls

lemma entry_state_sg_st_covered:
  "(v, ctx) \<in> fst (entry_state_sol gs empty_pred Pi ps)
   \<Longrightarrow> entry_state_sg_st gs empty_pred Pi ps (Inl (v, ctx))
         = locals (snd (entry_state_sol gs empty_pred Pi ps) (Inl (v, ctx)))"
  by (simp add: entry_state_sg_st_def)

lemma entry_state_sg_st_uncovered_empty:
  "(v, ctx) \<notin> fst (entry_state_sol gs empty_pred Pi ps)
     \<Longrightarrow> gamma_state_lift (map_lift (fun_of_resolved_st_q_for gs)
           (entry_state_sg_st gs empty_pred Pi ps (Inl (v, ctx)))) = {}"
  by (simp add: entry_state_sg_st_def)

subsection \<open>Instantiating the generic routed-context locale\<close>

interpretation entry_state_dg_base: sound_dg_spec_core "interval_spec gs empty_pred" "interval_gamma gs" gs
  by (rule interval_sound_exec[OF exact])


interpretation entry_state_routed: entry_state_routed_context "interval_spec gs empty_pred"
    "interval_gamma gs" gs Pi ps "Analysis_Global ()" "entry_state_route_gen gs empty_pred"
    Bot "Lifted cinit_ivl_st" Bot
    "snd (entry_state_sol gs empty_pred Pi ps)" "fst (entry_state_sol gs empty_pred Pi ps)"
    "(cfg_exit (compile_prog Pi ps), [])" "entry_state_sg_st gs empty_pred Pi ps" Activation_Seed
    "\<lambda>d. d = Bot" "\<lambda>m. gamma_state_lift (map_lift (fun_of_resolved_st_q_for gs) m)"
    "\<lambda>ci d. [(d, transfer_lift empty_pred (ivl_enter_st_for gs ci) d)]"
proof (unfold_locales, goal_cases FinE PP SgCov SgUncov Fwd SeedNe
    IsBotBot IsBotSound EnterPure EnterCover CallFwd CombFwd)
  case FinE show ?case by (rule entry_state_fin)
next
  case PP show ?case by (rule entry_state_pp_routed[OF solves exact])
next
  case (SgCov v ctx) then show ?case
    by (simp add: entry_state_sg_st_def interval_gamma_def)
next
  case (SgUncov v ctx) then show ?case by (rule entry_state_sg_st_uncovered_empty)
next
  case (Fwd u a v ctx) then show ?case by (rule fwd_ok)
next
  case (SeedNe p ctx) show ?case by simp
next
  case IsBotBot show ?case by simp
next
  case (IsBotSound d gv) then show ?case by (simp add: interval_gamma_def)
next
  case (EnterPure ci) show ?case
    unfolding interval_spec_def dgs_enter_local_state_st_for_lifted by (rule refl)
next
  case (EnterCover u ctx dst pars args p cont s)
  show ?case
    using interval_entry_cover_exec[OF exact EnterCover(3),
        where ci = "call_info_of (CallEdge dst pars args) p"]
    by simp
next
  case (CallFwd u ctx dst pars args p cont cont' entry)
  then have "entry = transfer_lift empty_pred
               (ivl_enter_st_for gs (call_info_of (CallEdge dst pars args) p))
               (locals (snd (entry_state_sol gs empty_pred Pi ps) (Inl (u, ctx))))"
    by simp
  with CallFwd(1,2) show ?case using call_fwd_ok by simp
next
  case (CombFwd cl c1 dst pars args p cont)
  show ?case using CombFwd(1,2) by (rule comb_fwd_ok)
qed

text \<open>
  The context relation this entry-state instance keys its collecting semantics by: an
  abbreviation over the interpreted \<open>entry_state_routed.entry_context_rel\<close>, named at
  Interval's carrier so downstream statements read as Interval vocabulary. Unlike the
  retired deterministic context function it replaces, this makes no claim to pick one
  context per concrete call -- only that whichever context an alternative of
  \<^const>\<open>ivl_enter_st_for\<close> routes to, and whose two halves cover the call, is admitted.
\<close>

abbreviation entry_state_context_rel :: "ivl list call_context_rel" where
  "entry_state_context_rel \<equiv> entry_state_routed.entry_context_rel"

lemmas entry_state_routed_context_call = entry_state_routed.routed_context_call
lemmas entry_state_routed_context_comb = entry_state_routed.routed_context_comb

lemma entry_state_sg_seed:
  assumes "(u, CallEdge dst xs es, FunctionEntry p, cont) \<in> calls (compile_prog Pi ps)"
    and "s \<in> gamma_state_lift (map_lift (fun_of_resolved_st_q_for gs)
               (entry_state_sg_st gs empty_pred Pi ps (Inl (u, ctx))))"
    and "entry_state_context_rel u ctx (call_info_of (CallEdge dst xs es) p) s
           (call_enter gs (CallEdge dst xs es) s) ctx'"
  shows "call_enter gs (CallEdge dst xs es) s
           \<in> gamma_state_lift (map_lift (fun_of_resolved_st_q_for gs)
               (entry_state_sg_st gs empty_pred Pi ps (Inl (FunctionEntry p, ctx'))))"
  by (rule entry_state_routed_context_call[OF assms])

lemma entry_state_sg_comb:
  assumes "(cl, CallEdge dst pars args, FunctionEntry p, v) \<in> calls (compile_prog Pi ps)"
    and "s \<in> gamma_state_lift (map_lift (fun_of_resolved_st_q_for gs)
               (entry_state_sg_st gs empty_pred Pi ps (Inl (cl, c1))))"
    and "admits_call_context gs (compile_prog Pi ps) entry_state_context_rel cl c1 p s es ctx'"
    and "t \<in> gamma_state_lift (map_lift (fun_of_resolved_st_q_for gs)
               (entry_state_sg_st gs empty_pred Pi ps (Inl (FunctionResult p, ctx'))))"
  shows "combine_collect gs dst s t
           \<in> gamma_state_lift (map_lift (fun_of_resolved_st_q_for gs)
               (entry_state_sg_st gs empty_pred Pi ps (Inl (v, c1))))"
  by (rule entry_state_routed_context_comb[OF assms])




subsection \<open>Activation-indexed collecting soundness\<close>

lemma entry_state_cinit_le_cinit_ivl_st:
  "cinit_stores gs \<subseteq> interval_gamma gs (Lifted cinit_ivl_st) Bot"
  by (auto simp: interval_gamma_def cinit_stores_def gamma_state_def fun_of_resolved_st_q_for_def
                 fun_of_st_cinit_ivl_st_for)

text \<open>
  \<^locale>\<open>dg_analysis_adapter\<close> at the same executable solved system, handed the readback
  as \<open>rd\<close> and Interval's classifier; its activation-collect soundness is the entry-state
  soundness theorem, stated against the routed local unknown read back through
  \<^const>\<open>gamma_state_lift\<close>. The four coverage hypotheses are properties of the
  \<^emph>\<open>solved\<close> system -- which keys the executable solver actually covers -- and are
  carried the same way \<^const>\<open>entry_state_terminates\<close> is: as \<open>by eval\<close>-checkable facts
  about a concrete, terminated solve.
\<close>

interpretation entry_state_adapter: dg_analysis_adapter "interval_spec gs empty_pred" "interval_gamma gs" gs
    "compile_prog Pi ps" "Analysis_Global ()" "entry_state_route_gen gs empty_pred" Bot "Lifted cinit_ivl_st" Bot
    "snd (entry_state_sol gs empty_pred Pi ps)" "fst (entry_state_sol gs empty_pred Pi ps)"
    "(cfg_exit (compile_prog Pi ps), [])" "entry_state_sg_st gs empty_pred Pi ps"
    Activation_Seed "\<lambda>d. d = Bot"
    "\<lambda>m. gamma_state_lift (map_lift (fun_of_resolved_st_q_for gs) m)" entry_state_context_rel
    "map_lift (fun_of_resolved_st_q_for gs)" interval_classify_check
proof (unfold_locales, goal_cases FinE PP SgCov SgUncov Fwd FinC CallsUnique SeedKey
    IsBotBot IsBotSound ResolveSound
    EnterCover EnterTotal CombFwd GammaRd ClProved ClRefuted VarsFin)
  case FinE show ?case by (rule entry_state_fin)
next
  case PP show ?case by (rule entry_state_pp_routed[OF solves exact])
next
  case (SgCov v c)
  thus ?case by (simp add: entry_state_sg_st_def interval_gamma_def)
next
  case (SgUncov v c)
  thus ?case by (simp add: entry_state_sg_st_def)
next
  case (Fwd u a v c)
  thus ?case by (rule fwd_ok)
next
  case FinC show ?case by (rule entry_state_finC)
next
  case CallsUnique
  show ?case unfolding calls_source_unique_def using compile_prog_calls_source_unique by blast
next
  case (SeedKey p ctx) show ?case by simp
next
  case IsBotBot show ?case by simp
next
  case (IsBotSound d g') then show ?case by (simp add: interval_gamma_def)
next
  case (ResolveSound u ctx dst pars args p cont s)
  thus ?case by (simp add: static_resolve_iff[OF entry_state_finC])
next
  case (EnterCover u ctx dst pars args p cont s ctx')
  show ?case using entry_state_routed.routed.routed_entry_cover[OF EnterCover(1,2,3,4)] .
next
  case (EnterTotal u ctx dst pars args p cont s)
  show ?case using entry_state_routed.routed.routed_entry_total[OF EnterTotal(1,2,3)] .
next
  case (CombFwd cl c1 dst pars args p cont)
  show ?case using CombFwd(1,2) by (rule comb_fwd_ok)
next
  case (GammaRd d g')
  show ?case by (simp add: interval_gamma_def)
next
  case (ClProved c d s)
  thus ?case by (rule interval_classify_check_proved)
next
  case (ClRefuted c d s)
  thus ?case by (rule interval_classify_check_refuted)
next
  case VarsFin show ?case by (rule entry_state_vars_finite[OF solves])
qed

theorem entry_state_activation_collect_sound:
  "activation_collect gs entry_state_context_rel [] (compile_prog Pi ps) (cinit_stores gs) v ctx
     \<subseteq> gamma_state_lift (map_lift (fun_of_resolved_st_q_for gs)
           (entry_state_sg_st gs empty_pred Pi ps (Inl (v, ctx))))"
  by (rule entry_state_routed.routed.activation_collect_dg_sound
             [OF entry_cov entry_state_cinit_le_cinit_ivl_st])

text \<open>Every valid trace over the entry-state routing admits some context: the existence half
  \<open>activation_collect_dg_sound\<close> needs, re-exported so a source-level caller can name a
  context witness without going through \<^locale>\<open>ltr_coverage\<close> itself.\<close>

theorem entry_state_has_context:
  assumes "t \<in> valid_ltr gs (compile_prog Pi ps) (cinit_stores gs)"
  shows "\<exists>c. trace_context gs entry_state_context_rel [] (compile_prog Pi ps) t c"
  by (rule entry_state_routed.routed.routed_valid_ltr_has_context
             [OF entry_cov entry_state_cinit_le_cinit_ivl_st assms])


end



section \<open>Solved-result table\<close>

text \<open>
  The solved entry-state D/G system, read as a
  \<^typ>\<open>(ivl list, ivl abs_state) analysis_result\<close>. This is the
  context-sensitive counterpart of \<open>Interval_Checks\<close>'s monovariant
  \<open>analyse_interval_td_result_for\<close>: the context type is \<^typ>\<open>ivl list\<close>, the
  entered abstract value of the callee's declared formals, so a node covered
  under several activations keeps one \<^type>\<open>lifted\<close> per activation.

  Construction is mechanical. \<^const>\<open>entry_state_sol\<close>'s own first component is
  the key set verbatim -- the solver already knows exactly which
  \<open>(node, context)\<close> pairs it reached, so nothing here rescans the solved map
  or reconstructs coverage. Each local unknown goes through
  \<^const>\<open>normalize_point\<close> exactly as it is stored, in its pre-conversion
  \<^typ>\<open>ivl resolved_st_q lifted\<close> shape; no context is joined at construction
  time, and an uncovered context is answered by \<^const>\<open>lookup_context\<close>'s
  membership guard with \<^const>\<open>Bot\<close>, never by falling back to the
  seeded default context \<open>[]\<close>.

  The \<open>[code]\<close> rewrite is a single-solve fix: binding \<open>sol\<close> once, outside the
  per-key closure, compiles to a single shared thunk, so neither building the
  table nor querying it re-solves. \<^const>\<open>entry_state_sol_prog\<close> is fully
  applied at that binding, so it is not the partially applied closure
  \<^const>\<open>entry_state_sg_st\<close> would produce, whose body -- including its own
  internal \<^const>\<open>entry_state_sol\<close> calls -- would re-run at every key.
\<close>

definition analyse_interval_entry_state_result_for ::
    "(vname \<Rightarrow> bool) \<Rightarrow> imp_prog \<Rightarrow> (ivl list, ivl abs_state) analysis_result" where
  "analyse_interval_entry_state_result_for gs p =
     Analysis_Result
       (fst (entry_state_sol_prog gs p))
       (\<lambda>v ctx. normalize_point gs
                  (canonicalize_lift (resolved_st_q_is_bot_for (declared_global_vars p))
                    (locals (snd (entry_state_sol_prog gs p) (Inl (v, ctx))))))"

declare analyse_interval_entry_state_result_for_def [code del]

lemma analyse_interval_entry_state_result_for_code [code]:
  "analyse_interval_entry_state_result_for gs p =
     (let sol = entry_state_sol_prog gs p; gl = declared_global_vars p
      in Analysis_Result (fst sol)
           (\<lambda>v ctx. normalize_point gs
                      (canonicalize_lift (resolved_st_q_is_bot_for gl)
                        (locals (snd sol (Inl (v, ctx)))))))"
  unfolding analyse_interval_entry_state_result_for_def Let_def by (rule refl)

text \<open>Convenience instance at \<^const>\<open>declared_global\<close> \<open>p\<close> and
  \<^const>\<open>prog_main_name\<close>, the instantiation the production entry points use.\<close>

definition analyse_interval_entry_state_result ::
    "imp_prog \<Rightarrow> (ivl list, ivl abs_state) analysis_result" where
  "analyse_interval_entry_state_result p =
     analyse_interval_entry_state_result_for (declared_global p) p"

text \<open>
  The route-consistency corollary at the table, on both outcomes: a caller
  point the table answers \<^const>\<open>Lifted\<close> either routes to the same callee
  context the solved system was built with, or is exactly the case that
  context is dead. \<^const>\<open>lookup_context\<close>'s membership guard supplies \<open>reach\<close>
  --- an uncovered key answers \<^const>\<open>Bot\<close>, so a \<^const>\<open>Lifted\<close>
  answer already witnesses that the solver stored this point --- and the
  \<open>not_bot\<close> premise \<open>entry_state_callee_ctx_eq_route_partial\<close> needs now
  comes from \<^const>\<open>canonicalize_lift\<close>'s own case split at the result
  boundary, not from \<open>normalize_point\<close> inspecting the raw value itself:
  \<open>norm\<close> below is stated over \<open>canonicalize_lift (resolved_st_q_is_bot_for
  (declared_global_vars p))\<close> applied to the raw solved local unknown,
  matching exactly what \<open>analyse_interval_entry_state_result_for\<close> now
  builds. No \<open>live\<close> side condition survives to this corollary either.
\<close>

corollary entry_state_callee_ctx_at_result:
  assumes reach: "lookup_context (analyse_interval_entry_state_result_for (declared_global p) p)
                    u ctx = Lifted st"
  shows "entry_state_callee_ctx (declared_global p) ca st =
    (if entered_state_abs (declared_global p) (Lifted st) ca = Bot
     then None
     else Some (entry_state_route (declared_global p)
               (resolved_st_q_is_bot_for (declared_global_vars p))
               (entry_state_entered (declared_global p)
                  (resolved_st_q_is_bot_for (declared_global_vars p))
                  (locals (snd (entry_state_sol_prog (declared_global p) p) (Inl (u, ctx)))) ca)
               ca))"
proof -
  have globals: "\<And>x. declared_global p x = (x \<in> set (declared_global_vars p))" by simp
  have exact: "\<And>s::ivl resolved_st_q. resolved_st_q_is_bot_for (declared_global_vars p) s
                     = is_empty_state (fun_of_resolved_st_q_for (declared_global p) s)"
    by (rule resolved_st_q_is_bot_for_iff[OF globals])
  have norm: "normalize_point (declared_global p)
                (canonicalize_lift (resolved_st_q_is_bot_for (declared_global_vars p))
                  (locals (snd (entry_state_sol_prog (declared_global p) p) (Inl (u, ctx)))))
              = Lifted st"
    using reach
    by (simp add: lookup_context_def analyse_interval_entry_state_result_for_def
                  split: if_splits)
  have key: "map_lift (fun_of_resolved_st_q_for (declared_global p))
               (locals (snd (entry_state_sol_prog (declared_global p) p) (Inl (u, ctx))))
             = Lifted st
           \<and> \<not> is_empty_state st"
  proof (cases "locals (snd (entry_state_sol_prog (declared_global p) p) (Inl (u, ctx)))")
    case Bot
    with norm show ?thesis by simp
  next
    case (Lifted s0)
    show ?thesis
    proof (cases "resolved_st_q_is_bot_for (declared_global_vars p) s0")
      case True
      with norm Lifted show ?thesis by simp
    next
      case False
      with norm Lifted exact show ?thesis by auto
    qed
  qed
  have reach_raw: "map_lift (fun_of_resolved_st_q_for (declared_global p))
                      (locals (snd (entry_state_sol_prog (declared_global p) p) (Inl (u, ctx))))
                    = Lifted st"
    and not_bot: "\<not> is_empty_state st"
    using key by auto
  show ?thesis
    by (rule entry_state_callee_ctx_eq_route_partial[OF exact reach_raw not_bot])
qed


section \<open>Contextual check report\<close>

text \<open>
  The check report is a projection of the result table above, not a second
  reading of the solved system: \<^const>\<open>classify_checks_ctx\<close> takes only a
  \<^type>\<open>cfg\<close>, an \<^type>\<open>analysis_result\<close>, and a classifier, so no solver
  state, solved map, or per-key lookup reaches the classification step. The
  entry-state specifics live here, in the one argument that supplies the
  table.

  This is what removes the fabricated verdict a solver-level reading gives
  dead code. Querying an uncovered or dead \<open>(node, context)\<close> pair against the
  solved map answers with a bottom abstract state, and a bottom state
  satisfies \<^const>\<open>interval_less_true\<close> vacuously, so \<open>check_query\<close> answers
  \<^term>\<open>Some True\<close> and the check classifies \<^const>\<open>Check_Proved\<close> even though
  no execution reaches
  it. \<^const>\<open>lookup_context\<close> answers \<^const>\<open>Bot\<close> for both cases
  instead --- the membership guard for the uncovered one, \<^const>\<open>normalize_point\<close>'s
  witness-bottom test for the covered-but-dead one --- and
  \<^const>\<open>classify_point\<close> declines to classify against it at all.

  Contexts stay separate in \<open>entry_state_check_projection\<close> and are
  aggregated only in \<open>entry_state_verdict_report_prog\<close>, which is the
  resolution the source level actually needs: one source check may be dead
  in some activations and live in others, and only the dead ones must drop
  out of the join.

  \<^const>\<open>analyse_interval_entry_state_result_for\<close> occurs once here, and it
  binds its own solve once, so a whole report costs exactly one solve
  regardless of how many checks or contexts it covers.
\<close>

definition entry_state_check_projection ::
    "imp_prog \<Rightarrow> (pp \<times> exp \<times> (ivl list \<times> contextual_verdict) set) list" where
  "entry_state_check_projection p =
     classify_checks_ctx (prog_cfg p)
       (analyse_interval_entry_state_result_for (declared_global p) p)
       interval_classify_check"

definition entry_state_verdict_report_prog ::
    "imp_prog \<Rightarrow> (pp \<times> exp \<times> contextual_verdict) list" where
  "entry_state_verdict_report_prog p =
     map (\<lambda>(u, c, vs). (u, c, aggregate_verdicts (snd ` vs)))
       (entry_state_check_projection p)"

text \<open>Aggregating the projection is exactly \<^const>\<open>classify_checks_verdicts\<close>
  over the same table; going through the projection is what keeps the two
  reports to one shared solve.\<close>

lemma entry_state_verdict_report_prog_eq:
  "entry_state_verdict_report_prog p =
     classify_checks_verdicts (prog_cfg p)
       (analyse_interval_entry_state_result_for (declared_global p) p)
       interval_classify_check"
  unfolding entry_state_verdict_report_prog_def entry_state_check_projection_def
  by (rule classify_checks_verdicts_proj)

definition analyse_interval_entry_state ::
    "imp_prog \<Rightarrow> (pp \<times> exp \<times> contextual_verdict) list" where
  "analyse_interval_entry_state p = entry_state_verdict_report_prog p"

end
