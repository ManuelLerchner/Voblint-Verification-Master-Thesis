theory Int_Ctx_None_Sound
  imports
    "Voblint_Exec.Monovariant_Analysis_Result"
    "Voblint_Exec.Routed_Domain_Exec"
    "Voblint_Analysis.Int_Classify"
    "Voblint_Core.DG_Analysis_Adapter"
    "Voblint_Core.Routed_Context"
    "Voblint_Core.Routed_Context_Unit"
    "Voblint_Solver.TD_Solver_Menu"
    "Voblint_VIMP.VIMP_Program"
    "Voblint_Core.Activation_Backbone"
begin

section \<open>Int at the routed spine, instantiated at the unit context\<close>

text \<open>
  Redirects the composite integer domain's production Base-family (\<^const>\<open>dg_gen_of\<close>)
  analysis onto the routed D/G spine (\<^locale>\<open>dg_ctx_activation_base\<close>,
  \<^locale>\<open>unit_routed_context\<close>) that Interval's own entry-state and call-string context
  analyses already use, mirroring Sign's own routed-unit-context production cutover
  exactly. The context here is \<^typ>\<open>unit\<close>:
  \<^locale>\<open>unit_routed_context\<close> (\<^theory>\<open>Voblint_Core.Routed_Context_Unit\<close>) fixes
  \<^const>\<open>route_unit\<close>, so every routing-agreement obligation that Interval's
  formals-context instance must prove from its own transfer facts collapses here
  to a free lemma about the constant function \<^const>\<open>route_unit\<close>.

  Unlike Sign and Interval, \<^typ>\<open>int_dom\<close> threads a \<^typ>\<open>refine_mode\<close> parameter
  (\<^const>\<open>int_tf_st_for\<close>, \<^const>\<open>int_dom_enter_st_for\<close>, both fixed here as a genuine
  ``mode'' argument rather than pinned to \<^const>\<open>Refine_Fixpoint\<close>): every commute and
  soundness fact this development needs is already split per mode in
  \<^theory>\<open>Voblint_Analysis.Int_Exec\<close>, so recombining them into one mode-generic
  fact is a three-way \<open>cases mode\<close> citing an existing lemma per branch, not new
  proof content.

  Soundness below is derived directly from \<^locale>\<open>dg_ctx_activation_base\<close>'s generic
  machinery against the collecting semantics, exactly as Sign's and Interval's own
  routed analyses are derived. No comparison to Int's Base-family production result is
  attempted or needed: \<^const>\<open>dg_gen_of\<close> never appears in this development.

  The public result/report table (Section 7) interprets \<^locale>\<open>dg_analysis_adapter\<close>
  directly instead of hand-rolling one: Sign's own file predates that locale.
\<close>

subsection \<open>Global key: real globals vs callee-entry seed slots\<close>

text \<open>
  \<^typ>\<open>unit\<close> context, so the seed constructor's second field is \<^typ>\<open>unit\<close> rather
  than an interesting per-context payload: exactly one seed slot per callee entry.
\<close>

datatype gk = Global | Seed (seed_pp: pp) (seed_ctx: unit)

subsection \<open>The routed unit-context D/G spec\<close>

text \<open>
  The same Base-style whole-state specification the production
  \<^const>\<open>analyse_int_dg_eqs_for\<close> already solves over
  (\<^theory>\<open>Voblint_Analysis.Int_Exec_Sound\<close>), at the same
  \<^const>\<open>int_tf_st_for\<close>/\<^const>\<open>int_dom_enter_st_for\<close> primitives, \<open>mode\<close> included.
  Only the equation-generator wrapped around this spec changes (\<^const>\<open>dg_gen_of\<close>
  there, the routed keyed-seed generator here) --- the spec itself, and every
  domain-transfer soundness fact about it, is untouched. Argument order (\<open>mode\<close>,
  \<open>empty_pred\<close>, \<open>gs\<close>) matches \<^const>\<open>analyse_int_dg_eqs_for\<close>'s own.
\<close>

definition ictx_spec ::
  "refine_mode \<Rightarrow> (int_dom exec_dg_st \<Rightarrow> bool) \<Rightarrow> (vname \<Rightarrow> bool)
     \<Rightarrow> ('x, 'k, int_dom exec_dg_st lifted, int_dom exec_dg_st lifted) dg_spec"
where
  "ictx_spec mode empty_pred gs =
     base_dg_spec_st_for_lifted gs empty_pred (int_tf_st_for mode gs) (int_dom_enter_st_for mode gs)"

definition ictx_abs_spec ::
    "refine_mode \<Rightarrow> (vname \<Rightarrow> bool)
     \<Rightarrow> ('x, 'k, int_dom abs_state lifted, int_dom abs_state lifted) dg_spec" where
  "ictx_abs_spec mode gs = base_dg_spec_for_lifted gs is_empty_state (int_tf_for mode gs)"

subsection \<open>The routed equation system and its executable solution\<close>

definition ictx_eqs ::
    "refine_mode \<Rightarrow> (int_dom exec_dg_st \<Rightarrow> bool) \<Rightarrow> (vname \<Rightarrow> bool) \<Rightarrow> proc_table \<Rightarrow> pname list \<Rightarrow> (pp \<times> unit, gk, (int_dom exec_dg_st lifted, int_dom exec_dg_st lifted) dg_state) eqsT" where
  "ictx_eqs mode empty_pred gs Pi ps =
     side_cfg_T_eff_keyed_seed_dg_buffered intra_predecessor_addr_list (\<lambda>_. Global)
       route_unit
       (\<lambda>ctx' src a. dg_spec_edge_tree (ictx_spec mode empty_pred gs) a src Global)
       (routed_cmb_g (ictx_spec mode empty_pred gs) Global Seed
          (static_resolve (compile_prog Pi ps)))
       (routed_extra_g Seed Global)
       (compile_prog Pi ps) Bot (Lifted cinit_int_dom_st) Bot"

definition ictx_sol ::
    "refine_mode \<Rightarrow> (int_dom exec_dg_st \<Rightarrow> bool) \<Rightarrow> (vname \<Rightarrow> bool) \<Rightarrow> proc_table \<Rightarrow> pname list \<Rightarrow> (pp \<times> unit) set \<times> (pp \<times> unit + gk \<Rightarrow> (int_dom exec_dg_st lifted, int_dom exec_dg_st lifted) dg_state)" where
  "ictx_sol mode empty_pred gs Pi ps =
     TD_side_always_join_Interp_solve (ictx_eqs mode empty_pred gs Pi ps)
       (cfg_exit (compile_prog Pi ps), ())"

definition ictx_terminates ::
    "refine_mode \<Rightarrow> (int_dom exec_dg_st \<Rightarrow> bool) \<Rightarrow> (vname \<Rightarrow> bool) \<Rightarrow> proc_table \<Rightarrow> pname list \<Rightarrow> bool" where
  "ictx_terminates mode empty_pred gs Pi ps =
     TD_side_always_join_Interp.solve_dom TYPE(gk) TYPE((int_dom exec_dg_st lifted, int_dom exec_dg_st lifted) dg_state)
       (ictx_eqs mode empty_pred gs Pi ps) (cfg_exit (compile_prog Pi ps), ())"

lemma ictx_terminates_via_solve_c:
  assumes "TD_side_always_join_Interp_solve_c (ictx_eqs mode empty_pred gs Pi ps)
             (cfg_exit (compile_prog Pi ps), ()) \<noteq> None"
  shows "ictx_terminates mode empty_pred gs Pi ps"
  unfolding ictx_terminates_def
  by (rule TD_side_always_join_Interp.solve_dom_of_solve_c[OF assms])

subsection \<open>Route agreement collapses to a free lemma\<close>


subsection \<open>Domain commute facts, at the routed unit spec\<close>

text \<open>
  \<open>int_tf_st_for\<close>/\<open>int_dom_enter_st_for\<close> are themselves defined by a case split on
  \<open>mode\<close> (\<^theory>\<open>Voblint_Analysis.Int_Exec_Sound\<close>), so the mode-generic commute facts
  below are the same case split, citing each mode's own commute theorem
  (\<open>int_tf_st_never_for_commute\<close> etc., \<^theory>\<open>Voblint_Analysis.Int_Exec\<close>) unchanged.
\<close>

lemma int_tf_st_for_commute:
  "fun_of_resolved_st_q_for gs (int_tf_st_for mode gs a s) =
     apply_tf (int_tf_for mode gs) a (fun_of_resolved_st_q_for gs s)"
  by (cases mode)
     (simp_all add: int_tf_st_never_for_commute int_tf_st_once_for_commute int_tf_st_fixpoint_for_commute)

lemma int_dom_enter_st_for_commute:
  "fun_of_resolved_st_q_for gs (int_dom_enter_st_for mode gs ci s) =
     snd (tf_enter (int_tf_for mode gs) ci (fun_of_resolved_st_q_for gs s))"
proof (cases mode)
  case Refine_Never
  then show ?thesis
    by (simp only: int_dom_enter_st_for.simps int_tf_for.simps int_dom_enter_never_st_for_commute)
next
  case Refine_Once
  then show ?thesis
    by (simp only: int_dom_enter_st_for.simps int_tf_for.simps int_dom_enter_once_st_for_commute)
next
  case Refine_Fixpoint
  then show ?thesis
    by (simp only: int_dom_enter_st_for.simps int_tf_for.simps int_dom_enter_fixpoint_st_for_commute)
qed

text \<open>
  \<^locale>\<open>routed_domain_exec\<close> derives exactly this shape once, generic in a domain:
  an interpretation at Int's own mode-generic commute facts just above replaces what used
  to be Int's own copy of the derivation. It adds only the seed-key pair, its
  distinctness, and the two routing functions on top of
  \<^locale>\<open>routed_dg_domain_exec\<close>, so the interpretation carries no Int mathematics.
  \<^const>\<open>route_unit\<close> ignores its \<open>'D\<close> argument outright, so routing agreement is free
  inside the locale rather than an Int obligation at all.
\<close>

text \<open>
  The abstract-carrier soundness of the spec, generic in \<open>mode\<close>: a three-way case split
  citing Int's own per-mode transfer-soundness facts.  The executable-carrier soundness
  \<open>ictx_sound_exec\<close> below pulls it back along the readback.
\<close>

lemma int_is_sound_transfer_for: "sound_transfer_for gs (int_tf_for mode gs)"
proof (cases mode)
  case Refine_Never
  then show ?thesis by (simp add: int_never_is_sound_transfer_for)
next
  case Refine_Once
  then show ?thesis by (simp add: int_once_is_sound_transfer_for)
next
  case Refine_Fixpoint
  then show ?thesis by (simp add: int_fixpoint_is_sound_transfer_for)
qed

lemma ictx_abs_spec_sound: "sound_dg_spec (ictx_abs_spec mode gs) gamma_dg_base gs"
  unfolding ictx_abs_spec_def
  by (rule base_dg_spec_sound[OF int_is_sound_transfer_for is_empty_state_gamma_state_empty])

text \<open>The concretization the executable-carrier interpretations below use: a local
  unknown means \<^const>\<open>gamma_state_lift\<close> of its readback, the global slot is ignored as
  in \<^const>\<open>gamma_dg_base\<close>. Named at top level so a downstream theory can state it.\<close>

definition ictx_gamma ::
    "(vname \<Rightarrow> bool) \<Rightarrow> int_dom exec_dg_st lifted \<Rightarrow> int_dom exec_dg_st lifted \<Rightarrow> store set" where
  "ictx_gamma gs d g = gamma_state_lift (map_lift (fun_of_resolved_st_q_for gs) d)"

lemma ictx_gamma_Bot [simp]: "ictx_gamma gs Bot g = {}"
  by (simp add: ictx_gamma_def)

context
  fixes gs :: "vname \<Rightarrow> bool" and empty_pred :: "int_dom exec_dg_st \<Rightarrow> bool" and mode :: refine_mode
  assumes exact: "\<And>s. empty_pred s = is_empty_state (fun_of_resolved_st_q_for gs s)"
begin

interpretation int_unit: routed_domain_exec
  gs empty_pred "int_tf_st_for mode gs" "int_dom_enter_st_for mode gs" "int_tf_for mode gs"
  Global Seed route_unit route_unit static_resolve static_resolve
  by unfold_locales
     (rule int_tf_st_for_commute, rule int_dom_enter_st_for_commute, rule exact, simp, simp,
      simp add: static_resolve_def)

lemmas int_pp_st_gen = int_unit.pp_st

lemma ictx_gamma_eq: "ictx_gamma gs = int_unit.gamma_exec"
  by (intro ext) (simp add: ictx_gamma_def int_unit.gamma_exec_def gamma_dg_base_def)

theorem ictx_sound_exec: "sound_dg_spec (ictx_spec mode empty_pred gs) (ictx_gamma gs) gs"
  unfolding ictx_gamma_eq ictx_spec_def
  by (rule int_unit.sound_dg_spec_st[OF int_is_sound_transfer_for])

end

lemma seed_ne_global [simp]: "Seed p ctx \<noteq> Global"
  by simp

section \<open>The solver-generic instantiation\<close>

text \<open>
  Everything downstream of the executable post-solution reaches the solver through exactly one
  fact: that the solved pair is a \<^const>\<open>part_post_solution\<close> of \<^const>\<open>ictx_eqs\<close>.  The update
  rule itself never appears again.  \<open>ictx_solved\<close> therefore fixes the solved pair and its
  termination predicate and assumes that single fact, so each update rule contributes an
  interpretation rather than a copy of the development.
\<close>

locale ictx_solved =
  fixes ictx_sol :: "refine_mode \<Rightarrow> (int_dom exec_dg_st \<Rightarrow> bool) \<Rightarrow> (vname \<Rightarrow> bool) \<Rightarrow> proc_table
                  \<Rightarrow> pname list \<Rightarrow> (pp \<times> unit) set
                     \<times> (pp \<times> unit + gk \<Rightarrow> (int_dom exec_dg_st lifted, int_dom exec_dg_st lifted) dg_state)"
    and ictx_terminates :: "refine_mode \<Rightarrow> (int_dom exec_dg_st \<Rightarrow> bool) \<Rightarrow> (vname \<Rightarrow> bool) \<Rightarrow> proc_table
                         \<Rightarrow> pname list \<Rightarrow> bool"
  assumes pp_st:
    "ictx_terminates mode empty_pred gs Pi ps
       \<Longrightarrow> part_post_solution (ictx_eqs mode empty_pred gs Pi ps)
             (cfg_exit (compile_prog Pi ps), ())
             (snd (ictx_sol mode empty_pred gs Pi ps))
             (fst (ictx_sol mode empty_pred gs Pi ps))"
begin

text \<open>The solver's post-solution, for the unbuffered routed generator at the executable
  spec: the shape \<^locale>\<open>dg_ctx_activation_base\<close> consumes directly.\<close>

theorem ictx_pp_routed:
  assumes solves: "ictx_terminates mode empty_pred gs Pi ps"
    and exact: "\<And>s. empty_pred s = is_empty_state (fun_of_resolved_st_q_for gs s)"
  shows
  "part_post_solution
     (side_cfg_T_eff_keyed_seed_dg intra_predecessor_addr_list (\<lambda>_. Global) route_unit
        (\<lambda>ctx' src a. dg_spec_edge_tree (ictx_spec mode empty_pred gs) a src Global)
        (routed_cmb_g (ictx_spec mode empty_pred gs) Global Seed
           (static_resolve (compile_prog Pi ps)))
        (routed_extra_g Seed Global)
        (compile_prog Pi ps) Bot (Lifted cinit_int_dom_st) Bot)
     (cfg_exit (compile_prog Pi ps), ())
     (snd (ictx_sol mode empty_pred gs Pi ps)) (fst (ictx_sol mode empty_pred gs Pi ps))"
  using pp_st[OF solves] unfolding ictx_eqs_def ictx_spec_def by (rule int_pp_st_gen[OF exact])

text \<open>
  The routed spine is interpreted at Int's executable carrier and fed the solver's own
  table: a local unknown concretizes to \<^const>\<open>gamma_state_lift\<close> of its readback, the
  covered reader \<open>ictx_sg_st\<close> hands the table's local slot through unchanged, and no
  solved system is transported between carriers.
\<close>

definition ictx_sg_st ::
    "refine_mode \<Rightarrow> (int_dom exec_dg_st \<Rightarrow> bool) \<Rightarrow> (vname \<Rightarrow> bool) \<Rightarrow> proc_table
       \<Rightarrow> pname list \<Rightarrow> pp \<times> unit + gk \<Rightarrow> int_dom exec_dg_st lifted" where
  "ictx_sg_st mode empty_pred gs Pi ps k =
     (case k of
        Inl (v, ctx) \<Rightarrow>
          (if (v, ctx) \<in> fst (ictx_sol mode empty_pred gs Pi ps)
           then locals (snd (ictx_sol mode empty_pred gs Pi ps) (Inl (v, ctx)))
           else Bot)
      | Inr _ \<Rightarrow> Bot)"

context
  fixes mode :: refine_mode and empty_pred :: "int_dom exec_dg_st \<Rightarrow> bool" and gs :: "vname \<Rightarrow> bool"
    and Pi :: proc_table and ps :: "pname list"
  assumes solves: "ictx_terminates mode empty_pred gs Pi ps"
    and exact: "\<And>s. empty_pred s = is_empty_state (fun_of_resolved_st_q_for gs s)"
    and entry_cov: "(cfg_entry (compile_prog Pi ps), ()) \<in> fst (ictx_sol mode empty_pred gs Pi ps)"
    and fwd_ok: "\<And>u a v ctx. (u, ctx) \<in> fst (ictx_sol mode empty_pred gs Pi ps)
                   \<Longrightarrow> (u, a, v) \<in> intra (compile_prog Pi ps)
                   \<Longrightarrow> (v, ctx) \<in> fst (ictx_sol mode empty_pred gs Pi ps)"
    and call_fwd_ok: "\<And>u ctx dst pars args p cont.
        (u, ctx) \<in> fst (ictx_sol mode empty_pred gs Pi ps)
        \<Longrightarrow> (u, CallEdge dst pars args, FunctionEntry p, cont) \<in> calls (compile_prog Pi ps)
        \<Longrightarrow> (FunctionEntry p, ()) \<in> fst (ictx_sol mode empty_pred gs Pi ps)"
    and comb_fwd_ok: "\<And>cl c1 dst pars args p cont.
        (cl, c1) \<in> fst (ictx_sol mode empty_pred gs Pi ps)
        \<Longrightarrow> (cl, CallEdge dst pars args, FunctionEntry p, cont) \<in> calls (compile_prog Pi ps)
        \<Longrightarrow> (cont, c1) \<in> fst (ictx_sol mode empty_pred gs Pi ps)"
begin

subsection \<open>The solver's table as the solved system\<close>

interpretation ictx_compiled: compiled_cfg Pi ps "compile_prog Pi ps"
  by (unfold_locales; simp add: compile_prog_finite)

lemmas ictx_fin = ictx_compiled.finite_intra
lemmas ictx_finC = ictx_compiled.finite_calls

lemma ictx_sg_st_covered:
  "(v, ctx) \<in> fst (ictx_sol mode empty_pred gs Pi ps)
   \<Longrightarrow> ictx_sg_st mode empty_pred gs Pi ps (Inl (v, ctx))
         = locals (snd (ictx_sol mode empty_pred gs Pi ps) (Inl (v, ctx)))"
  by (simp add: ictx_sg_st_def)

lemma ictx_sg_st_uncovered_empty:
  "(v, ctx) \<notin> fst (ictx_sol mode empty_pred gs Pi ps)
     \<Longrightarrow> gamma_state_lift (map_lift (fun_of_resolved_st_q_for gs)
           (ictx_sg_st mode empty_pred gs Pi ps (Inl (v, ctx)))) = {}"
  by (simp add: ictx_sg_st_def)

subsection \<open>Instantiating the generic DG-native activation discharge\<close>

interpretation ictx_dg_base: sound_dg_spec "ictx_spec mode empty_pred gs" "ictx_gamma gs" gs
  by (rule ictx_sound_exec[OF exact])

interpretation ictx_routed: unit_routed_context "ictx_spec mode empty_pred gs" "ictx_gamma gs" gs
    "compile_prog Pi ps" Global Bot "Lifted cinit_int_dom_st" Bot
    "snd (ictx_sol mode empty_pred gs Pi ps)" "fst (ictx_sol mode empty_pred gs Pi ps)"
    "(cfg_exit (compile_prog Pi ps), ())" "ictx_sg_st mode empty_pred gs Pi ps" Seed
    "\<lambda>m. gamma_state_lift (map_lift (fun_of_resolved_st_q_for gs) m)"
proof (unfold_locales, goal_cases FinE PP SgCov SgUncov Fwd FinC SeedKey CallFwd CombFwd EnterAgree)
  case FinE show ?case by (rule ictx_fin)
next
  case PP show ?case by (rule ictx_pp_routed[OF solves exact])
next
  case (SgCov v ctx) then show ?case
    by (simp add: ictx_sg_st_def ictx_gamma_def)
next
  case (SgUncov v ctx) then show ?case by (rule ictx_sg_st_uncovered_empty)
next
  case (Fwd u a v ctx) then show ?case by (rule fwd_ok)
next
  case FinC show ?case by (rule ictx_finC)
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

lemma ictx_cinit_le_cinit_int_dom_st:
  "cinit_stores gs \<subseteq> ictx_gamma gs (Lifted cinit_int_dom_st) Bot"
  by (auto simp: ictx_gamma_def cinit_stores_def gamma_state_def fun_of_resolved_st_q_for_def
                 fun_of_st_cinit_int_dom_st_for gamma_int_dom_top)
subsection \<open>The public result/report table, via the generic adapter locale\<close>

text \<open>
  \<^locale>\<open>dg_analysis_adapter\<close> at the same executable solved system as
  \<open>ictx_routed\<close> above, handed the readback as \<open>rd\<close>; the classifier obligations are
  \<open>int_classify_check_proved\<close>/\<open>int_classify_check_refuted\<close>
  (\<^theory>\<open>Voblint_Analysis.Int_Classify\<close>).
\<close>

interpretation ictx_adapter: dg_analysis_adapter "ictx_spec mode empty_pred gs" "ictx_gamma gs" gs
    "compile_prog Pi ps" Global route_unit Bot "Lifted cinit_int_dom_st" Bot
    "snd (ictx_sol mode empty_pred gs Pi ps)" "fst (ictx_sol mode empty_pred gs Pi ps)"
    "(cfg_exit (compile_prog Pi ps), ())" "ictx_sg_st mode empty_pred gs Pi ps"
    Seed "\<lambda>m. gamma_state_lift (map_lift (fun_of_resolved_st_q_for gs) m)" enterc_unit
    "map_lift (fun_of_resolved_st_q_for gs)" int_classify_check
proof (unfold_locales, goal_cases FinE PP SgCov SgUncov Fwd FinC SeedKey ResolveSound
    RouteEnterc CallFwd CombFwd EnterAgree GammaRd ClProved ClRefuted)
  case FinE show ?case by (rule ictx_fin)
next
  case PP show ?case by (rule ictx_pp_routed[OF solves exact])
next
  case (SgCov v c)
  thus ?case by (simp add: ictx_sg_st_def ictx_gamma_def)
next
  case (SgUncov v c)
  thus ?case by (simp add: ictx_sg_st_def)
next
  case (Fwd u a v c)
  thus ?case by (rule fwd_ok)
next
  case FinC show ?case by (rule ictx_finC)
next
  case (SeedKey p ctx) show ?case by simp
next
  case (ResolveSound u ctx dst pars args p cont s)
  thus ?case by (simp add: static_resolve_iff[OF ictx_finC])
next
  case (RouteEnterc u ctx dst pars args p cont s)
  show ?case by simp
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
              \<in> calls (compile_prog Pi ps)"
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

lemmas ictx_analyse_result_def = ictx_adapter.analyse_result_def
lemmas ictx_analyse_report_ctx_def = ictx_adapter.analyse_report_ctx_def
lemmas ictx_analyse_report_def = ictx_adapter.analyse_report_def
lemmas ictx_analyse_report_ctx_proved_sound = ictx_adapter.analyse_report_ctx_proved_sound
lemmas ictx_analyse_report_ctx_refuted_sound = ictx_adapter.analyse_report_ctx_refuted_sound

text \<open>
  \<open>ictx_result_node_sound\<close> re-exports the adapter's generic node-soundness bridge
  (\<^theory>\<open>Voblint_Core.DG_Analysis_Adapter\<close>). \<open>ictx_analyse_result_eq\<close> identifies that
  reading with the raw-tuple shape \<open>analyse_int_ctx_result_for\<close> (defined below)
  already builds by hand, mirroring \<open>Interval_Ctx_None_Sound.ictx_analyse_result_eq\<close>.
\<close>

lemmas ictx_result_node_sound = ictx_adapter.analyse_result_node_sound
lemmas ictx_activation_collect_sound = ictx_routed.routed.activation_collect_dg_sound

lemma ictx_analyse_result_eq:
  "lookup_context ictx_adapter.analyse_result v ctx =
     (if (v, ctx) \<in> fst (ictx_sol mode empty_pred gs Pi ps)
      then normalize_point gs
             (canonicalize_lift empty_pred (locals (snd (ictx_sol mode empty_pred gs Pi ps) (Inl (v, ctx)))))
      else Bot)"
  unfolding ictx_adapter.lookup_context_analyse_result
  by (cases "locals (snd (ictx_sol mode empty_pred gs Pi ps) (Inl (v, ctx)))")
     (simp_all add: exact normalize_lift_def)

end

end

section \<open>The four update-rule instances\<close>

text \<open>Each rule's entire obligation is \<open>partial_post_solution\<close>, which
  \<^locale>\<open>TD_side_upd_rule\<close> proves once for every update rule.\<close>

lemma ictx_join_pp_st:
  "ictx_terminates mode empty_pred gs Pi ps
     \<Longrightarrow> part_post_solution (ictx_eqs mode empty_pred gs Pi ps)
           (cfg_exit (compile_prog Pi ps), ())
           (snd (ictx_sol mode empty_pred gs Pi ps))
           (fst (ictx_sol mode empty_pred gs Pi ps))"
  unfolding ictx_sol_def ictx_terminates_def
  by (rule TD_side_always_join_Interp.partial_post_solution[OF _ surjective_pairing])

global_interpretation ictx_join: ictx_solved ictx_sol ictx_terminates
  by unfold_locales (rule ictx_join_pp_st)

lemmas ictx_result_node_sound = ictx_join.ictx_result_node_sound
lemmas ictx_analyse_result_eq = ictx_join.ictx_analyse_result_eq
lemmas ictx_cinit_le_cinit_int_dom_st = ictx_join.ictx_cinit_le_cinit_int_dom_st
lemmas ictx_activation_collect_sound = ictx_join.ictx_activation_collect_sound
lemmas ictx_analyse_report_ctx_proved_sound = ictx_join.ictx_analyse_report_ctx_proved_sound
lemmas ictx_analyse_report_ctx_refuted_sound = ictx_join.ictx_analyse_report_ctx_refuted_sound
lemmas ictx_analyse_result_def = ictx_join.ictx_analyse_result_def
lemmas ictx_analyse_report_ctx_def = ictx_join.ictx_analyse_report_ctx_def
lemmas ictx_analyse_report_def = ictx_join.ictx_analyse_report_def

section \<open>PerOrigin solver instantiation, at the same routed unit-context spec\<close>

text \<open>
  Mirrors the always-join instantiation above (\<open>ictx_eqs\<close>/\<open>ictx_sol\<close>/\<open>ictx_terminates\<close>)
  under \<^const>\<open>TD_side_per_origin_Interp_solve\<close> instead, solving the exact same
  \<open>ictx_eqs\<close> equation system -- mirroring how Int's own Base family
  (\<^theory>\<open>Voblint_Analysis.Int_Exec_Sound\<close>) already solves \<open>analyse_int_dg_eqs_for\<close>
  under three interchangeable update rules, orthogonally to the \<open>refine_mode\<close> axis
  threaded through \<open>mode\<close>. Genuinely sound: \<^locale>\<open>TD_side_upd_rule\<close>'s
  \<open>solve_dom\<close>/\<open>partial_post_solution\<close> are locale-generic over the update rule, so
  \<open>TD_side_per_origin_Interp\<close>'s own \<open>partial_post_solution\<close> instance discharges the same
  obligation \<open>TD_side_always_join_Interp\<close>'s \<open>partial_post_solution\<close> did above, with no
  extra premises.
\<close>

definition ictx_sol_per_origin ::
    "refine_mode \<Rightarrow> (int_dom exec_dg_st \<Rightarrow> bool) \<Rightarrow> (vname \<Rightarrow> bool) \<Rightarrow> proc_table \<Rightarrow> pname list \<Rightarrow> (pp \<times> unit) set \<times> (pp \<times> unit + gk \<Rightarrow> (int_dom exec_dg_st lifted, int_dom exec_dg_st lifted) dg_state)" where
  "ictx_sol_per_origin mode empty_pred gs Pi ps =
     TD_side_per_origin_Interp_solve (ictx_eqs mode empty_pred gs Pi ps)
       (cfg_exit (compile_prog Pi ps), ())"

definition ictx_terminates_per_origin ::
    "refine_mode \<Rightarrow> (int_dom exec_dg_st \<Rightarrow> bool) \<Rightarrow> (vname \<Rightarrow> bool) \<Rightarrow> proc_table \<Rightarrow> pname list \<Rightarrow> bool" where
  "ictx_terminates_per_origin mode empty_pred gs Pi ps =
     TD_side_per_origin_Interp.solve_dom TYPE(gk) TYPE((int_dom exec_dg_st lifted, int_dom exec_dg_st lifted) dg_state)
       (ictx_eqs mode empty_pred gs Pi ps) (cfg_exit (compile_prog Pi ps), ())"

lemma ictx_terminates_per_origin_via_solve_c:
  assumes "TD_side_per_origin_Interp_solve_c (ictx_eqs mode empty_pred gs Pi ps)
             (cfg_exit (compile_prog Pi ps), ()) \<noteq> None"
  shows "ictx_terminates_per_origin mode empty_pred gs Pi ps"
  unfolding ictx_terminates_per_origin_def
  by (rule TD_side_per_origin_Interp.solve_dom_of_solve_c[OF assms])

subsection \<open>The PerOrigin instance\<close>

lemma ictx_per_origin_pp_st:
  "ictx_terminates_per_origin mode empty_pred gs Pi ps
     \<Longrightarrow> part_post_solution (ictx_eqs mode empty_pred gs Pi ps)
           (cfg_exit (compile_prog Pi ps), ())
           (snd (ictx_sol_per_origin mode empty_pred gs Pi ps))
           (fst (ictx_sol_per_origin mode empty_pred gs Pi ps))"
  unfolding ictx_sol_per_origin_def ictx_terminates_per_origin_def
  by (rule TD_side_per_origin_Interp.partial_post_solution[OF _ surjective_pairing])

global_interpretation ictx_po: ictx_solved ictx_sol_per_origin ictx_terminates_per_origin
  by unfold_locales (rule ictx_per_origin_pp_st)

lemmas ictx_result_node_sound_per_origin = ictx_po.ictx_result_node_sound
lemmas ictx_analyse_result_eq_per_origin = ictx_po.ictx_analyse_result_eq
lemmas ictx_cinit_le_cinit_int_dom_st_per_origin = ictx_po.ictx_cinit_le_cinit_int_dom_st
lemmas ictx_activation_collect_sound_per_origin = ictx_po.ictx_activation_collect_sound
lemmas ictx_analyse_report_ctx_proved_sound_per_origin = ictx_po.ictx_analyse_report_ctx_proved_sound
lemmas ictx_analyse_report_ctx_refuted_sound_per_origin = ictx_po.ictx_analyse_report_ctx_refuted_sound
lemmas ictx_analyse_result_per_origin_def = ictx_po.ictx_analyse_result_def
lemmas ictx_analyse_report_ctx_per_origin_def = ictx_po.ictx_analyse_report_ctx_def
lemmas ictx_analyse_report_per_origin_def = ictx_po.ictx_analyse_report_def


section \<open>Apinis warrowing solver instantiation, at the same routed unit-context spec\<close>

text \<open>
  Int's default solver: mirrors the always-join instantiation above under
  \<^const>\<open>TD_side_warrowing_apinis_Interp_solve\<close> instead, solving the exact same
  \<open>ictx_eqs\<close> equation system -- exactly as Interval's own entry-state contextual mode
  already does. No \<open>int_dom\<close>-specific widen/narrow bridging fact is needed: those facts
  are needed only by the Base family's separate \<open>restrict_global_resolved_q\<close>
  bookkeeping for its flow-insensitive global slot
  (\<^theory>\<open>Voblint_Analysis.Int_Exec_Sound\<close>), which the routed spine's keyed-seed
  \<open>Global\<close>/\<open>Seed\<close> globals replace outright. \<^locale>\<open>TD_side_upd_rule\<close>'s
  \<open>solve_dom\<close>/\<open>partial_post_solution\<close> being locale-generic over the update rule (as
  for PerOrigin above) is exactly what makes this a mechanical solver-call swap here too.
\<close>

definition ictx_sol_warrow ::
    "refine_mode \<Rightarrow> (int_dom exec_dg_st \<Rightarrow> bool) \<Rightarrow> (vname \<Rightarrow> bool) \<Rightarrow> proc_table \<Rightarrow> pname list \<Rightarrow> (pp \<times> unit) set \<times> (pp \<times> unit + gk \<Rightarrow> (int_dom exec_dg_st lifted, int_dom exec_dg_st lifted) dg_state)" where
  "ictx_sol_warrow mode empty_pred gs Pi ps =
     TD_side_warrowing_apinis_Interp_solve (ictx_eqs mode empty_pred gs Pi ps)
       (cfg_exit (compile_prog Pi ps), ())"

definition ictx_terminates_warrow ::
    "refine_mode \<Rightarrow> (int_dom exec_dg_st \<Rightarrow> bool) \<Rightarrow> (vname \<Rightarrow> bool) \<Rightarrow> proc_table \<Rightarrow> pname list \<Rightarrow> bool" where
  "ictx_terminates_warrow mode empty_pred gs Pi ps =
     TD_side_warrowing_apinis_Interp.solve_dom TYPE(gk) TYPE((int_dom exec_dg_st lifted, int_dom exec_dg_st lifted) dg_state)
       (ictx_eqs mode empty_pred gs Pi ps) (cfg_exit (compile_prog Pi ps), ())"

lemma ictx_terminates_warrow_via_solve_c:
  assumes "TD_side_warrowing_apinis_Interp_solve_c (ictx_eqs mode empty_pred gs Pi ps)
             (cfg_exit (compile_prog Pi ps), ()) \<noteq> None"
  shows "ictx_terminates_warrow mode empty_pred gs Pi ps"
  unfolding ictx_terminates_warrow_def
  by (rule TD_side_warrowing_apinis_Interp.solve_dom_of_solve_c[OF assms])

subsection \<open>The Apinis warrowing instance\<close>

lemma ictx_warrow_pp_st:
  "ictx_terminates_warrow mode empty_pred gs Pi ps
     \<Longrightarrow> part_post_solution (ictx_eqs mode empty_pred gs Pi ps)
           (cfg_exit (compile_prog Pi ps), ())
           (snd (ictx_sol_warrow mode empty_pred gs Pi ps))
           (fst (ictx_sol_warrow mode empty_pred gs Pi ps))"
  unfolding ictx_sol_warrow_def ictx_terminates_warrow_def
  by (rule TD_side_warrowing_apinis_Interp.partial_post_solution[OF _ surjective_pairing])

global_interpretation ictx_wa: ictx_solved ictx_sol_warrow ictx_terminates_warrow
  by unfold_locales (rule ictx_warrow_pp_st)

lemmas ictx_result_node_sound_warrow = ictx_wa.ictx_result_node_sound
lemmas ictx_analyse_result_eq_warrow = ictx_wa.ictx_analyse_result_eq
lemmas ictx_cinit_le_cinit_int_dom_st_warrow = ictx_wa.ictx_cinit_le_cinit_int_dom_st
lemmas ictx_activation_collect_sound_warrow = ictx_wa.ictx_activation_collect_sound
lemmas ictx_analyse_report_ctx_proved_sound_warrow = ictx_wa.ictx_analyse_report_ctx_proved_sound
lemmas ictx_analyse_report_ctx_refuted_sound_warrow = ictx_wa.ictx_analyse_report_ctx_refuted_sound
lemmas ictx_analyse_result_warrow_def = ictx_wa.ictx_analyse_result_def
lemmas ictx_analyse_report_ctx_warrow_def = ictx_wa.ictx_analyse_report_ctx_def
lemmas ictx_analyse_report_warrow_def = ictx_wa.ictx_analyse_report_def

section \<open>Warrowing-per-origin solver instantiation\<close>

text \<open>
  The fourth update rule.  \<^const>\<open>update_global_warrowing_per_origin\<close> widens each origin's
  own contribution and joins afterwards, where \<^const>\<open>update_global_warrowing_apinis\<close>
  widens the value already joined across every origin.
\<close>

definition ictx_sol_wpo ::
    "refine_mode \<Rightarrow> (int_dom exec_dg_st \<Rightarrow> bool) \<Rightarrow> (vname \<Rightarrow> bool) \<Rightarrow> proc_table \<Rightarrow> pname list \<Rightarrow> (pp \<times> unit) set \<times> (pp \<times> unit + gk \<Rightarrow> (int_dom exec_dg_st lifted, int_dom exec_dg_st lifted) dg_state)" where
  "ictx_sol_wpo mode empty_pred gs Pi ps =
     TD_side_warrowing_per_origin_Interp_solve (ictx_eqs mode empty_pred gs Pi ps)
       (cfg_exit (compile_prog Pi ps), ())"

definition ictx_terminates_wpo ::
    "refine_mode \<Rightarrow> (int_dom exec_dg_st \<Rightarrow> bool) \<Rightarrow> (vname \<Rightarrow> bool) \<Rightarrow> proc_table \<Rightarrow> pname list \<Rightarrow> bool" where
  "ictx_terminates_wpo mode empty_pred gs Pi ps =
     TD_side_warrowing_per_origin_Interp.solve_dom TYPE(gk)
       TYPE((int_dom exec_dg_st lifted, int_dom exec_dg_st lifted) dg_state)
       (ictx_eqs mode empty_pred gs Pi ps) (cfg_exit (compile_prog Pi ps), ())"

lemma ictx_terminates_wpo_via_solve_c:
  assumes "TD_side_warrowing_per_origin_Interp_solve_c (ictx_eqs mode empty_pred gs Pi ps)
             (cfg_exit (compile_prog Pi ps), ()) \<noteq> None"
  shows "ictx_terminates_wpo mode empty_pred gs Pi ps"
  unfolding ictx_terminates_wpo_def
  by (rule TD_side_warrowing_per_origin_Interp.solve_dom_of_solve_c[OF assms])

lemma ictx_wpo_pp_st:
  "ictx_terminates_wpo mode empty_pred gs Pi ps
     \<Longrightarrow> part_post_solution (ictx_eqs mode empty_pred gs Pi ps)
           (cfg_exit (compile_prog Pi ps), ())
           (snd (ictx_sol_wpo mode empty_pred gs Pi ps))
           (fst (ictx_sol_wpo mode empty_pred gs Pi ps))"
  unfolding ictx_sol_wpo_def ictx_terminates_wpo_def
  by (rule TD_side_warrowing_per_origin_Interp.partial_post_solution[OF _ surjective_pairing])

global_interpretation ictx_wpo: ictx_solved ictx_sol_wpo ictx_terminates_wpo
  by unfold_locales (rule ictx_wpo_pp_st)

lemmas ictx_result_node_sound_wpo = ictx_wpo.ictx_result_node_sound
lemmas ictx_analyse_result_eq_wpo = ictx_wpo.ictx_analyse_result_eq
lemmas ictx_cinit_le_cinit_int_dom_st_wpo = ictx_wpo.ictx_cinit_le_cinit_int_dom_st
lemmas ictx_activation_collect_sound_wpo = ictx_wpo.ictx_activation_collect_sound
lemmas ictx_analyse_report_ctx_proved_sound_wpo = ictx_wpo.ictx_analyse_report_ctx_proved_sound
lemmas ictx_analyse_report_ctx_refuted_sound_wpo = ictx_wpo.ictx_analyse_report_ctx_refuted_sound
lemmas ictx_analyse_result_wpo_def = ictx_wpo.ictx_analyse_result_def
lemmas ictx_analyse_report_ctx_wpo_def = ictx_wpo.ictx_analyse_report_ctx_def
lemmas ictx_analyse_report_wpo_def = ictx_wpo.ictx_analyse_report_def


section \<open>Whole-program convenience layer\<close>

text \<open>
  Mirrors Sign's own \<open>sctx_eqs_prog\<close>/\<open>sctx_sol_prog\<close>/\<open>sctx_terminates_prog\<close>: the
  same per-program instances at \<^const>\<open>declared_global_vars\<close>/\<^const>\<open>declared_global\<close>,
  so a caller supplies only \<open>mode\<close>, \<open>gs\<close>, and the \<^typ>\<open>imp_prog\<close> value.
\<close>

definition ictx_eqs_prog ::
    "refine_mode \<Rightarrow> (vname \<Rightarrow> bool) \<Rightarrow> imp_prog
       \<Rightarrow> (pp \<times> unit, gk, (int_dom exec_dg_st lifted, int_dom exec_dg_st lifted) dg_state) eqsT" where
  "ictx_eqs_prog mode gs p =
     ictx_eqs mode (resolved_st_q_is_bot_for (declared_global_vars p))
       gs (prog_table p) (prog_procs p)"

definition ictx_sol_prog ::
    "refine_mode \<Rightarrow> (vname \<Rightarrow> bool) \<Rightarrow> imp_prog
       \<Rightarrow> (pp \<times> unit) set \<times> (pp \<times> unit + gk \<Rightarrow> (int_dom exec_dg_st lifted, int_dom exec_dg_st lifted) dg_state)" where
  "ictx_sol_prog mode gs p =
     TD_side_always_join_Interp_solve (ictx_eqs_prog mode gs p) (cfg_exit (prog_cfg p), ())"

definition ictx_terminates_prog :: "refine_mode \<Rightarrow> (vname \<Rightarrow> bool) \<Rightarrow> imp_prog \<Rightarrow> bool" where
  "ictx_terminates_prog mode gs p =
     ictx_terminates mode (resolved_st_q_is_bot_for (declared_global_vars p))
       gs (prog_table p) (prog_procs p)"

lemma ictx_terminates_prog_via_solve_c:
  assumes "TD_side_always_join_Interp_solve_c
             (ictx_eqs mode (resolved_st_q_is_bot_for (declared_global_vars p))
                gs (prog_table p) (prog_procs p))
             (cfg_exit (compile_prog (prog_table p) (prog_procs p)), ()) \<noteq> None"
  shows "ictx_terminates_prog mode gs p"
  unfolding ictx_terminates_prog_def
  using assms by (rule ictx_terminates_via_solve_c)

text \<open>
  \<open>analyse_int_ctx_result_for\<close> is the routed-spine, always-join solved-result table,
  read as a \<^typ>\<open>(unit, int_dom abs_state) analysis_result\<close>: mirrors
  \<open>Interval_Ctx_None_Sound.analyse_interval_ctx_result_for\<close> exactly, at the
  same \<open>ictx_sol_prog\<close> instance above, generic in \<open>mode\<close> to match
  \<open>ictx_sol_prog\<close>'s own signature. The \<open>[code]\<close> swap avoids re-solving per
  lookup: \<^const>\<open>ictx_sol_prog\<close> is bound once as \<open>sol\<close>, then read pointwise via
  \<^const>\<open>normalize_point\<close>/\<^const>\<open>canonicalize_lift\<close>, exactly as
  \<open>monovariant_analysis_result_for\<close> does internally.
\<close>

definition analyse_int_ctx_result_for ::
    "refine_mode \<Rightarrow> (vname \<Rightarrow> bool) \<Rightarrow> imp_prog \<Rightarrow> (unit, int_dom abs_state) analysis_result" where
  "analyse_int_ctx_result_for mode gs p =
     Analysis_Result
       (fst (ictx_sol_prog mode gs p))
       (\<lambda>v ctx. normalize_point gs
                  (canonicalize_lift (resolved_st_q_is_bot_for (declared_global_vars p))
                    (locals (snd (ictx_sol_prog mode gs p) (Inl (v, ctx))))))"

declare analyse_int_ctx_result_for_def [code del]

lemma analyse_int_ctx_result_for_code [code]:
  "analyse_int_ctx_result_for mode gs p =
     (let sol = ictx_sol_prog mode gs p; gl = declared_global_vars p
      in Analysis_Result (fst sol)
           (\<lambda>v ctx. normalize_point gs
                      (canonicalize_lift (resolved_st_q_is_bot_for gl)
                        (locals (snd sol (Inl (v, ctx)))))))"
  unfolding analyse_int_ctx_result_for_def Let_def by (rule refl)

subsection \<open>Solved-result tables: PerOrigin and Apinis warrowing siblings\<close>

text \<open>
  Mirror \<open>ictx_sol_prog\<close>/\<open>ictx_terminates_prog\<close>/\<open>analyse_int_ctx_result_for\<close> (the Join
  table above) at the PerOrigin and Apinis warrowing solvers, reading the same
  \<open>ictx_eqs_prog\<close> equation system: the three-solver orthogonality Int's Base family
  already has (\<open>analyse_int_dg_for\<close>/\<open>_join_for\<close>/\<open>_per_origin_for\<close>,
  \<^theory>\<open>Voblint_Analysis.Int_Exec_Sound\<close>) now also holds at the routed spine, orthogonally
  to the \<open>refine_mode\<close> axis.
\<close>

definition ictx_sol_prog_per_origin ::
    "refine_mode \<Rightarrow> (vname \<Rightarrow> bool) \<Rightarrow> imp_prog
       \<Rightarrow> (pp \<times> unit) set \<times> (pp \<times> unit + gk \<Rightarrow> (int_dom exec_dg_st lifted, int_dom exec_dg_st lifted) dg_state)" where
  "ictx_sol_prog_per_origin mode gs p =
     TD_side_per_origin_Interp_solve (ictx_eqs_prog mode gs p) (cfg_exit (prog_cfg p), ())"

definition ictx_terminates_prog_per_origin :: "refine_mode \<Rightarrow> (vname \<Rightarrow> bool) \<Rightarrow> imp_prog \<Rightarrow> bool" where
  "ictx_terminates_prog_per_origin mode gs p =
     ictx_terminates_per_origin mode (resolved_st_q_is_bot_for (declared_global_vars p))
       gs (prog_table p) (prog_procs p)"

lemma ictx_terminates_prog_per_origin_via_solve_c:
  assumes "TD_side_per_origin_Interp_solve_c
             (ictx_eqs mode (resolved_st_q_is_bot_for (declared_global_vars p))
                gs (prog_table p) (prog_procs p))
             (cfg_exit (compile_prog (prog_table p) (prog_procs p)), ()) \<noteq> None"
  shows "ictx_terminates_prog_per_origin mode gs p"
  unfolding ictx_terminates_prog_per_origin_def
  using assms by (rule ictx_terminates_per_origin_via_solve_c)

definition analyse_int_ctx_result_per_origin_for ::
    "refine_mode \<Rightarrow> (vname \<Rightarrow> bool) \<Rightarrow> imp_prog \<Rightarrow> (unit, int_dom abs_state) analysis_result" where
  "analyse_int_ctx_result_per_origin_for mode gs p =
     Analysis_Result
       (fst (ictx_sol_prog_per_origin mode gs p))
       (\<lambda>v ctx. normalize_point gs
                  (canonicalize_lift (resolved_st_q_is_bot_for (declared_global_vars p))
                    (locals (snd (ictx_sol_prog_per_origin mode gs p) (Inl (v, ctx))))))"

declare analyse_int_ctx_result_per_origin_for_def [code del]

lemma analyse_int_ctx_result_per_origin_for_code [code]:
  "analyse_int_ctx_result_per_origin_for mode gs p =
     (let sol = ictx_sol_prog_per_origin mode gs p; gl = declared_global_vars p
      in Analysis_Result (fst sol)
           (\<lambda>v ctx. normalize_point gs
                      (canonicalize_lift (resolved_st_q_is_bot_for gl)
                        (locals (snd sol (Inl (v, ctx)))))))"
  unfolding analyse_int_ctx_result_per_origin_for_def Let_def by (rule refl)

definition ictx_sol_prog_warrow ::
    "refine_mode \<Rightarrow> (vname \<Rightarrow> bool) \<Rightarrow> imp_prog
       \<Rightarrow> (pp \<times> unit) set \<times> (pp \<times> unit + gk \<Rightarrow> (int_dom exec_dg_st lifted, int_dom exec_dg_st lifted) dg_state)" where
  "ictx_sol_prog_warrow mode gs p =
     TD_side_warrowing_apinis_Interp_solve (ictx_eqs_prog mode gs p) (cfg_exit (prog_cfg p), ())"

definition ictx_terminates_prog_warrow :: "refine_mode \<Rightarrow> (vname \<Rightarrow> bool) \<Rightarrow> imp_prog \<Rightarrow> bool" where
  "ictx_terminates_prog_warrow mode gs p =
     ictx_terminates_warrow mode (resolved_st_q_is_bot_for (declared_global_vars p))
       gs (prog_table p) (prog_procs p)"

lemma ictx_terminates_prog_warrow_via_solve_c:
  assumes "TD_side_warrowing_apinis_Interp_solve_c
             (ictx_eqs mode (resolved_st_q_is_bot_for (declared_global_vars p))
                gs (prog_table p) (prog_procs p))
             (cfg_exit (compile_prog (prog_table p) (prog_procs p)), ()) \<noteq> None"
  shows "ictx_terminates_prog_warrow mode gs p"
  unfolding ictx_terminates_prog_warrow_def
  using assms by (rule ictx_terminates_warrow_via_solve_c)

definition analyse_int_ctx_result_warrow_for ::
    "refine_mode \<Rightarrow> (vname \<Rightarrow> bool) \<Rightarrow> imp_prog \<Rightarrow> (unit, int_dom abs_state) analysis_result" where
  "analyse_int_ctx_result_warrow_for mode gs p =
     Analysis_Result
       (fst (ictx_sol_prog_warrow mode gs p))
       (\<lambda>v ctx. normalize_point gs
                  (canonicalize_lift (resolved_st_q_is_bot_for (declared_global_vars p))
                    (locals (snd (ictx_sol_prog_warrow mode gs p) (Inl (v, ctx))))))"

text \<open>\<^const>\<open>ctx_solved_for\<close> at this domain's warrowing solve, with \<^const>\<open>Global\<close>
  and \<^const>\<open>Seed\<close> handed to \<^const>\<open>seed_global_keys\<close> the way \<^const>\<open>routed_extra_g\<close>
  already takes them. The refinement mode is applied first, leaving the solve in the
  shape \<^const>\<open>ctx_solved_for\<close> takes.\<close>

definition analyse_int_ctx_solved_warrow_for ::
    "refine_mode \<Rightarrow> (vname \<Rightarrow> bool) \<Rightarrow> imp_prog
     \<Rightarrow> (unit, int_dom abs_state) analysis_result
          \<times> (String.literal \<times> int_dom abs_state lifted) list" where
  "analyse_int_ctx_solved_warrow_for mode =
     ctx_solved_for (ictx_sol_prog_warrow mode) (unit_seed_global_keys Global Seed)"

lemma fst_analyse_int_ctx_solved_warrow_for:
  "fst (analyse_int_ctx_solved_warrow_for mode gs p)
     = analyse_int_ctx_result_warrow_for mode gs p"
  by (simp add: analyse_int_ctx_solved_warrow_for_def fst_ctx_solved_for
      analyse_int_ctx_result_warrow_for_def Let_def)

declare analyse_int_ctx_result_warrow_for_def [code del]

lemma analyse_int_ctx_result_warrow_for_code [code]:
  "analyse_int_ctx_result_warrow_for mode gs p =
     (let sol = ictx_sol_prog_warrow mode gs p; gl = declared_global_vars p
      in Analysis_Result (fst sol)
           (\<lambda>v ctx. normalize_point gs
                      (canonicalize_lift (resolved_st_q_is_bot_for gl)
                        (locals (snd sol (Inl (v, ctx)))))))"
  unfolding analyse_int_ctx_result_warrow_for_def Let_def by (rule refl)

subsection \<open>Solved-result table: warrowing per origin\<close>

definition ictx_sol_prog_wpo ::
    "refine_mode \<Rightarrow> (vname \<Rightarrow> bool) \<Rightarrow> imp_prog
       \<Rightarrow> (pp \<times> unit) set \<times> (pp \<times> unit + gk \<Rightarrow> (int_dom exec_dg_st lifted, int_dom exec_dg_st lifted) dg_state)" where
  "ictx_sol_prog_wpo mode gs p =
     TD_side_warrowing_per_origin_Interp_solve (ictx_eqs_prog mode gs p) (cfg_exit (prog_cfg p), ())"

definition ictx_terminates_prog_wpo :: "refine_mode \<Rightarrow> (vname \<Rightarrow> bool) \<Rightarrow> imp_prog \<Rightarrow> bool" where
  "ictx_terminates_prog_wpo mode gs p =
     ictx_terminates_wpo mode (resolved_st_q_is_bot_for (declared_global_vars p))
       gs (prog_table p) (prog_procs p)"

lemma ictx_terminates_prog_wpo_via_solve_c:
  assumes "TD_side_warrowing_per_origin_Interp_solve_c
             (ictx_eqs mode (resolved_st_q_is_bot_for (declared_global_vars p))
                gs (prog_table p) (prog_procs p))
             (cfg_exit (compile_prog (prog_table p) (prog_procs p)), ()) \<noteq> None"
  shows "ictx_terminates_prog_wpo mode gs p"
  unfolding ictx_terminates_prog_wpo_def
  using assms by (rule ictx_terminates_wpo_via_solve_c)

definition analyse_int_ctx_result_wpo_for ::
    "refine_mode \<Rightarrow> (vname \<Rightarrow> bool) \<Rightarrow> imp_prog \<Rightarrow> (unit, int_dom abs_state) analysis_result" where
  "analyse_int_ctx_result_wpo_for mode gs p =
     Analysis_Result
       (fst (ictx_sol_prog_wpo mode gs p))
       (\<lambda>v ctx. normalize_point gs
                  (canonicalize_lift (resolved_st_q_is_bot_for (declared_global_vars p))
                    (locals (snd (ictx_sol_prog_wpo mode gs p) (Inl (v, ctx))))))"

declare analyse_int_ctx_result_wpo_for_def [code del]

lemma analyse_int_ctx_result_wpo_for_code [code]:
  "analyse_int_ctx_result_wpo_for mode gs p =
     (let sol = ictx_sol_prog_wpo mode gs p; gl = declared_global_vars p
      in Analysis_Result (fst sol)
           (\<lambda>v ctx. normalize_point gs
                      (canonicalize_lift (resolved_st_q_is_bot_for gl)
                        (locals (snd sol (Inl (v, ctx)))))))"
  unfolding analyse_int_ctx_result_wpo_for_def Let_def by (rule refl)

end
