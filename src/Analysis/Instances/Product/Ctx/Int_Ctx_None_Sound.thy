theory Int_Ctx_None_Sound
  imports
    "Voblint_Exec.Monovariant_Analysis_Result"
    "Voblint_Exec.Exec_DG_Bridge"
    "Voblint_Exec.Routed_Domain_Exec"
    "Voblint_Analysis.Int_Classify"
    "Voblint_Core.DG_Analysis_Adapter"
    "Voblint_Core.Routed_Context"
    "Voblint_Core.Routed_Context_Unit"
    "Voblint_Exec.Solver_Menu"
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
  \<open>is_bot_pred\<close>, \<open>gs\<close>) matches \<^const>\<open>analyse_int_dg_eqs_for\<close>'s own.
\<close>

definition ictx_spec ::
  "refine_mode \<Rightarrow> (int_dom exec_dg_st \<Rightarrow> bool) \<Rightarrow> (vname \<Rightarrow> bool)
     \<Rightarrow> (int_dom exec_dg_st lifted, int_dom exec_dg_st lifted) dg_spec"
where
  "ictx_spec mode is_bot_pred gs =
     base_dg_spec_st_for_lifted gs is_bot_pred (int_tf_st_for mode gs) (int_dom_enter_st_for mode gs)"

definition ictx_abs_spec :: "refine_mode \<Rightarrow> (vname \<Rightarrow> bool) \<Rightarrow> (int_dom abs_state lifted, int_dom abs_state lifted) dg_spec" where
  "ictx_abs_spec mode gs = base_dg_spec_for_lifted gs is_bot_state (int_tf_for mode gs)"

subsection \<open>The routed equation system and its executable solution\<close>

definition ictx_eqs ::
    "refine_mode \<Rightarrow> (int_dom exec_dg_st \<Rightarrow> bool) \<Rightarrow> (vname \<Rightarrow> bool) \<Rightarrow> proc_table \<Rightarrow> pname list \<Rightarrow> (pp \<times> unit, gk, (int_dom exec_dg_st lifted, int_dom exec_dg_st lifted) dg_state) eqsT" where
  "ictx_eqs mode is_bot_pred gs Pi ps =
     side_cfg_T_eff_keyed_seed_dg_buffered intra_predecessor_addr_list (\<lambda>_. Global)
       route_unit
       (routed_cmb_g_contribution (ictx_spec mode is_bot_pred gs) Global Seed
          (static_resolve (compile_prog Pi ps)))
       (routed_extra_g Seed Global)
       (compile_prog Pi ps) (ictx_spec mode is_bot_pred gs) Bot (Lifted cinit_int_dom_st) Bot"

definition ictx_sol ::
    "refine_mode \<Rightarrow> (int_dom exec_dg_st \<Rightarrow> bool) \<Rightarrow> (vname \<Rightarrow> bool) \<Rightarrow> proc_table \<Rightarrow> pname list \<Rightarrow> (pp \<times> unit) set \<times> (pp \<times> unit + gk \<Rightarrow> (int_dom exec_dg_st lifted, int_dom exec_dg_st lifted) dg_state)" where
  "ictx_sol mode is_bot_pred gs Pi ps =
     TD_side_always_join_Interp_solve (ictx_eqs mode is_bot_pred gs Pi ps)
       (cfg_exit (compile_prog Pi ps), ())"

definition ictx_terminates ::
    "refine_mode \<Rightarrow> (int_dom exec_dg_st \<Rightarrow> bool) \<Rightarrow> (vname \<Rightarrow> bool) \<Rightarrow> proc_table \<Rightarrow> pname list \<Rightarrow> bool" where
  "ictx_terminates mode is_bot_pred gs Pi ps =
     TD_side_always_join_Interp.solve_dom TYPE(gk) TYPE((int_dom exec_dg_st lifted, int_dom exec_dg_st lifted) dg_state)
       (ictx_eqs mode is_bot_pred gs Pi ps) (cfg_exit (compile_prog Pi ps), ())"

lemma ictx_terminates_via_solve_c:
  assumes "TD_side_always_join_Interp_solve_c (ictx_eqs mode is_bot_pred gs Pi ps)
             (cfg_exit (compile_prog Pi ps), ()) \<noteq> None"
  shows "ictx_terminates mode is_bot_pred gs Pi ps"
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
  "fun_of_resolved_st_q_for gs (int_dom_enter_st_for mode gs xs es s) =
     tf_enter (int_tf_for mode gs) xs es (fun_of_resolved_st_q_for gs s)"
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

context
  fixes gs :: "vname \<Rightarrow> bool" and is_bot_pred :: "int_dom exec_dg_st \<Rightarrow> bool" and mode :: refine_mode
  assumes exact: "\<And>s. is_bot_pred s = is_bot_state (fun_of_resolved_st_q_for gs s)"
begin

interpretation int_unit: routed_domain_exec
  gs is_bot_pred "int_tf_st_for mode gs" "int_dom_enter_st_for mode gs" "int_tf_for mode gs"
  Global Seed route_unit route_unit static_resolve static_resolve
  by unfold_locales
     (rule int_tf_st_for_commute, rule int_dom_enter_st_for_commute, rule exact, simp, simp,
      simp add: static_resolve_def)

lemmas int_pp_abs_gen = int_unit.pp_abs

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

text \<open>
  The abstract-carrier soundness interpretation the \<open>dg_base\<close> analogue needs, generic in
  \<open>mode\<close>: a three-way case split citing Int's own per-mode \<^locale>\<open>sound_dg_spec\<close>
  registration.  Independent of the update rule, so it sits outside the locale below and
  serves the contextual siblings too.
\<close>

lemma ictx_abs_spec_sound: "sound_dg_spec (ictx_abs_spec mode gs) gamma_dg_base gs"
proof (cases mode)
  case Refine_Never
  then show ?thesis
    unfolding ictx_abs_spec_def
    by (simp add: base_dg_spec_sound[OF int_never_is_sound_transfer_for is_bot_state_gamma_state_empty])
next
  case Refine_Once
  then show ?thesis
    unfolding ictx_abs_spec_def
    by (simp add: base_dg_spec_sound[OF int_once_is_sound_transfer_for is_bot_state_gamma_state_empty])
next
  case Refine_Fixpoint
  then show ?thesis
    unfolding ictx_abs_spec_def
    by (simp add: base_dg_spec_sound[OF int_fixpoint_is_sound_transfer_for is_bot_state_gamma_state_empty])
qed

locale ictx_solved =
  fixes ictx_sol :: "refine_mode \<Rightarrow> (int_dom exec_dg_st \<Rightarrow> bool) \<Rightarrow> (vname \<Rightarrow> bool) \<Rightarrow> proc_table
                  \<Rightarrow> pname list \<Rightarrow> (pp \<times> unit) set
                     \<times> (pp \<times> unit + gk \<Rightarrow> (int_dom exec_dg_st lifted, int_dom exec_dg_st lifted) dg_state)"
    and ictx_terminates :: "refine_mode \<Rightarrow> (int_dom exec_dg_st \<Rightarrow> bool) \<Rightarrow> (vname \<Rightarrow> bool) \<Rightarrow> proc_table
                         \<Rightarrow> pname list \<Rightarrow> bool"
  assumes pp_st:
    "ictx_terminates mode is_bot_pred gs Pi ps
       \<Longrightarrow> part_post_solution (ictx_eqs mode is_bot_pred gs Pi ps)
             (cfg_exit (compile_prog Pi ps), ())
             (snd (ictx_sol mode is_bot_pred gs Pi ps))
             (fst (ictx_sol mode is_bot_pred gs Pi ps))"
begin

theorem ictx_pp_abs:
  assumes solves: "ictx_terminates mode is_bot_pred gs Pi ps"
    and exact: "\<And>s. is_bot_pred s = is_bot_state (fun_of_resolved_st_q_for gs s)"
  shows
  "part_post_solution
     (side_cfg_T_eff_keyed_seed_dg intra_predecessor_addr_list (\<lambda>_. Global) route_unit
        (routed_cmb_g (ictx_abs_spec mode gs) Global Seed
           (static_resolve (compile_prog Pi ps)))
        (routed_extra_g Seed Global)
        (compile_prog Pi ps) (ictx_abs_spec mode gs)
        (map_lift (fun_of_resolved_st_q_for gs) (Bot::int_dom exec_dg_st lifted))
        (map_lift (fun_of_resolved_st_q_for gs) (Lifted cinit_int_dom_st))
        (map_lift (fun_of_resolved_st_q_for gs) (Bot::int_dom exec_dg_st lifted)))
     (cfg_exit (compile_prog Pi ps), ())
     (fun_of_dg_st_gen (map_lift (fun_of_resolved_st_q_for gs)) (map_lift (fun_of_resolved_st_q_for gs))
        \<circ> snd (ictx_sol mode is_bot_pred gs Pi ps))
     (fst (ictx_sol mode is_bot_pred gs Pi ps))"
proof -
  have pp_buf: "part_post_solution
       (side_cfg_T_eff_keyed_seed_dg_buffered intra_predecessor_addr_list (\<lambda>_. Global)
          route_unit
          (routed_cmb_g_contribution (ictx_spec mode is_bot_pred gs) Global Seed
             (static_resolve (compile_prog Pi ps)))
          (routed_extra_g Seed Global)
          (compile_prog Pi ps) (ictx_spec mode is_bot_pred gs)
          Bot (Lifted cinit_int_dom_st) Bot)
       (cfg_exit (compile_prog Pi ps), ())
       (snd (ictx_sol mode is_bot_pred gs Pi ps))
       (fst (ictx_sol mode is_bot_pred gs Pi ps))"
    using pp_st[OF solves] unfolding ictx_eqs_def by simp
  show ?thesis
    unfolding ictx_abs_spec_def
    using pp_buf unfolding ictx_spec_def by (rule int_pp_abs_gen[OF exact])
qed


definition ictx_sigma_abs_exec ::
    "refine_mode \<Rightarrow> (int_dom exec_dg_st \<Rightarrow> bool) \<Rightarrow> (vname \<Rightarrow> bool) \<Rightarrow> proc_table \<Rightarrow> pname list \<Rightarrow> pp \<times> unit + gk \<Rightarrow> (int_dom abs_state lifted, int_dom abs_state lifted) dg_state" where
  "ictx_sigma_abs_exec mode is_bot_pred gs Pi ps =
     fun_of_dg_st_gen (map_lift (fun_of_resolved_st_q_for gs)) (map_lift (fun_of_resolved_st_q_for gs))
       \<circ> snd (ictx_sol mode is_bot_pred gs Pi ps)"

definition ictx_sg_exec ::
    "refine_mode \<Rightarrow> (int_dom exec_dg_st \<Rightarrow> bool) \<Rightarrow> (vname \<Rightarrow> bool) \<Rightarrow> proc_table \<Rightarrow> pname list \<Rightarrow> pp \<times> unit + gk \<Rightarrow> int_dom abs_state lifted" where
  "ictx_sg_exec mode is_bot_pred gs Pi ps k =
     (case k of
        Inl (v, ctx) \<Rightarrow>
          (if (v, ctx) \<in> fst (ictx_sol mode is_bot_pred gs Pi ps)
           then locals (ictx_sigma_abs_exec mode is_bot_pred gs Pi ps (Inl (v, ctx)))
           else Bot)
      | Inr _ \<Rightarrow> Bot)"

text \<open>
  The abstract-carrier soundness interpretation, generic in \<open>mode\<close>: a three-way
  case split citing Int's own per-mode transfer-soundness facts
  (\<open>int_never_is_sound_transfer_for\<close> and its siblings), one per branch.
\<close>


context
  fixes mode :: refine_mode and is_bot_pred :: "int_dom exec_dg_st \<Rightarrow> bool" and gs :: "vname \<Rightarrow> bool"
    and Pi :: proc_table and ps :: "pname list"
  assumes solves: "ictx_terminates mode is_bot_pred gs Pi ps"
    and exact: "\<And>s. is_bot_pred s = is_bot_state (fun_of_resolved_st_q_for gs s)"
    and entry_cov: "(cfg_entry (compile_prog Pi ps), ()) \<in> fst (ictx_sol mode is_bot_pred gs Pi ps)"
    and fwd_ok: "\<And>u a v ctx. (u, ctx) \<in> fst (ictx_sol mode is_bot_pred gs Pi ps)
                   \<Longrightarrow> (u, a, v) \<in> intra (compile_prog Pi ps)
                   \<Longrightarrow> (v, ctx) \<in> fst (ictx_sol mode is_bot_pred gs Pi ps)"
    and call_fwd_ok: "\<And>u ctx dst pars args p cont.
        (u, ctx) \<in> fst (ictx_sol mode is_bot_pred gs Pi ps)
        \<Longrightarrow> (u, CallEdge dst pars args, FunctionEntry p, cont) \<in> calls (compile_prog Pi ps)
        \<Longrightarrow> (FunctionEntry p, ()) \<in> fst (ictx_sol mode is_bot_pred gs Pi ps)"
    and comb_fwd_ok: "\<And>cl c1 dst pars args p cont.
        (cl, c1) \<in> fst (ictx_sol mode is_bot_pred gs Pi ps)
        \<Longrightarrow> (cl, CallEdge dst pars args, FunctionEntry p, cont) \<in> calls (compile_prog Pi ps)
        \<Longrightarrow> (cont, c1) \<in> fst (ictx_sol mode is_bot_pred gs Pi ps)"
begin

subsection \<open>The semantic solution projection\<close>

definition ictx_sigma_abs :: "pp \<times> unit + gk \<Rightarrow> (int_dom abs_state lifted, int_dom abs_state lifted) dg_state" where
  "ictx_sigma_abs = ictx_sigma_abs_exec mode is_bot_pred gs Pi ps"

definition ictx_sg :: "pp \<times> unit + gk \<Rightarrow> int_dom abs_state lifted" where
  "ictx_sg = ictx_sg_exec mode is_bot_pred gs Pi ps"

lemma ictx_fin: "finite (intra (compile_prog Pi ps))"
  using compile_prog_finite by blast

lemma ictx_finC: "finite (calls (compile_prog Pi ps))"
  using compile_prog_finite by blast

lemma ictx_sg_covered:
  "(v, ctx) \<in> fst (ictx_sol mode is_bot_pred gs Pi ps)
   \<Longrightarrow> ictx_sg (Inl (v, ctx)) = locals (ictx_sigma_abs (Inl (v, ctx)))"
  by (simp add: ictx_sg_def ictx_sg_exec_def ictx_sigma_abs_def ictx_sigma_abs_exec_def)

lemma ictx_sg_uncovered_empty:
  "(v, ctx) \<notin> fst (ictx_sol mode is_bot_pred gs Pi ps)
     \<Longrightarrow> gamma_state_lift (ictx_sg (Inl (v, ctx))) = {}"
  by (simp add: ictx_sg_def ictx_sg_exec_def)

subsection \<open>Instantiating the generic DG-native activation discharge\<close>

interpretation ictx_dg_base: sound_dg_spec "ictx_abs_spec mode gs" gamma_dg_base gs
  by (rule ictx_abs_spec_sound)

interpretation ictx_dg: dg_ctx_activation_base "ictx_abs_spec mode gs" gamma_dg_base gs
    "compile_prog Pi ps" Global route_unit
    "routed_cmb_g (ictx_abs_spec mode gs) Global Seed
       (static_resolve (compile_prog Pi ps))"
    "routed_extra_g Seed Global"
    "map_lift (fun_of_resolved_st_q_for gs) (Bot::int_dom exec_dg_st lifted)"
    "map_lift (fun_of_resolved_st_q_for gs) (Lifted cinit_int_dom_st)"
    "map_lift (fun_of_resolved_st_q_for gs) (Bot::int_dom exec_dg_st lifted)"
    ictx_sigma_abs "fst (ictx_sol mode is_bot_pred gs Pi ps)"
    "(cfg_exit (compile_prog Pi ps), ())" ictx_sg gamma_state_lift
proof unfold_locales
  show "finite (intra (compile_prog Pi ps))" by (rule ictx_fin)
next
  show "part_post_solution
          (side_cfg_T_eff_keyed_seed_dg intra_predecessor_addr_list (\<lambda>_. Global) route_unit
             (routed_cmb_g (ictx_abs_spec mode gs) Global Seed
                (static_resolve (compile_prog Pi ps)))
             (routed_extra_g Seed Global)
             (compile_prog Pi ps) (ictx_abs_spec mode gs)
             (map_lift (fun_of_resolved_st_q_for gs) (Bot::int_dom exec_dg_st lifted))
             (map_lift (fun_of_resolved_st_q_for gs) (Lifted cinit_int_dom_st))
             (map_lift (fun_of_resolved_st_q_for gs) (Bot::int_dom exec_dg_st lifted)))
          (cfg_exit (compile_prog Pi ps), ()) ictx_sigma_abs
          (fst (ictx_sol mode is_bot_pred gs Pi ps))"
    unfolding ictx_sigma_abs_def ictx_sigma_abs_exec_def
    by (rule ictx_pp_abs[OF solves exact])
next
  fix v ctx assume "(v, ctx) \<in> fst (ictx_sol mode is_bot_pred gs Pi ps)"
  thus "gamma_state_lift (ictx_sg (Inl (v, ctx)))
          = gamma_dg_base (locals (ictx_sigma_abs (Inl (v, ctx)))) (globs (ictx_sigma_abs (Inr Global)))"
    by (simp add: ictx_sg_covered gamma_dg_base_def)
next
  fix v ctx assume "(v, ctx) \<notin> fst (ictx_sol mode is_bot_pred gs Pi ps)"
  thus "gamma_state_lift (ictx_sg (Inl (v, ctx))) = {}"
    by (rule ictx_sg_uncovered_empty)
next
  fix u a v ctx assume "(u, ctx) \<in> fst (ictx_sol mode is_bot_pred gs Pi ps)"
    "(u, a, v) \<in> intra (compile_prog Pi ps)"
  thus "(v, ctx) \<in> fst (ictx_sol mode is_bot_pred gs Pi ps)" by (rule fwd_ok)
qed

subsection \<open>The routed interpretation and its CALL/COMB corollaries\<close>

interpretation ictx_routed: unit_routed_context "ictx_abs_spec mode gs" gamma_dg_base gs
    "compile_prog Pi ps" Global
    "map_lift (fun_of_resolved_st_q_for gs) (Bot::int_dom exec_dg_st lifted)"
    "map_lift (fun_of_resolved_st_q_for gs) (Lifted cinit_int_dom_st)"
    "map_lift (fun_of_resolved_st_q_for gs) (Bot::int_dom exec_dg_st lifted)"
    ictx_sigma_abs "fst (ictx_sol mode is_bot_pred gs Pi ps)"
    "(cfg_exit (compile_prog Pi ps), ())" ictx_sg
    Seed gamma_state_lift
proof (unfold_locales, goal_cases FinC SeedKey CallFwd CombFwd EnterAgree)
  case FinC show ?case by (rule ictx_finC)
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
      ce': "(cl, CallEdge dst' pars' args', FunctionEntry p', cont') \<in> calls (compile_prog Pi ps)"
    and es_eq: "es = call_enter gs (CallEdge dst' pars' args') s"
    using ces unfolding call_enter_store_def by blast
  have "CallEdge dst' pars' args' = CallEdge dst pars args"
    using compile_prog_calls_source_unique[OF ce' ce] by simp
  thus ?case using es_eq by simp
qed

lemma ictx_sg_seed:
  assumes "(u, CallEdge dst xs es, FunctionEntry p, cont) \<in> calls (compile_prog Pi ps)"
    and "s \<in> gamma_state_lift (ictx_sg (Inl (u, ctx)))"
  shows "call_enter gs (CallEdge dst xs es) s
           \<in> gamma_state_lift (ictx_sg (Inl (FunctionEntry p, ())))"
  using ictx_routed.routed_context_call[OF assms] by simp

lemma ictx_sg_comb:
  assumes "(cl, CallEdge dst pars args, FunctionEntry p, v) \<in> calls (compile_prog Pi ps)"
    and "s \<in> gamma_state_lift (ictx_sg (Inl (cl, c1)))"
    and "t \<in> gamma_state_lift (ictx_sg (Inl (FunctionResult p, ())))"
    and "call_enter_store gs (compile_prog Pi ps) cl s es"
  shows "combine_collect gs dst s t \<in> gamma_state_lift (ictx_sg (Inl (v, c1)))"
  using ictx_routed.routed_context_comb[OF assms(1,2) _ assms(4)] assms(3) by simp

subsection \<open>Activation-indexed collecting soundness\<close>

lemma ictx_cinit_le_cinit_int_dom_st:
  "cinit_stores gs \<subseteq> gamma_state_lift (map_lift (fun_of_resolved_st_q_for gs) (Lifted cinit_int_dom_st))"
  by (auto simp: cinit_stores_def gamma_state_def fun_of_resolved_st_q_for_def fun_of_st_cinit_int_dom_st_for
                 gamma_int_dom_top)

lemma ictx_locals_ge_s0d:
  "map_lift (fun_of_resolved_st_q_for gs) (Lifted cinit_int_dom_st)
     \<le> locals (ictx_sigma_abs (Inl (cfg_entry (compile_prog Pi ps), ())))"
proof -
  have "map_lift (fun_of_resolved_st_q_for gs) (Lifted cinit_int_dom_st)
      \<le> locals (eq ictx_dg.Gen (cfg_entry (compile_prog Pi ps), ()) ictx_sigma_abs)"
    by (simp add: eq_side_cfg_T_eff_keyed_seed_dg)
       (rule order_trans[OF _ side_acc_dg_ge_acc], simp add: le_supI2)
  also have "\<dots> \<le> locals (ictx_sigma_abs (Inl (cfg_entry (compile_prog Pi ps), ())))"
    using ictx_dg.pp_eq_bound[OF entry_cov] by (simp add: less_eq_dg_state_def)
  finally show ?thesis .
qed

theorem ictx_activation_collect_sound:
  "activation_collect gs enterc_unit () (compile_prog Pi ps) (cinit_stores gs) v ctx
     \<subseteq> gamma_state_lift (ictx_sg (Inl (v, ctx)))"
proof (rule activation_collect_sound_gen[where sg = ictx_sg and gammaM = gamma_state_lift
        and enterc = "enterc_unit"
        and initial_ctx = "()" and S = "cinit_stores gs" and g = "compile_prog Pi ps" and gs = gs])
  \<comment> \<open>ENTRY_G\<close>
  fix s assume "s \<in> cinit_stores gs"
  hence "s \<in> gamma_state_lift (map_lift (fun_of_resolved_st_q_for gs) (Lifted cinit_int_dom_st))"
    using ictx_cinit_le_cinit_int_dom_st by blast
  also have "gamma_state_lift (map_lift (fun_of_resolved_st_q_for gs) (Lifted cinit_int_dom_st))
        = gamma_dg_base (map_lift (fun_of_resolved_st_q_for gs) (Lifted cinit_int_dom_st))
            (map_lift (fun_of_resolved_st_q_for gs) (Bot::int_dom exec_dg_st lifted))"
    by (simp add: gamma_dg_base_def)
  also have "\<dots> \<subseteq> gamma_dg_base (locals (ictx_sigma_abs (Inl (cfg_entry (compile_prog Pi ps), ()))))
                   (globs (ictx_sigma_abs (Inr Global)))"
    by (rule gamma_dg_base_mono[OF ictx_locals_ge_s0d ictx_dg.pp_entry_s0g_bound[OF entry_cov]])
  also have "\<dots> = gamma_state_lift (ictx_sg (Inl (cfg_entry (compile_prog Pi ps), ())))"
    unfolding ictx_sg_covered[OF entry_cov] gamma_dg_base_def by (rule refl)
  finally show "s \<in> gamma_state_lift (ictx_sg (Inl (cfg_entry (compile_prog Pi ps), ())))" .
next
  \<comment> \<open>EDGE\<close>
  show "\<And>u a v c s s'. (u, a, v) \<in> intra (compile_prog Pi ps)
        \<Longrightarrow> s \<in> gamma_state_lift (ictx_sg (Inl (u, c))) \<Longrightarrow> s' \<in> edge_step a s
        \<Longrightarrow> s' \<in> gamma_state_lift (ictx_sg (Inl (v, c)))"
    by (rule ictx_dg.dg_ctx_act_edge)
next
  \<comment> \<open>CALL\<close>
  fix u dst pars args p cont c s
  assume ce: "(u, CallEdge dst pars args, FunctionEntry p, cont) \<in> calls (compile_prog Pi ps)"
    and sm: "s \<in> gamma_state_lift (ictx_sg (Inl (u, c)))"
  show "call_enter gs (CallEdge dst pars args) s
          \<in> gamma_state_lift
              (ictx_sg (Inl (FunctionEntry p, enterc_unit u c (call_enter gs (CallEdge dst pars args) s))))"
    using ictx_sg_seed[OF ce sm] by simp
next
  \<comment> \<open>COMB\<close>
  fix cl dst pars args p cont c1 s t es
  assume ce: "(cl, CallEdge dst pars args, FunctionEntry p, cont) \<in> calls (compile_prog Pi ps)"
    and sm: "s \<in> gamma_state_lift (ictx_sg (Inl (cl, c1)))"
    and tm: "t \<in> gamma_state_lift (ictx_sg (Inl (FunctionResult p, enterc_unit cl c1 es)))"
    and ces: "call_enter_store gs (compile_prog Pi ps) cl s es"
  show "combine_collect gs dst s t \<in> gamma_state_lift (ictx_sg (Inl (cont, c1)))"
    using tm ictx_sg_comb[OF ce sm _ ces] by simp
qed

subsection \<open>The public result/report table, via the generic adapter locale\<close>

text \<open>
  \<^locale>\<open>dg_analysis_adapter\<close> (\<^theory>\<open>Voblint_Core.DG_Analysis_Adapter\<close>) extends
  \<^locale>\<open>routed_context_hetero\<close> with one classifier obligation. Its own parameter
  list matches \<open>ictx_routed\<close>'s \<^locale>\<open>unit_routed_context\<close> instantiation above
  (same \<open>S\<close>/\<open>g\<close>/\<open>gk0\<close>/\<open>route\<close>/\<open>bot0\<close>/\<open>s0d\<close>/\<open>s0g\<close>/\<open>sigma\<close>/\<open>vars\<close>/\<open>x0\<close>/\<open>sg\<close>/\<open>seed_key\<close>),
  plus \<open>enterc\<close> (pinned at \<^const>\<open>enterc_unit\<close>, matching \<open>ictx_routed\<close>'s own sublocale)
  and \<open>classify\<close> (\<^const>\<open>int_classify_check\<close>). \<^locale>\<open>unit_routed_context\<close> only proves
  the weaker \<^locale>\<open>routed_context_base_hetero\<close> (generic in \<open>gammaDG\<close>/\<open>gammaM\<close>), not
  \<^locale>\<open>routed_context_hetero\<close> itself (fixed at \<^const>\<open>gamma_dg_base\<close>/
  \<^const>\<open>gamma_state_lift\<close>) even though the two predicates have the same assumption
  list once specialized: Isabelle does not identify the two locale predicates for
  free, so this second interpretation repeats \<open>ictx_routed\<close>'s five non-trivial
  obligations once more (\<open>route_enterc_agree\<close> collapses to plain \<open>simp\<close> on
  \<^const>\<open>route_unit\<close>/\<^const>\<open>enterc_unit\<close>, both already \<open>[simp]\<close>), plus the two
  classifier obligations \<open>int_classify_check_proved\<close>/
  \<open>int_classify_check_refuted\<close> (\<^theory>\<open>Voblint_Analysis.Int_Classify\<close>) discharge
  directly.
\<close>

interpretation ictx_adapter: dg_analysis_adapter
  where S = "ictx_abs_spec mode gs" and gs = gs
    and g = "compile_prog Pi ps" and gk0 = Global and route = route_unit
    and bot0 = "map_lift (fun_of_resolved_st_q_for gs) (Bot::int_dom exec_dg_st lifted)"
    and s0d = "map_lift (fun_of_resolved_st_q_for gs) (Lifted cinit_int_dom_st)"
    and s0g = "map_lift (fun_of_resolved_st_q_for gs) (Bot::int_dom exec_dg_st lifted)"
    and sigma = ictx_sigma_abs and vars = "fst (ictx_sol mode is_bot_pred gs Pi ps)"
    and x0 = "(cfg_exit (compile_prog Pi ps), ())" and sg = ictx_sg
    and seed_key = Seed and enterc = enterc_unit and gammaDG = gamma_dg_base
    and gammaM = gamma_state_lift and rd = id and classify = int_classify_check
proof (unfold_locales, goal_cases
    FinC SeedKey ResolveSound RouteEnterAgree CallFwd CombFwd CallEnterStoreAgree
    GammaRd ClassifyProved ClassifyRefuted)
  case FinC show ?case by (rule ictx_finC)
next
  case (SeedKey p ctx) show ?case by simp
next
  case (ResolveSound u ctx dst pars args p cont s)
  thus ?case by (simp add: static_resolve_iff[OF ictx_finC])
next
  case (RouteEnterAgree u ctx dst pars args p cont s)
  show ?case by simp
next
  case (CallFwd u ctx dst pars args p cont)
  show ?case
    using CallFwd(1,2) call_fwd_ok unfolding route_unit_def by blast
next
  case (CombFwd cl c1 dst pars args p cont)
  show ?case using CombFwd(1,2) comb_fwd_ok by blast
next
  case (CallEnterStoreAgree cl s es dst pars args p cont)
  note ces = CallEnterStoreAgree(1) and ce = CallEnterStoreAgree(2)
  obtain dst' pars' args' p' cont' where
      ce': "(cl, CallEdge dst' pars' args', FunctionEntry p', cont') \<in> calls (compile_prog Pi ps)"
    and es_eq: "es = call_enter gs (CallEdge dst' pars' args') s"
    using ces unfolding call_enter_store_def by blast
  have "CallEdge dst' pars' args' = CallEdge dst pars args"
    using compile_prog_calls_source_unique[OF ce' ce] by simp
  thus ?case using es_eq by simp
next
  case (GammaRd d g')
  show ?case by (simp add: gamma_dg_base_def)
next
  case (ClassifyProved c d s)
  show ?case using ClassifyProved(1,2) by (rule int_classify_check_proved)
next
  case (ClassifyRefuted c d s)
  show ?case using ClassifyRefuted(1,2) by (rule int_classify_check_refuted)
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

lemma ictx_analyse_result_eq:
  "lookup_context ictx_adapter.analyse_result v ctx =
     (if (v, ctx) \<in> fst (ictx_sol mode is_bot_pred gs Pi ps)
      then normalize_point gs
             (canonicalize_lift is_bot_pred (locals (snd (ictx_sol mode is_bot_pred gs Pi ps) (Inl (v, ctx)))))
      else Unreachable)"
  unfolding ictx_adapter.lookup_context_analyse_result
  apply (simp only: ictx_sigma_abs_def ictx_sigma_abs_exec_def o_apply fun_of_dg_st_gen_simps(1))
  by (cases "locals (snd (ictx_sol mode is_bot_pred gs Pi ps) (Inl (v, ctx)))")
     (simp_all add: exact normalize_lift_def)

end

end

section \<open>The four update-rule instances\<close>

text \<open>Each rule's entire obligation is \<open>partial_post_solution\<close>, which
  \<^locale>\<open>TD_side_upd_rule\<close> proves once for every update rule.\<close>

lemma ictx_join_pp_st:
  "ictx_terminates mode is_bot_pred gs Pi ps
     \<Longrightarrow> part_post_solution (ictx_eqs mode is_bot_pred gs Pi ps)
           (cfg_exit (compile_prog Pi ps), ())
           (snd (ictx_sol mode is_bot_pred gs Pi ps))
           (fst (ictx_sol mode is_bot_pred gs Pi ps))"
  unfolding ictx_sol_def ictx_terminates_def
  by (rule TD_side_always_join_Interp.partial_post_solution[OF _ surjective_pairing])

global_interpretation ictx_join: ictx_solved ictx_sol ictx_terminates
  defines ictx_sigma_abs_exec = ictx_join.ictx_sigma_abs_exec
      and ictx_sg_exec = ictx_join.ictx_sg_exec
      and ictx_sigma_abs = ictx_join.ictx_sigma_abs
      and ictx_sg = ictx_join.ictx_sg
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
  "ictx_sol_per_origin mode is_bot_pred gs Pi ps =
     TD_side_per_origin_Interp_solve (ictx_eqs mode is_bot_pred gs Pi ps)
       (cfg_exit (compile_prog Pi ps), ())"

definition ictx_terminates_per_origin ::
    "refine_mode \<Rightarrow> (int_dom exec_dg_st \<Rightarrow> bool) \<Rightarrow> (vname \<Rightarrow> bool) \<Rightarrow> proc_table \<Rightarrow> pname list \<Rightarrow> bool" where
  "ictx_terminates_per_origin mode is_bot_pred gs Pi ps =
     TD_side_per_origin_Interp.solve_dom TYPE(gk) TYPE((int_dom exec_dg_st lifted, int_dom exec_dg_st lifted) dg_state)
       (ictx_eqs mode is_bot_pred gs Pi ps) (cfg_exit (compile_prog Pi ps), ())"

lemma ictx_terminates_per_origin_via_solve_c:
  assumes "TD_side_per_origin_Interp_solve_c (ictx_eqs mode is_bot_pred gs Pi ps)
             (cfg_exit (compile_prog Pi ps), ()) \<noteq> None"
  shows "ictx_terminates_per_origin mode is_bot_pred gs Pi ps"
  unfolding ictx_terminates_per_origin_def
  by (rule TD_side_per_origin_Interp.solve_dom_of_solve_c[OF assms])

subsection \<open>The PerOrigin instance\<close>

lemma ictx_per_origin_pp_st:
  "ictx_terminates_per_origin mode is_bot_pred gs Pi ps
     \<Longrightarrow> part_post_solution (ictx_eqs mode is_bot_pred gs Pi ps)
           (cfg_exit (compile_prog Pi ps), ())
           (snd (ictx_sol_per_origin mode is_bot_pred gs Pi ps))
           (fst (ictx_sol_per_origin mode is_bot_pred gs Pi ps))"
  unfolding ictx_sol_per_origin_def ictx_terminates_per_origin_def
  by (rule TD_side_per_origin_Interp.partial_post_solution[OF _ surjective_pairing])

global_interpretation ictx_po: ictx_solved ictx_sol_per_origin ictx_terminates_per_origin
  defines ictx_sigma_abs_exec_per_origin = ictx_po.ictx_sigma_abs_exec
      and ictx_sg_exec_per_origin = ictx_po.ictx_sg_exec
      and ictx_sigma_abs_per_origin = ictx_po.ictx_sigma_abs
      and ictx_sg_per_origin = ictx_po.ictx_sg
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
  "ictx_sol_warrow mode is_bot_pred gs Pi ps =
     TD_side_warrowing_apinis_Interp_solve (ictx_eqs mode is_bot_pred gs Pi ps)
       (cfg_exit (compile_prog Pi ps), ())"

definition ictx_terminates_warrow ::
    "refine_mode \<Rightarrow> (int_dom exec_dg_st \<Rightarrow> bool) \<Rightarrow> (vname \<Rightarrow> bool) \<Rightarrow> proc_table \<Rightarrow> pname list \<Rightarrow> bool" where
  "ictx_terminates_warrow mode is_bot_pred gs Pi ps =
     TD_side_warrowing_apinis_Interp.solve_dom TYPE(gk) TYPE((int_dom exec_dg_st lifted, int_dom exec_dg_st lifted) dg_state)
       (ictx_eqs mode is_bot_pred gs Pi ps) (cfg_exit (compile_prog Pi ps), ())"

lemma ictx_terminates_warrow_via_solve_c:
  assumes "TD_side_warrowing_apinis_Interp_solve_c (ictx_eqs mode is_bot_pred gs Pi ps)
             (cfg_exit (compile_prog Pi ps), ()) \<noteq> None"
  shows "ictx_terminates_warrow mode is_bot_pred gs Pi ps"
  unfolding ictx_terminates_warrow_def
  by (rule TD_side_warrowing_apinis_Interp.solve_dom_of_solve_c[OF assms])

subsection \<open>The Apinis warrowing instance\<close>

lemma ictx_warrow_pp_st:
  "ictx_terminates_warrow mode is_bot_pred gs Pi ps
     \<Longrightarrow> part_post_solution (ictx_eqs mode is_bot_pred gs Pi ps)
           (cfg_exit (compile_prog Pi ps), ())
           (snd (ictx_sol_warrow mode is_bot_pred gs Pi ps))
           (fst (ictx_sol_warrow mode is_bot_pred gs Pi ps))"
  unfolding ictx_sol_warrow_def ictx_terminates_warrow_def
  by (rule TD_side_warrowing_apinis_Interp.partial_post_solution[OF _ surjective_pairing])

global_interpretation ictx_wa: ictx_solved ictx_sol_warrow ictx_terminates_warrow
  defines ictx_sigma_abs_exec_warrow = ictx_wa.ictx_sigma_abs_exec
      and ictx_sg_exec_warrow = ictx_wa.ictx_sg_exec
      and ictx_sigma_abs_warrow = ictx_wa.ictx_sigma_abs
      and ictx_sg_warrow = ictx_wa.ictx_sg
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
  "ictx_sol_wpo mode is_bot_pred gs Pi ps =
     TD_side_warrowing_per_origin_Interp_solve (ictx_eqs mode is_bot_pred gs Pi ps)
       (cfg_exit (compile_prog Pi ps), ())"

definition ictx_terminates_wpo ::
    "refine_mode \<Rightarrow> (int_dom exec_dg_st \<Rightarrow> bool) \<Rightarrow> (vname \<Rightarrow> bool) \<Rightarrow> proc_table \<Rightarrow> pname list \<Rightarrow> bool" where
  "ictx_terminates_wpo mode is_bot_pred gs Pi ps =
     TD_side_warrowing_per_origin_Interp.solve_dom TYPE(gk)
       TYPE((int_dom exec_dg_st lifted, int_dom exec_dg_st lifted) dg_state)
       (ictx_eqs mode is_bot_pred gs Pi ps) (cfg_exit (compile_prog Pi ps), ())"

lemma ictx_terminates_wpo_via_solve_c:
  assumes "TD_side_warrowing_per_origin_Interp_solve_c (ictx_eqs mode is_bot_pred gs Pi ps)
             (cfg_exit (compile_prog Pi ps), ()) \<noteq> None"
  shows "ictx_terminates_wpo mode is_bot_pred gs Pi ps"
  unfolding ictx_terminates_wpo_def
  by (rule TD_side_warrowing_per_origin_Interp.solve_dom_of_solve_c[OF assms])

lemma ictx_wpo_pp_st:
  "ictx_terminates_wpo mode is_bot_pred gs Pi ps
     \<Longrightarrow> part_post_solution (ictx_eqs mode is_bot_pred gs Pi ps)
           (cfg_exit (compile_prog Pi ps), ())
           (snd (ictx_sol_wpo mode is_bot_pred gs Pi ps))
           (fst (ictx_sol_wpo mode is_bot_pred gs Pi ps))"
  unfolding ictx_sol_wpo_def ictx_terminates_wpo_def
  by (rule TD_side_warrowing_per_origin_Interp.partial_post_solution[OF _ surjective_pairing])

global_interpretation ictx_wpo: ictx_solved ictx_sol_wpo ictx_terminates_wpo
  defines ictx_sigma_abs_exec_wpo = ictx_wpo.ictx_sigma_abs_exec
      and ictx_sg_exec_wpo = ictx_wpo.ictx_sg_exec
      and ictx_sigma_abs_wpo = ictx_wpo.ictx_sigma_abs
      and ictx_sg_wpo = ictx_wpo.ictx_sg
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
          \<times> (String.literal \<times> int_dom abs_state point_state) list" where
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
