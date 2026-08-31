theory Int_Ctx_Call_String_Sound
  imports
    "Voblint_Analysis.Int_Ctx_None_Sound"
    "Voblint_Analysis.Int_Classify"
    "Voblint_Core.Call_String_Context"
    Call_String_Routed_Context
begin

section \<open>Int at the routed spine, instantiated at the call-string context\<close>

text \<open>
  The call-string sibling of \<^theory>\<open>Voblint_Analysis.Int_Ctx_None_Sound\<close>'s own
  routed-unit-context instance, mirroring \<open>Sign_Ctx_Call_String_Sound\<close>'s own
  derivation for a second domain: same \<^const>\<open>ictx_spec\<close>/\<^const>\<open>ictx_abs_spec\<close>
  D/G specification and the same domain-commute facts Int's own routed-unit
  instance already interprets (\<^locale>\<open>routed_dg_domain_exec\<close>,
  \<^theory>\<open>Voblint_Exec.DG_Base_Exec\<close>) -- nothing here re-derives them, and the
  \<^typ>\<open>refine_mode\<close> parameter Int threads throughout stays a genuine fixed
  argument exactly as it already is at Int's own \<^const>\<open>ictx_spec\<close>. Only the
  routing policy changes, from \<^const>\<open>route_unit\<close> to
  \<^const>\<open>Call_String_Context.cs_route\<close> at a runtime bound \<open>k\<close>, and the routed-context
  locale interpreted changes from \<^locale>\<open>unit_routed_context\<close> to
  \<^locale>\<open>call_string_routed_context\<close> (\<^theory>\<open>Voblint_Analysis.Call_String_Routed_Context\<close>),
  exactly as Sign's own call-string derivation already uses.

  This is the mission's stretch-goal acceptance test at a third domain: a second
  context for Int, exposed from the existing generic routed-domain interpretation
  and the existing generic call-string context locale, with no new Int-domain
  mathematics.
\<close>

subsection \<open>The routed equation system and its executable solution\<close>

definition ics_eqs ::
    "nat \<Rightarrow> refine_mode \<Rightarrow> (vname \<Rightarrow> bool) \<Rightarrow> (int_dom exec_dg_st \<Rightarrow> bool) \<Rightarrow> proc_table \<Rightarrow> pname list
       \<Rightarrow> (pp \<times> call_string, call_string_gk, (int_dom exec_dg_st lifted, int_dom exec_dg_st lifted) dg_state) eqsT" where
  "ics_eqs k mode gs empty_pred Pi ps =
     side_cfg_T_eff_keyed_seed_dg_buffered intra_predecessor_addr_list (\<lambda>_. Call_String_Context.Global)
       (cs_route k)
       (routed_cmb_g_contribution (ictx_spec mode empty_pred gs)
          Call_String_Context.Global Call_String_Context.Seed
          (static_resolve (compile_prog Pi ps)))
       (routed_extra_g Call_String_Context.Seed Call_String_Context.Global)
       (compile_prog Pi ps) (ictx_spec mode empty_pred gs) Bot (Lifted cinit_int_dom_st) Bot"

definition ics_sol ::
    "nat \<Rightarrow> refine_mode \<Rightarrow> (vname \<Rightarrow> bool) \<Rightarrow> (int_dom exec_dg_st \<Rightarrow> bool) \<Rightarrow> proc_table \<Rightarrow> pname list
       \<Rightarrow> (pp \<times> call_string) set \<times> (pp \<times> call_string + call_string_gk \<Rightarrow> (int_dom exec_dg_st lifted, int_dom exec_dg_st lifted) dg_state)" where
  "ics_sol k mode gs empty_pred Pi ps =
     TD_side_always_join_Interp_solve (ics_eqs k mode gs empty_pred Pi ps)
       (cfg_exit (compile_prog Pi ps), [])"

definition ics_terminates ::
    "nat \<Rightarrow> refine_mode \<Rightarrow> (vname \<Rightarrow> bool) \<Rightarrow> (int_dom exec_dg_st \<Rightarrow> bool) \<Rightarrow> proc_table \<Rightarrow> pname list
       \<Rightarrow> bool" where
  "ics_terminates k mode gs empty_pred Pi ps =
     TD_side_always_join_Interp.solve_dom TYPE(call_string_gk) TYPE((int_dom exec_dg_st lifted, int_dom exec_dg_st lifted) dg_state)
       (ics_eqs k mode gs empty_pred Pi ps) (cfg_exit (compile_prog Pi ps), [])"

lemma ics_terminates_via_solve_c:
  assumes "TD_side_always_join_Interp_solve_c (ics_eqs k mode gs empty_pred Pi ps)
             (cfg_exit (compile_prog Pi ps), []) \<noteq> None"
  shows "ics_terminates k mode gs empty_pred Pi ps"
  unfolding ics_terminates_def
  by (rule TD_side_always_join_Interp.solve_dom_of_solve_c[OF assms])

text \<open>
  The same routed system under Apinis warrowing, Int's production default at
  \<open>Ctx_None\<close>. Always-join has no termination guarantee on the interval component:
  a call string that collapses a recursion's contexts feeds the callee entry its
  own decremented formals, and a join-only solve descends that chain forever.
  \<^locale>\<open>TD_side_upd_rule\<close>'s \<open>solve_dom\<close>/\<open>partial_post_solution\<close> are generic over
  the update rule, so the certificate below is the join one with the solver
  swapped, exactly as \<^theory>\<open>Voblint_Analysis.Int_Ctx_None_Sound\<close> does.
\<close>

definition ics_sol_warrow ::
    "nat \<Rightarrow> refine_mode \<Rightarrow> (vname \<Rightarrow> bool) \<Rightarrow> (int_dom exec_dg_st \<Rightarrow> bool) \<Rightarrow> proc_table \<Rightarrow> pname list
       \<Rightarrow> (pp \<times> call_string) set \<times> (pp \<times> call_string + call_string_gk \<Rightarrow> (int_dom exec_dg_st lifted, int_dom exec_dg_st lifted) dg_state)" where
  "ics_sol_warrow k mode gs empty_pred Pi ps =
     TD_side_warrowing_apinis_Interp_solve (ics_eqs k mode gs empty_pred Pi ps)
       (cfg_exit (compile_prog Pi ps), [])"

definition ics_terminates_warrow ::
    "nat \<Rightarrow> refine_mode \<Rightarrow> (vname \<Rightarrow> bool) \<Rightarrow> (int_dom exec_dg_st \<Rightarrow> bool) \<Rightarrow> proc_table \<Rightarrow> pname list
       \<Rightarrow> bool" where
  "ics_terminates_warrow k mode gs empty_pred Pi ps =
     TD_side_warrowing_apinis_Interp.solve_dom TYPE(call_string_gk) TYPE((int_dom exec_dg_st lifted, int_dom exec_dg_st lifted) dg_state)
       (ics_eqs k mode gs empty_pred Pi ps) (cfg_exit (compile_prog Pi ps), [])"

lemma ics_terminates_warrow_via_solve_c:
  assumes "TD_side_warrowing_apinis_Interp_solve_c (ics_eqs k mode gs empty_pred Pi ps)
             (cfg_exit (compile_prog Pi ps), []) \<noteq> None"
  shows "ics_terminates_warrow k mode gs empty_pred Pi ps"
  unfolding ics_terminates_warrow_def
  by (rule TD_side_warrowing_apinis_Interp.solve_dom_of_solve_c[OF assms])

subsection \<open>Domain commute facts, at the call-string routed spec\<close>

text \<open>
  \<^const>\<open>Call_String_Context.cs_route\<close> is polymorphic in its \<open>'d\<close> argument and ignores
  it outright, exactly as \<^const>\<open>route_unit\<close> does, so the routing-agreement obligation
  \<^locale>\<open>routed_domain_exec\<close> takes as a parameter is true unconditionally here.
  Everything else in the interpretation is Int's own mode-generic commute facts,
  cited unchanged: switching context policy is a different instantiation of one
  derivation, not a second one.
\<close>

lemma ics_route_commute: "cs_route k u c' d ca = cs_route k u c' (f d) ca"
  by (simp add: cs_route_def)

context
  fixes mode :: refine_mode and gs :: "vname \<Rightarrow> bool"
    and empty_pred :: "int_dom exec_dg_st \<Rightarrow> bool" and k :: nat
  assumes exact: "\<And>s. empty_pred s = is_empty_state (fun_of_resolved_st_q_for gs s)"
begin

interpretation int_cs: routed_domain_exec
  gs empty_pred "int_tf_st_for mode gs" "int_dom_enter_st_for mode gs" "int_tf_for mode gs"
  Call_String_Context.Global Call_String_Context.Seed "cs_route k" "cs_route k"
  static_resolve static_resolve
  by unfold_locales
     (rule int_tf_st_for_commute, rule int_dom_enter_st_for_commute, rule exact, simp,
      rule ics_route_commute, simp add: static_resolve_def)

lemmas int_cs_pp_st_gen = int_cs.pp_st

end

subsection \<open>The certified executable post-solution, generic per compiled program\<close>

context
  fixes mode :: refine_mode and gs :: "vname \<Rightarrow> bool" and empty_pred :: "int_dom exec_dg_st \<Rightarrow> bool"
    and Pi :: proc_table and ps :: "pname list" and k :: nat
  assumes solves: "ics_terminates k mode gs empty_pred Pi ps"
    and exact: "\<And>s. empty_pred s = is_empty_state (fun_of_resolved_st_q_for gs s)"
begin

lemma ics_solve_dom:
  "TD_side_always_join_Interp.solve_dom TYPE(call_string_gk) TYPE((int_dom exec_dg_st lifted, int_dom exec_dg_st lifted) dg_state)
     (ics_eqs k mode gs empty_pred Pi ps) (cfg_exit (compile_prog Pi ps), [])"
  using solves[unfolded ics_terminates_def] .

lemma ics_pp_st:
  "part_post_solution (ics_eqs k mode gs empty_pred Pi ps) (cfg_exit (compile_prog Pi ps), [])
     (snd (ics_sol k mode gs empty_pred Pi ps)) (fst (ics_sol k mode gs empty_pred Pi ps))"
  using TD_side_always_join_Interp.partial_post_solution
          [OF ics_solve_dom, of "fst (ics_sol k mode gs empty_pred Pi ps)"
             "snd (ics_sol k mode gs empty_pred Pi ps)"]
  unfolding ics_sol_def by simp

text \<open>The solver's post-solution, for the unbuffered routed generator at the executable
  spec: the shape \<^locale>\<open>call_string_routed_context\<close> consumes directly.\<close>

theorem ics_pp_routed:
  "part_post_solution
     (side_cfg_T_eff_keyed_seed_dg intra_predecessor_addr_list (\<lambda>_. Call_String_Context.Global)
        (cs_route k)
        (routed_cmb_g (ictx_spec mode empty_pred gs) Call_String_Context.Global
           Call_String_Context.Seed (static_resolve (compile_prog Pi ps)))
        (routed_extra_g Call_String_Context.Seed Call_String_Context.Global)
        (compile_prog Pi ps) (ictx_spec mode empty_pred gs) Bot (Lifted cinit_int_dom_st) Bot)
     (cfg_exit (compile_prog Pi ps), [])
     (snd (ics_sol k mode gs empty_pred Pi ps)) (fst (ics_sol k mode gs empty_pred Pi ps))"
  using ics_pp_st unfolding ics_eqs_def ictx_spec_def by (rule int_cs_pp_st_gen[OF exact])
end

subsection \<open>The certified executable post-solution under warrowing\<close>

context
  fixes mode :: refine_mode and gs :: "vname \<Rightarrow> bool" and empty_pred :: "int_dom exec_dg_st \<Rightarrow> bool"
    and Pi :: proc_table and ps :: "pname list" and k :: nat
  assumes solves: "ics_terminates_warrow k mode gs empty_pred Pi ps"
    and exact: "\<And>s. empty_pred s = is_empty_state (fun_of_resolved_st_q_for gs s)"
begin

lemma ics_solve_dom_warrow:
  "TD_side_warrowing_apinis_Interp.solve_dom TYPE(call_string_gk) TYPE((int_dom exec_dg_st lifted, int_dom exec_dg_st lifted) dg_state)
     (ics_eqs k mode gs empty_pred Pi ps) (cfg_exit (compile_prog Pi ps), [])"
  using solves[unfolded ics_terminates_warrow_def] .

lemma ics_pp_st_warrow:
  "part_post_solution (ics_eqs k mode gs empty_pred Pi ps) (cfg_exit (compile_prog Pi ps), [])
     (snd (ics_sol_warrow k mode gs empty_pred Pi ps)) (fst (ics_sol_warrow k mode gs empty_pred Pi ps))"
  using TD_side_warrowing_apinis_Interp.partial_post_solution
          [OF ics_solve_dom_warrow, of "fst (ics_sol_warrow k mode gs empty_pred Pi ps)"
             "snd (ics_sol_warrow k mode gs empty_pred Pi ps)"]
  unfolding ics_sol_warrow_def by simp

theorem ics_pp_routed_warrow:
  "part_post_solution
     (side_cfg_T_eff_keyed_seed_dg intra_predecessor_addr_list (\<lambda>_. Call_String_Context.Global)
        (cs_route k)
        (routed_cmb_g (ictx_spec mode empty_pred gs) Call_String_Context.Global
           Call_String_Context.Seed (static_resolve (compile_prog Pi ps)))
        (routed_extra_g Call_String_Context.Seed Call_String_Context.Global)
        (compile_prog Pi ps) (ictx_spec mode empty_pred gs) Bot (Lifted cinit_int_dom_st) Bot)
     (cfg_exit (compile_prog Pi ps), [])
     (snd (ics_sol_warrow k mode gs empty_pred Pi ps))
     (fst (ics_sol_warrow k mode gs empty_pred Pi ps))"
  using ics_pp_st_warrow unfolding ics_eqs_def ictx_spec_def by (rule int_cs_pp_st_gen[OF exact])
end

subsection \<open>Whole-program convenience layer\<close>

text \<open>
  Fixed at \<^const>\<open>Refine_Fixpoint\<close>, matching Int's own production default
  (\<open>Int_Entry\<close>'s own \<open>analyse_int_report\<close>): \<open>mode\<close> stays a
  genuine parameter through every lemma above, exactly as Int's own routed-unit
  file threads it, and is only pinned here where the public, config-driven
  surface needs one concrete choice.
\<close>

definition ics_eqs_prog ::
    "nat \<Rightarrow> (vname \<Rightarrow> bool) \<Rightarrow> imp_prog
       \<Rightarrow> (pp \<times> call_string, call_string_gk, (int_dom exec_dg_st lifted, int_dom exec_dg_st lifted) dg_state) eqsT" where
  "ics_eqs_prog k gs p =
     ics_eqs k Refine_Fixpoint gs (resolved_st_q_is_bot_for (declared_global_vars p))
       (prog_table p) (prog_procs p)"

definition ics_sol_prog ::
    "nat \<Rightarrow> (vname \<Rightarrow> bool) \<Rightarrow> imp_prog
       \<Rightarrow> (pp \<times> call_string) set \<times> (pp \<times> call_string + call_string_gk \<Rightarrow> (int_dom exec_dg_st lifted, int_dom exec_dg_st lifted) dg_state)" where
  "ics_sol_prog k gs p =
     ics_sol k Refine_Fixpoint gs (resolved_st_q_is_bot_for (declared_global_vars p))
       (prog_table p) (prog_procs p)"

definition ics_terminates_prog :: "nat \<Rightarrow> (vname \<Rightarrow> bool) \<Rightarrow> imp_prog \<Rightarrow> bool" where
  "ics_terminates_prog k gs p =
     ics_terminates k Refine_Fixpoint gs (resolved_st_q_is_bot_for (declared_global_vars p))
       (prog_table p) (prog_procs p)"

lemma ics_terminates_prog_via_solve_c:
  assumes "TD_side_always_join_Interp_solve_c
             (ics_eqs_prog k gs p)
             (cfg_exit (compile_prog (prog_table p) (prog_procs p)), []) \<noteq> None"
  shows "ics_terminates_prog k gs p"
  using assms
  unfolding ics_terminates_prog_def ics_eqs_prog_def
  by (rule ics_terminates_via_solve_c)

definition ics_sol_prog_warrow ::
    "nat \<Rightarrow> (vname \<Rightarrow> bool) \<Rightarrow> imp_prog
       \<Rightarrow> (pp \<times> call_string) set \<times> (pp \<times> call_string + call_string_gk \<Rightarrow> (int_dom exec_dg_st lifted, int_dom exec_dg_st lifted) dg_state)" where
  "ics_sol_prog_warrow k gs p =
     ics_sol_warrow k Refine_Fixpoint gs (resolved_st_q_is_bot_for (declared_global_vars p))
       (prog_table p) (prog_procs p)"

definition ics_terminates_prog_warrow :: "nat \<Rightarrow> (vname \<Rightarrow> bool) \<Rightarrow> imp_prog \<Rightarrow> bool" where
  "ics_terminates_prog_warrow k gs p =
     ics_terminates_warrow k Refine_Fixpoint gs (resolved_st_q_is_bot_for (declared_global_vars p))
       (prog_table p) (prog_procs p)"

lemma ics_terminates_prog_warrow_via_solve_c:
  assumes "TD_side_warrowing_apinis_Interp_solve_c
             (ics_eqs_prog k gs p)
             (cfg_exit (compile_prog (prog_table p) (prog_procs p)), []) \<noteq> None"
  shows "ics_terminates_prog_warrow k gs p"
  using assms
  unfolding ics_terminates_prog_warrow_def ics_eqs_prog_def
  by (rule ics_terminates_warrow_via_solve_c)

section \<open>Solved-result table\<close>

text \<open>
  The solved call-string D/G system, read as a \<^typ>\<open>(call_string, int_dom abs_state)
  analysis_result\<close> -- the exact construction Sign's and Interval's own call-string
  result tables already use, at Int's own solve. The covered-key set is the
  solver's own, never an enumerated theoretical context space.
\<close>

definition analyse_int_call_string_result_for ::
    "nat \<Rightarrow> (vname \<Rightarrow> bool) \<Rightarrow> imp_prog \<Rightarrow> (call_string, int_dom abs_state) analysis_result" where
  "analyse_int_call_string_result_for k gs p =
     Analysis_Result
       (fst (ics_sol_prog k gs p))
       (\<lambda>v ctx. normalize_point gs
                  (canonicalize_lift (resolved_st_q_is_bot_for (declared_global_vars p))
                    (locals (snd (ics_sol_prog k gs p) (Inl (v, ctx))))))"

declare analyse_int_call_string_result_for_def [code del]

lemma analyse_int_call_string_result_for_code [code]:
  "analyse_int_call_string_result_for k gs p =
     (let sol = ics_sol_prog k gs p; gl = declared_global_vars p
      in Analysis_Result (fst sol)
           (\<lambda>v ctx. normalize_point gs
                      (canonicalize_lift (resolved_st_q_is_bot_for gl)
                        (locals (snd sol (Inl (v, ctx)))))))"
  unfolding analyse_int_call_string_result_for_def Let_def by (rule refl)

text \<open>Convenience instance at \<^const>\<open>declared_global\<close> \<open>p\<close> and \<^const>\<open>prog_main_name\<close>,
  matching Sign's own \<open>analyse_sign_call_string_result\<close>'s shape, with \<open>k\<close> as an
  explicit leading runtime argument.\<close>

definition analyse_int_call_string_result ::
    "nat \<Rightarrow> imp_prog \<Rightarrow> (call_string, int_dom abs_state) analysis_result" where
  "analyse_int_call_string_result k p =
     analyse_int_call_string_result_for k (declared_global p) p"

section \<open>Contextual check report\<close>

text \<open>
  Reuses \<^const>\<open>classify_checks_ctx\<close>/\<^const>\<open>classify_checks_verdicts\<close> unchanged --
  both are generic in the context type already, so nothing call-string-specific
  is needed here beyond supplying the call-string result table and Int's own
  \<^const>\<open>int_classify_check\<close>, exactly mirroring Sign's own
  \<open>scs_check_projection\<close>/\<open>scs_verdict_report_prog\<close>.
\<close>

definition ics_check_projection ::
    "nat \<Rightarrow> imp_prog \<Rightarrow> (pp \<times> exp \<times> (call_string \<times> contextual_verdict) set) list" where
  "ics_check_projection k p =
     classify_checks_ctx (prog_cfg p)
       (analyse_int_call_string_result_for k (declared_global p) p)
       int_classify_check"

definition ics_verdict_report_prog ::
    "nat \<Rightarrow> imp_prog \<Rightarrow> (pp \<times> exp \<times> contextual_verdict) list" where
  "ics_verdict_report_prog k p =
     map (\<lambda>(u, c, vs). (u, c, aggregate_verdicts (snd ` vs)))
       (ics_check_projection k p)"

lemma ics_verdict_report_prog_eq:
  "ics_verdict_report_prog k p =
     classify_checks_verdicts (prog_cfg p)
       (analyse_int_call_string_result_for k (declared_global p) p)
       int_classify_check"
  unfolding ics_verdict_report_prog_def ics_check_projection_def
  by (rule classify_checks_verdicts_proj)

definition analyse_int_call_string_report ::
    "nat \<Rightarrow> imp_prog \<Rightarrow> (pp \<times> exp \<times> contextual_verdict) list" where
  "analyse_int_call_string_report k p = ics_verdict_report_prog k p"

subsection \<open>Result table and report under warrowing\<close>

definition analyse_int_call_string_result_for_warrow ::
    "nat \<Rightarrow> (vname \<Rightarrow> bool) \<Rightarrow> imp_prog \<Rightarrow> (call_string, int_dom abs_state) analysis_result" where
  "analyse_int_call_string_result_for_warrow k gs p =
     Analysis_Result
       (fst (ics_sol_prog_warrow k gs p))
       (\<lambda>v ctx. normalize_point gs
                  (canonicalize_lift (resolved_st_q_is_bot_for (declared_global_vars p))
                    (locals (snd (ics_sol_prog_warrow k gs p) (Inl (v, ctx))))))"

declare analyse_int_call_string_result_for_warrow_def [code del]

lemma analyse_int_call_string_result_for_warrow_code [code]:
  "analyse_int_call_string_result_for_warrow k gs p =
     (let sol = ics_sol_prog_warrow k gs p; gl = declared_global_vars p
      in Analysis_Result (fst sol)
           (\<lambda>v ctx. normalize_point gs
                      (canonicalize_lift (resolved_st_q_is_bot_for gl)
                        (locals (snd sol (Inl (v, ctx)))))))"
  unfolding analyse_int_call_string_result_for_warrow_def Let_def by (rule refl)

definition analyse_int_call_string_result_warrow ::
    "nat \<Rightarrow> imp_prog \<Rightarrow> (call_string, int_dom abs_state) analysis_result" where
  "analyse_int_call_string_result_warrow k p =
     analyse_int_call_string_result_for_warrow k (declared_global p) p"

definition ics_verdict_report_prog_warrow ::
    "nat \<Rightarrow> imp_prog \<Rightarrow> (pp \<times> exp \<times> contextual_verdict) list" where
  "ics_verdict_report_prog_warrow k p =
     classify_checks_verdicts (prog_cfg p)
       (analyse_int_call_string_result_for_warrow k (declared_global p) p)
       int_classify_check"

definition analyse_int_call_string_report_warrow ::
    "nat \<Rightarrow> imp_prog \<Rightarrow> (pp \<times> exp \<times> contextual_verdict) list" where
  "analyse_int_call_string_report_warrow k p = ics_verdict_report_prog_warrow k p"

end
