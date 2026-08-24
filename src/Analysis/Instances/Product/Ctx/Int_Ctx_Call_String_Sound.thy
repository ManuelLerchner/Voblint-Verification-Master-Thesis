theory Int_Ctx_Call_String_Sound
  imports
    "Voblint_Analysis.Int_Ctx_None_Sound"
    "Voblint_Analysis.Int_Classify"
    "Voblint_Core.Call_String_Context"
    "Voblint_Core.Call_String_Routed_Context"
begin

section \<open>Int at the routed spine, instantiated at the call-string context\<close>

text \<open>
  The call-string sibling of \<^theory>\<open>Voblint_Analysis.Int_Ctx_None_Sound\<close>'s own
  routed-unit-context instance, mirroring \<open>Sign_Ctx_Call_String_Sound\<close>'s own
  derivation for a second domain: same \<^const>\<open>ictx_spec\<close>/\<^const>\<open>ictx_abs_spec\<close>
  D/G specification and the same domain-commute facts Int's own routed-unit
  instance already interprets (\<^locale>\<open>routed_dg_domain_exec\<close>,
  \<^theory>\<open>Voblint_Core.DG_Base_Exec\<close>) -- nothing here re-derives them, and the
  \<^typ>\<open>refine_mode\<close> parameter Int threads throughout stays a genuine fixed
  argument exactly as it already is at Int's own \<^const>\<open>ictx_spec\<close>. Only the
  routing policy changes, from \<^const>\<open>route_unit\<close> to
  \<^const>\<open>Call_String_Context.cs_route\<close> at a runtime bound \<open>k\<close>, and the routed-context
  locale interpreted changes from \<^locale>\<open>unit_routed_context\<close> to
  \<^locale>\<open>call_string_routed_context\<close> (\<^theory>\<open>Voblint_Core.Call_String_Routed_Context\<close>),
  exactly as Sign's own call-string derivation already uses.

  This is the mission's stretch-goal acceptance test at a third domain: a second
  context for Int, exposed from the existing generic routed-domain interpretation
  and the existing generic call-string context locale, with no new Int-domain
  mathematics.
\<close>

subsection \<open>The routed equation system and its executable solution\<close>

definition ics_eqs ::
    "nat \<Rightarrow> refine_mode \<Rightarrow> (vname \<Rightarrow> bool) \<Rightarrow> (int_dom exec_dg_st \<Rightarrow> bool) \<Rightarrow> proc_table \<Rightarrow> pname list
       \<Rightarrow> pname \<Rightarrow> com
       \<Rightarrow> (pp \<times> call_string, call_string_gk, (int_dom exec_dg_st lifted, int_dom exec_dg_st lifted) dg_state) eqsT" where
  "ics_eqs k mode gs is_bot_pred Pi ps mnm main =
     side_cfg_T_eff_keyed_seed_dg_buffered intra_predecessor_addr_list (\<lambda>_. Call_String_Context.Global)
       (cs_route k)
       (routed_cmb_g_contribution (ictx_spec mode is_bot_pred gs)
          Call_String_Context.Global Call_String_Context.Seed
          (static_resolve (compile_prog Pi ps mnm main)))
       (routed_extra_g Call_String_Context.Seed Call_String_Context.Global)
       (compile_prog Pi ps mnm main) (ictx_spec mode is_bot_pred gs) Bot (Lifted cinit_int_dom_st) Bot"

definition ics_sol ::
    "nat \<Rightarrow> refine_mode \<Rightarrow> (vname \<Rightarrow> bool) \<Rightarrow> (int_dom exec_dg_st \<Rightarrow> bool) \<Rightarrow> proc_table \<Rightarrow> pname list
       \<Rightarrow> pname \<Rightarrow> com
       \<Rightarrow> (pp \<times> call_string) set \<times> (pp \<times> call_string + call_string_gk \<Rightarrow> (int_dom exec_dg_st lifted, int_dom exec_dg_st lifted) dg_state)" where
  "ics_sol k mode gs is_bot_pred Pi ps mnm main =
     TD_side_always_join_Interp_solve (ics_eqs k mode gs is_bot_pred Pi ps mnm main)
       (cfg_exit (compile_prog Pi ps mnm main), [])"

definition ics_terminates ::
    "nat \<Rightarrow> refine_mode \<Rightarrow> (vname \<Rightarrow> bool) \<Rightarrow> (int_dom exec_dg_st \<Rightarrow> bool) \<Rightarrow> proc_table \<Rightarrow> pname list
       \<Rightarrow> pname \<Rightarrow> com \<Rightarrow> bool" where
  "ics_terminates k mode gs is_bot_pred Pi ps mnm main =
     TD_side_always_join_Interp.solve_dom TYPE(call_string_gk) TYPE((int_dom exec_dg_st lifted, int_dom exec_dg_st lifted) dg_state)
       (ics_eqs k mode gs is_bot_pred Pi ps mnm main) (cfg_exit (compile_prog Pi ps mnm main), [])"

lemma ics_terminates_via_solve_c:
  assumes "TD_side_always_join_Interp_solve_c (ics_eqs k mode gs is_bot_pred Pi ps mnm main)
             (cfg_exit (compile_prog Pi ps mnm main), []) \<noteq> None"
  shows "ics_terminates k mode gs is_bot_pred Pi ps mnm main"
  unfolding ics_terminates_def
  by (rule TD_side_always_join_Interp.solve_dom_of_solve_c[OF assms])

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
    and is_bot_pred :: "int_dom exec_dg_st \<Rightarrow> bool" and k :: nat
  assumes exact: "\<And>s. is_bot_pred s = is_bot_state (fun_of_resolved_st_q_for gs s)"
begin

interpretation int_cs: routed_domain_exec
  gs is_bot_pred "int_tf_st_for mode gs" "int_dom_enter_st_for mode gs" "int_tf_for mode gs"
  Call_String_Context.Global Call_String_Context.Seed "cs_route k" "cs_route k"
  static_resolve static_resolve
  by unfold_locales
     (rule int_tf_st_for_commute, rule int_dom_enter_st_for_commute, rule exact, simp,
      rule ics_route_commute, simp add: static_resolve_def)

lemmas int_cs_pp_abs_gen = int_cs.pp_abs

end

subsection \<open>The certified executable post-solution, generic per compiled program\<close>

context
  fixes mode :: refine_mode and gs :: "vname \<Rightarrow> bool" and is_bot_pred :: "int_dom exec_dg_st \<Rightarrow> bool"
    and Pi :: proc_table and ps :: "pname list" and mnm :: pname and main :: com and k :: nat
  assumes solves: "ics_terminates k mode gs is_bot_pred Pi ps mnm main"
    and exact: "\<And>s. is_bot_pred s = is_bot_state (fun_of_resolved_st_q_for gs s)"
begin

lemma ics_solve_dom:
  "TD_side_always_join_Interp.solve_dom TYPE(call_string_gk) TYPE((int_dom exec_dg_st lifted, int_dom exec_dg_st lifted) dg_state)
     (ics_eqs k mode gs is_bot_pred Pi ps mnm main) (cfg_exit (compile_prog Pi ps mnm main), [])"
  using solves[unfolded ics_terminates_def] .

lemma ics_pp_st:
  "part_post_solution (ics_eqs k mode gs is_bot_pred Pi ps mnm main) (cfg_exit (compile_prog Pi ps mnm main), [])
     (snd (ics_sol k mode gs is_bot_pred Pi ps mnm main)) (fst (ics_sol k mode gs is_bot_pred Pi ps mnm main))"
  using TD_side_always_join_Interp.partial_post_solution
          [OF ics_solve_dom, of "fst (ics_sol k mode gs is_bot_pred Pi ps mnm main)"
             "snd (ics_sol k mode gs is_bot_pred Pi ps mnm main)"]
  unfolding ics_sol_def by simp

theorem ics_pp_abs:
  "part_post_solution
     (side_cfg_T_eff_keyed_seed_dg intra_predecessor_addr_list (\<lambda>_. Call_String_Context.Global) (cs_route k)
        (routed_cmb_g (ictx_abs_spec mode gs) Call_String_Context.Global Call_String_Context.Seed
           (static_resolve (compile_prog Pi ps mnm main)))
        (routed_extra_g Call_String_Context.Seed Call_String_Context.Global)
        (compile_prog Pi ps mnm main) (ictx_abs_spec mode gs)
        (map_lift (fun_of_resolved_st_q_for gs) (Bot::int_dom exec_dg_st lifted))
        (map_lift (fun_of_resolved_st_q_for gs) (Lifted cinit_int_dom_st))
        (map_lift (fun_of_resolved_st_q_for gs) (Bot::int_dom exec_dg_st lifted)))
     (cfg_exit (compile_prog Pi ps mnm main), [])
     (fun_of_dg_st_gen (map_lift (fun_of_resolved_st_q_for gs)) (map_lift (fun_of_resolved_st_q_for gs))
        \<circ> snd (ics_sol k mode gs is_bot_pred Pi ps mnm main))
     (fst (ics_sol k mode gs is_bot_pred Pi ps mnm main))"
proof -
  have pp_buf: "part_post_solution
       (side_cfg_T_eff_keyed_seed_dg_buffered intra_predecessor_addr_list
          (\<lambda>_. Call_String_Context.Global) (cs_route k)
          (routed_cmb_g_contribution (ictx_spec mode is_bot_pred gs)
             Call_String_Context.Global Call_String_Context.Seed
             (static_resolve (compile_prog Pi ps mnm main)))
          (routed_extra_g Call_String_Context.Seed Call_String_Context.Global)
          (compile_prog Pi ps mnm main) (ictx_spec mode is_bot_pred gs)
          Bot (Lifted cinit_int_dom_st) Bot)
       (cfg_exit (compile_prog Pi ps mnm main), [])
       (snd (ics_sol k mode gs is_bot_pred Pi ps mnm main))
       (fst (ics_sol k mode gs is_bot_pred Pi ps mnm main))"
    using ics_pp_st unfolding ics_eqs_def by simp
  show ?thesis
    unfolding ictx_abs_spec_def
    using pp_buf unfolding ictx_spec_def by (rule int_cs_pp_abs_gen[OF exact])
qed

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
    "nat \<Rightarrow> (vname \<Rightarrow> bool) \<Rightarrow> pname \<Rightarrow> imp_prog
       \<Rightarrow> (pp \<times> call_string, call_string_gk, (int_dom exec_dg_st lifted, int_dom exec_dg_st lifted) dg_state) eqsT" where
  "ics_eqs_prog k gs mnm p =
     ics_eqs k Refine_Fixpoint gs (resolved_st_q_is_bot_for (declared_global_vars p))
       (prog_table p) (prog_procs p) mnm (prog_main p)"

definition ics_sol_prog ::
    "nat \<Rightarrow> (vname \<Rightarrow> bool) \<Rightarrow> pname \<Rightarrow> imp_prog
       \<Rightarrow> (pp \<times> call_string) set \<times> (pp \<times> call_string + call_string_gk \<Rightarrow> (int_dom exec_dg_st lifted, int_dom exec_dg_st lifted) dg_state)" where
  "ics_sol_prog k gs mnm p =
     ics_sol k Refine_Fixpoint gs (resolved_st_q_is_bot_for (declared_global_vars p))
       (prog_table p) (prog_procs p) mnm (prog_main p)"

definition ics_terminates_prog :: "nat \<Rightarrow> (vname \<Rightarrow> bool) \<Rightarrow> pname \<Rightarrow> imp_prog \<Rightarrow> bool" where
  "ics_terminates_prog k gs mnm p =
     ics_terminates k Refine_Fixpoint gs (resolved_st_q_is_bot_for (declared_global_vars p))
       (prog_table p) (prog_procs p) mnm (prog_main p)"

lemma ics_terminates_prog_via_solve_c:
  assumes "TD_side_always_join_Interp_solve_c
             (ics_eqs_prog k gs mnm p)
             (cfg_exit (compile_prog (prog_table p) (prog_procs p) mnm (prog_main p)), []) \<noteq> None"
  shows "ics_terminates_prog k gs mnm p"
  using assms
  unfolding ics_terminates_prog_def ics_eqs_prog_def
  by (rule ics_terminates_via_solve_c)

section \<open>Solved-result table\<close>

text \<open>
  The solved call-string D/G system, read as a \<^typ>\<open>(call_string, int_dom abs_state)
  analysis_result\<close> -- the exact construction Sign's and Interval's own call-string
  result tables already use, at Int's own solve. The covered-key set is the
  solver's own, never an enumerated theoretical context space.
\<close>

definition analyse_int_call_string_result_for ::
    "nat \<Rightarrow> (vname \<Rightarrow> bool) \<Rightarrow> pname \<Rightarrow> imp_prog \<Rightarrow> (call_string, int_dom abs_state) analysis_result" where
  "analyse_int_call_string_result_for k gs mnm p =
     Analysis_Result
       (fst (ics_sol_prog k gs mnm p))
       (\<lambda>v ctx. normalize_point gs
                  (canonicalize_lift (resolved_st_q_is_bot_for (declared_global_vars p))
                    (locals (snd (ics_sol_prog k gs mnm p) (Inl (v, ctx))))))"

declare analyse_int_call_string_result_for_def [code del]

lemma analyse_int_call_string_result_for_code [code]:
  "analyse_int_call_string_result_for k gs mnm p =
     (let sol = ics_sol_prog k gs mnm p; gl = declared_global_vars p
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
     analyse_int_call_string_result_for k (declared_global p) prog_main_name p"

section \<open>Contextual check report\<close>

text \<open>
  Reuses \<^const>\<open>classify_checks_ctx\<close>/\<^const>\<open>classify_checks_verdicts\<close> unchanged --
  both are generic in the context type already, so nothing call-string-specific
  is needed here beyond supplying the call-string result table and Int's own
  \<^const>\<open>int_classify_check\<close>, exactly mirroring Sign's own
  \<open>scs_check_projection\<close>/\<open>scs_verdict_report_prog\<close>.
\<close>

definition ics_check_projection ::
    "nat \<Rightarrow> pname \<Rightarrow> imp_prog \<Rightarrow> (pp \<times> exp \<times> (call_string \<times> contextual_verdict) set) list" where
  "ics_check_projection k mnm p =
     classify_checks_ctx (prog_cfg mnm p)
       (analyse_int_call_string_result_for k (declared_global p) mnm p)
       int_classify_check"

definition ics_verdict_report_prog ::
    "nat \<Rightarrow> pname \<Rightarrow> imp_prog \<Rightarrow> (pp \<times> exp \<times> contextual_verdict) list" where
  "ics_verdict_report_prog k mnm p =
     map (\<lambda>(u, c, vs). (u, c, aggregate_verdicts (snd ` vs)))
       (ics_check_projection k mnm p)"

lemma ics_verdict_report_prog_eq:
  "ics_verdict_report_prog k mnm p =
     classify_checks_verdicts (prog_cfg mnm p)
       (analyse_int_call_string_result_for k (declared_global p) mnm p)
       int_classify_check"
  unfolding ics_verdict_report_prog_def ics_check_projection_def
  by (rule classify_checks_verdicts_proj)

definition analyse_int_call_string_report ::
    "nat \<Rightarrow> imp_prog \<Rightarrow> (pp \<times> exp \<times> contextual_verdict) list" where
  "analyse_int_call_string_report k p = ics_verdict_report_prog k prog_main_name p"

end
