theory Int_Call_String_Ctx_Sound
  imports
    "Voblint_Analysis.Int_Exec_Ctx_Sound"
    "Voblint_Analysis.Int_Classify"
    "Voblint_Core.Call_String_Context"
    "Voblint_Core.Call_String_Routed_Context"
begin

section \<open>Int at the routed spine, instantiated at the call-string context\<close>

text \<open>
  The call-string sibling of \<^theory>\<open>Voblint_Analysis.Int_Exec_Ctx_Sound\<close>'s own
  routed-unit-context instance, mirroring \<open>Sign_Call_String_Ctx_Sound\<close>'s own
  derivation for a second domain: same \<^const>\<open>ictx_spec\<close>/\<^const>\<open>ictx_abs_spec\<close>
  D/G specification and the same domain-commute facts Int's own routed-unit
  instance already interprets (\<^locale>\<open>routed_dg_domain_exec\<close>,
  \<^theory>\<open>Voblint_Analysis.DG_Base_Exec\<close>) -- nothing here re-derives them, and the
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
     side_cfg_T_eff_keyed_seed_dg_buffered intra_predecessor_list (\<lambda>_. Call_String_Context.Global)
       (cs_route k)
       (routed_cmb_g_contribution (ictx_spec mode is_bot_pred gs) Call_String_Context.Global Call_String_Context.Seed)
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
  unfolding ics_terminates_def TD_side_always_join_Interp.term_equivalence
            TD_side_always_join_Interp.solve_c_dom_def
  using assms by simp

subsection \<open>Route agreement collapses to a free lemma\<close>

text \<open>
  \<^const>\<open>Call_String_Context.cs_route\<close> is polymorphic in its \<open>'d\<close> argument and ignores
  it outright, exactly as \<^const>\<open>route_unit\<close> does: the routing-agreement obligation
  is true unconditionally, for any reader \<open>f\<close>, the same free lemma Int's own
  \<open>route_unit_commute\<close> is.
\<close>

lemma ics_route_commute: "cs_route k u c' d ca = cs_route k u c' (f d) ca"
  by (simp add: cs_route_def)

subsection \<open>Domain commute facts, at the call-string routed spec\<close>

text \<open>
  Mirrors Int's own routed-unit instance verbatim, only repointed from
  \<^const>\<open>route_unit\<close>/Int's own unit-context \<open>gk\<close> to \<^const>\<open>cs_route\<close>/
  \<^type>\<open>call_string_gk\<close>: both cite the exact same generic packaging theorem
  (\<^locale>\<open>dg_reader_commute_gen\<close>) at the exact same domain-commute facts
  (\<open>int_Henter_lifted_for\<close>, \<open>int_Hcomb_lifted_for\<close>,
  \<open>dg_reader_commute_gen_int_lifted\<close>) the routed-unit instance already established
  -- no new Int transfer mathematics, only the routing-policy substitution.
\<close>

lemma ics_seed_ne_global [simp]: "Call_String_Context.Seed p ctx \<noteq> Call_String_Context.Global"
  by simp

lemma dg_tree_st_commute_routed_cmb_g_int_cs:
  assumes exact: "\<And>s. is_bot_pred s = is_bot_state (fun_of_resolved_st_q_for gs s)"
  shows "dg_reader_commute_gen.dg_tree_st_commute
           (map_lift (fun_of_resolved_st_q_for gs)) (map_lift (fun_of_resolved_st_q_for gs)) env
     (routed_cmb_g (ictx_spec mode is_bot_pred gs) Call_String_Context.Global Call_String_Context.Seed
        (cs_route k) ctx ca cc ex)
     (routed_cmb_g (ictx_abs_spec mode gs) Call_String_Context.Global Call_String_Context.Seed
        (cs_route k) ctx ca cc ex)"
  unfolding ictx_spec_def ictx_abs_spec_def
  apply (rule dg_reader_commute_gen.dg_tree_st_commute_routed_cmb_g
        [where Floc = "map_lift (fun_of_resolved_st_q_for gs)"
           and Fglob = "map_lift (fun_of_resolved_st_q_for gs)"])
      apply (rule dg_reader_commute_gen_int_lifted)
     apply (rule ics_seed_ne_global)
    apply (rule int_Henter_lifted_for[OF exact])
   apply (rule int_Hcomb_lifted_for[OF exact])
  apply (rule int_Hcont_lifted_for[OF exact])
  apply (rule ics_route_commute)
  done

lemma hextra_commute_routed_int_cs:
  "list_all2 (dg_reader_commute_gen.dg_tree_st_commute
                (map_lift (fun_of_resolved_st_q_for gs)) (map_lift (fun_of_resolved_st_q_for gs)) env)
     (routed_extra_g Call_String_Context.Seed Call_String_Context.Global (cs_route k) ctx w)
     (routed_extra_g Call_String_Context.Seed Call_String_Context.Global (cs_route k) ctx w)"
  by (rule dg_reader_commute_gen.dg_tree_st_commute_routed_extra_g[OF dg_reader_commute_gen_int_lifted])

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
  using solves
  unfolding ics_terminates_def TD_side_always_join_Interp.term_equivalence
            TD_side_always_join_Interp.solve_c_dom_def
  by simp

lemma ics_pp_st:
  "part_post_solution (ics_eqs k mode gs is_bot_pred Pi ps mnm main) (cfg_exit (compile_prog Pi ps mnm main), [])
     (snd (ics_sol k mode gs is_bot_pred Pi ps mnm main)) (fst (ics_sol k mode gs is_bot_pred Pi ps mnm main))"
  using TD_side_always_join_Interp.partial_post_solution
          [OF ics_solve_dom, of "fst (ics_sol k mode gs is_bot_pred Pi ps mnm main)"
             "snd (ics_sol k mode gs is_bot_pred Pi ps mnm main)"]
  unfolding ics_sol_def by simp

theorem ics_pp_abs:
  "part_post_solution
     (side_cfg_T_eff_keyed_seed_dg intra_predecessor_list (\<lambda>_. Call_String_Context.Global) (cs_route k)
        (routed_cmb_g (ictx_abs_spec mode gs) Call_String_Context.Global Call_String_Context.Seed)
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
  have pp'_buf: "part_post_solution
       (side_cfg_T_eff_keyed_seed_dg_buffered intra_predecessor_list (\<lambda>_. Call_String_Context.Global)
          (cs_route k)
          (routed_cmb_g_contribution (ictx_spec mode is_bot_pred gs) Call_String_Context.Global Call_String_Context.Seed)
          (routed_extra_g Call_String_Context.Seed Call_String_Context.Global)
          (compile_prog Pi ps mnm main) (ictx_spec mode is_bot_pred gs) Bot (Lifted cinit_int_dom_st) Bot)
       (cfg_exit (compile_prog Pi ps mnm main), [])
       (snd (ics_sol k mode gs is_bot_pred Pi ps mnm main)) (fst (ics_sol k mode gs is_bot_pred Pi ps mnm main))"
    using ics_pp_st unfolding ics_eqs_def by simp
  have seed_ne_global: "\<And>p c. Call_String_Context.Seed p c \<noteq> Call_String_Context.Global" by simp
  have pp': "part_post_solution
       (side_cfg_T_eff_keyed_seed_dg intra_predecessor_list (\<lambda>_. Call_String_Context.Global) (cs_route k)
          (routed_cmb_g (ictx_spec mode is_bot_pred gs) Call_String_Context.Global Call_String_Context.Seed)
          (routed_extra_g Call_String_Context.Seed Call_String_Context.Global)
          (compile_prog Pi ps mnm main) (ictx_spec mode is_bot_pred gs) Bot (Lifted cinit_int_dom_st) Bot)
       (cfg_exit (compile_prog Pi ps mnm main), [])
       (snd (ics_sol k mode gs is_bot_pred Pi ps mnm main)) (fst (ics_sol k mode gs is_bot_pred Pi ps mnm main))"
  proof (rule part_post_solution_seed_dg_buffered_to_old
      [where cmb_c = "routed_cmb_g_contribution (ictx_spec mode is_bot_pred gs) Call_String_Context.Global Call_String_Context.Seed"])
    show "\<And>c' ca cc ex \<tau>. locals (traverse_rhs
             (routed_cmb_g_contribution (ictx_spec mode is_bot_pred gs) Call_String_Context.Global Call_String_Context.Seed
               (cs_route k) c' ca cc ex) \<tau>)
           = locals (traverse_rhs
             (routed_cmb_g (ictx_spec mode is_bot_pred gs) Call_String_Context.Global Call_String_Context.Seed
               (cs_route k) c' ca cc ex) \<tau>)"
      by (rule routed_cmb_g_contribution_matches_local)
    show "\<And>c' ca cc ex \<tau>. locals (sides_of_rhs
             (routed_cmb_g (ictx_spec mode is_bot_pred gs) Call_String_Context.Global Call_String_Context.Seed
               (cs_route k) c' ca cc ex) \<tau> (Inr ((\<lambda>_. Call_String_Context.Global) c'))) = bot"
      by (rule routed_cmb_g_side_pure[of Call_String_Context.Seed Call_String_Context.Global, OF seed_ne_global])
    show "\<And>c' ca cc ex \<tau>. globs (traverse_rhs
             (routed_cmb_g_contribution (ictx_spec mode is_bot_pred gs) Call_String_Context.Global Call_String_Context.Seed
               (cs_route k) c' ca cc ex) \<tau>)
           = globs (sides_of_rhs
             (routed_cmb_g (ictx_spec mode is_bot_pred gs) Call_String_Context.Global Call_String_Context.Seed
               (cs_route k) c' ca cc ex) \<tau> (Inr ((\<lambda>_. Call_String_Context.Global) c')))"
      by (rule routed_cmb_g_contribution_matches_global[of Call_String_Context.Seed Call_String_Context.Global, OF seed_ne_global])
    show "\<And>c' ca cc ex \<tau>. sides_of_rhs
             (routed_cmb_g_contribution (ictx_spec mode is_bot_pred gs) Call_String_Context.Global Call_String_Context.Seed
               (cs_route k) c' ca cc ex) \<tau> (Inr ((\<lambda>_. Call_String_Context.Global) c')) = bot"
      by (rule routed_cmb_g_contribution_free_at_key[of Call_String_Context.Seed Call_String_Context.Global, OF seed_ne_global])
    show "\<And>c' ca cc ex \<tau> z. z \<noteq> Inr ((\<lambda>_. Call_String_Context.Global) c') \<Longrightarrow> sides_of_rhs
             (routed_cmb_g_contribution (ictx_spec mode is_bot_pred gs) Call_String_Context.Global Call_String_Context.Seed
               (cs_route k) c' ca cc ex) \<tau> z
           = sides_of_rhs
             (routed_cmb_g (ictx_spec mode is_bot_pred gs) Call_String_Context.Global Call_String_Context.Seed
               (cs_route k) c' ca cc ex) \<tau> z"
      by (rule routed_cmb_g_contribution_sides_off_key[of Call_String_Context.Seed Call_String_Context.Global, OF seed_ne_global])
    show "\<And>c' ca cc ex \<tau>. dep_aux \<tau>
             (routed_cmb_g_contribution (ictx_spec mode is_bot_pred gs) Call_String_Context.Global Call_String_Context.Seed
               (cs_route k) c' ca cc ex)
           = dep_aux \<tau>
             (routed_cmb_g (ictx_spec mode is_bot_pred gs) Call_String_Context.Global Call_String_Context.Seed
               (cs_route k) c' ca cc ex)"
      by (rule routed_cmb_g_contribution_dep)
    show "\<And>c' w \<tau> z x. x \<in> set (routed_extra_g Call_String_Context.Seed Call_String_Context.Global (cs_route k) c' w)
           \<Longrightarrow> sides_of_rhs x \<tau> z = bot"
      by (rule routed_extra_g_free)
    show "\<And>c' w \<tau> x. x \<in> set (routed_extra_g Call_String_Context.Seed Call_String_Context.Global (cs_route k) c' w)
           \<Longrightarrow> globs (traverse_rhs x \<tau>) = bot"
      by (rule routed_extra_g_local_only)
    show "part_post_solution
       (side_cfg_T_eff_keyed_seed_dg_buffered intra_predecessor_list (\<lambda>_. Call_String_Context.Global)
          (cs_route k)
          (routed_cmb_g_contribution (ictx_spec mode is_bot_pred gs) Call_String_Context.Global Call_String_Context.Seed)
          (routed_extra_g Call_String_Context.Seed Call_String_Context.Global)
          (compile_prog Pi ps mnm main) (ictx_spec mode is_bot_pred gs) Bot (Lifted cinit_int_dom_st) Bot)
       (cfg_exit (compile_prog Pi ps mnm main), [])
       (snd (ics_sol k mode gs is_bot_pred Pi ps mnm main)) (fst (ics_sol k mode gs is_bot_pred Pi ps mnm main))"
      by (rule pp'_buf)
  qed
  have int_Hstep_ctx:
    "map_prod (map_lift (fun_of_resolved_st_q_for gs)) (map_lift (fun_of_resolved_st_q_for gs))
       (dg_spec_step (ictx_spec mode is_bot_pred gs) a d g') =
       dg_spec_step (ictx_abs_spec mode gs) a
         (map_lift (fun_of_resolved_st_q_for gs) d) (map_lift (fun_of_resolved_st_q_for gs) g')" for a d g'
    unfolding ictx_spec_def ictx_abs_spec_def by (rule int_Hstep_lifted_for[OF exact])
  show ?thesis
    apply (rule part_post_solution_seed_dg_st_to_abs_lifted_for
          [where gs = gs and pred_sel = intra_predecessor_list and gkey = "\<lambda>_. Call_String_Context.Global"
             and route_st = "cs_route k :: cfg_node \<Rightarrow> call_string \<Rightarrow> int_dom exec_dg_st lifted \<Rightarrow> call_action \<Rightarrow> call_string"
             and route_abs = "cs_route k :: cfg_node \<Rightarrow> call_string \<Rightarrow> int_dom abs_state lifted \<Rightarrow> call_action \<Rightarrow> call_string"
             and cmb_st = "routed_cmb_g (ictx_spec mode is_bot_pred gs) Call_String_Context.Global Call_String_Context.Seed"
             and cmb_abs = "routed_cmb_g (ictx_abs_spec mode gs) Call_String_Context.Global Call_String_Context.Seed"
             and extra_st = "routed_extra_g Call_String_Context.Seed Call_String_Context.Global"
             and extra_abs = "routed_extra_g Call_String_Context.Seed Call_String_Context.Global"
             and g = "compile_prog Pi ps mnm main" and S_st = "ictx_spec mode is_bot_pred gs" and S_abs = "ictx_abs_spec mode gs"])
        apply (rule int_Hstep_ctx)
       apply (rule ics_route_commute)
      apply (rule dg_tree_st_commute_routed_cmb_g_int_cs[OF exact])
     apply (rule hextra_commute_routed_int_cs)
    apply (rule pp')
    done
qed

end

subsection \<open>Whole-program convenience layer\<close>

text \<open>
  Fixed at \<^const>\<open>Refine_Fixpoint\<close>, matching Int's own production default
  (\<open>Int_Codegen\<close>'s own \<open>analyse_int_report\<close>): \<open>mode\<close> stays a
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
