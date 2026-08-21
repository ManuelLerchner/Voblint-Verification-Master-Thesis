theory Interval_Ctx_None_Routed_Sound
  imports
    "Voblint_Analysis.Exec_DG_Bridge"
    "Voblint_Analysis.Interval_DG"
    "Voblint_Analysis.Interval_Exec_Sound"
    "Voblint_Analysis.Interval_Classify"
    "Voblint_Core.Routed_Context"
    "Voblint_Core.Routed_Context_Unit"
    "Voblint_Core.DG_Analysis_Adapter"
    "Voblint_Core.Solver_Menu"
    "Voblint_VIMP.VIMP_Notation"
begin

section \<open>Interval at the routed spine, instantiated at the unit context\<close>

text \<open>
  Redirects Interval's production Base-family (\<open>dg_gen_of\<close>) analysis onto the
  routed D/G spine (\<^locale>\<open>dg_ctx_activation_base\<close>, \<^locale>\<open>unit_routed_context\<close>)
  that Interval's own entry-state and call-string context analyses already use.
  The context here is \<^typ>\<open>unit\<close>: \<^locale>\<open>unit_routed_context\<close>
  (\<^theory>\<open>Voblint_Core.Routed_Context_Unit\<close>) fixes \<^const>\<open>route_unit\<close>, so every
  routing-agreement obligation a non-trivial routed instance must prove from its
  own transfer facts collapses here to a free lemma about the constant function
  \<^const>\<open>route_unit\<close> --- exactly the collapse Sign's own unit-context instance
  (\<open>Sign_Exec_Ctx_Sound\<close>) already exercises.

  Soundness below is derived directly from \<^locale>\<open>dg_ctx_activation_base\<close>'s
  generic machinery against the collecting semantics, exactly as Interval's
  entry-state analysis is derived. No comparison to Interval's Base-family
  production result is attempted or needed: \<^const>\<open>dg_gen_of\<close> never appears in
  this development.
\<close>

subsection \<open>Global key: real globals vs callee-entry seed slots\<close>

text \<open>
  \<^typ>\<open>unit\<close> context, so the seed constructor's second field is \<^typ>\<open>unit\<close> rather
  than an interesting per-context payload: exactly one seed slot per callee entry.
\<close>

datatype gk = Global | Seed (seed_pp: pp) (seed_ctx: unit)

subsection \<open>The routed unit-context D/G spec\<close>

text \<open>
  The same Base-style whole-state specification Interval's own production
  \<^const>\<open>analyse_interval_dg_eqs_for\<close> already solves over
  (\<^theory>\<open>Voblint_Analysis.Interval_Exec_Sound\<close>), at the same
  \<^const>\<open>ivl_tf_st_for\<close>/\<^const>\<open>ivl_enter_st_for\<close> primitives -- byte-for-byte the
  term \<open>base_dg_spec_st_for_lifted gs is_bot_pred (ivl_tf_st_for gs) (ivl_enter_st_for gs)\<close>
  that \<^const>\<open>analyse_interval_dg_eqs_for\<close> feeds \<^const>\<open>dg_gen_of\<close>. Only the
  equation-generator wrapped around this spec changes (\<open>dg_gen_of\<close> there, the
  routed keyed-seed generator here) --- the spec itself, and every domain-transfer
  soundness fact about it, is untouched.
\<close>

definition ictx_spec ::
  "(vname \<Rightarrow> bool) \<Rightarrow> (ivl exec_dg_st \<Rightarrow> bool) \<Rightarrow> (ivl exec_dg_st lifted, ivl exec_dg_st lifted) dg_spec"
where
  "ictx_spec gs is_bot_pred = base_dg_spec_st_for_lifted gs is_bot_pred (ivl_tf_st_for gs) (ivl_enter_st_for gs)"

definition ictx_abs_spec :: "(vname \<Rightarrow> bool) \<Rightarrow> (ivl abs_state lifted, ivl abs_state lifted) dg_spec" where
  "ictx_abs_spec gs = base_dg_spec_for_lifted gs is_bot_state (ivl_tf_for gs)"

subsection \<open>The routed equation system and its executable solution\<close>

text \<open>
  Solved under the always-join update rule, mirroring Sign's own choice: the
  minimal solver instance needed to prove direct soundness once. Interval's
  production route needs Apinis warrowing for termination on an unbounded local
  loop (\<^theory>\<open>Voblint_Analysis.Interval_Exec_Sound\<close>'s own
  \<open>analyse_interval_dg_for\<close>); that solver choice is orthogonal to this context
  (commit \<open>c38efade\<close>) and is future work here, not attempted.
\<close>

definition ictx_eqs ::
    "(vname \<Rightarrow> bool) \<Rightarrow> (ivl exec_dg_st \<Rightarrow> bool) \<Rightarrow> proc_table \<Rightarrow> pname list \<Rightarrow> pname \<Rightarrow> com
       \<Rightarrow> (pp \<times> unit, gk, (ivl exec_dg_st lifted, ivl exec_dg_st lifted) dg_state) eqsT" where
  "ictx_eqs gs is_bot_pred Pi ps mnm main =
     side_cfg_T_eff_keyed_seed_dg_buffered intra_predecessor_list (\<lambda>_. Global)
       route_unit
       (routed_cmb_g_contribution (ictx_spec gs is_bot_pred) Global Seed)
       (routed_extra_g Seed Global)
       (compile_prog Pi ps mnm main) (ictx_spec gs is_bot_pred) Bot (Lifted cinit_ivl_st) Bot"

definition ictx_sol ::
    "(vname \<Rightarrow> bool) \<Rightarrow> (ivl exec_dg_st \<Rightarrow> bool) \<Rightarrow> proc_table \<Rightarrow> pname list \<Rightarrow> pname \<Rightarrow> com
       \<Rightarrow> (pp \<times> unit) set \<times> (pp \<times> unit + gk \<Rightarrow> (ivl exec_dg_st lifted, ivl exec_dg_st lifted) dg_state)" where
  "ictx_sol gs is_bot_pred Pi ps mnm main =
     TD_side_always_join_Interp_solve (ictx_eqs gs is_bot_pred Pi ps mnm main)
       (cfg_exit (compile_prog Pi ps mnm main), ())"

definition ictx_terminates ::
    "(vname \<Rightarrow> bool) \<Rightarrow> (ivl exec_dg_st \<Rightarrow> bool) \<Rightarrow> proc_table \<Rightarrow> pname list \<Rightarrow> pname \<Rightarrow> com \<Rightarrow> bool" where
  "ictx_terminates gs is_bot_pred Pi ps mnm main =
     TD_side_always_join_Interp.solve_dom TYPE(gk) TYPE((ivl exec_dg_st lifted, ivl exec_dg_st lifted) dg_state)
       (ictx_eqs gs is_bot_pred Pi ps mnm main) (cfg_exit (compile_prog Pi ps mnm main), ())"

lemma ictx_terminates_via_solve_c:
  assumes "TD_side_always_join_Interp_solve_c (ictx_eqs gs is_bot_pred Pi ps mnm main)
             (cfg_exit (compile_prog Pi ps mnm main), ()) \<noteq> None"
  shows "ictx_terminates gs is_bot_pred Pi ps mnm main"
  unfolding ictx_terminates_def TD_side_always_join_Interp.term_equivalence
            TD_side_always_join_Interp.solve_c_dom_def
  using assms by simp

subsection \<open>Route agreement collapses to a free lemma\<close>

text \<open>
  \<^const>\<open>route_unit\<close> is used, unchanged, at both the executable and abstract
  carrier: it is polymorphic in its \<^typ>\<open>'D\<close> argument and ignores it outright, so
  the routing-agreement obligation every other routed instance must prove from
  its own transfer facts is here true unconditionally, for any reader \<open>f\<close>.
\<close>

lemma route_unit_commute: "route_unit u c' d ca = route_unit u c' (f d) ca"
  by simp

subsection \<open>Domain commute facts, at the routed unit spec\<close>

text \<open>
  Mirrors Interval's own \<open>ivl_Hstep_lifted_for\<close>/\<open>ivl_Henter_lifted_for\<close>/
  \<open>ivl_Hcomb_lifted_for\<close> (\<open>Interval_Exec_Ctx_Sound\<close>),
  citing the same carrier-generic packaging theorems from
  \<^theory>\<open>Voblint_Analysis.DG_Base_Exec\<close> at Interval's own primitive commute facts
  \<^const>\<open>ivl_tf_st_for\<close>/\<^const>\<open>ivl_enter_st_for\<close> already prove
  (\<open>ivl_tf_st_for_commute\<close>, \<open>ivl_enter_st_for_commute\<close>,
  \<^theory>\<open>Voblint_Analysis.Ivl_Exec\<close>).
\<close>

lemma ictx_Hstep_lifted_for:
  assumes exact: "\<And>s. is_bot_pred s = is_bot_state (fun_of_resolved_st_q_for gs s)"
  shows "map_prod (map_lift (fun_of_resolved_st_q_for gs)) (map_lift (fun_of_resolved_st_q_for gs))
           (dg_spec_step (base_dg_spec_st_for_lifted gs is_bot_pred (ivl_tf_st_for gs) (ivl_enter_st_for gs)) a d g)
         = dg_spec_step (base_dg_spec_for_lifted gs is_bot_state (ivl_tf_for gs)) a
             (map_lift (fun_of_resolved_st_q_for gs) d) (map_lift (fun_of_resolved_st_q_for gs) g)"
  by (rule base_dg_spec_st_for_lifted_dg_spec_step_commute
        [unfolded fun_of_exec_dg_st_for_def, OF ivl_tf_st_for_commute exact])

lemma ictx_Henter_lifted_for:
  assumes exact: "\<And>s. is_bot_pred s = is_bot_state (fun_of_resolved_st_q_for gs s)"
  shows "map_prod (map_lift (fun_of_resolved_st_q_for gs)) (map_lift (fun_of_resolved_st_q_for gs))
           (dgs_enter (base_dg_spec_st_for_lifted gs is_bot_pred (ivl_tf_st_for gs) (ivl_enter_st_for gs)) xs es d g)
         = dgs_enter (base_dg_spec_for_lifted gs is_bot_state (ivl_tf_for gs)) xs es
             (map_lift (fun_of_resolved_st_q_for gs) d) (map_lift (fun_of_resolved_st_q_for gs) g)"
  by (rule base_dg_spec_st_for_lifted_dgs_enter_commute
        [unfolded fun_of_exec_dg_st_for_def, OF ivl_enter_st_for_commute exact])

lemma ictx_Hcomb_lifted_for:
  assumes exact: "\<And>s. is_bot_pred s = is_bot_state (fun_of_resolved_st_q_for gs s)"
  shows "map_prod (map_lift (fun_of_resolved_st_q_for gs)) (map_lift (fun_of_resolved_st_q_for gs))
           (dgs_combine (base_dg_spec_st_for_lifted gs is_bot_pred (ivl_tf_st_for gs) (ivl_enter_st_for gs)) dst dc de g)
         = dgs_combine (base_dg_spec_for_lifted gs is_bot_state (ivl_tf_for gs)) dst
             (map_lift (fun_of_resolved_st_q_for gs) dc) (map_lift (fun_of_resolved_st_q_for gs) de)
             (map_lift (fun_of_resolved_st_q_for gs) g)"
  by (rule base_dg_spec_st_for_lifted_dgs_combine_commute
        [where tf = "ivl_tf_for gs", unfolded fun_of_exec_dg_st_for_def, OF exact])

lemma dg_reader_commute_gen_ictx_lifted:
  "dg_reader_commute_gen
     (map_lift (fun_of_resolved_st_q_for gs)) (map_lift (fun_of_resolved_st_q_for gs))"
  by unfold_locales (simp_all add: map_lift_sup fun_of_resolved_st_q_for_sup)

lemma seed_ne_global [simp]: "Seed p ctx \<noteq> Global"
  by simp

lemma dg_tree_st_commute_routed_cmb_g_ictx:
  assumes exact: "\<And>s. is_bot_pred s = is_bot_state (fun_of_resolved_st_q_for gs s)"
  shows "dg_reader_commute_gen.dg_tree_st_commute
           (map_lift (fun_of_resolved_st_q_for gs)) (map_lift (fun_of_resolved_st_q_for gs)) env
     (routed_cmb_g (ictx_spec gs is_bot_pred) Global Seed route_unit ctx ca cc ex)
     (routed_cmb_g (ictx_abs_spec gs) Global Seed route_unit ctx ca cc ex)"
  unfolding ictx_spec_def ictx_abs_spec_def
  apply (rule dg_reader_commute_gen.dg_tree_st_commute_routed_cmb_g
        [where Floc = "map_lift (fun_of_resolved_st_q_for gs)"
           and Fglob = "map_lift (fun_of_resolved_st_q_for gs)"])
      apply (rule dg_reader_commute_gen_ictx_lifted)
     apply (rule seed_ne_global)
    apply (rule ictx_Henter_lifted_for[OF exact])
   apply (rule ictx_Hcomb_lifted_for[OF exact])
  apply (rule route_unit_commute)
  done

lemma hextra_commute_routed_ictx:
  "list_all2 (dg_reader_commute_gen.dg_tree_st_commute
                (map_lift (fun_of_resolved_st_q_for gs)) (map_lift (fun_of_resolved_st_q_for gs)) env)
     (routed_extra_g Seed Global route_unit ctx w)
     (routed_extra_g Seed Global route_unit ctx w)"
  by (rule dg_reader_commute_gen.dg_tree_st_commute_routed_extra_g[OF dg_reader_commute_gen_ictx_lifted])

subsection \<open>The certified executable post-solution, generic per compiled program\<close>

context
  fixes gs :: "vname \<Rightarrow> bool" and is_bot_pred :: "ivl exec_dg_st \<Rightarrow> bool"
    and Pi :: proc_table and ps :: "pname list" and mnm :: pname and main :: com
  assumes solves: "ictx_terminates gs is_bot_pred Pi ps mnm main"
    and exact: "\<And>s. is_bot_pred s = is_bot_state (fun_of_resolved_st_q_for gs s)"
begin

lemma ictx_solve_dom:
  "TD_side_always_join_Interp.solve_dom TYPE(gk) TYPE((ivl exec_dg_st lifted, ivl exec_dg_st lifted) dg_state)
     (ictx_eqs gs is_bot_pred Pi ps mnm main) (cfg_exit (compile_prog Pi ps mnm main), ())"
  using solves
  unfolding ictx_terminates_def TD_side_always_join_Interp.term_equivalence
            TD_side_always_join_Interp.solve_c_dom_def
  by simp

lemma ictx_pp_st:
  "part_post_solution (ictx_eqs gs is_bot_pred Pi ps mnm main) (cfg_exit (compile_prog Pi ps mnm main), ())
     (snd (ictx_sol gs is_bot_pred Pi ps mnm main)) (fst (ictx_sol gs is_bot_pred Pi ps mnm main))"
  using TD_side_always_join_Interp.partial_post_solution
          [OF ictx_solve_dom, of "fst (ictx_sol gs is_bot_pred Pi ps mnm main)"
             "snd (ictx_sol gs is_bot_pred Pi ps mnm main)"]
  unfolding ictx_sol_def by simp

theorem ictx_pp_abs:
  "part_post_solution
     (side_cfg_T_eff_keyed_seed_dg intra_predecessor_list (\<lambda>_. Global) route_unit
        (routed_cmb_g (ictx_abs_spec gs) Global Seed)
        (routed_extra_g Seed Global)
        (compile_prog Pi ps mnm main) (ictx_abs_spec gs)
        (map_lift (fun_of_resolved_st_q_for gs) (Bot::ivl exec_dg_st lifted))
        (map_lift (fun_of_resolved_st_q_for gs) (Lifted cinit_ivl_st))
        (map_lift (fun_of_resolved_st_q_for gs) (Bot::ivl exec_dg_st lifted)))
     (cfg_exit (compile_prog Pi ps mnm main), ())
     (fun_of_dg_st_gen (map_lift (fun_of_resolved_st_q_for gs)) (map_lift (fun_of_resolved_st_q_for gs))
        \<circ> snd (ictx_sol gs is_bot_pred Pi ps mnm main))
     (fst (ictx_sol gs is_bot_pred Pi ps mnm main))"
proof -
  have pp'_buf: "part_post_solution
       (side_cfg_T_eff_keyed_seed_dg_buffered intra_predecessor_list (\<lambda>_. Global)
          route_unit
          (routed_cmb_g_contribution (ictx_spec gs is_bot_pred) Global Seed)
          (routed_extra_g Seed Global)
          (compile_prog Pi ps mnm main) (ictx_spec gs is_bot_pred) Bot (Lifted cinit_ivl_st) Bot)
       (cfg_exit (compile_prog Pi ps mnm main), ())
       (snd (ictx_sol gs is_bot_pred Pi ps mnm main)) (fst (ictx_sol gs is_bot_pred Pi ps mnm main))"
    using ictx_pp_st unfolding ictx_eqs_def by simp
  have seed_ne_global: "\<And>p c. Seed p c \<noteq> Global" by simp
  have pp': "part_post_solution
       (side_cfg_T_eff_keyed_seed_dg intra_predecessor_list (\<lambda>_. Global) route_unit
          (routed_cmb_g (ictx_spec gs is_bot_pred) Global Seed)
          (routed_extra_g Seed Global)
          (compile_prog Pi ps mnm main) (ictx_spec gs is_bot_pred) Bot (Lifted cinit_ivl_st) Bot)
       (cfg_exit (compile_prog Pi ps mnm main), ())
       (snd (ictx_sol gs is_bot_pred Pi ps mnm main)) (fst (ictx_sol gs is_bot_pred Pi ps mnm main))"
  proof (rule part_post_solution_seed_dg_buffered_to_old
      [where cmb_c = "routed_cmb_g_contribution (ictx_spec gs is_bot_pred) Global Seed"])
    show "\<And>c' ca cc ex \<tau>. locals (traverse_rhs
             (routed_cmb_g_contribution (ictx_spec gs is_bot_pred) Global Seed
               route_unit c' ca cc ex) \<tau>)
           = locals (traverse_rhs
             (routed_cmb_g (ictx_spec gs is_bot_pred) Global Seed
               route_unit c' ca cc ex) \<tau>)"
      by (rule routed_cmb_g_contribution_matches_local)
    show "\<And>c' ca cc ex \<tau>. locals (sides_of_rhs
             (routed_cmb_g (ictx_spec gs is_bot_pred) Global Seed
               route_unit c' ca cc ex) \<tau> (Inr ((\<lambda>_. Global) c'))) = bot"
      by (rule routed_cmb_g_side_pure[of Seed Global, OF seed_ne_global])
    show "\<And>c' ca cc ex \<tau>. globs (traverse_rhs
             (routed_cmb_g_contribution (ictx_spec gs is_bot_pred) Global Seed
               route_unit c' ca cc ex) \<tau>)
           = globs (sides_of_rhs
             (routed_cmb_g (ictx_spec gs is_bot_pred) Global Seed
               route_unit c' ca cc ex) \<tau> (Inr ((\<lambda>_. Global) c')))"
      by (rule routed_cmb_g_contribution_matches_global[of Seed Global, OF seed_ne_global])
    show "\<And>c' ca cc ex \<tau>. sides_of_rhs
             (routed_cmb_g_contribution (ictx_spec gs is_bot_pred) Global Seed
               route_unit c' ca cc ex) \<tau> (Inr ((\<lambda>_. Global) c')) = bot"
      by (rule routed_cmb_g_contribution_free_at_key[of Seed Global, OF seed_ne_global])
    show "\<And>c' ca cc ex \<tau> z. z \<noteq> Inr ((\<lambda>_. Global) c') \<Longrightarrow> sides_of_rhs
             (routed_cmb_g_contribution (ictx_spec gs is_bot_pred) Global Seed
               route_unit c' ca cc ex) \<tau> z
           = sides_of_rhs
             (routed_cmb_g (ictx_spec gs is_bot_pred) Global Seed
               route_unit c' ca cc ex) \<tau> z"
      by (rule routed_cmb_g_contribution_sides_off_key[of Seed Global, OF seed_ne_global])
    show "\<And>c' ca cc ex \<tau>. dep_aux \<tau>
             (routed_cmb_g_contribution (ictx_spec gs is_bot_pred) Global Seed
               route_unit c' ca cc ex)
           = dep_aux \<tau>
             (routed_cmb_g (ictx_spec gs is_bot_pred) Global Seed
               route_unit c' ca cc ex)"
      by (rule routed_cmb_g_contribution_dep)
    show "\<And>c' w \<tau> z x. x \<in> set (routed_extra_g Seed Global route_unit c' w)
           \<Longrightarrow> sides_of_rhs x \<tau> z = bot"
      by (rule routed_extra_g_free)
    show "\<And>c' w \<tau> x. x \<in> set (routed_extra_g Seed Global route_unit c' w)
           \<Longrightarrow> globs (traverse_rhs x \<tau>) = bot"
      by (rule routed_extra_g_local_only)
    show "part_post_solution
       (side_cfg_T_eff_keyed_seed_dg_buffered intra_predecessor_list (\<lambda>_. Global)
          route_unit
          (routed_cmb_g_contribution (ictx_spec gs is_bot_pred) Global Seed)
          (routed_extra_g Seed Global)
          (compile_prog Pi ps mnm main) (ictx_spec gs is_bot_pred) Bot (Lifted cinit_ivl_st) Bot)
       (cfg_exit (compile_prog Pi ps mnm main), ())
       (snd (ictx_sol gs is_bot_pred Pi ps mnm main)) (fst (ictx_sol gs is_bot_pred Pi ps mnm main))"
      by (rule pp'_buf)
  qed
  have ictx_Hstep_ctx:
    "map_prod (map_lift (fun_of_resolved_st_q_for gs)) (map_lift (fun_of_resolved_st_q_for gs))
       (dg_spec_step (ictx_spec gs is_bot_pred) a d g') =
       dg_spec_step (ictx_abs_spec gs) a
         (map_lift (fun_of_resolved_st_q_for gs) d) (map_lift (fun_of_resolved_st_q_for gs) g')" for a d g'
    unfolding ictx_spec_def ictx_abs_spec_def by (rule ictx_Hstep_lifted_for[OF exact])
  show ?thesis
    apply (rule part_post_solution_seed_dg_st_to_abs_lifted_for
          [where gs = gs and pred_sel = intra_predecessor_list and gkey = "\<lambda>_. Global"
             and route_st = "route_unit :: cfg_node \<Rightarrow> unit \<Rightarrow> ivl exec_dg_st lifted \<Rightarrow> call_action \<Rightarrow> unit"
             and route_abs = "route_unit :: cfg_node \<Rightarrow> unit \<Rightarrow> ivl abs_state lifted \<Rightarrow> call_action \<Rightarrow> unit"
             and cmb_st = "routed_cmb_g (ictx_spec gs is_bot_pred) Global Seed"
             and cmb_abs = "routed_cmb_g (ictx_abs_spec gs) Global Seed"
             and extra_st = "routed_extra_g Seed Global"
             and extra_abs = "routed_extra_g Seed Global"
             and g = "compile_prog Pi ps mnm main" and S_st = "ictx_spec gs is_bot_pred" and S_abs = "ictx_abs_spec gs"])
        apply (rule ictx_Hstep_ctx)
       apply (rule route_unit_commute)
      apply (rule dg_tree_st_commute_routed_cmb_g_ictx[OF exact])
     apply (rule hextra_commute_routed_ictx)
    apply (rule pp')
    done
qed

end

section \<open>Activation-indexed collecting soundness, generic per compiled program\<close>

text \<open>
  Executable twins of the context's own \<open>ictx_sigma_abs\<close>/\<open>ictx_sg\<close> (below),
  defined before that context so their equations are unconditional -- mirrors
  Interval's \<open>entry_state_sigma_abs_exec\<close>/\<open>entry_state_sg_exec\<close> convention
  exactly.
\<close>

definition ictx_sigma_abs_exec ::
    "(vname \<Rightarrow> bool) \<Rightarrow> (ivl exec_dg_st \<Rightarrow> bool) \<Rightarrow> proc_table \<Rightarrow> pname list \<Rightarrow> pname \<Rightarrow> com
       \<Rightarrow> pp \<times> unit + gk \<Rightarrow> (ivl abs_state lifted, ivl abs_state lifted) dg_state" where
  "ictx_sigma_abs_exec gs is_bot_pred Pi ps mnm main =
     fun_of_dg_st_gen (map_lift (fun_of_resolved_st_q_for gs)) (map_lift (fun_of_resolved_st_q_for gs))
       \<circ> snd (ictx_sol gs is_bot_pred Pi ps mnm main)"

definition ictx_sg_exec ::
    "(vname \<Rightarrow> bool) \<Rightarrow> (ivl exec_dg_st \<Rightarrow> bool) \<Rightarrow> proc_table \<Rightarrow> pname list \<Rightarrow> pname \<Rightarrow> com
       \<Rightarrow> pp \<times> unit + gk \<Rightarrow> ivl abs_state lifted" where
  "ictx_sg_exec gs is_bot_pred Pi ps mnm main k =
     (case k of
        Inl (v, ctx) \<Rightarrow>
          (if (v, ctx) \<in> fst (ictx_sol gs is_bot_pred Pi ps mnm main)
           then locals (ictx_sigma_abs_exec gs is_bot_pred Pi ps mnm main (Inl (v, ctx)))
           else Bot)
      | Inr _ \<Rightarrow> Bot)"

context
  fixes gs :: "vname \<Rightarrow> bool" and is_bot_pred :: "ivl exec_dg_st \<Rightarrow> bool"
    and Pi :: proc_table and ps :: "pname list" and mnm :: pname and main :: com
  assumes solves: "ictx_terminates gs is_bot_pred Pi ps mnm main"
    and exact: "\<And>s. is_bot_pred s = is_bot_state (fun_of_resolved_st_q_for gs s)"
    and entry_cov: "(cfg_entry (compile_prog Pi ps mnm main), ()) \<in> fst (ictx_sol gs is_bot_pred Pi ps mnm main)"
    and fwd_ok: "\<And>u a v ctx. (u, ctx) \<in> fst (ictx_sol gs is_bot_pred Pi ps mnm main)
                   \<Longrightarrow> (u, a, v) \<in> intra (compile_prog Pi ps mnm main)
                   \<Longrightarrow> (v, ctx) \<in> fst (ictx_sol gs is_bot_pred Pi ps mnm main)"
    and call_fwd_ok: "\<And>u ctx dst pars args p cont.
        (u, ctx) \<in> fst (ictx_sol gs is_bot_pred Pi ps mnm main)
        \<Longrightarrow> (u, CallEdge dst pars args, FunctionEntry p, cont) \<in> calls (compile_prog Pi ps mnm main)
        \<Longrightarrow> (FunctionEntry p, ()) \<in> fst (ictx_sol gs is_bot_pred Pi ps mnm main)"
    and comb_fwd_ok: "\<And>cl c1 dst pars args p cont.
        (cl, c1) \<in> fst (ictx_sol gs is_bot_pred Pi ps mnm main)
        \<Longrightarrow> (cl, CallEdge dst pars args, FunctionEntry p, cont) \<in> calls (compile_prog Pi ps mnm main)
        \<Longrightarrow> (cont, c1) \<in> fst (ictx_sol gs is_bot_pred Pi ps mnm main)"
begin

subsection \<open>The semantic solution projection\<close>

definition ictx_sigma_abs :: "pp \<times> unit + gk \<Rightarrow> (ivl abs_state lifted, ivl abs_state lifted) dg_state" where
  "ictx_sigma_abs = ictx_sigma_abs_exec gs is_bot_pred Pi ps mnm main"

definition ictx_sg :: "pp \<times> unit + gk \<Rightarrow> ivl abs_state lifted" where
  "ictx_sg = ictx_sg_exec gs is_bot_pred Pi ps mnm main"

lemma ictx_fin: "finite (intra (compile_prog Pi ps mnm main))"
  using compile_prog_finite by blast

lemma ictx_finC: "finite (calls (compile_prog Pi ps mnm main))"
  using compile_prog_finite by blast

lemma ictx_sg_covered:
  "(v, ctx) \<in> fst (ictx_sol gs is_bot_pred Pi ps mnm main)
   \<Longrightarrow> ictx_sg (Inl (v, ctx)) = locals (ictx_sigma_abs (Inl (v, ctx)))"
  by (simp add: ictx_sg_def ictx_sg_exec_def ictx_sigma_abs_def ictx_sigma_abs_exec_def)

lemma ictx_sg_uncovered_empty:
  "(v, ctx) \<notin> fst (ictx_sol gs is_bot_pred Pi ps mnm main)
     \<Longrightarrow> gamma_state_lift (ictx_sg (Inl (v, ctx))) = {}"
  by (simp add: ictx_sg_def ictx_sg_exec_def)

subsection \<open>Instantiating the generic DG-native activation discharge\<close>

interpretation ictx_dg_base: sound_dg_spec "ictx_abs_spec gs" gamma_dg_base gs
  unfolding ictx_abs_spec_def
  by (rule base_dg_spec_sound[OF ivl_is_sound_transfer_for is_bot_state_gamma_state_empty])

interpretation ictx_dg: dg_ctx_activation_base "ictx_abs_spec gs" gamma_dg_base gs
    "compile_prog Pi ps mnm main" Global route_unit
    "routed_cmb_g (ictx_abs_spec gs) Global Seed"
    "routed_extra_g Seed Global"
    "map_lift (fun_of_resolved_st_q_for gs) (Bot::ivl exec_dg_st lifted)"
    "map_lift (fun_of_resolved_st_q_for gs) (Lifted cinit_ivl_st)"
    "map_lift (fun_of_resolved_st_q_for gs) (Bot::ivl exec_dg_st lifted)"
    ictx_sigma_abs "fst (ictx_sol gs is_bot_pred Pi ps mnm main)"
    "(cfg_exit (compile_prog Pi ps mnm main), ())" ictx_sg gamma_state_lift
proof unfold_locales
  show "finite (intra (compile_prog Pi ps mnm main))" by (rule ictx_fin)
next
  show "part_post_solution
          (side_cfg_T_eff_keyed_seed_dg intra_predecessor_list (\<lambda>_. Global) route_unit
             (routed_cmb_g (ictx_abs_spec gs) Global Seed)
             (routed_extra_g Seed Global)
             (compile_prog Pi ps mnm main) (ictx_abs_spec gs)
             (map_lift (fun_of_resolved_st_q_for gs) (Bot::ivl exec_dg_st lifted))
             (map_lift (fun_of_resolved_st_q_for gs) (Lifted cinit_ivl_st))
             (map_lift (fun_of_resolved_st_q_for gs) (Bot::ivl exec_dg_st lifted)))
          (cfg_exit (compile_prog Pi ps mnm main), ()) ictx_sigma_abs
          (fst (ictx_sol gs is_bot_pred Pi ps mnm main))"
    unfolding ictx_sigma_abs_def ictx_sigma_abs_exec_def
    by (rule ictx_pp_abs[OF solves exact])
next
  fix v ctx assume "(v, ctx) \<in> fst (ictx_sol gs is_bot_pred Pi ps mnm main)"
  thus "gamma_state_lift (ictx_sg (Inl (v, ctx)))
          = gamma_dg_base (locals (ictx_sigma_abs (Inl (v, ctx)))) (globs (ictx_sigma_abs (Inr Global)))"
    by (simp add: ictx_sg_covered gamma_dg_base_def)
next
  fix v ctx assume "(v, ctx) \<notin> fst (ictx_sol gs is_bot_pred Pi ps mnm main)"
  thus "gamma_state_lift (ictx_sg (Inl (v, ctx))) = {}"
    by (rule ictx_sg_uncovered_empty)
next
  fix u a v ctx assume "(u, ctx) \<in> fst (ictx_sol gs is_bot_pred Pi ps mnm main)"
    "(u, a, v) \<in> intra (compile_prog Pi ps mnm main)"
  thus "(v, ctx) \<in> fst (ictx_sol gs is_bot_pred Pi ps mnm main)" by (rule fwd_ok)
qed

subsection \<open>The routed interpretation and its CALL/COMB corollaries\<close>

interpretation ictx_routed: unit_routed_context "ictx_abs_spec gs" gamma_dg_base gs
    "compile_prog Pi ps mnm main" Global
    "map_lift (fun_of_resolved_st_q_for gs) (Bot::ivl exec_dg_st lifted)"
    "map_lift (fun_of_resolved_st_q_for gs) (Lifted cinit_ivl_st)"
    "map_lift (fun_of_resolved_st_q_for gs) (Bot::ivl exec_dg_st lifted)"
    ictx_sigma_abs "fst (ictx_sol gs is_bot_pred Pi ps mnm main)"
    "(cfg_exit (compile_prog Pi ps mnm main), ())" ictx_sg
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
      ce': "(cl, CallEdge dst' pars' args', FunctionEntry p', cont') \<in> calls (compile_prog Pi ps mnm main)"
    and es_eq: "es = call_enter gs (CallEdge dst' pars' args') s"
    using ces unfolding call_enter_store_def by blast
  have "CallEdge dst' pars' args' = CallEdge dst pars args"
    using compile_prog_calls_source_unique[OF ce' ce] by simp
  thus ?case using es_eq by simp
qed

subsection \<open>Activation-indexed collecting soundness\<close>

lemma ictx_cinit_le_cinit_ivl_st:
  "cinit_stores gs \<subseteq> gamma_state_lift (map_lift (fun_of_resolved_st_q_for gs) (Lifted cinit_ivl_st))"
  by (auto simp: cinit_stores_def gamma_state_def fun_of_resolved_st_q_for_def fun_of_st_cinit_ivl_st)

subsection \<open>The generic report adapter\<close>

text \<open>
  Interpreting \<^locale>\<open>dg_analysis_adapter\<close> at this context's own solved
  system reuses every obligation already discharged for \<open>ictx_dg\<close>/\<open>ictx_routed\<close>
  above: the five \<^locale>\<open>dg_ctx_activation_base\<close> obligations are exactly
  \<open>ictx_dg\<close>'s own, and the routed obligations collapse the same way
  \<^locale>\<open>unit_routed_context\<close>'s did, at \<^const>\<open>route_unit\<close>/\<^const>\<open>enterc_unit\<close>.
  Only \<open>classify_proved\<close>/\<open>classify_refuted\<close> are genuinely new, discharged by
  Interval's own \<open>interval_classify_check_proved\<close>/\<open>interval_classify_check_refuted\<close>
  (\<^theory>\<open>Voblint_Analysis.Interval_Classify\<close>).
\<close>

interpretation ictx_adapter: dg_analysis_adapter enterc_unit "ictx_abs_spec gs" gs
    "compile_prog Pi ps mnm main" Global route_unit
    "map_lift (fun_of_resolved_st_q_for gs) (Bot::ivl exec_dg_st lifted)"
    "map_lift (fun_of_resolved_st_q_for gs) (Lifted cinit_ivl_st)"
    "map_lift (fun_of_resolved_st_q_for gs) (Bot::ivl exec_dg_st lifted)"
    ictx_sigma_abs "fst (ictx_sol gs is_bot_pred Pi ps mnm main)"
    "(cfg_exit (compile_prog Pi ps mnm main), ())" ictx_sg
    Seed interval_classify_check
proof (unfold_locales, goal_cases FinE PP SgCov SgUncov Fwd FinC SeedKey RouteEnterc CallFwd CombFwd EnterAgree ClProved ClRefuted)
  case FinE show ?case by (rule ictx_fin)
next
  case PP show ?case
    unfolding ictx_sigma_abs_def ictx_sigma_abs_exec_def by (rule ictx_pp_abs[OF solves exact])
next
  case (SgCov v c)
  thus ?case
    by (simp add: ictx_sg_covered gamma_dg_base_def)
next
  case (SgUncov v c)
  thus ?case by (rule ictx_sg_uncovered_empty)
next
  case (Fwd u a v c)
  thus ?case by (rule fwd_ok)
next
  case FinC show ?case by (rule ictx_finC)
next
  case (SeedKey p ctx) show ?case by simp
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
      ce': "(cl, CallEdge dst' pars' args', FunctionEntry p', cont') \<in> calls (compile_prog Pi ps mnm main)"
    and es_eq: "es = call_enter gs (CallEdge dst' pars' args') s"
    using ces unfolding call_enter_store_def by blast
  have "CallEdge dst' pars' args' = CallEdge dst pars args"
    using compile_prog_calls_source_unique[OF ce' ce] by simp
  thus ?case using es_eq by simp
next
  case (ClProved c d s)
  thus ?case by (rule interval_classify_check_proved)
next
  case (ClRefuted c d s)
  thus ?case by (rule interval_classify_check_refuted)
qed

text \<open>
  The two generic soundness corollaries \<^locale>\<open>dg_analysis_adapter\<close> derives
  once and for all -- \<open>ictx_adapter.analyse_report_ctx_proved_sound\<close>,
  \<open>ictx_adapter.analyse_report_ctx_refuted_sound\<close> -- are available here without
  any further proof: an improvement over Sign's own file, which predates this
  locale and hand-rolls a report table with no soundness theorem attached.
\<close>

lemmas ictx_report_ctx_proved_sound = ictx_adapter.analyse_report_ctx_proved_sound
lemmas ictx_report_ctx_refuted_sound = ictx_adapter.analyse_report_ctx_refuted_sound

text \<open>
  \<open>ictx_result_node_sound\<close> re-exports the adapter's generic node-soundness bridge
  (\<^theory>\<open>Voblint_Core.DG_Analysis_Adapter\<close>). \<open>ictx_analyse_result_eq\<close> identifies that
  reading with the raw-tuple shape \<open>analyse_interval_ctx_result_for\<close> (defined below)
  already builds by hand, mirroring \<open>ictx_analyse_result_eq_warrow\<close>.
\<close>

lemmas ictx_result_node_sound = ictx_adapter.analyse_result_node_sound

lemma ictx_analyse_result_eq:
  "lookup_context ictx_adapter.analyse_result v ctx =
     (if (v, ctx) \<in> fst (ictx_sol gs is_bot_pred Pi ps mnm main)
      then normalize_point gs
             (canonicalize_lift is_bot_pred (locals (snd (ictx_sol gs is_bot_pred Pi ps mnm main) (Inl (v, ctx)))))
      else Unreachable)"
  unfolding ictx_adapter.lookup_context_analyse_result
  apply (simp only: ictx_sigma_abs_def ictx_sigma_abs_exec_def o_apply fun_of_dg_st_gen_simps(1))
  by (cases "locals (snd (ictx_sol gs is_bot_pred Pi ps mnm main) (Inl (v, ctx)))")
     (simp_all add: exact normalize_lift_def)

end

section \<open>PerOrigin solver instantiation, at the same routed unit-context spec\<close>

text \<open>
  Mirrors the always-join instantiation above (\<open>ictx_eqs\<close>/\<open>ictx_sol\<close>/\<open>ictx_terminates\<close>)
  under \<^const>\<open>TD_side_per_origin_Interp_solve\<close> instead, solving the exact same
  \<open>ictx_eqs\<close> equation system -- mirroring how Interval's own Base family
  (\<^theory>\<open>Voblint_Analysis.Interval_Exec_Sound\<close>) already solves
  \<open>analyse_interval_dg_eqs_for\<close> under three interchangeable update rules. Genuinely
  sound: \<^locale>\<open>TD_side_upd_rule\<close>'s \<open>solve_dom\<close>/\<open>partial_post_solution\<close> are
  locale-generic over the update rule, so \<open>TD_side_per_origin_Interp\<close>'s own
  \<open>partial_post_solution\<close> instance discharges the same obligation \<open>TD_side_always_join_Interp\<close>'s
  \<open>partial_post_solution\<close> did above, with no extra premises.
\<close>

definition ictx_sol_per_origin ::
    "(vname \<Rightarrow> bool) \<Rightarrow> (ivl exec_dg_st \<Rightarrow> bool) \<Rightarrow> proc_table \<Rightarrow> pname list \<Rightarrow> pname \<Rightarrow> com
       \<Rightarrow> (pp \<times> unit) set \<times> (pp \<times> unit + gk \<Rightarrow> (ivl exec_dg_st lifted, ivl exec_dg_st lifted) dg_state)" where
  "ictx_sol_per_origin gs is_bot_pred Pi ps mnm main =
     TD_side_per_origin_Interp_solve (ictx_eqs gs is_bot_pred Pi ps mnm main)
       (cfg_exit (compile_prog Pi ps mnm main), ())"

definition ictx_terminates_per_origin ::
    "(vname \<Rightarrow> bool) \<Rightarrow> (ivl exec_dg_st \<Rightarrow> bool) \<Rightarrow> proc_table \<Rightarrow> pname list \<Rightarrow> pname \<Rightarrow> com \<Rightarrow> bool" where
  "ictx_terminates_per_origin gs is_bot_pred Pi ps mnm main =
     TD_side_per_origin_Interp.solve_dom TYPE(gk) TYPE((ivl exec_dg_st lifted, ivl exec_dg_st lifted) dg_state)
       (ictx_eqs gs is_bot_pred Pi ps mnm main) (cfg_exit (compile_prog Pi ps mnm main), ())"

lemma ictx_terminates_per_origin_via_solve_c:
  assumes "TD_side_per_origin_Interp_solve_c (ictx_eqs gs is_bot_pred Pi ps mnm main)
             (cfg_exit (compile_prog Pi ps mnm main), ()) \<noteq> None"
  shows "ictx_terminates_per_origin gs is_bot_pred Pi ps mnm main"
  unfolding ictx_terminates_per_origin_def TD_side_per_origin_Interp.term_equivalence
            TD_side_per_origin_Interp.solve_c_dom_def
  using assms by simp

subsection \<open>The certified executable post-solution, generic per compiled program\<close>

context
  fixes gs :: "vname \<Rightarrow> bool" and is_bot_pred :: "ivl exec_dg_st \<Rightarrow> bool"
    and Pi :: proc_table and ps :: "pname list" and mnm :: pname and main :: com
  assumes solves: "ictx_terminates_per_origin gs is_bot_pred Pi ps mnm main"
    and exact: "\<And>s. is_bot_pred s = is_bot_state (fun_of_resolved_st_q_for gs s)"
begin

lemma ictx_solve_dom_per_origin:
  "TD_side_per_origin_Interp.solve_dom TYPE(gk) TYPE((ivl exec_dg_st lifted, ivl exec_dg_st lifted) dg_state)
     (ictx_eqs gs is_bot_pred Pi ps mnm main) (cfg_exit (compile_prog Pi ps mnm main), ())"
  using solves
  unfolding ictx_terminates_per_origin_def TD_side_per_origin_Interp.term_equivalence
            TD_side_per_origin_Interp.solve_c_dom_def
  by simp

lemma ictx_pp_st_per_origin:
  "part_post_solution (ictx_eqs gs is_bot_pred Pi ps mnm main) (cfg_exit (compile_prog Pi ps mnm main), ())
     (snd (ictx_sol_per_origin gs is_bot_pred Pi ps mnm main)) (fst (ictx_sol_per_origin gs is_bot_pred Pi ps mnm main))"
  using TD_side_upd_rule.TD_side_per_origin_Interp.partial_post_solution
          [OF ictx_solve_dom_per_origin, of "fst (ictx_sol_per_origin gs is_bot_pred Pi ps mnm main)"
             "snd (ictx_sol_per_origin gs is_bot_pred Pi ps mnm main)"]
  unfolding ictx_sol_per_origin_def by simp

theorem ictx_pp_abs_per_origin:
  "part_post_solution
     (side_cfg_T_eff_keyed_seed_dg intra_predecessor_list (\<lambda>_. Global) route_unit
        (routed_cmb_g (ictx_abs_spec gs) Global Seed)
        (routed_extra_g Seed Global)
        (compile_prog Pi ps mnm main) (ictx_abs_spec gs)
        (map_lift (fun_of_resolved_st_q_for gs) (Bot::ivl exec_dg_st lifted))
        (map_lift (fun_of_resolved_st_q_for gs) (Lifted cinit_ivl_st))
        (map_lift (fun_of_resolved_st_q_for gs) (Bot::ivl exec_dg_st lifted)))
     (cfg_exit (compile_prog Pi ps mnm main), ())
     (fun_of_dg_st_gen (map_lift (fun_of_resolved_st_q_for gs)) (map_lift (fun_of_resolved_st_q_for gs))
        \<circ> snd (ictx_sol_per_origin gs is_bot_pred Pi ps mnm main))
     (fst (ictx_sol_per_origin gs is_bot_pred Pi ps mnm main))"
proof -
  have pp'_buf: "part_post_solution
       (side_cfg_T_eff_keyed_seed_dg_buffered intra_predecessor_list (\<lambda>_. Global)
          route_unit
          (routed_cmb_g_contribution (ictx_spec gs is_bot_pred) Global Seed)
          (routed_extra_g Seed Global)
          (compile_prog Pi ps mnm main) (ictx_spec gs is_bot_pred) Bot (Lifted cinit_ivl_st) Bot)
       (cfg_exit (compile_prog Pi ps mnm main), ())
       (snd (ictx_sol_per_origin gs is_bot_pred Pi ps mnm main)) (fst (ictx_sol_per_origin gs is_bot_pred Pi ps mnm main))"
    using ictx_pp_st_per_origin unfolding ictx_eqs_def by simp
  have seed_ne_global: "\<And>p c. Seed p c \<noteq> Global" by simp
  have pp': "part_post_solution
       (side_cfg_T_eff_keyed_seed_dg intra_predecessor_list (\<lambda>_. Global) route_unit
          (routed_cmb_g (ictx_spec gs is_bot_pred) Global Seed)
          (routed_extra_g Seed Global)
          (compile_prog Pi ps mnm main) (ictx_spec gs is_bot_pred) Bot (Lifted cinit_ivl_st) Bot)
       (cfg_exit (compile_prog Pi ps mnm main), ())
       (snd (ictx_sol_per_origin gs is_bot_pred Pi ps mnm main)) (fst (ictx_sol_per_origin gs is_bot_pred Pi ps mnm main))"
  proof (rule part_post_solution_seed_dg_buffered_to_old
      [where cmb_c = "routed_cmb_g_contribution (ictx_spec gs is_bot_pred) Global Seed"])
    show "\<And>c' ca cc ex \<tau>. locals (traverse_rhs
             (routed_cmb_g_contribution (ictx_spec gs is_bot_pred) Global Seed
               route_unit c' ca cc ex) \<tau>)
           = locals (traverse_rhs
             (routed_cmb_g (ictx_spec gs is_bot_pred) Global Seed
               route_unit c' ca cc ex) \<tau>)"
      by (rule routed_cmb_g_contribution_matches_local)
    show "\<And>c' ca cc ex \<tau>. locals (sides_of_rhs
             (routed_cmb_g (ictx_spec gs is_bot_pred) Global Seed
               route_unit c' ca cc ex) \<tau> (Inr ((\<lambda>_. Global) c'))) = bot"
      by (rule routed_cmb_g_side_pure[of Seed Global, OF seed_ne_global])
    show "\<And>c' ca cc ex \<tau>. globs (traverse_rhs
             (routed_cmb_g_contribution (ictx_spec gs is_bot_pred) Global Seed
               route_unit c' ca cc ex) \<tau>)
           = globs (sides_of_rhs
             (routed_cmb_g (ictx_spec gs is_bot_pred) Global Seed
               route_unit c' ca cc ex) \<tau> (Inr ((\<lambda>_. Global) c')))"
      by (rule routed_cmb_g_contribution_matches_global[of Seed Global, OF seed_ne_global])
    show "\<And>c' ca cc ex \<tau>. sides_of_rhs
             (routed_cmb_g_contribution (ictx_spec gs is_bot_pred) Global Seed
               route_unit c' ca cc ex) \<tau> (Inr ((\<lambda>_. Global) c')) = bot"
      by (rule routed_cmb_g_contribution_free_at_key[of Seed Global, OF seed_ne_global])
    show "\<And>c' ca cc ex \<tau> z. z \<noteq> Inr ((\<lambda>_. Global) c') \<Longrightarrow> sides_of_rhs
             (routed_cmb_g_contribution (ictx_spec gs is_bot_pred) Global Seed
               route_unit c' ca cc ex) \<tau> z
           = sides_of_rhs
             (routed_cmb_g (ictx_spec gs is_bot_pred) Global Seed
               route_unit c' ca cc ex) \<tau> z"
      by (rule routed_cmb_g_contribution_sides_off_key[of Seed Global, OF seed_ne_global])
    show "\<And>c' ca cc ex \<tau>. dep_aux \<tau>
             (routed_cmb_g_contribution (ictx_spec gs is_bot_pred) Global Seed
               route_unit c' ca cc ex)
           = dep_aux \<tau>
             (routed_cmb_g (ictx_spec gs is_bot_pred) Global Seed
               route_unit c' ca cc ex)"
      by (rule routed_cmb_g_contribution_dep)
    show "\<And>c' w \<tau> z x. x \<in> set (routed_extra_g Seed Global route_unit c' w)
           \<Longrightarrow> sides_of_rhs x \<tau> z = bot"
      by (rule routed_extra_g_free)
    show "\<And>c' w \<tau> x. x \<in> set (routed_extra_g Seed Global route_unit c' w)
           \<Longrightarrow> globs (traverse_rhs x \<tau>) = bot"
      by (rule routed_extra_g_local_only)
    show "part_post_solution
       (side_cfg_T_eff_keyed_seed_dg_buffered intra_predecessor_list (\<lambda>_. Global)
          route_unit
          (routed_cmb_g_contribution (ictx_spec gs is_bot_pred) Global Seed)
          (routed_extra_g Seed Global)
          (compile_prog Pi ps mnm main) (ictx_spec gs is_bot_pred) Bot (Lifted cinit_ivl_st) Bot)
       (cfg_exit (compile_prog Pi ps mnm main), ())
       (snd (ictx_sol_per_origin gs is_bot_pred Pi ps mnm main)) (fst (ictx_sol_per_origin gs is_bot_pred Pi ps mnm main))"
      by (rule pp'_buf)
  qed
  have ictx_Hstep_ctx:
    "map_prod (map_lift (fun_of_resolved_st_q_for gs)) (map_lift (fun_of_resolved_st_q_for gs))
       (dg_spec_step (ictx_spec gs is_bot_pred) a d g') =
       dg_spec_step (ictx_abs_spec gs) a
         (map_lift (fun_of_resolved_st_q_for gs) d) (map_lift (fun_of_resolved_st_q_for gs) g')" for a d g'
    unfolding ictx_spec_def ictx_abs_spec_def by (rule ictx_Hstep_lifted_for[OF exact])
  show ?thesis
    apply (rule part_post_solution_seed_dg_st_to_abs_lifted_for
          [where gs = gs and pred_sel = intra_predecessor_list and gkey = "\<lambda>_. Global"
             and route_st = "route_unit :: cfg_node \<Rightarrow> unit \<Rightarrow> ivl exec_dg_st lifted \<Rightarrow> call_action \<Rightarrow> unit"
             and route_abs = "route_unit :: cfg_node \<Rightarrow> unit \<Rightarrow> ivl abs_state lifted \<Rightarrow> call_action \<Rightarrow> unit"
             and cmb_st = "routed_cmb_g (ictx_spec gs is_bot_pred) Global Seed"
             and cmb_abs = "routed_cmb_g (ictx_abs_spec gs) Global Seed"
             and extra_st = "routed_extra_g Seed Global"
             and extra_abs = "routed_extra_g Seed Global"
             and g = "compile_prog Pi ps mnm main" and S_st = "ictx_spec gs is_bot_pred" and S_abs = "ictx_abs_spec gs"])
        apply (rule ictx_Hstep_ctx)
       apply (rule route_unit_commute)
      apply (rule dg_tree_st_commute_routed_cmb_g_ictx[OF exact])
     apply (rule hextra_commute_routed_ictx)
    apply (rule pp')
    done
qed

end

section \<open>Activation-indexed collecting soundness, generic per compiled program\<close>

text \<open>
  Executable twins of the context's own \<open>ictx_sigma_abs_per_origin\<close>/\<open>ictx_sg_per_origin\<close> (below),
  defined before that context so their equations are unconditional -- mirrors
  Interval's \<open>entry_state_sigma_abs_exec\<close>/\<open>entry_state_sg_exec\<close> convention
  exactly.
\<close>

definition ictx_sigma_abs_exec_per_origin ::
    "(vname \<Rightarrow> bool) \<Rightarrow> (ivl exec_dg_st \<Rightarrow> bool) \<Rightarrow> proc_table \<Rightarrow> pname list \<Rightarrow> pname \<Rightarrow> com
       \<Rightarrow> pp \<times> unit + gk \<Rightarrow> (ivl abs_state lifted, ivl abs_state lifted) dg_state" where
  "ictx_sigma_abs_exec_per_origin gs is_bot_pred Pi ps mnm main =
     fun_of_dg_st_gen (map_lift (fun_of_resolved_st_q_for gs)) (map_lift (fun_of_resolved_st_q_for gs))
       \<circ> snd (ictx_sol_per_origin gs is_bot_pred Pi ps mnm main)"

definition ictx_sg_exec_per_origin ::
    "(vname \<Rightarrow> bool) \<Rightarrow> (ivl exec_dg_st \<Rightarrow> bool) \<Rightarrow> proc_table \<Rightarrow> pname list \<Rightarrow> pname \<Rightarrow> com
       \<Rightarrow> pp \<times> unit + gk \<Rightarrow> ivl abs_state lifted" where
  "ictx_sg_exec_per_origin gs is_bot_pred Pi ps mnm main k =
     (case k of
        Inl (v, ctx) \<Rightarrow>
          (if (v, ctx) \<in> fst (ictx_sol_per_origin gs is_bot_pred Pi ps mnm main)
           then locals (ictx_sigma_abs_exec_per_origin gs is_bot_pred Pi ps mnm main (Inl (v, ctx)))
           else Bot)
      | Inr _ \<Rightarrow> Bot)"

context
  fixes gs :: "vname \<Rightarrow> bool" and is_bot_pred :: "ivl exec_dg_st \<Rightarrow> bool"
    and Pi :: proc_table and ps :: "pname list" and mnm :: pname and main :: com
  assumes solves: "ictx_terminates_per_origin gs is_bot_pred Pi ps mnm main"
    and exact: "\<And>s. is_bot_pred s = is_bot_state (fun_of_resolved_st_q_for gs s)"
    and entry_cov: "(cfg_entry (compile_prog Pi ps mnm main), ()) \<in> fst (ictx_sol_per_origin gs is_bot_pred Pi ps mnm main)"
    and fwd_ok: "\<And>u a v ctx. (u, ctx) \<in> fst (ictx_sol_per_origin gs is_bot_pred Pi ps mnm main)
                   \<Longrightarrow> (u, a, v) \<in> intra (compile_prog Pi ps mnm main)
                   \<Longrightarrow> (v, ctx) \<in> fst (ictx_sol_per_origin gs is_bot_pred Pi ps mnm main)"
    and call_fwd_ok: "\<And>u ctx dst pars args p cont.
        (u, ctx) \<in> fst (ictx_sol_per_origin gs is_bot_pred Pi ps mnm main)
        \<Longrightarrow> (u, CallEdge dst pars args, FunctionEntry p, cont) \<in> calls (compile_prog Pi ps mnm main)
        \<Longrightarrow> (FunctionEntry p, ()) \<in> fst (ictx_sol_per_origin gs is_bot_pred Pi ps mnm main)"
    and comb_fwd_ok: "\<And>cl c1 dst pars args p cont.
        (cl, c1) \<in> fst (ictx_sol_per_origin gs is_bot_pred Pi ps mnm main)
        \<Longrightarrow> (cl, CallEdge dst pars args, FunctionEntry p, cont) \<in> calls (compile_prog Pi ps mnm main)
        \<Longrightarrow> (cont, c1) \<in> fst (ictx_sol_per_origin gs is_bot_pred Pi ps mnm main)"
begin

subsection \<open>The semantic solution projection\<close>

definition ictx_sigma_abs_per_origin :: "pp \<times> unit + gk \<Rightarrow> (ivl abs_state lifted, ivl abs_state lifted) dg_state" where
  "ictx_sigma_abs_per_origin = ictx_sigma_abs_exec_per_origin gs is_bot_pred Pi ps mnm main"

definition ictx_sg_per_origin :: "pp \<times> unit + gk \<Rightarrow> ivl abs_state lifted" where
  "ictx_sg_per_origin = ictx_sg_exec_per_origin gs is_bot_pred Pi ps mnm main"

lemma ictx_fin_per_origin: "finite (intra (compile_prog Pi ps mnm main))"
  using compile_prog_finite by blast

lemma ictx_finC_per_origin: "finite (calls (compile_prog Pi ps mnm main))"
  using compile_prog_finite by blast

lemma ictx_sg_covered_per_origin:
  "(v, ctx) \<in> fst (ictx_sol_per_origin gs is_bot_pred Pi ps mnm main)
   \<Longrightarrow> ictx_sg_per_origin (Inl (v, ctx)) = locals (ictx_sigma_abs_per_origin (Inl (v, ctx)))"
  by (simp add: ictx_sg_per_origin_def ictx_sg_exec_per_origin_def ictx_sigma_abs_per_origin_def ictx_sigma_abs_exec_per_origin_def)

lemma ictx_sg_uncovered_empty_per_origin:
  "(v, ctx) \<notin> fst (ictx_sol_per_origin gs is_bot_pred Pi ps mnm main)
     \<Longrightarrow> gamma_state_lift (ictx_sg_per_origin (Inl (v, ctx))) = {}"
  by (simp add: ictx_sg_per_origin_def ictx_sg_exec_per_origin_def)

subsection \<open>Instantiating the generic DG-native activation discharge\<close>

interpretation ictx_dg_base_per_origin: sound_dg_spec "ictx_abs_spec gs" gamma_dg_base gs
  unfolding ictx_abs_spec_def
  by (rule base_dg_spec_sound[OF ivl_is_sound_transfer_for is_bot_state_gamma_state_empty])

interpretation ictx_dg_per_origin: dg_ctx_activation_base "ictx_abs_spec gs" gamma_dg_base gs
    "compile_prog Pi ps mnm main" Global route_unit
    "routed_cmb_g (ictx_abs_spec gs) Global Seed"
    "routed_extra_g Seed Global"
    "map_lift (fun_of_resolved_st_q_for gs) (Bot::ivl exec_dg_st lifted)"
    "map_lift (fun_of_resolved_st_q_for gs) (Lifted cinit_ivl_st)"
    "map_lift (fun_of_resolved_st_q_for gs) (Bot::ivl exec_dg_st lifted)"
    ictx_sigma_abs_per_origin "fst (ictx_sol_per_origin gs is_bot_pred Pi ps mnm main)"
    "(cfg_exit (compile_prog Pi ps mnm main), ())" ictx_sg_per_origin gamma_state_lift
proof unfold_locales
  show "finite (intra (compile_prog Pi ps mnm main))" by (rule ictx_fin_per_origin)
next
  show "part_post_solution
          (side_cfg_T_eff_keyed_seed_dg intra_predecessor_list (\<lambda>_. Global) route_unit
             (routed_cmb_g (ictx_abs_spec gs) Global Seed)
             (routed_extra_g Seed Global)
             (compile_prog Pi ps mnm main) (ictx_abs_spec gs)
             (map_lift (fun_of_resolved_st_q_for gs) (Bot::ivl exec_dg_st lifted))
             (map_lift (fun_of_resolved_st_q_for gs) (Lifted cinit_ivl_st))
             (map_lift (fun_of_resolved_st_q_for gs) (Bot::ivl exec_dg_st lifted)))
          (cfg_exit (compile_prog Pi ps mnm main), ()) ictx_sigma_abs_per_origin
          (fst (ictx_sol_per_origin gs is_bot_pred Pi ps mnm main))"
    unfolding ictx_sigma_abs_per_origin_def ictx_sigma_abs_exec_per_origin_def
    by (rule ictx_pp_abs_per_origin[OF solves exact])
next
  fix v ctx assume "(v, ctx) \<in> fst (ictx_sol_per_origin gs is_bot_pred Pi ps mnm main)"
  thus "gamma_state_lift (ictx_sg_per_origin (Inl (v, ctx)))
          = gamma_dg_base (locals (ictx_sigma_abs_per_origin (Inl (v, ctx)))) (globs (ictx_sigma_abs_per_origin (Inr Global)))"
    by (simp add: ictx_sg_covered_per_origin gamma_dg_base_def)
next
  fix v ctx assume "(v, ctx) \<notin> fst (ictx_sol_per_origin gs is_bot_pred Pi ps mnm main)"
  thus "gamma_state_lift (ictx_sg_per_origin (Inl (v, ctx))) = {}"
    by (rule ictx_sg_uncovered_empty_per_origin)
next
  fix u a v ctx assume "(u, ctx) \<in> fst (ictx_sol_per_origin gs is_bot_pred Pi ps mnm main)"
    "(u, a, v) \<in> intra (compile_prog Pi ps mnm main)"
  thus "(v, ctx) \<in> fst (ictx_sol_per_origin gs is_bot_pred Pi ps mnm main)" by (rule fwd_ok)
qed

subsection \<open>The routed interpretation and its CALL/COMB corollaries\<close>

interpretation ictx_routed_per_origin: unit_routed_context "ictx_abs_spec gs" gamma_dg_base gs
    "compile_prog Pi ps mnm main" Global
    "map_lift (fun_of_resolved_st_q_for gs) (Bot::ivl exec_dg_st lifted)"
    "map_lift (fun_of_resolved_st_q_for gs) (Lifted cinit_ivl_st)"
    "map_lift (fun_of_resolved_st_q_for gs) (Bot::ivl exec_dg_st lifted)"
    ictx_sigma_abs_per_origin "fst (ictx_sol_per_origin gs is_bot_pred Pi ps mnm main)"
    "(cfg_exit (compile_prog Pi ps mnm main), ())" ictx_sg_per_origin
    Seed gamma_state_lift
proof (unfold_locales, goal_cases FinC SeedKey CallFwd CombFwd EnterAgree)
  case FinC show ?case by (rule ictx_finC_per_origin)
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
      ce': "(cl, CallEdge dst' pars' args', FunctionEntry p', cont') \<in> calls (compile_prog Pi ps mnm main)"
    and es_eq: "es = call_enter gs (CallEdge dst' pars' args') s"
    using ces unfolding call_enter_store_def by blast
  have "CallEdge dst' pars' args' = CallEdge dst pars args"
    using compile_prog_calls_source_unique[OF ce' ce] by simp
  thus ?case using es_eq by simp
qed

subsection \<open>Activation-indexed collecting soundness\<close>

lemma ictx_cinit_le_cinit_ivl_st_per_origin:
  "cinit_stores gs \<subseteq> gamma_state_lift (map_lift (fun_of_resolved_st_q_for gs) (Lifted cinit_ivl_st))"
  by (auto simp: cinit_stores_def gamma_state_def fun_of_resolved_st_q_for_def fun_of_st_cinit_ivl_st)

subsection \<open>The generic report adapter\<close>

interpretation ictx_adapter_per_origin: dg_analysis_adapter enterc_unit "ictx_abs_spec gs" gs
    "compile_prog Pi ps mnm main" Global route_unit
    "map_lift (fun_of_resolved_st_q_for gs) (Bot::ivl exec_dg_st lifted)"
    "map_lift (fun_of_resolved_st_q_for gs) (Lifted cinit_ivl_st)"
    "map_lift (fun_of_resolved_st_q_for gs) (Bot::ivl exec_dg_st lifted)"
    ictx_sigma_abs_per_origin "fst (ictx_sol_per_origin gs is_bot_pred Pi ps mnm main)"
    "(cfg_exit (compile_prog Pi ps mnm main), ())" ictx_sg_per_origin
    Seed interval_classify_check
proof (unfold_locales, goal_cases FinE PP SgCov SgUncov Fwd FinC SeedKey RouteEnterc CallFwd CombFwd EnterAgree ClProved ClRefuted)
  case FinE show ?case by (rule ictx_fin_per_origin)
next
  case PP show ?case
    unfolding ictx_sigma_abs_per_origin_def ictx_sigma_abs_exec_per_origin_def by (rule ictx_pp_abs_per_origin[OF solves exact])
next
  case (SgCov v c)
  thus ?case
    by (simp add: ictx_sg_covered_per_origin gamma_dg_base_def)
next
  case (SgUncov v c)
  thus ?case by (rule ictx_sg_uncovered_empty_per_origin)
next
  case (Fwd u a v c)
  thus ?case by (rule fwd_ok)
next
  case FinC show ?case by (rule ictx_finC_per_origin)
next
  case (SeedKey p ctx) show ?case by simp
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
      ce': "(cl, CallEdge dst' pars' args', FunctionEntry p', cont') \<in> calls (compile_prog Pi ps mnm main)"
    and es_eq: "es = call_enter gs (CallEdge dst' pars' args') s"
    using ces unfolding call_enter_store_def by blast
  have "CallEdge dst' pars' args' = CallEdge dst pars args"
    using compile_prog_calls_source_unique[OF ce' ce] by simp
  thus ?case using es_eq by simp
next
  case (ClProved c d s)
  thus ?case by (rule interval_classify_check_proved)
next
  case (ClRefuted c d s)
  thus ?case by (rule interval_classify_check_refuted)
qed

lemmas ictx_report_ctx_proved_sound_per_origin = ictx_adapter_per_origin.analyse_report_ctx_proved_sound
lemmas ictx_report_ctx_refuted_sound_per_origin = ictx_adapter_per_origin.analyse_report_ctx_refuted_sound

text \<open>
  \<open>ictx_result_node_sound_per_origin\<close> re-exports the adapter's generic node-soundness
  bridge (\<^theory>\<open>Voblint_Core.DG_Analysis_Adapter\<close>). \<open>ictx_analyse_result_eq_per_origin\<close>
  identifies that reading with the raw-tuple shape
  \<open>analyse_interval_ctx_result_per_origin_for\<close> (defined below) already builds by hand,
  mirroring \<open>ictx_analyse_result_eq_warrow\<close>.
\<close>

lemmas ictx_result_node_sound_per_origin = ictx_adapter_per_origin.analyse_result_node_sound

lemma ictx_analyse_result_eq_per_origin:
  "lookup_context ictx_adapter_per_origin.analyse_result v ctx =
     (if (v, ctx) \<in> fst (ictx_sol_per_origin gs is_bot_pred Pi ps mnm main)
      then normalize_point gs
             (canonicalize_lift is_bot_pred
               (locals (snd (ictx_sol_per_origin gs is_bot_pred Pi ps mnm main) (Inl (v, ctx)))))
      else Unreachable)"
  unfolding ictx_adapter_per_origin.lookup_context_analyse_result
  apply (simp only: ictx_sigma_abs_per_origin_def ictx_sigma_abs_exec_per_origin_def o_apply
                     fun_of_dg_st_gen_simps(1))
  by (cases "locals (snd (ictx_sol_per_origin gs is_bot_pred Pi ps mnm main) (Inl (v, ctx)))")
     (simp_all add: exact normalize_lift_def)

end

section \<open>Apinis warrowing solver instantiation, at the same routed unit-context spec\<close>

text \<open>
  Interval production's default solver: mirrors the always-join instantiation above under
  \<^const>\<open>TD_side_warrowing_apinis_Interp_solve\<close> instead, solving the exact same \<open>ictx_eqs\<close>
  equation system -- exactly as Interval's own entry-state contextual mode
  (\<open>Interval_Exec_Ctx_Sound\<close>) already does. That file's own soundness derivation needs no
  \<open>ivl_widen_bot_bot\<close>/\<open>ivl_narrow_bot_bot\<close> bridging fact: those facts are needed only by the
  Base family's separate \<open>restrict_global_resolved_q\<close> bookkeeping for its flow-insensitive
  global slot (\<^theory>\<open>Voblint_Analysis.Interval_Exec_Sound\<close>), which the routed spine's
  keyed-seed \<open>Global\<close>/\<open>Seed\<close> globals replace outright. \<open>TD_side_upd_rule\<close>'s
  \<open>solve_dom\<close>/\<open>partial_post_solution\<close> being locale-generic over the update rule (as for
  PerOrigin above) is exactly what makes this a mechanical solver-call swap here too.
\<close>

definition ictx_sol_warrow ::
    "(vname \<Rightarrow> bool) \<Rightarrow> (ivl exec_dg_st \<Rightarrow> bool) \<Rightarrow> proc_table \<Rightarrow> pname list \<Rightarrow> pname \<Rightarrow> com
       \<Rightarrow> (pp \<times> unit) set \<times> (pp \<times> unit + gk \<Rightarrow> (ivl exec_dg_st lifted, ivl exec_dg_st lifted) dg_state)" where
  "ictx_sol_warrow gs is_bot_pred Pi ps mnm main =
     TD_side_warrowing_apinis_Interp_solve (ictx_eqs gs is_bot_pred Pi ps mnm main)
       (cfg_exit (compile_prog Pi ps mnm main), ())"

definition ictx_terminates_warrow ::
    "(vname \<Rightarrow> bool) \<Rightarrow> (ivl exec_dg_st \<Rightarrow> bool) \<Rightarrow> proc_table \<Rightarrow> pname list \<Rightarrow> pname \<Rightarrow> com \<Rightarrow> bool" where
  "ictx_terminates_warrow gs is_bot_pred Pi ps mnm main =
     TD_side_warrowing_apinis_Interp.solve_dom TYPE(gk) TYPE((ivl exec_dg_st lifted, ivl exec_dg_st lifted) dg_state)
       (ictx_eqs gs is_bot_pred Pi ps mnm main) (cfg_exit (compile_prog Pi ps mnm main), ())"

lemma ictx_terminates_warrow_via_solve_c:
  assumes "TD_side_warrowing_apinis_Interp_solve_c (ictx_eqs gs is_bot_pred Pi ps mnm main)
             (cfg_exit (compile_prog Pi ps mnm main), ()) \<noteq> None"
  shows "ictx_terminates_warrow gs is_bot_pred Pi ps mnm main"
  unfolding ictx_terminates_warrow_def TD_side_warrowing_apinis_Interp.term_equivalence
            TD_side_warrowing_apinis_Interp.solve_c_dom_def
  using assms by simp

subsection \<open>The certified executable post-solution, generic per compiled program\<close>

context
  fixes gs :: "vname \<Rightarrow> bool" and is_bot_pred :: "ivl exec_dg_st \<Rightarrow> bool"
    and Pi :: proc_table and ps :: "pname list" and mnm :: pname and main :: com
  assumes solves: "ictx_terminates_warrow gs is_bot_pred Pi ps mnm main"
    and exact: "\<And>s. is_bot_pred s = is_bot_state (fun_of_resolved_st_q_for gs s)"
begin

lemma ictx_solve_dom_warrow:
  "TD_side_warrowing_apinis_Interp.solve_dom TYPE(gk) TYPE((ivl exec_dg_st lifted, ivl exec_dg_st lifted) dg_state)
     (ictx_eqs gs is_bot_pred Pi ps mnm main) (cfg_exit (compile_prog Pi ps mnm main), ())"
  using solves
  unfolding ictx_terminates_warrow_def TD_side_warrowing_apinis_Interp.term_equivalence
            TD_side_warrowing_apinis_Interp.solve_c_dom_def
  by simp

lemma ictx_pp_st_warrow:
  "part_post_solution (ictx_eqs gs is_bot_pred Pi ps mnm main) (cfg_exit (compile_prog Pi ps mnm main), ())
     (snd (ictx_sol_warrow gs is_bot_pred Pi ps mnm main)) (fst (ictx_sol_warrow gs is_bot_pred Pi ps mnm main))"
  using TD_side_upd_rule.TD_side_warrowing_apinis_Interp.partial_post_solution
          [OF ictx_solve_dom_warrow, of "fst (ictx_sol_warrow gs is_bot_pred Pi ps mnm main)"
             "snd (ictx_sol_warrow gs is_bot_pred Pi ps mnm main)"]
  unfolding ictx_sol_warrow_def by simp

theorem ictx_pp_abs_warrow:
  "part_post_solution
     (side_cfg_T_eff_keyed_seed_dg intra_predecessor_list (\<lambda>_. Global) route_unit
        (routed_cmb_g (ictx_abs_spec gs) Global Seed)
        (routed_extra_g Seed Global)
        (compile_prog Pi ps mnm main) (ictx_abs_spec gs)
        (map_lift (fun_of_resolved_st_q_for gs) (Bot::ivl exec_dg_st lifted))
        (map_lift (fun_of_resolved_st_q_for gs) (Lifted cinit_ivl_st))
        (map_lift (fun_of_resolved_st_q_for gs) (Bot::ivl exec_dg_st lifted)))
     (cfg_exit (compile_prog Pi ps mnm main), ())
     (fun_of_dg_st_gen (map_lift (fun_of_resolved_st_q_for gs)) (map_lift (fun_of_resolved_st_q_for gs))
        \<circ> snd (ictx_sol_warrow gs is_bot_pred Pi ps mnm main))
     (fst (ictx_sol_warrow gs is_bot_pred Pi ps mnm main))"
proof -
  have pp'_buf: "part_post_solution
       (side_cfg_T_eff_keyed_seed_dg_buffered intra_predecessor_list (\<lambda>_. Global)
          route_unit
          (routed_cmb_g_contribution (ictx_spec gs is_bot_pred) Global Seed)
          (routed_extra_g Seed Global)
          (compile_prog Pi ps mnm main) (ictx_spec gs is_bot_pred) Bot (Lifted cinit_ivl_st) Bot)
       (cfg_exit (compile_prog Pi ps mnm main), ())
       (snd (ictx_sol_warrow gs is_bot_pred Pi ps mnm main)) (fst (ictx_sol_warrow gs is_bot_pred Pi ps mnm main))"
    using ictx_pp_st_warrow unfolding ictx_eqs_def by simp
  have seed_ne_global: "\<And>p c. Seed p c \<noteq> Global" by simp
  have pp': "part_post_solution
       (side_cfg_T_eff_keyed_seed_dg intra_predecessor_list (\<lambda>_. Global) route_unit
          (routed_cmb_g (ictx_spec gs is_bot_pred) Global Seed)
          (routed_extra_g Seed Global)
          (compile_prog Pi ps mnm main) (ictx_spec gs is_bot_pred) Bot (Lifted cinit_ivl_st) Bot)
       (cfg_exit (compile_prog Pi ps mnm main), ())
       (snd (ictx_sol_warrow gs is_bot_pred Pi ps mnm main)) (fst (ictx_sol_warrow gs is_bot_pred Pi ps mnm main))"
  proof (rule part_post_solution_seed_dg_buffered_to_old
      [where cmb_c = "routed_cmb_g_contribution (ictx_spec gs is_bot_pred) Global Seed"])
    show "\<And>c' ca cc ex \<tau>. locals (traverse_rhs
             (routed_cmb_g_contribution (ictx_spec gs is_bot_pred) Global Seed
               route_unit c' ca cc ex) \<tau>)
           = locals (traverse_rhs
             (routed_cmb_g (ictx_spec gs is_bot_pred) Global Seed
               route_unit c' ca cc ex) \<tau>)"
      by (rule routed_cmb_g_contribution_matches_local)
    show "\<And>c' ca cc ex \<tau>. locals (sides_of_rhs
             (routed_cmb_g (ictx_spec gs is_bot_pred) Global Seed
               route_unit c' ca cc ex) \<tau> (Inr ((\<lambda>_. Global) c'))) = bot"
      by (rule routed_cmb_g_side_pure[of Seed Global, OF seed_ne_global])
    show "\<And>c' ca cc ex \<tau>. globs (traverse_rhs
             (routed_cmb_g_contribution (ictx_spec gs is_bot_pred) Global Seed
               route_unit c' ca cc ex) \<tau>)
           = globs (sides_of_rhs
             (routed_cmb_g (ictx_spec gs is_bot_pred) Global Seed
               route_unit c' ca cc ex) \<tau> (Inr ((\<lambda>_. Global) c')))"
      by (rule routed_cmb_g_contribution_matches_global[of Seed Global, OF seed_ne_global])
    show "\<And>c' ca cc ex \<tau>. sides_of_rhs
             (routed_cmb_g_contribution (ictx_spec gs is_bot_pred) Global Seed
               route_unit c' ca cc ex) \<tau> (Inr ((\<lambda>_. Global) c')) = bot"
      by (rule routed_cmb_g_contribution_free_at_key[of Seed Global, OF seed_ne_global])
    show "\<And>c' ca cc ex \<tau> z. z \<noteq> Inr ((\<lambda>_. Global) c') \<Longrightarrow> sides_of_rhs
             (routed_cmb_g_contribution (ictx_spec gs is_bot_pred) Global Seed
               route_unit c' ca cc ex) \<tau> z
           = sides_of_rhs
             (routed_cmb_g (ictx_spec gs is_bot_pred) Global Seed
               route_unit c' ca cc ex) \<tau> z"
      by (rule routed_cmb_g_contribution_sides_off_key[of Seed Global, OF seed_ne_global])
    show "\<And>c' ca cc ex \<tau>. dep_aux \<tau>
             (routed_cmb_g_contribution (ictx_spec gs is_bot_pred) Global Seed
               route_unit c' ca cc ex)
           = dep_aux \<tau>
             (routed_cmb_g (ictx_spec gs is_bot_pred) Global Seed
               route_unit c' ca cc ex)"
      by (rule routed_cmb_g_contribution_dep)
    show "\<And>c' w \<tau> z x. x \<in> set (routed_extra_g Seed Global route_unit c' w)
           \<Longrightarrow> sides_of_rhs x \<tau> z = bot"
      by (rule routed_extra_g_free)
    show "\<And>c' w \<tau> x. x \<in> set (routed_extra_g Seed Global route_unit c' w)
           \<Longrightarrow> globs (traverse_rhs x \<tau>) = bot"
      by (rule routed_extra_g_local_only)
    show "part_post_solution
       (side_cfg_T_eff_keyed_seed_dg_buffered intra_predecessor_list (\<lambda>_. Global)
          route_unit
          (routed_cmb_g_contribution (ictx_spec gs is_bot_pred) Global Seed)
          (routed_extra_g Seed Global)
          (compile_prog Pi ps mnm main) (ictx_spec gs is_bot_pred) Bot (Lifted cinit_ivl_st) Bot)
       (cfg_exit (compile_prog Pi ps mnm main), ())
       (snd (ictx_sol_warrow gs is_bot_pred Pi ps mnm main)) (fst (ictx_sol_warrow gs is_bot_pred Pi ps mnm main))"
      by (rule pp'_buf)
  qed
  have ictx_Hstep_ctx:
    "map_prod (map_lift (fun_of_resolved_st_q_for gs)) (map_lift (fun_of_resolved_st_q_for gs))
       (dg_spec_step (ictx_spec gs is_bot_pred) a d g') =
       dg_spec_step (ictx_abs_spec gs) a
         (map_lift (fun_of_resolved_st_q_for gs) d) (map_lift (fun_of_resolved_st_q_for gs) g')" for a d g'
    unfolding ictx_spec_def ictx_abs_spec_def by (rule ictx_Hstep_lifted_for[OF exact])
  show ?thesis
    apply (rule part_post_solution_seed_dg_st_to_abs_lifted_for
          [where gs = gs and pred_sel = intra_predecessor_list and gkey = "\<lambda>_. Global"
             and route_st = "route_unit :: cfg_node \<Rightarrow> unit \<Rightarrow> ivl exec_dg_st lifted \<Rightarrow> call_action \<Rightarrow> unit"
             and route_abs = "route_unit :: cfg_node \<Rightarrow> unit \<Rightarrow> ivl abs_state lifted \<Rightarrow> call_action \<Rightarrow> unit"
             and cmb_st = "routed_cmb_g (ictx_spec gs is_bot_pred) Global Seed"
             and cmb_abs = "routed_cmb_g (ictx_abs_spec gs) Global Seed"
             and extra_st = "routed_extra_g Seed Global"
             and extra_abs = "routed_extra_g Seed Global"
             and g = "compile_prog Pi ps mnm main" and S_st = "ictx_spec gs is_bot_pred" and S_abs = "ictx_abs_spec gs"])
        apply (rule ictx_Hstep_ctx)
       apply (rule route_unit_commute)
      apply (rule dg_tree_st_commute_routed_cmb_g_ictx[OF exact])
     apply (rule hextra_commute_routed_ictx)
    apply (rule pp')
    done
qed

end

section \<open>Activation-indexed collecting soundness, generic per compiled program\<close>

text \<open>
  Executable twins of the context's own \<open>ictx_sigma_abs_warrow\<close>/\<open>ictx_sg_warrow\<close> (below),
  defined before that context so their equations are unconditional -- mirrors
  Interval's \<open>entry_state_sigma_abs_exec\<close>/\<open>entry_state_sg_exec\<close> convention
  exactly.
\<close>

definition ictx_sigma_abs_exec_warrow ::
    "(vname \<Rightarrow> bool) \<Rightarrow> (ivl exec_dg_st \<Rightarrow> bool) \<Rightarrow> proc_table \<Rightarrow> pname list \<Rightarrow> pname \<Rightarrow> com
       \<Rightarrow> pp \<times> unit + gk \<Rightarrow> (ivl abs_state lifted, ivl abs_state lifted) dg_state" where
  "ictx_sigma_abs_exec_warrow gs is_bot_pred Pi ps mnm main =
     fun_of_dg_st_gen (map_lift (fun_of_resolved_st_q_for gs)) (map_lift (fun_of_resolved_st_q_for gs))
       \<circ> snd (ictx_sol_warrow gs is_bot_pred Pi ps mnm main)"

definition ictx_sg_exec_warrow ::
    "(vname \<Rightarrow> bool) \<Rightarrow> (ivl exec_dg_st \<Rightarrow> bool) \<Rightarrow> proc_table \<Rightarrow> pname list \<Rightarrow> pname \<Rightarrow> com
       \<Rightarrow> pp \<times> unit + gk \<Rightarrow> ivl abs_state lifted" where
  "ictx_sg_exec_warrow gs is_bot_pred Pi ps mnm main k =
     (case k of
        Inl (v, ctx) \<Rightarrow>
          (if (v, ctx) \<in> fst (ictx_sol_warrow gs is_bot_pred Pi ps mnm main)
           then locals (ictx_sigma_abs_exec_warrow gs is_bot_pred Pi ps mnm main (Inl (v, ctx)))
           else Bot)
      | Inr _ \<Rightarrow> Bot)"

context
  fixes gs :: "vname \<Rightarrow> bool" and is_bot_pred :: "ivl exec_dg_st \<Rightarrow> bool"
    and Pi :: proc_table and ps :: "pname list" and mnm :: pname and main :: com
  assumes solves: "ictx_terminates_warrow gs is_bot_pred Pi ps mnm main"
    and exact: "\<And>s. is_bot_pred s = is_bot_state (fun_of_resolved_st_q_for gs s)"
    and entry_cov: "(cfg_entry (compile_prog Pi ps mnm main), ()) \<in> fst (ictx_sol_warrow gs is_bot_pred Pi ps mnm main)"
    and fwd_ok: "\<And>u a v ctx. (u, ctx) \<in> fst (ictx_sol_warrow gs is_bot_pred Pi ps mnm main)
                   \<Longrightarrow> (u, a, v) \<in> intra (compile_prog Pi ps mnm main)
                   \<Longrightarrow> (v, ctx) \<in> fst (ictx_sol_warrow gs is_bot_pred Pi ps mnm main)"
    and call_fwd_ok: "\<And>u ctx dst pars args p cont.
        (u, ctx) \<in> fst (ictx_sol_warrow gs is_bot_pred Pi ps mnm main)
        \<Longrightarrow> (u, CallEdge dst pars args, FunctionEntry p, cont) \<in> calls (compile_prog Pi ps mnm main)
        \<Longrightarrow> (FunctionEntry p, ()) \<in> fst (ictx_sol_warrow gs is_bot_pred Pi ps mnm main)"
    and comb_fwd_ok: "\<And>cl c1 dst pars args p cont.
        (cl, c1) \<in> fst (ictx_sol_warrow gs is_bot_pred Pi ps mnm main)
        \<Longrightarrow> (cl, CallEdge dst pars args, FunctionEntry p, cont) \<in> calls (compile_prog Pi ps mnm main)
        \<Longrightarrow> (cont, c1) \<in> fst (ictx_sol_warrow gs is_bot_pred Pi ps mnm main)"
begin

subsection \<open>The semantic solution projection\<close>

definition ictx_sigma_abs_warrow :: "pp \<times> unit + gk \<Rightarrow> (ivl abs_state lifted, ivl abs_state lifted) dg_state" where
  "ictx_sigma_abs_warrow = ictx_sigma_abs_exec_warrow gs is_bot_pred Pi ps mnm main"

definition ictx_sg_warrow :: "pp \<times> unit + gk \<Rightarrow> ivl abs_state lifted" where
  "ictx_sg_warrow = ictx_sg_exec_warrow gs is_bot_pred Pi ps mnm main"

lemma ictx_fin_warrow: "finite (intra (compile_prog Pi ps mnm main))"
  using compile_prog_finite by blast

lemma ictx_finC_warrow: "finite (calls (compile_prog Pi ps mnm main))"
  using compile_prog_finite by blast

lemma ictx_sg_covered_warrow:
  "(v, ctx) \<in> fst (ictx_sol_warrow gs is_bot_pred Pi ps mnm main)
   \<Longrightarrow> ictx_sg_warrow (Inl (v, ctx)) = locals (ictx_sigma_abs_warrow (Inl (v, ctx)))"
  by (simp add: ictx_sg_warrow_def ictx_sg_exec_warrow_def ictx_sigma_abs_warrow_def ictx_sigma_abs_exec_warrow_def)

lemma ictx_sg_uncovered_empty_warrow:
  "(v, ctx) \<notin> fst (ictx_sol_warrow gs is_bot_pred Pi ps mnm main)
     \<Longrightarrow> gamma_state_lift (ictx_sg_warrow (Inl (v, ctx))) = {}"
  by (simp add: ictx_sg_warrow_def ictx_sg_exec_warrow_def)

subsection \<open>Instantiating the generic DG-native activation discharge\<close>

interpretation ictx_dg_base_warrow: sound_dg_spec "ictx_abs_spec gs" gamma_dg_base gs
  unfolding ictx_abs_spec_def
  by (rule base_dg_spec_sound[OF ivl_is_sound_transfer_for is_bot_state_gamma_state_empty])

interpretation ictx_dg_warrow: dg_ctx_activation_base "ictx_abs_spec gs" gamma_dg_base gs
    "compile_prog Pi ps mnm main" Global route_unit
    "routed_cmb_g (ictx_abs_spec gs) Global Seed"
    "routed_extra_g Seed Global"
    "map_lift (fun_of_resolved_st_q_for gs) (Bot::ivl exec_dg_st lifted)"
    "map_lift (fun_of_resolved_st_q_for gs) (Lifted cinit_ivl_st)"
    "map_lift (fun_of_resolved_st_q_for gs) (Bot::ivl exec_dg_st lifted)"
    ictx_sigma_abs_warrow "fst (ictx_sol_warrow gs is_bot_pred Pi ps mnm main)"
    "(cfg_exit (compile_prog Pi ps mnm main), ())" ictx_sg_warrow gamma_state_lift
proof unfold_locales
  show "finite (intra (compile_prog Pi ps mnm main))" by (rule ictx_fin_warrow)
next
  show "part_post_solution
          (side_cfg_T_eff_keyed_seed_dg intra_predecessor_list (\<lambda>_. Global) route_unit
             (routed_cmb_g (ictx_abs_spec gs) Global Seed)
             (routed_extra_g Seed Global)
             (compile_prog Pi ps mnm main) (ictx_abs_spec gs)
             (map_lift (fun_of_resolved_st_q_for gs) (Bot::ivl exec_dg_st lifted))
             (map_lift (fun_of_resolved_st_q_for gs) (Lifted cinit_ivl_st))
             (map_lift (fun_of_resolved_st_q_for gs) (Bot::ivl exec_dg_st lifted)))
          (cfg_exit (compile_prog Pi ps mnm main), ()) ictx_sigma_abs_warrow
          (fst (ictx_sol_warrow gs is_bot_pred Pi ps mnm main))"
    unfolding ictx_sigma_abs_warrow_def ictx_sigma_abs_exec_warrow_def
    by (rule ictx_pp_abs_warrow[OF solves exact])
next
  fix v ctx assume "(v, ctx) \<in> fst (ictx_sol_warrow gs is_bot_pred Pi ps mnm main)"
  thus "gamma_state_lift (ictx_sg_warrow (Inl (v, ctx)))
          = gamma_dg_base (locals (ictx_sigma_abs_warrow (Inl (v, ctx)))) (globs (ictx_sigma_abs_warrow (Inr Global)))"
    by (simp add: ictx_sg_covered_warrow gamma_dg_base_def)
next
  fix v ctx assume "(v, ctx) \<notin> fst (ictx_sol_warrow gs is_bot_pred Pi ps mnm main)"
  thus "gamma_state_lift (ictx_sg_warrow (Inl (v, ctx))) = {}"
    by (rule ictx_sg_uncovered_empty_warrow)
next
  fix u a v ctx assume "(u, ctx) \<in> fst (ictx_sol_warrow gs is_bot_pred Pi ps mnm main)"
    "(u, a, v) \<in> intra (compile_prog Pi ps mnm main)"
  thus "(v, ctx) \<in> fst (ictx_sol_warrow gs is_bot_pred Pi ps mnm main)" by (rule fwd_ok)
qed

subsection \<open>The routed interpretation and its CALL/COMB corollaries\<close>

interpretation ictx_routed_warrow: unit_routed_context "ictx_abs_spec gs" gamma_dg_base gs
    "compile_prog Pi ps mnm main" Global
    "map_lift (fun_of_resolved_st_q_for gs) (Bot::ivl exec_dg_st lifted)"
    "map_lift (fun_of_resolved_st_q_for gs) (Lifted cinit_ivl_st)"
    "map_lift (fun_of_resolved_st_q_for gs) (Bot::ivl exec_dg_st lifted)"
    ictx_sigma_abs_warrow "fst (ictx_sol_warrow gs is_bot_pred Pi ps mnm main)"
    "(cfg_exit (compile_prog Pi ps mnm main), ())" ictx_sg_warrow
    Seed gamma_state_lift
proof (unfold_locales, goal_cases FinC SeedKey CallFwd CombFwd EnterAgree)
  case FinC show ?case by (rule ictx_finC_warrow)
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
      ce': "(cl, CallEdge dst' pars' args', FunctionEntry p', cont') \<in> calls (compile_prog Pi ps mnm main)"
    and es_eq: "es = call_enter gs (CallEdge dst' pars' args') s"
    using ces unfolding call_enter_store_def by blast
  have "CallEdge dst' pars' args' = CallEdge dst pars args"
    using compile_prog_calls_source_unique[OF ce' ce] by simp
  thus ?case using es_eq by simp
qed

subsection \<open>Activation-indexed collecting soundness\<close>

lemma ictx_cinit_le_cinit_ivl_st_warrow:
  "cinit_stores gs \<subseteq> gamma_state_lift (map_lift (fun_of_resolved_st_q_for gs) (Lifted cinit_ivl_st))"
  by (auto simp: cinit_stores_def gamma_state_def fun_of_resolved_st_q_for_def fun_of_st_cinit_ivl_st)

subsection \<open>The generic report adapter\<close>

interpretation ictx_adapter_warrow: dg_analysis_adapter enterc_unit "ictx_abs_spec gs" gs
    "compile_prog Pi ps mnm main" Global route_unit
    "map_lift (fun_of_resolved_st_q_for gs) (Bot::ivl exec_dg_st lifted)"
    "map_lift (fun_of_resolved_st_q_for gs) (Lifted cinit_ivl_st)"
    "map_lift (fun_of_resolved_st_q_for gs) (Bot::ivl exec_dg_st lifted)"
    ictx_sigma_abs_warrow "fst (ictx_sol_warrow gs is_bot_pred Pi ps mnm main)"
    "(cfg_exit (compile_prog Pi ps mnm main), ())" ictx_sg_warrow
    Seed interval_classify_check
proof (unfold_locales, goal_cases FinE PP SgCov SgUncov Fwd FinC SeedKey RouteEnterc CallFwd CombFwd EnterAgree ClProved ClRefuted)
  case FinE show ?case by (rule ictx_fin_warrow)
next
  case PP show ?case
    unfolding ictx_sigma_abs_warrow_def ictx_sigma_abs_exec_warrow_def by (rule ictx_pp_abs_warrow[OF solves exact])
next
  case (SgCov v c)
  thus ?case
    by (simp add: ictx_sg_covered_warrow gamma_dg_base_def)
next
  case (SgUncov v c)
  thus ?case by (rule ictx_sg_uncovered_empty_warrow)
next
  case (Fwd u a v c)
  thus ?case by (rule fwd_ok)
next
  case FinC show ?case by (rule ictx_finC_warrow)
next
  case (SeedKey p ctx) show ?case by simp
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
      ce': "(cl, CallEdge dst' pars' args', FunctionEntry p', cont') \<in> calls (compile_prog Pi ps mnm main)"
    and es_eq: "es = call_enter gs (CallEdge dst' pars' args') s"
    using ces unfolding call_enter_store_def by blast
  have "CallEdge dst' pars' args' = CallEdge dst pars args"
    using compile_prog_calls_source_unique[OF ce' ce] by simp
  thus ?case using es_eq by simp
next
  case (ClProved c d s)
  thus ?case by (rule interval_classify_check_proved)
next
  case (ClRefuted c d s)
  thus ?case by (rule interval_classify_check_refuted)
qed

lemmas ictx_report_ctx_proved_sound_warrow = ictx_adapter_warrow.analyse_report_ctx_proved_sound
lemmas ictx_report_ctx_refuted_sound_warrow = ictx_adapter_warrow.analyse_report_ctx_refuted_sound

text \<open>
  \<open>ictx_result_node_sound_warrow\<close> re-exports the adapter's generic node-soundness bridge
  (\<^theory>\<open>Voblint_Core.DG_Analysis_Adapter\<close>). \<open>ictx_analyse_result_eq_warrow\<close> identifies that
  reading with the raw-tuple shape \<open>analyse_interval_ctx_result_warrow_for\<close> (defined below)
  already builds by hand, mirroring \<open>Sign_Checks.sctx_analyse_result_eq\<close>.
\<close>

lemmas ictx_result_node_sound_warrow = ictx_adapter_warrow.analyse_result_node_sound

lemma ictx_analyse_result_eq_warrow:
  "lookup_context ictx_adapter_warrow.analyse_result v ctx =
     (if (v, ctx) \<in> fst (ictx_sol_warrow gs is_bot_pred Pi ps mnm main)
      then normalize_point gs
             (canonicalize_lift is_bot_pred (locals (snd (ictx_sol_warrow gs is_bot_pred Pi ps mnm main) (Inl (v, ctx)))))
      else Unreachable)"
  unfolding ictx_adapter_warrow.lookup_context_analyse_result
  apply (simp only: ictx_sigma_abs_warrow_def ictx_sigma_abs_exec_warrow_def o_apply fun_of_dg_st_gen_simps(1))
  by (cases "locals (snd (ictx_sol_warrow gs is_bot_pred Pi ps mnm main) (Inl (v, ctx)))")
     (simp_all add: exact normalize_lift_def)

end

section \<open>Solved-result table\<close>

text \<open>
  Whole-program convenience layer, interpreting \<^locale>\<open>dg_analysis_adapter\<close>
  directly rather than hand-rolling a temporary adapter the way Sign's own file (predating that
  locale) had to. \<open>ictx_eqs_prog\<close>/\<open>ictx_sol_prog\<close>/\<open>ictx_terminates_prog\<close> mirror
  Interval's own \<open>entry_state_eqs_prog\<close>/\<open>entry_state_sol_prog\<close>/
  \<open>entry_state_terminates_prog\<close>.
\<close>

definition ictx_eqs_prog ::
    "(vname \<Rightarrow> bool) \<Rightarrow> pname \<Rightarrow> imp_prog
       \<Rightarrow> (pp \<times> unit, gk, (ivl exec_dg_st lifted, ivl exec_dg_st lifted) dg_state) eqsT" where
  "ictx_eqs_prog gs mnm p =
     ictx_eqs gs (resolved_st_q_is_bot_for (declared_global_vars p))
       (prog_table p) (prog_procs p) mnm (prog_main p)"

definition ictx_sol_prog ::
    "(vname \<Rightarrow> bool) \<Rightarrow> pname \<Rightarrow> imp_prog
       \<Rightarrow> (pp \<times> unit) set \<times> (pp \<times> unit + gk \<Rightarrow> (ivl exec_dg_st lifted, ivl exec_dg_st lifted) dg_state)" where
  "ictx_sol_prog gs mnm p =
     TD_side_always_join_Interp_solve (ictx_eqs_prog gs mnm p) (cfg_exit (prog_cfg mnm p), ())"

definition ictx_terminates_prog :: "(vname \<Rightarrow> bool) \<Rightarrow> pname \<Rightarrow> imp_prog \<Rightarrow> bool" where
  "ictx_terminates_prog gs mnm p =
     ictx_terminates gs (resolved_st_q_is_bot_for (declared_global_vars p))
       (prog_table p) (prog_procs p) mnm (prog_main p)"

lemma ictx_terminates_prog_via_solve_c:
  assumes "TD_side_always_join_Interp_solve_c
             (ictx_eqs gs (resolved_st_q_is_bot_for (declared_global_vars p))
                (prog_table p) (prog_procs p) mnm (prog_main p))
             (cfg_exit (compile_prog (prog_table p) (prog_procs p) mnm (prog_main p)), ()) \<noteq> None"
  shows "ictx_terminates_prog gs mnm p"
  unfolding ictx_terminates_prog_def
  using assms by (rule ictx_terminates_via_solve_c)

definition analyse_interval_ctx_result_for ::
    "(vname \<Rightarrow> bool) \<Rightarrow> pname \<Rightarrow> imp_prog \<Rightarrow> (unit, ivl abs_state) analysis_result" where
  "analyse_interval_ctx_result_for gs mnm p =
     Analysis_Result
       (fst (ictx_sol_prog gs mnm p))
       (\<lambda>v ctx. normalize_point gs
                  (canonicalize_lift (resolved_st_q_is_bot_for (declared_global_vars p))
                    (locals (snd (ictx_sol_prog gs mnm p) (Inl (v, ctx))))))"

declare analyse_interval_ctx_result_for_def [code del]

lemma analyse_interval_ctx_result_for_code [code]:
  "analyse_interval_ctx_result_for gs mnm p =
     (let sol = ictx_sol_prog gs mnm p; gl = declared_global_vars p
      in Analysis_Result (fst sol)
           (\<lambda>v ctx. normalize_point gs
                      (canonicalize_lift (resolved_st_q_is_bot_for gl)
                        (locals (snd sol (Inl (v, ctx)))))))"
  unfolding analyse_interval_ctx_result_for_def Let_def by (rule refl)

definition analyse_interval_ctx_result :: "imp_prog \<Rightarrow> (unit, ivl abs_state) analysis_result" where
  "analyse_interval_ctx_result p =
     analyse_interval_ctx_result_for (declared_global p) prog_main_name p"

subsection \<open>Solved-result tables: PerOrigin and Apinis warrowing siblings\<close>

text \<open>
  Mirror \<open>ictx_sol_prog\<close>/\<open>ictx_terminates_prog\<close>/\<open>analyse_interval_ctx_result_for\<close> (the Join
  table above) at the PerOrigin and Apinis warrowing solvers, reading the same
  \<open>ictx_eqs_prog\<close> equation system: the three-solver orthogonality Interval's Base family
  already has (\<open>analyse_interval_dg_for\<close>/\<open>_join_for\<close>/\<open>_per_origin_for\<close>,
  \<^theory>\<open>Voblint_Analysis.Interval_Exec_Sound\<close>) now also holds at the routed spine.
\<close>

definition ictx_sol_prog_per_origin ::
    "(vname \<Rightarrow> bool) \<Rightarrow> pname \<Rightarrow> imp_prog
       \<Rightarrow> (pp \<times> unit) set \<times> (pp \<times> unit + gk \<Rightarrow> (ivl exec_dg_st lifted, ivl exec_dg_st lifted) dg_state)" where
  "ictx_sol_prog_per_origin gs mnm p =
     TD_side_per_origin_Interp_solve (ictx_eqs_prog gs mnm p) (cfg_exit (prog_cfg mnm p), ())"

definition ictx_terminates_prog_per_origin :: "(vname \<Rightarrow> bool) \<Rightarrow> pname \<Rightarrow> imp_prog \<Rightarrow> bool" where
  "ictx_terminates_prog_per_origin gs mnm p =
     ictx_terminates_per_origin gs (resolved_st_q_is_bot_for (declared_global_vars p))
       (prog_table p) (prog_procs p) mnm (prog_main p)"

lemma ictx_terminates_prog_per_origin_via_solve_c:
  assumes "TD_side_per_origin_Interp_solve_c
             (ictx_eqs gs (resolved_st_q_is_bot_for (declared_global_vars p))
                (prog_table p) (prog_procs p) mnm (prog_main p))
             (cfg_exit (compile_prog (prog_table p) (prog_procs p) mnm (prog_main p)), ()) \<noteq> None"
  shows "ictx_terminates_prog_per_origin gs mnm p"
  unfolding ictx_terminates_prog_per_origin_def
  using assms by (rule ictx_terminates_per_origin_via_solve_c)

definition analyse_interval_ctx_result_per_origin_for ::
    "(vname \<Rightarrow> bool) \<Rightarrow> pname \<Rightarrow> imp_prog \<Rightarrow> (unit, ivl abs_state) analysis_result" where
  "analyse_interval_ctx_result_per_origin_for gs mnm p =
     Analysis_Result
       (fst (ictx_sol_prog_per_origin gs mnm p))
       (\<lambda>v ctx. normalize_point gs
                  (canonicalize_lift (resolved_st_q_is_bot_for (declared_global_vars p))
                    (locals (snd (ictx_sol_prog_per_origin gs mnm p) (Inl (v, ctx))))))"

declare analyse_interval_ctx_result_per_origin_for_def [code del]

lemma analyse_interval_ctx_result_per_origin_for_code [code]:
  "analyse_interval_ctx_result_per_origin_for gs mnm p =
     (let sol = ictx_sol_prog_per_origin gs mnm p; gl = declared_global_vars p
      in Analysis_Result (fst sol)
           (\<lambda>v ctx. normalize_point gs
                      (canonicalize_lift (resolved_st_q_is_bot_for gl)
                        (locals (snd sol (Inl (v, ctx)))))))"
  unfolding analyse_interval_ctx_result_per_origin_for_def Let_def by (rule refl)

definition analyse_interval_ctx_result_per_origin :: "imp_prog \<Rightarrow> (unit, ivl abs_state) analysis_result" where
  "analyse_interval_ctx_result_per_origin p =
     analyse_interval_ctx_result_per_origin_for (declared_global p) prog_main_name p"

definition ictx_sol_prog_warrow ::
    "(vname \<Rightarrow> bool) \<Rightarrow> pname \<Rightarrow> imp_prog
       \<Rightarrow> (pp \<times> unit) set \<times> (pp \<times> unit + gk \<Rightarrow> (ivl exec_dg_st lifted, ivl exec_dg_st lifted) dg_state)" where
  "ictx_sol_prog_warrow gs mnm p =
     TD_side_warrowing_apinis_Interp_solve (ictx_eqs_prog gs mnm p) (cfg_exit (prog_cfg mnm p), ())"

definition ictx_terminates_prog_warrow :: "(vname \<Rightarrow> bool) \<Rightarrow> pname \<Rightarrow> imp_prog \<Rightarrow> bool" where
  "ictx_terminates_prog_warrow gs mnm p =
     ictx_terminates_warrow gs (resolved_st_q_is_bot_for (declared_global_vars p))
       (prog_table p) (prog_procs p) mnm (prog_main p)"

lemma ictx_terminates_prog_warrow_via_solve_c:
  assumes "TD_side_warrowing_apinis_Interp_solve_c
             (ictx_eqs gs (resolved_st_q_is_bot_for (declared_global_vars p))
                (prog_table p) (prog_procs p) mnm (prog_main p))
             (cfg_exit (compile_prog (prog_table p) (prog_procs p) mnm (prog_main p)), ()) \<noteq> None"
  shows "ictx_terminates_prog_warrow gs mnm p"
  unfolding ictx_terminates_prog_warrow_def
  using assms by (rule ictx_terminates_warrow_via_solve_c)

definition analyse_interval_ctx_result_warrow_for ::
    "(vname \<Rightarrow> bool) \<Rightarrow> pname \<Rightarrow> imp_prog \<Rightarrow> (unit, ivl abs_state) analysis_result" where
  "analyse_interval_ctx_result_warrow_for gs mnm p =
     Analysis_Result
       (fst (ictx_sol_prog_warrow gs mnm p))
       (\<lambda>v ctx. normalize_point gs
                  (canonicalize_lift (resolved_st_q_is_bot_for (declared_global_vars p))
                    (locals (snd (ictx_sol_prog_warrow gs mnm p) (Inl (v, ctx))))))"

declare analyse_interval_ctx_result_warrow_for_def [code del]

lemma analyse_interval_ctx_result_warrow_for_code [code]:
  "analyse_interval_ctx_result_warrow_for gs mnm p =
     (let sol = ictx_sol_prog_warrow gs mnm p; gl = declared_global_vars p
      in Analysis_Result (fst sol)
           (\<lambda>v ctx. normalize_point gs
                      (canonicalize_lift (resolved_st_q_is_bot_for gl)
                        (locals (snd sol (Inl (v, ctx)))))))"
  unfolding analyse_interval_ctx_result_warrow_for_def Let_def by (rule refl)

definition analyse_interval_ctx_result_warrow :: "imp_prog \<Rightarrow> (unit, ivl abs_state) analysis_result" where
  "analyse_interval_ctx_result_warrow p =
     analyse_interval_ctx_result_warrow_for (declared_global p) prog_main_name p"

end
