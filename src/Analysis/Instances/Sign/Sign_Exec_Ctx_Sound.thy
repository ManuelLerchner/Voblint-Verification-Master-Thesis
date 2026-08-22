theory Sign_Exec_Ctx_Sound
  imports
    "Voblint_Analysis.Exec_DG_Bridge"
    "Voblint_Analysis.Sign_DG"
    "Voblint_Analysis.Sign_Exec_Sound"
    "Voblint_Core.Routed_Context"
    "Voblint_Core.Routed_Context_Unit"
    "Voblint_Core.Solver_Menu"
    "Voblint_VIMP.VIMP_Notation"
    "Voblint_Core.Activation_Backbone"
    "Voblint_Core.Analysis_Result"
begin

section \<open>Sign at the routed spine, instantiated at the unit context\<close>

text \<open>
  Redirects Sign's production Base-family (\<open>dg_gen_of\<close>) analysis onto the routed
  D/G spine (\<^locale>\<open>dg_ctx_activation_base\<close>, \<^locale>\<open>unit_routed_context\<close>) that
  Interval's own entry-state and call-string context analyses already use. The
  context here is \<^typ>\<open>unit\<close>:
  \<^locale>\<open>unit_routed_context\<close> (\<^theory>\<open>Voblint_Core.Routed_Context_Unit\<close>) fixes
  \<^const>\<open>route_unit\<close>, so every routing-agreement obligation that Interval's
  formals-context instance must prove from its own transfer facts collapses here
  to a free lemma about the constant function \<^const>\<open>route_unit\<close> --- the same
  collapse the \<open>Routed_Context_Unit\<close> theory documents generically.

  Soundness below is derived directly from \<^locale>\<open>dg_ctx_activation_base\<close>'s generic
  machinery against the collecting semantics, exactly as Interval's entry-state
  analysis is derived. No comparison to Sign's Base-family production result is
  attempted or needed: \<^const>\<open>dg_gen_of\<close> never appears in this development.
\<close>

subsection \<open>Global key: real globals vs callee-entry seed slots\<close>

text \<open>
  \<^typ>\<open>unit\<close> context, so the seed constructor's second field is \<^typ>\<open>unit\<close> rather
  than an interesting per-context payload: exactly one seed slot per callee entry.
\<close>

datatype gk = Global | Seed (seed_pp: pp) (seed_ctx: unit)

subsection \<open>The routed unit-context D/G spec\<close>

text \<open>
  The same Base-style whole-state specification Sign's own production
  \<^const>\<open>analyse_sign_eqs_for\<close> already solves over (\<^theory>\<open>Voblint_Analysis.Sign_Exec_Sound\<close>),
  at the same \<^const>\<open>sign_tf_st_for\<close>/\<^const>\<open>sign_enter_st_for\<close> primitives. Only the
  equation-generator wrapped around this spec changes (\<open>dg_gen_of\<close> there, the routed
  keyed-seed generator here) --- the spec itself, and every domain-transfer soundness
  fact about it, is untouched.
\<close>

definition sctx_spec ::
  "(vname \<Rightarrow> bool) \<Rightarrow> (sign exec_dg_st \<Rightarrow> bool) \<Rightarrow> (sign exec_dg_st lifted, sign exec_dg_st lifted) dg_spec"
where
  "sctx_spec gs is_bot_pred = base_dg_spec_st_for_lifted gs is_bot_pred (sign_tf_st_for gs) (sign_enter_st_for gs)"

definition sctx_abs_spec :: "(vname \<Rightarrow> bool) \<Rightarrow> (sign abs_state lifted, sign abs_state lifted) dg_spec" where
  "sctx_abs_spec gs = base_dg_spec_for_lifted gs is_bot_state (sign_tf_for gs)"

subsection \<open>The routed equation system and its executable solution\<close>

definition sctx_eqs ::
    "(vname \<Rightarrow> bool) \<Rightarrow> (sign exec_dg_st \<Rightarrow> bool) \<Rightarrow> proc_table \<Rightarrow> pname list \<Rightarrow> pname \<Rightarrow> com
       \<Rightarrow> (pp \<times> unit, gk, (sign exec_dg_st lifted, sign exec_dg_st lifted) dg_state) eqsT" where
  "sctx_eqs gs is_bot_pred Pi ps mnm main =
     side_cfg_T_eff_keyed_seed_dg_buffered intra_predecessor_list (\<lambda>_. Global)
       route_unit
       (routed_cmb_g_contribution (sctx_spec gs is_bot_pred) Global Seed)
       (routed_extra_g Seed Global)
       (compile_prog Pi ps mnm main) (sctx_spec gs is_bot_pred) Bot (Lifted cinit_sign_st) Bot"

definition sctx_sol ::
    "(vname \<Rightarrow> bool) \<Rightarrow> (sign exec_dg_st \<Rightarrow> bool) \<Rightarrow> proc_table \<Rightarrow> pname list \<Rightarrow> pname \<Rightarrow> com
       \<Rightarrow> (pp \<times> unit) set \<times> (pp \<times> unit + gk \<Rightarrow> (sign exec_dg_st lifted, sign exec_dg_st lifted) dg_state)" where
  "sctx_sol gs is_bot_pred Pi ps mnm main =
     TD_side_always_join_Interp_solve (sctx_eqs gs is_bot_pred Pi ps mnm main)
       (cfg_exit (compile_prog Pi ps mnm main), ())"

definition sctx_terminates ::
    "(vname \<Rightarrow> bool) \<Rightarrow> (sign exec_dg_st \<Rightarrow> bool) \<Rightarrow> proc_table \<Rightarrow> pname list \<Rightarrow> pname \<Rightarrow> com \<Rightarrow> bool" where
  "sctx_terminates gs is_bot_pred Pi ps mnm main =
     TD_side_always_join_Interp.solve_dom TYPE(gk) TYPE((sign exec_dg_st lifted, sign exec_dg_st lifted) dg_state)
       (sctx_eqs gs is_bot_pred Pi ps mnm main) (cfg_exit (compile_prog Pi ps mnm main), ())"

lemma sctx_terminates_via_solve_c:
  assumes "TD_side_always_join_Interp_solve_c (sctx_eqs gs is_bot_pred Pi ps mnm main)
             (cfg_exit (compile_prog Pi ps mnm main), ()) \<noteq> None"
  shows "sctx_terminates gs is_bot_pred Pi ps mnm main"
  unfolding sctx_terminates_def TD_side_always_join_Interp.term_equivalence
            TD_side_always_join_Interp.solve_c_dom_def
  using assms by simp

subsection \<open>Route agreement collapses to a free lemma\<close>

text \<open>
  \<^const>\<open>route_unit\<close> is used, unchanged, at both the executable and abstract carrier:
  it is polymorphic in its \<^typ>\<open>'D\<close> argument and ignores it outright, so the
  routing-agreement obligation every other routed instance must prove from its own
  transfer facts is here true unconditionally, for any reader \<open>f\<close>.
\<close>

lemma route_unit_commute: "route_unit u c' d ca = route_unit u c' (f d) ca"
  by simp

subsection \<open>Domain commute facts, at the routed unit spec\<close>

text \<open>
  \<^locale>\<open>routed_dg_domain_exec\<close> (\<^theory>\<open>Voblint_Analysis.DG_Base_Exec\<close>) derives exactly
  this shape once, generic in a domain: an interpretation at Sign's own primitive commute
  facts \<^const>\<open>sign_tf_st_for\<close>/\<^const>\<open>sign_enter_st_for\<close> already prove
  (\<open>sign_tf_st_for_commute\<close>, \<open>sign_enter_st_for_commute\<close>, \<^theory>\<open>Voblint_Analysis.Sign_Exec\<close>)
  replaces what used to be Sign's own copy of the derivation.
\<close>

context
  fixes gs :: "vname \<Rightarrow> bool" and is_bot_pred :: "sign exec_dg_st \<Rightarrow> bool"
  assumes exact: "\<And>s. is_bot_pred s = is_bot_state (fun_of_resolved_st_q_for gs s)"
begin

interpretation sign_domain: routed_dg_domain_exec
  gs is_bot_pred "sign_tf_st_for gs" "sign_enter_st_for gs" "sign_tf_for gs"
  by unfold_locales (rule sign_tf_st_for_commute, rule sign_enter_st_for_commute, rule exact)

lemmas sign_Hstep_lifted_for = sign_domain.Hstep_lifted_for
lemmas sign_Henter_lifted_for = sign_domain.Henter_lifted_for
lemmas sign_Hcomb_lifted_for = sign_domain.Hcomb_lifted_for
lemmas sign_Hcont_lifted_for = sign_domain.Hcont_lifted_for

end

lemmas dg_reader_commute_gen_sign_lifted = dg_reader_commute_gen_lifted_for

lemma seed_ne_global [simp]: "Seed p ctx \<noteq> Global"
  by simp

lemma dg_tree_st_commute_routed_cmb_g_sign:
  assumes exact: "\<And>s. is_bot_pred s = is_bot_state (fun_of_resolved_st_q_for gs s)"
  shows "dg_reader_commute_gen.dg_tree_st_commute
           (map_lift (fun_of_resolved_st_q_for gs)) (map_lift (fun_of_resolved_st_q_for gs)) env
     (routed_cmb_g (sctx_spec gs is_bot_pred) Global Seed route_unit ctx ca cc ex)
     (routed_cmb_g (sctx_abs_spec gs) Global Seed route_unit ctx ca cc ex)"
  unfolding sctx_spec_def sctx_abs_spec_def
  apply (rule dg_reader_commute_gen.dg_tree_st_commute_routed_cmb_g
        [where Floc = "map_lift (fun_of_resolved_st_q_for gs)"
           and Fglob = "map_lift (fun_of_resolved_st_q_for gs)"])
      apply (rule dg_reader_commute_gen_sign_lifted)
     apply (rule seed_ne_global)
    apply (rule sign_Henter_lifted_for[OF exact])
   apply (rule sign_Hcomb_lifted_for[OF exact])
  apply (rule sign_Hcont_lifted_for[OF exact])
  apply (rule route_unit_commute)
  done

lemma hextra_commute_routed_sign:
  "list_all2 (dg_reader_commute_gen.dg_tree_st_commute
                (map_lift (fun_of_resolved_st_q_for gs)) (map_lift (fun_of_resolved_st_q_for gs)) env)
     (routed_extra_g Seed Global route_unit ctx w)
     (routed_extra_g Seed Global route_unit ctx w)"
  by (rule dg_reader_commute_gen.dg_tree_st_commute_routed_extra_g[OF dg_reader_commute_gen_sign_lifted])

subsection \<open>The certified executable post-solution, generic per compiled program\<close>

context
  fixes gs :: "vname \<Rightarrow> bool" and is_bot_pred :: "sign exec_dg_st \<Rightarrow> bool"
    and Pi :: proc_table and ps :: "pname list" and mnm :: pname and main :: com
  assumes solves: "sctx_terminates gs is_bot_pred Pi ps mnm main"
    and exact: "\<And>s. is_bot_pred s = is_bot_state (fun_of_resolved_st_q_for gs s)"
begin

lemma sctx_solve_dom:
  "TD_side_always_join_Interp.solve_dom TYPE(gk) TYPE((sign exec_dg_st lifted, sign exec_dg_st lifted) dg_state)
     (sctx_eqs gs is_bot_pred Pi ps mnm main) (cfg_exit (compile_prog Pi ps mnm main), ())"
  using solves
  unfolding sctx_terminates_def TD_side_always_join_Interp.term_equivalence
            TD_side_always_join_Interp.solve_c_dom_def
  by simp

lemma sctx_pp_st:
  "part_post_solution (sctx_eqs gs is_bot_pred Pi ps mnm main) (cfg_exit (compile_prog Pi ps mnm main), ())
     (snd (sctx_sol gs is_bot_pred Pi ps mnm main)) (fst (sctx_sol gs is_bot_pred Pi ps mnm main))"
  using TD_side_always_join_Interp.partial_post_solution
          [OF sctx_solve_dom, of "fst (sctx_sol gs is_bot_pred Pi ps mnm main)"
             "snd (sctx_sol gs is_bot_pred Pi ps mnm main)"]
  unfolding sctx_sol_def by simp

theorem sctx_pp_abs:
  "part_post_solution
     (side_cfg_T_eff_keyed_seed_dg intra_predecessor_list (\<lambda>_. Global) route_unit
        (routed_cmb_g (sctx_abs_spec gs) Global Seed)
        (routed_extra_g Seed Global)
        (compile_prog Pi ps mnm main) (sctx_abs_spec gs)
        (map_lift (fun_of_resolved_st_q_for gs) (Bot::sign exec_dg_st lifted))
        (map_lift (fun_of_resolved_st_q_for gs) (Lifted cinit_sign_st))
        (map_lift (fun_of_resolved_st_q_for gs) (Bot::sign exec_dg_st lifted)))
     (cfg_exit (compile_prog Pi ps mnm main), ())
     (fun_of_dg_st_gen (map_lift (fun_of_resolved_st_q_for gs)) (map_lift (fun_of_resolved_st_q_for gs))
        \<circ> snd (sctx_sol gs is_bot_pred Pi ps mnm main))
     (fst (sctx_sol gs is_bot_pred Pi ps mnm main))"
proof -
  have pp'_buf: "part_post_solution
       (side_cfg_T_eff_keyed_seed_dg_buffered intra_predecessor_list (\<lambda>_. Global)
          route_unit
          (routed_cmb_g_contribution (sctx_spec gs is_bot_pred) Global Seed)
          (routed_extra_g Seed Global)
          (compile_prog Pi ps mnm main) (sctx_spec gs is_bot_pred) Bot (Lifted cinit_sign_st) Bot)
       (cfg_exit (compile_prog Pi ps mnm main), ())
       (snd (sctx_sol gs is_bot_pred Pi ps mnm main)) (fst (sctx_sol gs is_bot_pred Pi ps mnm main))"
    using sctx_pp_st unfolding sctx_eqs_def by simp
  have seed_ne_global: "\<And>p c. Seed p c \<noteq> Global" by simp
  have pp': "part_post_solution
       (side_cfg_T_eff_keyed_seed_dg intra_predecessor_list (\<lambda>_. Global) route_unit
          (routed_cmb_g (sctx_spec gs is_bot_pred) Global Seed)
          (routed_extra_g Seed Global)
          (compile_prog Pi ps mnm main) (sctx_spec gs is_bot_pred) Bot (Lifted cinit_sign_st) Bot)
       (cfg_exit (compile_prog Pi ps mnm main), ())
       (snd (sctx_sol gs is_bot_pred Pi ps mnm main)) (fst (sctx_sol gs is_bot_pred Pi ps mnm main))"
  proof (rule part_post_solution_seed_dg_buffered_to_old
      [where cmb_c = "routed_cmb_g_contribution (sctx_spec gs is_bot_pred) Global Seed"])
    show "\<And>c' ca cc ex \<tau>. locals (traverse_rhs
             (routed_cmb_g_contribution (sctx_spec gs is_bot_pred) Global Seed
               route_unit c' ca cc ex) \<tau>)
           = locals (traverse_rhs
             (routed_cmb_g (sctx_spec gs is_bot_pred) Global Seed
               route_unit c' ca cc ex) \<tau>)"
      by (rule routed_cmb_g_contribution_matches_local)
    show "\<And>c' ca cc ex \<tau>. locals (sides_of_rhs
             (routed_cmb_g (sctx_spec gs is_bot_pred) Global Seed
               route_unit c' ca cc ex) \<tau> (Inr ((\<lambda>_. Global) c'))) = bot"
      by (rule routed_cmb_g_side_pure[of Seed Global, OF seed_ne_global])
    show "\<And>c' ca cc ex \<tau>. globs (traverse_rhs
             (routed_cmb_g_contribution (sctx_spec gs is_bot_pred) Global Seed
               route_unit c' ca cc ex) \<tau>)
           = globs (sides_of_rhs
             (routed_cmb_g (sctx_spec gs is_bot_pred) Global Seed
               route_unit c' ca cc ex) \<tau> (Inr ((\<lambda>_. Global) c')))"
      by (rule routed_cmb_g_contribution_matches_global[of Seed Global, OF seed_ne_global])
    show "\<And>c' ca cc ex \<tau>. sides_of_rhs
             (routed_cmb_g_contribution (sctx_spec gs is_bot_pred) Global Seed
               route_unit c' ca cc ex) \<tau> (Inr ((\<lambda>_. Global) c')) = bot"
      by (rule routed_cmb_g_contribution_free_at_key[of Seed Global, OF seed_ne_global])
    show "\<And>c' ca cc ex \<tau> z. z \<noteq> Inr ((\<lambda>_. Global) c') \<Longrightarrow> sides_of_rhs
             (routed_cmb_g_contribution (sctx_spec gs is_bot_pred) Global Seed
               route_unit c' ca cc ex) \<tau> z
           = sides_of_rhs
             (routed_cmb_g (sctx_spec gs is_bot_pred) Global Seed
               route_unit c' ca cc ex) \<tau> z"
      by (rule routed_cmb_g_contribution_sides_off_key[of Seed Global, OF seed_ne_global])
    show "\<And>c' ca cc ex \<tau>. dep_aux \<tau>
             (routed_cmb_g_contribution (sctx_spec gs is_bot_pred) Global Seed
               route_unit c' ca cc ex)
           = dep_aux \<tau>
             (routed_cmb_g (sctx_spec gs is_bot_pred) Global Seed
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
          (routed_cmb_g_contribution (sctx_spec gs is_bot_pred) Global Seed)
          (routed_extra_g Seed Global)
          (compile_prog Pi ps mnm main) (sctx_spec gs is_bot_pred) Bot (Lifted cinit_sign_st) Bot)
       (cfg_exit (compile_prog Pi ps mnm main), ())
       (snd (sctx_sol gs is_bot_pred Pi ps mnm main)) (fst (sctx_sol gs is_bot_pred Pi ps mnm main))"
      by (rule pp'_buf)
  qed
  have sign_Hstep_ctx:
    "map_prod (map_lift (fun_of_resolved_st_q_for gs)) (map_lift (fun_of_resolved_st_q_for gs))
       (dg_spec_step (sctx_spec gs is_bot_pred) a d g') =
       dg_spec_step (sctx_abs_spec gs) a
         (map_lift (fun_of_resolved_st_q_for gs) d) (map_lift (fun_of_resolved_st_q_for gs) g')" for a d g'
    unfolding sctx_spec_def sctx_abs_spec_def by (rule sign_Hstep_lifted_for[OF exact])
  show ?thesis
    apply (rule part_post_solution_seed_dg_st_to_abs_lifted_for
          [where gs = gs and pred_sel = intra_predecessor_list and gkey = "\<lambda>_. Global"
             and route_st = "route_unit :: cfg_node \<Rightarrow> unit \<Rightarrow> sign exec_dg_st lifted \<Rightarrow> call_action \<Rightarrow> unit"
             and route_abs = "route_unit :: cfg_node \<Rightarrow> unit \<Rightarrow> sign abs_state lifted \<Rightarrow> call_action \<Rightarrow> unit"
             and cmb_st = "routed_cmb_g (sctx_spec gs is_bot_pred) Global Seed"
             and cmb_abs = "routed_cmb_g (sctx_abs_spec gs) Global Seed"
             and extra_st = "routed_extra_g Seed Global"
             and extra_abs = "routed_extra_g Seed Global"
             and g = "compile_prog Pi ps mnm main" and S_st = "sctx_spec gs is_bot_pred" and S_abs = "sctx_abs_spec gs"])
        apply (rule sign_Hstep_ctx)
       apply (rule route_unit_commute)
      apply (rule dg_tree_st_commute_routed_cmb_g_sign[OF exact])
     apply (rule hextra_commute_routed_sign)
    apply (rule pp')
    done
qed

end

section \<open>Activation-indexed collecting soundness, generic per compiled program\<close>

text \<open>
  Executable twins of the context's own \<open>sctx_sigma_abs\<close>/\<open>sctx_sg\<close> (below), defined
  before that context so their equations are unconditional -- mirrors Interval's
  \<open>entry_state_sigma_abs_exec\<close>/\<open>entry_state_sg_exec\<close> convention exactly.
\<close>

definition sctx_sigma_abs_exec ::
    "(vname \<Rightarrow> bool) \<Rightarrow> (sign exec_dg_st \<Rightarrow> bool) \<Rightarrow> proc_table \<Rightarrow> pname list \<Rightarrow> pname \<Rightarrow> com
       \<Rightarrow> pp \<times> unit + gk \<Rightarrow> (sign abs_state lifted, sign abs_state lifted) dg_state" where
  "sctx_sigma_abs_exec gs is_bot_pred Pi ps mnm main =
     fun_of_dg_st_gen (map_lift (fun_of_resolved_st_q_for gs)) (map_lift (fun_of_resolved_st_q_for gs))
       \<circ> snd (sctx_sol gs is_bot_pred Pi ps mnm main)"

definition sctx_sg_exec ::
    "(vname \<Rightarrow> bool) \<Rightarrow> (sign exec_dg_st \<Rightarrow> bool) \<Rightarrow> proc_table \<Rightarrow> pname list \<Rightarrow> pname \<Rightarrow> com
       \<Rightarrow> pp \<times> unit + gk \<Rightarrow> sign abs_state lifted" where
  "sctx_sg_exec gs is_bot_pred Pi ps mnm main k =
     (case k of
        Inl (v, ctx) \<Rightarrow>
          (if (v, ctx) \<in> fst (sctx_sol gs is_bot_pred Pi ps mnm main)
           then locals (sctx_sigma_abs_exec gs is_bot_pred Pi ps mnm main (Inl (v, ctx)))
           else Bot)
      | Inr _ \<Rightarrow> Bot)"

context
  fixes gs :: "vname \<Rightarrow> bool" and is_bot_pred :: "sign exec_dg_st \<Rightarrow> bool"
    and Pi :: proc_table and ps :: "pname list" and mnm :: pname and main :: com
  assumes solves: "sctx_terminates gs is_bot_pred Pi ps mnm main"
    and exact: "\<And>s. is_bot_pred s = is_bot_state (fun_of_resolved_st_q_for gs s)"
    and entry_cov: "(cfg_entry (compile_prog Pi ps mnm main), ()) \<in> fst (sctx_sol gs is_bot_pred Pi ps mnm main)"
    and fwd_ok: "\<And>u a v ctx. (u, ctx) \<in> fst (sctx_sol gs is_bot_pred Pi ps mnm main)
                   \<Longrightarrow> (u, a, v) \<in> intra (compile_prog Pi ps mnm main)
                   \<Longrightarrow> (v, ctx) \<in> fst (sctx_sol gs is_bot_pred Pi ps mnm main)"
    and call_fwd_ok: "\<And>u ctx dst pars args p cont.
        (u, ctx) \<in> fst (sctx_sol gs is_bot_pred Pi ps mnm main)
        \<Longrightarrow> (u, CallEdge dst pars args, FunctionEntry p, cont) \<in> calls (compile_prog Pi ps mnm main)
        \<Longrightarrow> (FunctionEntry p, ()) \<in> fst (sctx_sol gs is_bot_pred Pi ps mnm main)"
    and comb_fwd_ok: "\<And>cl c1 dst pars args p cont.
        (cl, c1) \<in> fst (sctx_sol gs is_bot_pred Pi ps mnm main)
        \<Longrightarrow> (cl, CallEdge dst pars args, FunctionEntry p, cont) \<in> calls (compile_prog Pi ps mnm main)
        \<Longrightarrow> (cont, c1) \<in> fst (sctx_sol gs is_bot_pred Pi ps mnm main)"
begin

subsection \<open>The semantic solution projection\<close>

definition sctx_sigma_abs :: "pp \<times> unit + gk \<Rightarrow> (sign abs_state lifted, sign abs_state lifted) dg_state" where
  "sctx_sigma_abs = sctx_sigma_abs_exec gs is_bot_pred Pi ps mnm main"

definition sctx_sg :: "pp \<times> unit + gk \<Rightarrow> sign abs_state lifted" where
  "sctx_sg = sctx_sg_exec gs is_bot_pred Pi ps mnm main"

lemma sctx_fin: "finite (intra (compile_prog Pi ps mnm main))"
  using compile_prog_finite by blast

lemma sctx_finC: "finite (calls (compile_prog Pi ps mnm main))"
  using compile_prog_finite by blast

lemma sctx_sg_covered:
  "(v, ctx) \<in> fst (sctx_sol gs is_bot_pred Pi ps mnm main)
   \<Longrightarrow> sctx_sg (Inl (v, ctx)) = locals (sctx_sigma_abs (Inl (v, ctx)))"
  by (simp add: sctx_sg_def sctx_sg_exec_def sctx_sigma_abs_def sctx_sigma_abs_exec_def)

lemma sctx_sg_uncovered_empty:
  "(v, ctx) \<notin> fst (sctx_sol gs is_bot_pred Pi ps mnm main)
     \<Longrightarrow> gamma_state_lift (sctx_sg (Inl (v, ctx))) = {}"
  by (simp add: sctx_sg_def sctx_sg_exec_def)

subsection \<open>Instantiating the generic DG-native activation discharge\<close>

interpretation sctx_dg_base: sound_dg_spec "sctx_abs_spec gs" gamma_dg_base gs
  unfolding sctx_abs_spec_def
  by (rule base_dg_spec_sound[OF sign_is_sound_transfer_for is_bot_state_gamma_state_empty])

interpretation sctx_dg: dg_ctx_activation_base "sctx_abs_spec gs" gamma_dg_base gs
    "compile_prog Pi ps mnm main" Global route_unit
    "routed_cmb_g (sctx_abs_spec gs) Global Seed"
    "routed_extra_g Seed Global"
    "map_lift (fun_of_resolved_st_q_for gs) (Bot::sign exec_dg_st lifted)"
    "map_lift (fun_of_resolved_st_q_for gs) (Lifted cinit_sign_st)"
    "map_lift (fun_of_resolved_st_q_for gs) (Bot::sign exec_dg_st lifted)"
    sctx_sigma_abs "fst (sctx_sol gs is_bot_pred Pi ps mnm main)"
    "(cfg_exit (compile_prog Pi ps mnm main), ())" sctx_sg gamma_state_lift
proof unfold_locales
  show "finite (intra (compile_prog Pi ps mnm main))" by (rule sctx_fin)
next
  show "part_post_solution
          (side_cfg_T_eff_keyed_seed_dg intra_predecessor_list (\<lambda>_. Global) route_unit
             (routed_cmb_g (sctx_abs_spec gs) Global Seed)
             (routed_extra_g Seed Global)
             (compile_prog Pi ps mnm main) (sctx_abs_spec gs)
             (map_lift (fun_of_resolved_st_q_for gs) (Bot::sign exec_dg_st lifted))
             (map_lift (fun_of_resolved_st_q_for gs) (Lifted cinit_sign_st))
             (map_lift (fun_of_resolved_st_q_for gs) (Bot::sign exec_dg_st lifted)))
          (cfg_exit (compile_prog Pi ps mnm main), ()) sctx_sigma_abs
          (fst (sctx_sol gs is_bot_pred Pi ps mnm main))"
    unfolding sctx_sigma_abs_def sctx_sigma_abs_exec_def
    by (rule sctx_pp_abs[OF solves exact])
next
  fix v ctx assume "(v, ctx) \<in> fst (sctx_sol gs is_bot_pred Pi ps mnm main)"
  thus "gamma_state_lift (sctx_sg (Inl (v, ctx)))
          = gamma_dg_base (locals (sctx_sigma_abs (Inl (v, ctx)))) (globs (sctx_sigma_abs (Inr Global)))"
    by (simp add: sctx_sg_covered gamma_dg_base_def)
next
  fix v ctx assume "(v, ctx) \<notin> fst (sctx_sol gs is_bot_pred Pi ps mnm main)"
  thus "gamma_state_lift (sctx_sg (Inl (v, ctx))) = {}"
    by (rule sctx_sg_uncovered_empty)
next
  fix u a v ctx assume "(u, ctx) \<in> fst (sctx_sol gs is_bot_pred Pi ps mnm main)"
    "(u, a, v) \<in> intra (compile_prog Pi ps mnm main)"
  thus "(v, ctx) \<in> fst (sctx_sol gs is_bot_pred Pi ps mnm main)" by (rule fwd_ok)
qed

subsection \<open>The routed interpretation and its CALL/COMB corollaries\<close>

interpretation sctx_routed: unit_routed_context "sctx_abs_spec gs" gamma_dg_base gs
    "compile_prog Pi ps mnm main" Global
    "map_lift (fun_of_resolved_st_q_for gs) (Bot::sign exec_dg_st lifted)"
    "map_lift (fun_of_resolved_st_q_for gs) (Lifted cinit_sign_st)"
    "map_lift (fun_of_resolved_st_q_for gs) (Bot::sign exec_dg_st lifted)"
    sctx_sigma_abs "fst (sctx_sol gs is_bot_pred Pi ps mnm main)"
    "(cfg_exit (compile_prog Pi ps mnm main), ())" sctx_sg
    Seed gamma_state_lift
proof (unfold_locales, goal_cases FinC SeedKey CallFwd CombFwd EnterAgree)
  case FinC show ?case by (rule sctx_finC)
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

lemma sctx_cinit_le_cinit_sign_st:
  "cinit_stores gs \<subseteq> gamma_state_lift (map_lift (fun_of_resolved_st_q_for gs) (Lifted cinit_sign_st))"
  by (auto simp: cinit_stores_def gamma_state_def fun_of_resolved_st_q_for_def fun_of_st_cinit_sign_st_for)

end

section \<open>Solved-result table\<close>

text \<open>
  Whole-program convenience layer, mirroring Interval's own \<open>entry_state_eqs_prog\<close>/
  \<open>entry_state_sol_prog\<close>/\<open>entry_state_terminates_prog\<close>. The result tables below read
  the raw executable solve through the same \<^const>\<open>canonicalize_lift\<close>/\<^const>\<open>normalize_point\<close>
  boundary the mixed-analysis \<open>monovariant_analysis_result_for\<close> and Interval's own
  \<open>analyse_interval_entry_state_result_for\<close> already use, and are the tables Sign's public
  API (\<open>Sign_Checks.thy\<close>) redirects onto in production. Their soundness is established there
  through a \<open>dg_analysis_adapter\<close> interpretation of this file's own \<open>sctx_dg\<close>/\<open>sctx_routed\<close>
  context, bridged to these executable tables via \<open>normalize_point_canonicalize_lift_eq_old\<close>
  (\<^theory>\<open>Voblint_Core.Analysis_Result\<close>).
\<close>

definition sctx_eqs_prog ::
    "(vname \<Rightarrow> bool) \<Rightarrow> pname \<Rightarrow> imp_prog
       \<Rightarrow> (pp \<times> unit, gk, (sign exec_dg_st lifted, sign exec_dg_st lifted) dg_state) eqsT" where
  "sctx_eqs_prog gs mnm p =
     sctx_eqs gs (resolved_st_q_is_bot_for (declared_global_vars p))
       (prog_table p) (prog_procs p) mnm (prog_main p)"

definition sctx_sol_prog ::
    "(vname \<Rightarrow> bool) \<Rightarrow> pname \<Rightarrow> imp_prog
       \<Rightarrow> (pp \<times> unit) set \<times> (pp \<times> unit + gk \<Rightarrow> (sign exec_dg_st lifted, sign exec_dg_st lifted) dg_state)" where
  "sctx_sol_prog gs mnm p =
     TD_side_always_join_Interp_solve (sctx_eqs_prog gs mnm p) (cfg_exit (prog_cfg mnm p), ())"

text \<open>
  Solver-choice sibling of \<^const>\<open>sctx_sol_prog\<close>: the same \<^const>\<open>sctx_eqs_prog\<close> equation
  system, solved under the per-origin update rule instead of the always-join rule production
  uses. \<open>Sign_Checks.analyse_sign_result_per_origin_for\<close> reads this table.
\<close>

definition sctx_sol_prog_per_origin ::
    "(vname \<Rightarrow> bool) \<Rightarrow> pname \<Rightarrow> imp_prog
       \<Rightarrow> (pp \<times> unit) set \<times> (pp \<times> unit + gk \<Rightarrow> (sign exec_dg_st lifted, sign exec_dg_st lifted) dg_state)" where
  "sctx_sol_prog_per_origin gs mnm p =
     TD_side_per_origin_Interp_solve (sctx_eqs_prog gs mnm p) (cfg_exit (prog_cfg mnm p), ())"

definition sctx_terminates_prog :: "(vname \<Rightarrow> bool) \<Rightarrow> pname \<Rightarrow> imp_prog \<Rightarrow> bool" where
  "sctx_terminates_prog gs mnm p =
     sctx_terminates gs (resolved_st_q_is_bot_for (declared_global_vars p))
       (prog_table p) (prog_procs p) mnm (prog_main p)"

lemma sctx_terminates_prog_via_solve_c:
  assumes "TD_side_always_join_Interp_solve_c
             (sctx_eqs gs (resolved_st_q_is_bot_for (declared_global_vars p))
                (prog_table p) (prog_procs p) mnm (prog_main p))
             (cfg_exit (compile_prog (prog_table p) (prog_procs p) mnm (prog_main p)), ()) \<noteq> None"
  shows "sctx_terminates_prog gs mnm p"
  unfolding sctx_terminates_prog_def
  using assms by (rule sctx_terminates_via_solve_c)

definition analyse_sign_ctx_result_for ::
    "(vname \<Rightarrow> bool) \<Rightarrow> pname \<Rightarrow> imp_prog \<Rightarrow> (unit, sign abs_state) analysis_result" where
  "analyse_sign_ctx_result_for gs mnm p =
     Analysis_Result
       (fst (sctx_sol_prog gs mnm p))
       (\<lambda>v ctx. normalize_point gs
                  (canonicalize_lift (resolved_st_q_is_bot_for (declared_global_vars p))
                    (locals (snd (sctx_sol_prog gs mnm p) (Inl (v, ctx))))))"

declare analyse_sign_ctx_result_for_def [code del]

lemma analyse_sign_ctx_result_for_code [code]:
  "analyse_sign_ctx_result_for gs mnm p =
     (let sol = sctx_sol_prog gs mnm p; gl = declared_global_vars p
      in Analysis_Result (fst sol)
           (\<lambda>v ctx. normalize_point gs
                      (canonicalize_lift (resolved_st_q_is_bot_for gl)
                        (locals (snd sol (Inl (v, ctx)))))))"
  unfolding analyse_sign_ctx_result_for_def Let_def by (rule refl)

definition analyse_sign_ctx_result :: "imp_prog \<Rightarrow> (unit, sign abs_state) analysis_result" where
  "analyse_sign_ctx_result p =
     analyse_sign_ctx_result_for (declared_global p) prog_main_name p"

text \<open>Per-origin sibling of \<^const>\<open>analyse_sign_ctx_result_for\<close>, reading
  \<^const>\<open>sctx_sol_prog_per_origin\<close> instead of \<^const>\<open>sctx_sol_prog\<close>.\<close>

definition analyse_sign_ctx_result_per_origin_for ::
    "(vname \<Rightarrow> bool) \<Rightarrow> pname \<Rightarrow> imp_prog \<Rightarrow> (unit, sign abs_state) analysis_result" where
  "analyse_sign_ctx_result_per_origin_for gs mnm p =
     Analysis_Result
       (fst (sctx_sol_prog_per_origin gs mnm p))
       (\<lambda>v ctx. normalize_point gs
                  (canonicalize_lift (resolved_st_q_is_bot_for (declared_global_vars p))
                    (locals (snd (sctx_sol_prog_per_origin gs mnm p) (Inl (v, ctx))))))"

declare analyse_sign_ctx_result_per_origin_for_def [code del]

lemma analyse_sign_ctx_result_per_origin_for_code [code]:
  "analyse_sign_ctx_result_per_origin_for gs mnm p =
     (let sol = sctx_sol_prog_per_origin gs mnm p; gl = declared_global_vars p
      in Analysis_Result (fst sol)
           (\<lambda>v ctx. normalize_point gs
                      (canonicalize_lift (resolved_st_q_is_bot_for gl)
                        (locals (snd sol (Inl (v, ctx)))))))"
  unfolding analyse_sign_ctx_result_per_origin_for_def Let_def by (rule refl)

definition analyse_sign_ctx_result_per_origin :: "imp_prog \<Rightarrow> (unit, sign abs_state) analysis_result" where
  "analyse_sign_ctx_result_per_origin p =
     analyse_sign_ctx_result_per_origin_for (declared_global p) prog_main_name p"

end
