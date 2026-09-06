theory Example_Sign_DG_CallString_K2
  imports
    Example_Sign_DG_CallString_K1
begin

section \<open>A computed 2-call-string context, routed by truncated call history\<close>

text \<open>
  The \<open>k = 2\<close> sibling of \<^theory>\<open>Voblint_Examples.Example_Sign_DG_CallString_K1\<close>, same
  \<open>sign_nest\<close> program and same Base-style storage: \<open>g\<close>'s single call site is reached from
  two different \<open>f\<close> activations. At \<open>k = 1\<close> both collapse into one merged context and
  \<open>g\<close>'s entry parameter joins to \<open>STop\<close>; at \<open>k = 2\<close> the call string also records which
  \<open>f\<close> call led there, so the two activations stay separate and \<open>g\<close>'s entry parameter is
  \<open>SPos\<close> in one context, \<open>SNeg\<close> in the other. Only the bound changes --- the
  specification, the transport, and the routed locale are the ones \<open>k = 1\<close> already fixed.
\<close>

subsection \<open>The routed equation system and its computed solution\<close>

text \<open>Reuses \<^type>\<open>call_string_gk\<close> from \<^theory>\<open>Voblint_Framework.Call_String_Context\<close> rather
  than minting its own global-key type: the key shape never depended on \<open>k\<close>, only the
  \<open>Seed\<close> payload's context length did.\<close>

definition sign_nest_2_eqs ::
  "(pp \<times> cfg_node list, call_string_gk,
     (sign exec_dg_st lifted, sign exec_dg_st lifted) dg_state) eqsT" where
  "sign_nest_2_eqs =
     routed_node_rhs intra_predecessor_addr_list (\<lambda>_. Global) (cs_route 2)
       (\<lambda>ctx' src a. dg_spec_edge_tree sign_nest_S_st a src (\<lambda>_. Global))
       (routed_call_tree sign_nest_S_st Global Seed (static_resolve sign_nest_cfg)
          (\<lambda>d. d = Bot))
       (routed_entry_seed_tree Seed)
       sign_nest_cfg Bot (Lifted cinit_sign_st) Bot"

definition sign_nest_2_sol ::
  "(pp \<times> cfg_node list) set
     \<times> (pp \<times> cfg_node list + call_string_gk
          \<Rightarrow> (sign exec_dg_st lifted, sign exec_dg_st lifted) dg_state)" where
  "sign_nest_2_sol = TD_side_always_join_Interp_solve sign_nest_2_eqs
                       (cfg_exit sign_nest_cfg, [])"

lemma sign_nest_2_terminates:
  "TD_side_always_join_Interp_solve_c sign_nest_2_eqs (cfg_exit sign_nest_cfg, []) \<noteq> None"
  by eval

subsection \<open>Coverage\<close>

text \<open>The full solved node set, computed once; every membership fact below is a
  \<open>simp\<close> lookup into this literal set instead of a separate \<open>eval\<close> re-derivation.\<close>

definition sign_nest_2_nodes :: "(pp \<times> cfg_node list) set" where
  "sign_nest_2_nodes = {
     (FunctionEntry (STR ''main''), []), (Statement 5, []), (Statement 6, []), (Statement 7, []),
     (FunctionEntry (STR ''f''), [Statement 5]), (Statement 2, [Statement 5]),
     (Statement 3, [Statement 5]), (FunctionResult (STR ''f''), [Statement 5]),
     (FunctionEntry (STR ''f''), [Statement 6]), (Statement 2, [Statement 6]),
     (Statement 3, [Statement 6]), (FunctionResult (STR ''f''), [Statement 6]),
     (FunctionEntry (STR ''g''), [Statement 2, Statement 5]), (Statement 0, [Statement 2, Statement 5]),
     (FunctionResult (STR ''g''), [Statement 2, Statement 5]),
     (FunctionEntry (STR ''g''), [Statement 2, Statement 6]), (Statement 0, [Statement 2, Statement 6]),
     (FunctionResult (STR ''g''), [Statement 2, Statement 6]),
     (FunctionResult (STR ''main''), [])}"

lemma sign_nest_2_nodes_eq: "fst sign_nest_2_sol = sign_nest_2_nodes"
  unfolding sign_nest_2_sol_def sign_nest_2_eqs_def sign_nest_2_nodes_def by eval

lemma entry_covered_2: "(cfg_entry sign_nest_cfg, []) \<in> fst sign_nest_2_sol"
  unfolding sign_nest_entry sign_nest_2_nodes_eq sign_nest_2_nodes_def by simp

lemma sign_nest_fwd_closed_all_2:
  "\<forall>(u, c)\<in>fst sign_nest_2_sol. \<forall>(u', a, v)\<in>intra sign_nest_cfg.
      u = u' \<longrightarrow> (v, c) \<in> fst sign_nest_2_sol"
  unfolding sign_nest_2_sol_def sign_nest_2_eqs_def by eval

lemma sign_nest_fwd_closed_2:
  assumes "(u, ctx) \<in> fst sign_nest_2_sol" and "(u, a, v) \<in> intra sign_nest_cfg"
  shows "(v, ctx) \<in> fst sign_nest_2_sol"
  using sign_nest_fwd_closed_all_2 assms by fastforce

text \<open>Unlike \<open>k = 1\<close>, \<open>g\<close>'s call site is now covered at two \<^emph>\<open>distinct\<close> two-element
  contexts, one per \<open>f\<close> activation that reaches it.\<close>

lemma enter_callers_only_root_main_2:
  "\<forall>(p, ctx)\<in>fst sign_nest_2_sol.
     (p = Statement 5 \<or> p = Statement 6) \<longrightarrow> ctx = []"
  unfolding sign_nest_2_nodes_eq sign_nest_2_nodes_def by simp

lemma enter_callers_g_2:
  "\<forall>(p, ctx)\<in>fst sign_nest_2_sol.
     p = Statement 2 \<longrightarrow> ctx = [Statement 5] \<or> ctx = [Statement 6]"
  unfolding sign_nest_2_nodes_eq sign_nest_2_nodes_def by simp

lemma callee_covered_fpos_2: "(FunctionEntry (STR ''f''), [Statement 5]) \<in> fst sign_nest_2_sol"
  unfolding sign_nest_2_nodes_eq sign_nest_2_nodes_def by simp
lemma callee_covered_fneg_2: "(FunctionEntry (STR ''f''), [Statement 6]) \<in> fst sign_nest_2_sol"
  unfolding sign_nest_2_nodes_eq sign_nest_2_nodes_def by simp
lemma callee_covered_g_fpos_2:
  "(FunctionEntry (STR ''g''), [Statement 2, Statement 5]) \<in> fst sign_nest_2_sol"
  unfolding sign_nest_2_nodes_eq sign_nest_2_nodes_def by simp
lemma callee_covered_g_fneg_2:
  "(FunctionEntry (STR ''g''), [Statement 2, Statement 6]) \<in> fst sign_nest_2_sol"
  unfolding sign_nest_2_nodes_eq sign_nest_2_nodes_def by simp

lemma covered_ret6_2: "(Statement 6, []) \<in> fst sign_nest_2_sol"
  unfolding sign_nest_2_nodes_eq sign_nest_2_nodes_def by simp
lemma covered_ret7_2: "(Statement 7, []) \<in> fst sign_nest_2_sol"
  unfolding sign_nest_2_nodes_eq sign_nest_2_nodes_def by simp
lemma covered_ret3_fpos_2: "(Statement 3, [Statement 5]) \<in> fst sign_nest_2_sol"
  unfolding sign_nest_2_nodes_eq sign_nest_2_nodes_def by simp
lemma covered_ret3_fneg_2: "(Statement 3, [Statement 6]) \<in> fst sign_nest_2_sol"
  unfolding sign_nest_2_nodes_eq sign_nest_2_nodes_def by simp


section \<open>The solver's post-solution\<close>

lemma sign_nest_2_solve_dom:
  "TD_side_always_join_Interp.solve_dom TYPE(call_string_gk)
     TYPE((sign exec_dg_st lifted, sign exec_dg_st lifted) dg_state)
     sign_nest_2_eqs (cfg_exit sign_nest_cfg, [])"
  by (rule TD_side_always_join_Interp.solve_dom_of_solve_c[OF sign_nest_2_terminates])

lemma sign_nest_2_pp_st:
  "part_post_solution sign_nest_2_eqs (cfg_exit sign_nest_cfg, [])
     (snd sign_nest_2_sol) (fst sign_nest_2_sol)"
  using TD_side_always_join_Interp.partial_post_solution
          [OF sign_nest_2_solve_dom, of "fst sign_nest_2_sol" "snd sign_nest_2_sol"]
  unfolding sign_nest_2_sol_def by simp

abbreviation sigma_2 ::
  "pp \<times> cfg_node list + call_string_gk
     \<Rightarrow> (sign exec_dg_st lifted, sign exec_dg_st lifted) dg_state" where
  "sigma_2 \<equiv> snd sign_nest_2_sol"

section \<open>Activation-indexed collecting soundness for the 2-call-string-routed solution\<close>

definition sign_ctx_sg_2 ::
  "pp \<times> cfg_node list + call_string_gk \<Rightarrow> sign exec_dg_st lifted" where
  "sign_ctx_sg_2 z =
     (case z of
        Inl (v, ctx) \<Rightarrow>
          (if (v, ctx) \<in> fst sign_nest_2_sol then locals (sigma_2 (Inl (v, ctx))) else Bot)
      | Inr _ \<Rightarrow> Bot)"

lemma sign_ctx_sg_2_covered:
  "(v, ctx) \<in> fst sign_nest_2_sol
     \<Longrightarrow> sign_ctx_sg_2 (Inl (v, ctx)) = locals (sigma_2 (Inl (v, ctx)))"
  by (simp add: sign_ctx_sg_2_def)

lemma sign_ctx_sg_2_uncovered_empty:
  "(v, ctx) \<notin> fst sign_nest_2_sol
     \<Longrightarrow> gamma_state_lift (map_lift (fun_of_resolved_st_q_for sign_nest_gs)
           (sign_ctx_sg_2 (Inl (v, ctx)))) = {}"
  by (simp add: sign_ctx_sg_2_def)

text \<open>Unlike \<open>k = 1\<close>, \<open>call_fwd\<close>'s \<open>Statement 2\<close> case now genuinely splits: \<open>g\<close>'s call site
  is covered at two distinct one-element contexts, and \<open>take 2\<close> keeps them apart after
  routing, so each needs its own coverage witness. Everything else the routed locale asks
  for is discharged generically at \<^const>\<open>cs_route\<close>, exactly as at \<open>k = 1\<close>.\<close>

interpretation sign_nest_2_cs: call_string_routed_context
    sign_nest_S_st sign_nest_gamma sign_nest_gs sign_nest_pi sign_nest_procs 2
    Bot "Lifted cinit_sign_st" Bot
    sigma_2 "fst sign_nest_2_sol" "(cfg_exit sign_nest_cfg, [])" sign_ctx_sg_2
    "\<lambda>d. d = Bot"
    "\<lambda>m. gamma_state_lift (map_lift (fun_of_resolved_st_q_for sign_nest_gs) m)"
proof (unfold_locales, unfold sign_nest_cfg_compile,
       goal_cases FinE PP SgCov SgUncov Fwd IsBotBot IsBotSound
       EnterComplete CallFwd CombFwd)
  case FinE
  show ?case by (rule sign_nest_finE)
next
  case PP
  show ?case by (rule sign_nest_2_pp_st[unfolded sign_nest_2_eqs_def])
next
  case (SgCov v c)
  show ?case using SgCov by (simp add: sign_ctx_sg_2_covered sign_nest_gamma_def)
next
  case (SgUncov v c)
  show ?case using SgUncov by (rule sign_ctx_sg_2_uncovered_empty)
next
  case (Fwd u a v c)
  show ?case using Fwd by (rule sign_nest_fwd_closed_2)
next
  case IsBotBot show ?case by simp
next
  case (IsBotSound d gv) then show ?case by (simp add: sign_nest_gamma_eq)
next
  case (EnterComplete u ctx dst pars args p cont s)
  let ?ci = "call_info_of (CallEdge dst pars args) p"
  let ?caller = "locals (sigma_2 (Inl (u, ctx)))"
  have cov: "entry_pairs_cover (\<lambda>d. sign_nest_gamma d (globs (sigma_2 (Inr Global)))) s
      (call_enter sign_nest_gs (CallEdge dst pars args) s)
      [(?caller, transfer_lift sign_nest_empty_pred (sign_enter_st_for sign_nest_gs ?ci)
                   ?caller)]"
    using sign_nest_domain.entry_pairs_cover_st
            [OF sign_is_sound_transfer_for, where ci = ?ci and d = ?caller]
      EnterComplete(3)
    by (simp add: sign_nest_gamma_eq sign_nest_domain.gamma_exec_def)
  show ?case
    unfolding sign_nest_S_st_def dgs_enter_local_state_st_for_lifted
    using enter_runs_local_enter_transfer enter_deps_local_enter_transfer cov by fastforce
next
  case (CallFwd u ctx dst pars args p cont)
  note covU = CallFwd(1) and ce = CallFwd(2)
  from ce sign_nest_calls_shape have
    "(u = Statement 2 \<and> p = (STR ''g'') \<and> cont = Statement 3) \<or>
     (u = Statement 5 \<and> p = (STR ''f'') \<and> cont = Statement 6) \<or>
     (u = Statement 6 \<and> p = (STR ''f'') \<and> cont = Statement 7)"
    by fastforce
  then consider
      (c1) "u = Statement 2" "p = (STR ''g'')"
    | (c2) "u = Statement 5" "p = (STR ''f'')"
    | (c3) "u = Statement 6" "p = (STR ''f'')"
    by blast
  thus ?case
  proof cases
    case c1
    from covU c1 enter_callers_g_2 have "ctx = [Statement 5] \<or> ctx = [Statement 6]" by fastforce
    thus ?thesis
    proof
      assume "ctx = [Statement 5]"
      thus ?thesis using c1 callee_covered_g_fpos_2 by (simp add: cs_route_def)
    next
      assume "ctx = [Statement 6]"
      thus ?thesis using c1 callee_covered_g_fneg_2 by (simp add: cs_route_def)
    qed
  next
    case c2
    have ctx0: "ctx = []" using covU c2 enter_callers_only_root_main_2 by fastforce
    thus ?thesis using c2 callee_covered_fpos_2 by (simp add: cs_route_def)
  next
    case c3
    have ctx0: "ctx = []" using covU c3 enter_callers_only_root_main_2 by fastforce
    thus ?thesis using c3 callee_covered_fneg_2 by (simp add: cs_route_def)
  qed
next
  case (CombFwd cl c1 dst pars args p cont)
  show ?case
    using CombFwd enter_callers_only_root_main_2 enter_callers_g_2
          covered_ret3_fpos_2 covered_ret3_fneg_2 covered_ret6_2 covered_ret7_2
          sign_nest_calls_shape
    by fastforce
qed

lemma sign_ctx_sg_2_seed:
  assumes "(u, CallEdge dst xs es, FunctionEntry p, cont) \<in> calls sign_nest_cfg"
    and "s \<in> gamma_state_lift (map_lift (fun_of_resolved_st_q_for sign_nest_gs)
               (sign_ctx_sg_2 (Inl (u, ctx))))"
  shows "call_enter sign_nest_gs (CallEdge dst xs es) s
           \<in> gamma_state_lift (map_lift (fun_of_resolved_st_q_for sign_nest_gs)
               (sign_ctx_sg_2 (Inl (FunctionEntry p,
                 cs_context 2 u ctx (call_enter sign_nest_gs (CallEdge dst xs es) s)))))"
proof (rule sign_nest_2_cs.routed_context_call[OF assms[unfolded sign_nest_cfg_def]])
  show "call_context_rel_of_fun (cs_context 2) u ctx (call_info_of (CallEdge dst xs es) p) s
          (call_enter sign_nest_gs (CallEdge dst xs es) s)
          (cs_context 2 u ctx (call_enter sign_nest_gs (CallEdge dst xs es) s))"
    by simp
qed

lemma sign_ctx_sg_2_comb:
  assumes "(cl, CallEdge dst pars args, FunctionEntry p, v) \<in> calls sign_nest_cfg"
    and "s \<in> gamma_state_lift (map_lift (fun_of_resolved_st_q_for sign_nest_gs)
               (sign_ctx_sg_2 (Inl (cl, c1))))"
    and "t \<in> gamma_state_lift (map_lift (fun_of_resolved_st_q_for sign_nest_gs)
               (sign_ctx_sg_2 (Inl (FunctionResult p, cs_context 2 cl c1 es))))"
    and "call_enter_store sign_nest_gs sign_nest_cfg cl s es"
  shows "combine_collect sign_nest_gs dst s t
           \<in> gamma_state_lift (map_lift (fun_of_resolved_st_q_for sign_nest_gs)
               (sign_ctx_sg_2 (Inl (v, c1))))"
proof -
  from assms(4) obtain dst' pars' args' p' cont' where
      ce': "(cl, CallEdge dst' pars' args', FunctionEntry p', cont') \<in> calls sign_nest_cfg"
    and es_eq: "es = call_enter sign_nest_gs (CallEdge dst' pars' args') s"
    unfolding call_enter_store_def by blast
  have adm: "admits_call_context sign_nest_gs (compile_prog sign_nest_pi sign_nest_procs)
          (call_context_rel_of_fun (cs_context 2)) cl c1 p' s es (cs_context 2 cl c1 es)"
    unfolding admits_call_context_def call_context_rel_of_fun_iff
    using ce'[unfolded sign_nest_cfg_def] es_eq by blast
  show ?thesis
    by (rule sign_nest_2_cs.routed_context_comb[OF assms(1)[unfolded sign_nest_cfg_def]
          assms(2)[unfolded sign_nest_cfg_def] adm assms(3)[unfolded sign_nest_cfg_def]])
qed

section \<open>The headline theorem: 2-call-string activation collecting soundness\<close>

theorem sign_nest_2_activation_collect_sound:
  "activation_collect sign_nest_gs (call_context_rel_of_fun (cs_context 2)) [] sign_nest_cfg
     (cinit_stores sign_nest_gs) v ctx
     \<subseteq> gamma_state_lift (map_lift (fun_of_resolved_st_q_for sign_nest_gs)
           (sign_ctx_sg_2 (Inl (v, ctx))))"
  by (rule sign_nest_2_cs.activation_collect_sound[unfolded sign_nest_cfg_compile,
            OF entry_covered_2 sign_nest_cinit_le_cinit_sign_st])


section \<open>The precision comparison: k=2 keeps \<open>g\<close>'s two activations separated where k=1 merges them\<close>

text \<open>
  A concrete, executable precision statement for this program and this D/G analysis: the
  1-call-string context collapses \<open>g\<close>'s two activations to one context and their join at
  \<open>STop\<close> loses all sign information, while the 2-call-string context keeps them apart and each
  retains its own exact sign. This is not a general "call strings always improve precision"
  claim --- it is the concrete forcing witness the sign lattice's finiteness lets us compute
  and verify outright, in the style of the paper's context-sensitivity discussion (Tilscher/
  Grass/Seidl, "Verifying a Solver for Mixed Flow-Sensitive Analyses").
\<close>

lemma sign_k2_g_entry_fpos:
  "sign_nest_lookup
     (locals (snd sign_nest_2_sol (Inl (FunctionEntry (STR ''g''), [Statement 2, Statement 5]))))
     (STR ''p'') = SPos"
  unfolding sign_nest_2_sol_def sign_nest_2_eqs_def by eval

lemma sign_k2_g_entry_fneg:
  "sign_nest_lookup
     (locals (snd sign_nest_2_sol (Inl (FunctionEntry (STR ''g''), [Statement 2, Statement 6]))))
     (STR ''p'') = SNeg"
  unfolding sign_nest_2_sol_def sign_nest_2_eqs_def by eval

theorem sign_k2_strictly_more_precise_than_k1_at_g:
  "sign_nest_lookup
     (locals (snd sign_nest_2_sol (Inl (FunctionEntry (STR ''g''), [Statement 2, Statement 5]))))
     (STR ''p'')
     < sign_nest_lookup
         (locals (snd sign_nest_1_sol (Inl (FunctionEntry (STR ''g''), [Statement 2]))))
         (STR ''p'')"
  "sign_nest_lookup
     (locals (snd sign_nest_2_sol (Inl (FunctionEntry (STR ''g''), [Statement 2, Statement 6]))))
     (STR ''p'')
     < sign_nest_lookup
         (locals (snd sign_nest_1_sol (Inl (FunctionEntry (STR ''g''), [Statement 2]))))
         (STR ''p'')"
  by (simp_all add: sign_nest_1_g_entry_merged sign_k2_g_entry_fpos sign_k2_g_entry_fneg
                    less_sign_def sign_le_refl)

end

