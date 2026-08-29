theory Example_Sign_DG_CallString_K1
  imports
    "Voblint_Core.DG_LTR_Sound"
    "Voblint_Analysis.Sign_Transfer"
    "Voblint_Analysis.Sign_Exec"
    "Voblint_Core.DG_Base_Exec"
    "Voblint_Core.Call_String_Routed_Context"
    "Voblint_Core.Activation_Backbone"
    "Voblint_Core.Solver_Menu"
    "Voblint_Soundness.Run_Analysis_Sound"
    "Voblint_VIMP.VIMP_Notation"
begin

section \<open>A computed 1-call-string context, routed by truncated call history\<close>

text \<open>
  Sign counterpart of the Interval call-string pair, on the same \<open>nest\<close> shape: \<open>main\<close>
  calls \<open>f\<close> from two distinct sites, and \<open>f\<close> calls \<open>g\<close> from one site inside its own body,
  with one positive and one negative argument so the Sign domain separates the two
  \<open>f\<close>-activations. \<open>g\<close>'s immediate call site is identical for both activations, so a
  1-call-string context cannot separate them --- only a longer call string, keying on
  which \<open>f\<close> call led there, can.

  Storage is Base-style: the local unknown carries the whole abstract state on the lifted
  carrier \<^typ>\<open>sign exec_dg_st lifted\<close>, so a global is read and written exactly where a
  local is, and the solver-global carrier is inert --- every field of
  \<^const>\<open>base_dg_spec_st_for_lifted\<close> threads its incoming \<open>g\<close> through unchanged, so
  \<open>Inr Global\<close> is never read back to reconstruct program state. Only the routing policy
  (\<^const>\<open>cs_route\<close>, \<^const>\<open>cs_context\<close>) is call-string specific; the storage, the transfer
  primitives, and the CALL/COMB discharge are shared with every other Base-style analysis.

  Sign is a finite lattice, so the plain join update rule \<open>TD_side_always_join_Interp\<close>
  terminates on this loop-free program and reaches the true least fixpoint --- no widening
  or narrowing is invoked, matching the optimality precondition of the underlying solver
  theory.
\<close>

definition sign_nest_program :: imp_prog where
  "sign_nest_program = program {
     void g(p) { return p + p }
     void f(p) { t := g(p); return t }
     void main() { x := f(3); y := f(-10) }
   }"

text \<open>The storage classifier: \<open>sign_nest_program\<close> declares no globals, so
  \<open>sign_nest_gs\<close> classifies every variable this chain touches as local.\<close>
abbreviation sign_nest_gs :: "vname \<Rightarrow> bool" where
  "sign_nest_gs \<equiv> declared_global sign_nest_program"

text \<open>Reading one variable off a lifted whole-state local unknown: an unreachable point
  (\<^const>\<open>Bot\<close>) reads \<open>bot\<close> at every variable.\<close>
abbreviation sign_nest_lookup :: "sign exec_dg_st lifted \<Rightarrow> vname \<Rightarrow> sign" where
  "sign_nest_lookup d x \<equiv>
     (case d of Bot \<Rightarrow> bot | Lifted d0 \<Rightarrow> lookup_resolved_st_q d0 (location_of sign_nest_gs x))"

definition sign_nest_pi :: proc_table where "sign_nest_pi = prog_table sign_nest_program"
definition sign_nest_procs :: "pname list" where "sign_nest_procs = prog_procs sign_nest_program"
definition sign_nest_main :: "VIMP_Proc.com" where "sign_nest_main = prog_main sign_nest_program"

definition sign_nest_cfg :: cfg where
  "sign_nest_cfg = compile_prog sign_nest_pi sign_nest_procs"

text \<open>The compiled CFG, folded back under its own name: every obligation the routed
  locale states is phrased in \<^const>\<open>compile_prog\<close>, every fact below in \<open>sign_nest_cfg\<close>.\<close>
lemma sign_nest_cfg_compile [simp]:
  "compile_prog sign_nest_pi sign_nest_procs = sign_nest_cfg"
  by (simp add: sign_nest_cfg_def)

lemma sign_nest_entry: "cfg_entry sign_nest_cfg = FunctionEntry (STR ''main'')"
  by (simp only: sign_nest_cfg_def cfg_entry_compile_prog prog_main_name_def)

lemma sign_nest_finE: "finite (intra sign_nest_cfg)"
  unfolding sign_nest_cfg_def using compile_prog_finite by blast

text \<open>The three call edges' shape, computed directly from \<open>sign_nest_cfg\<close>: each call site
  \<open>u\<close> pins down its callee \<open>p\<close> and continuation \<open>cont\<close>. \<open>g\<close> is called once, from inside
  \<open>f\<close>, at the same source location regardless of which \<open>f\<close>-activation runs it.\<close>
lemma sign_nest_calls_shape:
  "\<forall>(u, ca, ce, cont) \<in> calls sign_nest_cfg.
     case ca of CallEdge dst pars args \<Rightarrow>
       (case ce of FunctionEntry p \<Rightarrow>
          (u = Statement 2 \<and> p = (STR ''g'') \<and> cont = Statement 3) \<or>
          (u = Statement 5 \<and> p = (STR ''f'') \<and> cont = Statement 6) \<or>
          (u = Statement 6 \<and> p = (STR ''f'') \<and> cont = Statement 7)
        | _ \<Rightarrow> True)"
  unfolding sign_nest_cfg_def by eval

subsection \<open>The Base-style sign specification, executable and abstract\<close>

text \<open>The executable bottom predicate the lifted carrier needs, at this program's own
  declared globals; \<open>sign_nest_exact\<close> is the exactness fact every transport step below
  consumes.\<close>

definition sign_nest_is_bot_pred :: "sign resolved_st_q \<Rightarrow> bool" where
  "sign_nest_is_bot_pred = resolved_st_q_is_bot_for (declared_global_vars sign_nest_program)"

lemma sign_nest_exact:
  "sign_nest_is_bot_pred s = is_bot_state (fun_of_resolved_st_q_for sign_nest_gs s)"
  unfolding sign_nest_is_bot_pred_def by (rule resolved_st_q_is_bot_for_iff) simp

text \<open>The same Base-style pair every other Sign analysis solves over, at the same
  \<^const>\<open>sign_tf_st_for\<close>/\<^const>\<open>sign_enter_st_for\<close> primitives: nothing call-string
  specific enters the specification.\<close>

definition sign_nest_S_st :: "(sign exec_dg_st lifted, sign exec_dg_st lifted) dg_spec" where
  "sign_nest_S_st = base_dg_spec_st_for_lifted sign_nest_gs sign_nest_is_bot_pred
                      (sign_tf_st_for sign_nest_gs) (sign_enter_st_for sign_nest_gs)"

definition sign_nest_S_abs :: "(sign abs_state lifted, sign abs_state lifted) dg_spec" where
  "sign_nest_S_abs = base_dg_spec_for_lifted sign_nest_gs is_bot_state (sign_tf_for sign_nest_gs)"

subsection \<open>Executable-to-abstract transport, once for every bound\<close>

text \<open>The readback is the lifted \<^const>\<open>fun_of_resolved_st_q_for\<close>, used identically for the
  local and the (inert) global carrier. Every commute below is an instance of the generic
  Base-style engine; only Sign's own primitive facts are supplied.\<close>

lemma sign_nest_dg_reader:
  "dg_reader_commute_gen (map_lift (fun_of_resolved_st_q_for sign_nest_gs))
     (map_lift (fun_of_resolved_st_q_for sign_nest_gs))"
  by unfold_locales (simp_all add: map_lift_sup fun_of_resolved_st_q_for_sup)

lemma sign_nest_Hstep:
  "map_prod (map_lift (fun_of_resolved_st_q_for sign_nest_gs))
      (map_lift (fun_of_resolved_st_q_for sign_nest_gs))
     (dg_spec_step sign_nest_S_st a d g)
   = dg_spec_step sign_nest_S_abs a (map_lift (fun_of_resolved_st_q_for sign_nest_gs) d)
       (map_lift (fun_of_resolved_st_q_for sign_nest_gs) g)"
  unfolding sign_nest_S_st_def sign_nest_S_abs_def
  by (rule base_dg_spec_st_for_lifted_dg_spec_step_commute
        [unfolded fun_of_exec_dg_st_for_def, OF sign_tf_st_for_commute sign_nest_exact])

lemma sign_nest_Henter:
  "map_prod (map_lift (fun_of_resolved_st_q_for sign_nest_gs))
      (map_lift (fun_of_resolved_st_q_for sign_nest_gs))
     (dgs_enter sign_nest_S_st xs es d g)
   = dgs_enter sign_nest_S_abs xs es (map_lift (fun_of_resolved_st_q_for sign_nest_gs) d)
       (map_lift (fun_of_resolved_st_q_for sign_nest_gs) g)"
  unfolding sign_nest_S_st_def sign_nest_S_abs_def
  by (rule base_dg_spec_st_for_lifted_dgs_enter_commute
        [unfolded fun_of_exec_dg_st_for_def, OF sign_enter_st_for_commute sign_nest_exact])

lemma sign_nest_Hcomb:
  "map_prod (map_lift (fun_of_resolved_st_q_for sign_nest_gs))
      (map_lift (fun_of_resolved_st_q_for sign_nest_gs))
     (dgs_combine sign_nest_S_st dst dc de g)
   = dgs_combine sign_nest_S_abs dst (map_lift (fun_of_resolved_st_q_for sign_nest_gs) dc)
       (map_lift (fun_of_resolved_st_q_for sign_nest_gs) de)
       (map_lift (fun_of_resolved_st_q_for sign_nest_gs) g)"
  unfolding sign_nest_S_st_def sign_nest_S_abs_def
  by (rule base_dg_spec_st_for_lifted_dgs_combine_commute
        [where tf = "sign_tf_for sign_nest_gs", unfolded fun_of_exec_dg_st_for_def,
         OF sign_nest_exact])

lemma sign_nest_Hcont:
  "map_lift (fun_of_resolved_st_q_for sign_nest_gs) (caller_cont sign_nest_S_st ci dc g)
   = caller_cont sign_nest_S_abs ci (map_lift (fun_of_resolved_st_q_for sign_nest_gs) dc)
       (map_lift (fun_of_resolved_st_q_for sign_nest_gs) g)"
  unfolding sign_nest_S_st_def sign_nest_S_abs_def
  by (rule base_dg_spec_st_for_lifted_dgs_caller_cont_commute
        [where tf = "sign_tf_for sign_nest_gs", unfolded fun_of_exec_dg_st_for_def])

lemma sign_nest_seed_ne_global: "Seed p ctx \<noteq> Global" by simp

text \<open>\<^const>\<open>cs_route\<close> never reads its data argument, so the routed combine and the routed
  entry-seed read transport for ``any'' bound \<open>k\<close> at once: \<open>cs_route_indep_of_data\<close> is the
  whole route-agreement obligation, with no per-domain commute lemma.\<close>

lemma sign_nest_Hcmb_routed:
  "dg_reader_commute_gen.dg_tree_st_commute
     (map_lift (fun_of_resolved_st_q_for sign_nest_gs))
     (map_lift (fun_of_resolved_st_q_for sign_nest_gs)) sigma_st
     (routed_cmb_g sign_nest_S_st Global Seed (static_resolve sign_nest_cfg)
        (cs_route k) ctx ca cc ex)
     (routed_cmb_g sign_nest_S_abs Global Seed (static_resolve sign_nest_cfg)
        (cs_route k) ctx ca cc ex)"
  by (rule dg_reader_commute_gen.dg_tree_st_commute_routed_cmb_g
        [OF sign_nest_dg_reader sign_nest_seed_ne_global sign_nest_Henter sign_nest_Hcomb
            sign_nest_Hcont
            cs_route_indep_of_data])
     (simp add: static_resolve_def)
lemma sign_nest_Hextra_routed:
  "list_all2 (dg_reader_commute_gen.dg_tree_st_commute
                (map_lift (fun_of_resolved_st_q_for sign_nest_gs))
                (map_lift (fun_of_resolved_st_q_for sign_nest_gs)) sigma_st)
     (routed_extra_g Seed Global route_st ctx w)
     (routed_extra_g Seed Global route_abs ctx w)"
  by (rule dg_reader_commute_gen.dg_tree_st_commute_routed_extra_g[OF sign_nest_dg_reader])

text \<open>The whole post-solution transport, stated once for a free bound \<open>k\<close>: both the \<open>k = 1\<close>
  system here and its \<open>k = 2\<close> sibling instantiate this single lemma.\<close>

lemma sign_nest_pp_abs_of_st:
  assumes pp: "part_post_solution
       (side_cfg_T_eff_keyed_seed_dg intra_predecessor_addr_list (\<lambda>_. Global) (cs_route k)
          (routed_cmb_g sign_nest_S_st Global Seed (static_resolve sign_nest_cfg))
          (routed_extra_g Seed Global)
          sign_nest_cfg sign_nest_S_st Bot (Lifted cinit_sign_st) Bot)
       x sigma_st vars"
  shows "part_post_solution
       (side_cfg_T_eff_keyed_seed_dg intra_predecessor_addr_list (\<lambda>_. Global) (cs_route k)
          (routed_cmb_g sign_nest_S_abs Global Seed (static_resolve sign_nest_cfg))
          (routed_extra_g Seed Global)
          sign_nest_cfg sign_nest_S_abs
          (map_lift (fun_of_resolved_st_q_for sign_nest_gs) (Bot::sign exec_dg_st lifted))
          (map_lift (fun_of_resolved_st_q_for sign_nest_gs) (Lifted cinit_sign_st))
          (map_lift (fun_of_resolved_st_q_for sign_nest_gs) (Bot::sign exec_dg_st lifted)))
       x (fun_of_dg_st_gen (map_lift (fun_of_resolved_st_q_for sign_nest_gs))
            (map_lift (fun_of_resolved_st_q_for sign_nest_gs)) \<circ> sigma_st) vars"
  by (rule part_post_solution_seed_dg_st_to_abs_lifted_for
        [where gs = sign_nest_gs and pred_sel = intra_predecessor_addr_list and gkey = "\<lambda>_. Global"
           and route_st = "cs_route k" and route_abs = "cs_route k"
           and cmb_st = "routed_cmb_g sign_nest_S_st Global Seed (static_resolve sign_nest_cfg)"
           and cmb_abs = "routed_cmb_g sign_nest_S_abs Global Seed (static_resolve sign_nest_cfg)"
           and extra_st = "routed_extra_g Seed Global"
           and extra_abs = "routed_extra_g Seed Global"
           and g = sign_nest_cfg and S_st = sign_nest_S_st and S_abs = sign_nest_S_abs,
         OF sign_nest_Hstep cs_route_indep_of_data sign_nest_Hcmb_routed
            sign_nest_Hextra_routed pp])

text \<open>The abstract specification is sound for the Base-style concretization
  \<^const>\<open>gamma_dg_base\<close>, which discards its inert \<open>'G\<close> argument outright.\<close>

interpretation sign_nest_dg_sound: sound_dg_spec sign_nest_S_abs gamma_dg_base sign_nest_gs
  unfolding sign_nest_S_abs_def
  by (rule base_dg_spec_sound[OF sign_is_sound_transfer_for is_bot_state_gamma_state_empty])

subsection \<open>The routed equation system and its computed solution\<close>

text \<open>The global-key type \<^type>\<open>call_string_gk\<close> and its truncation
  \<^const>\<open>cs_project_gk\<close> come from \<^theory>\<open>Voblint_Core.Call_String_Context\<close>: the key
  shape never depended on \<open>k\<close> or on this program.\<close>

definition sign_nest_1_eqs ::
  "(pp \<times> cfg_node list, call_string_gk,
     (sign exec_dg_st lifted, sign exec_dg_st lifted) dg_state) eqsT" where
  "sign_nest_1_eqs =
     side_cfg_T_eff_keyed_seed_dg intra_predecessor_addr_list (\<lambda>_. Global) (cs_route 1)
       (routed_cmb_g sign_nest_S_st Global Seed (static_resolve sign_nest_cfg))
       (routed_extra_g Seed Global)
       sign_nest_cfg sign_nest_S_st Bot (Lifted cinit_sign_st) Bot"

definition sign_nest_1_sol ::
  "(pp \<times> cfg_node list) set
     \<times> (pp \<times> cfg_node list + call_string_gk
          \<Rightarrow> (sign exec_dg_st lifted, sign exec_dg_st lifted) dg_state)" where
  "sign_nest_1_sol = TD_side_always_join_Interp_solve sign_nest_1_eqs
                       (cfg_exit sign_nest_cfg, [])"

lemma sign_nest_1_terminates:
  "TD_side_always_join_Interp_solve_c sign_nest_1_eqs (cfg_exit sign_nest_cfg, []) \<noteq> None"
  by eval

subsection \<open>Coverage\<close>

text \<open>The full solved node set, computed once; every membership fact below is a
  \<open>simp\<close> lookup into this literal set instead of a separate \<open>eval\<close> re-derivation.\<close>

definition sign_nest_1_nodes :: "(pp \<times> cfg_node list) set" where
  "sign_nest_1_nodes = {
     (FunctionEntry (STR ''main''), []), (Statement 5, []),
     (FunctionEntry (STR ''f''), [Statement 5]), (Statement 2, [Statement 5]),
     (FunctionEntry (STR ''g''), [Statement 2]), (Statement 0, [Statement 2]),
     (FunctionResult (STR ''g''), [Statement 2]), (Statement 3, [Statement 5]),
     (FunctionResult (STR ''f''), [Statement 5]), (Statement 6, []),
     (FunctionEntry (STR ''f''), [Statement 6]), (Statement 2, [Statement 6]),
     (Statement 3, [Statement 6]), (FunctionResult (STR ''f''), [Statement 6]),
     (Statement 7, []), (FunctionResult (STR ''main''), [])}"

lemma sign_nest_1_nodes_eq: "fst sign_nest_1_sol = sign_nest_1_nodes"
  unfolding sign_nest_1_sol_def sign_nest_1_eqs_def sign_nest_1_nodes_def by eval

lemma entry_covered_1: "(cfg_entry sign_nest_cfg, []) \<in> fst sign_nest_1_sol"
  unfolding sign_nest_entry sign_nest_1_nodes_eq sign_nest_1_nodes_def by simp

lemma sign_nest_fwd_closed_all_1:
  "\<forall>(u, c)\<in>fst sign_nest_1_sol. \<forall>(u', a, v)\<in>intra sign_nest_cfg.
      u = u' \<longrightarrow> (v, c) \<in> fst sign_nest_1_sol"
  unfolding sign_nest_1_sol_def sign_nest_1_eqs_def by eval

lemma sign_nest_fwd_closed_1:
  assumes "(u, ctx) \<in> fst sign_nest_1_sol" and "(u, a, v) \<in> intra sign_nest_cfg"
  shows "(v, ctx) \<in> fst sign_nest_1_sol"
  using sign_nest_fwd_closed_all_1 assms by fastforce

text \<open>\<open>main\<close>'s two call sites are only ever reached at the root context: \<open>main\<close> is never
  itself called. \<open>f\<close>'s one call site (to \<open>g\<close>) is reached at either of \<open>f\<close>'s two activation
  contexts, never at the root --- \<open>g\<close> is only ever called from inside \<open>f\<close>.\<close>

lemma enter_callers_only_root_main_1:
  "\<forall>(p, ctx)\<in>fst sign_nest_1_sol.
     (p = Statement 5 \<or> p = Statement 6) \<longrightarrow> ctx = []"
  unfolding sign_nest_1_nodes_eq sign_nest_1_nodes_def by simp

lemma enter_callers_g_1:
  "\<forall>(p, ctx)\<in>fst sign_nest_1_sol.
     p = Statement 2 \<longrightarrow> ctx = [Statement 5] \<or> ctx = [Statement 6]"
  unfolding sign_nest_1_nodes_eq sign_nest_1_nodes_def by simp

lemma callee_covered_fpos_1: "(FunctionEntry (STR ''f''), [Statement 5]) \<in> fst sign_nest_1_sol"
  unfolding sign_nest_1_nodes_eq sign_nest_1_nodes_def by simp
lemma callee_covered_fneg_1: "(FunctionEntry (STR ''f''), [Statement 6]) \<in> fst sign_nest_1_sol"
  unfolding sign_nest_1_nodes_eq sign_nest_1_nodes_def by simp
lemma callee_covered_g_1: "(FunctionEntry (STR ''g''), [Statement 2]) \<in> fst sign_nest_1_sol"
  unfolding sign_nest_1_nodes_eq sign_nest_1_nodes_def by simp

lemma covered_ret6_1: "(Statement 6, []) \<in> fst sign_nest_1_sol"
  unfolding sign_nest_1_nodes_eq sign_nest_1_nodes_def by simp
lemma covered_ret7_1: "(Statement 7, []) \<in> fst sign_nest_1_sol"
  unfolding sign_nest_1_nodes_eq sign_nest_1_nodes_def by simp
lemma covered_ret3_fpos_1: "(Statement 3, [Statement 5]) \<in> fst sign_nest_1_sol"
  unfolding sign_nest_1_nodes_eq sign_nest_1_nodes_def by simp
lemma covered_ret3_fneg_1: "(Statement 3, [Statement 6]) \<in> fst sign_nest_1_sol"
  unfolding sign_nest_1_nodes_eq sign_nest_1_nodes_def by simp


section \<open>Abstract transport of the routed solution\<close>

lemma sign_nest_1_solve_dom:
  "TD_side_always_join_Interp.solve_dom TYPE(call_string_gk)
     TYPE((sign exec_dg_st lifted, sign exec_dg_st lifted) dg_state)
     sign_nest_1_eqs (cfg_exit sign_nest_cfg, [])"
  by (rule TD_side_always_join_Interp.solve_dom_of_solve_c[OF sign_nest_1_terminates])

lemma sign_nest_1_pp_st:
  "part_post_solution sign_nest_1_eqs (cfg_exit sign_nest_cfg, [])
     (snd sign_nest_1_sol) (fst sign_nest_1_sol)"
  using TD_side_always_join_Interp.partial_post_solution
          [OF sign_nest_1_solve_dom, of "fst sign_nest_1_sol" "snd sign_nest_1_sol"]
  unfolding sign_nest_1_sol_def by simp

abbreviation sigma_1 ::
  "pp \<times> cfg_node list + call_string_gk
     \<Rightarrow> (sign abs_state lifted, sign abs_state lifted) dg_state" where
  "sigma_1 \<equiv>
     fun_of_dg_st_gen (map_lift (fun_of_resolved_st_q_for sign_nest_gs))
       (map_lift (fun_of_resolved_st_q_for sign_nest_gs)) \<circ> snd sign_nest_1_sol"

theorem sign_nest_1_pp_abs:
  "part_post_solution
     (side_cfg_T_eff_keyed_seed_dg intra_predecessor_addr_list (\<lambda>_. Global) (cs_route 1)
       (routed_cmb_g sign_nest_S_abs Global Seed (static_resolve sign_nest_cfg))
       (routed_extra_g Seed Global)
        sign_nest_cfg sign_nest_S_abs
        (map_lift (fun_of_resolved_st_q_for sign_nest_gs) (Bot::sign exec_dg_st lifted))
        (map_lift (fun_of_resolved_st_q_for sign_nest_gs) (Lifted cinit_sign_st))
        (map_lift (fun_of_resolved_st_q_for sign_nest_gs) (Bot::sign exec_dg_st lifted)))
     (cfg_exit sign_nest_cfg, []) sigma_1 (fst sign_nest_1_sol)"
  by (rule sign_nest_pp_abs_of_st[OF sign_nest_1_pp_st[unfolded sign_nest_1_eqs_def]])


section \<open>Activation-indexed collecting soundness for the 1-call-string-routed solution\<close>

definition sign_ctx_sg_1 ::
  "pp \<times> cfg_node list + call_string_gk \<Rightarrow> sign abs_state lifted" where
  "sign_ctx_sg_1 z =
     (case z of
        Inl (v, ctx) \<Rightarrow>
          (if (v, ctx) \<in> fst sign_nest_1_sol then locals (sigma_1 (Inl (v, ctx))) else Bot)
      | Inr _ \<Rightarrow> Bot)"

lemma sign_ctx_sg_1_covered:
  "(v, ctx) \<in> fst sign_nest_1_sol
     \<Longrightarrow> sign_ctx_sg_1 (Inl (v, ctx)) = locals (sigma_1 (Inl (v, ctx)))"
  by (simp add: sign_ctx_sg_1_def)

lemma sign_ctx_sg_1_uncovered_empty:
  "(v, ctx) \<notin> fst sign_nest_1_sol \<Longrightarrow> gamma_state_lift (sign_ctx_sg_1 (Inl (v, ctx))) = {}"
  by (simp add: sign_ctx_sg_1_def)

text \<open>The call-string routing policy instantiated at \<open>k = 1\<close>. The generic locale
  discharges everything that is a fact about \<^const>\<open>cs_route\<close>/\<^const>\<open>cs_context\<close> or about
  \<^const>\<open>compile_prog\<close> alone --- call-edge finiteness, seed-key distinctness, route/context
  agreement, and call-source uniqueness. What stays here is the two coverage obligations
  about this program's own solved system: \<open>g\<close>'s single call site is reached at either of
  \<open>f\<close>'s two activation contexts (\<open>enter_callers_g_1\<close>), but \<open>take 1\<close> erases that distinction
  before it reaches the goal, so \<open>call_fwd\<close> does not need to case-split on which one.\<close>

interpretation sign_nest_1_cs: call_string_routed_context
    sign_nest_S_abs sign_nest_gs sign_nest_pi sign_nest_procs 1
    "map_lift (fun_of_resolved_st_q_for sign_nest_gs) (Bot::sign exec_dg_st lifted)"
    "map_lift (fun_of_resolved_st_q_for sign_nest_gs) (Lifted cinit_sign_st)"
    "map_lift (fun_of_resolved_st_q_for sign_nest_gs) (Bot::sign exec_dg_st lifted)"
    sigma_1 "fst sign_nest_1_sol" "(cfg_exit sign_nest_cfg, [])" sign_ctx_sg_1
proof (unfold_locales, unfold sign_nest_cfg_compile,
       goal_cases FinE PP SgCov SgUncov Fwd CallFwd CombFwd)
  case FinE
  show ?case by (rule sign_nest_finE)
next
  case PP
  show ?case by (rule sign_nest_1_pp_abs)
next
  case (SgCov v c)
  show ?case using SgCov by (simp add: sign_ctx_sg_1_covered gamma_dg_base_def)
next
  case (SgUncov v c)
  show ?case using SgUncov by (rule sign_ctx_sg_1_uncovered_empty)
next
  case (Fwd u a v c)
  show ?case using Fwd by (rule sign_nest_fwd_closed_1)
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
    thus ?thesis using callee_covered_g_1 by (simp add: cs_route_def)
  next
    case c2
    have ctx0: "ctx = []" using covU c2 enter_callers_only_root_main_1 by fastforce
    thus ?thesis using c2 callee_covered_fpos_1 by (simp add: cs_route_def)
  next
    case c3
    have ctx0: "ctx = []" using covU c3 enter_callers_only_root_main_1 by fastforce
    thus ?thesis using c3 callee_covered_fneg_1 by (simp add: cs_route_def)
  qed
next
  case (CombFwd cl c1 dst pars args p cont)
  show ?case
    using CombFwd enter_callers_only_root_main_1 enter_callers_g_1
          covered_ret3_fpos_1 covered_ret3_fneg_1 covered_ret6_1 covered_ret7_1
          sign_nest_calls_shape
    by fastforce
qed

text \<open>CALL and COMB at this program, re-exported from the routed interpretation.\<close>

lemma sign_ctx_sg_1_seed:
  assumes "(u, CallEdge dst xs es, FunctionEntry p, cont) \<in> calls sign_nest_cfg"
    and "s \<in> gamma_state_lift (sign_ctx_sg_1 (Inl (u, ctx)))"
  shows "call_enter sign_nest_gs (CallEdge dst xs es) s
           \<in> gamma_state_lift (sign_ctx_sg_1 (Inl (FunctionEntry p,
                 cs_context 1 u ctx (call_enter sign_nest_gs (CallEdge dst xs es) s))))"
  by (rule sign_nest_1_cs.routed_context_call[OF assms[unfolded sign_nest_cfg_def]])

lemma sign_ctx_sg_1_comb:
  assumes "(cl, CallEdge dst pars args, FunctionEntry p, v) \<in> calls sign_nest_cfg"
    and "s \<in> gamma_state_lift (sign_ctx_sg_1 (Inl (cl, c1)))"
    and "t \<in> gamma_state_lift (sign_ctx_sg_1 (Inl (FunctionResult p, cs_context 1 cl c1 es)))"
    and "call_enter_store sign_nest_gs sign_nest_cfg cl s es"
  shows "combine_collect sign_nest_gs dst s t \<in> gamma_state_lift (sign_ctx_sg_1 (Inl (v, c1)))"
  by (rule sign_nest_1_cs.routed_context_comb[OF assms[unfolded sign_nest_cfg_def]])


section \<open>The headline theorem: 1-call-string activation collecting soundness\<close>

lemma sign_nest_cinit_le_cinit_sign_st:
  "cinit_stores sign_nest_gs
     \<subseteq> gamma_state_lift (map_lift (fun_of_resolved_st_q_for sign_nest_gs) (Lifted cinit_sign_st))"
  by (auto simp: cinit_stores_def gamma_state_def fun_of_resolved_st_q_for_def
                 fun_of_st_cinit_sign_st_for)

lemma sign_nest_1_entry_locals_ge_s0d:
  "map_lift (fun_of_resolved_st_q_for sign_nest_gs) (Lifted cinit_sign_st)
     \<le> locals (sigma_1 (Inl (cfg_entry sign_nest_cfg, [])))"
proof -
  have "map_lift (fun_of_resolved_st_q_for sign_nest_gs) (Lifted cinit_sign_st)
      \<le> locals (eq sign_nest_1_cs.Gen (cfg_entry sign_nest_cfg, []) sigma_1)"
    by (simp add: eq_side_cfg_T_eff_keyed_seed_dg)
       (rule order_trans[OF _ side_acc_dg_ge_acc], simp add: le_supI2)
  also have "\<dots> \<le> locals (sigma_1 (Inl (cfg_entry sign_nest_cfg, [])))"
    using sign_nest_1_cs.pp_eq_bound[OF entry_covered_1] by (simp add: less_eq_dg_state_def)
  finally show ?thesis .
qed

theorem sign_nest_1_activation_collect_sound:
  "activation_collect sign_nest_gs (cs_context 1) [] sign_nest_cfg
     (cinit_stores sign_nest_gs) v ctx
     \<subseteq> gamma_state_lift (sign_ctx_sg_1 (Inl (v, ctx)))"
proof (rule activation_collect_sound_gen[where sg = sign_ctx_sg_1 and gammaM = gamma_state_lift
        and enterc = "cs_context 1" and initial_ctx = "[]"
        and S = "cinit_stores sign_nest_gs" and g = sign_nest_cfg and gs = sign_nest_gs])
  \<comment> \<open>ENTRY_G\<close>
  fix s assume "s \<in> cinit_stores sign_nest_gs"
  hence "s \<in> gamma_state_lift (map_lift (fun_of_resolved_st_q_for sign_nest_gs) (Lifted cinit_sign_st))"
    using sign_nest_cinit_le_cinit_sign_st by blast
  also have "gamma_state_lift (map_lift (fun_of_resolved_st_q_for sign_nest_gs) (Lifted cinit_sign_st))
        = gamma_dg_base (map_lift (fun_of_resolved_st_q_for sign_nest_gs) (Lifted cinit_sign_st))
            (map_lift (fun_of_resolved_st_q_for sign_nest_gs) (Bot::sign exec_dg_st lifted))"
    by (simp add: gamma_dg_base_def)
  also have "\<dots> \<subseteq> gamma_dg_base (locals (sigma_1 (Inl (cfg_entry sign_nest_cfg, []))))
                   (globs (sigma_1 (Inr Global)))"
    by (rule gamma_dg_base_mono[OF sign_nest_1_entry_locals_ge_s0d
          sign_nest_1_cs.pp_entry_s0g_bound[unfolded sign_nest_cfg_compile, OF entry_covered_1]])
  also have "\<dots> = gamma_state_lift (sign_ctx_sg_1 (Inl (cfg_entry sign_nest_cfg, [])))"
    unfolding sign_ctx_sg_1_covered[OF entry_covered_1] gamma_dg_base_def by (rule refl)
  finally show "s \<in> gamma_state_lift (sign_ctx_sg_1 (Inl (cfg_entry sign_nest_cfg, [])))" .
next
  \<comment> \<open>EDGE --- discharged generically off the post-solution by \<open>dg_ctx_activation_base\<close>.\<close>
  show "\<And>u a v c s s'. (u, a, v) \<in> intra sign_nest_cfg
        \<Longrightarrow> s \<in> gamma_state_lift (sign_ctx_sg_1 (Inl (u, c))) \<Longrightarrow> s' \<in> edge_step a s
        \<Longrightarrow> s' \<in> gamma_state_lift (sign_ctx_sg_1 (Inl (v, c)))"
    by (rule sign_nest_1_cs.dg_ctx_act_edge[unfolded sign_nest_cfg_compile])
next
  \<comment> \<open>CALL --- enter routed to the truncated call string.\<close>
  fix u dst pars args p cont c s
  assume ce: "(u, CallEdge dst pars args, FunctionEntry p, cont) \<in> calls sign_nest_cfg"
    and sm: "s \<in> gamma_state_lift (sign_ctx_sg_1 (Inl (u, c)))"
  show "call_enter sign_nest_gs (CallEdge dst pars args) s
          \<in> gamma_state_lift (sign_ctx_sg_1 (Inl (FunctionEntry p, cs_context 1 u c (call_enter sign_nest_gs (CallEdge dst pars args) s))))"
    using sign_ctx_sg_1_seed[OF ce sm] .
next
  \<comment> \<open>COMB --- return combine at the caller's own truncated context.\<close>
  fix cl dst pars args p cont c1 s t es
  assume ce: "(cl, CallEdge dst pars args, FunctionEntry p, cont) \<in> calls sign_nest_cfg"
    and sm: "s \<in> gamma_state_lift (sign_ctx_sg_1 (Inl (cl, c1)))"
    and tm: "t \<in> gamma_state_lift (sign_ctx_sg_1 (Inl (FunctionResult p, cs_context 1 cl c1 es)))"
    and ces: "call_enter_store sign_nest_gs sign_nest_cfg cl s es"
  show "combine_collect sign_nest_gs dst s t \<in> gamma_state_lift (sign_ctx_sg_1 (Inl (cont, c1)))"
    using tm sign_ctx_sg_1_comb[OF ce sm _ ces] by blast
qed


section \<open>What the 1-call-string context actually computes\<close>

text \<open>\<open>f\<close>'s two activations stay separated at their own entry (\<open>SPos\<close> from \<open>f(3)\<close>, \<open>SNeg\<close>
  from \<open>f(-10)\<close>), since their call sites at \<open>main\<close> differ. \<open>g\<close>'s single call site inside
  \<open>f\<close> is identical for both activations, so the 1-call-string context collapses them to one
  unknown, and their join lands at \<open>STop\<close> --- the merge a 2-call-string keeps separated.\<close>

lemma sign_nest_1_f_entry_pos:
  "sign_nest_lookup (locals (snd sign_nest_1_sol (Inl (FunctionEntry (STR ''f''), [Statement 5]))))
     (STR ''p'') = SPos"
  unfolding sign_nest_1_sol_def sign_nest_1_eqs_def by eval

lemma sign_nest_1_f_entry_neg:
  "sign_nest_lookup (locals (snd sign_nest_1_sol (Inl (FunctionEntry (STR ''f''), [Statement 6]))))
     (STR ''p'') = SNeg"
  unfolding sign_nest_1_sol_def sign_nest_1_eqs_def by eval

lemma sign_nest_1_g_entry_merged:
  "sign_nest_lookup (locals (snd sign_nest_1_sol (Inl (FunctionEntry (STR ''g''), [Statement 2]))))
     (STR ''p'') = STop"
  unfolding sign_nest_1_sol_def sign_nest_1_eqs_def by eval

end

