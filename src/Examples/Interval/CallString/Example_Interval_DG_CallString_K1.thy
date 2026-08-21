theory Example_Interval_DG_CallString_K1
  imports
    "Voblint_Analysis.Interval_DG"
    "Voblint_Analysis.Ivl_Exec"
    "Voblint_Analysis.DG_Base_Exec"
    "Voblint_Analysis.Analysis_GraphViz"
    "Voblint_Core.Call_String_Routed_Context"
    "Voblint_Core.Activation_Backbone"
    "Voblint_Core.Solver_Menu"
    "Voblint_Formalization.Run_Analysis_Sound"
    "Voblint_CFG.CFG_Prune"
    "Voblint_VIMP.VIMP_Notation"
begin

section \<open>A computed 1-call-string context, routed by truncated call history\<close>

text \<open>
  A \<open>cs_route\<close>/\<open>cs_context\<close> instance at \<open>k = 1\<close>. Unlike the flat \<open>twice\<close> program used
  elsewhere, \<open>nest\<close> chains two procedures: \<open>main\<close> calls \<open>f\<close> from two distinct sites, and
  \<open>f\<close> calls \<open>g\<close> from one site inside its own body. \<open>g\<close>'s immediate call site is therefore
  identical for both activations, so a 1-call-string context cannot separate them --- only a
  longer call string, keying on which \<open>f\<close> call led there, can.

  Storage is Base-style: the local unknown carries the whole abstract state on the lifted
  carrier \<^typ>\<open>ivl exec_dg_st lifted\<close>, so a global is read and written exactly where a
  local is, and the solver-global carrier is inert --- every field of
  \<^const>\<open>base_dg_spec_st_for_lifted\<close> threads its incoming \<open>g\<close> through unchanged, so
  \<open>Inr Global\<close> is never read back to reconstruct program state. Only the routing policy
  (\<^const>\<open>cs_route\<close>, \<^const>\<open>cs_context\<close>) is call-string specific; the storage, the
  transfer primitives, and the CALL/COMB discharge are shared with the
  entry-state-keyed analysis.
\<close>

definition nest_program :: imp_prog where
  "nest_program = program {
     void g(p) { return p + p }
     void f(p) { t := g(p); return t }
     void main() { x := f(3); y := f(10) }
   }"

text \<open>The storage classifier: \<open>nest_program\<close> declares no globals, so \<open>nest_gs\<close>
  classifies every variable this chain touches as local.\<close>
abbreviation nest_gs :: "vname \<Rightarrow> bool" where
  "nest_gs \<equiv> declared_global nest_program"

text \<open>Reading one variable off a lifted whole-state local unknown: an unreachable point
  (\<^const>\<open>Bot\<close>) reads \<open>bot\<close> at every variable.\<close>
abbreviation nest_lookup :: "ivl exec_dg_st lifted \<Rightarrow> vname \<Rightarrow> ivl" where
  "nest_lookup d x \<equiv>
     (case d of Bot \<Rightarrow> bot | Lifted d0 \<Rightarrow> lookup_resolved_st_q d0 (location_of nest_gs x))"

definition nest_pi :: proc_table where "nest_pi = prog_table nest_program"
definition nest_procs :: "pname list" where "nest_procs = prog_procs nest_program"
definition nest_main :: "VIMP_Proc.com" where "nest_main = prog_main nest_program"

definition nest_cfg :: cfg where
  "nest_cfg = compile_prog nest_pi nest_procs (STR ''main'') nest_main"

text \<open>The compiled CFG, folded back under its own name: every obligation the routed
  locale states is phrased in \<^const>\<open>compile_prog\<close>, every fact below in \<open>nest_cfg\<close>.\<close>
lemma nest_cfg_compile [simp]:
  "compile_prog nest_pi nest_procs (STR ''main'') nest_main = nest_cfg"
  by (simp add: nest_cfg_def)

lemma nest_entry: "cfg_entry nest_cfg = FunctionEntry (STR ''main'')" by eval

text \<open>\<open>main\<close> calls \<open>f\<close> at two sites (\<open>Statement 5\<close>, args \<open>3\<close>; \<open>Statement 6\<close>, args \<open>10\<close>).
  \<open>f\<close> calls \<open>g\<close> at one site inside its own body (\<open>Statement 2\<close>), passing through its own
  parameter --- the same source location regardless of which \<open>f\<close> activation runs it.\<close>

lemma nest_finE: "finite (intra nest_cfg)"
  unfolding nest_cfg_def using compile_prog_finite by blast
lemma nest_finC: "finite (calls nest_cfg)"
  unfolding nest_cfg_def using compile_prog_finite by blast

text \<open>The three call edges' shape, computed directly from \<open>nest_cfg\<close>: each call site \<open>u\<close>
  pins down its callee \<open>p\<close> and continuation \<open>cont\<close>.\<close>
lemma nest_calls_shape:
  "\<forall>(u, ca, ce, cont) \<in> calls nest_cfg.
     case ca of CallEdge dst pars args \<Rightarrow>
       (case ce of FunctionEntry p \<Rightarrow>
          (u = Statement 2 \<and> p = (STR ''g'') \<and> cont = Statement 3) \<or>
          (u = Statement 5 \<and> p = (STR ''f'') \<and> cont = Statement 6) \<or>
          (u = Statement 6 \<and> p = (STR ''f'') \<and> cont = Statement 7)
        | _ \<Rightarrow> True)"
  unfolding nest_cfg_def by eval

subsection \<open>The Base-style interval specification, executable and abstract\<close>

text \<open>The executable bottom predicate the lifted carrier needs, at this program's own
  declared globals; \<open>nest_exact\<close> is the exactness fact every transport step below
  consumes.\<close>

definition nest_is_bot_pred :: "ivl resolved_st_q \<Rightarrow> bool" where
  "nest_is_bot_pred = resolved_st_q_is_bot_for (declared_global_vars nest_program)"

lemma nest_exact: "nest_is_bot_pred s = is_bot_state (fun_of_resolved_st_q_for nest_gs s)"
  unfolding nest_is_bot_pred_def by (rule resolved_st_q_is_bot_for_iff) simp

text \<open>The same Base-style pair the context-insensitive and entry-state-keyed interval
  analyses solve over, at the same \<^const>\<open>ivl_tf_st_for\<close>/\<^const>\<open>ivl_enter_st_for\<close>
  primitives: nothing call-string specific enters the specification.\<close>

definition nest_S_st :: "(ivl exec_dg_st lifted, ivl exec_dg_st lifted) dg_spec" where
  "nest_S_st = base_dg_spec_st_for_lifted nest_gs nest_is_bot_pred
                 (ivl_tf_st_for nest_gs) (ivl_enter_st_for nest_gs)"

definition nest_S_abs :: "(ivl abs_state lifted, ivl abs_state lifted) dg_spec" where
  "nest_S_abs = base_dg_spec_for_lifted nest_gs is_bot_state (ivl_tf_for nest_gs)"

subsection \<open>Executable-to-abstract transport, once for every bound\<close>

text \<open>The readback is the lifted \<^const>\<open>fun_of_resolved_st_q_for\<close>, used identically for the
  local and the (inert) global carrier. Every commute below is an instance of the generic
  Base-style engine; only Interval's own primitive facts are supplied.\<close>

lemma nest_dg_reader:
  "dg_reader_commute_gen (map_lift (fun_of_resolved_st_q_for nest_gs))
     (map_lift (fun_of_resolved_st_q_for nest_gs))"
  by unfold_locales (simp_all add: map_lift_sup fun_of_resolved_st_q_for_sup)

lemma nest_Hstep:
  "map_prod (map_lift (fun_of_resolved_st_q_for nest_gs)) (map_lift (fun_of_resolved_st_q_for nest_gs))
     (dg_spec_step nest_S_st a d g)
   = dg_spec_step nest_S_abs a (map_lift (fun_of_resolved_st_q_for nest_gs) d)
       (map_lift (fun_of_resolved_st_q_for nest_gs) g)"
  unfolding nest_S_st_def nest_S_abs_def
  by (rule base_dg_spec_st_for_lifted_dg_spec_step_commute
        [unfolded fun_of_exec_dg_st_for_def, OF ivl_tf_st_for_commute nest_exact])

lemma nest_Henter:
  "map_prod (map_lift (fun_of_resolved_st_q_for nest_gs)) (map_lift (fun_of_resolved_st_q_for nest_gs))
     (dgs_enter nest_S_st xs es d g)
   = dgs_enter nest_S_abs xs es (map_lift (fun_of_resolved_st_q_for nest_gs) d)
       (map_lift (fun_of_resolved_st_q_for nest_gs) g)"
  unfolding nest_S_st_def nest_S_abs_def
  by (rule base_dg_spec_st_for_lifted_dgs_enter_commute
        [unfolded fun_of_exec_dg_st_for_def, OF ivl_enter_st_for_commute nest_exact])

lemma nest_Hcomb:
  "map_prod (map_lift (fun_of_resolved_st_q_for nest_gs)) (map_lift (fun_of_resolved_st_q_for nest_gs))
     (dgs_combine nest_S_st dst dc de g)
   = dgs_combine nest_S_abs dst (map_lift (fun_of_resolved_st_q_for nest_gs) dc)
       (map_lift (fun_of_resolved_st_q_for nest_gs) de) (map_lift (fun_of_resolved_st_q_for nest_gs) g)"
  unfolding nest_S_st_def nest_S_abs_def
  by (rule base_dg_spec_st_for_lifted_dgs_combine_commute
        [where tf = "ivl_tf_for nest_gs", unfolded fun_of_exec_dg_st_for_def, OF nest_exact])

lemma nest_seed_ne_global: "Seed p ctx \<noteq> Global" by simp

text \<open>\<^const>\<open>cs_route\<close> never reads its data argument, so the routed combine and the routed
  entry-seed read transport for ``any'' bound \<open>k\<close> at once: \<open>cs_route_indep_of_data\<close> is the
  whole route-agreement obligation, with no per-domain commute lemma.\<close>

lemma nest_Hcmb_routed:
  "dg_reader_commute_gen.dg_tree_st_commute
     (map_lift (fun_of_resolved_st_q_for nest_gs)) (map_lift (fun_of_resolved_st_q_for nest_gs)) sigma_st
     (routed_cmb_g nest_S_st Global Seed (cs_route k) ctx ca cc ex)
     (routed_cmb_g nest_S_abs Global Seed (cs_route k) ctx ca cc ex)"
  by (rule dg_reader_commute_gen.dg_tree_st_commute_routed_cmb_g
        [OF nest_dg_reader nest_seed_ne_global nest_Henter nest_Hcomb cs_route_indep_of_data])

lemma nest_Hextra_routed:
  "list_all2 (dg_reader_commute_gen.dg_tree_st_commute
                (map_lift (fun_of_resolved_st_q_for nest_gs))
                (map_lift (fun_of_resolved_st_q_for nest_gs)) sigma_st)
     (routed_extra_g Seed Global route_st ctx w)
     (routed_extra_g Seed Global route_abs ctx w)"
  by (rule dg_reader_commute_gen.dg_tree_st_commute_routed_extra_g[OF nest_dg_reader])

text \<open>The whole post-solution transport, stated once for a free bound \<open>k\<close>: both the \<open>k = 1\<close>
  system here and its \<open>k = 2\<close> sibling instantiate this single lemma.\<close>

lemma nest_pp_abs_of_st:
  assumes pp: "part_post_solution
       (side_cfg_T_eff_keyed_seed_dg intra_predecessor_list (\<lambda>_. Global) (cs_route k)
          (routed_cmb_g nest_S_st Global Seed) (routed_extra_g Seed Global)
          nest_cfg nest_S_st Bot (Lifted cinit_ivl_st) Bot)
       x sigma_st vars"
  shows "part_post_solution
       (side_cfg_T_eff_keyed_seed_dg intra_predecessor_list (\<lambda>_. Global) (cs_route k)
          (routed_cmb_g nest_S_abs Global Seed) (routed_extra_g Seed Global)
          nest_cfg nest_S_abs
          (map_lift (fun_of_resolved_st_q_for nest_gs) (Bot::ivl exec_dg_st lifted))
          (map_lift (fun_of_resolved_st_q_for nest_gs) (Lifted cinit_ivl_st))
          (map_lift (fun_of_resolved_st_q_for nest_gs) (Bot::ivl exec_dg_st lifted)))
       x (fun_of_dg_st_gen (map_lift (fun_of_resolved_st_q_for nest_gs))
            (map_lift (fun_of_resolved_st_q_for nest_gs)) \<circ> sigma_st) vars"
  by (rule part_post_solution_seed_dg_st_to_abs_lifted_for
        [where gs = nest_gs and pred_sel = intra_predecessor_list and gkey = "\<lambda>_. Global"
           and route_st = "cs_route k" and route_abs = "cs_route k"
           and cmb_st = "routed_cmb_g nest_S_st Global Seed"
           and cmb_abs = "routed_cmb_g nest_S_abs Global Seed"
           and extra_st = "routed_extra_g Seed Global"
           and extra_abs = "routed_extra_g Seed Global"
           and g = nest_cfg and S_st = nest_S_st and S_abs = nest_S_abs,
         OF nest_Hstep cs_route_indep_of_data nest_Hcmb_routed nest_Hextra_routed pp])

text \<open>The abstract specification is sound for the Base-style concretization
  \<^const>\<open>gamma_dg_base\<close>, which discards its inert \<open>'G\<close> argument outright.\<close>

interpretation nest_dg_sound: sound_dg_spec nest_S_abs gamma_dg_base nest_gs
  unfolding nest_S_abs_def
  by (rule base_dg_spec_sound[OF ivl_is_sound_transfer_for is_bot_state_gamma_state_empty])

subsection \<open>The routed equation system and its computed solution\<close>

text \<open>The global-key type \<^type>\<open>call_string_gk\<close> and its truncation
  \<^const>\<open>cs_project_gk\<close> come from \<^theory>\<open>Voblint_Core.Call_String_Context\<close>: the key
  shape never depended on \<open>k\<close> or on this program.\<close>

definition nest_1_eqs ::
  "(pp \<times> cfg_node list, call_string_gk,
     (ivl exec_dg_st lifted, ivl exec_dg_st lifted) dg_state) eqsT" where
  "nest_1_eqs =
     side_cfg_T_eff_keyed_seed_dg intra_predecessor_list (\<lambda>_. Global) (cs_route 1)
      (routed_cmb_g nest_S_st Global Seed) (routed_extra_g Seed Global)
       nest_cfg nest_S_st Bot (Lifted cinit_ivl_st) Bot"

definition nest_1_sol ::
  "(pp \<times> cfg_node list) set
     \<times> (pp \<times> cfg_node list + call_string_gk
          \<Rightarrow> (ivl exec_dg_st lifted, ivl exec_dg_st lifted) dg_state)" where
  "nest_1_sol = TD_side_warrowing_apinis_Interp_solve nest_1_eqs
                    (cfg_exit nest_cfg, [])"

lemma nest_1_terminates:
  "TD_side_warrowing_apinis_Interp_solve_c nest_1_eqs (cfg_exit nest_cfg, [])
     \<noteq> None"
  by eval

subsection \<open>Coverage\<close>

text \<open>The full solved node set, computed once; every membership fact below is a
  \<open>simp\<close> lookup into this literal set instead of a separate \<open>eval\<close> re-derivation.\<close>

definition nest_1_nodes :: "(pp \<times> cfg_node list) set" where
  "nest_1_nodes = {
     (FunctionEntry (STR ''main''), []), (Statement 5, []), (Statement 6, []), (Statement 7, []),
     (FunctionEntry (STR ''f''), [Statement 5]), (Statement 2, [Statement 5]),
     (Statement 3, [Statement 5]), (FunctionResult (STR ''f''), [Statement 5]),
     (FunctionEntry (STR ''f''), [Statement 6]), (Statement 2, [Statement 6]),
     (Statement 3, [Statement 6]), (FunctionResult (STR ''f''), [Statement 6]),
     (FunctionEntry (STR ''g''), [Statement 2]), (Statement 0, [Statement 2]),
     (FunctionResult (STR ''g''), [Statement 2]), (FunctionResult (STR ''main''), [])}"

lemma nest_1_nodes_eq: "fst nest_1_sol = nest_1_nodes"
  unfolding nest_1_sol_def nest_1_eqs_def nest_1_nodes_def by eval

lemma entry_covered_1: "(cfg_entry nest_cfg, []) \<in> fst nest_1_sol"
  unfolding nest_entry nest_1_nodes_eq nest_1_nodes_def by simp

lemma nest_fwd_closed_all_1:
  "\<forall>(u, c)\<in>fst nest_1_sol. \<forall>(u', a, v)\<in>intra nest_cfg.
      u = u' \<longrightarrow> (v, c) \<in> fst nest_1_sol"
  unfolding nest_1_sol_def nest_1_eqs_def by eval

lemma nest_fwd_closed_1:
  assumes "(u, ctx) \<in> fst nest_1_sol" and "(u, a, v) \<in> intra nest_cfg"
  shows "(v, ctx) \<in> fst nest_1_sol"
  using nest_fwd_closed_all_1 assms by fastforce

text \<open>\<open>main\<close>'s two call sites are only ever reached at the root context: \<open>main\<close> is never
  itself called. \<open>f\<close>'s one call site (to \<open>g\<close>) is reached at either of \<open>f\<close>'s two activation
  contexts, never at the root --- \<open>g\<close> is only ever called from inside \<open>f\<close>.\<close>

lemma enter_callers_only_root_main_1:
  "\<forall>(p, ctx)\<in>fst nest_1_sol.
     (p = Statement 5 \<or> p = Statement 6) \<longrightarrow> ctx = []"
  unfolding nest_1_sol_def nest_1_eqs_def by eval

lemma enter_callers_g_1:
  "\<forall>(p, ctx)\<in>fst nest_1_sol.
     p = Statement 2 \<longrightarrow> ctx = [Statement 5] \<or> ctx = [Statement 6]"
  unfolding nest_1_sol_def nest_1_eqs_def by eval

lemma callee_covered_f3_1: "(FunctionEntry (STR ''f''), [Statement 5]) \<in> fst nest_1_sol"
  unfolding nest_1_nodes_eq nest_1_nodes_def by simp
lemma callee_covered_f10_1: "(FunctionEntry (STR ''f''), [Statement 6]) \<in> fst nest_1_sol"
  unfolding nest_1_nodes_eq nest_1_nodes_def by simp
lemma callee_covered_g_1: "(FunctionEntry (STR ''g''), [Statement 2]) \<in> fst nest_1_sol"
  unfolding nest_1_nodes_eq nest_1_nodes_def by simp

lemma covered_ret6_1: "(Statement 6, []) \<in> fst nest_1_sol"
  unfolding nest_1_nodes_eq nest_1_nodes_def by simp
lemma covered_ret7_1: "(Statement 7, []) \<in> fst nest_1_sol"
  unfolding nest_1_nodes_eq nest_1_nodes_def by simp
lemma covered_ret3_f3_1: "(Statement 3, [Statement 5]) \<in> fst nest_1_sol"
  unfolding nest_1_nodes_eq nest_1_nodes_def by simp
lemma covered_ret3_f10_1: "(Statement 3, [Statement 6]) \<in> fst nest_1_sol"
  unfolding nest_1_nodes_eq nest_1_nodes_def by simp


section \<open>Abstract transport of the routed solution\<close>

lemma nest_1_solve_dom:
  "TD_side_warrowing_apinis_Interp.solve_dom TYPE(call_string_gk)
     TYPE((ivl exec_dg_st lifted, ivl exec_dg_st lifted) dg_state)
     nest_1_eqs (cfg_exit nest_cfg, [])"
  using nest_1_terminates
  unfolding TD_side_warrowing_apinis_Interp.term_equivalence
            TD_side_warrowing_apinis_Interp.solve_c_dom_def
  by simp

lemma nest_1_pp_st:
  "part_post_solution nest_1_eqs (cfg_exit nest_cfg, [])
     (snd nest_1_sol) (fst nest_1_sol)"
  using TD_side_warrowing_apinis_Interp.partial_post_solution
          [OF nest_1_solve_dom, of "fst nest_1_sol" "snd nest_1_sol"]
  unfolding nest_1_sol_def by simp

abbreviation nest_1_sigma_abs ::
  "pp \<times> cfg_node list + call_string_gk
     \<Rightarrow> (ivl abs_state lifted, ivl abs_state lifted) dg_state" where
  "nest_1_sigma_abs \<equiv>
     fun_of_dg_st_gen (map_lift (fun_of_resolved_st_q_for nest_gs))
       (map_lift (fun_of_resolved_st_q_for nest_gs)) \<circ> snd nest_1_sol"

theorem nest_1_pp_abs:
  "part_post_solution
     (side_cfg_T_eff_keyed_seed_dg intra_predecessor_list (\<lambda>_. Global) (cs_route 1)
       (routed_cmb_g nest_S_abs Global Seed) (routed_extra_g Seed Global) nest_cfg nest_S_abs
        (map_lift (fun_of_resolved_st_q_for nest_gs) (Bot::ivl exec_dg_st lifted))
        (map_lift (fun_of_resolved_st_q_for nest_gs) (Lifted cinit_ivl_st))
        (map_lift (fun_of_resolved_st_q_for nest_gs) (Bot::ivl exec_dg_st lifted)))
     (cfg_exit nest_cfg, []) nest_1_sigma_abs (fst nest_1_sol)"
  by (rule nest_pp_abs_of_st[OF nest_1_pp_st[unfolded nest_1_eqs_def]])


section \<open>Activation-indexed collecting soundness for the 1-call-string-routed solution\<close>

definition nest_1_sg ::
  "pp \<times> cfg_node list + call_string_gk \<Rightarrow> ivl abs_state lifted" where
  "nest_1_sg z =
     (case z of
        Inl (v, ctx) \<Rightarrow>
          (if (v, ctx) \<in> fst nest_1_sol then locals (nest_1_sigma_abs (Inl (v, ctx))) else Bot)
      | Inr _ \<Rightarrow> Bot)"

lemma nest_1_sg_covered:
  "(v, ctx) \<in> fst nest_1_sol
     \<Longrightarrow> nest_1_sg (Inl (v, ctx)) = locals (nest_1_sigma_abs (Inl (v, ctx)))"
  by (simp add: nest_1_sg_def)

lemma nest_1_sg_uncovered_empty:
  "(v, ctx) \<notin> fst nest_1_sol \<Longrightarrow> gamma_state_lift (nest_1_sg (Inl (v, ctx))) = {}"
  by (simp add: nest_1_sg_def)

text \<open>The call-string routing policy instantiated at \<open>k = 1\<close>. The generic locale
  discharges everything that is a fact about \<^const>\<open>cs_route\<close>/\<^const>\<open>cs_context\<close> or about
  \<^const>\<open>compile_prog\<close> alone --- call-edge finiteness, seed-key distinctness, route/context
  agreement, and call-source uniqueness. What stays here is the two coverage obligations
  about this program's own solved system: \<open>g\<close>'s single call site is reached at either of
  \<open>f\<close>'s two activation contexts (\<open>enter_callers_g_1\<close>), but \<open>take 1\<close> erases that distinction
  before it reaches the goal, so \<open>call_fwd\<close> does not need to case-split on which one.\<close>

interpretation nest_1_cs: call_string_routed_context
    nest_S_abs nest_gs nest_pi nest_procs "STR ''main''" nest_main 1
    "map_lift (fun_of_resolved_st_q_for nest_gs) (Bot::ivl exec_dg_st lifted)"
    "map_lift (fun_of_resolved_st_q_for nest_gs) (Lifted cinit_ivl_st)"
    "map_lift (fun_of_resolved_st_q_for nest_gs) (Bot::ivl exec_dg_st lifted)"
    nest_1_sigma_abs "fst nest_1_sol" "(cfg_exit nest_cfg, [])" nest_1_sg
proof (unfold_locales, unfold nest_cfg_compile,
       goal_cases FinE PP SgCov SgUncov Fwd CallFwd CombFwd)
  case FinE
  show ?case by (rule nest_finE)
next
  case PP
  show ?case by (rule nest_1_pp_abs)
next
  case (SgCov v c)
  show ?case using SgCov by (simp add: nest_1_sg_covered gamma_dg_base_def)
next
  case (SgUncov v c)
  show ?case using SgUncov by (rule nest_1_sg_uncovered_empty)
next
  case (Fwd u a v c)
  show ?case using Fwd by (rule nest_fwd_closed_1)
next
  case (CallFwd u ctx dst pars args p cont)
  note covU = CallFwd(1) and ce = CallFwd(2)
  from ce nest_calls_shape have
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
    thus ?thesis using c2 callee_covered_f3_1 by (simp add: cs_route_def)
  next
    case c3
    have ctx0: "ctx = []" using covU c3 enter_callers_only_root_main_1 by fastforce
    thus ?thesis using c3 callee_covered_f10_1 by (simp add: cs_route_def)
  qed
next
  case (CombFwd cl c1 dst pars args p cont)
  show ?case
    using CombFwd enter_callers_only_root_main_1 enter_callers_g_1
          covered_ret3_f3_1 covered_ret3_f10_1 covered_ret6_1 covered_ret7_1
          nest_calls_shape
    by fastforce
qed

text \<open>CALL and COMB at this program, re-exported from the routed interpretation.\<close>

lemma nest_1_sg_seed:
  assumes "(u, CallEdge dst xs es, FunctionEntry p, cont) \<in> calls nest_cfg"
    and "s \<in> gamma_state_lift (nest_1_sg (Inl (u, ctx)))"
  shows "call_enter nest_gs (CallEdge dst xs es) s
           \<in> gamma_state_lift (nest_1_sg (Inl (FunctionEntry p,
                 cs_context 1 u ctx (call_enter nest_gs (CallEdge dst xs es) s))))"
  by (rule nest_1_cs.routed_context_call[OF assms[unfolded nest_cfg_def]])

lemma nest_1_sg_comb:
  assumes "(cl, CallEdge dst pars args, FunctionEntry p, v) \<in> calls nest_cfg"
    and "s \<in> gamma_state_lift (nest_1_sg (Inl (cl, c1)))"
    and "t \<in> gamma_state_lift (nest_1_sg (Inl (FunctionResult p, cs_context 1 cl c1 es)))"
    and "call_enter_store nest_gs nest_cfg cl s es"
  shows "combine_collect nest_gs dst s t \<in> gamma_state_lift (nest_1_sg (Inl (v, c1)))"
  by (rule nest_1_cs.routed_context_comb[OF assms[unfolded nest_cfg_def]])


section \<open>The headline theorem: 1-call-string activation collecting soundness\<close>

lemma nest_cinit_le_cinit_ivl_st:
  "cinit_stores nest_gs
     \<subseteq> gamma_state_lift (map_lift (fun_of_resolved_st_q_for nest_gs) (Lifted cinit_ivl_st))"
  by (auto simp: cinit_stores_def gamma_state_def fun_of_resolved_st_q_for_def
                 fun_of_st_cinit_ivl_st_for)

lemma nest_1_entry_locals_ge_s0d:
  "map_lift (fun_of_resolved_st_q_for nest_gs) (Lifted cinit_ivl_st)
     \<le> locals (nest_1_sigma_abs (Inl (cfg_entry nest_cfg, [])))"
proof -
  have "map_lift (fun_of_resolved_st_q_for nest_gs) (Lifted cinit_ivl_st)
      \<le> locals (eq nest_1_cs.Gen (cfg_entry nest_cfg, []) nest_1_sigma_abs)"
    by (simp add: eq_side_cfg_T_eff_keyed_seed_dg)
       (rule order_trans[OF _ side_acc_dg_ge_acc], simp add: le_supI2)
  also have "\<dots> \<le> locals (nest_1_sigma_abs (Inl (cfg_entry nest_cfg, [])))"
    using nest_1_cs.pp_eq_bound[OF entry_covered_1] by (simp add: less_eq_dg_state_def)
  finally show ?thesis .
qed

theorem nest_1_activation_collect_sound:
  "activation_collect nest_gs (admiss_exact (cs_context 1)) [] nest_cfg (cinit_stores nest_gs) v ctx
     \<subseteq> gamma_state_lift (nest_1_sg (Inl (v, ctx)))"
proof (rule activation_collect_sound_gen[where sg = nest_1_sg and gammaM = gamma_state_lift
        and admiss = "admiss_exact (cs_context 1)" and startcontext = "[]"
        and S = "cinit_stores nest_gs" and g = nest_cfg and gs = nest_gs])
  \<comment> \<open>ENTRY_G\<close>
  fix s assume "s \<in> cinit_stores nest_gs"
  hence "s \<in> gamma_state_lift (map_lift (fun_of_resolved_st_q_for nest_gs) (Lifted cinit_ivl_st))"
    using nest_cinit_le_cinit_ivl_st by blast
  also have "gamma_state_lift (map_lift (fun_of_resolved_st_q_for nest_gs) (Lifted cinit_ivl_st))
        = gamma_dg_base (map_lift (fun_of_resolved_st_q_for nest_gs) (Lifted cinit_ivl_st))
            (map_lift (fun_of_resolved_st_q_for nest_gs) (Bot::ivl exec_dg_st lifted))"
    by (simp add: gamma_dg_base_def)
  also have "\<dots> \<subseteq> gamma_dg_base (locals (nest_1_sigma_abs (Inl (cfg_entry nest_cfg, []))))
                   (globs (nest_1_sigma_abs (Inr Global)))"
    by (rule gamma_dg_base_mono[OF nest_1_entry_locals_ge_s0d
          nest_1_cs.pp_entry_s0g_bound[unfolded nest_cfg_compile, OF entry_covered_1]])
  also have "\<dots> = gamma_state_lift (nest_1_sg (Inl (cfg_entry nest_cfg, [])))"
    unfolding nest_1_sg_covered[OF entry_covered_1] gamma_dg_base_def by (rule refl)
  finally show "s \<in> gamma_state_lift (nest_1_sg (Inl (cfg_entry nest_cfg, [])))" .
next
  \<comment> \<open>EDGE --- discharged generically off the post-solution by \<open>dg_ctx_activation_base\<close>.\<close>
  show "\<And>u a v c s s'. (u, a, v) \<in> intra nest_cfg
        \<Longrightarrow> s \<in> gamma_state_lift (nest_1_sg (Inl (u, c))) \<Longrightarrow> s' \<in> edge_step a s
        \<Longrightarrow> s' \<in> gamma_state_lift (nest_1_sg (Inl (v, c)))"
    by (rule nest_1_cs.dg_ctx_act_edge[unfolded nest_cfg_compile])
next
  \<comment> \<open>ADMISS_TOTAL --- trivial, \<open>cs_context 1\<close> is a total function.\<close>
  show "\<And>u c s. \<exists>c'. admiss_exact (cs_context 1) u c s c'" by (simp add: admiss_exact_def)
next
  \<comment> \<open>CALL --- enter routed to the truncated call string.\<close>
  fix u dst pars args p cont c s c'
  assume ce: "(u, CallEdge dst pars args, FunctionEntry p, cont) \<in> calls nest_cfg"
    and sm: "s \<in> gamma_state_lift (nest_1_sg (Inl (u, c)))"
    and adm: "admiss_exact (cs_context 1) u c (call_enter nest_gs (CallEdge dst pars args) s) c'"
  show "call_enter nest_gs (CallEdge dst pars args) s
          \<in> gamma_state_lift (nest_1_sg (Inl (FunctionEntry p, c')))"
    using adm nest_1_sg_seed[OF ce sm] by (simp add: admiss_exact_def)
next
  \<comment> \<open>COMB --- return combine at the caller's own truncated context.\<close>
  fix cl dst pars args p cont c1 c2 s t es
  assume ce: "(cl, CallEdge dst pars args, FunctionEntry p, cont) \<in> calls nest_cfg"
    and sm: "s \<in> gamma_state_lift (nest_1_sg (Inl (cl, c1)))"
    and adm: "admiss_exact (cs_context 1) cl c1 es c2"
    and tm: "t \<in> gamma_state_lift (nest_1_sg (Inl (FunctionResult p, c2)))"
    and ces: "call_enter_store nest_gs nest_cfg cl s es"
  show "combine_collect nest_gs dst s t \<in> gamma_state_lift (nest_1_sg (Inl (cont, c1)))"
    using adm tm nest_1_sg_comb[OF ce sm _ ces] by (simp add: admiss_exact_def)
qed


section \<open>What the 1-call-string context actually computes\<close>

text \<open>\<open>f\<close>'s two activations are kept apart by their own call sites, so the formal \<open>p\<close> binds
  exactly in each. \<open>g\<close>'s single call site collapses both into one context, so \<open>g\<close>'s entry
  unknown is updated twice from below --- once per \<open>f\<close> activation --- and the solver's
  widening turns that second update into an unbounded upper edge rather than the plain
  join \<open>[3,10]\<close>. The widened callee result then flows back into both \<open>f\<close> activations and
  therefore into both \<open>x\<close> and \<open>y\<close>.\<close>

lemma nest_1_f_entry_first:
  "nest_lookup (locals (snd nest_1_sol (Inl (FunctionEntry (STR ''f''), [Statement 5])))) (STR ''p'')
     = Ivl (Fin 3) (Fin 3)"
  unfolding nest_1_sol_def nest_1_eqs_def by eval

lemma nest_1_f_entry_second:
  "nest_lookup (locals (snd nest_1_sol (Inl (FunctionEntry (STR ''f''), [Statement 6])))) (STR ''p'')
     = Ivl (Fin 10) (Fin 10)"
  unfolding nest_1_sol_def nest_1_eqs_def by eval

lemma nest_1_g_entry_merged:
  "nest_lookup (locals (snd nest_1_sol (Inl (FunctionEntry (STR ''g''), [Statement 2])))) (STR ''p'')
     = Ivl (Fin 3) PlusInf"
  unfolding nest_1_sol_def nest_1_eqs_def by eval

lemma nest_1_g_result_merged:
  "nest_lookup (locals (snd nest_1_sol (Inl (FunctionResult (STR ''g''), [Statement 2])))) (STR ''#ret'')
     = Ivl (Fin 6) PlusInf"
  unfolding nest_1_sol_def nest_1_eqs_def by eval

lemma nest_1_t_after_inner_return:
  "nest_lookup (locals (snd nest_1_sol (Inl (Statement 3, [Statement 5])))) (STR ''t'')
     = Ivl (Fin 6) PlusInf"
  unfolding nest_1_sol_def nest_1_eqs_def by eval

lemma nest_1_x_after_first_return:
  "nest_lookup (locals (snd nest_1_sol (Inl (Statement 6, [])))) (STR ''x'') = Ivl (Fin 6) PlusInf"
  unfolding nest_1_sol_def nest_1_eqs_def by eval

lemma nest_1_y_after_second_return:
  "nest_lookup (locals (snd nest_1_sol (Inl (Statement 7, [])))) (STR ''y'') = Ivl (Fin 6) PlusInf"
  unfolding nest_1_sol_def nest_1_eqs_def by eval


text \<open>Each call publishes the entered store into its own context's seed slot, on the
  \<^const>\<open>locals\<close> half the callee entry reads it back from.\<close>

lemma nest_1_seed_f_first:
  "nest_lookup (locals (snd nest_1_sol (Inr (Seed (FunctionEntry (STR ''f'')) [Statement 5])))) (STR ''p'')
     = Ivl (Fin 3) (Fin 3)"
  unfolding nest_1_sol_def nest_1_eqs_def by eval

lemma nest_1_seed_f_second:
  "nest_lookup (locals (snd nest_1_sol (Inr (Seed (FunctionEntry (STR ''f'')) [Statement 6])))) (STR ''p'')
     = Ivl (Fin 10) (Fin 10)"
  unfolding nest_1_sol_def nest_1_eqs_def by eval


section \<open>Globals across a call-string-routed call\<close>

text \<open>
  The whole-state carrier makes a declared global cross a call boundary in the same slot a
  local does. \<open>bump\<close> reads the global \<open>g\<close> its caller wrote before the call, writes it, and
  returns it; \<open>main\<close> then observes both the returned value and the callee's update. The
  three call sites are syntactically distinct, so a 1-call-string already separates all
  three activations, and the third one --- whose actual argument is the global \<open>g\<close> itself
  --- locks in that a call argument is evaluated against the caller's real state, not a
  globals-bottomed one.
\<close>

definition nestg_program :: imp_prog where
  "nestg_program = program {
     global g;
     void bump(n) {
       g := g + n;
       return g
     }
     void main() {
       g := 10;
       a := bump(5);
       b := bump(4);
       __voblint_check(a == 15);
       __voblint_check(b == 19);
       __voblint_check(g == 19);
       c := bump(g);
       __voblint_check(c == 38);
       __voblint_check(g == 38)
     }
   }"

abbreviation nestg_gs :: "vname \<Rightarrow> bool" where "nestg_gs \<equiv> declared_global nestg_program"

abbreviation nestg_lookup :: "ivl exec_dg_st lifted \<Rightarrow> vname \<Rightarrow> ivl" where
  "nestg_lookup d x \<equiv>
     (case d of Bot \<Rightarrow> bot | Lifted d0 \<Rightarrow> lookup_resolved_st_q d0 (location_of nestg_gs x))"

definition nestg_cfg :: cfg where
  "nestg_cfg = compile_prog (prog_table nestg_program) (prog_procs nestg_program)
                 (STR ''main'') (prog_main nestg_program)"

definition nestg_is_bot_pred :: "ivl resolved_st_q \<Rightarrow> bool" where
  "nestg_is_bot_pred = resolved_st_q_is_bot_for (declared_global_vars nestg_program)"

definition nestg_1_eqs ::
  "(pp \<times> cfg_node list, call_string_gk,
     (ivl exec_dg_st lifted, ivl exec_dg_st lifted) dg_state) eqsT" where
  "nestg_1_eqs =
     side_cfg_T_eff_keyed_seed_dg intra_predecessor_list (\<lambda>_. Global) (cs_route 1)
      (routed_cmb_g (base_dg_spec_st_for_lifted nestg_gs nestg_is_bot_pred
                       (ivl_tf_st_for nestg_gs) (ivl_enter_st_for nestg_gs)) Global Seed)
      (routed_extra_g Seed Global)
       nestg_cfg
       (base_dg_spec_st_for_lifted nestg_gs nestg_is_bot_pred
          (ivl_tf_st_for nestg_gs) (ivl_enter_st_for nestg_gs))
       Bot (Lifted cinit_ivl_st) Bot"

definition nestg_1_sol ::
  "(pp \<times> cfg_node list) set
     \<times> (pp \<times> cfg_node list + call_string_gk
          \<Rightarrow> (ivl exec_dg_st lifted, ivl exec_dg_st lifted) dg_state)" where
  "nestg_1_sol = TD_side_warrowing_apinis_Interp_solve nestg_1_eqs (cfg_exit nestg_cfg, [])"

lemma nestg_1_terminates:
  "TD_side_warrowing_apinis_Interp_solve_c nestg_1_eqs (cfg_exit nestg_cfg, []) \<noteq> None"
  by eval

text \<open>Three call sites, three 1-call-strings: the activations never share a solver unknown.\<close>

lemma nestg_1_call_contexts:
  "(FunctionEntry (STR ''bump''), [Statement 4]) \<in> fst nestg_1_sol \<and>
   (FunctionEntry (STR ''bump''), [Statement 5]) \<in> fst nestg_1_sol \<and>
   (FunctionEntry (STR ''bump''), [Statement 9]) \<in> fst nestg_1_sol \<and>
   (FunctionEntry (STR ''bump''), []) \<notin> fst nestg_1_sol"
  unfolding nestg_1_sol_def nestg_1_eqs_def by eval

text \<open>Callee entry, first activation: the formal \<open>n\<close> binds to the argument, and the global
  \<open>g\<close> arrives at the value \<open>main\<close> wrote before the call.\<close>
lemma nestg_1_entry_first:
  "(nestg_lookup (locals (snd nestg_1_sol (Inl (FunctionEntry (STR ''bump''), [Statement 4])))) (STR ''g''),
    nestg_lookup (locals (snd nestg_1_sol (Inl (FunctionEntry (STR ''bump''), [Statement 4])))) (STR ''n''))
     = (Ivl (Fin 10) (Fin 10), Ivl (Fin 5) (Fin 5))"
  unfolding nestg_1_sol_def nestg_1_eqs_def by eval

text \<open>Callee entry, second activation: \<open>g\<close> is the value the first activation wrote and
  returned through, so a callee global write survives the return into the next call.\<close>
lemma nestg_1_entry_second:
  "(nestg_lookup (locals (snd nestg_1_sol (Inl (FunctionEntry (STR ''bump''), [Statement 5])))) (STR ''g''),
    nestg_lookup (locals (snd nestg_1_sol (Inl (FunctionEntry (STR ''bump''), [Statement 5])))) (STR ''n''))
     = (Ivl (Fin 15) (Fin 15), Ivl (Fin 4) (Fin 4))"
  unfolding nestg_1_sol_def nestg_1_eqs_def by eval

text \<open>Callee entry, third activation: the global-valued argument is evaluated against the
  caller's real state before entry, so the entered \<open>n\<close> carries the caller's live value.\<close>
lemma nestg_1_entry_third:
  "(nestg_lookup (locals (snd nestg_1_sol (Inl (FunctionEntry (STR ''bump''), [Statement 9])))) (STR ''g''),
    nestg_lookup (locals (snd nestg_1_sol (Inl (FunctionEntry (STR ''bump''), [Statement 9])))) (STR ''n''))
     = (Ivl (Fin 19) (Fin 19), Ivl (Fin 19) (Fin 19))"
  unfolding nestg_1_sol_def nestg_1_eqs_def by eval

text \<open>Caller state after each return: the callee's global write is visible, the caller's
  own locals are preserved, and the return destination holds the callee's returned value.\<close>
lemma nestg_1_after_first_return:
  "(nestg_lookup (locals (snd nestg_1_sol (Inl (Statement 5, [])))) (STR ''g''),
    nestg_lookup (locals (snd nestg_1_sol (Inl (Statement 5, [])))) (STR ''a''))
     = (Ivl (Fin 15) (Fin 15), Ivl (Fin 15) (Fin 15))"
  unfolding nestg_1_sol_def nestg_1_eqs_def by eval

lemma nestg_1_after_second_return:
  "(nestg_lookup (locals (snd nestg_1_sol (Inl (Statement 8, [])))) (STR ''g''),
    nestg_lookup (locals (snd nestg_1_sol (Inl (Statement 8, [])))) (STR ''a''),
    nestg_lookup (locals (snd nestg_1_sol (Inl (Statement 8, [])))) (STR ''b''))
     = (Ivl (Fin 19) (Fin 19), Ivl (Fin 15) (Fin 15), Ivl (Fin 19) (Fin 19))"
  unfolding nestg_1_sol_def nestg_1_eqs_def by eval

lemma nestg_1_after_third_return:
  "(nestg_lookup (locals (snd nestg_1_sol (Inl (Statement 10, [])))) (STR ''g''),
    nestg_lookup (locals (snd nestg_1_sol (Inl (Statement 10, [])))) (STR ''c''))
     = (Ivl (Fin 38) (Fin 38), Ivl (Fin 38) (Fin 38))"
  unfolding nestg_1_sol_def nestg_1_eqs_def by eval



section \<open>Call-string-context-expanded analysis graph\<close>

definition nest_1_graph_config ::
  "(cfg_node list, call_string_gk,
     (ivl exec_dg_st lifted, ivl exec_dg_st lifted) dg_state, ivl exec_dg_st lifted)
     analysis_graph_config" where
  "nest_1_graph_config =
    \<lparr> local_of = locals,
      route = (\<lambda>u ctx action d. Some (cs_route 1 u ctx d action)),
      context_key = String.implode o
        (\<lambda>ctx. ''['' @ join_source '', '' (map string_of_cfg_node ctx) @ '']''),
      show_context = (\<lambda>ctx. ''['' @ join_source '', '' (map string_of_cfg_node ctx) @ '']''),
      locals_for_pp = (\<lambda>p.
        let sc = compiled_procedure_scope nest_gs nest_pi nest_procs (STR ''main'') nest_main
          nest_cfg p
        in scope_formals sc @ scope_locals sc),
      return_slot_for_pp = (\<lambda>p.
        scope_return_slot (compiled_procedure_scope nest_gs nest_pi nest_procs (STR ''main'') nest_main
          nest_cfg p)),
      globals_to_show = [],
      show_local = (\<lambda>p ctx vars d. map (\<lambda>x.
        String.explode x @ ''='' @ string_of_ivl (nest_lookup d x)) vars),
      format_return = (\<lambda>p ctx ret d.
        if nest_lookup d ret = ivl_top then []
        else [''ret='' @ string_of_ivl (nest_lookup d ret)]),
      show_global = (\<lambda>k vars s. [''(none)'']),
      show_global_key = (\<lambda>k. case k of Global \<Rightarrow> ''Global'' | Seed p ctx \<Rightarrow> ''Seed''),
      is_shared_global = (\<lambda>k. case k of Global \<Rightarrow> True | Seed _ _ \<Rightarrow> False),
      show_internal_globals = False,
      owner_of = String.explode o compiled_owner_of nest_pi nest_procs (STR ''main'') nest_main,
      cluster_label = (\<lambda>owner ctx.
        if owner = ''main'' \<and> ctx = [] then ''main / root context''
        else owner @ '' / call string='' @ ''['' @ join_source '', '' (map string_of_cfg_node ctx) @ '']''),
      source_text = Some (pretty_string_of_program nest_pi nest_procs nest_main []),
      node_annotation = (\<lambda>_ _. None)
    \<rparr>"

definition nest_1_contexts_for_pp :: "pp \<Rightarrow> cfg_node list list" where
  "nest_1_contexts_for_pp p =
    (let owner = compiled_owner_of nest_pi nest_procs (STR ''main'') nest_main p
     in if owner = (STR ''main'') then [[]]
        else if owner = (STR ''f'') then [[Statement 5], [Statement 6]]
        else [[Statement 2]])"

definition nest_1_local_graph_domain :: "(pp \<times> cfg_node list + call_string_gk) list" where
  "nest_1_local_graph_domain =
    contextual_graph_domain nest_cfg nest_1_contexts_for_pp"

definition nest_1_seed_keys :: "call_string_gk list" where
  "nest_1_seed_keys =
     map (\<lambda>ctx. Seed (FunctionEntry (STR ''f'')) ctx) [[Statement 5], [Statement 6]]
     @ [Seed (FunctionEntry (STR ''g'')) [Statement 2]]"

definition nest_1_graph_domain :: "(pp \<times> cfg_node list + call_string_gk) list" where
  "nest_1_graph_domain =
    nest_1_local_graph_domain @ map Inr nest_1_seed_keys"

definition nest_1_graph :: "(cfg_node list, call_string_gk) analysis_graph" where
  "nest_1_graph =
    build_analysis_graph nest_1_graph_config nest_cfg nest_1_graph_domain
      (snd nest_1_sol)"

definition nest_1_dot :: String.literal where
  "nest_1_dot =
    String.implode
      (analysis_graph_to_dot nest_1_graph_config nest_cfg (snd nest_1_sol)
        nest_1_graph)"

lemma nest_1_graph_wf: "analysis_graph_wf nest_1_graph" by eval

lemma nest_1_graph_domain_is_covered:
  "list_all (\<lambda>x. case x of Inl pc \<Rightarrow> pc \<in> fst nest_1_sol | Inr _ \<Rightarrow> True)
    nest_1_graph_domain" by eval

lemma nest_1_dot_nonempty: "String.explode nest_1_dot \<noteq> []" by eval


end


