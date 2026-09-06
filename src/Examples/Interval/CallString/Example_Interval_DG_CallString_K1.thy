theory Example_Interval_DG_CallString_K1
  imports
    "Voblint_Analysis.Interval_Transfer"
    "Voblint_Analysis.Ivl_Exec"
    "Voblint_Exec.DG_Local_State_Exec"
    "Voblint_Analysis.Analysis_GraphViz"
    "Voblint_Analysis.Call_String_Routed_Context"
    "Voblint_Framework.Activation_Backbone"
    "Voblint_Solver.TD_Solver_Bridge"
    "Voblint_Soundness.Run_Analysis_Sound"
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
  \<^const>\<open>local_state_dg_spec_st_for_lifted\<close> threads its incoming \<open>g\<close> through unchanged, so
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
  "nest_cfg = compile_prog nest_pi nest_procs"

text \<open>The compiled CFG, folded back under its own name: every obligation the routed
  locale states is phrased in \<^const>\<open>compile_prog\<close>, every fact below in \<open>nest_cfg\<close>.\<close>
lemma nest_cfg_compile [simp]:
  "compile_prog nest_pi nest_procs = nest_cfg"
  by (simp add: nest_cfg_def)

interpretation nest: compiled_cfg nest_pi nest_procs nest_cfg
proof unfold_locales
  show "finite (intra nest_cfg)"
    unfolding nest_cfg_def using compile_prog_finite by blast
  show "finite (calls nest_cfg)"
    unfolding nest_cfg_def using compile_prog_finite by blast
  show "nest_cfg = compile_prog nest_pi nest_procs"
    by (rule nest_cfg_def)
qed

lemmas nest_entry = nest.entry[unfolded prog_main_name_def]

text \<open>\<open>main\<close> calls \<open>f\<close> at two sites (\<open>Statement 5\<close>, args \<open>3\<close>; \<open>Statement 6\<close>, args \<open>10\<close>).
  \<open>f\<close> calls \<open>g\<close> at one site inside its own body (\<open>Statement 2\<close>), passing through its own
  parameter --- the same source location regardless of which \<open>f\<close> activation runs it.\<close>

lemmas nest_finE = nest.finite_intra

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

definition nest_empty_pred :: "ivl resolved_st_q \<Rightarrow> bool" where
  "nest_empty_pred = resolved_st_q_is_bot_for (declared_global_vars nest_program)"

lemma nest_exact: "nest_empty_pred s = is_empty_state (fun_of_resolved_st_q_for nest_gs s)"
  unfolding nest_empty_pred_def by (rule resolved_st_q_is_bot_for_iff) simp

text \<open>The same Base-style pair the context-insensitive and entry-state-keyed interval
  analyses solve over, at the same \<^const>\<open>ivl_tf_st_for\<close>/\<^const>\<open>ivl_enter_st_for\<close>
  primitives: nothing call-string specific enters the specification.\<close>

definition nest_S_st ::
  "(pp \<times> cfg_node list, call_string_gk,
     unit, ivl exec_dg_st lifted, ivl exec_dg_st lifted) dg_spec" where
  "nest_S_st = local_state_dg_spec_st_for_lifted nest_gs nest_empty_pred
                 (ivl_tf_st_for nest_gs) (ivl_enter_st_for nest_gs)"

subsection \<open>Soundness of the executable specification, once for every bound\<close>

text \<open>The executable spec is sound for the concretization that reads a local unknown back
  through \<^const>\<open>fun_of_resolved_st_q_for\<close> and ignores the inert global slot; Interval's
  own primitive commute facts are all the generic engine needs.\<close>

definition nest_gamma :: "ivl exec_dg_st lifted \<Rightarrow> ivl exec_dg_st lifted \<Rightarrow> store set" where
  "nest_gamma d g = gamma_state_lift (map_lift (fun_of_resolved_st_q_for nest_gs) d)"

interpretation nest_domain: routed_dg_domain_exec
  nest_gs nest_empty_pred "ivl_tf_st_for nest_gs" "ivl_enter_st_for nest_gs"
  skip_ivl assign_ivl special_ivl branch_ivl body_ivl return_ivl
  "enter_ivl_ci_for nest_gs" event_ivl
  by unfold_locales
     (rule ivl_tf_st_for_commute[unfolded ivl_tf_abs_def], assumption,
      rule ivl_enter_st_for_commute, rule nest_exact)


lemma nest_gamma_eq: "nest_gamma = nest_domain.gamma_exec"
  by (intro ext) (simp add: nest_gamma_def nest_domain.gamma_exec_def gamma_dg_local_state_def)

interpretation nest_dg_sound: sound_dg_spec_core nest_S_st nest_gamma nest_gs
  unfolding nest_gamma_eq nest_S_st_def
  by (rule nest_domain.sound_dg_spec_core_st[OF ivl_is_sound_transfer_for])

subsection \<open>The routed equation system and its computed solution\<close>

text \<open>The global-key type \<^type>\<open>call_string_gk\<close> comes from
  \<^theory>\<open>Voblint_Framework.Call_String_Context\<close>: the key shape never depended
  on \<open>k\<close> or on this program.\<close>

definition nest_1_eqs ::
  "(pp \<times> cfg_node list, call_string_gk,
     (ivl exec_dg_st lifted, ivl exec_dg_st lifted) dg_state) eqsT" where
  "nest_1_eqs =
     routed_node_rhs intra_predecessor_addr_list (\<lambda>_. Global) (cs_route 1)
      (\<lambda>ctx' src a. dg_spec_edge_tree nest_S_st a src (\<lambda>_. Global))
      (routed_call_tree nest_S_st Global Seed (static_resolve nest_cfg) (\<lambda>d. d = Bot))
      (routed_entry_seed_tree Seed)
       nest_cfg Bot (Lifted cinit_ivl_st) Bot"

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
  unfolding nest_1_nodes_eq nest_1_nodes_def by simp

lemma enter_callers_g_1:
  "\<forall>(p, ctx)\<in>fst nest_1_sol.
     p = Statement 2 \<longrightarrow> ctx = [Statement 5] \<or> ctx = [Statement 6]"
  unfolding nest_1_nodes_eq nest_1_nodes_def by simp

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


section \<open>The solver's post-solution\<close>

lemma nest_1_solve_dom:
  "TD_side_warrowing_apinis_Interp.solve_dom TYPE(call_string_gk)
     TYPE((ivl exec_dg_st lifted, ivl exec_dg_st lifted) dg_state)
     nest_1_eqs (cfg_exit nest_cfg, [])"
  by (rule TD_side_warrowing_apinis_Interp.solve_dom_of_solve_c[OF nest_1_terminates])

lemma nest_1_pp_st:
  "part_post_solution nest_1_eqs (cfg_exit nest_cfg, [])
     (snd nest_1_sol) (fst nest_1_sol)"
  using TD_side_warrowing_apinis_Interp.partial_post_solution
          [OF nest_1_solve_dom, of "fst nest_1_sol" "snd nest_1_sol"]
  unfolding nest_1_sol_def by simp

text \<open>The solver's own table is the solved system the routed spine is interpreted at;
  nothing is transported to another carrier.\<close>

section \<open>Activation-indexed collecting soundness for the 1-call-string-routed solution\<close>

definition nest_1_sg ::
  "pp \<times> cfg_node list + call_string_gk \<Rightarrow> ivl exec_dg_st lifted" where
  "nest_1_sg z =
     (case z of
        Inl (v, ctx) \<Rightarrow>
          (if (v, ctx) \<in> fst nest_1_sol then locals (snd nest_1_sol (Inl (v, ctx))) else Bot)
      | Inr _ \<Rightarrow> Bot)"

lemma nest_1_sg_covered:
  "(v, ctx) \<in> fst nest_1_sol
     \<Longrightarrow> nest_1_sg (Inl (v, ctx)) = locals (snd nest_1_sol (Inl (v, ctx)))"
  by (simp add: nest_1_sg_def)

lemma nest_1_sg_uncovered_empty:
  "(v, ctx) \<notin> fst nest_1_sol
     \<Longrightarrow> gamma_state_lift (map_lift (fun_of_resolved_st_q_for nest_gs) (nest_1_sg (Inl (v, ctx)))) = {}"
  by (simp add: nest_1_sg_def)

text \<open>The call-string routing policy instantiated at \<open>k = 1\<close>. The generic locale
  discharges everything that is a fact about \<^const>\<open>cs_route\<close>/\<^const>\<open>cs_context\<close> or about
  \<^const>\<open>compile_prog\<close> alone --- call-edge finiteness, seed-key distinctness, route/context
  agreement, and call-source uniqueness. What stays here is the two coverage obligations
  about this program's own solved system: \<open>g\<close>'s single call site is reached at either of
  \<open>f\<close>'s two activation contexts (\<open>enter_callers_g_1\<close>), but \<open>take 1\<close> erases that distinction
  before it reaches the goal, so \<open>call_fwd\<close> does not need to case-split on which one.\<close>

interpretation nest_1_cs: call_string_routed_context
    nest_S_st nest_gamma nest_gs nest_pi nest_procs 1 Bot "Lifted cinit_ivl_st" Bot
    "snd nest_1_sol" "fst nest_1_sol" "(cfg_exit nest_cfg, [])" nest_1_sg
    "\<lambda>d. d = Bot"
    "\<lambda>m. gamma_state_lift (map_lift (fun_of_resolved_st_q_for nest_gs) m)"
proof (unfold_locales, unfold nest_cfg_compile,
       goal_cases FinE PP SgCov SgUncov Fwd IsBotBot IsBotSound
       EnterComplete CallFwd CombFwd)
  case FinE
  show ?case by (rule nest_finE)
next
  case PP
  show ?case by (rule nest_1_pp_st[unfolded nest_1_eqs_def])
next
  case (SgCov v c)
  show ?case using SgCov by (simp add: nest_1_sg_covered nest_gamma_def)
next
  case (SgUncov v c)
  show ?case using SgUncov by (rule nest_1_sg_uncovered_empty)
next
  case (Fwd u a v c)
  show ?case using Fwd by (rule nest_fwd_closed_1)
next
  case IsBotBot show ?case by simp
next
  case (IsBotSound d gv) then show ?case by (simp add: nest_gamma_eq)
next
  case (EnterComplete u ctx dst pars args p cont s)
  let ?ci = "call_info_of (CallEdge dst pars args) p"
  let ?caller = "locals (snd nest_1_sol (Inl (u, ctx)))"
  have cov: "entry_pairs_cover (\<lambda>d. nest_gamma d (globs (snd nest_1_sol (Inr Global)))) s
      (call_enter nest_gs (CallEdge dst pars args) s)
      [(?caller, transfer_lift nest_empty_pred (ivl_enter_st_for nest_gs ?ci) ?caller)]"
    using nest_domain.entry_pairs_cover_st
            [OF ivl_is_sound_transfer_for, where ci = ?ci and d = ?caller]
      EnterComplete(3)
    by (simp add: nest_gamma_eq nest_domain.gamma_exec_def)
  show ?case
    unfolding nest_S_st_def dgs_enter_local_state_st_for_lifted
    using enter_runs_local_enter_transfer enter_deps_local_enter_transfer cov by fastforce
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
    and "s \<in> gamma_state_lift (map_lift (fun_of_resolved_st_q_for nest_gs) (nest_1_sg (Inl (u, ctx))))"
  shows "call_enter nest_gs (CallEdge dst xs es) s
           \<in> gamma_state_lift (map_lift (fun_of_resolved_st_q_for nest_gs)
               (nest_1_sg (Inl (FunctionEntry p,
                 cs_context 1 u ctx (call_enter nest_gs (CallEdge dst xs es) s)))))"
proof (rule nest_1_cs.routed_context_call[OF assms[unfolded nest_cfg_def]])
  show "call_context_rel_of_fun (cs_context 1) u ctx (call_info_of (CallEdge dst xs es) p) s
          (call_enter nest_gs (CallEdge dst xs es) s)
          (cs_context 1 u ctx (call_enter nest_gs (CallEdge dst xs es) s))"
    by simp
qed

lemma nest_1_sg_comb:
  assumes "(cl, CallEdge dst pars args, FunctionEntry p, v) \<in> calls nest_cfg"
    and "s \<in> gamma_state_lift (map_lift (fun_of_resolved_st_q_for nest_gs) (nest_1_sg (Inl (cl, c1))))"
    and "t \<in> gamma_state_lift (map_lift (fun_of_resolved_st_q_for nest_gs)
               (nest_1_sg (Inl (FunctionResult p, cs_context 1 cl c1 es))))"
    and "call_enter_store nest_gs nest_cfg cl s es"
  shows "combine_collect nest_gs dst s t
           \<in> gamma_state_lift (map_lift (fun_of_resolved_st_q_for nest_gs) (nest_1_sg (Inl (v, c1))))"
proof -
  from assms(4) obtain dst' pars' args' p' cont' where
      ce': "(cl, CallEdge dst' pars' args', FunctionEntry p', cont') \<in> calls nest_cfg"
    and es_eq: "es = call_enter nest_gs (CallEdge dst' pars' args') s"
    unfolding call_enter_store_def by blast
  have adm: "admits_call_context nest_gs (compile_prog nest_pi nest_procs)
          (call_context_rel_of_fun (cs_context 1)) cl c1 p' s es (cs_context 1 cl c1 es)"
    unfolding admits_call_context_def call_context_rel_of_fun_iff
    using ce'[unfolded nest_cfg_def] es_eq by blast
  show ?thesis
    by (rule nest_1_cs.routed_context_comb[OF assms(1)[unfolded nest_cfg_def]
          assms(2)[unfolded nest_cfg_def] adm assms(3)[unfolded nest_cfg_def]])
qed

section \<open>The headline theorem: 1-call-string activation collecting soundness\<close>

lemma nest_cinit_le_cinit_ivl_st:
  "cinit_stores nest_gs \<subseteq> nest_gamma (Lifted cinit_ivl_st) Bot"
  by (auto simp: nest_gamma_def cinit_stores_def gamma_state_def fun_of_resolved_st_q_for_def
                 fun_of_st_cinit_ivl_st_for)

text \<open>The routed interpretation carries the theorem: every store the 1-call-string
  activation-local collecting semantics reaches at \<open>(v, ctx)\<close> is concretized by the solved
  local unknown at that key, read back into an abstract state.\<close>

theorem nest_1_activation_collect_sound:
  "activation_collect nest_gs (call_context_rel_of_fun (cs_context 1)) [] nest_cfg (cinit_stores nest_gs) v ctx
     \<subseteq> gamma_state_lift (map_lift (fun_of_resolved_st_q_for nest_gs) (nest_1_sg (Inl (v, ctx))))"
  by (rule nest_1_cs.activation_collect_sound[unfolded nest_cfg_compile,
            OF entry_covered_1 nest_cinit_le_cinit_ivl_st])

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
  "nestg_cfg = compile_prog (prog_table nestg_program) (prog_procs nestg_program)"

definition nestg_empty_pred :: "ivl resolved_st_q \<Rightarrow> bool" where
  "nestg_empty_pred = resolved_st_q_is_bot_for (declared_global_vars nestg_program)"

definition nestg_1_eqs ::
  "(pp \<times> cfg_node list, call_string_gk,
     (ivl exec_dg_st lifted, ivl exec_dg_st lifted) dg_state) eqsT" where
  "nestg_1_eqs =
     routed_node_rhs intra_predecessor_addr_list (\<lambda>_. Global) (cs_route 1)
      (\<lambda>ctx' src a. dg_spec_edge_tree
         (local_state_dg_spec_st_for_lifted nestg_gs nestg_empty_pred
            (ivl_tf_st_for nestg_gs) (ivl_enter_st_for nestg_gs)) a src (\<lambda>_. Global))
      (routed_call_tree (local_state_dg_spec_st_for_lifted nestg_gs nestg_empty_pred
                       (ivl_tf_st_for nestg_gs) (ivl_enter_st_for nestg_gs)) Global Seed
         (static_resolve nestg_cfg) (\<lambda>d. d = Bot))
      (routed_entry_seed_tree Seed)
       nestg_cfg
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
        let sc = compiled_procedure_scope nest_gs nest_pi nest_procs
          nest_cfg p
        in scope_formals sc @ scope_locals sc),
      return_slot_for_pp = (\<lambda>p.
        scope_return_slot (compiled_procedure_scope nest_gs nest_pi nest_procs
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
      owner_of = String.explode o compiled_owner_of nest_pi nest_procs,
      cluster_label = (\<lambda>owner ctx.
        if owner = ''main'' \<and> ctx = [] then ''main / root context''
        else owner @ '' / call string='' @ ''['' @ join_source '', '' (map string_of_cfg_node ctx) @ '']''),
      source_text = Some (pretty_string_of_program nest_pi nest_procs nest_main []),
      node_annotation = (\<lambda>_ _. None)
    \<rparr>"

definition nest_1_contexts_for_pp :: "pp \<Rightarrow> cfg_node list list" where
  "nest_1_contexts_for_pp p =
    (let owner = compiled_owner_of nest_pi nest_procs p
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

lemma nest_1_graph_wf: "analysis_graph_wf nest_1_graph"
  unfolding nest_1_graph_def nest_cfg_def
  by (rule build_analysis_graph_wf
        [OF calls_source_unique_compile_prog compile_prog_finite[THEN conjunct2]])

lemma nest_1_graph_domain_is_covered:
  "list_all (\<lambda>x. case x of Inl pc \<Rightarrow> pc \<in> fst nest_1_sol | Inr _ \<Rightarrow> True)
    nest_1_graph_domain" by eval

lemma nest_1_dot_nonempty: "String.explode nest_1_dot \<noteq> []" by eval


end


