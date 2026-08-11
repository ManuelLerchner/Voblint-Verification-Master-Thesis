theory Example_Interval_DG_CallString_K1
  imports
    "Voblint_Analysis.Interval_DG"
    "Voblint_Analysis.Ivl_Exec"
    "Voblint_Core.Routed_Context"
    "Voblint_Core.Activation_Backbone"
    "Voblint_Core.DG_Ctx_Activation"
    "Voblint_Core.Call_String_Context"
    "Voblint_Analysis.Analysis_GraphViz"
    "Voblint_Analysis.Exec_DG_Bridge"
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

abbreviation nest_lookup_exec_dg_st :: "('a::bot) exec_dg_st \<Rightarrow> vname \<Rightarrow> 'a" where
  "nest_lookup_exec_dg_st s x \<equiv> lookup_resolved_st_q s (location_of nest_gs x)"

abbreviation nest_update_exec_dg_st :: "('a::bot) exec_dg_st \<Rightarrow> vname \<Rightarrow> 'a \<Rightarrow> 'a exec_dg_st" where
  "nest_update_exec_dg_st s x a \<equiv> update_resolved_st_q s (location_of nest_gs x) a"

definition nest_pi :: proc_table where "nest_pi = prog_table nest_program"
definition nest_procs :: "pname list" where "nest_procs = prog_procs nest_program"
definition nest_main :: "VIMP_Proc.com" where "nest_main = prog_main nest_program"

definition nest_cfg :: cfg where
  "nest_cfg = compile_prog nest_pi nest_procs (STR ''main'') nest_main"

lemma nest_entry: "cfg_entry nest_cfg = FunctionEntry (STR ''main'')" by eval

text \<open>\<open>main\<close> calls \<open>f\<close> at two sites (\<open>Statement 5\<close>, args \<open>3\<close>; \<open>Statement 6\<close>, args \<open>10\<close>).
  \<open>f\<close> calls \<open>g\<close> at one site inside its own body (\<open>Statement 2\<close>), passing through its own
  parameter --- the same source location regardless of which \<open>f\<close> activation runs it.\<close>

lemma nest_finE: "finite (intra nest_cfg)" unfolding nest_cfg_def using compile_prog_finite by simp
lemma nest_finC: "finite (calls nest_cfg)" unfolding nest_cfg_def using compile_prog_finite by simp

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

text \<open>Each call site has exactly one outgoing edge.\<close>
lemma nest_calls_unique_site:
  "\<forall>(u1, ca1, ce1, k1) \<in> calls nest_cfg. \<forall>(u2, ca2, ce2, k2) \<in> calls nest_cfg.
      u1 = u2 \<longrightarrow> ca1 = ca2 \<and> ce1 = ce2 \<and> k1 = k2"
  unfolding nest_cfg_def by eval

subsection \<open>The interval domain, executable and abstract\<close>

definition Spoly :: "(ivl exec_dg_st, ivl exec_dg_st) dg_spec" where
  "Spoly = unit_dg_spec_st_for nest_gs (ivl_tf_st_for nest_gs) (ivl_enter_st_for nest_gs)"

abbreviation Sabs :: "(ivl abs_state, ivl abs_state) dg_spec" where
  "Sabs \<equiv> unit_dg_spec_for nest_gs (ivl_tf_for nest_gs)"

lemmas ivl_Hstep =
  unit_dg_Hstep_for[OF ivl_tf_st_for_commute[folded fun_of_exec_dg_st_for_def]
    ivl_tf_st_for_reduces]
lemmas ivl_Henter = unit_dg_Henter_for[OF ivl_enter_st_for_commute[folded fun_of_exec_dg_st_for_def]]
lemmas ivl_Hcomb = unit_dg_Hcomb_for

subsection \<open>A call-string-keyed global-key type\<close>

datatype gk_1 = Global1 | Seed1 (seed1_pp: pp) (seed1_cs: "cfg_node list")

subsection \<open>The routed equation system and its computed solution\<close>

definition nest_1_eqs :: "(pp \<times> cfg_node list, gk_1, (ivl exec_dg_st, ivl exec_dg_st) dg_state) eqsT" where
  "nest_1_eqs =
     side_cfg_T_eff_keyed_seed_dg intra_predecessor_list (\<lambda>_. Global1) (cs_route 1)
      (routed_cmb Spoly Global1 Seed1) (routed_extra Seed1 Global1)
       nest_cfg Spoly bot cinit_ivl_st (restrict_global_resolved_q cinit_ivl_st)"

definition nest_1_sol ::
  "(pp \<times> cfg_node list) set \<times> (pp \<times> cfg_node list + gk_1 \<Rightarrow> (ivl exec_dg_st, ivl exec_dg_st) dg_state)" where
  "nest_1_sol = TD_side_warrowing_apinis_Interp_solve nest_1_eqs
                    (cfg_exit nest_cfg, [])"

lemma nest_1_terminates:
  "TD_side_warrowing_apinis_Interp_solve_c nest_1_eqs (cfg_exit nest_cfg, [])
     \<noteq> None"
  by eval

subsection \<open>Coverage\<close>

lemma entry_covered_1: "(cfg_entry nest_cfg, []) \<in> fst nest_1_sol"
  unfolding nest_1_sol_def nest_1_eqs_def nest_entry by eval

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
  unfolding nest_1_sol_def nest_1_eqs_def by eval
lemma callee_covered_f10_1: "(FunctionEntry (STR ''f''), [Statement 6]) \<in> fst nest_1_sol"
  unfolding nest_1_sol_def nest_1_eqs_def by eval
lemma callee_covered_g_1: "(FunctionEntry (STR ''g''), [Statement 2]) \<in> fst nest_1_sol"
  unfolding nest_1_sol_def nest_1_eqs_def by eval

lemma covered_ret6_1: "(Statement 6, []) \<in> fst nest_1_sol"
  unfolding nest_1_sol_def nest_1_eqs_def by eval
lemma covered_ret7_1: "(Statement 7, []) \<in> fst nest_1_sol"
  unfolding nest_1_sol_def nest_1_eqs_def by eval
lemma covered_ret3_f3_1: "(Statement 3, [Statement 5]) \<in> fst nest_1_sol"
  unfolding nest_1_sol_def nest_1_eqs_def by eval
lemma covered_ret3_f10_1: "(Statement 3, [Statement 6]) \<in> fst nest_1_sol"
  unfolding nest_1_sol_def nest_1_eqs_def by eval

lemma callee_exit_f3_1: "(FunctionResult (STR ''f''), [Statement 5]) \<in> fst nest_1_sol"
  unfolding nest_1_sol_def nest_1_eqs_def by eval
lemma callee_exit_f10_1: "(FunctionResult (STR ''f''), [Statement 6]) \<in> fst nest_1_sol"
  unfolding nest_1_sol_def nest_1_eqs_def by eval
lemma callee_exit_g_1: "(FunctionResult (STR ''g''), [Statement 2]) \<in> fst nest_1_sol"
  unfolding nest_1_sol_def nest_1_eqs_def by eval

section \<open>Abstract transport of the routed solution\<close>

text \<open>The return combine and the enter transfer each commute componentwise with an
  arbitrary incoming global slot.\<close>

lemma dgs_combine_snd_commute_gen:
  "fun_of_exec_dg_st_for nest_gs (snd (dgs_combine Spoly dst dc de g))
     = snd (dgs_combine Sabs dst (fun_of_exec_dg_st_for nest_gs dc) (fun_of_exec_dg_st_for nest_gs de) (fun_of_exec_dg_st_for nest_gs g))"
proof -
  have step: "map_prod (fun_of_exec_dg_st_for nest_gs) (fun_of_exec_dg_st_for nest_gs)
                (dgs_combine (unit_dg_spec_st_for nest_gs (ivl_tf_st_for nest_gs) (ivl_enter_st_for nest_gs)) dst dc de g)
              = dgs_combine Sabs dst (fun_of_exec_dg_st_for nest_gs dc) (fun_of_exec_dg_st_for nest_gs de) (fun_of_exec_dg_st_for nest_gs g)"
    by (rule ivl_Hcomb)
  have "fun_of_exec_dg_st_for nest_gs (snd (dgs_combine (unit_dg_spec_st_for nest_gs (ivl_tf_st_for nest_gs) (ivl_enter_st_for nest_gs)) dst dc de g))
      = snd (map_prod (fun_of_exec_dg_st_for nest_gs) (fun_of_exec_dg_st_for nest_gs)
               (dgs_combine (unit_dg_spec_st_for nest_gs (ivl_tf_st_for nest_gs) (ivl_enter_st_for nest_gs)) dst dc de g))"
    by (metis snd_conv map_prod_simp surj_pair)
  also have "\<dots> = snd (dgs_combine Sabs dst (fun_of_exec_dg_st_for nest_gs dc) (fun_of_exec_dg_st_for nest_gs de) (fun_of_exec_dg_st_for nest_gs g))"
    by (simp add: step)
  finally show ?thesis by (simp add: Spoly_def)
qed

lemma dgs_combine_fst_commute_gen:
  "fun_of_exec_dg_st_for nest_gs (fst (dgs_combine Spoly dst dc de g))
     = fst (dgs_combine Sabs dst (fun_of_exec_dg_st_for nest_gs dc) (fun_of_exec_dg_st_for nest_gs de) (fun_of_exec_dg_st_for nest_gs g))"
proof -
  have step: "map_prod (fun_of_exec_dg_st_for nest_gs) (fun_of_exec_dg_st_for nest_gs) (dgs_combine (unit_dg_spec_st_for nest_gs (ivl_tf_st_for nest_gs) (ivl_enter_st_for nest_gs)) dst dc de g)
              = dgs_combine Sabs dst (fun_of_exec_dg_st_for nest_gs dc) (fun_of_exec_dg_st_for nest_gs de) (fun_of_exec_dg_st_for nest_gs g)"
    by (rule ivl_Hcomb)
  have "fun_of_exec_dg_st_for nest_gs (fst (dgs_combine (unit_dg_spec_st_for nest_gs (ivl_tf_st_for nest_gs) (ivl_enter_st_for nest_gs)) dst dc de g))
      = fst (map_prod (fun_of_exec_dg_st_for nest_gs) (fun_of_exec_dg_st_for nest_gs) (dgs_combine (unit_dg_spec_st_for nest_gs (ivl_tf_st_for nest_gs) (ivl_enter_st_for nest_gs)) dst dc de g))"
    by (metis fst_conv map_prod_simp surj_pair)
  also have "\<dots> = fst (dgs_combine Sabs dst (fun_of_exec_dg_st_for nest_gs dc) (fun_of_exec_dg_st_for nest_gs de) (fun_of_exec_dg_st_for nest_gs g))"
    by (simp add: step)
  finally show ?thesis by (simp add: Spoly_def)
qed

lemma dgs_enter_snd_commute_gen:
  "fun_of_exec_dg_st_for nest_gs (snd (dgs_enter Spoly fs as d g))
     = snd (dgs_enter Sabs fs as (fun_of_exec_dg_st_for nest_gs d) (fun_of_exec_dg_st_for nest_gs g))"
proof -
  have step: "map_prod (fun_of_exec_dg_st_for nest_gs) (fun_of_exec_dg_st_for nest_gs) (dgs_enter (unit_dg_spec_st_for nest_gs (ivl_tf_st_for nest_gs) (ivl_enter_st_for nest_gs)) fs as d g)
              = dgs_enter Sabs fs as (fun_of_exec_dg_st_for nest_gs d) (fun_of_exec_dg_st_for nest_gs g)"
    by (rule ivl_Henter)
  have "fun_of_exec_dg_st_for nest_gs (snd (dgs_enter (unit_dg_spec_st_for nest_gs (ivl_tf_st_for nest_gs) (ivl_enter_st_for nest_gs)) fs as d g))
      = snd (map_prod (fun_of_exec_dg_st_for nest_gs) (fun_of_exec_dg_st_for nest_gs) (dgs_enter (unit_dg_spec_st_for nest_gs (ivl_tf_st_for nest_gs) (ivl_enter_st_for nest_gs)) fs as d g))"
    by (metis snd_conv map_prod_simp surj_pair)
  also have "\<dots> = snd (dgs_enter Sabs fs as (fun_of_exec_dg_st_for nest_gs d) (fun_of_exec_dg_st_for nest_gs g))"
    by (simp add: step)
  finally show ?thesis by (simp add: Spoly_def)
qed

lemma dgs_enter_fst_commute_gen:
  "fun_of_exec_dg_st_for nest_gs (fst (dgs_enter Spoly fs as d g))
     = fst (dgs_enter Sabs fs as (fun_of_exec_dg_st_for nest_gs d) (fun_of_exec_dg_st_for nest_gs g))"
proof -
  have step: "map_prod (fun_of_exec_dg_st_for nest_gs) (fun_of_exec_dg_st_for nest_gs) (dgs_enter (unit_dg_spec_st_for nest_gs (ivl_tf_st_for nest_gs) (ivl_enter_st_for nest_gs)) fs as d g)
              = dgs_enter Sabs fs as (fun_of_exec_dg_st_for nest_gs d) (fun_of_exec_dg_st_for nest_gs g)"
    by (rule ivl_Henter)
  have "fun_of_exec_dg_st_for nest_gs (fst (dgs_enter (unit_dg_spec_st_for nest_gs (ivl_tf_st_for nest_gs) (ivl_enter_st_for nest_gs)) fs as d g))
      = fst (map_prod (fun_of_exec_dg_st_for nest_gs) (fun_of_exec_dg_st_for nest_gs) (dgs_enter (unit_dg_spec_st_for nest_gs (ivl_tf_st_for nest_gs) (ivl_enter_st_for nest_gs)) fs as d g))"
    by (metis fst_conv map_prod_simp surj_pair)
  also have "\<dots> = fst (dgs_enter Sabs fs as (fun_of_exec_dg_st_for nest_gs d) (fun_of_exec_dg_st_for nest_gs g))"
    by (simp add: step)
  finally show ?thesis by (simp add: Spoly_def)
qed

text \<open>\<open>cs_route\<close> ignores its data argument, so every \<open>Side\<close> key computed from it is
  literally the same term on the executable and the abstract carrier.\<close>

lemma dg_tree_st_commute_frame_read_1:
  "dg_tree_st_commute_for nest_gs env
     (QueryG (Seed1 v ctx) (\<lambda>s. Answer (DG (globs s) bot)))
     (QueryG (Seed1 v ctx) (\<lambda>s. Answer (DG (globs s) bot)))"
  by (simp add: dg_tree_st_commute_for_def fun_of_dg_st_for_simps fun_of_exec_dg_st_for_bot o_def
                dep_aux_def bot_fun_def)

lemma dg_tree_st_commute_routed_cmb_1:
  "dg_tree_st_commute_for nest_gs env (routed_cmb Spoly Global1 Seed1 (cs_route 1) ctx ca cc ex)
                          (routed_cmb Sabs Global1 Seed1 (cs_route 1) ctx ca cc ex)"
  unfolding routed_cmb_def Let_def
  by (cases ca)
     (simp_all add: dg_tree_st_commute_for_def fun_of_dg_st_for_simps fun_of_exec_dg_st_for_bot o_def
                    cs_route_def dgs_combine_fst_commute_gen dgs_combine_snd_commute_gen
                    dgs_enter_fst_commute_gen dgs_enter_snd_commute_gen fun_of_dg_st_for_sup
                    dep_aux_def bot_fun_def fun_upd_apply fun_eq_iff)

lemma hextra_commute_routed_1:
  "list_all2 (dg_tree_st_commute_for nest_gs env)
     (routed_extra Seed1 Global1 (cs_route 1) ctx w)
     (routed_extra Seed1 Global1 (cs_route 1) ctx w)"
  unfolding routed_extra_def Let_def
  by (auto simp: dg_tree_st_commute_frame_read_1 split: cfg_node.split)

lemma nest_1_solve_dom:
  "TD_side_warrowing_apinis_Interp.solve_dom TYPE(gk_1) TYPE((ivl exec_dg_st, ivl exec_dg_st) dg_state)
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

theorem nest_1_pp_abs:
  "part_post_solution
     (side_cfg_T_eff_keyed_seed_dg intra_predecessor_list (\<lambda>_. Global1) (cs_route 1)
       (routed_cmb Sabs Global1 Seed1) (routed_extra Seed1 Global1) nest_cfg Sabs
        (fun_of_exec_dg_st_for nest_gs (bot::ivl exec_dg_st)) (fun_of_exec_dg_st_for nest_gs cinit_ivl_st) (fun_of_exec_dg_st_for nest_gs (restrict_global_resolved_q cinit_ivl_st)))
     (cfg_exit nest_cfg, []) (fun_of_dg_st_for nest_gs \<circ> snd nest_1_sol) (fst nest_1_sol)"
proof -
  have pp': "part_post_solution
       (side_cfg_T_eff_keyed_seed_dg intra_predecessor_list (\<lambda>_. Global1) (cs_route 1)
          (routed_cmb Spoly Global1 Seed1) (routed_extra Seed1 Global1) nest_cfg Spoly
          bot cinit_ivl_st (restrict_global_resolved_q cinit_ivl_st))
       (cfg_exit nest_cfg, []) (snd nest_1_sol) (fst nest_1_sol)"
    using nest_1_pp_st unfolding nest_1_eqs_def by simp
  have ivl_Hstep_1:
    "map_prod (fun_of_exec_dg_st_for nest_gs) (fun_of_exec_dg_st_for nest_gs) (dg_spec_step Spoly a d g') =
       dg_spec_step Sabs a (fun_of_exec_dg_st_for nest_gs d) (fun_of_exec_dg_st_for nest_gs g')" for a d g'
    unfolding Spoly_def by (rule ivl_Hstep)
  show ?thesis
    by (rule part_post_solution_seed_dg_st_to_abs_for
          [where gs = nest_gs and pred_sel = intra_predecessor_list and gkey = "\<lambda>_. Global1"
             and route_st = "cs_route 1" and route_abs = "cs_route 1"
             and cmb_st = "routed_cmb Spoly Global1 Seed1" and cmb_abs = "routed_cmb Sabs Global1 Seed1"
             and extra_st = "routed_extra Seed1 Global1"
             and extra_abs = "routed_extra Seed1 Global1"
             and g = nest_cfg and S_st = Spoly and S_abs = Sabs,              OF ivl_Hstep_1 cs_route_indep_of_data dg_tree_st_commute_routed_cmb_1
              hextra_commute_routed_1 pp'])
qed

section \<open>Activation-indexed collecting soundness for the 1-call-string-routed solution\<close>

abbreviation sigma_1 :: "pp \<times> cfg_node list + gk_1 \<Rightarrow> (ivl abs_state, ivl abs_state) dg_state" where
  "sigma_1 \<equiv> fun_of_dg_st_for nest_gs \<circ> snd nest_1_sol"

abbreviation gen_1_abs :: "(pp \<times> cfg_node list, gk_1, (ivl abs_state, ivl abs_state) dg_state) eqsT" where
  "gen_1_abs \<equiv> side_cfg_T_eff_keyed_seed_dg intra_predecessor_list (\<lambda>_. Global1) (cs_route 1)
       (routed_cmb Sabs Global1 Seed1) (routed_extra Seed1 Global1) nest_cfg Sabs
       (fun_of_exec_dg_st_for nest_gs (bot::ivl exec_dg_st)) (fun_of_exec_dg_st_for nest_gs cinit_ivl_st) (fun_of_exec_dg_st_for nest_gs (restrict_global_resolved_q cinit_ivl_st))"

lemma pp_eq_bound_1:
  "(v, ctx) \<in> fst nest_1_sol
     \<Longrightarrow> eq gen_1_abs (v, ctx) sigma_1 \<le> sigma_1 (Inl (v, ctx))"
  using nest_1_pp_abs by simp

lemma side_acc_dg_ge_1: "acc \<le> side_acc_dg acc \<tau> ts"
proof (induction ts arbitrary: acc)
  case (Cons t ts)
  show ?case
    using Cons.IH[of "acc \<squnion> locals (traverse_rhs t \<tau>)"]
    by (simp add: le_supI1)
qed simp

definition ivl_ctx_sg_1 :: "pp \<times> cfg_node list + gk_1 \<Rightarrow> ivl abs_state" where
  "ivl_ctx_sg_1 k =
     (case k of
        Inl (v, ctx) \<Rightarrow>
          (if (v, ctx) \<in> fst nest_1_sol
           then combine_env\<^sup># nest_gs (locals (sigma_1 (Inl (v, ctx)))) (globs (sigma_1 (Inr Global1)))
           else bot)
      | Inr _ \<Rightarrow> bot)"

lemma ivl_ctx_sg_1_covered:
  "(v, ctx) \<in> fst nest_1_sol
   \<Longrightarrow> ivl_ctx_sg_1 (Inl (v, ctx))
       = combine_env\<^sup># nest_gs (locals (sigma_1 (Inl (v, ctx)))) (globs (sigma_1 (Inr Global1)))"
  by (simp add: ivl_ctx_sg_1_def)

lemma ivl_ctx_sg_1_uncovered_empty:
  "(v, ctx) \<notin> fst nest_1_sol \<Longrightarrow> \<lbrakk>ivl_ctx_sg_1 (Inl (v, ctx))\<rbrakk> = {}"
  by (simp add: ivl_ctx_sg_1_def gamma_state_bot)

lemma entry_locals_ge_s0d_1:
  assumes cov: "(cfg_entry nest_cfg, []) \<in> fst nest_1_sol"
  shows "fun_of_exec_dg_st_for nest_gs cinit_ivl_st \<le> locals (sigma_1 (Inl (cfg_entry nest_cfg, [])))"
proof -
  have "fun_of_exec_dg_st_for nest_gs cinit_ivl_st
          \<le> locals (eq gen_1_abs (cfg_entry nest_cfg, []) sigma_1)"
    by (simp add: eq_side_cfg_T_eff_keyed_seed_dg)
       (rule order_trans[OF _ side_acc_dg_ge_1], simp add: le_supI2)
  also have "\<dots> \<le> locals (sigma_1 (Inl (cfg_entry nest_cfg, [])))"
    using pp_eq_bound_1[OF cov] by (simp add: less_eq_dg_state_def)
  finally show ?thesis .
qed

text \<open>\<open>nest_program\<close> declares no globals, so \<^const>\<open>nest_gs\<close> has no pre-registered
  \<^locale>\<open>sound_dg_spec\<close> interpretation for the diagonal interval spec: establish it
  once here, in this chain's shared ancestor, so every downstream
  \<open>dg_ctx_activation\<close>/\<open>routed_context\<close> interpretation on \<open>Sabs\<close> discharges its
  inherited step/combine/enter obligations automatically.\<close>

lemma nest_reserved: "reserved_ret_var nest_gs"
  unfolding reserved_ret_var_def by eval

interpretation ivl_dg_for: sound_dg_spec Sabs "gamma_unit nest_gs" nest_gs
  by (rule sound_dg_spec_unit_for[OF ivl_is_sound_transfer_for nest_reserved])

interpretation nest_1_dg: dg_ctx_activation Sabs nest_gs nest_cfg Global1 "cs_route 1"
    "routed_cmb Sabs Global1 Seed1" "routed_extra Seed1 Global1"
    "fun_of_exec_dg_st_for nest_gs (bot::ivl exec_dg_st)" "fun_of_exec_dg_st_for nest_gs cinit_ivl_st" "fun_of_exec_dg_st_for nest_gs (restrict_global_resolved_q cinit_ivl_st)"
    sigma_1 "fst nest_1_sol" "(cfg_exit nest_cfg, [])" ivl_ctx_sg_1
proof unfold_locales
  show "finite (intra nest_cfg)" by (rule nest_finE)
next
  show "part_post_solution
          (side_cfg_T_eff_keyed_seed_dg intra_predecessor_list (\<lambda>_. Global1) (cs_route 1)
             (routed_cmb Sabs Global1 Seed1) (routed_extra Seed1 Global1) nest_cfg Sabs
             (fun_of_exec_dg_st_for nest_gs (bot::ivl exec_dg_st)) (fun_of_exec_dg_st_for nest_gs cinit_ivl_st)
             (fun_of_exec_dg_st_for nest_gs (restrict_global_resolved_q cinit_ivl_st)))
          (cfg_exit nest_cfg, []) sigma_1 (fst nest_1_sol)"
    by (rule nest_1_pp_abs)
next
  fix v ctx
  assume "(v, ctx) \<in> fst nest_1_sol"
  thus "ivl_ctx_sg_1 (Inl (v, ctx))
          = combine_env\<^sup># nest_gs (locals (sigma_1 (Inl (v, ctx)))) (globs (sigma_1 (Inr Global1)))"
    by (rule ivl_ctx_sg_1_covered)
next
  fix v ctx
  assume "(v, ctx) \<notin> fst nest_1_sol"
  thus "\<lbrakk>ivl_ctx_sg_1 (Inl (v, ctx))\<rbrakk> = {}"
    by (rule ivl_ctx_sg_1_uncovered_empty)
next
  fix u a v ctx
  assume "(u, ctx) \<in> fst nest_1_sol" "(u, a, v) \<in> intra nest_cfg"
  thus "(v, ctx) \<in> fst nest_1_sol" by (rule nest_fwd_closed_1)
qed

text \<open>\<open>cs_route 1\<close> and \<open>cs_context 1\<close> are the identical closed term \<open>take 1 (u # ctx)\<close>, so
  \<open>route_enterc_agree\<close> is bare reflexivity. \<open>g\<close>'s single call site is reached at either of
  \<open>f\<close>'s two activation contexts (\<open>enter_callers_g_1\<close>), but \<open>take 1\<close> erases that distinction
  before it reaches the goal, so \<open>CallFwd\<close> does not need to case-split on which one.\<close>

interpretation nest_1_routed: routed_context Sabs nest_gs nest_cfg Global1 "cs_route 1"
    "fun_of_exec_dg_st_for nest_gs (bot::ivl exec_dg_st)" "fun_of_exec_dg_st_for nest_gs cinit_ivl_st" "fun_of_exec_dg_st_for nest_gs (restrict_global_resolved_q cinit_ivl_st)"
    sigma_1 "fst nest_1_sol" "(cfg_exit nest_cfg, [])" ivl_ctx_sg_1
    Seed1 "cs_context 1"
proof (unfold_locales, goal_cases FinC SeedKey RouteAgree CallFwd CombFwd EnterAgree)
  case FinC
  show ?case by (rule nest_finC)
next
  case (SeedKey p ctx)
  show ?case by simp
next
  case (RouteAgree u ctx dst pars args p cont s)
  show ?case by (rule cs_route_context_agree)
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
  note covCl = CombFwd(1) and ce = CombFwd(2)
  show ?case
    using ce covCl enter_callers_only_root_main_1 enter_callers_g_1
          covered_ret3_f3_1 covered_ret3_f10_1 covered_ret6_1 covered_ret7_1
          nest_calls_shape
    by fastforce
next
  case (EnterAgree cl s es dst pars args p cont)
  note ces = EnterAgree(1) and ce = EnterAgree(2)
  show ?case
    using ces ce nest_calls_unique_site unfolding call_enter_store_def by fastforce
qed

lemma ivl_ctx_sg_1_seed:
  assumes "(u, CallEdge dst xs es, FunctionEntry p, cont) \<in> calls nest_cfg"
    and "s \<in> \<lbrakk>ivl_ctx_sg_1 (Inl (u, ctx))\<rbrakk>"
  shows "call_enter nest_gs (CallEdge dst xs es) s
           \<in> \<lbrakk>ivl_ctx_sg_1 (Inl (FunctionEntry p,
                 cs_context 1 u ctx (call_enter nest_gs (CallEdge dst xs es) s)))\<rbrakk>"
  by (rule nest_1_routed.routed_context_call[OF assms])

lemma ivl_ctx_sg_1_comb:
  assumes "(cl, CallEdge dst pars args, FunctionEntry p, v) \<in> calls nest_cfg"
    and "s \<in> \<lbrakk>ivl_ctx_sg_1 (Inl (cl, c1))\<rbrakk>"
    and "t \<in> \<lbrakk>ivl_ctx_sg_1 (Inl (FunctionResult p, cs_context 1 cl c1 es))\<rbrakk>"
    and "call_enter_store nest_gs nest_cfg cl s es"
  shows "combine_collect nest_gs dst s t \<in> \<lbrakk>ivl_ctx_sg_1 (Inl (v, c1))\<rbrakk>"
  by (rule nest_1_routed.routed_context_comb[OF assms])

section \<open>The headline theorem: 1-call-string activation collecting soundness\<close>

lemma cinit_le_cinit_ivl_st_1: "cinit_stores nest_gs \<subseteq> \<lbrakk>fun_of_exec_dg_st_for nest_gs cinit_ivl_st\<rbrakk>"
  by (auto simp: cinit_stores_def gamma_state_def fun_of_exec_dg_st_for_def fun_of_st_cinit_ivl_st_for)

theorem nest_1_activation_collect_sound:
  "activation_collect nest_gs (admiss_exact (cs_context 1)) [] nest_cfg (cinit_stores nest_gs) v ctx
     \<subseteq> \<lbrakk>ivl_ctx_sg_1 (Inl (v, ctx))\<rbrakk>"
proof (rule activation_collect_sound[where sg = ivl_ctx_sg_1 and admiss = "admiss_exact (cs_context 1)"
        and startcontext = "[]"
        and S = "cinit_stores nest_gs" and g = nest_cfg and gs = nest_gs])
  \<comment> \<open>ENTRY_G\<close>
  text \<open>Both the local seed \<open>s0d\<close> and the global seed \<open>s0g\<close> are \<open>cinit_ivl_st\<close>'s own
    projections, so routing them back together through \<open>combine_env\<^sup>#\<close> exactly recovers
    \<open>s0d\<close>; the membership transports through \<open>gamma_unit_mono\<close> componentwise, needing
    the caller's local bound (\<open>entry_locals_ge_s0d_1\<close>) and the entry's global-seed
    bound (\<open>nest_1_dg.pp_entry_s0g_bound\<close>) separately instead of one joined bound.\<close>
  fix s assume "s \<in> cinit_stores nest_gs"
  hence "s \<in> \<lbrakk>fun_of_exec_dg_st_for nest_gs cinit_ivl_st\<rbrakk>" using cinit_le_cinit_ivl_st_1 by blast
  also have "\<lbrakk>fun_of_exec_dg_st_for nest_gs cinit_ivl_st\<rbrakk>
        = gamma_unit nest_gs (fun_of_exec_dg_st_for nest_gs cinit_ivl_st)
            (fun_of_exec_dg_st_for nest_gs (restrict_global_resolved_q cinit_ivl_st))"
    unfolding gamma_unit_def fun_of_exec_dg_st_for_def
    by (rule arg_cong[where f = gamma_state], rule ext)
       (simp add: combine_env_abs_def restrict_global_for_def)
  also have "\<dots> \<subseteq> gamma_unit nest_gs (locals (sigma_1 (Inl (cfg_entry nest_cfg, []))))
                   (globs (sigma_1 (Inr Global1)))"
    by (rule gamma_unit_mono[OF entry_locals_ge_s0d_1[OF entry_covered_1]
          nest_1_dg.pp_entry_s0g_bound[OF entry_covered_1]])
  also have "\<dots> = \<lbrakk>ivl_ctx_sg_1 (Inl (cfg_entry nest_cfg, []))\<rbrakk>"
    unfolding ivl_ctx_sg_1_covered[OF entry_covered_1] gamma_unit_def by (rule refl)
  finally show "s \<in> \<lbrakk>ivl_ctx_sg_1 (Inl (cfg_entry nest_cfg, []))\<rbrakk>" .
next
  \<comment> \<open>EDGE --- discharged generically off the post-solution by \<open>dg_ctx_activation\<close>.\<close>
  show "\<And>u a v c s s'. (u, a, v) \<in> intra nest_cfg
        \<Longrightarrow> s \<in> \<lbrakk>ivl_ctx_sg_1 (Inl (u, c))\<rbrakk> \<Longrightarrow> s' \<in> edge_step a s
        \<Longrightarrow> s' \<in> \<lbrakk>ivl_ctx_sg_1 (Inl (v, c))\<rbrakk>"
    by (rule nest_1_dg.dg_ctx_act_edge)
next
  \<comment> \<open>ADMISS_TOTAL --- trivial, \<open>cs_context 1\<close> is a total function.\<close>
  show "\<And>u c s. \<exists>c'. admiss_exact (cs_context 1) u c s c'" by (simp add: admiss_exact_def)
next
  \<comment> \<open>CALL --- enter routed to the truncated call string.\<close>
  fix u dst pars args p cont c s c'
  assume ce: "(u, CallEdge dst pars args, FunctionEntry p, cont) \<in> calls nest_cfg"
    and sm: "s \<in> \<lbrakk>ivl_ctx_sg_1 (Inl (u, c))\<rbrakk>"
    and adm: "admiss_exact (cs_context 1) u c (call_enter nest_gs (CallEdge dst pars args) s) c'"
  show "call_enter nest_gs (CallEdge dst pars args) s \<in> \<lbrakk>ivl_ctx_sg_1 (Inl (FunctionEntry p, c'))\<rbrakk>"
    using adm ivl_ctx_sg_1_seed[OF ce sm] by (simp add: admiss_exact_def)
next
  \<comment> \<open>COMB --- return combine at the caller's own truncated context.\<close>
  fix cl dst pars args p cont c1 c2 s t es
  assume ce: "(cl, CallEdge dst pars args, FunctionEntry p, cont) \<in> calls nest_cfg"
    and sm: "s \<in> \<lbrakk>ivl_ctx_sg_1 (Inl (cl, c1))\<rbrakk>"
    and adm: "admiss_exact (cs_context 1) cl c1 es c2"
    and tm: "t \<in> \<lbrakk>ivl_ctx_sg_1 (Inl (FunctionResult p, c2))\<rbrakk>"
    and ces: "call_enter_store nest_gs nest_cfg cl s es"
  show "combine_collect nest_gs dst s t \<in> \<lbrakk>ivl_ctx_sg_1 (Inl (cont, c1))\<rbrakk>"
    using adm tm ivl_ctx_sg_1_comb[OF ce sm _ ces] by (simp add: admiss_exact_def)
qed

section \<open>Call-string-context-expanded analysis graph\<close>

definition nest_1_graph_config ::
  "(cfg_node list, gk_1, (ivl exec_dg_st, ivl exec_dg_st) dg_state, ivl exec_dg_st) analysis_graph_config" where
  "nest_1_graph_config =
    \<lparr> local_of = locals,
      route = (\<lambda>u ctx action d. cs_route 1 u ctx d action),
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
        String.explode x @ ''='' @ string_of_ivl (nest_lookup_exec_dg_st d x)) vars),
      format_return = (\<lambda>p ctx ret d.
        if nest_lookup_exec_dg_st d ret = ivl_top then []
        else [''ret='' @ string_of_ivl (nest_lookup_exec_dg_st d ret)]),
      show_global = (\<lambda>k vars s. [''(none)'']),
      show_global_key = (\<lambda>k. case k of Global1 \<Rightarrow> ''Global'' | Seed1 p ctx \<Rightarrow> ''Seed''),
      is_shared_global = (\<lambda>k. case k of Global1 \<Rightarrow> True | Seed1 _ _ \<Rightarrow> False),
      show_internal_globals = False,
      owner_of = String.explode o compiled_owner_of nest_pi nest_procs (STR ''main'') nest_main,
      cluster_label = (\<lambda>owner ctx.
        if owner = ''main'' \<and> ctx = [] then ''main / root context''
        else owner @ '' / call string='' @ ''['' @ join_source '', '' (map string_of_cfg_node ctx) @ '']''),
      source_text = Some (pretty_string_of_program nest_pi nest_procs nest_main []),
      node_annotation = (\<lambda>_. None)
    \<rparr>"

definition nest_1_contexts_for_pp :: "pp \<Rightarrow> cfg_node list list" where
  "nest_1_contexts_for_pp p =
    (let owner = compiled_owner_of nest_pi nest_procs (STR ''main'') nest_main p
     in if owner = (STR ''main'') then [[]]
        else if owner = (STR ''f'') then [[Statement 5], [Statement 6]]
        else [[Statement 2]])"

definition nest_1_local_graph_domain :: "(pp \<times> cfg_node list + gk_1) list" where
  "nest_1_local_graph_domain =
    contextual_graph_domain nest_cfg nest_1_contexts_for_pp"

definition nest_1_seed_keys :: "gk_1 list" where
  "nest_1_seed_keys =
     map (\<lambda>ctx. Seed1 (FunctionEntry (STR ''f'')) ctx) [[Statement 5], [Statement 6]]
     @ [Seed1 (FunctionEntry (STR ''g'')) [Statement 2]]"

definition nest_1_graph_domain :: "(pp \<times> cfg_node list + gk_1) list" where
  "nest_1_graph_domain =
    nest_1_local_graph_domain @ map Inr nest_1_seed_keys"

definition nest_1_graph :: "(cfg_node list, gk_1) analysis_graph" where
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

ML_val \<open>writeln (@{code nest_1_dot})\<close>

end

