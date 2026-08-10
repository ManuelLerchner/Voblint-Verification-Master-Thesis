theory Example_Sign_DG_CallString_K1
  imports
    "Voblint_Analysis.Sign_DG"
    "Voblint_Analysis.Sign_Exec"
    "Voblint_Analysis.Sign_Side_Soundness"
    "Voblint_Analysis.Exec_DG_Bridge"
    "Voblint_Formalization.Run_Analysis_Sound"
    "Voblint_Core.Routed_Context"
    "Voblint_Core.Activation_Backbone"
    "Voblint_Core.DG_Ctx_Activation"
    "Voblint_Core.Call_String_Context"
    "Voblint_Core.Solver_Menu"
    "Voblint_VIMP.VIMP_Notation"
begin

section \<open>A hand-witnessed 1-call-string context, routed by truncated call history\<close>

text \<open>
  Sign counterpart of the Interval \<open>Example_Interval_DG_CallString_K1\<close> example: same
  \<open>nest\<close> shape (\<open>main\<close> calls \<open>f\<close> from two distinct sites, \<open>f\<close> calls \<open>g\<close> from one site
  inside its own body), but with one positive and one non-positive argument so the Sign
  domain actually separates the two \<open>f\<close>-activations. \<open>TD_side_mono\<close> has no executable
  refinement in the vendored solver (only the widening/\<open>abort=False\<close> path does), so
  \<open>sigma\<close>/\<open>vars\<close> are hand-witnessed here rather than obtained by running a solver, in the
  style of \<open>projected_part_post_solution\<close> (\<open>Context_Refinement.thy\<close>).
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

abbreviation sign_nest_lookup_exec_dg_st :: "('a::bot) exec_dg_st \<Rightarrow> vname \<Rightarrow> 'a" where
  "sign_nest_lookup_exec_dg_st s x \<equiv> lookup_resolved_st_q s (location_of sign_nest_gs x)"

definition sign_nest_pi :: proc_table where "sign_nest_pi = prog_table sign_nest_program"
definition sign_nest_procs :: "pname list" where "sign_nest_procs = prog_procs sign_nest_program"
definition sign_nest_main :: "VIMP_Proc.com" where "sign_nest_main = prog_main sign_nest_program"

definition sign_nest_cfg :: cfg where
  "sign_nest_cfg = compile_prog sign_nest_pi sign_nest_procs (STR ''main'') sign_nest_main"

lemma sign_nest_entry: "cfg_entry sign_nest_cfg = FunctionEntry (STR ''main'')" by eval

lemma sign_nest_finE: "finite (intra sign_nest_cfg)"
  unfolding sign_nest_cfg_def using compile_prog_finite by simp
lemma sign_nest_finC: "finite (calls sign_nest_cfg)"
  unfolding sign_nest_cfg_def using compile_prog_finite by simp

text \<open>Same call-site shape as the Interval \<open>nest\<close> program (the literal arguments differ,
  the CFG does not): \<open>g\<close> is called once, from inside \<open>f\<close>, at the same source location
  regardless of which \<open>f\<close>-activation runs it; \<open>f\<close> is called twice from \<open>main\<close>.\<close>
lemma sign_nest_calls_shape:
  "\<forall>(u, ca, ce, cont) \<in> calls sign_nest_cfg.
     case ca of CallEdge dst pars args \<Rightarrow>
       (case ce of FunctionEntry p \<Rightarrow>
          (u = Statement 2 \<and> p = (STR ''g'') \<and> cont = Statement 3) \<or>
          (u = Statement 5 \<and> p = (STR ''f'') \<and> cont = Statement 6) \<or>
          (u = Statement 6 \<and> p = (STR ''f'') \<and> cont = Statement 7)
        | _ \<Rightarrow> True)"
  unfolding sign_nest_cfg_def by eval

lemma sign_nest_calls_unique_site:
  "\<forall>(u1, ca1, ce1, k1) \<in> calls sign_nest_cfg. \<forall>(u2, ca2, ce2, k2) \<in> calls sign_nest_cfg.
      u1 = u2 \<longrightarrow> ca1 = ca2 \<and> ce1 = ce2 \<and> k1 = k2"
  unfolding sign_nest_cfg_def by eval

subsection \<open>The Sign domain, executable and abstract\<close>

definition Spoly :: "(sign exec_dg_st, sign exec_dg_st) dg_spec" where
  "Spoly = unit_dg_spec_st_for sign_nest_gs (sign_tf_st_for sign_nest_gs) (sign_enter_st_for sign_nest_gs)"

abbreviation Sabs :: "(sign abs_state, sign abs_state) dg_spec" where
  "Sabs \<equiv> unit_dg_spec_for sign_nest_gs (sign_tf_for sign_nest_gs)"

lemmas sign_Hstep =
  unit_dg_Hstep_for[OF sign_tf_st_for_commute[folded fun_of_exec_dg_st_for_def]
    sign_tf_st_for_reduces]
lemmas sign_Henter = unit_dg_Henter_for[OF sign_enter_st_for_commute[folded fun_of_exec_dg_st_for_def]]
lemmas sign_Hcomb = unit_dg_Hcomb_for

subsection \<open>A call-string-keyed global-key type\<close>

datatype gk_1 = Global1 | Seed1 (seed1_pp: pp) (seed1_cs: "cfg_node list")

subsection \<open>The routed equation system and its computed solution\<close>

text \<open>Sign is a finite lattice, so the plain join update rule (\<open>TD_side_always_join_Interp\<close>)
  terminates on this loop-free program and reaches the true least fixpoint --- no widening or
  narrowing is invoked, matching the optimality precondition of the underlying solver theory.\<close>

definition sign_nest_1_eqs :: "(pp \<times> cfg_node list, gk_1, (sign exec_dg_st, sign exec_dg_st) dg_state) eqsT" where
  "sign_nest_1_eqs =
     side_cfg_T_eff_keyed_seed_dg intra_predecessor_list (\<lambda>_. Global1) (cs_route 1)
       (routed_cmb Spoly Global1) (routed_extra sign_nest_cfg Spoly Seed1 Global1)
       sign_nest_cfg Spoly bot cinit_sign_st (restrict_global_resolved_q cinit_sign_st)"

definition sign_nest_1_sol ::
  "(pp \<times> cfg_node list) set \<times> (pp \<times> cfg_node list + gk_1 \<Rightarrow> (sign exec_dg_st, sign exec_dg_st) dg_state)" where
  "sign_nest_1_sol = TD_side_always_join_Interp_solve sign_nest_1_eqs (cfg_exit sign_nest_cfg, [])"

lemma sign_nest_1_terminates:
  "TD_side_always_join_Interp_solve_c sign_nest_1_eqs (cfg_exit sign_nest_cfg, []) \<noteq> None"
  by eval

subsection \<open>Coverage\<close>

lemma entry_covered_1: "(cfg_entry sign_nest_cfg, []) \<in> fst sign_nest_1_sol"
  unfolding sign_nest_1_sol_def sign_nest_1_eqs_def sign_nest_entry by eval

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
  unfolding sign_nest_1_sol_def sign_nest_1_eqs_def by eval

lemma enter_callers_g_1:
  "\<forall>(p, ctx)\<in>fst sign_nest_1_sol.
     p = Statement 2 \<longrightarrow> ctx = [Statement 5] \<or> ctx = [Statement 6]"
  unfolding sign_nest_1_sol_def sign_nest_1_eqs_def by eval

lemma callee_covered_fpos_1: "(FunctionEntry (STR ''f''), [Statement 5]) \<in> fst sign_nest_1_sol"
  unfolding sign_nest_1_sol_def sign_nest_1_eqs_def by eval
lemma callee_covered_fneg_1: "(FunctionEntry (STR ''f''), [Statement 6]) \<in> fst sign_nest_1_sol"
  unfolding sign_nest_1_sol_def sign_nest_1_eqs_def by eval
lemma callee_covered_g_1: "(FunctionEntry (STR ''g''), [Statement 2]) \<in> fst sign_nest_1_sol"
  unfolding sign_nest_1_sol_def sign_nest_1_eqs_def by eval

lemma covered_ret6_1: "(Statement 6, []) \<in> fst sign_nest_1_sol"
  unfolding sign_nest_1_sol_def sign_nest_1_eqs_def by eval
lemma covered_ret7_1: "(Statement 7, []) \<in> fst sign_nest_1_sol"
  unfolding sign_nest_1_sol_def sign_nest_1_eqs_def by eval
lemma covered_ret3_fpos_1: "(Statement 3, [Statement 5]) \<in> fst sign_nest_1_sol"
  unfolding sign_nest_1_sol_def sign_nest_1_eqs_def by eval
lemma covered_ret3_fneg_1: "(Statement 3, [Statement 6]) \<in> fst sign_nest_1_sol"
  unfolding sign_nest_1_sol_def sign_nest_1_eqs_def by eval

lemma callee_exit_fpos_1: "(FunctionResult (STR ''f''), [Statement 5]) \<in> fst sign_nest_1_sol"
  unfolding sign_nest_1_sol_def sign_nest_1_eqs_def by eval
lemma callee_exit_fneg_1: "(FunctionResult (STR ''f''), [Statement 6]) \<in> fst sign_nest_1_sol"
  unfolding sign_nest_1_sol_def sign_nest_1_eqs_def by eval
lemma callee_exit_g_1: "(FunctionResult (STR ''g''), [Statement 2]) \<in> fst sign_nest_1_sol"
  unfolding sign_nest_1_sol_def sign_nest_1_eqs_def by eval

section \<open>Abstract transport of the routed solution\<close>

text \<open>The return combine and the enter transfer each commute componentwise with an
  arbitrary incoming global slot.\<close>

lemma dgs_combine_snd_commute_gen:
  "fun_of_exec_dg_st_for sign_nest_gs (snd (dgs_combine Spoly dst dc de g))
     = snd (dgs_combine Sabs dst (fun_of_exec_dg_st_for sign_nest_gs dc) (fun_of_exec_dg_st_for sign_nest_gs de) (fun_of_exec_dg_st_for sign_nest_gs g))"
proof -
  have step: "map_prod (fun_of_exec_dg_st_for sign_nest_gs) (fun_of_exec_dg_st_for sign_nest_gs)
                (dgs_combine (unit_dg_spec_st_for sign_nest_gs (sign_tf_st_for sign_nest_gs) (sign_enter_st_for sign_nest_gs)) dst dc de g)
              = dgs_combine Sabs dst (fun_of_exec_dg_st_for sign_nest_gs dc) (fun_of_exec_dg_st_for sign_nest_gs de) (fun_of_exec_dg_st_for sign_nest_gs g)"
    by (rule sign_Hcomb)
  have "fun_of_exec_dg_st_for sign_nest_gs (snd (dgs_combine (unit_dg_spec_st_for sign_nest_gs (sign_tf_st_for sign_nest_gs) (sign_enter_st_for sign_nest_gs)) dst dc de g))
      = snd (map_prod (fun_of_exec_dg_st_for sign_nest_gs) (fun_of_exec_dg_st_for sign_nest_gs)
               (dgs_combine (unit_dg_spec_st_for sign_nest_gs (sign_tf_st_for sign_nest_gs) (sign_enter_st_for sign_nest_gs)) dst dc de g))"
    by (metis snd_conv map_prod_simp surj_pair)
  also have "\<dots> = snd (dgs_combine Sabs dst (fun_of_exec_dg_st_for sign_nest_gs dc) (fun_of_exec_dg_st_for sign_nest_gs de) (fun_of_exec_dg_st_for sign_nest_gs g))"
    by (simp add: step)
  finally show ?thesis by (simp add: Spoly_def)
qed

lemma dgs_combine_fst_commute_gen:
  "fun_of_exec_dg_st_for sign_nest_gs (fst (dgs_combine Spoly dst dc de g))
     = fst (dgs_combine Sabs dst (fun_of_exec_dg_st_for sign_nest_gs dc) (fun_of_exec_dg_st_for sign_nest_gs de) (fun_of_exec_dg_st_for sign_nest_gs g))"
proof -
  have step: "map_prod (fun_of_exec_dg_st_for sign_nest_gs) (fun_of_exec_dg_st_for sign_nest_gs) (dgs_combine (unit_dg_spec_st_for sign_nest_gs (sign_tf_st_for sign_nest_gs) (sign_enter_st_for sign_nest_gs)) dst dc de g)
              = dgs_combine Sabs dst (fun_of_exec_dg_st_for sign_nest_gs dc) (fun_of_exec_dg_st_for sign_nest_gs de) (fun_of_exec_dg_st_for sign_nest_gs g)"
    by (rule sign_Hcomb)
  have "fun_of_exec_dg_st_for sign_nest_gs (fst (dgs_combine (unit_dg_spec_st_for sign_nest_gs (sign_tf_st_for sign_nest_gs) (sign_enter_st_for sign_nest_gs)) dst dc de g))
      = fst (map_prod (fun_of_exec_dg_st_for sign_nest_gs) (fun_of_exec_dg_st_for sign_nest_gs) (dgs_combine (unit_dg_spec_st_for sign_nest_gs (sign_tf_st_for sign_nest_gs) (sign_enter_st_for sign_nest_gs)) dst dc de g))"
    by (metis fst_conv map_prod_simp surj_pair)
  also have "\<dots> = fst (dgs_combine Sabs dst (fun_of_exec_dg_st_for sign_nest_gs dc) (fun_of_exec_dg_st_for sign_nest_gs de) (fun_of_exec_dg_st_for sign_nest_gs g))"
    by (simp add: step)
  finally show ?thesis by (simp add: Spoly_def)
qed

lemma dgs_enter_snd_commute_gen:
  "fun_of_exec_dg_st_for sign_nest_gs (snd (dgs_enter Spoly fs as d g))
     = snd (dgs_enter Sabs fs as (fun_of_exec_dg_st_for sign_nest_gs d) (fun_of_exec_dg_st_for sign_nest_gs g))"
proof -
  have step: "map_prod (fun_of_exec_dg_st_for sign_nest_gs) (fun_of_exec_dg_st_for sign_nest_gs) (dgs_enter (unit_dg_spec_st_for sign_nest_gs (sign_tf_st_for sign_nest_gs) (sign_enter_st_for sign_nest_gs)) fs as d g)
              = dgs_enter Sabs fs as (fun_of_exec_dg_st_for sign_nest_gs d) (fun_of_exec_dg_st_for sign_nest_gs g)"
    by (rule sign_Henter)
  have "fun_of_exec_dg_st_for sign_nest_gs (snd (dgs_enter (unit_dg_spec_st_for sign_nest_gs (sign_tf_st_for sign_nest_gs) (sign_enter_st_for sign_nest_gs)) fs as d g))
      = snd (map_prod (fun_of_exec_dg_st_for sign_nest_gs) (fun_of_exec_dg_st_for sign_nest_gs) (dgs_enter (unit_dg_spec_st_for sign_nest_gs (sign_tf_st_for sign_nest_gs) (sign_enter_st_for sign_nest_gs)) fs as d g))"
    by (metis snd_conv map_prod_simp surj_pair)
  also have "\<dots> = snd (dgs_enter Sabs fs as (fun_of_exec_dg_st_for sign_nest_gs d) (fun_of_exec_dg_st_for sign_nest_gs g))"
    by (simp add: step)
  finally show ?thesis by (simp add: Spoly_def)
qed

lemma dgs_enter_fst_commute_gen:
  "fun_of_exec_dg_st_for sign_nest_gs (fst (dgs_enter Spoly fs as d g))
     = fst (dgs_enter Sabs fs as (fun_of_exec_dg_st_for sign_nest_gs d) (fun_of_exec_dg_st_for sign_nest_gs g))"
proof -
  have step: "map_prod (fun_of_exec_dg_st_for sign_nest_gs) (fun_of_exec_dg_st_for sign_nest_gs) (dgs_enter (unit_dg_spec_st_for sign_nest_gs (sign_tf_st_for sign_nest_gs) (sign_enter_st_for sign_nest_gs)) fs as d g)
              = dgs_enter Sabs fs as (fun_of_exec_dg_st_for sign_nest_gs d) (fun_of_exec_dg_st_for sign_nest_gs g)"
    by (rule sign_Henter)
  have "fun_of_exec_dg_st_for sign_nest_gs (fst (dgs_enter (unit_dg_spec_st_for sign_nest_gs (sign_tf_st_for sign_nest_gs) (sign_enter_st_for sign_nest_gs)) fs as d g))
      = fst (map_prod (fun_of_exec_dg_st_for sign_nest_gs) (fun_of_exec_dg_st_for sign_nest_gs) (dgs_enter (unit_dg_spec_st_for sign_nest_gs (sign_tf_st_for sign_nest_gs) (sign_enter_st_for sign_nest_gs)) fs as d g))"
    by (metis fst_conv map_prod_simp surj_pair)
  also have "\<dots> = fst (dgs_enter Sabs fs as (fun_of_exec_dg_st_for sign_nest_gs d) (fun_of_exec_dg_st_for sign_nest_gs g))"
    by (simp add: step)
  finally show ?thesis by (simp add: Spoly_def)
qed

text \<open>\<open>cs_route\<close> ignores its data argument, so every \<open>Side\<close> key computed from it is
  literally the same term on the executable and the abstract carrier.\<close>

lemma dg_tree_st_commute_frame_read_1:
  "dg_tree_st_commute_for sign_nest_gs env
     (QueryG (Seed1 v ctx) (\<lambda>s. Answer (DG (globs s) bot)))
     (QueryG (Seed1 v ctx) (\<lambda>s. Answer (DG (globs s) bot)))"
  by (simp add: dg_tree_st_commute_for_def fun_of_dg_st_for_simps fun_of_exec_dg_st_for_bot o_def
                dep_aux_def bot_fun_def)

lemma dg_tree_st_commute_routed_cmb_1:
  "dg_tree_st_commute_for sign_nest_gs env (routed_cmb Spoly Global1 (cs_route 1) ctx ca cc ex)
                          (routed_cmb Sabs Global1 (cs_route 1) ctx ca cc ex)"
  unfolding routed_cmb_def Let_def
  by (cases ca)
     (simp_all add: dg_tree_st_commute_for_def fun_of_dg_st_for_simps fun_of_exec_dg_st_for_bot o_def
                    cs_route_def dgs_combine_fst_commute_gen dgs_combine_snd_commute_gen
                    dep_aux_def bot_fun_def fun_upd_apply fun_eq_iff)

lemma dg_tree_st_commute_routed_enter_pub_1:
  "dg_tree_st_commute_for sign_nest_gs env
     (with_call a (\<lambda>dst fs as. do {
        entry_state \<leftarrow> read_local (v, ctx);
        globals_state \<leftarrow> read_global Global1;
        publish_global Global1 (enter_global Spoly fs as (locals entry_state) (globs globals_state));
        publish_seed (Seed1 w (cs_route 1 v ctx (locals entry_state) a))
          (enter_local Spoly fs as (locals entry_state) (globs globals_state));
        answer_local bot
      }))
     (with_call a (\<lambda>dst fs as. do {
        entry_state \<leftarrow> read_local (v, ctx);
        globals_state \<leftarrow> read_global Global1;
        publish_global Global1 (enter_global Sabs fs as (locals entry_state) (globs globals_state));
        publish_seed (Seed1 w (cs_route 1 v ctx (locals entry_state) a))
          (enter_local Sabs fs as (locals entry_state) (globs globals_state));
        answer_local bot
      }))"
  by (cases a)
     (simp add: dg_tree_st_commute_for_def fun_of_dg_st_for_simps fun_of_exec_dg_st_for_bot o_def
                cs_route_def dgs_enter_fst_commute_gen dgs_enter_snd_commute_gen
                dep_aux_def bot_fun_def fun_upd_apply fun_eq_iff)

lemma hextra_commute_routed_1:
  "list_all2 (dg_tree_st_commute_for sign_nest_gs env)
     (routed_extra sign_nest_cfg Spoly Seed1 Global1 (cs_route 1) ctx w)
     (routed_extra sign_nest_cfg Sabs Seed1 Global1 (cs_route 1) ctx w)"
  unfolding routed_extra_def Let_def
  by (auto simp: list_all2_appendI list_all2_map1 list_all2_map2 list_all2_refl split_beta
                 dg_tree_st_commute_frame_read_1 dg_tree_st_commute_routed_enter_pub_1
           split: cfg_node.split)

lemma sign_nest_1_solve_dom:
  "TD_side_always_join_Interp.solve_dom TYPE(gk_1) TYPE((sign exec_dg_st, sign exec_dg_st) dg_state)
     sign_nest_1_eqs (cfg_exit sign_nest_cfg, [])"
  using sign_nest_1_terminates
  unfolding TD_side_always_join_Interp.term_equivalence
            TD_side_always_join_Interp.solve_c_dom_def
  by simp

lemma sign_nest_1_pp_st:
  "part_post_solution sign_nest_1_eqs (cfg_exit sign_nest_cfg, [])
     (snd sign_nest_1_sol) (fst sign_nest_1_sol)"
  using TD_side_always_join_Interp.partial_post_solution
          [OF sign_nest_1_solve_dom, of "fst sign_nest_1_sol" "snd sign_nest_1_sol"]
  unfolding sign_nest_1_sol_def by simp

theorem sign_nest_1_pp_abs:
  "part_post_solution
     (side_cfg_T_eff_keyed_seed_dg intra_predecessor_list (\<lambda>_. Global1) (cs_route 1)
        (routed_cmb Sabs Global1) (routed_extra sign_nest_cfg Sabs Seed1 Global1) sign_nest_cfg Sabs
        (fun_of_exec_dg_st_for sign_nest_gs (bot::sign exec_dg_st)) (fun_of_exec_dg_st_for sign_nest_gs cinit_sign_st) (fun_of_exec_dg_st_for sign_nest_gs (restrict_global_resolved_q cinit_sign_st)))
     (cfg_exit sign_nest_cfg, []) (fun_of_dg_st_for sign_nest_gs \<circ> snd sign_nest_1_sol) (fst sign_nest_1_sol)"
proof -
  have pp': "part_post_solution
       (side_cfg_T_eff_keyed_seed_dg intra_predecessor_list (\<lambda>_. Global1) (cs_route 1)
          (routed_cmb Spoly Global1) (routed_extra sign_nest_cfg Spoly Seed1 Global1) sign_nest_cfg Spoly
          bot cinit_sign_st (restrict_global_resolved_q cinit_sign_st))
       (cfg_exit sign_nest_cfg, []) (snd sign_nest_1_sol) (fst sign_nest_1_sol)"
    using sign_nest_1_pp_st unfolding sign_nest_1_eqs_def by simp
  have sign_Hstep_1:
    "map_prod (fun_of_exec_dg_st_for sign_nest_gs) (fun_of_exec_dg_st_for sign_nest_gs) (dg_spec_step Spoly a d g') =
       dg_spec_step Sabs a (fun_of_exec_dg_st_for sign_nest_gs d) (fun_of_exec_dg_st_for sign_nest_gs g')" for a d g'
    unfolding Spoly_def by (rule sign_Hstep)
  show ?thesis
    by (rule part_post_solution_seed_dg_st_to_abs_for
          [where gs = sign_nest_gs and pred_sel = intra_predecessor_list and gkey = "\<lambda>_. Global1"
             and route_st = "cs_route 1" and route_abs = "cs_route 1"
             and cmb_st = "routed_cmb Spoly Global1" and cmb_abs = "routed_cmb Sabs Global1"
             and extra_st = "routed_extra sign_nest_cfg Spoly Seed1 Global1"
             and extra_abs = "routed_extra sign_nest_cfg Sabs Seed1 Global1"
             and g = sign_nest_cfg and S_st = Spoly and S_abs = Sabs,
           OF sign_Hstep_1 cs_route_indep_of_data dg_tree_st_commute_routed_cmb_1
              hextra_commute_routed_1 pp'])
qed

section \<open>Activation-indexed collecting soundness for the 1-call-string-routed solution\<close>

abbreviation sigma_1 :: "pp \<times> cfg_node list + gk_1 \<Rightarrow> (sign abs_state, sign abs_state) dg_state" where
  "sigma_1 \<equiv> fun_of_dg_st_for sign_nest_gs \<circ> snd sign_nest_1_sol"

abbreviation gen_1_abs :: "(pp \<times> cfg_node list, gk_1, (sign abs_state, sign abs_state) dg_state) eqsT" where
  "gen_1_abs \<equiv> side_cfg_T_eff_keyed_seed_dg intra_predecessor_list (\<lambda>_. Global1) (cs_route 1)
       (routed_cmb Sabs Global1) (routed_extra sign_nest_cfg Sabs Seed1 Global1) sign_nest_cfg Sabs
       (fun_of_exec_dg_st_for sign_nest_gs (bot::sign exec_dg_st)) (fun_of_exec_dg_st_for sign_nest_gs cinit_sign_st) (fun_of_exec_dg_st_for sign_nest_gs (restrict_global_resolved_q cinit_sign_st))"

lemma pp_eq_bound_1:
  "(v, ctx) \<in> fst sign_nest_1_sol
     \<Longrightarrow> eq gen_1_abs (v, ctx) sigma_1 \<le> sigma_1 (Inl (v, ctx))"
  using sign_nest_1_pp_abs by simp

lemma side_acc_dg_ge_1: "acc \<le> side_acc_dg acc \<tau> ts"
proof (induction ts arbitrary: acc)
  case (Cons t ts)
  show ?case
    using Cons.IH[of "acc \<squnion> locals (traverse_rhs t \<tau>)"]
    by (simp add: le_supI1)
qed simp

definition sign_ctx_sg_1 :: "pp \<times> cfg_node list + gk_1 \<Rightarrow> sign abs_state" where
  "sign_ctx_sg_1 k =
     (case k of
        Inl (v, ctx) \<Rightarrow>
          (if (v, ctx) \<in> fst sign_nest_1_sol
           then combine_abs sign_nest_gs (locals (sigma_1 (Inl (v, ctx)))) (globs (sigma_1 (Inr Global1)))
           else bot)
      | Inr _ \<Rightarrow> bot)"

lemma sign_ctx_sg_1_covered:
  "(v, ctx) \<in> fst sign_nest_1_sol
   \<Longrightarrow> sign_ctx_sg_1 (Inl (v, ctx))
       = combine_abs sign_nest_gs (locals (sigma_1 (Inl (v, ctx)))) (globs (sigma_1 (Inr Global1)))"
  by (simp add: sign_ctx_sg_1_def)

lemma sign_ctx_sg_1_uncovered_empty:
  "(v, ctx) \<notin> fst sign_nest_1_sol \<Longrightarrow> \<lbrakk>sign_ctx_sg_1 (Inl (v, ctx))\<rbrakk> = {}"
  by (simp add: sign_ctx_sg_1_def gamma_state_bot)

lemma entry_locals_ge_s0d_1:
  assumes cov: "(cfg_entry sign_nest_cfg, []) \<in> fst sign_nest_1_sol"
  shows "fun_of_exec_dg_st_for sign_nest_gs cinit_sign_st \<le> locals (sigma_1 (Inl (cfg_entry sign_nest_cfg, [])))"
proof -
  have "fun_of_exec_dg_st_for sign_nest_gs cinit_sign_st
          \<le> locals (eq gen_1_abs (cfg_entry sign_nest_cfg, []) sigma_1)"
    by (simp add: eq_side_cfg_T_eff_keyed_seed_dg)
       (rule order_trans[OF _ side_acc_dg_ge_1], simp add: le_supI2)
  also have "\<dots> \<le> locals (sigma_1 (Inl (cfg_entry sign_nest_cfg, [])))"
    using pp_eq_bound_1[OF cov] by (simp add: less_eq_dg_state_def)
  finally show ?thesis .
qed

text \<open>\<open>sign_nest_program\<close> declares no globals, so \<^const>\<open>sign_nest_gs\<close> has no
  pre-registered \<^locale>\<open>sound_dg_spec\<close> interpretation for the diagonal sign spec:
  establish it once here, in this chain's shared ancestor, so every downstream
  \<open>dg_ctx_activation\<close>/\<open>routed_context\<close> interpretation on \<open>Sabs\<close> discharges its
  inherited step/combine/enter obligations automatically.\<close>

lemma sign_nest_reserved: "reserved_ret_var sign_nest_gs"
  unfolding reserved_ret_var_def by eval

interpretation sign_dg_for: sound_dg_spec Sabs "gamma_unit sign_nest_gs" sign_nest_gs
  by (rule sound_dg_spec_unit_for[OF sign_is_sound_transfer_for sign_nest_reserved])

interpretation sign_nest_1_dg: dg_ctx_activation Sabs sign_nest_gs sign_nest_cfg Global1 "cs_route 1"
    "routed_cmb Sabs Global1" "routed_extra sign_nest_cfg Sabs Seed1 Global1"
    "fun_of_exec_dg_st_for sign_nest_gs (bot::sign exec_dg_st)" "fun_of_exec_dg_st_for sign_nest_gs cinit_sign_st" "fun_of_exec_dg_st_for sign_nest_gs (restrict_global_resolved_q cinit_sign_st)"
    sigma_1 "fst sign_nest_1_sol" "(cfg_exit sign_nest_cfg, [])" sign_ctx_sg_1
proof unfold_locales
  show "finite (intra sign_nest_cfg)" by (rule sign_nest_finE)
next
  show "part_post_solution
          (side_cfg_T_eff_keyed_seed_dg intra_predecessor_list (\<lambda>_. Global1) (cs_route 1)
             (routed_cmb Sabs Global1) (routed_extra sign_nest_cfg Sabs Seed1 Global1) sign_nest_cfg Sabs
             (fun_of_exec_dg_st_for sign_nest_gs (bot::sign exec_dg_st)) (fun_of_exec_dg_st_for sign_nest_gs cinit_sign_st)
             (fun_of_exec_dg_st_for sign_nest_gs (restrict_global_resolved_q cinit_sign_st)))
          (cfg_exit sign_nest_cfg, []) sigma_1 (fst sign_nest_1_sol)"
    by (rule sign_nest_1_pp_abs)
next
  fix v ctx
  assume "(v, ctx) \<in> fst sign_nest_1_sol"
  thus "sign_ctx_sg_1 (Inl (v, ctx))
          = combine_abs sign_nest_gs (locals (sigma_1 (Inl (v, ctx)))) (globs (sigma_1 (Inr Global1)))"
    by (rule sign_ctx_sg_1_covered)
next
  fix v ctx
  assume "(v, ctx) \<notin> fst sign_nest_1_sol"
  thus "\<lbrakk>sign_ctx_sg_1 (Inl (v, ctx))\<rbrakk> = {}"
    by (rule sign_ctx_sg_1_uncovered_empty)
next
  fix u a v ctx
  assume "(u, ctx) \<in> fst sign_nest_1_sol" "(u, a, v) \<in> intra sign_nest_cfg"
  thus "(v, ctx) \<in> fst sign_nest_1_sol" by (rule sign_nest_fwd_closed_1)
qed

text \<open>\<open>cs_route 1\<close> and \<open>cs_enterc 1\<close> are the identical closed term \<open>take 1 (u # ctx)\<close>, so
  \<open>route_enterc_agree\<close> is bare reflexivity. \<open>g\<close>'s single call site is reached at either of
  \<open>f\<close>'s two activation contexts (\<open>enter_callers_g_1\<close>), but \<open>take 1\<close> erases that distinction
  before it reaches the goal, so \<open>CallFwd\<close> does not need to case-split on which one.\<close>

interpretation sign_nest_1_routed: routed_context Sabs sign_nest_gs sign_nest_cfg Global1 "cs_route 1"
    "fun_of_exec_dg_st_for sign_nest_gs (bot::sign exec_dg_st)" "fun_of_exec_dg_st_for sign_nest_gs cinit_sign_st" "fun_of_exec_dg_st_for sign_nest_gs (restrict_global_resolved_q cinit_sign_st)"
    sigma_1 "fst sign_nest_1_sol" "(cfg_exit sign_nest_cfg, [])" sign_ctx_sg_1
    Seed1 "cs_enterc 1"
proof (unfold_locales, goal_cases FinC SeedKey RouteAgree CallFwd CombFwd EnterAgree)
  case FinC
  show ?case by (rule sign_nest_finC)
next
  case (SeedKey p ctx)
  show ?case by simp
next
  case (RouteAgree u ctx dst pars args p cont s)
  show ?case by (rule cs_route_enterc_agree)
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
  note covCl = CombFwd(1) and ce = CombFwd(2)
  show ?case
    using ce covCl enter_callers_only_root_main_1 enter_callers_g_1
          covered_ret3_fpos_1 covered_ret3_fneg_1 covered_ret6_1 covered_ret7_1
          sign_nest_calls_shape
    by fastforce
next
  case (EnterAgree cl s es dst pars args p cont)
  note ces = EnterAgree(1) and ce = EnterAgree(2)
  show ?case
    using ces ce sign_nest_calls_unique_site unfolding call_enter_store_def by fastforce
qed

lemma sign_ctx_sg_1_seed:
  assumes "(u, CallEdge dst xs es, FunctionEntry p, cont) \<in> calls sign_nest_cfg"
    and "s \<in> \<lbrakk>sign_ctx_sg_1 (Inl (u, ctx))\<rbrakk>"
  shows "call_enter sign_nest_gs (CallEdge dst xs es) s
           \<in> \<lbrakk>sign_ctx_sg_1 (Inl (FunctionEntry p,
                 cs_enterc 1 u ctx (call_enter sign_nest_gs (CallEdge dst xs es) s)))\<rbrakk>"
  by (rule sign_nest_1_routed.routed_context_call[OF assms])

lemma sign_ctx_sg_1_comb:
  assumes "(cl, CallEdge dst pars args, FunctionEntry p, v) \<in> calls sign_nest_cfg"
    and "s \<in> \<lbrakk>sign_ctx_sg_1 (Inl (cl, c1))\<rbrakk>"
    and "t \<in> \<lbrakk>sign_ctx_sg_1 (Inl (FunctionResult p, cs_enterc 1 cl c1 es))\<rbrakk>"
    and "call_enter_store sign_nest_gs sign_nest_cfg cl s es"
  shows "combine_collect sign_nest_gs dst s t \<in> \<lbrakk>sign_ctx_sg_1 (Inl (v, c1))\<rbrakk>"
  by (rule sign_nest_1_routed.routed_context_comb[OF assms])

section \<open>The headline theorem: 1-call-string activation collecting soundness\<close>

lemma cinit_le_cinit_sign_st_1: "cinit_stores sign_nest_gs \<subseteq> \<lbrakk>fun_of_exec_dg_st_for sign_nest_gs cinit_sign_st\<rbrakk>"
  by (auto simp: cinit_stores_def gamma_state_def fun_of_exec_dg_st_for_def fun_of_st_cinit_sign_st_for)

theorem sign_nest_1_activation_collect_sound:
  "activation_collect sign_nest_gs (cs_enterc 1) [] (=) sign_nest_cfg (cinit_stores sign_nest_gs) v ctx
     \<subseteq> \<lbrakk>sign_ctx_sg_1 (Inl (v, ctx))\<rbrakk>"
proof (rule activation_collect_sound[where sg = sign_ctx_sg_1 and enterc = "cs_enterc 1"
        and seedc = "[]" and ctx_rep = "(=)"
        and S = "cinit_stores sign_nest_gs" and g = sign_nest_cfg and gs = sign_nest_gs])
  \<comment>\<open>ENTRY_G\<close>
  text \<open>Both the local seed \<open>s0d\<close> and the global seed \<open>s0g\<close> are \<open>cinit_sign_st\<close>'s own
    projections, so routing them back together through \<open>combine_abs\<close> exactly recovers
    \<open>s0d\<close>; the membership transports through \<open>gamma_unit_mono\<close> componentwise, needing
    the caller's local bound (\<open>entry_locals_ge_s0d_1\<close>) and the entry's global-seed
    bound (\<open>sign_nest_1_dg.pp_entry_s0g_bound\<close>) separately instead of one joined bound.\<close>
  fix s assume "s \<in> cinit_stores sign_nest_gs"
  hence "s \<in> \<lbrakk>fun_of_exec_dg_st_for sign_nest_gs cinit_sign_st\<rbrakk>" using cinit_le_cinit_sign_st_1 by blast
  also have "\<lbrakk>fun_of_exec_dg_st_for sign_nest_gs cinit_sign_st\<rbrakk>
        = gamma_unit sign_nest_gs (fun_of_exec_dg_st_for sign_nest_gs cinit_sign_st)
            (fun_of_exec_dg_st_for sign_nest_gs (restrict_global_resolved_q cinit_sign_st))"
    unfolding gamma_unit_def fun_of_exec_dg_st_for_def
    by (rule arg_cong[where f = gamma_state], rule ext)
       (simp add: combine_abs_def restrict_global_for_def)
  also have "\<dots> \<subseteq> gamma_unit sign_nest_gs (locals (sigma_1 (Inl (cfg_entry sign_nest_cfg, []))))
                   (globs (sigma_1 (Inr Global1)))"
    by (rule gamma_unit_mono[OF entry_locals_ge_s0d_1[OF entry_covered_1]
          sign_nest_1_dg.pp_entry_s0g_bound[OF entry_covered_1]])
  also have "\<dots> = \<lbrakk>sign_ctx_sg_1 (Inl (cfg_entry sign_nest_cfg, []))\<rbrakk>"
    unfolding sign_ctx_sg_1_covered[OF entry_covered_1] gamma_unit_def by (rule refl)
  finally show "s \<in> \<lbrakk>sign_ctx_sg_1 (Inl (cfg_entry sign_nest_cfg, []))\<rbrakk>" .
next
  \<comment>\<open>EDGE --- discharged generically off the post-solution by \<open>dg_ctx_activation\<close>.\<close>
  show "\<And>u a v c s s'. (u, a, v) \<in> intra sign_nest_cfg
        \<Longrightarrow> s \<in> \<lbrakk>sign_ctx_sg_1 (Inl (u, c))\<rbrakk> \<Longrightarrow> s' \<in> edge_step a s
        \<Longrightarrow> s' \<in> \<lbrakk>sign_ctx_sg_1 (Inl (v, c))\<rbrakk>"
    by (rule sign_nest_1_dg.dg_ctx_act_edge)
next
  \<comment>\<open>CALL --- enter routed to the truncated call string.\<close>
  show "\<And>u dst pars args p cont c s.
        (u, CallEdge dst pars args, FunctionEntry p, cont) \<in> calls sign_nest_cfg
        \<Longrightarrow> s \<in> \<lbrakk>sign_ctx_sg_1 (Inl (u, c))\<rbrakk>
        \<Longrightarrow> call_enter sign_nest_gs (CallEdge dst pars args) s
             \<in> \<lbrakk>sign_ctx_sg_1 (Inl (FunctionEntry p,
                    cs_enterc 1 u c (call_enter sign_nest_gs (CallEdge dst pars args) s)))\<rbrakk>"
    by (rule sign_ctx_sg_1_seed)
next
  \<comment>\<open>COMB --- return combine at the caller's own truncated context.\<close>
  show "\<And>cl dst pars args p cont c1 s t es.
        (cl, CallEdge dst pars args, FunctionEntry p, cont) \<in> calls sign_nest_cfg
        \<Longrightarrow> s \<in> \<lbrakk>sign_ctx_sg_1 (Inl (cl, c1))\<rbrakk>
        \<Longrightarrow> t \<in> \<lbrakk>sign_ctx_sg_1 (Inl (FunctionResult p, cs_enterc 1 cl c1 es))\<rbrakk>
        \<Longrightarrow> call_enter_store sign_nest_gs sign_nest_cfg cl s es
        \<Longrightarrow> combine_collect sign_nest_gs dst s t \<in> \<lbrakk>sign_ctx_sg_1 (Inl (cont, c1))\<rbrakk>"
    by (rule sign_ctx_sg_1_comb)
next
  \<comment>\<open>MONO --- trivial at exact match.\<close>
  show "\<And>c1 c2. c1 = c2 \<Longrightarrow> \<lbrakk>sign_ctx_sg_1 (Inl (v, c1))\<rbrakk> \<subseteq> \<lbrakk>sign_ctx_sg_1 (Inl (v, c2))\<rbrakk>"
    by simp
qed

section \<open>Executable check: the 1-call-string merge at \<open>g\<close>'s entry\<close>

text \<open>\<open>f\<close>'s two activations stay separated at their own entry (\<open>SPos\<close> from \<open>f(3)\<close>, \<open>SNeg\<close>
  from \<open>f(-10)\<close>), since their call sites at \<open>main\<close> differ. \<open>g\<close>'s single call site inside \<open>f\<close>
  is identical for both activations, so the 1-call-string context collapses them to one
  unknown, and their join lands at \<open>STop\<close> --- the merge a 2-call-string keeps separated.\<close>

value "sign_nest_lookup_exec_dg_st (locals (snd sign_nest_1_sol (Inl (FunctionEntry (STR ''g''), [Statement 2])))) (STR ''p'')"
value "sign_nest_lookup_exec_dg_st (locals (snd sign_nest_1_sol (Inl (FunctionEntry (STR ''f''), [Statement 5])))) (STR ''p'')"
value "sign_nest_lookup_exec_dg_st (locals (snd sign_nest_1_sol (Inl (FunctionEntry (STR ''f''), [Statement 6])))) (STR ''p'')"

end

