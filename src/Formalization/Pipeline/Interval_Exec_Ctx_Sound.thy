theory Interval_Exec_Ctx_Sound
  imports
    "Voblint_Analysis.Exec_DG_Bridge"
    "Voblint_Analysis.Interval_DG"
    "Voblint_Analysis.Interval_Exec_Sound"
    "Voblint_Analysis.Interval_Checks"
    "Voblint_Core.Routed_Context"
    "Voblint_Core.Solver_Menu"
    "Voblint_CFG.CFG_Prune"
    "Voblint_VIMP.VIMP_Notation"
    Run_Analysis_Sound
begin

section \<open>Generic executable entry-state context analysis for Interval\<close>

text \<open>
  Promotes the routed D/G machinery a fixed-program example (an entry-state
  acceptance case such as \<open>void p(a) { return a }\<close> / \<open>void main() { x := random();
  y := p(x) }\<close>) exercises to an executable analysis over an arbitrary
  \<^type>\<open>imp_prog\<close>: the context at a call is the entered abstract value of the
  callee's declared formals (\<^const>\<open>formals_route\<close>/\<^const>\<open>formals_context\<close>),
  never call-site history, so a call whose argument is unconstrained (e.g.
  \<open>random()\<close>) is analyzed once under one wide context rather than diverging over
  every concrete value. Mirrors \<^theory>\<open>Voblint_Analysis.Interval_Exec_Sound\<close>'s
  \<open>analyse_interval_td\<close> family and naming convention, adding one context
  dimension: every quantity here is keyed on \<^typ>\<open>pp \<times> ivl list\<close>, not \<^typ>\<open>pp\<close>
  alone.
\<close>

subsection \<open>Global key: real globals vs callee-entry seed slots\<close>

datatype gk = Global | Seed (seed_pp: pp) (seed_ivl: "ivl list")

subsection \<open>The routed context hooks, generic over the compiled program\<close>

text \<open>
  The one D/G spec every hook below shares.
\<close>

definition ectx_spec :: "(vname \<Rightarrow> bool) \<Rightarrow> (ivl exec_dg_st, ivl exec_dg_st) dg_spec" where
  "ectx_spec gs = unit_dg_spec_st_for gs (ivl_tf_st_for gs) (ivl_enter_st_for gs)"

text \<open>
  \<^const>\<open>formals_route\<close>/\<^const>\<open>formals_route_gen\<close> (\<^theory>\<open>Voblint_Core.Routed_Context\<close>)
  read the entered callee formals off an arbitrary \<^const>\<open>CallEdge\<close> generically,
  but only at the semantic \<^typ>\<open>'a abs_state\<close> carrier, not the executable
  \<^typ>\<open>'a exec_dg_st\<close> one this equation system solves over: the entered callee
  store is materialized here as an \<^const>\<open>dgs_enter\<close> result and read back through
  \<^const>\<open>lookup_resolved_st_q\<close>, then \<^const>\<open>formals_context\<close> -- the same generic
  per-variable projection -- reads off the formals.
\<close>

definition entry_state_entered ::
    "(vname \<Rightarrow> bool) \<Rightarrow> ivl exec_dg_st \<Rightarrow> call_action \<Rightarrow> ivl exec_dg_st" where
  "entry_state_entered gs d ca =
     (case ca of CallEdge dst fs as \<Rightarrow> snd (dgs_enter (ectx_spec gs) fs as d bot))"

definition entry_state_route :: "(vname \<Rightarrow> bool) \<Rightarrow> ivl exec_dg_st \<Rightarrow> call_action \<Rightarrow> ivl list" where
  "entry_state_route gs d ca =
     (case ca of CallEdge dst pars args \<Rightarrow>
        formals_context pars
          (\<lambda>x. lookup_resolved_st_q (entry_state_entered gs d ca) (location_of gs x)))"

definition entry_state_route_gen ::
    "(vname \<Rightarrow> bool) \<Rightarrow> pp \<Rightarrow> ivl list \<Rightarrow> ivl exec_dg_st \<Rightarrow> call_action \<Rightarrow> ivl list" where
  "entry_state_route_gen gs u ctx d ca = entry_state_route gs d ca"

subsection \<open>The routed equation system and its executable solution\<close>

definition entry_state_eqs ::
    "(vname \<Rightarrow> bool) \<Rightarrow> proc_table \<Rightarrow> pname list \<Rightarrow> pname \<Rightarrow> com
       \<Rightarrow> (pp \<times> ivl list, gk, (ivl exec_dg_st, ivl exec_dg_st) dg_state) eqsT" where
  "entry_state_eqs gs Pi ps mnm main =
     side_cfg_T_eff_keyed_seed_dg intra_predecessor_list (\<lambda>_. Global)
       (entry_state_route_gen gs)
       (routed_cmb (ectx_spec gs) Global)
       (routed_extra (compile_prog Pi ps mnm main) (ectx_spec gs) Seed Global)
       (compile_prog Pi ps mnm main) (ectx_spec gs) bot cinit_ivl_st
       (restrict_global_resolved_q cinit_ivl_st)"

definition entry_state_sol ::
    "(vname \<Rightarrow> bool) \<Rightarrow> proc_table \<Rightarrow> pname list \<Rightarrow> pname \<Rightarrow> com
       \<Rightarrow> (pp \<times> ivl list) set \<times> (pp \<times> ivl list + gk \<Rightarrow> (ivl exec_dg_st, ivl exec_dg_st) dg_state)" where
  "entry_state_sol gs Pi ps mnm main =
     TD_side_warrowing_apinis_Interp_solve (entry_state_eqs gs Pi ps mnm main)
       (cfg_exit (compile_prog Pi ps mnm main), [])"

definition entry_state_terminates ::
    "(vname \<Rightarrow> bool) \<Rightarrow> proc_table \<Rightarrow> pname list \<Rightarrow> pname \<Rightarrow> com \<Rightarrow> bool" where
  "entry_state_terminates gs Pi ps mnm main =
     TD_side_warrowing_apinis_Interp.solve_dom TYPE(gk) TYPE((ivl exec_dg_st, ivl exec_dg_st) dg_state)
       (entry_state_eqs gs Pi ps mnm main) (cfg_exit (compile_prog Pi ps mnm main), [])"

text \<open>
  Discharging termination by execution, exactly as
  \<open>analyse_interval_td_terminates_via_solve_c\<close> discharges
  \<^const>\<open>analyse_interval_td_terminates\<close>.
\<close>

lemma entry_state_terminates_via_solve_c:
  assumes "TD_side_warrowing_apinis_Interp_solve_c (entry_state_eqs gs Pi ps mnm main)
             (cfg_exit (compile_prog Pi ps mnm main), []) \<noteq> None"
  shows "entry_state_terminates gs Pi ps mnm main"
  unfolding entry_state_terminates_def TD_side_warrowing_apinis_Interp.term_equivalence
            TD_side_warrowing_apinis_Interp.solve_c_dom_def
  using assms by simp

subsection \<open>Whole-program convenience layer\<close>

definition entry_state_eqs_prog ::
    "(vname \<Rightarrow> bool) \<Rightarrow> pname \<Rightarrow> imp_prog
       \<Rightarrow> (pp \<times> ivl list, gk, (ivl exec_dg_st, ivl exec_dg_st) dg_state) eqsT" where
  "entry_state_eqs_prog gs mnm p = entry_state_eqs gs (prog_table p) (prog_procs p) mnm (prog_main p)"

definition entry_state_sol_prog ::
    "(vname \<Rightarrow> bool) \<Rightarrow> pname \<Rightarrow> imp_prog
       \<Rightarrow> (pp \<times> ivl list) set \<times> (pp \<times> ivl list + gk \<Rightarrow> (ivl exec_dg_st, ivl exec_dg_st) dg_state)" where
  "entry_state_sol_prog gs mnm p = entry_state_sol gs (prog_table p) (prog_procs p) mnm (prog_main p)"

definition entry_state_terminates_prog :: "(vname \<Rightarrow> bool) \<Rightarrow> pname \<Rightarrow> imp_prog \<Rightarrow> bool" where
  "entry_state_terminates_prog gs mnm p =
     entry_state_terminates gs (prog_table p) (prog_procs p) mnm (prog_main p)"

lemma entry_state_terminates_prog_via_solve_c:
  assumes "TD_side_warrowing_apinis_Interp_solve_c
             (entry_state_eqs_prog gs mnm p)
             (cfg_exit (compile_prog (prog_table p) (prog_procs p) mnm (prog_main p)), []) \<noteq> None"
  shows "entry_state_terminates_prog gs mnm p"
  using assms
  unfolding entry_state_terminates_prog_def entry_state_eqs_prog_def
  by (rule entry_state_terminates_via_solve_c)

section \<open>Route consistency and the abstract transport of the executable solution\<close>

text \<open>
  Mirrors an entry-state acceptance example's \<open>Sound\<close> theory, generalized from one
  fixed compiled program to an arbitrary one: nothing in that argument used the
  example's concrete shape, only the generic commutation facts
  \<open>ivl_Henter_for\<close>/\<open>ivl_Hcomb_for\<close>/\<open>ivl_Hstep_for\<close>, so every lemma
  below repeats \<open>gs Pi ps mnm main\<close> as free variables exactly as
  \<^theory>\<open>Voblint_Analysis.Interval_Exec_Sound\<close>'s own theorems do.
\<close>

subsection \<open>The abstract routed hooks\<close>

text \<open>
  Classifier-parametric commutation mirrors, generic in \<open>gs\<close>: same aliases the
  entry-state example's own base theory defines, not tied to any one \<open>gs\<close>.
\<close>

lemmas ivl_Hstep_for =
  unit_dg_Hstep_for[OF ivl_tf_st_for_commute[folded fun_of_exec_dg_st_for_def]
    ivl_tf_st_for_reduces]

lemmas ivl_Henter_for =
  unit_dg_Henter_for[OF ivl_enter_st_for_commute[folded fun_of_exec_dg_st_for_def]]

lemmas ivl_Hcomb_for = unit_dg_Hcomb_for

definition ectx_abs_spec :: "(vname \<Rightarrow> bool) \<Rightarrow> (ivl abs_state, ivl abs_state) dg_spec" where
  "ectx_abs_spec gs = unit_dg_spec_for gs (ivl_tf_for gs)"

definition entered_state_abs :: "(vname \<Rightarrow> bool) \<Rightarrow> ivl abs_state \<Rightarrow> call_action \<Rightarrow> ivl abs_state" where
  "entered_state_abs gs d ca =
     (case ca of CallEdge dst fs as \<Rightarrow> snd (dgs_enter (ectx_abs_spec gs) fs as d bot))"

definition entry_state_route_abs :: "(vname \<Rightarrow> bool) \<Rightarrow> ivl abs_state \<Rightarrow> call_action \<Rightarrow> ivl list" where
  "entry_state_route_abs gs d ca =
     (case ca of CallEdge dst pars args \<Rightarrow> formals_context pars (entered_state_abs gs d ca))"

definition entry_state_route_abs_gen ::
    "(vname \<Rightarrow> bool) \<Rightarrow> pp \<Rightarrow> ivl list \<Rightarrow> ivl abs_state \<Rightarrow> call_action \<Rightarrow> ivl list" where
  "entry_state_route_abs_gen gs u ctx d ca = entry_state_route_abs gs d ca"

subsection \<open>The route-consistency core\<close>

lemma entry_state_entered_commute:
  "fun_of_exec_dg_st_for gs (entry_state_entered gs s ca)
     = entered_state_abs gs (fun_of_exec_dg_st_for gs s) ca"
proof (cases ca)
  case (CallEdge dst fs as)
  have enter: "map_prod (fun_of_exec_dg_st_for gs) (fun_of_exec_dg_st_for gs)
                 (dgs_enter (ectx_spec gs) fs as s bot)
               = dgs_enter (ectx_abs_spec gs) fs as (fun_of_exec_dg_st_for gs s) (fun_of_exec_dg_st_for gs bot)"
    by (simp add: ectx_spec_def ectx_abs_spec_def ivl_Henter_for)
  have "fun_of_exec_dg_st_for gs (snd (dgs_enter (ectx_spec gs) fs as s bot))
      = snd (map_prod (fun_of_exec_dg_st_for gs) (fun_of_exec_dg_st_for gs)
               (dgs_enter (ectx_spec gs) fs as s bot))"
    by (metis snd_conv map_prod_simp surj_pair)
  also have "\<dots> = snd (dgs_enter (ectx_abs_spec gs) fs as (fun_of_exec_dg_st_for gs s) (fun_of_exec_dg_st_for gs bot))"
    by (simp add: enter)
  finally show ?thesis
    using CallEdge
    by (simp add: entry_state_entered_def entered_state_abs_def ectx_spec_def
                  fun_of_exec_dg_st_for_bot bot_fun_def)
qed

lemma entry_state_route_commute:
  "entry_state_route_abs gs (fun_of_exec_dg_st_for gs s) ca = entry_state_route gs s ca"
proof (cases ca)
  case (CallEdge dst pars args)
  have "entry_state_route_abs gs (fun_of_exec_dg_st_for gs s) ca
      = formals_context pars (entered_state_abs gs (fun_of_exec_dg_st_for gs s) ca)"
    using CallEdge by (simp add: entry_state_route_abs_def)
  also have "\<dots> = formals_context pars (fun_of_exec_dg_st_for gs (entry_state_entered gs s ca))"
    by (simp add: entry_state_entered_commute)
  also have "\<dots> = entry_state_route gs s ca"
    using CallEdge
    by (simp add: entry_state_route_def formals_context_def fun_of_exec_dg_st_for_def
                  fun_of_resolved_st_q_for_def)
  finally show ?thesis .
qed

lemma entry_state_route_commute_gen:
  "entry_state_route_gen gs u ctx s ca = entry_state_route_abs_gen gs u ctx (fun_of_exec_dg_st_for gs s) ca"
  by (simp add: entry_state_route_gen_def entry_state_route_abs_gen_def entry_state_route_commute)

subsection \<open>Per-tree transport commutation\<close>

lemma dg_tree_st_commute_frame_read:
  "dg_tree_st_commute_for gs env
     (QueryG (Seed v ctx) (\<lambda>s. Answer (DG (globs s) bot)))
     (QueryG (Seed v ctx) (\<lambda>s. Answer (DG (globs s) bot)))"
  by (simp add: dg_tree_st_commute_for_def fun_of_dg_st_for_simps fun_of_exec_dg_st_for_bot o_def
                dep_aux_def bot_fun_def)

lemma dgs_combine_snd_commute_gen:
  "fun_of_exec_dg_st_for gs (snd (dgs_combine (ectx_spec gs) dst dc de g'))
     = snd (dgs_combine (ectx_abs_spec gs) dst (fun_of_exec_dg_st_for gs dc) (fun_of_exec_dg_st_for gs de)
             (fun_of_exec_dg_st_for gs g'))"
proof -
  have step: "map_prod (fun_of_exec_dg_st_for gs) (fun_of_exec_dg_st_for gs)
                (dgs_combine (ectx_spec gs) dst dc de g')
              = dgs_combine (ectx_abs_spec gs) dst (fun_of_exec_dg_st_for gs dc)
                  (fun_of_exec_dg_st_for gs de) (fun_of_exec_dg_st_for gs g')"
    by (simp add: ectx_spec_def ectx_abs_spec_def ivl_Hcomb_for)
  have "fun_of_exec_dg_st_for gs (snd (dgs_combine (ectx_spec gs) dst dc de g'))
      = snd (map_prod (fun_of_exec_dg_st_for gs) (fun_of_exec_dg_st_for gs)
               (dgs_combine (ectx_spec gs) dst dc de g'))"
    by (metis snd_conv map_prod_simp surj_pair)
  also have "\<dots> = snd (dgs_combine (ectx_abs_spec gs) dst (fun_of_exec_dg_st_for gs dc)
                    (fun_of_exec_dg_st_for gs de) (fun_of_exec_dg_st_for gs g'))"
    by (simp add: step)
  finally show ?thesis by (simp add: ectx_spec_def)
qed

lemma dgs_combine_fst_commute_gen:
  "fun_of_exec_dg_st_for gs (fst (dgs_combine (ectx_spec gs) dst dc de g'))
     = fst (dgs_combine (ectx_abs_spec gs) dst (fun_of_exec_dg_st_for gs dc) (fun_of_exec_dg_st_for gs de)
             (fun_of_exec_dg_st_for gs g'))"
proof -
  have step: "map_prod (fun_of_exec_dg_st_for gs) (fun_of_exec_dg_st_for gs)
                (dgs_combine (ectx_spec gs) dst dc de g')
              = dgs_combine (ectx_abs_spec gs) dst (fun_of_exec_dg_st_for gs dc)
                  (fun_of_exec_dg_st_for gs de) (fun_of_exec_dg_st_for gs g')"
    by (simp add: ectx_spec_def ectx_abs_spec_def ivl_Hcomb_for)
  have "fun_of_exec_dg_st_for gs (fst (dgs_combine (ectx_spec gs) dst dc de g'))
      = fst (map_prod (fun_of_exec_dg_st_for gs) (fun_of_exec_dg_st_for gs)
               (dgs_combine (ectx_spec gs) dst dc de g'))"
    by (metis fst_conv map_prod_simp surj_pair)
  also have "\<dots> = fst (dgs_combine (ectx_abs_spec gs) dst (fun_of_exec_dg_st_for gs dc)
                    (fun_of_exec_dg_st_for gs de) (fun_of_exec_dg_st_for gs g'))"
    by (simp add: step)
  finally show ?thesis by (simp add: ectx_spec_def)
qed

lemma dgs_enter_snd_commute_gen:
  "fun_of_exec_dg_st_for gs (snd (dgs_enter (ectx_spec gs) fs as d g'))
     = snd (dgs_enter (ectx_abs_spec gs) fs as (fun_of_exec_dg_st_for gs d) (fun_of_exec_dg_st_for gs g'))"
proof -
  have step: "map_prod (fun_of_exec_dg_st_for gs) (fun_of_exec_dg_st_for gs)
                (dgs_enter (ectx_spec gs) fs as d g')
              = dgs_enter (ectx_abs_spec gs) fs as (fun_of_exec_dg_st_for gs d) (fun_of_exec_dg_st_for gs g')"
    by (simp add: ectx_spec_def ectx_abs_spec_def ivl_Henter_for)
  have "fun_of_exec_dg_st_for gs (snd (dgs_enter (ectx_spec gs) fs as d g'))
      = snd (map_prod (fun_of_exec_dg_st_for gs) (fun_of_exec_dg_st_for gs)
               (dgs_enter (ectx_spec gs) fs as d g'))"
    by (metis snd_conv map_prod_simp surj_pair)
  also have "\<dots> = snd (dgs_enter (ectx_abs_spec gs) fs as (fun_of_exec_dg_st_for gs d) (fun_of_exec_dg_st_for gs g'))"
    by (simp add: step)
  finally show ?thesis by (simp add: ectx_spec_def)
qed

lemma dgs_enter_fst_commute_gen:
  "fun_of_exec_dg_st_for gs (fst (dgs_enter (ectx_spec gs) fs as d g'))
     = fst (dgs_enter (ectx_abs_spec gs) fs as (fun_of_exec_dg_st_for gs d) (fun_of_exec_dg_st_for gs g'))"
proof -
  have step: "map_prod (fun_of_exec_dg_st_for gs) (fun_of_exec_dg_st_for gs)
                (dgs_enter (ectx_spec gs) fs as d g')
              = dgs_enter (ectx_abs_spec gs) fs as (fun_of_exec_dg_st_for gs d) (fun_of_exec_dg_st_for gs g')"
    by (simp add: ectx_spec_def ectx_abs_spec_def ivl_Henter_for)
  have "fun_of_exec_dg_st_for gs (fst (dgs_enter (ectx_spec gs) fs as d g'))
      = fst (map_prod (fun_of_exec_dg_st_for gs) (fun_of_exec_dg_st_for gs)
               (dgs_enter (ectx_spec gs) fs as d g'))"
    by (metis fst_conv map_prod_simp surj_pair)
  also have "\<dots> = fst (dgs_enter (ectx_abs_spec gs) fs as (fun_of_exec_dg_st_for gs d) (fun_of_exec_dg_st_for gs g'))"
    by (simp add: step)
  finally show ?thesis by (simp add: ectx_spec_def)
qed

lemma dg_tree_st_commute_routed_cmb:
  "dg_tree_st_commute_for gs env
     (routed_cmb (ectx_spec gs) Global (entry_state_route_gen gs) ctx ca cc ex)
     (routed_cmb (ectx_abs_spec gs) Global (entry_state_route_abs_gen gs) ctx ca cc ex)"
  unfolding routed_cmb_def entry_state_route_gen_def entry_state_route_abs_gen_def Let_def
  by (cases ca)
     (simp_all add: dg_tree_st_commute_for_def fun_of_dg_st_for_simps fun_of_exec_dg_st_for_bot o_def
                    entry_state_route_commute dgs_combine_fst_commute_gen dgs_combine_snd_commute_gen
                    dep_aux_def bot_fun_def fun_upd_apply fun_eq_iff)

lemma dg_tree_st_commute_routed_enter_pub:
  "dg_tree_st_commute_for gs env
     (with_call a (\<lambda>dst fs as. do {
        entry_state \<leftarrow> read_local (v, ctx);
        globals_state \<leftarrow> read_global Global;
        publish_global Global (enter_global (ectx_spec gs) fs as (locals entry_state) (globs globals_state));
        publish_seed (Seed w (entry_state_route_gen gs v ctx (locals entry_state) a))
          (enter_local (ectx_spec gs) fs as (locals entry_state) (globs globals_state));
        answer_local bot
      }))
     (with_call a (\<lambda>dst fs as. do {
        entry_state \<leftarrow> read_local (v, ctx);
        globals_state \<leftarrow> read_global Global;
        publish_global Global (enter_global (ectx_abs_spec gs) fs as (locals entry_state) (globs globals_state));
        publish_seed (Seed w (entry_state_route_abs_gen gs v ctx (locals entry_state) a))
          (enter_local (ectx_abs_spec gs) fs as (locals entry_state) (globs globals_state));
        answer_local bot
      }))"
  unfolding entry_state_route_gen_def entry_state_route_abs_gen_def
  by (cases a)
     (simp add: dg_tree_st_commute_for_def fun_of_dg_st_for_simps fun_of_exec_dg_st_for_bot o_def
                entry_state_route_commute dgs_enter_fst_commute_gen dgs_enter_snd_commute_gen
                dep_aux_def bot_fun_def fun_upd_apply fun_eq_iff)

lemma hextra_commute_routed:
  "list_all2 (dg_tree_st_commute_for gs env)
     (routed_extra (compile_prog Pi ps mnm main) (ectx_spec gs) Seed Global (entry_state_route_gen gs) ctx w)
     (routed_extra (compile_prog Pi ps mnm main) (ectx_abs_spec gs) Seed Global
        (entry_state_route_abs_gen gs) ctx w)"
  unfolding routed_extra_def Let_def
  by (auto simp: list_all2_appendI list_all2_map1 list_all2_map2 list_all2_refl split_beta
                 dg_tree_st_commute_frame_read dg_tree_st_commute_routed_enter_pub
           split: cfg_node.split)

subsection \<open>The certified executable post-solution, generic per compiled program\<close>

context
  fixes gs :: "vname \<Rightarrow> bool" and Pi :: proc_table and ps :: "pname list" and mnm :: pname and main :: com
  assumes solves: "entry_state_terminates gs Pi ps mnm main"
begin

lemma entry_state_solve_dom:
  "TD_side_warrowing_apinis_Interp.solve_dom TYPE(gk) TYPE((ivl exec_dg_st, ivl exec_dg_st) dg_state)
     (entry_state_eqs gs Pi ps mnm main) (cfg_exit (compile_prog Pi ps mnm main), [])"
  using solves
  unfolding entry_state_terminates_def TD_side_warrowing_apinis_Interp.term_equivalence
            TD_side_warrowing_apinis_Interp.solve_c_dom_def
  by simp

lemma entry_state_pp_st:
  "part_post_solution (entry_state_eqs gs Pi ps mnm main) (cfg_exit (compile_prog Pi ps mnm main), [])
     (snd (entry_state_sol gs Pi ps mnm main)) (fst (entry_state_sol gs Pi ps mnm main))"
  using TD_side_warrowing_apinis_Interp.partial_post_solution
          [OF entry_state_solve_dom, of "fst (entry_state_sol gs Pi ps mnm main)"
             "snd (entry_state_sol gs Pi ps mnm main)"]
  unfolding entry_state_sol_def by simp

theorem entry_state_pp_abs:
  "part_post_solution
     (side_cfg_T_eff_keyed_seed_dg intra_predecessor_list (\<lambda>_. Global) (entry_state_route_abs_gen gs)
        (routed_cmb (ectx_abs_spec gs) Global)
        (routed_extra (compile_prog Pi ps mnm main) (ectx_abs_spec gs) Seed Global)
        (compile_prog Pi ps mnm main) (ectx_abs_spec gs)
        (fun_of_exec_dg_st_for gs (bot::ivl exec_dg_st)) (fun_of_exec_dg_st_for gs cinit_ivl_st)
        (fun_of_exec_dg_st_for gs (restrict_global_resolved_q cinit_ivl_st)))
     (cfg_exit (compile_prog Pi ps mnm main), [])
     (fun_of_dg_st_for gs \<circ> snd (entry_state_sol gs Pi ps mnm main)) (fst (entry_state_sol gs Pi ps mnm main))"
proof -
  have pp': "part_post_solution
       (side_cfg_T_eff_keyed_seed_dg intra_predecessor_list (\<lambda>_. Global) (entry_state_route_gen gs)
          (routed_cmb (ectx_spec gs) Global)
          (routed_extra (compile_prog Pi ps mnm main) (ectx_spec gs) Seed Global)
          (compile_prog Pi ps mnm main) (ectx_spec gs) bot cinit_ivl_st
          (restrict_global_resolved_q cinit_ivl_st))
       (cfg_exit (compile_prog Pi ps mnm main), [])
       (snd (entry_state_sol gs Pi ps mnm main)) (fst (entry_state_sol gs Pi ps mnm main))"
    using entry_state_pp_st unfolding entry_state_eqs_def by simp
  have ivl_Hstep_ctx:
    "map_prod (fun_of_exec_dg_st_for gs) (fun_of_exec_dg_st_for gs) (dg_spec_step (ectx_spec gs) a d g') =
       dg_spec_step (ectx_abs_spec gs) a (fun_of_exec_dg_st_for gs d) (fun_of_exec_dg_st_for gs g')" for a d g'
    unfolding ectx_spec_def ectx_abs_spec_def by (rule ivl_Hstep_for)
  show ?thesis
    by (rule part_post_solution_seed_dg_st_to_abs_for
          [where gs = gs and pred_sel = intra_predecessor_list and gkey = "\<lambda>_. Global"
             and route_st = "entry_state_route_gen gs" and route_abs = "entry_state_route_abs_gen gs"
             and cmb_st = "routed_cmb (ectx_spec gs) Global" and cmb_abs = "routed_cmb (ectx_abs_spec gs) Global"
             and extra_st = "routed_extra (compile_prog Pi ps mnm main) (ectx_spec gs) Seed Global"
             and extra_abs = "routed_extra (compile_prog Pi ps mnm main) (ectx_abs_spec gs) Seed Global"
             and g = "compile_prog Pi ps mnm main" and S_st = "ectx_spec gs" and S_abs = "ectx_abs_spec gs",
           OF ivl_Hstep_ctx entry_state_route_commute_gen dg_tree_st_commute_routed_cmb
              hextra_commute_routed pp'])
qed

end

section \<open>Activation-indexed collecting soundness, generic per compiled program\<close>

text \<open>
  Mirrors \<open>Example_Interval_DG_EntryState_Collect\<close>, generalized the same way
  \<open>Example_Interval_DG_EntryState_Sound\<close> was: the trace-semantic context function
  \<open>entry_state_enterc\<close> ignores its concrete-store argument and instead
  recomputes the routed value the executable solver already produced, using
  \<^const>\<open>call_action_at_call_site\<close> to resolve the one call at a node --
  \<open>compile_prog_calls_source_unique\<close> is what makes that resolution unambiguous
  for \<open>any\<close> \<^const>\<open>compile_prog\<close> output, not just the acceptance example's one
  call site.

  Four more obligations are properties of the \<open>solved\<close> system -- which keys the
  executable solver actually covers, given its own seed/routing/query behavior --
  not of routing ambiguity. \<open>compile_prog_calls_source_unique\<close> does not
  bear on them, and no generic dependency-closure theorem for the keyed D/G solver
  exists yet in this development (the analogous fact for the \<open>flat\<close>, unkeyed
  solver, \<open>side_cone_in_vars_eff_cone\<close>, does not transfer to
  \<^const>\<open>side_cfg_T_eff_keyed_seed_dg\<close>). They are carried here the same way
  \<^const>\<open>entry_state_terminates\<close> already is: as \<open>by eval\<close>-checkable hypotheses on
  a concrete, terminated solve, not as a hidden singleton- or exact-entry-style
  premise. Closing that gap with a proved dependency-closure theorem is future
  work, not required by this milestone.
\<close>

text \<open>
  Executable twins of the context's own \<open>entry_state_sigma_abs\<close>/\<open>entry_state_sg\<close>
  (below), defined here before that \<open>context\<close> so their equations are
  unconditional. Neither reads anything but \<^const>\<open>entry_state_sol\<close>: none of
  the context's soundness obligations (\<open>wf\<close>, \<open>solves\<close>, \<open>entry_cov\<close>, \<open>fwd_ok\<close>,
  \<open>call_fwd_ok\<close>, \<open>comb_fwd_ok\<close>) are needed to compute them, but the code
  generator cannot discharge those obligations as a runtime side-condition,
  so the context-local names -- kept, unchanged in shape, for the soundness
  development below -- are simply defined as aliases of these.
\<close>

definition entry_state_sigma_abs_exec ::
    "(vname \<Rightarrow> bool) \<Rightarrow> proc_table \<Rightarrow> pname list \<Rightarrow> pname \<Rightarrow> com
       \<Rightarrow> pp \<times> ivl list + gk \<Rightarrow> (ivl abs_state, ivl abs_state) dg_state" where
  "entry_state_sigma_abs_exec gs Pi ps mnm main =
     fun_of_dg_st_for gs \<circ> snd (entry_state_sol gs Pi ps mnm main)"

definition entry_state_sg_exec ::
    "(vname \<Rightarrow> bool) \<Rightarrow> proc_table \<Rightarrow> pname list \<Rightarrow> pname \<Rightarrow> com
       \<Rightarrow> pp \<times> ivl list + gk \<Rightarrow> ivl abs_state" where
  "entry_state_sg_exec gs Pi ps mnm main k =
     (case k of
        Inl (v, ctx) \<Rightarrow>
          (if (v, ctx) \<in> fst (entry_state_sol gs Pi ps mnm main)
           then combine_abs gs (locals (entry_state_sigma_abs_exec gs Pi ps mnm main (Inl (v, ctx))))
                  (globs (entry_state_sigma_abs_exec gs Pi ps mnm main (Inr Global)))
           else bot)
      | Inr _ \<Rightarrow> bot)"

context
  fixes gs :: "vname \<Rightarrow> bool" and Pi :: proc_table and ps :: "pname list" and mnm :: pname and main :: com
  assumes wf: "wf_compile_input gs Pi ps mnm main"
    and solves: "entry_state_terminates gs Pi ps mnm main"
    and entry_cov: "(cfg_entry (compile_prog Pi ps mnm main), []) \<in> fst (entry_state_sol gs Pi ps mnm main)"
    and fwd_ok: "\<And>u a v ctx. (u, ctx) \<in> fst (entry_state_sol gs Pi ps mnm main)
                   \<Longrightarrow> (u, a, v) \<in> intra (compile_prog Pi ps mnm main)
                   \<Longrightarrow> (v, ctx) \<in> fst (entry_state_sol gs Pi ps mnm main)"
    and call_fwd_ok: "\<And>u ctx dst pars args p cont.
        (u, ctx) \<in> fst (entry_state_sol gs Pi ps mnm main)
        \<Longrightarrow> (u, CallEdge dst pars args, FunctionEntry p, cont) \<in> calls (compile_prog Pi ps mnm main)
        \<Longrightarrow> (FunctionEntry p,
              entry_state_route_abs_gen gs u ctx
                (locals ((fun_of_dg_st_for gs \<circ> snd (entry_state_sol gs Pi ps mnm main)) (Inl (u, ctx))))
                (CallEdge dst pars args))
            \<in> fst (entry_state_sol gs Pi ps mnm main)"
    and comb_fwd_ok: "\<And>cl c1 dst pars args p cont.
        (cl, c1) \<in> fst (entry_state_sol gs Pi ps mnm main)
        \<Longrightarrow> (cl, CallEdge dst pars args, FunctionEntry p, cont) \<in> calls (compile_prog Pi ps mnm main)
        \<Longrightarrow> (cont, c1) \<in> fst (entry_state_sol gs Pi ps mnm main)"
begin

subsection \<open>The semantic solution projection\<close>

definition entry_state_sigma_abs ::
    "pp \<times> ivl list + gk \<Rightarrow> (ivl abs_state, ivl abs_state) dg_state" where
  "entry_state_sigma_abs = entry_state_sigma_abs_exec gs Pi ps mnm main"

definition entry_state_sg :: "pp \<times> ivl list + gk \<Rightarrow> ivl abs_state" where
  "entry_state_sg = entry_state_sg_exec gs Pi ps mnm main"

text \<open>
  The trace-semantic context function: ignores its store argument entirely and
  recomputes the routed value from the caller's own solved abstract state, using
  \<^const>\<open>call_action_at_call_site\<close> for the one call at \<open>u\<close>.  This is
  \<open>admiss_exact\<close>'s functional shape, specialized so coverage of infinitely many
  concrete stores comes from the caller's own value being imprecise, not from
  \<open>entry_state_enterc\<close> being multi-valued.
\<close>

definition entry_state_enterc :: "cfg_node \<Rightarrow> ivl list \<Rightarrow> store \<Rightarrow> ivl list" where
  "entry_state_enterc u ctx s =
     entry_state_route_abs_gen gs u ctx (locals (entry_state_sigma_abs (Inl (u, ctx))))
       (call_action_at_call_site (compile_prog Pi ps mnm main) u)"

lemma entry_state_reserved: "reserved_ret_var gs"
  using wf by (rule wf_compile_input_reserved_ret_var)

lemma entry_state_fin: "finite (intra (compile_prog Pi ps mnm main))"
  using compile_prog_finite by blast

lemma entry_state_finC: "finite (calls (compile_prog Pi ps mnm main))"
  using compile_prog_finite by blast

interpretation entry_state_dg_base: sound_dg_spec "ectx_abs_spec gs" "gamma_unit gs" gs
  unfolding ectx_abs_spec_def by (rule sound_dg_spec_unit_for[OF ivl_is_sound_transfer_for entry_state_reserved])

lemma entry_state_sg_covered:
  "(v, ctx) \<in> fst (entry_state_sol gs Pi ps mnm main)
   \<Longrightarrow> entry_state_sg (Inl (v, ctx))
       = combine_abs gs (locals (entry_state_sigma_abs (Inl (v, ctx)))) (globs (entry_state_sigma_abs (Inr Global)))"
  by (simp add: entry_state_sg_def entry_state_sg_exec_def entry_state_sigma_abs_def entry_state_sigma_abs_exec_def)

lemma entry_state_sg_uncovered_empty:
  "(v, ctx) \<notin> fst (entry_state_sol gs Pi ps mnm main) \<Longrightarrow> \<lbrakk>entry_state_sg (Inl (v, ctx))\<rbrakk> = {}"
  by (simp add: entry_state_sg_def entry_state_sg_exec_def gamma_state_bot)

subsection \<open>Instantiating the generic DG-native activation discharge\<close>

interpretation entry_state_dg: dg_ctx_activation "ectx_abs_spec gs" gs "compile_prog Pi ps mnm main" Global
    "entry_state_route_abs_gen gs" "routed_cmb (ectx_abs_spec gs) Global"
    "routed_extra (compile_prog Pi ps mnm main) (ectx_abs_spec gs) Seed Global"
    "fun_of_exec_dg_st_for gs (bot::ivl exec_dg_st)" "fun_of_exec_dg_st_for gs cinit_ivl_st"
    "fun_of_exec_dg_st_for gs (restrict_global_resolved_q cinit_ivl_st)"
    entry_state_sigma_abs "fst (entry_state_sol gs Pi ps mnm main)"
    "(cfg_exit (compile_prog Pi ps mnm main), [])" entry_state_sg
proof unfold_locales
  show "finite (intra (compile_prog Pi ps mnm main))" by (rule entry_state_fin)
next
  show "part_post_solution
          (side_cfg_T_eff_keyed_seed_dg intra_predecessor_list (\<lambda>_. Global) (entry_state_route_abs_gen gs)
             (routed_cmb (ectx_abs_spec gs) Global)
             (routed_extra (compile_prog Pi ps mnm main) (ectx_abs_spec gs) Seed Global)
             (compile_prog Pi ps mnm main) (ectx_abs_spec gs)
             (fun_of_exec_dg_st_for gs (bot::ivl exec_dg_st)) (fun_of_exec_dg_st_for gs cinit_ivl_st)
             (fun_of_exec_dg_st_for gs (restrict_global_resolved_q cinit_ivl_st)))
          (cfg_exit (compile_prog Pi ps mnm main), []) entry_state_sigma_abs
          (fst (entry_state_sol gs Pi ps mnm main))"
    unfolding entry_state_sigma_abs_def entry_state_sigma_abs_exec_def
    by (rule entry_state_pp_abs[OF solves])
next
  fix v ctx assume "(v, ctx) \<in> fst (entry_state_sol gs Pi ps mnm main)"
  thus "entry_state_sg (Inl (v, ctx))
          = combine_abs gs (locals (entry_state_sigma_abs (Inl (v, ctx)))) (globs (entry_state_sigma_abs (Inr Global)))"
    by (rule entry_state_sg_covered)
next
  fix v ctx assume "(v, ctx) \<notin> fst (entry_state_sol gs Pi ps mnm main)"
  thus "\<lbrakk>entry_state_sg (Inl (v, ctx))\<rbrakk> = {}"
    by (rule entry_state_sg_uncovered_empty)
next
  fix u a v ctx assume "(u, ctx) \<in> fst (entry_state_sol gs Pi ps mnm main)" "(u, a, v) \<in> intra (compile_prog Pi ps mnm main)"
  thus "(v, ctx) \<in> fst (entry_state_sol gs Pi ps mnm main)" by (rule fwd_ok)
qed

subsection \<open>The routed interpretation and its CALL/COMB corollaries\<close>

interpretation entry_state_routed: routed_context "ectx_abs_spec gs" gs "compile_prog Pi ps mnm main" Global
    "entry_state_route_abs_gen gs"
    "fun_of_exec_dg_st_for gs (bot::ivl exec_dg_st)" "fun_of_exec_dg_st_for gs cinit_ivl_st"
    "fun_of_exec_dg_st_for gs (restrict_global_resolved_q cinit_ivl_st)"
    entry_state_sigma_abs "fst (entry_state_sol gs Pi ps mnm main)"
    "(cfg_exit (compile_prog Pi ps mnm main), [])" entry_state_sg
    Seed entry_state_enterc
proof (unfold_locales, goal_cases FinC SeedKey RouteAgree CallFwd CombFwd EnterAgree)
  case FinC show ?case by (rule entry_state_finC)
next
  case (SeedKey p ctx) show ?case by simp
next
  case (RouteAgree u ctx dst pars args p cont s)
  note ce = RouteAgree(2)
  have "call_action_at_call_site (compile_prog Pi ps mnm main) u = CallEdge dst pars args"
    by (rule call_action_at_call_site_eq[OF entry_state_finC compile_prog_calls_source_unique ce])
  thus ?case unfolding entry_state_enterc_def by simp
next
  case (CallFwd u ctx dst pars args p cont)
  show ?case using CallFwd(1,2) call_fwd_ok
    unfolding entry_state_sigma_abs_def entry_state_sigma_abs_exec_def by blast
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

lemma entry_state_sg_seed:
  assumes "(u, CallEdge dst xs es, FunctionEntry p, cont) \<in> calls (compile_prog Pi ps mnm main)"
    and "s \<in> \<lbrakk>entry_state_sg (Inl (u, ctx))\<rbrakk>"
  shows "call_enter gs (CallEdge dst xs es) s
           \<in> \<lbrakk>entry_state_sg (Inl (FunctionEntry p, entry_state_enterc u ctx (call_enter gs (CallEdge dst xs es) s)))\<rbrakk>"
  by (rule entry_state_routed.routed_context_call[OF assms])

lemma entry_state_sg_comb:
  assumes "(cl, CallEdge dst pars args, FunctionEntry p, v) \<in> calls (compile_prog Pi ps mnm main)"
    and "s \<in> \<lbrakk>entry_state_sg (Inl (cl, c1))\<rbrakk>"
    and "t \<in> \<lbrakk>entry_state_sg (Inl (FunctionResult p, entry_state_enterc cl c1 es))\<rbrakk>"
    and "call_enter_store gs (compile_prog Pi ps mnm main) cl s es"
  shows "combine_collect gs dst s t \<in> \<lbrakk>entry_state_sg (Inl (v, c1))\<rbrakk>"
  by (rule entry_state_routed.routed_context_comb[OF assms])

subsection \<open>Activation-indexed collecting soundness\<close>

lemma entry_state_cinit_le_cinit_ivl_st: "cinit_stores gs \<subseteq> \<lbrakk>fun_of_exec_dg_st_for gs cinit_ivl_st\<rbrakk>"
  by (auto simp: cinit_stores_def gamma_state_def fun_of_exec_dg_st_for_def fun_of_st_cinit_ivl_st_for)

lemma entry_state_locals_ge_s0d:
  "fun_of_exec_dg_st_for gs cinit_ivl_st
     \<le> locals (entry_state_sigma_abs (Inl (cfg_entry (compile_prog Pi ps mnm main), [])))"
proof -
  have "fun_of_exec_dg_st_for gs cinit_ivl_st
      \<le> locals (eq entry_state_dg.Gen (cfg_entry (compile_prog Pi ps mnm main), []) entry_state_sigma_abs)"
    by (simp add: eq_side_cfg_T_eff_keyed_seed_dg)
       (rule order_trans[OF _ side_acc_dg_ge_acc], simp add: le_supI2)
  also have "\<dots> \<le> locals (entry_state_sigma_abs (Inl (cfg_entry (compile_prog Pi ps mnm main), [])))"
    using entry_state_dg.pp_eq_bound[OF entry_cov] by (simp add: less_eq_dg_state_def)
  finally show ?thesis .
qed

theorem entry_state_activation_collect_sound:
  "activation_collect gs (admiss_exact entry_state_enterc) [] (compile_prog Pi ps mnm main) (cinit_stores gs) v ctx
     \<subseteq> \<lbrakk>entry_state_sg (Inl (v, ctx))\<rbrakk>"
proof (rule activation_collect_sound[where sg = entry_state_sg and admiss = "admiss_exact entry_state_enterc"
        and seedc = "[]" and S = "cinit_stores gs" and g = "compile_prog Pi ps mnm main" and gs = gs])
  \<comment> \<open>ENTRY_G\<close>
  fix s assume "s \<in> cinit_stores gs"
  hence "s \<in> \<lbrakk>fun_of_exec_dg_st_for gs cinit_ivl_st\<rbrakk>" using entry_state_cinit_le_cinit_ivl_st by blast
  also have "\<lbrakk>fun_of_exec_dg_st_for gs cinit_ivl_st\<rbrakk>
        = gamma_unit gs (fun_of_exec_dg_st_for gs cinit_ivl_st)
            (fun_of_exec_dg_st_for gs (restrict_global_resolved_q cinit_ivl_st))"
    unfolding gamma_unit_def fun_of_exec_dg_st_for_def
    by (rule arg_cong[where f = gamma_state], rule ext)
       (simp add: combine_abs_def restrict_global_for_def)
  also have "\<dots> \<subseteq> gamma_unit gs (locals (entry_state_sigma_abs (Inl (cfg_entry (compile_prog Pi ps mnm main), []))))
                   (globs (entry_state_sigma_abs (Inr Global)))"
    by (rule gamma_unit_mono[OF entry_state_locals_ge_s0d entry_state_dg.pp_entry_s0g_bound[OF entry_cov]])
  also have "\<dots> = \<lbrakk>entry_state_sg (Inl (cfg_entry (compile_prog Pi ps mnm main), []))\<rbrakk>"
    unfolding entry_state_sg_covered[OF entry_cov] gamma_unit_def by (rule refl)
  finally show "s \<in> \<lbrakk>entry_state_sg (Inl (cfg_entry (compile_prog Pi ps mnm main), []))\<rbrakk>" .
next
  \<comment> \<open>EDGE\<close>
  show "\<And>u a v c s s'. (u, a, v) \<in> intra (compile_prog Pi ps mnm main)
        \<Longrightarrow> s \<in> \<lbrakk>entry_state_sg (Inl (u, c))\<rbrakk> \<Longrightarrow> s' \<in> edge_step a s
        \<Longrightarrow> s' \<in> \<lbrakk>entry_state_sg (Inl (v, c))\<rbrakk>"
    by (rule entry_state_dg.dg_ctx_act_edge)
next
  \<comment> \<open>ADMISS_TOTAL\<close>
  show "\<And>u c s. \<exists>c'. admiss_exact entry_state_enterc u c s c'"
    by (simp add: admiss_exact_def)
next
  \<comment> \<open>CALL\<close>
  fix u dst pars args p cont c s c'
  assume ce: "(u, CallEdge dst pars args, FunctionEntry p, cont) \<in> calls (compile_prog Pi ps mnm main)"
    and sm: "s \<in> \<lbrakk>entry_state_sg (Inl (u, c))\<rbrakk>"
    and adm: "admiss_exact entry_state_enterc u c (call_enter gs (CallEdge dst pars args) s) c'"
  show "call_enter gs (CallEdge dst pars args) s \<in> \<lbrakk>entry_state_sg (Inl (FunctionEntry p, c'))\<rbrakk>"
    using adm entry_state_sg_seed[OF ce sm] by (simp add: admiss_exact_def)
next
  \<comment> \<open>COMB\<close>
  fix cl dst pars args p cont c1 c2 s t es
  assume ce: "(cl, CallEdge dst pars args, FunctionEntry p, cont) \<in> calls (compile_prog Pi ps mnm main)"
    and sm: "s \<in> \<lbrakk>entry_state_sg (Inl (cl, c1))\<rbrakk>"
    and adm: "admiss_exact entry_state_enterc cl c1 es c2"
    and tm: "t \<in> \<lbrakk>entry_state_sg (Inl (FunctionResult p, c2))\<rbrakk>"
    and ces: "call_enter_store gs (compile_prog Pi ps mnm main) cl s es"
  show "combine_collect gs dst s t \<in> \<lbrakk>entry_state_sg (Inl (cont, c1))\<rbrakk>"
    using adm tm entry_state_sg_comb[OF ce sm _ ces] by (simp add: admiss_exact_def)
qed

end

section \<open>Context-aggregated check report\<close>

text \<open>
  For each check node, aggregates the verdict across every context the solver
  actually covers there, using \<^class>\<open>semilattice_sup\<close>'s flat join on
  \<^typ>\<open>check_result\<close> (\<open>Check_Unknown\<close> is the top: two contexts agreeing keep
  that verdict, any disagreement collapses to \<open>Check_Unknown\<close>) rather than
  joining the underlying interval states first. A node with no covered context
  is classified directly against the uncovered reading of \<^const>\<open>entry_state_sg_exec\<close>
  (\<open>bot\<close> at the seeded default context \<open>[]\<close>, since \<^const>\<open>entry_state_sg_exec\<close>
  returns \<open>bot\<close> at every context for an uncovered node) -- the same \<open>bot\<close>
  classification the flat, context-insensitive report already gives dead code,
  not a fabricated new case. \<open>entry_state_sg_exec\<close> (not the context-scoped
  \<open>entry_state_sg\<close> the soundness theorem above is stated about) is used here
  directly because the two are the same function unconditionally, by
  \<open>entry_state_sg_def\<close> inside that context, and only the top-level
  definition carries an unconditional code equation -- the context's own
  soundness obligations are not runtime-decidable side-conditions the code
  generator could discharge.

  Enumerating the contexts at a node reads \<^const>\<open>Set.filter\<close> over the
  solver's own already-finite \<open>fst sol\<close>, never a raw set comprehension: since
  \<^typ>\<open>ivl\<close>'s only order is the abstract-domain lattice (interval containment,
  not total -- \<open>[0,5]\<close> and \<open>[3,10]\<close> are incomparable), \<^typ>\<open>ivl list\<close> has no
  \<^class>\<open>enum\<close> instance, so a comprehension \<open>{ctx. ...}\<close> is not executable here;
  filtering an already-finite set needs no such instance.
\<close>

definition entry_state_classify_at ::
    "cfg_node \<Rightarrow> bexp \<Rightarrow> (pp \<times> ivl list) set \<Rightarrow> (pp \<times> ivl list + gk \<Rightarrow> ivl abs_state)
       \<Rightarrow> check_result" where
  "entry_state_classify_at v cnd vars sg =
     (let ctxs = snd ` Set.filter (\<lambda>(v', ctx). v' = v) vars
      in if ctxs = {} then interval_classify_check cnd (sg (Inl (v, [])))
         else Sup_fin ((\<lambda>ctx. interval_classify_check cnd (sg (Inl (v, ctx)))) ` ctxs))"

definition entry_state_check_report ::
    "(vname \<Rightarrow> bool) \<Rightarrow> proc_table \<Rightarrow> pname list \<Rightarrow> pname \<Rightarrow> com \<Rightarrow> check_report_entry list" where
  "entry_state_check_report gs Pi ps mnm main =
     (let sol = entry_state_sol gs Pi ps mnm main
      in map (\<lambda>(u, a, v). (u, ea_check_cond a,
                entry_state_classify_at u (ea_check_cond a) (fst sol) (entry_state_sg_exec gs Pi ps mnm main)))
           (filter (\<lambda>(u, a, v). is_EA_Check a) (cfg_intra_list (compile_prog Pi ps mnm main))))"

text \<open>
  Same single-solve-per-report fix as \<open>interval_td_check_report_code\<close>: bind
  \<open>entry_state_sol\<close> once, outside \<^const>\<open>map\<close>'s per-check closure, so the
  generated code computes the solved system once per report regardless of
  check count.
\<close>

declare entry_state_check_report_def [code del]

lemma entry_state_check_report_code [code]:
  "entry_state_check_report gs Pi ps mnm main =
     (let sol = entry_state_sol gs Pi ps mnm main;
          sg = entry_state_sg_exec gs Pi ps mnm main
      in map (\<lambda>(u, a, v). (u, ea_check_cond a, entry_state_classify_at u (ea_check_cond a) (fst sol) sg))
           (filter (\<lambda>(u, a, v). is_EA_Check a) (cfg_intra_list (compile_prog Pi ps mnm main))))"
  unfolding entry_state_check_report_def Let_def by (rule refl)

definition entry_state_check_report_prog :: "pname \<Rightarrow> imp_prog \<Rightarrow> check_report_entry list" where
  "entry_state_check_report_prog mnm p =
     entry_state_check_report (declared_global p) (prog_table p) (prog_procs p) mnm (prog_main p)"

definition analyse_interval_entry_state :: "imp_prog \<Rightarrow> check_report_entry list" where
  "analyse_interval_entry_state p = entry_state_check_report_prog prog_main_name p"

end
