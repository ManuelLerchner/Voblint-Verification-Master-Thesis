theory Example_Interval_DG_Ctx_Sound
  imports                    
    Example_Interval_DG_Ctx_Flagship
begin

section \<open>Route consistency and the abstract transport of the context-sensitive solution\<close>

text \<open>
  The executable routed equations are transported to an abstract context-indexed
  post-solution.  Entry publication, activation selection, and callee-result lookup
  use one route function.  Proving that route commutes with representation transport
  therefore discharges both strategy-tree commutation obligations.
\<close>

subsection \<open>The abstract routed hooks\<close>

abbreviation Sabs :: "(ivl abs_state, ivl abs_state) dg_spec" where
  "Sabs \<equiv> unit_dg_spec_for twice_gs (ivl_tf_for twice_gs)"

text \<open>Unlike a fixed name-based classifier, \<open>twice_gs\<close> has no pre-registered
  \<^locale>\<open>sound_dg_spec\<close> interpretation for the diagonal interval spec: establish
  it once here, in the chain's shared ancestor, so
  every downstream \<open>dg_ctx_activation\<close>/\<open>routed_context\<close> interpretation on \<open>Sabs\<close>
  discharges its inherited step/combine/enter obligations automatically.\<close>

lemma twice_gs_reserved: "reserved_ret_var twice_gs"
  unfolding reserved_ret_var_def by eval

interpretation ivl_dg_for: sound_dg_spec Sabs "gamma_unit twice_gs" twice_gs
  by (rule sound_dg_spec_unit_for[OF ivl_is_sound_transfer_for twice_gs_reserved])

text \<open>The post-enter callee state and its context projection, abstractly.  These
  mirror \<^const>\<open>entered_ivl\<close> / \<^const>\<open>route_ivl\<close> on \<^typ>\<open>ivl abs_state\<close>.\<close>

definition entered_abs :: "ivl abs_state \<Rightarrow> call_action \<Rightarrow> ivl abs_state" where
  "entered_abs d ca =
     (case ca of CallEdge dst fs as \<Rightarrow> snd (dgs_enter Sabs fs as d bot))"

definition route_abs :: "ivl abs_state \<Rightarrow> call_action \<Rightarrow> ivl list" where
  "route_abs d ca =
     (case ca of CallEdge dst pars args \<Rightarrow> formals_context pars (entered_abs d ca))"

text \<open>The generic 4-argument routing hook, mirroring \<^const>\<open>route_ivl_gen\<close>.\<close>
definition route_abs_gen :: "pp \<Rightarrow> ivl list \<Rightarrow> ivl abs_state \<Rightarrow> call_action \<Rightarrow> ivl list" where
  "route_abs_gen u ctx d ca = route_abs d ca"

subsection \<open>The route-consistency core\<close>

text \<open>The post-enter callee state commutes with the refinement morphism: the entered
  executable store maps (through \<open>fun_of_exec_dg_st_for\<close>) to the entered abstract store.
  This is \<open>ivl_Hstep\<close> read on the returned local component, with the incoming
  global slot defaulted to \<open>bot\<close>.\<close>

lemma entered_commute:
  "fun_of_exec_dg_st_for twice_gs (entered_ivl s ca) = entered_abs (fun_of_exec_dg_st_for twice_gs s) ca"
proof (cases ca)
  case (CallEdge dst fs as)
  have enter: "map_prod (fun_of_exec_dg_st_for twice_gs) (fun_of_exec_dg_st_for twice_gs)
                 (dgs_enter (unit_dg_spec_st_for twice_gs (ivl_tf_st_for twice_gs) (ivl_enter_st_for twice_gs)) fs as s bot)
               = dgs_enter Sabs fs as (fun_of_exec_dg_st_for twice_gs s) (fun_of_exec_dg_st_for twice_gs bot)"
    by (rule ivl_Henter_for)
  have "fun_of_exec_dg_st_for twice_gs (snd (dgs_enter (unit_dg_spec_st_for twice_gs (ivl_tf_st_for twice_gs) (ivl_enter_st_for twice_gs)) fs as s bot))
      = snd (map_prod (fun_of_exec_dg_st_for twice_gs) (fun_of_exec_dg_st_for twice_gs)
               (dgs_enter (unit_dg_spec_st_for twice_gs (ivl_tf_st_for twice_gs) (ivl_enter_st_for twice_gs)) fs as s bot))"
    by (metis snd_conv map_prod_simp surj_pair)
  also have "\<dots> = snd (dgs_enter Sabs fs as (fun_of_exec_dg_st_for twice_gs s) (fun_of_exec_dg_st_for twice_gs bot))"
    by (simp add: enter)
  finally show ?thesis
    using CallEdge
    by (simp add: entered_ivl_def entered_abs_def Spoly_def fun_of_exec_dg_st_for_bot bot_fun_def)
qed

text \<open>The route-consistency corollary: the abstract route on a pushed-forward state
  is the executable route.  Because \<^const>\<open>route_abs\<close> / \<^const>\<open>route_ivl\<close> project the
  \<^emph>\<open>same\<close> variable and \<^term>\<open>fun_of_exec_dg_st \<equiv> lookup_exec_dg_st\<close>, the two routes agree \<^emph>\<open>as
  values\<close> --- so the \<^const>\<open>Side\<close> keys they compute are literally equal, on any read
  callee state.\<close>

lemma route_commute:
  "route_abs (fun_of_exec_dg_st_for twice_gs s) ca = route_ivl s ca"
proof (cases ca)
  case (CallEdge dst pars args)
  have "route_abs (fun_of_exec_dg_st_for twice_gs s) ca
      = formals_context pars (entered_abs (fun_of_exec_dg_st_for twice_gs s) ca)"
    using CallEdge by (simp add: route_abs_def)
  also have "\<dots> = formals_context pars (fun_of_exec_dg_st_for twice_gs (entered_ivl s ca))"
    by (simp add: entered_commute)
  also have "\<dots> = route_ivl s ca"
    using CallEdge
    by (simp add: route_ivl_def formals_context_def fun_of_exec_dg_st_for_def fun_of_resolved_st_q_for_def)
  finally show ?thesis .
qed

lemma route_commute_gen:
  "route_ivl_gen u ctx s ca = route_abs_gen u ctx (fun_of_exec_dg_st_for twice_gs s) ca"
  by (simp add: route_ivl_gen_def route_abs_gen_def route_commute)

subsection \<open>Per-tree transport commutation\<close>

text \<open>The frame-entry seed \<^emph>\<open>read\<close> transports: it reads the seed global slot and
  echoes it back as a local Answer; no routing, so the tree is identical on both
  carriers and commutes through \<open>fun_of_dg_st_for\<close>.\<close>

lemma dg_tree_st_commute_frame_read:
  "dg_tree_st_commute_for twice_gs env
     (QueryG (Seed v ctx) (\<lambda>s. Answer (DG (globs s) bot)))
     (QueryG (Seed v ctx) (\<lambda>s. Answer (DG (globs s) bot)))"
  by (simp add: dg_tree_st_commute_for_def fun_of_dg_st_for_simps fun_of_exec_dg_st_for_bot o_def
                dep_aux_def bot_fun_def)

text \<open>The return combine commutes componentwise with an arbitrary incoming global
  slot: the \<open>ivl_Hcomb_for\<close> homomorphism read on each output projection, for a routed
  combine that reads the shared global through a query instead of discarding it.\<close>

lemma dgs_combine_snd_commute_gen:
  "fun_of_exec_dg_st_for twice_gs (snd (dgs_combine Spoly dst dc de g))
     = snd (dgs_combine Sabs dst (fun_of_exec_dg_st_for twice_gs dc) (fun_of_exec_dg_st_for twice_gs de) (fun_of_exec_dg_st_for twice_gs g))"
proof -
  have step: "map_prod (fun_of_exec_dg_st_for twice_gs) (fun_of_exec_dg_st_for twice_gs)
                (dgs_combine (unit_dg_spec_st_for twice_gs (ivl_tf_st_for twice_gs) (ivl_enter_st_for twice_gs)) dst dc de g)
              = dgs_combine Sabs dst (fun_of_exec_dg_st_for twice_gs dc) (fun_of_exec_dg_st_for twice_gs de) (fun_of_exec_dg_st_for twice_gs g)"
    by (rule ivl_Hcomb_for)
  have "fun_of_exec_dg_st_for twice_gs (snd (dgs_combine (unit_dg_spec_st_for twice_gs (ivl_tf_st_for twice_gs) (ivl_enter_st_for twice_gs)) dst dc de g))
      = snd (map_prod (fun_of_exec_dg_st_for twice_gs) (fun_of_exec_dg_st_for twice_gs)
               (dgs_combine (unit_dg_spec_st_for twice_gs (ivl_tf_st_for twice_gs) (ivl_enter_st_for twice_gs)) dst dc de g))"
    by (metis snd_conv map_prod_simp surj_pair)
  also have "\<dots> = snd (dgs_combine Sabs dst (fun_of_exec_dg_st_for twice_gs dc) (fun_of_exec_dg_st_for twice_gs de) (fun_of_exec_dg_st_for twice_gs g))"
    by (simp add: step)
  finally show ?thesis by (simp add: Spoly_def)
qed

lemma dgs_combine_fst_commute_gen:
  "fun_of_exec_dg_st_for twice_gs (fst (dgs_combine Spoly dst dc de g))
     = fst (dgs_combine Sabs dst (fun_of_exec_dg_st_for twice_gs dc) (fun_of_exec_dg_st_for twice_gs de) (fun_of_exec_dg_st_for twice_gs g))"
proof -
  have step: "map_prod (fun_of_exec_dg_st_for twice_gs) (fun_of_exec_dg_st_for twice_gs) (dgs_combine (unit_dg_spec_st_for twice_gs (ivl_tf_st_for twice_gs) (ivl_enter_st_for twice_gs)) dst dc de g)
              = dgs_combine Sabs dst (fun_of_exec_dg_st_for twice_gs dc) (fun_of_exec_dg_st_for twice_gs de) (fun_of_exec_dg_st_for twice_gs g)"
    by (rule ivl_Hcomb_for)
  have "fun_of_exec_dg_st_for twice_gs (fst (dgs_combine (unit_dg_spec_st_for twice_gs (ivl_tf_st_for twice_gs) (ivl_enter_st_for twice_gs)) dst dc de g))
      = fst (map_prod (fun_of_exec_dg_st_for twice_gs) (fun_of_exec_dg_st_for twice_gs) (dgs_combine (unit_dg_spec_st_for twice_gs (ivl_tf_st_for twice_gs) (ivl_enter_st_for twice_gs)) dst dc de g))"
    by (metis fst_conv map_prod_simp surj_pair)
  also have "\<dots> = fst (dgs_combine Sabs dst (fun_of_exec_dg_st_for twice_gs dc) (fun_of_exec_dg_st_for twice_gs de) (fun_of_exec_dg_st_for twice_gs g))"
    by (simp add: step)
  finally show ?thesis by (simp add: Spoly_def)
qed

text \<open>The enter transfer commutes componentwise with an arbitrary incoming global
  slot, generalizing \<open>entered_commute\<close> (which reads only the local half at a
  fixed \<open>bot\<close> global) to both projections at any global.\<close>

lemma dgs_enter_snd_commute_gen:
  "fun_of_exec_dg_st_for twice_gs (snd (dgs_enter Spoly fs as d g))
     = snd (dgs_enter Sabs fs as (fun_of_exec_dg_st_for twice_gs d) (fun_of_exec_dg_st_for twice_gs g))"
proof -
  have step: "map_prod (fun_of_exec_dg_st_for twice_gs) (fun_of_exec_dg_st_for twice_gs) (dgs_enter (unit_dg_spec_st_for twice_gs (ivl_tf_st_for twice_gs) (ivl_enter_st_for twice_gs)) fs as d g)
              = dgs_enter Sabs fs as (fun_of_exec_dg_st_for twice_gs d) (fun_of_exec_dg_st_for twice_gs g)"
    by (rule ivl_Henter_for)
  have "fun_of_exec_dg_st_for twice_gs (snd (dgs_enter (unit_dg_spec_st_for twice_gs (ivl_tf_st_for twice_gs) (ivl_enter_st_for twice_gs)) fs as d g))
      = snd (map_prod (fun_of_exec_dg_st_for twice_gs) (fun_of_exec_dg_st_for twice_gs) (dgs_enter (unit_dg_spec_st_for twice_gs (ivl_tf_st_for twice_gs) (ivl_enter_st_for twice_gs)) fs as d g))"
    by (metis snd_conv map_prod_simp surj_pair)
  also have "\<dots> = snd (dgs_enter Sabs fs as (fun_of_exec_dg_st_for twice_gs d) (fun_of_exec_dg_st_for twice_gs g))"
    by (simp add: step)
  finally show ?thesis by (simp add: Spoly_def)
qed

lemma dgs_enter_fst_commute_gen:
  "fun_of_exec_dg_st_for twice_gs (fst (dgs_enter Spoly fs as d g))
     = fst (dgs_enter Sabs fs as (fun_of_exec_dg_st_for twice_gs d) (fun_of_exec_dg_st_for twice_gs g))"
proof -
  have step: "map_prod (fun_of_exec_dg_st_for twice_gs) (fun_of_exec_dg_st_for twice_gs) (dgs_enter (unit_dg_spec_st_for twice_gs (ivl_tf_st_for twice_gs) (ivl_enter_st_for twice_gs)) fs as d g)
              = dgs_enter Sabs fs as (fun_of_exec_dg_st_for twice_gs d) (fun_of_exec_dg_st_for twice_gs g)"
    by (rule ivl_Henter_for)
  have "fun_of_exec_dg_st_for twice_gs (fst (dgs_enter (unit_dg_spec_st_for twice_gs (ivl_tf_st_for twice_gs) (ivl_enter_st_for twice_gs)) fs as d g))
      = fst (map_prod (fun_of_exec_dg_st_for twice_gs) (fun_of_exec_dg_st_for twice_gs) (dgs_enter (unit_dg_spec_st_for twice_gs (ivl_tf_st_for twice_gs) (ivl_enter_st_for twice_gs)) fs as d g))"
    by (metis fst_conv map_prod_simp surj_pair)
  also have "\<dots> = fst (dgs_enter Sabs fs as (fun_of_exec_dg_st_for twice_gs d) (fun_of_exec_dg_st_for twice_gs g))"
    by (simp add: step)
  finally show ?thesis by (simp add: Spoly_def)
qed

text \<open>The routed combine tree, reading the shared global through a query instead
  of a fixed \<open>bot\<close>, transports the same way once the extra query commutes: the
  read slot \<open>gk0\<close> is the same key on both carriers, so \<open>fun_of_dg_st_for\<close>
  applied to \<^term>\<open>env (Inr gk0)\<close> is exactly what the abstract side reads at that
  key.\<close>

lemma dg_tree_st_commute_routed_cmb:
  "dg_tree_st_commute_for twice_gs env (routed_cmb Spoly gk0 route_ivl_gen ctx ca cc ex)
                          (routed_cmb Sabs gk0 route_abs_gen ctx ca cc ex)"
  unfolding routed_cmb_def route_ivl_gen_def route_abs_gen_def Let_def
  by (cases ca)
     (simp_all add: dg_tree_st_commute_for_def fun_of_dg_st_for_simps fun_of_exec_dg_st_for_bot o_def
                    route_commute dgs_combine_fst_commute_gen dgs_combine_snd_commute_gen
                    dep_aux_def bot_fun_def fun_upd_apply fun_eq_iff)

text \<open>The routed enter publication --- reading the shared global through a query
  and additionally publishing the enter transfer's own global side-effect to
  \<open>gk0\<close>, on top of the routed local seed --- transports the same way once both
  projections of the enter transfer commute.\<close>

lemma dg_tree_st_commute_routed_enter_pub:
  "dg_tree_st_commute_for twice_gs env
     (with_call a (\<lambda>dst fs as. do {
        entry_state \<leftarrow> read_local (v, ctx);
        globals_state \<leftarrow> read_global Global;
        publish_global Global (enter_global Spoly fs as (locals entry_state) (globs globals_state));
        publish_seed (Seed w (route_ivl_gen v ctx (locals entry_state) a))
          (enter_local Spoly fs as (locals entry_state) (globs globals_state));
        answer_local bot
      }))
     (with_call a (\<lambda>dst fs as. do {
        entry_state \<leftarrow> read_local (v, ctx);
        globals_state \<leftarrow> read_global Global;
        publish_global Global (enter_global Sabs fs as (locals entry_state) (globs globals_state));
        publish_seed (Seed w (route_abs_gen v ctx (locals entry_state) a))
          (enter_local Sabs fs as (locals entry_state) (globs globals_state));
        answer_local bot
      }))"
  unfolding route_ivl_gen_def route_abs_gen_def
  by (cases a)
     (simp add: dg_tree_st_commute_for_def fun_of_dg_st_for_simps fun_of_exec_dg_st_for_bot o_def
                route_commute dgs_enter_fst_commute_gen dgs_enter_snd_commute_gen
                dep_aux_def bot_fun_def fun_upd_apply fun_eq_iff)

lemma hextra_commute_routed:
  "list_all2 (dg_tree_st_commute_for twice_gs env)
     (routed_extra twice_cfg Spoly Seed Global route_ivl_gen ctx w)
     (routed_extra twice_cfg Sabs Seed Global route_abs_gen ctx w)"
  unfolding routed_extra_def Let_def
  by (auto simp: list_all2_appendI list_all2_map1 list_all2_map2 list_all2_refl split_beta
                 dg_tree_st_commute_frame_read dg_tree_st_commute_routed_enter_pub
           split: cfg_node.split)

subsection \<open>The certified executable post-solution\<close>

lemma twice_ctx_solve_dom:
  "TD_side_warrowing_apinis_Interp.solve_dom TYPE(gk) TYPE((ivl exec_dg_st, ivl exec_dg_st) dg_state)
     twice_ctx_eqs (cfg_exit twice_cfg, [])"
  using twice_ctx_terminates
  unfolding TD_side_warrowing_apinis_Interp.term_equivalence
            TD_side_warrowing_apinis_Interp.solve_c_dom_def
  by simp

lemma twice_ctx_pp_st:
  "part_post_solution twice_ctx_eqs (cfg_exit twice_cfg, []) (snd twice_ctx_sol) (fst twice_ctx_sol)"
  using TD_side_warrowing_apinis_Interp.partial_post_solution
          [OF twice_ctx_solve_dom, of "fst twice_ctx_sol" "snd twice_ctx_sol"]
  unfolding twice_ctx_sol_def by simp

subsection \<open>Transport to the abstract context-indexed D/G post-solution\<close>

text \<open>The generic bridge \<open>part_post_solution_seed_dg_st_to_abs\<close> carries the
  executable routed post-solution to the abstract one.  The three bundled
  obligations are \<open>ivl_Hstep\<close> (intra edges), \<open>dg_tree_st_commute_routed_cmb\<close>
  (routed combine), and \<open>hextra_commute_routed\<close> (frame read / routed enter
  publication) -- the latter two discharged solely from route consistency.\<close>

theorem twice_ctx_pp_abs:
  "part_post_solution
     (side_cfg_T_eff_keyed_seed_dg intra_predecessor_list (\<lambda>_. Global) route_abs_gen
        (routed_cmb Sabs Global) (routed_extra twice_cfg Sabs Seed Global) twice_cfg Sabs
        (fun_of_exec_dg_st_for twice_gs (bot::ivl exec_dg_st)) (fun_of_exec_dg_st_for twice_gs cinit_ivl_st)
        (fun_of_exec_dg_st_for twice_gs (restrict_global_resolved_q cinit_ivl_st)))
     (cfg_exit twice_cfg, []) (fun_of_dg_st_for twice_gs \<circ> snd twice_ctx_sol) (fst twice_ctx_sol)"
proof -
  have pp': "part_post_solution
       (side_cfg_T_eff_keyed_seed_dg intra_predecessor_list (\<lambda>_. Global) route_ivl_gen
          (routed_cmb Spoly Global) (routed_extra twice_cfg Spoly Seed Global) twice_cfg Spoly
          bot cinit_ivl_st (restrict_global_resolved_q cinit_ivl_st))
       (cfg_exit twice_cfg, []) (snd twice_ctx_sol) (fst twice_ctx_sol)"
    using twice_ctx_pp_st unfolding twice_ctx_eqs_def by simp
  text \<open>\<open>ivl_Hstep_for\<close> is stated for the generic \<open>unit_dg_spec_st_for gs ivl_tf_st_for ?enter_st\<close>
    shape; \<open>Spoly\<close> hides that shape behind a \<open>definition\<close>, so plain rule resolution
    cannot unify the two without folding \<open>Spoly_def\<close> back in first.\<close>
  have ivl_Hstep_ctx:
    "map_prod (fun_of_exec_dg_st_for twice_gs) (fun_of_exec_dg_st_for twice_gs) (dg_spec_step Spoly a d g') =
       dg_spec_step Sabs a (fun_of_exec_dg_st_for twice_gs d) (fun_of_exec_dg_st_for twice_gs g')" for a d g'
    unfolding Spoly_def by (rule ivl_Hstep_for)
  show ?thesis
    by (rule part_post_solution_seed_dg_st_to_abs_for
          [where gs = twice_gs and pred_sel = intra_predecessor_list and gkey = "\<lambda>_. Global"
             and route_st = route_ivl_gen and route_abs = route_abs_gen
             and cmb_st = "routed_cmb Spoly Global" and cmb_abs = "routed_cmb Sabs Global"
             and extra_st = "routed_extra twice_cfg Spoly Seed Global"
             and extra_abs = "routed_extra twice_cfg Sabs Seed Global"
             and g = twice_cfg and S_st = Spoly and S_abs = Sabs,
           OF ivl_Hstep_ctx route_commute_gen dg_tree_st_commute_routed_cmb hextra_commute_routed pp'])
qed


end


