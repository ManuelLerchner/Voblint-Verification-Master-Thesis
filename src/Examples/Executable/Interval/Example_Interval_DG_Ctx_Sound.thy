theory Example_Interval_DG_Ctx_Sound
  imports                    
    Example_Interval_DG_Ctx_Flagship
begin

section \<open>Route consistency and the abstract transport of the context-sensitive solution\<close>

text \<open>
  Phase 3 of the interval vertical slice.  The executable routed generator
  \<^const>\<open>twice_ctx_eqs\<close> is transported to an abstract context-indexed post-solution
  through the generic bridge \<^theory>\<open>Voblint_Analysis.Exec_DG_Bridge\<close>.

  The only instance-specific obligations the generic transport leaves open are the
  bundled tree-commutation hypotheses \<open>Hcmb\<close> and \<open>Hextra\<close> --- exactly the layers
  where a context is routed.  Both are discharged from a \<^emph>\<open>single\<close> route-consistency
  core: the abstract route computed on the pushed-forward callee state equals the
  executable route.  Enter publication, the activation context, and the combine
  callee-exit lookup all read the same route, so the executable and abstract
  \<^const>\<open>Side\<close> targets coincide rather than agreeing by accident.
\<close>

subsection \<open>The abstract routed hooks\<close>

abbreviation Sabs :: "(ivl abs_state, ivl abs_state) dg_spec" where
  "Sabs \<equiv> unit_dg_spec ivl_tf"

text \<open>The post-enter callee state and its context projection, abstractly.  These
  mirror \<^const>\<open>entered_ivl\<close> / \<^const>\<open>route_ivl\<close> on \<^typ>\<open>ivl abs_state\<close>.\<close>

definition entered_abs :: "ivl abs_state \<Rightarrow> call_action \<Rightarrow> ivl abs_state" where
  "entered_abs d ca =
     (case ca of CallEdge dst fs as \<Rightarrow> snd (dgs_enter Sabs fs as d bot))"

definition route_abs :: "ivl abs_state \<Rightarrow> call_action \<Rightarrow> ivl" where
  "route_abs d ca = entered_abs d ca ''p''"

subsection \<open>The route-consistency core\<close>

text \<open>The post-enter callee state commutes with the refinement morphism: the entered
  executable store maps (through \<^const>\<open>fun_of_st\<close>) to the entered abstract store.
  This is \<open>ivl_Hstep\<close> read on the returned local component, with the incoming
  global slot defaulted to \<open>bot\<close>.\<close>

lemma entered_commute:
  "fun_of_st (entered_ivl s ca) = entered_abs (fun_of_st s) ca"
proof (cases ca)
  case (CallEdge dst fs as)
  have enter: "map_prod fun_of_st fun_of_st
                 (dgs_enter (unit_dg_spec_st ivl_tf_st ivl_enter_st) fs as s bot)
               = dgs_enter Sabs fs as (fun_of_st s) (fun_of_st bot)"
    by (rule ivl_Henter)
  have "fun_of_st (snd (dgs_enter (unit_dg_spec_st ivl_tf_st ivl_enter_st) fs as s bot))
      = snd (map_prod fun_of_st fun_of_st
               (dgs_enter (unit_dg_spec_st ivl_tf_st ivl_enter_st) fs as s bot))"
    by (metis snd_conv map_prod_simp surj_pair)
  also have "\<dots> = snd (dgs_enter Sabs fs as (fun_of_st s) (fun_of_st bot))"
    by (simp add: enter)
  finally show ?thesis
    using CallEdge
    by (simp add: entered_ivl_def entered_abs_def Spoly_def fun_of_st_bot bot_fun_def)
qed

text \<open>The route-consistency corollary: the abstract route on a pushed-forward state
  is the executable route.  Because \<^const>\<open>route_abs\<close> / \<^const>\<open>route_ivl\<close> project the
  \<^emph>\<open>same\<close> variable and \<^term>\<open>fun_of_st \<equiv> lookup_st\<close>, the two routes agree \<^emph>\<open>as
  values\<close> --- so the \<^const>\<open>Side\<close> keys they compute are literally equal, on any read
  callee state.\<close>

lemma route_commute:
  "route_abs (fun_of_st s) ca = route_ivl s ca"
  by (simp add: route_abs_def route_ivl_def entered_commute[symmetric])

subsection \<open>The abstract routed enter-seed and combine trees\<close>

text \<open>The abstract mirrors of \<^const>\<open>extra_ivl\<close> / \<^const>\<open>cmb_ivl\<close>, over
  \<^typ>\<open>ivl abs_state\<close>: same tree skeleton, routed through \<^const>\<open>route_abs\<close> /
  \<^const>\<open>entered_abs\<close> and the abstract combine \<^const>\<open>Sabs\<close>.\<close>

definition extra_abs ::
  "cfg \<Rightarrow> ivl \<Rightarrow> pp \<Rightarrow> (pp \<times> ivl, gk, (ivl abs_state, ivl abs_state) dg_state) strategy_tree list" where
  "extra_abs g ctx v =
     (if is_function_entry v
        then [QueryG (Seed v ctx) (\<lambda>s. Answer (DG (globs s) bot))]
        else [])
     @ map (\<lambda>(w, ca, k).
             QueryL (v, ctx) (\<lambda>d.
               Side (Seed w (route_abs (locals d) ca)) (DG bot (entered_abs (locals d) ca))
                 (Answer (DG bot bot))))
           (call_successor_list g v)"

definition cmb_abs ::
  "cfg \<Rightarrow> ivl \<Rightarrow> vname option \<Rightarrow> pp \<Rightarrow> pp
     \<Rightarrow> (pp \<times> ivl, gk, (ivl abs_state, ivl abs_state) dg_state) strategy_tree" where
  "cmb_abs g ctx dst cc ex =
     QueryL (cc, ctx) (\<lambda>dcl.
       (case call_successor_list g cc of
          (w, ca, k) # _ \<Rightarrow>
            QueryL (ex, route_abs (locals dcl) ca) (\<lambda>dex.
              Side Global (DG bot (fst (dgs_combine Sabs dst (locals dcl) (locals dex) bot)))
                (Answer (DG (snd (dgs_combine Sabs dst (locals dcl) (locals dex) bot)) bot)))
        | [] \<Rightarrow> Answer (DG bot bot)))"

subsection \<open>Per-tree transport commutation\<close>

text \<open>The frame-entry seed \<^emph>\<open>read\<close> transports: it reads the seed global slot and
  echoes it back as a local Answer; no routing, so the tree is identical on both
  carriers and commutes through \<^const>\<open>fun_of_dg_st\<close>.\<close>

lemma dg_tree_st_commute_frame_read:
  "dg_tree_st_commute env
     (QueryG (Seed v ctx) (\<lambda>s. Answer (DG (globs s) bot)))
     (QueryG (Seed v ctx) (\<lambda>s. Answer (DG (globs s) bot)))"
  by (simp add: dg_tree_st_commute_def fun_of_dg_st_simps fun_of_st_bot o_def
                dep_aux_def bot_fun_def)

text \<open>The caller-side routed enter publication transports.  The \<^const>\<open>Side\<close> key
  \<^term>\<open>Seed w (route_ivl (locals d) a)\<close> is carried over \<^emph>\<open>literally\<close> by
  \<open>route_commute\<close>, and the published entered store by \<open>entered_commute\<close>;
  the dependency set is the single read \<^term>\<open>Inl (v, ctx)\<close>, unaffected by routing.\<close>

lemma dg_tree_st_commute_enter_pub:
  "dg_tree_st_commute env
     (QueryL (v, ctx) (\<lambda>d. Side (Seed w (route_ivl (locals d) a))
                             (DG bot (entered_ivl (locals d) a)) (Answer (DG bot bot))))
     (QueryL (v, ctx) (\<lambda>d. Side (Seed w (route_abs (locals d) a))
                             (DG bot (entered_abs (locals d) a)) (Answer (DG bot bot))))"
  by (simp add: dg_tree_st_commute_def fun_of_dg_st_simps fun_of_st_bot o_def
                route_commute entered_commute dep_aux_def bot_fun_def
                fun_upd_apply fun_eq_iff)

text \<open>The return combine commutes componentwise (\<open>ivl_Hcomb\<close> read on each
  output projection, incoming global slot \<open>bot\<close>).\<close>

lemma dgs_combine_snd_commute:
  "fun_of_st (snd (dgs_combine Spoly dst dc de bot))
     = snd (dgs_combine Sabs dst (fun_of_st dc) (fun_of_st de) bot)"
proof -
  have step: "map_prod fun_of_st fun_of_st
                (dgs_combine (unit_dg_spec_st ivl_tf_st ivl_enter_st) dst dc de bot)
              = dgs_combine Sabs dst (fun_of_st dc) (fun_of_st de) (fun_of_st bot)"
    by (rule ivl_Hcomb)
  have "fun_of_st (snd (dgs_combine (unit_dg_spec_st ivl_tf_st ivl_enter_st) dst dc de bot))
      = snd (map_prod fun_of_st fun_of_st
               (dgs_combine (unit_dg_spec_st ivl_tf_st ivl_enter_st) dst dc de bot))"
    by (metis snd_conv map_prod_simp surj_pair)
  also have "\<dots> = snd (dgs_combine Sabs dst (fun_of_st dc) (fun_of_st de) (fun_of_st bot))"
    by (simp add: step)
  finally show ?thesis by (simp add: Spoly_def fun_of_st_bot bot_fun_def)
qed

lemma dgs_combine_fst_commute:
  "fun_of_st (fst (dgs_combine Spoly dst dc de bot))
     = fst (dgs_combine Sabs dst (fun_of_st dc) (fun_of_st de) bot)"
proof -
  have step: "map_prod fun_of_st fun_of_st (dgs_combine (unit_dg_spec_st ivl_tf_st ivl_enter_st) dst dc de bot)
              = dgs_combine Sabs dst (fun_of_st dc) (fun_of_st de) (fun_of_st bot)"
    by (rule ivl_Hcomb)
  have "fun_of_st (fst (dgs_combine (unit_dg_spec_st ivl_tf_st ivl_enter_st) dst dc de bot))
      = fst (map_prod fun_of_st fun_of_st (dgs_combine (unit_dg_spec_st ivl_tf_st ivl_enter_st) dst dc de bot))"
    by (metis fst_conv map_prod_simp surj_pair)
  also have "\<dots> = fst (dgs_combine Sabs dst (fun_of_st dc) (fun_of_st de) (fun_of_st bot))"
    by (simp add: step)
  finally show ?thesis by (simp add: Spoly_def fun_of_st_bot bot_fun_def)
qed

text \<open>The destination-aware return combine transports.  The callee exit is read
  under \<^term>\<open>route_ivl (locals dcl) ca\<close> --- the \<^emph>\<open>same\<close> context selected at the
  matching call site's call edge --- carried over literally by \<open>route_commute\<close>; the two
  combine outputs transport through \<open>dgs_combine_fst_commute\<close> / \<open>_snd_commute\<close>.\<close>

lemma dg_tree_st_commute_cmb:
  "dg_tree_st_commute env (cmb_ivl g ctx dst cc ex) (cmb_abs g ctx dst cc ex)"
  unfolding cmb_ivl_def cmb_abs_def
  by (cases "call_successor_list g cc")
     (simp_all add: dg_tree_st_commute_def fun_of_dg_st_simps fun_of_st_bot o_def
                    route_commute dgs_combine_fst_commute dgs_combine_snd_commute
                    dep_aux_def bot_fun_def fun_upd_apply fun_eq_iff
              split: prod.splits)

text \<open>The per-node \<open>extra\<close> list transports elementwise: the optional frame-entry
  read and every routed enter publication.\<close>

lemma hextra_commute:
  "list_all2 (dg_tree_st_commute env) (extra_ivl g ctx w) (extra_abs g ctx w)"
  unfolding extra_ivl_def extra_abs_def
  by (auto simp: list_all2_appendI list_all2_map1 list_all2_map2 list_all2_refl split_beta
                 dg_tree_st_commute_frame_read dg_tree_st_commute_enter_pub)

subsection \<open>The certified executable post-solution\<close>

lemma twice_ctx_solve_dom:
  "TD_side_warrowing_apinis_Interp.solve_dom TYPE(gk) TYPE((ivl st, ivl st) dg_state)
     twice_ctx_eqs (cfg_exit twice_cfg, bot)"
  using twice_ctx_terminates
  unfolding TD_side_warrowing_apinis_Interp.term_equivalence
            TD_side_warrowing_apinis_Interp.solve_c_dom_def
  by simp

lemma twice_ctx_pp_st:
  "part_post_solution twice_ctx_eqs (cfg_exit twice_cfg, bot) (snd twice_ctx_sol) (fst twice_ctx_sol)"
  using TD_side_warrowing_apinis_Interp.partial_post_solution
          [OF twice_ctx_solve_dom, of "fst twice_ctx_sol" "snd twice_ctx_sol"]
  unfolding twice_ctx_sol_def by simp

subsection \<open>Transport to the abstract context-indexed D/G post-solution\<close>

text \<open>The generic bridge \<open>part_post_solution_seed_dg_st_to_abs\<close> carries the
  executable routed post-solution to the abstract one.  The three bundled
  obligations are \<open>ivl_Hstep\<close> (intra edges), \<open>dg_tree_st_commute_cmb\<close> (routed
  combine), and \<open>hextra_commute\<close> (frame read / routed enter publication) --- the
  latter two discharged \<^emph>\<open>solely\<close> from route consistency.\<close>

theorem twice_ctx_pp_abs:
  "part_post_solution
     (side_cfg_T_eff_keyed_seed_dg intra_predecessor_list (\<lambda>_. Global)
        (cmb_abs twice_cfg) (extra_abs twice_cfg) twice_cfg Sabs
        (fun_of_st (bot::ivl st)) (fun_of_st cinit_ivl_st) (fun_of_st (restrict_global_st cinit_ivl_st)))
     (cfg_exit twice_cfg, bot) (fun_of_dg_st \<circ> snd twice_ctx_sol) (fst twice_ctx_sol)"
  using part_post_solution_seed_dg_st_to_abs
          [OF ivl_Hstep dg_tree_st_commute_cmb hextra_commute
              twice_ctx_pp_st[unfolded twice_ctx_eqs_def Spoly_def]]
  by simp


end
