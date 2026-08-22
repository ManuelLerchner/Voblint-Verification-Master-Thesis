section \<open>The post-solution transport theorem\<close>

text \<open>
  The bridge itself: a partial post-solution of the executable equation system, read through
  \<open>fun_of_dg_st\<close>, is a partial post-solution of the abstract one over the same unknowns. Only
  the equation values transport --- unknown identity, the covered set and the dependencies are
  unchanged.

  Consumers import this theory for the whole stack; the three layers below it are separate
  files because they are separately readable, not because they are separately useful.
\<close>

theory Exec_DG_Bridge
  imports
    Exec_DG_Generator
begin
subsection \<open>Bundled per-tree transport relation\<close>

text \<open>
  \<open>dg_tree_st_commute \<sigma>_st t_st t_abs\<close> is the reusable transport contract for a
  single strategy tree: its executable denotation, its side-effect map, and its
  static dependencies all agree (through \<open>fun_of_dg_st\<close>) with the abstract tree
  read against the pushed-forward valuation \<open>fun_of_dg_st \<circ> \<sigma>_st\<close>.  It bundles
  the three commutation obligations the equation-system transport threads through
  the accumulator fold.

  The intra per-edge trees are discharged generically below from a componentwise
  analysis step.  The opaque \<open>cmb\<close>/\<open>extra\<close> trees --- whose \<^const>\<open>Side\<close> targets
  may be computed inside a \<^const>\<open>QueryL\<close>/\<^const>\<open>QueryG\<close> continuation (a routed
  callee seed) --- are supplied by the instance as bundled hypotheses; the bridge
  never assumes their side targets are syntactically fixed.

  The context is bound as \<open>ctx\<close>, never \<open>c\<close>: an unqualified \<open>c\<close> is captured by the
  imported constant \<open>state.c\<close>, which silently pins these theorems to a single
  context and produces a proof that only looks polymorphic.
\<close>

definition dg_tree_st_commute_for ::
  "(vname => bool)
   \<Rightarrow> ('u + 'k \<Rightarrow> (('a::bounded_semilattice_sup_bot) exec_dg_st, ('b::bounded_semilattice_sup_bot) exec_dg_st) dg_state)
   \<Rightarrow> ('u, 'k, ('a exec_dg_st, 'b exec_dg_st) dg_state) strategy_tree
   \<Rightarrow> ('u, 'k, ('a abs_state, 'b abs_state) dg_state) strategy_tree \<Rightarrow> bool"
where
  "dg_tree_st_commute_for gs \<sigma>_st t_st t_abs \<longleftrightarrow>
     fun_of_dg_st_for gs (traverse_rhs t_st \<sigma>_st) = traverse_rhs t_abs (fun_of_dg_st_for gs \<circ> \<sigma>_st)
   \<and> (\<forall>k. fun_of_dg_st_for gs (sides_of_rhs t_st \<sigma>_st k) = sides_of_rhs t_abs (fun_of_dg_st_for gs \<circ> \<sigma>_st) k)
   \<and> dep_aux \<sigma>_st t_st = dep_aux (fun_of_dg_st_for gs \<circ> \<sigma>_st) t_abs"

text \<open>The raw readback and its bundled per-tree relation are the generic engine at
  \<^const>\<open>fun_of_exec_dg_st_for\<close> on both halves, so every transport fact below is that
  engine's, instantiated rather than reproved.\<close>

lemma fun_of_dg_st_for_as_gen:
  "fun_of_dg_st_for gs = fun_of_dg_st_gen (fun_of_exec_dg_st_for gs) (fun_of_exec_dg_st_for gs)"
  by (rule ext) (simp add: fun_of_dg_st_for_def fun_of_dg_st_gen_def)

lemma dg_tree_st_commute_for_as_gen:
  "dg_tree_st_commute_for gs \<sigma>_st t_st t_abs
     \<longleftrightarrow> dg_reader_commute_gen.dg_tree_st_commute
           (fun_of_exec_dg_st_for gs) (fun_of_exec_dg_st_for gs) \<sigma>_st t_st t_abs"
proof -
  interpret R: dg_reader_commute_gen
    "fun_of_exec_dg_st_for gs" "fun_of_exec_dg_st_for gs"
    by unfold_locales simp_all
  show ?thesis
    by (simp add: dg_tree_st_commute_for_def R.dg_tree_st_commute_def fun_of_dg_st_for_as_gen)
qed



text \<open>The intra per-edge tree, relabelled by an arbitrary global key \<open>gk\<close> and
  local relabel \<open>lk\<close>, satisfies the bundled relation whenever the analysis step
  commutes componentwise.\<close>


lemma dg_tree_st_commute_wrapped_edge_for:
  assumes H: "\<And>d g. map_prod (fun_of_exec_dg_st_for gs) (fun_of_exec_dg_st_for gs) (step_st d g) = step_abs (fun_of_exec_dg_st_for gs d) (fun_of_exec_dg_st_for gs g)"
  shows "dg_tree_st_commute_for gs \<sigma>_st
           (map_gtree (\<lambda>_. gk) (map_ltree lk (dg_edge_tree step_st u)))
           (map_gtree (\<lambda>_. gk) (map_ltree lk (dg_edge_tree step_abs u)))"
  unfolding dg_tree_st_commute_for_def
  by (intro conjI allI
        traverse_wrapped_edge_commute_for[where step_st=step_st and step_abs=step_abs, OF H]
        sides_wrapped_edge_commute_for[where step_st=step_st and step_abs=step_abs, OF H]
        dep_aux_wrapped_edge_eq)





subsection \<open>The post-solution transport theorem\<close>

text \<open>
  A partial post-solution of the executable context-indexed D/G equation system,
  mapped value-wise through \<open>fun_of_dg_st\<close>, is a partial post-solution of the
  abstract system over the same unknown set --- unknown identity, \<open>vars\<close>, and
  dependencies are unchanged; only the equation values transport.  The routed
  combine and enter-seed trees transport through the bundled \<open>Hcmb\<close> / \<open>Hextra\<close>
  hypotheses, so the dynamic \<^const>\<open>Side\<close> targets are carried over faithfully.
\<close>


theorem part_post_solution_seed_dg_st_to_abs_for:
  assumes Hstep: "\<And>a d g'. map_prod (fun_of_exec_dg_st_for gs) (fun_of_exec_dg_st_for gs) (dg_spec_step S_st a d g')
                           = dg_spec_step S_abs a (fun_of_exec_dg_st_for gs d) (fun_of_exec_dg_st_for gs g')"
      and Hroute: "\<And>u c' d ca. route_st u c' d ca = route_abs u c' (fun_of_exec_dg_st_for gs d) ca"
      and Hcmb: "\<And>c' ca cc ex. dg_tree_st_commute_for gs \<sigma>_st (cmb_st route_st c' ca cc ex) (cmb_abs route_abs c' ca cc ex)"
      and Hextra: "\<And>c' w. list_all2 (dg_tree_st_commute_for gs \<sigma>_st) (extra_st route_st c' w) (extra_abs route_abs c' w)"
      and pp: "part_post_solution
                 (side_cfg_T_eff_keyed_seed_dg pred_sel gkey route_st cmb_st extra_st g S_st bot0 s0d s0g) x \<sigma>_st vars"
  shows "part_post_solution
           (side_cfg_T_eff_keyed_seed_dg pred_sel gkey route_abs cmb_abs extra_abs g S_abs
              (fun_of_exec_dg_st_for gs bot0) (fun_of_exec_dg_st_for gs s0d) (fun_of_exec_dg_st_for gs s0g)) x (fun_of_dg_st_for gs \<circ> \<sigma>_st) vars"
proof -
  interpret R: dg_reader_commute_gen
    "fun_of_exec_dg_st_for gs" "fun_of_exec_dg_st_for gs"
    by unfold_locales simp_all
  have Hcmb': "\<And>c' ca cc ex. R.dg_tree_st_commute \<sigma>_st (cmb_st route_st c' ca cc ex) (cmb_abs route_abs c' ca cc ex)"
    using Hcmb by (simp add: dg_tree_st_commute_for_as_gen)
  have Hextra': "\<And>c' w. list_all2 (R.dg_tree_st_commute \<sigma>_st) (extra_st route_st c' w) (extra_abs route_abs c' w)"
    by (rule list_all2_mono[OF Hextra]) (simp add: dg_tree_st_commute_for_as_gen)
  show ?thesis
    unfolding fun_of_dg_st_for_as_gen
    by (rule R.part_post_solution_seed_dg_st_to_abs
          [where pred_sel=pred_sel and gkey=gkey and route_st=route_st and route_abs=route_abs
             and cmb_st=cmb_st and cmb_abs=cmb_abs and extra_st=extra_st and extra_abs=extra_abs
             and g=g and S_st=S_st and S_abs=S_abs, OF Hstep Hroute Hcmb' Hextra' pp])
qed

text \<open>
  The reachability-lifted instance of the same post-solution transport, proved as a
  corollary of \<open>dg_reader_commute_gen\<close> at the lifted readback
  \<open>map_lift (fun_of_resolved_st_q_for gs)\<close> rather than by re-running the whole-CFG proof
  chain a second time.
\<close>

theorem part_post_solution_seed_dg_st_to_abs_lifted_for:
  assumes Hstep: "\<And>a d g'. map_prod (map_lift (fun_of_resolved_st_q_for gs)) (map_lift (fun_of_resolved_st_q_for gs))
                              (dg_spec_step S_st a d g')
                           = dg_spec_step S_abs a (map_lift (fun_of_resolved_st_q_for gs) d) (map_lift (fun_of_resolved_st_q_for gs) g')"
      and Hroute: "\<And>u c' d ca. route_st u c' d ca = route_abs u c' (map_lift (fun_of_resolved_st_q_for gs) d) ca"
      and Hcmb: "\<And>c' ca cc ex. dg_reader_commute_gen.dg_tree_st_commute
                       (map_lift (fun_of_resolved_st_q_for gs)) (map_lift (fun_of_resolved_st_q_for gs)) \<sigma>_st
                       (cmb_st route_st c' ca cc ex) (cmb_abs route_abs c' ca cc ex)"
      and Hextra: "\<And>c' w. list_all2 (dg_reader_commute_gen.dg_tree_st_commute
                       (map_lift (fun_of_resolved_st_q_for gs)) (map_lift (fun_of_resolved_st_q_for gs)) \<sigma>_st)
                     (extra_st route_st c' w) (extra_abs route_abs c' w)"
      and pp: "part_post_solution
                 (side_cfg_T_eff_keyed_seed_dg pred_sel gkey route_st cmb_st extra_st g S_st bot0 s0d s0g) x \<sigma>_st vars"
  shows "part_post_solution
           (side_cfg_T_eff_keyed_seed_dg pred_sel gkey route_abs cmb_abs extra_abs g S_abs
              (map_lift (fun_of_resolved_st_q_for gs) bot0) (map_lift (fun_of_resolved_st_q_for gs) s0d)
              (map_lift (fun_of_resolved_st_q_for gs) s0g))
           x (fun_of_dg_st_gen (map_lift (fun_of_resolved_st_q_for gs)) (map_lift (fun_of_resolved_st_q_for gs)) \<circ> \<sigma>_st) vars"
proof -
  interpret R: dg_reader_commute_gen
    "map_lift (fun_of_resolved_st_q_for gs)" "map_lift (fun_of_resolved_st_q_for gs)"
    by unfold_locales (simp_all add: map_lift_sup fun_of_resolved_st_q_for_sup)
  show ?thesis
    by (rule R.part_post_solution_seed_dg_st_to_abs
          [where pred_sel=pred_sel and gkey=gkey and route_st=route_st and route_abs=route_abs
             and cmb_st=cmb_st and cmb_abs=cmb_abs and extra_st=extra_st and extra_abs=extra_abs
             and g=g and S_st=S_st and S_abs=S_abs, OF Hstep Hroute Hcmb Hextra pp])
qed



subsection \<open>The monovariant (unit-context) specialisation\<close>

text \<open>\<^const>\<open>dg_spec_combine_tree\<close> applies the caller continuation itself, so the
  operator whose commutation these proofs need is \<open>combine\<close> after \<open>caller_cont\<close>,
  not \<open>combine\<close> alone.  \<open>Hcont\<close> is the executable/abstract commute for that
  caller half; the two hypotheses compose into \<open>Hcomb'\<close> below.\<close>

lemma dg_tree_st_commute_dg_cmb_of_for:
  assumes Hcomb: "\<And>ci dc de g. map_prod (fun_of_exec_dg_st_for gs) (fun_of_exec_dg_st_for gs) (dgs_combine S_st ci dc de g)
                            = dgs_combine S_abs ci (fun_of_exec_dg_st_for gs dc) (fun_of_exec_dg_st_for gs de) (fun_of_exec_dg_st_for gs g)"
    and Hcont: "\<And>ci d g. fun_of_exec_dg_st_for gs (caller_cont S_st ci d g)
                            = caller_cont S_abs ci (fun_of_exec_dg_st_for gs d) (fun_of_exec_dg_st_for gs g)"
  shows "dg_tree_st_commute_for gs \<sigma>_st (dg_cmb_of S_st (\<lambda>_ _ _ _. ()) c' (CallEdge dst fs as) cc ex)
                                  (dg_cmb_of S_abs (\<lambda>_ _ _ _. ()) c' (CallEdge dst fs as) cc ex)"
proof -
  have Hcomb': "\<And>ci dc de g. map_prod (fun_of_exec_dg_st_for gs) (fun_of_exec_dg_st_for gs)
        (dgs_combine S_st ci (caller_cont S_st ci dc g) de g)
      = dgs_combine S_abs ci (caller_cont S_abs ci (fun_of_exec_dg_st_for gs dc) (fun_of_exec_dg_st_for gs g))
          (fun_of_exec_dg_st_for gs de) (fun_of_exec_dg_st_for gs g)"
    by (simp add: Hcomb Hcont)
  show ?thesis
    unfolding dg_tree_st_commute_for_def dg_cmb_of_def dg_spec_combine_tree_def
    apply simp
    apply (intro conjI allI
          traverse_wrapped_combine_commute_for
            [where comb_st = "\<lambda>ci' dc de g. dgs_combine S_st ci' (caller_cont S_st ci' dc g) de g"
               and comb_abs = "\<lambda>ci' dc de g. dgs_combine S_abs ci' (caller_cont S_abs ci' dc g) de g",
             OF Hcomb']
          sides_wrapped_combine_commute_for
            [where comb_st = "\<lambda>ci' dc de g. dgs_combine S_st ci' (caller_cont S_st ci' dc g) de g"
               and comb_abs = "\<lambda>ci' dc de g. dgs_combine S_abs ci' (caller_cont S_abs ci' dc g) de g",
             OF Hcomb']
          dep_aux_wrapped_combine_eq)
    done
qed

lemma dg_extra_of_commute_for:
  assumes Henter:
    "\<And>xs es d g. map_prod (fun_of_exec_dg_st_for gs) (fun_of_exec_dg_st_for gs) (dgs_enter S_st xs es d g)
      = dgs_enter S_abs xs es (fun_of_exec_dg_st_for gs d) (fun_of_exec_dg_st_for gs g)"
  shows "list_all2 (dg_tree_st_commute_for gs \<sigma>_st)
      (dg_extra_of S_st g (\<lambda>_ _ _ _. ()) c' w) (dg_extra_of S_abs g (\<lambda>_ _ _ _. ()) c' w)"
  unfolding dg_extra_of_def
  by (auto simp: list_all2_map1 list_all2_map2 Henter
      split: call_action.splits
      intro!: list_all2_refl dg_tree_st_commute_wrapped_edge_for)

theorem part_post_solution_dg_st_to_abs_for:
  assumes Hstep: "\<And>a d g. map_prod (fun_of_exec_dg_st_for gs) (fun_of_exec_dg_st_for gs) (dg_spec_step S_st a d g)
                          = dg_spec_step S_abs a (fun_of_exec_dg_st_for gs d) (fun_of_exec_dg_st_for gs g)"
      and Henter: "\<And>xs es d g. map_prod (fun_of_exec_dg_st_for gs) (fun_of_exec_dg_st_for gs) (dgs_enter S_st xs es d g)
                            = dgs_enter S_abs xs es (fun_of_exec_dg_st_for gs d) (fun_of_exec_dg_st_for gs g)"
      and Hcomb: "\<And>ci dc de g. map_prod (fun_of_exec_dg_st_for gs) (fun_of_exec_dg_st_for gs) (dgs_combine S_st ci dc de g)
                            = dgs_combine S_abs ci (fun_of_exec_dg_st_for gs dc) (fun_of_exec_dg_st_for gs de) (fun_of_exec_dg_st_for gs g)"
      and Hcont: "\<And>ci d g. fun_of_exec_dg_st_for gs (caller_cont S_st ci d g)
                            = caller_cont S_abs ci (fun_of_exec_dg_st_for gs d) (fun_of_exec_dg_st_for gs g)"
      and pp: "part_post_solution (dg_gen_of S_st g bot0 s0d s0g) x \<sigma>_st vars"
  shows "part_post_solution (dg_gen_of S_abs g (fun_of_exec_dg_st_for gs bot0) (fun_of_exec_dg_st_for gs s0d) (fun_of_exec_dg_st_for gs s0g))
           x (fun_of_dg_st_for gs \<circ> \<sigma>_st) vars"
proof -
  have hr: "\<And>u c' d ca. (\<lambda>_ _ _ _. ()) u c' d ca = (\<lambda>_ _ _ _. ()) u c' (fun_of_exec_dg_st_for gs d) ca"
    by simp
  have hc: "\<And>c' ca cc ex. dg_tree_st_commute_for gs \<sigma>_st
      (dg_cmb_of S_st (\<lambda>_ _ _ _. ()) c' ca cc ex) (dg_cmb_of S_abs (\<lambda>_ _ _ _. ()) c' ca cc ex)"
  proof -
    fix c' ca cc ex
    obtain dst fs as where ca_eq: "ca = CallEdge dst fs as" by (cases ca) auto
    thus "dg_tree_st_commute_for gs \<sigma>_st
        (dg_cmb_of S_st (\<lambda>_ _ _ _. ()) c' ca cc ex) (dg_cmb_of S_abs (\<lambda>_ _ _ _. ()) c' ca cc ex)"
      by (simp add: dg_tree_st_commute_dg_cmb_of_for[OF Hcomb Hcont])
  qed
  have he: "\<And>c' w. list_all2 (dg_tree_st_commute_for gs \<sigma>_st)
      (dg_extra_of S_st g (\<lambda>_ _ _ _. ()) c' w) (dg_extra_of S_abs g (\<lambda>_ _ _ _. ()) c' w)"
    by (rule dg_extra_of_commute_for[OF Henter])
  from pp have pp':
    "part_post_solution
      (side_cfg_T_eff_keyed_seed_dg intra_predecessor_list (\<lambda>_. ()) (\<lambda>_ _ _ _. ())
        (dg_cmb_of S_st) (dg_extra_of S_st g) g S_st bot0 s0d s0g) x \<sigma>_st vars"
    unfolding dg_gen_of_def .
  show ?thesis
    unfolding dg_gen_of_def
    by (rule part_post_solution_seed_dg_st_to_abs_for
          [where pred_sel = intra_predecessor_list and gkey = "\<lambda>_. ()"
             and route_st = "\<lambda>_ _ _ _. ()" and route_abs = "\<lambda>_ _ _ _. ()"
             and cmb_st = "dg_cmb_of S_st" and cmb_abs = "dg_cmb_of S_abs"
             and extra_st = "dg_extra_of S_st g" and extra_abs = "dg_extra_of S_abs g",
           OF Hstep hr hc he pp'])
qed

subsection \<open>The monovariant (unit-context) specialisation, lifted\<close>

text \<open>
  The lifted analogues of the diagonal monovariant lemmas above. Each cites the
  generic \<open>dg_reader_commute_gen\<close> facts at the lifted readback
  \<open>map_lift (fun_of_resolved_st_q_for gs)\<close> instead of re-deriving the tree-commute
  reasoning, mirroring the diagonal proofs at the reachability-lifted local carrier.
\<close>

lemma dg_tree_st_commute_dg_cmb_of_lifted_for:
  assumes Hcomb: "\<And>ci dc de g. map_prod (map_lift (fun_of_resolved_st_q_for gs)) (map_lift (fun_of_resolved_st_q_for gs))
                            (dgs_combine S_st ci dc de g)
                          = dgs_combine S_abs ci (map_lift (fun_of_resolved_st_q_for gs) dc)
                              (map_lift (fun_of_resolved_st_q_for gs) de) (map_lift (fun_of_resolved_st_q_for gs) g)"
    and Hcont: "\<And>ci d g. map_lift (fun_of_resolved_st_q_for gs) (caller_cont S_st ci d g)
                          = caller_cont S_abs ci (map_lift (fun_of_resolved_st_q_for gs) d)
                              (map_lift (fun_of_resolved_st_q_for gs) g)"
  shows "dg_reader_commute_gen.dg_tree_st_commute
           (map_lift (fun_of_resolved_st_q_for gs)) (map_lift (fun_of_resolved_st_q_for gs)) \<sigma>_st
           (dg_cmb_of S_st (\<lambda>_ _ _ _. ()) c' (CallEdge dst fs as) cc ex)
           (dg_cmb_of S_abs (\<lambda>_ _ _ _. ()) c' (CallEdge dst fs as) cc ex)"
proof -
  interpret R: dg_reader_commute_gen
    "map_lift (fun_of_resolved_st_q_for gs)" "map_lift (fun_of_resolved_st_q_for gs)"
    by unfold_locales (simp_all add: map_lift_sup fun_of_resolved_st_q_for_sup)
  have Hcomb': "\<And>ci dc de g. map_prod (map_lift (fun_of_resolved_st_q_for gs)) (map_lift (fun_of_resolved_st_q_for gs))
        (dgs_combine S_st ci (caller_cont S_st ci dc g) de g)
      = dgs_combine S_abs ci
          (caller_cont S_abs ci (map_lift (fun_of_resolved_st_q_for gs) dc) (map_lift (fun_of_resolved_st_q_for gs) g))
          (map_lift (fun_of_resolved_st_q_for gs) de) (map_lift (fun_of_resolved_st_q_for gs) g)"
    by (simp add: Hcomb Hcont)
  show ?thesis
    unfolding dg_cmb_of_def dg_spec_combine_tree_def
    apply simp
    apply (rule R.dg_tree_st_commute_wrapped_combine
            [where comb_st = "\<lambda>ci' dc de g. dgs_combine S_st ci' (caller_cont S_st ci' dc g) de g"
               and comb_abs = "\<lambda>ci' dc de g. dgs_combine S_abs ci' (caller_cont S_abs ci' dc g) de g",
             OF Hcomb'])
    done
qed

lemma dg_extra_of_commute_lifted_for:
  assumes Henter:
    "\<And>xs es d g. map_prod (map_lift (fun_of_resolved_st_q_for gs)) (map_lift (fun_of_resolved_st_q_for gs)) (dgs_enter S_st xs es d g)
      = dgs_enter S_abs xs es (map_lift (fun_of_resolved_st_q_for gs) d) (map_lift (fun_of_resolved_st_q_for gs) g)"
  shows "list_all2 (dg_reader_commute_gen.dg_tree_st_commute
             (map_lift (fun_of_resolved_st_q_for gs)) (map_lift (fun_of_resolved_st_q_for gs)) \<sigma>_st)
      (dg_extra_of S_st g (\<lambda>_ _ _ _. ()) c' w) (dg_extra_of S_abs g (\<lambda>_ _ _ _. ()) c' w)"
proof -
  interpret R: dg_reader_commute_gen
    "map_lift (fun_of_resolved_st_q_for gs)" "map_lift (fun_of_resolved_st_q_for gs)"
    by unfold_locales (simp_all add: map_lift_sup fun_of_resolved_st_q_for_sup)
  show ?thesis
    unfolding dg_extra_of_def
    by (auto simp: list_all2_map1 list_all2_map2 Henter
        split: call_action.splits
        intro!: list_all2_refl R.dg_tree_st_commute_wrapped_edge)
qed

theorem part_post_solution_dg_st_to_abs_lifted_for:
  assumes Hstep: "\<And>a d g. map_prod (map_lift (fun_of_resolved_st_q_for gs)) (map_lift (fun_of_resolved_st_q_for gs))
                          (dg_spec_step S_st a d g)
                        = dg_spec_step S_abs a (map_lift (fun_of_resolved_st_q_for gs) d) (map_lift (fun_of_resolved_st_q_for gs) g)"
      and Henter: "\<And>xs es d g. map_prod (map_lift (fun_of_resolved_st_q_for gs)) (map_lift (fun_of_resolved_st_q_for gs))
                            (dgs_enter S_st xs es d g)
                          = dgs_enter S_abs xs es (map_lift (fun_of_resolved_st_q_for gs) d) (map_lift (fun_of_resolved_st_q_for gs) g)"
      and Hcomb: "\<And>ci dc de g. map_prod (map_lift (fun_of_resolved_st_q_for gs)) (map_lift (fun_of_resolved_st_q_for gs))
                            (dgs_combine S_st ci dc de g)
                          = dgs_combine S_abs ci (map_lift (fun_of_resolved_st_q_for gs) dc)
                              (map_lift (fun_of_resolved_st_q_for gs) de) (map_lift (fun_of_resolved_st_q_for gs) g)"
      and Hcont: "\<And>ci d g. map_lift (fun_of_resolved_st_q_for gs) (caller_cont S_st ci d g)
                          = caller_cont S_abs ci (map_lift (fun_of_resolved_st_q_for gs) d)
                              (map_lift (fun_of_resolved_st_q_for gs) g)"
      and pp: "part_post_solution (dg_gen_of S_st g bot0 s0d s0g) x \<sigma>_st vars"
  shows "part_post_solution (dg_gen_of S_abs g (map_lift (fun_of_resolved_st_q_for gs) bot0)
                               (map_lift (fun_of_resolved_st_q_for gs) s0d) (map_lift (fun_of_resolved_st_q_for gs) s0g))
           x (fun_of_dg_st_gen (map_lift (fun_of_resolved_st_q_for gs)) (map_lift (fun_of_resolved_st_q_for gs)) \<circ> \<sigma>_st) vars"
proof -
  have hr: "\<And>u c' d ca. (\<lambda>_ _ _ _. ()) u c' d ca = (\<lambda>_ _ _ _. ()) u c' (map_lift (fun_of_resolved_st_q_for gs) d) ca"
    by simp
  have hc: "\<And>c' ca cc ex. dg_reader_commute_gen.dg_tree_st_commute
      (map_lift (fun_of_resolved_st_q_for gs)) (map_lift (fun_of_resolved_st_q_for gs)) \<sigma>_st
      (dg_cmb_of S_st (\<lambda>_ _ _ _. ()) c' ca cc ex) (dg_cmb_of S_abs (\<lambda>_ _ _ _. ()) c' ca cc ex)"
  proof -
    fix c' ca cc ex
    obtain dst fs as where ca_eq: "ca = CallEdge dst fs as" by (cases ca) auto
    thus "dg_reader_commute_gen.dg_tree_st_commute
        (map_lift (fun_of_resolved_st_q_for gs)) (map_lift (fun_of_resolved_st_q_for gs)) \<sigma>_st
        (dg_cmb_of S_st (\<lambda>_ _ _ _. ()) c' ca cc ex) (dg_cmb_of S_abs (\<lambda>_ _ _ _. ()) c' ca cc ex)"
      by (simp add: dg_tree_st_commute_dg_cmb_of_lifted_for[OF Hcomb Hcont])
  qed
  have he: "\<And>c' w. list_all2 (dg_reader_commute_gen.dg_tree_st_commute
      (map_lift (fun_of_resolved_st_q_for gs)) (map_lift (fun_of_resolved_st_q_for gs)) \<sigma>_st)
      (dg_extra_of S_st g (\<lambda>_ _ _ _. ()) c' w) (dg_extra_of S_abs g (\<lambda>_ _ _ _. ()) c' w)"
    by (rule dg_extra_of_commute_lifted_for[OF Henter])
  from pp have pp':
    "part_post_solution
      (side_cfg_T_eff_keyed_seed_dg intra_predecessor_list (\<lambda>_. ()) (\<lambda>_ _ _ _. ())
        (dg_cmb_of S_st) (dg_extra_of S_st g) g S_st bot0 s0d s0g) x \<sigma>_st vars"
    unfolding dg_gen_of_def .
  show ?thesis
    unfolding dg_gen_of_def
    by (rule part_post_solution_seed_dg_st_to_abs_lifted_for
          [where pred_sel = intra_predecessor_list and gkey = "\<lambda>_. ()"
             and route_st = "\<lambda>_ _ _ _. ()" and route_abs = "\<lambda>_ _ _ _. ()"
             and cmb_st = "dg_cmb_of S_st" and cmb_abs = "dg_cmb_of S_abs"
             and extra_st = "dg_extra_of S_st g" and extra_abs = "dg_extra_of S_abs g",
           OF Hstep hr hc he pp'])
qed




end
