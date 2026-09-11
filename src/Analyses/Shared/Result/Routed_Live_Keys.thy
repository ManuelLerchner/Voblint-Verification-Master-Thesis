theory Routed_Live_Keys
  imports Routed_DG_Analysis "Voblint_Compile.Live_Nodes"
begin

section \<open>Which solved keys a terminating solve is closed on\<close>

text \<open>
  The key set a terminating solve returns is not one the soundness argument can use as it
  stands: it may hold keys the solver queried under an earlier value and no longer reads,
  and keys inside code no execution reaches.  \<open>live_keys\<close> keeps a solved key when its
  node is live in a procedure (\<^theory>\<open>Voblint_Compile.Live_Nodes\<close>) whose result is
  solved at the same context.  From what each generated equation reads under the final
  valuation, \<open>live_keys_cover\<close> shows that set closed under every intra edge, every call
  continuation and every call that enters a live state, with no premise beyond termination
  and a well-formed program.  The endpoints below restate the routed soundness over these
  keys and carry it to the published table.
\<close>

subsection \<open>What a routed equation reads\<close>

lemma dep_aux_routed_node_rhs:
  "dep_aux \<tau> (routed_node_rhs pred_sel gkey route it cmb extra g bot0 s0d s0g (v, cx))
     = (\<Union>t\<in>set (routed_contribution_trees pred_sel route it cmb extra g cx v). dep_aux \<tau> t)"
  by (cases "v = cfg_entry g")
     (simp_all add: routed_node_rhs_def Let_def dep_aux_side_rhs_fold_dg_char)

lemma dep_L_routed_node_rhs_intra:
  assumes fin: "finite (intra g)" and e: "(u, a, v) \<in> intra g"
  shows "(u, cx) \<in> dep\<^sub>L (routed_node_rhs intra_predecessor_addr_list gkey route
            (\<lambda>cx src a. dg_spec_edge_tree S a src slot) cmb extra g bot0 s0d s0g) \<tau> (v, cx)"
proof -
  have "dg_spec_edge_tree S a (Inl (u, cx)) slot
          \<in> set (routed_contribution_trees intra_predecessor_addr_list route
                   (\<lambda>cx src a. dg_spec_edge_tree S a src slot) cmb extra g cx v)"
    using e fin
    by (force simp: routed_contribution_trees_def intra_predecessor_addr_list_def
        intra_predecessors_def)
  then show ?thesis
    unfolding dep\<^sub>L_def dep_def
    using dep_aux_dg_spec_edge_tree_source[of "Inl (u, cx)" \<tau> S a slot]
    by (auto simp: dep_aux_routed_node_rhs)
qed

lemma dep_aux_routed_call_tree:
  "dep_aux \<tau> (routed_call_tree S gk0 seed_key resolve is_bot route ctx ca cc v)
     = insert (Inl (cc, ctx))
         (\<Union>q\<in>set (resolve v cc ca (locals (\<tau> (Inl (cc, ctx))))).
            dep_aux \<tau> (routed_callee_call_tree S gk0 seed_key route is_bot ctx ca cc
                        (locals (\<tau> (Inl (cc, ctx)))) q))"
  by (simp add: routed_call_tree_def dep_aux_side_rhs_fold_dg_char)

lemma routed_call_tree_mem:
  assumes fin: "finite (calls g)" and e: "(u, ca, FunctionEntry q, k) \<in> calls g"
  shows "routed_call_tree S gk0 seed_key resolve is_bot route cx ca u k
           \<in> set (routed_contribution_trees pred_sel route it
                    (routed_call_tree S gk0 seed_key resolve is_bot) extra g cx k)"
proof -
  have "(u, ca) \<in> set (call_site_list g k)" using e fin by auto
  then show ?thesis by (rule routed_contribution_trees_combineI)
qed

lemma dep_L_routed_node_rhs_call_site:
  assumes fin: "finite (calls g)" and e: "(u, ca, FunctionEntry q, k) \<in> calls g"
  shows "(u, cx) \<in> dep\<^sub>L (routed_node_rhs pred_sel gkey route it
            (routed_call_tree S gk0 seed_key resolve is_bot) extra g bot0 s0d s0g) \<tau> (k, cx)"
proof -
  have "Inl (u, cx) \<in> dep_aux \<tau> (routed_call_tree S gk0 seed_key resolve is_bot route cx ca u k)"
    by (simp add: dep_aux_routed_call_tree)
  then show ?thesis
    unfolding dep\<^sub>L_def dep_def
    using routed_call_tree_mem
            [OF fin e, of S gk0 seed_key resolve is_bot route cx pred_sel it extra]
    by (auto simp: dep_aux_routed_node_rhs)
qed

lemma dep_L_routed_node_rhs_callee_result:
  fixes f :: "'d::bounded_semilattice_sup_bot \<Rightarrow> 'd"
  assumes fin: "finite (calls g)" and e: "(u, ca, FunctionEntry q, k) \<in> calls g"
    and enter: "enter\<^sup># S (call_info_of ca q) = local_enter_transfer (\<lambda>d. [(d, f d)])"
    and res: "q \<in> set (resolve k u ca (locals (\<tau> (Inl (u, cx)))))"
    and nb: "\<not> is_bot (f (locals (\<tau> (Inl (u, cx)))))"
  shows "(FunctionResult q, route u cx (f (locals (\<tau> (Inl (u, cx))))) ca)
           \<in> dep\<^sub>L (routed_node_rhs pred_sel gkey route it
                (routed_call_tree S gk0 seed_key resolve is_bot) extra g bot0 s0d s0g) \<tau> (k, cx)"
proof -
  let ?d = "locals (\<tau> (Inl (u, cx)))"
  have callee: "dep_aux \<tau> (routed_callee_call_tree S gk0 seed_key route is_bot cx ca u ?d q)
      = dep_aux \<tau> (sp_compile (side_rhs_fold_dg bot
          (map (routed_call_alternative_tree S gk0 seed_key route is_bot cx ca u q)
             [(?d, f ?d)])))"
    unfolding routed_callee_call_tree_def enter
    by (rule enter_depsD[OF enter_deps_local_enter_transfer_mk_dg_man, simplified])
  have "Inl (FunctionResult q, route u cx (f ?d) ca)
          \<in> dep_aux \<tau> (routed_callee_call_tree S gk0 seed_key route is_bot cx ca u ?d q)"
  proof -
    have "Inl (FunctionResult q, route u cx (f ?d) ca)
            \<in> dep_aux \<tau> (routed_call_alternative_tree S gk0 seed_key route is_bot cx ca u q
                           (?d, f ?d))"
      using nb by (simp add: routed_call_alternative_tree_def Let_def)
    then show ?thesis unfolding callee dep_aux_side_rhs_fold_dg_char by simp
  qed
  then have "Inl (FunctionResult q, route u cx (f ?d) ca)
               \<in> dep_aux \<tau> (routed_call_tree S gk0 seed_key resolve is_bot route cx ca u k)"
    using res by (auto simp: dep_aux_routed_call_tree)
  then show ?thesis
    unfolding dep\<^sub>L_def dep_def
    using routed_call_tree_mem
            [OF fin e, of S gk0 seed_key resolve is_bot route cx pred_sel it extra]
    by (auto simp: dep_aux_routed_node_rhs)
qed

subsection \<open>Keys of a solve whose activation returned\<close>

context routed_dg_analysis
begin

lemma analysis_spec_enter:
  "enter\<^sup># (analysis_spec gs p) ci
     = local_enter_transfer
         (\<lambda>d. [(d, transfer_lift (resolved_st_q_is_bot_for (declared_global_vars p))
                   (enter_st gs ci) d)])"
  by (simp add: analysis_spec_def local_state_dg_spec_st_for_lifted_def local_dg_spec_def)

lemma sol_vars_dep_closed:
  assumes solves: "terminates (declared_global p) p"
    and x: "x \<in> sol_vars (declared_global p) p"
    and y: "y \<in> dep\<^sub>L
       (routed_node_rhs intra_predecessor_addr_list (\<lambda>_. gk0) (route (declared_global p))
          (\<lambda>ctx' src a. dg_spec_edge_tree (analysis_spec (declared_global p) p) a src (\<lambda>_. gk0))
          (routed_call_tree (analysis_spec (declared_global p) p) gk0 seed
             (static_resolve (prog_cfg p)) (\<lambda>d. d = Bot))
          (routed_entry_seed_tree seed)
          (prog_cfg p) Bot (Lifted init_st) Bot)
       (sol_env (declared_global p) p) x"
  shows "y \<in> sol_vars (declared_global p) p"
  using pp_routed[OF solves] x y by blast

lemma prog_cfg_finite: "finite (intra (prog_cfg p))" "finite (calls (prog_cfg p))"
  unfolding prog_cfg_def using compile_prog_finite by simp_all

lemma sol_vars_back_intra:
  assumes solves: "terminates (declared_global p) p"
    and v: "(v, cx) \<in> sol_vars (declared_global p) p" and e: "(u, a, v) \<in> intra (prog_cfg p)"
  shows "(u, cx) \<in> sol_vars (declared_global p) p"
  by (rule sol_vars_dep_closed[OF solves v dep_L_routed_node_rhs_intra[OF prog_cfg_finite(1) e]])

lemma sol_vars_back_call_site:
  assumes solves: "terminates (declared_global p) p"
    and k: "(k, cx) \<in> sol_vars (declared_global p) p"
    and e: "(u, ca, FunctionEntry q, k) \<in> calls (prog_cfg p)"
  shows "(u, cx) \<in> sol_vars (declared_global p) p"
  by (rule sol_vars_dep_closed
        [OF solves k dep_L_routed_node_rhs_call_site[OF prog_cfg_finite(2) e]])

lemma sol_vars_callee_result:
  assumes solves: "terminates (declared_global p) p"
    and k: "(k, cx) \<in> sol_vars (declared_global p) p"
    and e: "(u, ca, FunctionEntry q, k) \<in> calls (prog_cfg p)"
    and nb: "transfer_lift (resolved_st_q_is_bot_for (declared_global_vars p))
               (enter_st (declared_global p) (call_info_of ca q))
               (locals (sol_env (declared_global p) p (Inl (u, cx)))) \<noteq> Bot"
  shows "(FunctionResult q, ctx_succ (declared_global p) p u cx ca q)
           \<in> sol_vars (declared_global p) p"
proof -
  have res: "q \<in> set (static_resolve (prog_cfg p) k u ca
                        (locals (sol_env (declared_global p) p (Inl (u, cx)))))"
    using e prog_cfg_finite(2) by simp
  show ?thesis
    unfolding ctx_succ_def
    by (rule sol_vars_dep_closed[OF solves k],
        rule dep_L_routed_node_rhs_callee_result[where resolve = "static_resolve (prog_cfg p)"
            and \<tau> = "sol_env (declared_global p) p" and cx = cx,
          OF prog_cfg_finite(2) e analysis_spec_enter[of "declared_global p" p] res])
       (use nb in simp)
qed

lemma sol_vars_back_reach:
  assumes solves: "terminates (declared_global p) p"
    and w: "(w, cx) \<in> sol_vars (declared_global p) p"
    and r: "local_reaches (prog_cfg p) y w"
  shows "(y, cx) \<in> sol_vars (declared_global p) p"
  using r[unfolded local_reaches_def]
proof (induction rule: converse_rtrancl_induct)
  case base show ?case by (rule w)
next
  case (step y z)
  from step.hyps(1) show ?case
    unfolding local_succ_rel_def
    using sol_vars_back_intra[OF solves step.IH] sol_vars_back_call_site[OF solves step.IH]
    by blast
qed

definition live_keys :: "imp_prog \<Rightarrow> (pp \<times> 'c) set" where
  "live_keys p =
     {(u, cx) \<in> sol_vars (declared_global p) p.
        \<exists>q. prog_live (prog_table p) (prog_procs p) q u
          \<and> (FunctionResult q, cx) \<in> sol_vars (declared_global p) p}"

lemma live_keys_sub: "live_keys p \<subseteq> sol_vars (declared_global p) p"
  unfolding live_keys_def by blast

lemma live_keys_of_result:
  assumes wf: "wf_program_compile_input p" and solves: "terminates (declared_global p) p"
    and live: "prog_live (prog_table p) (prog_procs p) q y"
    and r: "(FunctionResult q, cx) \<in> sol_vars (declared_global p) p"
  shows "(y, cx) \<in> live_keys p"
proof -
  have "local_reaches (prog_cfg p) y (FunctionResult q)"
    unfolding prog_cfg_def by (rule prog_live_reaches[OF live])
  then have "(y, cx) \<in> sol_vars (declared_global p) p" by (rule sol_vars_back_reach[OF solves r])
  then show ?thesis unfolding live_keys_def using live r by blast
qed

theorem live_keys_cover:
  assumes wf: "wf_program_compile_input p" and solves: "terminates (declared_global p) p"
  shows "ctx_vars_cover_live (prog_cfg p) (\<lambda>_ _. True) (live_succ (declared_global p) p)
           root_ctx (live_keys p)"
proof (rule ctx_vars_cover_liveI)
  have root: "(FunctionResult prog_main_name, root_ctx) \<in> sol_vars (declared_global p) p"
    using pp_routed[OF solves] by (simp add: root_query_def prog_cfg_def)
  show "(cfg_entry (prog_cfg p), root_ctx) \<in> live_keys p"
    using live_keys_of_result[OF wf solves prog_live_main_entry[OF wf] root]
    by (simp add: prog_cfg_def)
next
  fix u a v ctx
  assume u: "(u, ctx) \<in> live_keys p" and e: "(u, a, v) \<in> intra (prog_cfg p)"
  from u obtain q where lq: "prog_live (prog_table p) (prog_procs p) q u"
    and r: "(FunctionResult q, ctx) \<in> sol_vars (declared_global p) p"
    unfolding live_keys_def by blast
  have "prog_live (prog_table p) (prog_procs p) q v"
    using prog_live_intra[OF wf lq] e by (simp add: prog_cfg_def)
  then show "(v, ctx) \<in> live_keys p" by (rule live_keys_of_result[OF wf solves _ r])
next
  fix u ctx dst fs as q k
  assume u: "(u, ctx) \<in> live_keys p"
    and e: "(u, CallEdge dst fs as, FunctionEntry q, k) \<in> calls (prog_cfg p)"
  from u obtain r where lr: "prog_live (prog_table p) (prog_procs p) r u"
    and res: "(FunctionResult r, ctx) \<in> sol_vars (declared_global p) p"
    unfolding live_keys_def by blast
  have "prog_live (prog_table p) (prog_procs p) r k"
    using prog_live_calls[OF wf lr] e by (simp add: prog_cfg_def)
  then show "(k, ctx) \<in> live_keys p" by (rule live_keys_of_result[OF wf solves _ res])
next
  fix u ctx dst fs as q k ctx'
  assume u: "(u, ctx) \<in> live_keys p"
    and e: "(u, CallEdge dst fs as, FunctionEntry q, k) \<in> calls (prog_cfg p)"
    and s: "live_succ (declared_global p) p u ctx (CallEdge dst fs as) q = Some ctx'"
  from u obtain r where lr: "prog_live (prog_table p) (prog_procs p) r u"
    and res: "(FunctionResult r, ctx) \<in> sol_vars (declared_global p) p"
    unfolding live_keys_def by blast
  have "prog_live (prog_table p) (prog_procs p) r k"
    using prog_live_calls[OF wf lr] e by (simp add: prog_cfg_def)
  then have k: "(k, ctx) \<in> sol_vars (declared_global p) p"
    using live_keys_of_result[OF wf solves _ res] live_keys_sub by blast
  from s have nb: "transfer_lift (resolved_st_q_is_bot_for (declared_global_vars p))
               (enter_st (declared_global p) (call_info_of (CallEdge dst fs as) q))
               (locals (sol_env (declared_global p) p (Inl (u, ctx)))) \<noteq> Bot"
    and c': "ctx' = ctx_succ (declared_global p) p u ctx (CallEdge dst fs as) q"
    by (auto simp: live_succ_def split: if_splits)
  have rq: "(FunctionResult q, ctx') \<in> sol_vars (declared_global p) p"
    unfolding c' by (rule sol_vars_callee_result[OF solves k e nb])
  have "prog_live (prog_table p) (prog_procs p) q (FunctionEntry q)"
    using prog_live_callee_entry[OF wf] e by (simp add: prog_cfg_def)
  then show "(FunctionEntry q, ctx') \<in> live_keys p" by (rule live_keys_of_result[OF wf solves _ rq])
qed

lemma root_live_key:
  assumes wf: "wf_program_compile_input p" and solves: "terminates (declared_global p) p"
  shows "root_query p \<in> live_keys p"
proof -
  have r: "(FunctionResult prog_main_name, root_ctx) \<in> sol_vars (declared_global p) p"
    using pp_routed[OF solves] by (simp add: root_query_def prog_cfg_def)
  show ?thesis
    using live_keys_of_result[OF wf solves prog_live_result[OF prog_live_main_entry[OF wf]] r]
    by (simp add: root_query_def prog_cfg_def)
qed

subsection \<open>The entry-state endpoint over the live keys\<close>

context
  fixes p :: imp_prog
begin

interpretation dom: routed_dg_domain_exec "declared_global p"
    "resolved_st_q_is_bot_for (declared_global_vars p)" "tf_st (declared_global p)"
    "enter_st (declared_global p)" sk asn spc br bd rt "en (declared_global p)" ev
  by unfold_locales
     (rule tf_commute[unfolded fun_of_exec_dg_st_for_def], assumption,
      rule enter_commute[unfolded fun_of_exec_dg_st_for_def],
      rule empty_pred_exact)

interpretation dg_base: sound_dg_spec_core "analysis_spec (declared_global p) p" dom.gamma_exec
    "declared_global p"
  unfolding analysis_spec_def by (rule dom.sound_dg_spec_core_st[OF tf_sound])

text \<open>
  The routed soundness at the live keys, for any relation admitting call contexts.
  Beyond termination and well-formedness a policy owes only its own two facts: an
  admitted context is the one this pipeline routes the entered state to, and every
  concrete call at a live key is admitted somewhere. \<open>live_keys_cover\<close> supplies
  callee-entry membership.
\<close>

lemma routed_analysis_sound_live_keys:
  fixes R :: "'c call_context_rel"
  assumes wf: "wf_program_compile_input p" and solves: "terminates (declared_global p) p"
    and cover_R: "\<And>u ctx dst pars args q cont s ctx'. (u, ctx) \<in> live_keys p
        \<Longrightarrow> (u, CallEdge dst pars args, FunctionEntry q, cont) \<in> calls (prog_cfg p)
        \<Longrightarrow> R u ctx (call_info_of (CallEdge dst pars args) q) s
              (call_enter (declared_global p) (CallEdge dst pars args) s) ctx'
        \<Longrightarrow> route (declared_global p) u ctx
              (transfer_lift (resolved_st_q_is_bot_for (declared_global_vars p))
                 (enter_st (declared_global p) (call_info_of (CallEdge dst pars args) q))
                 (locals (sol_env (declared_global p) p (Inl (u, ctx)))))
              (CallEdge dst pars args) = ctx'"
    and total_R: "\<And>u ctx dst pars args q cont s. (u, ctx) \<in> live_keys p
        \<Longrightarrow> (u, CallEdge dst pars args, FunctionEntry q, cont) \<in> calls (prog_cfg p)
        \<Longrightarrow> s \<in> dom.gamma_exec (locals (sol_env (declared_global p) p (Inl (u, ctx))))
                  (globs (sol_env (declared_global p) p (Inr gk0)))
        \<Longrightarrow> \<exists>ctx'. R u ctx (call_info_of (CallEdge dst pars args) q) s
                      (call_enter (declared_global p) (CallEdge dst pars args) s) ctx'"
  shows "routed_analysis_sound (analysis_spec (declared_global p) p) dom.gamma_exec
     (declared_global p) (prog_cfg p) gk0 (route (declared_global p)) Bot (Lifted init_st) Bot
     (sol_env (declared_global p) p) (live_keys p) (root_query p) seed (\<lambda>d. d = Bot) R
     (map_lift (fun_of_resolved_st_q_for (declared_global p))) classify"
proof (unfold_locales, goal_cases FinE PP SgCov SgUncov Fwd FinC CallsUnique SeedKey
    IsBotBot IsBotSound ResolveSound EnterCover EnterTotal CombFwd GammaRd
    ClProved ClRefuted VarsFin)
  case FinE show ?case unfolding prog_cfg_def using compile_prog_finite by simp
next
  case PP show ?case
    by (rule post_bounded_subset[OF post_bounded_of_part_post_solution[OF pp_routed[OF solves]]
          root_live_key[OF wf solves] live_keys_sub])
next
  case (SgCov v c) then show ?case by (simp add: dom.gamma_exec_def)
next
  case (SgUncov v c) then show ?case by simp
next
  case (Fwd u a v c)
  show ?case
    by (rule ctx_vars_cover_live_edgeD[OF live_keys_cover[OF wf solves] Fwd(1) _ Fwd(3)]) simp
next
  case FinC show ?case unfolding prog_cfg_def by (simp add: compile_prog_finite)
next
  case CallsUnique show ?case
    unfolding calls_source_unique_def prog_cfg_def
    using compile_prog_calls_source_unique by blast
next
  case (SeedKey q ctx) show ?case by (rule seed_ne_gk0)
next
  case IsBotBot show ?case by simp
next
  case (IsBotSound d g') then show ?case by (simp add: dom.gamma_exec_def)
next
  case (ResolveSound u ctx dst pars args q cont s)
  then show ?case unfolding prog_cfg_def by (simp add: compile_prog_finite)
next
  case (EnterCover u ctx dst pars args q cont s ctx')
  let ?ci = "call_info_of (CallEdge dst pars args) q"
  let ?caller = "locals (sol_env (declared_global p) p (Inl (u, ctx)))"
  let ?ent = "transfer_lift (resolved_st_q_is_bot_for (declared_global_vars p))
                (enter_st (declared_global p) ?ci) ?caller"
  have cov_e: "entry_pairs_cover
      (\<lambda>d'. dom.gamma_exec d' (globs (sol_env (declared_global p) p (Inr gk0)))) s
      (call_enter (declared_global p) (CallEdge dst pars args) s) [(?caller, ?ent)]"
    using entry_cover[OF EnterCover(3), where ci = ?ci] by simp
  have nbE: "?ent \<noteq> Bot"
  proof
    assume "?ent = Bot"
    with cov_e show False by (simp add: entry_pairs_cover_def dom.gamma_exec_def)
  qed
  have req: "route (declared_global p) u ctx ?ent (CallEdge dst pars args) = ctx'"
    by (rule cover_R[OF EnterCover(1,2,4)])
  have covE: "(FunctionEntry q, ctx') \<in> live_keys p"
    by (rule ctx_vars_cover_live_enterD[OF live_keys_cover[OF wf solves] EnterCover(1,2)])
       (use nbE req in \<open>simp add: live_succ_def ctx_succ_def\<close>)
  show ?case
    unfolding analysis_spec_def dgs_enter_local_state_st_for_lifted
    using enter_runs_local_enter_transfer enter_deps_local_enter_transfer cov_e req covE
    by (fastforce simp: entry_pairs_cover_def)
next
  case (EnterTotal u ctx dst pars args q cont s)
  then show ?case by (rule total_R)
next
  case (CombFwd cl c1 dst pars args q cont)
  show ?case
    by (rule ctx_vars_cover_live_combineD[OF live_keys_cover[OF wf solves] CombFwd(1,2)])
next
  case (GammaRd d g') show ?case by (simp add: dom.gamma_exec_def)
next
  case (ClProved c d s) then show ?case by (rule classify_proved)
next
  case (ClRefuted c d s) then show ?case by (rule classify_refuted)
next
  case VarsFin show ?case
    by (rule finite_subset[OF live_keys_sub vars_finite_of_terminates[OF solves]])
qed

text \<open>
  The reader over the live keys agrees with the published one on them and describes
  nothing elsewhere, so a bound proved for it is a bound on the published table.
\<close>

lemma gamma_live_reader_le:
  "gamma_state_lift (map_lift (fun_of_resolved_st_q_for (declared_global p))
       (solved_local_reader (live_keys p) (sol_env (declared_global p) p) (Inl (v, ctx))))
     \<subseteq> gamma_state_lift (map_lift (fun_of_resolved_st_q_for (declared_global p))
          (reader (declared_global p) p (Inl (v, ctx))))"
proof (cases "(v, ctx) \<in> live_keys p")
  case True
  then have "(v, ctx) \<in> sol_vars (declared_global p) p" using live_keys_sub by blast
  with True show ?thesis by (simp add: reader_def)
next
  case False then show ?thesis by simp
qed

theorem activation_collect_sound_live_keys:
  fixes R :: "'c call_context_rel"
  assumes wf: "wf_program_compile_input p" and solves: "terminates (declared_global p) p"
    and cover_R: "\<And>u ctx dst pars args q cont s ctx'. (u, ctx) \<in> live_keys p
        \<Longrightarrow> (u, CallEdge dst pars args, FunctionEntry q, cont) \<in> calls (prog_cfg p)
        \<Longrightarrow> R u ctx (call_info_of (CallEdge dst pars args) q) s
              (call_enter (declared_global p) (CallEdge dst pars args) s) ctx'
        \<Longrightarrow> route (declared_global p) u ctx
              (transfer_lift (resolved_st_q_is_bot_for (declared_global_vars p))
                 (enter_st (declared_global p) (call_info_of (CallEdge dst pars args) q))
                 (locals (sol_env (declared_global p) p (Inl (u, ctx)))))
              (CallEdge dst pars args) = ctx'"
    and total_R: "\<And>u ctx dst pars args q cont s. (u, ctx) \<in> live_keys p
        \<Longrightarrow> (u, CallEdge dst pars args, FunctionEntry q, cont) \<in> calls (prog_cfg p)
        \<Longrightarrow> s \<in> dom.gamma_exec (locals (sol_env (declared_global p) p (Inl (u, ctx))))
                  (globs (sol_env (declared_global p) p (Inr gk0)))
        \<Longrightarrow> \<exists>ctx'. R u ctx (call_info_of (CallEdge dst pars args) q) s
                      (call_enter (declared_global p) (CallEdge dst pars args) s) ctx'"
  shows "activation_collect (declared_global p) R root_ctx (prog_cfg p)
           (cinit_stores (declared_global p)) v ctx
           \<subseteq> gamma_state_lift (map_lift (fun_of_resolved_st_q_for (declared_global p))
                 (reader (declared_global p) p (Inl (v, ctx))))"
proof -
  interpret live: routed_analysis_sound "analysis_spec (declared_global p) p" dom.gamma_exec
      "declared_global p" "prog_cfg p" gk0 "route (declared_global p)" Bot "Lifted init_st" Bot
      "sol_env (declared_global p) p" "live_keys p" "root_query p" seed "\<lambda>d. d = Bot" R
      "map_lift (fun_of_resolved_st_q_for (declared_global p))" classify
    by (rule routed_analysis_sound_live_keys[where R = R, OF wf solves cover_R total_R])
  have "activation_collect (declared_global p) R root_ctx (prog_cfg p)
          (cinit_stores (declared_global p)) v ctx
        \<subseteq> gamma_state_lift (map_lift (fun_of_resolved_st_q_for (declared_global p))
             (solved_local_reader (live_keys p) (sol_env (declared_global p) p) (Inl (v, ctx))))"
    by (rule live.routed_activation_collect_sound
          [OF ctx_vars_cover_live_entryD[OF live_keys_cover[OF wf solves]] cinit_le_init])
  then show ?thesis using gamma_live_reader_le by blast
qed

text \<open>
  A policy whose route ignores the entered state --- a call string, or the unit
  context --- admits exactly the context it computes, so both of its facts are
  immediate.
\<close>

theorem fun_route_activation_collect_sound_of_terminates:
  fixes ctx_fun :: "cfg_node \<Rightarrow> 'c \<Rightarrow> store \<Rightarrow> 'c"
  assumes route_const: "\<And>u ctx d ca s. route (declared_global p) u ctx d ca = ctx_fun u ctx s"
    and wf: "wf_program_compile_input p" and solves: "terminates (declared_global p) p"
  shows "activation_collect (declared_global p) (call_context_rel_of_fun ctx_fun) root_ctx
           (prog_cfg p) (cinit_stores (declared_global p)) v ctx
           \<subseteq> gamma_state_lift (map_lift (fun_of_resolved_st_q_for (declared_global p))
                 (reader (declared_global p) p (Inl (v, ctx))))"
proof (rule activation_collect_sound_live_keys[OF wf solves])
  fix u ctx dst pars args q cont and s :: store and ctx'
  assume "(u, ctx) \<in> live_keys p"
    and "(u, CallEdge dst pars args, FunctionEntry q, cont) \<in> calls (prog_cfg p)"
    and Rc: "call_context_rel_of_fun ctx_fun u ctx (call_info_of (CallEdge dst pars args) q) s
               (call_enter (declared_global p) (CallEdge dst pars args) s) ctx'"
  show "route (declared_global p) u ctx
          (transfer_lift (resolved_st_q_is_bot_for (declared_global_vars p))
             (enter_st (declared_global p) (call_info_of (CallEdge dst pars args) q))
             (locals (sol_env (declared_global p) p (Inl (u, ctx)))))
          (CallEdge dst pars args) = ctx'"
    using Rc
    by (simp add: route_const[of _ _ _ _ "call_enter (declared_global p) (CallEdge dst pars args) s"])
next
  fix u ctx dst pars args q cont and s :: store
  show "\<exists>ctx'. call_context_rel_of_fun ctx_fun u ctx (call_info_of (CallEdge dst pars args) q) s
                 (call_enter (declared_global p) (CallEdge dst pars args) s) ctx'"
    by simp
qed

subsection \<open>Entry-state routing\<close>

lemma entry_state_routed_analysis_sound_live_keys:
  assumes wf: "wf_program_compile_input p" and solves: "terminates (declared_global p) p"
  shows "routed_analysis_sound (analysis_spec (declared_global p) p) dom.gamma_exec
     (declared_global p) (prog_cfg p) gk0 (route (declared_global p)) Bot (Lifted init_st) Bot
     (sol_env (declared_global p) p) (live_keys p) (root_query p) seed (\<lambda>d. d = Bot)
     (admitted_contexts (declared_global p) p)
     (map_lift (fun_of_resolved_st_q_for (declared_global p))) classify"
proof (rule routed_analysis_sound_live_keys[OF wf solves])
  fix u ctx dst pars args q cont and s :: store and ctx'
  assume "(u, ctx) \<in> live_keys p"
    and "(u, CallEdge dst pars args, FunctionEntry q, cont) \<in> calls (prog_cfg p)"
    and Rc: "admitted_contexts (declared_global p) p u ctx
               (call_info_of (CallEdge dst pars args) q) s
               (call_enter (declared_global p) (CallEdge dst pars args) s) ctx'"
  let ?ci = "call_info_of (CallEdge dst pars args) q"
  let ?caller = "locals (sol_env (declared_global p) p (Inl (u, ctx)))"
  let ?ent = "transfer_lift (resolved_st_q_is_bot_for (declared_global_vars p))
                (enter_st (declared_global p) ?ci) ?caller"
  from Rc[unfolded admitted_contexts_alt] obtain cont' entry
    where mem: "(cont', entry) \<in> set [(?caller, ?ent)]"
      and req0: "ctx' = route (declared_global p) u ctx entry
                   (CallEdge (ci_dst ?ci) (ci_formals ?ci) (ci_args ?ci))"
    by (rule routed_entry_context_relE)
  show "route (declared_global p) u ctx ?ent (CallEdge dst pars args) = ctx'"
    using mem req0 by simp
next
  fix u ctx dst pars args q cont and s :: store
  assume "(u, ctx) \<in> live_keys p"
    and "(u, CallEdge dst pars args, FunctionEntry q, cont) \<in> calls (prog_cfg p)"
    and sin: "s \<in> dom.gamma_exec (locals (sol_env (declared_global p) p (Inl (u, ctx))))
                (globs (sol_env (declared_global p) p (Inr gk0)))"
  show "\<exists>ctx'. admitted_contexts (declared_global p) p u ctx
                 (call_info_of (CallEdge dst pars args) q) s
                 (call_enter (declared_global p) (CallEdge dst pars args) s) ctx'"
    unfolding admitted_contexts_alt
    by (rule routed_entry_context_rel_total)
       (use entry_cover[OF sin, where ci = "call_info_of (CallEdge dst pars args) q"] in simp)
qed

theorem entry_state_activation_collect_sound_of_terminates:
  assumes wf: "wf_program_compile_input p" and solves: "terminates (declared_global p) p"
  shows "activation_collect (declared_global p) (admitted_contexts (declared_global p) p)
           root_ctx (prog_cfg p) (cinit_stores (declared_global p)) v ctx
           \<subseteq> gamma_state_lift (map_lift (fun_of_resolved_st_q_for (declared_global p))
                 (reader (declared_global p) p (Inl (v, ctx))))"
proof -
  interpret live: routed_analysis_sound "analysis_spec (declared_global p) p" dom.gamma_exec
      "declared_global p" "prog_cfg p" gk0 "route (declared_global p)" Bot "Lifted init_st" Bot
      "sol_env (declared_global p) p" "live_keys p" "root_query p" seed "\<lambda>d. d = Bot"
      "admitted_contexts (declared_global p) p"
      "map_lift (fun_of_resolved_st_q_for (declared_global p))" classify
    by (rule entry_state_routed_analysis_sound_live_keys[OF wf solves])
  have "activation_collect (declared_global p) (admitted_contexts (declared_global p) p)
          root_ctx (prog_cfg p) (cinit_stores (declared_global p)) v ctx
        \<subseteq> gamma_state_lift (map_lift (fun_of_resolved_st_q_for (declared_global p))
             (solved_local_reader (live_keys p) (sol_env (declared_global p) p) (Inl (v, ctx))))"
    by (rule live.routed_activation_collect_sound
          [OF ctx_vars_cover_live_entryD[OF live_keys_cover[OF wf solves]] cinit_le_init])
  then show ?thesis using gamma_live_reader_le by blast
qed

corollary entry_state_lookup_sound_of_terminates:
  assumes wf: "wf_program_compile_input p" and solves: "terminates (declared_global p) p"
  shows "activation_collect (declared_global p) (admitted_contexts (declared_global p) p)
           root_ctx (prog_cfg p) (cinit_stores (declared_global p)) v ctx
           \<subseteq> gamma_point (lookup_context (result (declared_global p) p) v ctx)"
  using entry_state_activation_collect_sound_of_terminates[OF wf solves]
  unfolding gamma_reader_eq_lookup .

theorem entry_state_ltr_collect_eq_Union_of_terminates:
  assumes wf: "wf_program_compile_input p" and solves: "terminates (declared_global p) p"
  shows "ltr_collect (declared_global p) (prog_cfg p) (cinit_stores (declared_global p)) v
           = (\<Union>ctx. activation_collect (declared_global p) (admitted_contexts (declared_global p) p)
                       root_ctx (prog_cfg p) (cinit_stores (declared_global p)) v ctx)"
proof (rule ltr_collect_eq_Union_activation_of_has_context)
  interpret live: routed_analysis_sound "analysis_spec (declared_global p) p" dom.gamma_exec
      "declared_global p" "prog_cfg p" gk0 "route (declared_global p)" Bot "Lifted init_st" Bot
      "sol_env (declared_global p) p" "live_keys p" "root_query p" seed "\<lambda>d. d = Bot"
      "admitted_contexts (declared_global p) p"
      "map_lift (fun_of_resolved_st_q_for (declared_global p))" classify
    by (rule entry_state_routed_analysis_sound_live_keys[OF wf solves])
  fix t
  assume "t \<in> valid_ltr (declared_global p) (prog_cfg p) (cinit_stores (declared_global p))"
  then show "\<exists>c. trace_context (declared_global p) (admitted_contexts (declared_global p) p)
                   root_ctx (prog_cfg p) t c"
    by (rule live.routed_valid_ltr_has_context
          [OF ctx_vars_cover_live_entryD[OF live_keys_cover[OF wf solves]] cinit_le_init])
qed

end

end

end
