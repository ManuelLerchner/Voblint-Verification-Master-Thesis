theory DG_Live_Unknowns
  imports DG_Analysis "Voblint_Compile.Live_Nodes"
begin

section \<open>Which solved keys a terminating solve is closed on\<close>

text \<open>
  The key set a terminating solve returns is not one the soundness argument can use as it
  stands: it may hold keys the solver queried under an earlier value and no longer reads,
  and keys inside code no execution reaches.  \<open>live_unknowns\<close> keeps a solved key when its
  node is live in a procedure (\<^theory>\<open>Voblint_Compile.Live_Nodes\<close>) whose result is
  solved at the same context.  From what each generated equation reads under the final
  valuation, \<open>live_unknowns_cover\<close> shows that set closed under every intra edge, every call
  continuation and every call that enters a live state, with no premise beyond termination
  and a well-formed program.  The endpoints below restate the routed soundness over these
  keys and carry it to the published table.
\<close>

subsection \<open>What a routed equation reads\<close>

lemma dep_aux_routed_node_rhs:
  assumes wf: "\<And>w. \<forall>q \<in> set (routed_contribution_programs pred_sel site_sel route
                     it cmb extra g cx w). sp_wf q"
  shows "dep_aux \<tau> (routed_node_rhs pred_sel site_sel analysis_global_at route it cmb extra g bot0 s0d s0g
           (v, cx))
     = (\<Union>q\<in>set (routed_contribution_programs pred_sel site_sel route it cmb extra g cx v).
          dep_program \<tau> q)"
  by (cases "v = cfg_entry g")
     (simp_all add: routed_node_rhs_def Let_def dep_program_side_rhs_fold_dg_char[OF wf])

lemma dep_L_routed_node_rhs_intra:
  assumes fin: "finite (intra g)" and e: "(u, a, v) \<in> intra g"
    and wf: "\<And>w. \<forall>q \<in> set (routed_contribution_programs
                     intra_predecessor_addr_list call_site_list route
                     (\<lambda>cx src a. dg_spec_edge_program S a src slot) cmb extra g cx w). sp_wf q"
  shows "(u, cx) \<in> dep\<^sub>L (routed_node_rhs intra_predecessor_addr_list call_site_list analysis_global_at route
            (\<lambda>cx src a. dg_spec_edge_program S a src slot) cmb extra g bot0 s0d s0g) \<tau> (v, cx)"
proof -
  have "dg_spec_edge_program S a (Inl (u, cx)) slot
          \<in> set (routed_contribution_programs intra_predecessor_addr_list call_site_list route
                   (\<lambda>cx src a. dg_spec_edge_program S a src slot) cmb extra g cx v)"
    using e fin
    by (force simp: routed_contribution_programs_def intra_predecessor_addr_list_def
        intra_predecessors_def)
  then show ?thesis
    unfolding dep\<^sub>L_def dep_def
    using dep_dg_spec_edge_program_source[of "Inl (u, cx)" \<tau> S a slot]
    by (auto simp: dep_aux_routed_node_rhs[OF wf])
qed

lemma dep_program_routed_call_program:
  assumes wfS: "dg_spec_wf S"
  shows "dep_program \<tau> (routed_call_program S analysis_global seed resolve is_bot route ctx ca cc v)
     = insert (Inl (cc, ctx))
         (\<Union>q\<in>set (resolve v cc ca (dg_local (\<tau> (Inl (cc, ctx))))).
            dep_program \<tau> (routed_callee_call_program S analysis_global seed route is_bot ctx ca cc
                        (dg_local (\<tau> (Inl (cc, ctx)))) q))"
  by (simp add: routed_call_program_def sp_compile_bind sp_wf_observes
      dep_program_side_rhs_fold_dg_char[OF sp_wf_routed_callee_call_programs[OF wfS]])

lemma routed_call_program_mem:
  assumes fin: "finite (calls g)" and e: "(u, ca, FunctionEntry q, k) \<in> calls g"
  shows "routed_call_program S analysis_global seed resolve is_bot route cx ca u k
           \<in> set (routed_contribution_programs pred_sel call_site_list route it
                    (routed_call_program S analysis_global seed resolve is_bot) extra g cx k)"
proof -
  have "(u, ca) \<in> set (call_site_list g k)" using e fin by auto
  then show ?thesis by (rule routed_contribution_programs_combineI)
qed

lemma dep_L_routed_node_rhs_call_site:
  assumes fin: "finite (calls g)" and e: "(u, ca, FunctionEntry q, k) \<in> calls g"
    and wfS: "dg_spec_wf S"
    and wf: "\<And>w. \<forall>q \<in> set (routed_contribution_programs pred_sel call_site_list route it
                     (routed_call_program S analysis_global seed resolve is_bot) extra g cx w). sp_wf q"
  shows "(u, cx) \<in> dep\<^sub>L (routed_node_rhs pred_sel call_site_list analysis_global_at route it
            (routed_call_program S analysis_global seed resolve is_bot) extra g bot0 s0d s0g) \<tau> (k, cx)"
proof -
  have "Inl (u, cx)
          \<in> dep_program \<tau> (routed_call_program S analysis_global seed resolve is_bot route cx ca u k)"
    by (simp add: dep_program_routed_call_program[OF wfS])
  then show ?thesis
    unfolding dep\<^sub>L_def dep_def
    using routed_call_program_mem
            [OF fin e, of S analysis_global seed resolve is_bot route cx pred_sel it extra]
    by (auto simp: dep_aux_routed_node_rhs[OF wf])
qed

lemma dep_L_routed_node_rhs_callee_result:
  fixes f :: "'d::bounded_semilattice_sup_bot \<Rightarrow> 'd"
  assumes fin: "finite (calls g)" and e: "(u, ca, FunctionEntry q, k) \<in> calls g"
    and enter: "enter\<^sup># S (call_info_of ca q) = local_enter_transfer (\<lambda>d. [(d, f d)])"
    and res: "q \<in> set (resolve k u ca (dg_local (\<tau> (Inl (u, cx)))))"
    and nb: "\<not> is_bot (f (dg_local (\<tau> (Inl (u, cx)))))"
    and wfS: "dg_spec_wf S"
    and wf: "\<And>w. \<forall>q \<in> set (routed_contribution_programs pred_sel call_site_list route it
                     (routed_call_program S analysis_global seed resolve is_bot) extra g cx w). sp_wf q"
  shows "(FunctionResult q, route u cx (f (dg_local (\<tau> (Inl (u, cx))))) ca)
           \<in> dep\<^sub>L (routed_node_rhs pred_sel call_site_list analysis_global_at route it
                (routed_call_program S analysis_global seed resolve is_bot) extra g bot0 s0d s0g) \<tau> (k, cx)"
proof -
  let ?d = "dg_local (\<tau> (Inl (u, cx)))"
  have callee: "dep_program \<tau> (routed_callee_call_program S analysis_global seed route is_bot cx ca u ?d q)
      = dep_aux \<tau> (sp_compile (side_rhs_fold_dg bot
          (map (routed_call_alternative_program S analysis_global seed route is_bot cx ca u q)
             [(?d, f ?d)])))"
    unfolding routed_callee_call_program_def enter sp_compile_bind
    by (rule enter_depsD[OF enter_deps_local_enter_transfer_mk_dg_man, simplified])
  have "Inl (FunctionResult q, route u cx (f ?d) ca)
          \<in> dep_program \<tau> (routed_callee_call_program S analysis_global seed route is_bot cx ca u ?d q)"
  proof -
    have "Inl (FunctionResult q, route u cx (f ?d) ca)
            \<in> dep_program \<tau> (routed_call_alternative_program S analysis_global seed route is_bot cx ca u q
                           (?d, f ?d))"
      using nb by (simp add: routed_call_alternative_program_def Let_def)
    then show ?thesis
      unfolding callee
        dep_program_side_rhs_fold_dg_char[OF sp_wf_routed_call_alternative_programs[OF wfS]]
      by simp
  qed
  then have "Inl (FunctionResult q, route u cx (f ?d) ca)
               \<in> dep_program \<tau> (routed_call_program S analysis_global seed resolve is_bot route cx ca u k)"
    using res by (auto simp: dep_program_routed_call_program[OF wfS])
  then show ?thesis
    unfolding dep\<^sub>L_def dep_def
    using routed_call_program_mem
            [OF fin e, of S analysis_global seed resolve is_bot route cx pred_sel it extra]
    by (auto simp: dep_aux_routed_node_rhs[OF wf])
qed

subsection \<open>Keys of a solve whose activation returned\<close>

context dg_analysis
begin

lemma analysis_spec_enter:
  "enter\<^sup># (analysis_spec (declared_global p) p) ci
     = local_enter_transfer (\<lambda>d. [(d, entry_of (declared_global p) p ci d)])"
  by (simp add: analysis_spec_def dg_spec_of_def enter_single)

lemma analysis_contribs_wf [simp]:
  "\<forall>q \<in> set (routed_contribution_programs intra_predecessor_addr_list call_site_list
       (route \<G>)
       (\<lambda>ctx' src a. dg_spec_edge_program (analysis_spec \<G> p) a src (\<lambda>_. analysis_global))
       (routed_call_program (analysis_spec \<G> p) analysis_global seed rsv (\<lambda>d. d = Bot))
       (routed_entry_seed_programs seed) cfg cx w). sp_wf q"
  by (rule routed_contribution_programs_wf) auto

lemma sol_vars_dep_closed:
  assumes solves: "terminates (declared_global p) p"
    and x: "x \<in> sol_vars (declared_global p) p"
    and y: "y \<in> dep\<^sub>L
       (routed_node_rhs intra_predecessor_addr_list call_site_list (\<lambda>_. analysis_global)
          (route (declared_global p))
          (\<lambda>ctx' src a. dg_spec_edge_program (analysis_spec (declared_global p) p) a src (\<lambda>_. analysis_global))
          (routed_call_program (analysis_spec (declared_global p) p) analysis_global seed
             (static_resolve (prog_cfg p)) (\<lambda>d. d = Bot))
          (routed_entry_seed_programs seed)
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
  by (rule sol_vars_dep_closed
        [OF solves v dep_L_routed_node_rhs_intra[OF prog_cfg_finite(1) e analysis_contribs_wf]])

lemma sol_vars_back_call_site:
  assumes solves: "terminates (declared_global p) p"
    and k: "(k, cx) \<in> sol_vars (declared_global p) p"
    and e: "(u, ca, FunctionEntry q, k) \<in> calls (prog_cfg p)"
  shows "(u, cx) \<in> sol_vars (declared_global p) p"
  by (rule sol_vars_dep_closed
        [OF solves k dep_L_routed_node_rhs_call_site
           [OF prog_cfg_finite(2) e dg_spec_wf_analysis_spec analysis_contribs_wf]])

lemma sol_vars_callee_result:
  assumes solves: "terminates (declared_global p) p"
    and k: "(k, cx) \<in> sol_vars (declared_global p) p"
    and e: "(u, ca, FunctionEntry q, k) \<in> calls (prog_cfg p)"
    and nb: "entry_of (declared_global p) p (call_info_of ca q)
               (dg_local (sol_env (declared_global p) p (Inl (u, cx)))) \<noteq> Bot"
  shows "(FunctionResult q, ctx_succ (declared_global p) p u cx ca q)
           \<in> sol_vars (declared_global p) p"
proof -
  have res: "q \<in> set (static_resolve (prog_cfg p) k u ca
                        (dg_local (sol_env (declared_global p) p (Inl (u, cx)))))"
    using e prog_cfg_finite(2) by simp
  show ?thesis
    unfolding ctx_succ_def
    by (rule sol_vars_dep_closed[OF solves k],
        rule dep_L_routed_node_rhs_callee_result[where resolve = "static_resolve (prog_cfg p)"
            and \<tau> = "sol_env (declared_global p) p" and cx = cx,
          OF prog_cfg_finite(2) e analysis_spec_enter[of p] res])
       (use nb in simp, rule dg_spec_wf_analysis_spec, rule analysis_contribs_wf)
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

definition live_unknowns :: "imp_prog \<Rightarrow> (pp \<times> 'c) set" where
  "live_unknowns p =
     {(u, cx) \<in> sol_vars (declared_global p) p.
        \<exists>q. prog_live (prog_table p) (prog_procs p) q u
          \<and> (FunctionResult q, cx) \<in> sol_vars (declared_global p) p}"

lemma live_unknowns_sub: "live_unknowns p \<subseteq> sol_vars (declared_global p) p"
  unfolding live_unknowns_def by blast

lemma live_unknowns_of_result:
  assumes wf: "wf_program_compile_input p" and solves: "terminates (declared_global p) p"
    and live: "prog_live (prog_table p) (prog_procs p) q y"
    and r: "(FunctionResult q, cx) \<in> sol_vars (declared_global p) p"
  shows "(y, cx) \<in> live_unknowns p"
proof -
  have "local_reaches (prog_cfg p) y (FunctionResult q)"
    unfolding prog_cfg_def by (rule prog_live_reaches[OF live])
  then have "(y, cx) \<in> sol_vars (declared_global p) p" by (rule sol_vars_back_reach[OF solves r])
  then show ?thesis unfolding live_unknowns_def using live r by blast
qed

theorem live_unknowns_cover:
  assumes wf: "wf_program_compile_input p" and solves: "terminates (declared_global p) p"
  shows "ctx_vars_cover_live (prog_cfg p) (\<lambda>_ _. True) (live_succ (declared_global p) p)
           root_ctx (live_unknowns p)"
proof (rule ctx_vars_cover_liveI)
  have root: "(FunctionResult prog_main_name, root_ctx) \<in> sol_vars (declared_global p) p"
    using pp_routed[OF solves] by (simp add: root_query_def prog_cfg_def)
  show "(cfg_entry (prog_cfg p), root_ctx) \<in> live_unknowns p"
    using live_unknowns_of_result[OF wf solves prog_live_main_entry[OF wf] root]
    by (simp add: prog_cfg_def)
next
  fix u a v ctx
  assume u: "(u, ctx) \<in> live_unknowns p" and e: "(u, a, v) \<in> intra (prog_cfg p)"
  from u obtain q where lq: "prog_live (prog_table p) (prog_procs p) q u"
    and r: "(FunctionResult q, ctx) \<in> sol_vars (declared_global p) p"
    unfolding live_unknowns_def by blast
  have "prog_live (prog_table p) (prog_procs p) q v"
    using prog_live_intra[OF wf lq] e by (simp add: prog_cfg_def)
  then show "(v, ctx) \<in> live_unknowns p" by (rule live_unknowns_of_result[OF wf solves _ r])
next
  fix u ctx dst fs as q k
  assume u: "(u, ctx) \<in> live_unknowns p"
    and e: "(u, CallEdge dst fs as, FunctionEntry q, k) \<in> calls (prog_cfg p)"
  from u obtain r where lr: "prog_live (prog_table p) (prog_procs p) r u"
    and res: "(FunctionResult r, ctx) \<in> sol_vars (declared_global p) p"
    unfolding live_unknowns_def by blast
  have "prog_live (prog_table p) (prog_procs p) r k"
    using prog_live_calls[OF wf lr] e by (simp add: prog_cfg_def)
  then show "(k, ctx) \<in> live_unknowns p" by (rule live_unknowns_of_result[OF wf solves _ res])
next
  fix u ctx dst fs as q k ctx'
  assume u: "(u, ctx) \<in> live_unknowns p"
    and e: "(u, CallEdge dst fs as, FunctionEntry q, k) \<in> calls (prog_cfg p)"
    and s: "live_succ (declared_global p) p u ctx (CallEdge dst fs as) q = Some ctx'"
  from u obtain r where lr: "prog_live (prog_table p) (prog_procs p) r u"
    and res: "(FunctionResult r, ctx) \<in> sol_vars (declared_global p) p"
    unfolding live_unknowns_def by blast
  have "prog_live (prog_table p) (prog_procs p) r k"
    using prog_live_calls[OF wf lr] e by (simp add: prog_cfg_def)
  then have k: "(k, ctx) \<in> sol_vars (declared_global p) p"
    using live_unknowns_of_result[OF wf solves _ res] live_unknowns_sub by blast
  from s have nb: "entry_of (declared_global p) p (call_info_of (CallEdge dst fs as) q)
               (dg_local (sol_env (declared_global p) p (Inl (u, ctx)))) \<noteq> Bot"
    and c': "ctx' = ctx_succ (declared_global p) p u ctx (CallEdge dst fs as) q"
    by (auto simp: live_succ_def split: if_splits)
  have rq: "(FunctionResult q, ctx') \<in> sol_vars (declared_global p) p"
    unfolding c' by (rule sol_vars_callee_result[OF solves k e nb])
  have "prog_live (prog_table p) (prog_procs p) q (FunctionEntry q)"
    using prog_live_callee_entry[OF wf] e by (simp add: prog_cfg_def)
  then show "(FunctionEntry q, ctx') \<in> live_unknowns p"
    by (rule live_unknowns_of_result[OF wf solves _ rq])
qed

lemma root_live_key:
  assumes wf: "wf_program_compile_input p" and solves: "terminates (declared_global p) p"
  shows "root_query p \<in> live_unknowns p"
proof -
  have r: "(FunctionResult prog_main_name, root_ctx) \<in> sol_vars (declared_global p) p"
    using pp_routed[OF solves] by (simp add: root_query_def prog_cfg_def)
  show ?thesis
    using live_unknowns_of_result[OF wf solves prog_live_result[OF prog_live_main_entry[OF wf]] r]
    by (simp add: root_query_def prog_cfg_def)
qed

subsection \<open>The entry-state endpoint over the live keys\<close>

context
  fixes p :: imp_prog
begin

interpretation dg_base: analysis_contract "analysis_spec (declared_global p) p"
    "\<lambda>d g. gamma_lift gamma\<^sub>V (map_lift (rd (declared_global p)) d)" "declared_global p"
  unfolding analysis_spec_def by (rule dg_spec_of_contract[OF comp_sound])

text \<open>
  The routed soundness at the live keys, for any relation admitting call contexts.
  Beyond termination and well-formedness a policy owes only its own two facts: an
  admitted context is the one this pipeline routes the entered state to, and every
  concrete call at a live key is admitted somewhere. \<open>live_unknowns_cover\<close> supplies
  callee-entry membership.
\<close>

lemma routed_analysis_sound_live_unknowns:
  fixes R :: "'c call_context_rel"
  assumes wf: "wf_program_compile_input p" and solves: "terminates (declared_global p) p"
    and cover_R: "\<And>u ctx dst pars args q cont s ctx'. (u, ctx) \<in> live_unknowns p
        \<Longrightarrow> (u, CallEdge dst pars args, FunctionEntry q, cont) \<in> calls (prog_cfg p)
        \<Longrightarrow> R u ctx (call_info_of (CallEdge dst pars args) q) s
              (call_enter (declared_global p) (CallEdge dst pars args) s) ctx'
        \<Longrightarrow> route (declared_global p) u ctx
              (entry_of (declared_global p) p (call_info_of (CallEdge dst pars args) q)
                 (dg_local (sol_env (declared_global p) p (Inl (u, ctx)))))
              (CallEdge dst pars args) = ctx'"
    and total_R: "\<And>u ctx dst pars args q cont s. (u, ctx) \<in> live_unknowns p
        \<Longrightarrow> (u, CallEdge dst pars args, FunctionEntry q, cont) \<in> calls (prog_cfg p)
        \<Longrightarrow> s \<in> gamma_lift gamma\<^sub>V (map_lift (rd (declared_global p)) (dg_local (sol_env (declared_global p) p (Inl (u, ctx)))))
        \<Longrightarrow> \<exists>ctx'. R u ctx (call_info_of (CallEdge dst pars args) q) s
                      (call_enter (declared_global p) (CallEdge dst pars args) s) ctx'"
  shows "routed_analysis (analysis_spec (declared_global p) p)
     (\<lambda>d g. gamma_lift gamma\<^sub>V (map_lift (rd (declared_global p)) d))
     (declared_global p) (prog_cfg p) analysis_global (route (declared_global p)) Bot (Lifted init_st) Bot
     (sol_env (declared_global p) p) (live_unknowns p) (root_query p) seed (\<lambda>d. d = Bot) R
     (map_lift (rd (declared_global p))) gamma\<^sub>V empty\<^sub>V classify"
proof (unfold_locales, goal_cases CmbWf ExtraWf FinE PP SgCov SgUncov Fwd FinC CallsUnique
    SeedUnknown IsBotBot IsBotSound ResolveSound EnterCover EnterTotal CombFwd GammaRd EmptyExact
    ClProved ClRefuted VarsFin)
  case CmbWf show ?case by (rule sp_wf_routed_call_program[OF dg_spec_wf_analysis_spec])
next
  case ExtraWf then show ?case by (rule sp_wf_routed_entry_seed_programs)
next
  case FinE show ?case unfolding prog_cfg_def using compile_prog_finite by simp
next
  case PP show ?case
    by (rule post_bounded_subset[OF post_bounded_of_part_post_solution[OF pp_routed[OF solves]]
          root_live_key[OF wf solves] live_unknowns_sub])
next
  case (SgCov v c) then show ?case by simp
next
  case (SgUncov v c) then show ?case by simp
next
  case (Fwd u a v c)
  show ?case
    by (rule ctx_vars_cover_live_edgeD[OF live_unknowns_cover[OF wf solves] Fwd(1) _ Fwd(3)]) simp
next
  case FinC show ?case unfolding prog_cfg_def by (simp add: compile_prog_finite)
next
  case CallsUnique show ?case
    unfolding calls_source_unique_def prog_cfg_def
    using compile_prog_calls_source_unique by blast
next
  case (SeedUnknown q ctx) show ?case by (rule seed_ne_analysis_global)
next
  case IsBotBot show ?case by simp
next
  case (IsBotSound d g') then show ?case by simp
next
  case (ResolveSound u ctx dst pars args q cont s)
  then show ?case unfolding prog_cfg_def by (simp add: compile_prog_finite)
next
  case (EnterCover u ctx dst pars args q cont s ctx')
  let ?ci = "call_info_of (CallEdge dst pars args) q"
  let ?caller = "dg_local (sol_env (declared_global p) p (Inl (u, ctx)))"
  let ?ent = "entry_of (declared_global p) p ?ci ?caller"
  have cov_e: "entry_pairs_cover
      (\<lambda>d'. gamma_lift gamma\<^sub>V (map_lift (rd (declared_global p)) d')) s
      (call_enter (declared_global p) (CallEdge dst pars args) s) [(?caller, ?ent)]"
    using entry_cover[OF EnterCover(3), where ci = ?ci] by simp
  have nbE: "?ent \<noteq> Bot"
  proof
    assume "?ent = Bot"
    with cov_e show False by (simp add: entry_pairs_cover_def)
  qed
  have req: "route (declared_global p) u ctx ?ent (CallEdge dst pars args) = ctx'"
    by (rule cover_R[OF EnterCover(1,2,4)])
  have covE: "(FunctionEntry q, ctx') \<in> live_unknowns p"
    by (rule ctx_vars_cover_live_enterD[OF live_unknowns_cover[OF wf solves] EnterCover(1,2)])
       (use nbE req in \<open>simp add: live_succ_def ctx_succ_def\<close>)
  show ?case
    using enter_runs_local_enter_transfer enter_deps_local_enter_transfer cov_e req covE
    by (fastforce simp: analysis_spec_def dg_spec_of_def enter_single entry_pairs_cover_def)
next
  case (EnterTotal u ctx dst pars args q cont s)
  then show ?case by (rule total_R)
next
  case (CombFwd cl c1 dst pars args q cont)
  show ?case
    by (rule ctx_vars_cover_live_combineD[OF live_unknowns_cover[OF wf solves] CombFwd(1,2)])
next
  case (GammaRd d g') show ?case by simp
next
  case (EmptyExact v) then show ?case by (rule empty\<^sub>V_sound)
next
  case (ClProved c d s) then show ?case by (rule classify_proved)
next
  case (ClRefuted c d s) then show ?case by (rule classify_refuted)
next
  case VarsFin show ?case
    by (rule finite_subset[OF live_unknowns_sub vars_finite_of_terminates[OF solves]])
qed

text \<open>
  The reader over the live keys agrees with the published one on them and describes
  nothing elsewhere, so a bound proved for it is a bound on the published table.
\<close>

lemma gamma_live_reader_le:
  "gamma_lift gamma\<^sub>V (map_lift (rd (declared_global p))
       (solved_local_reader (live_unknowns p) (sol_env (declared_global p) p) (Inl (v, ctx))))
     \<subseteq> gamma_lift gamma\<^sub>V (map_lift (rd (declared_global p))
          (reader (declared_global p) p (Inl (v, ctx))))"
proof (cases "(v, ctx) \<in> live_unknowns p")
  case True
  then have "(v, ctx) \<in> sol_vars (declared_global p) p" using live_unknowns_sub by blast
  with True show ?thesis by (simp add: reader_def)
next
  case False then show ?thesis by simp
qed

theorem activation_collect_sound_live_unknowns:
  fixes R :: "'c call_context_rel"
  assumes wf: "wf_program_compile_input p" and solves: "terminates (declared_global p) p"
    and cover_R: "\<And>u ctx dst pars args q cont s ctx'. (u, ctx) \<in> live_unknowns p
        \<Longrightarrow> (u, CallEdge dst pars args, FunctionEntry q, cont) \<in> calls (prog_cfg p)
        \<Longrightarrow> R u ctx (call_info_of (CallEdge dst pars args) q) s
              (call_enter (declared_global p) (CallEdge dst pars args) s) ctx'
        \<Longrightarrow> route (declared_global p) u ctx
              (entry_of (declared_global p) p (call_info_of (CallEdge dst pars args) q)
                 (dg_local (sol_env (declared_global p) p (Inl (u, ctx)))))
              (CallEdge dst pars args) = ctx'"
    and total_R: "\<And>u ctx dst pars args q cont s. (u, ctx) \<in> live_unknowns p
        \<Longrightarrow> (u, CallEdge dst pars args, FunctionEntry q, cont) \<in> calls (prog_cfg p)
        \<Longrightarrow> s \<in> gamma_lift gamma\<^sub>V (map_lift (rd (declared_global p)) (dg_local (sol_env (declared_global p) p (Inl (u, ctx)))))
        \<Longrightarrow> \<exists>ctx'. R u ctx (call_info_of (CallEdge dst pars args) q) s
                      (call_enter (declared_global p) (CallEdge dst pars args) s) ctx'"
  shows "\<A>\<^bsub>declared_global p,R,root_ctx,prog_cfg p,cinit_stores (declared_global p)\<^esub> v ctx
           \<subseteq> gamma_lift gamma\<^sub>V (map_lift (rd (declared_global p))
                 (reader (declared_global p) p (Inl (v, ctx))))"
proof -
  interpret live: routed_analysis "analysis_spec (declared_global p) p"
      "\<lambda>d g. gamma_lift gamma\<^sub>V (map_lift (rd (declared_global p)) d)"
      "declared_global p" "prog_cfg p" analysis_global "route (declared_global p)" Bot
        "Lifted init_st" Bot
      "sol_env (declared_global p) p" "live_unknowns p" "root_query p" seed "\<lambda>d. d = Bot" R
      "map_lift (rd (declared_global p))" gamma\<^sub>V empty\<^sub>V classify
    by (rule routed_analysis_sound_live_unknowns[where R = R, OF wf solves cover_R total_R])
  have "\<A>\<^bsub>declared_global p,R,root_ctx,prog_cfg p,cinit_stores (declared_global p)\<^esub> v ctx
        \<subseteq> gamma_lift gamma\<^sub>V (map_lift (rd (declared_global p))
             (solved_local_reader (live_unknowns p) (sol_env (declared_global p) p) (Inl (v, ctx))))"
    by (rule live.activation_collect_dg_sound
          [OF ctx_vars_cover_live_entryD[OF live_unknowns_cover[OF wf solves]] cinit_le_init])
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
  shows "\<A>\<^bsub>declared_global p,call_context_rel_of_fun ctx_fun,root_ctx,
           prog_cfg p,cinit_stores (declared_global p)\<^esub> v ctx
           \<subseteq> gamma_lift gamma\<^sub>V (map_lift (rd (declared_global p))
                 (reader (declared_global p) p (Inl (v, ctx))))"
proof (rule activation_collect_sound_live_unknowns[OF wf solves])
  fix u ctx dst pars args q cont and s :: store and ctx'
  assume "(u, ctx) \<in> live_unknowns p"
    and "(u, CallEdge dst pars args, FunctionEntry q, cont) \<in> calls (prog_cfg p)"
    and Rc: "call_context_rel_of_fun ctx_fun u ctx (call_info_of (CallEdge dst pars args) q) s
               (call_enter (declared_global p) (CallEdge dst pars args) s) ctx'"
  show "route (declared_global p) u ctx
          (entry_of (declared_global p) p (call_info_of (CallEdge dst pars args) q)
             (dg_local (sol_env (declared_global p) p (Inl (u, ctx)))))
          (CallEdge dst pars args) = ctx'"
    using Rc
    by (simp add:
      route_const[of _ _ _ _ "call_enter (declared_global p) (CallEdge dst pars args) s"])
next
  fix u ctx dst pars args q cont and s :: store
  show "\<exists>ctx'. call_context_rel_of_fun ctx_fun u ctx (call_info_of (CallEdge dst pars args) q) s
                 (call_enter (declared_global p) (CallEdge dst pars args) s) ctx'"
    by simp
qed

text \<open>
  The same fact read off the published surface, and what it yields at a program
  point, at a check and at a source run. A store reaching a point lies in one of
  the point's contexts, so the point is bounded by the union of the states published
  there. At the unit policy the union has the one member \<open>()\<close>.
\<close>

theorem fun_route_state_at_sound:
  fixes ctx_fun :: "cfg_node \<Rightarrow> 'c \<Rightarrow> store \<Rightarrow> 'c"
  assumes route_const: "\<And>u ctx d ca s. route (declared_global p) u ctx d ca = ctx_fun u ctx s"
    and wf: "wf_program_compile_input p" and solves: "terminates (declared_global p) p"
  shows "\<A>\<^bsub>declared_global p,call_context_rel_of_fun ctx_fun,root_ctx,
           prog_cfg p,cinit_stores (declared_global p)\<^esub> v ctx
           \<subseteq> gamma\<^sub>V (state_at (declared_global p) p ctx v)"
proof -
  have "\<A>\<^bsub>declared_global p,call_context_rel_of_fun ctx_fun,root_ctx,
          prog_cfg p,cinit_stores (declared_global p)\<^esub> v ctx
        \<subseteq> gamma_lift gamma\<^sub>V (lookup_context (result (declared_global p) p) v ctx)"
    using fun_route_activation_collect_sound_of_terminates[OF route_const wf solves]
    unfolding gamma_reader_eq_lookup .
  then show ?thesis
    by (auto simp: state_at_unfold bot_state_empty split: lifted.splits)
qed

theorem fun_route_result_node_sound:
  fixes ctx_fun :: "cfg_node \<Rightarrow> 'c \<Rightarrow> store \<Rightarrow> 'c"
  assumes route_const: "\<And>u ctx d ca s. route (declared_global p) u ctx d ca = ctx_fun u ctx s"
    and wf: "wf_program_compile_input p" and solves: "terminates (declared_global p) p"
  shows "\<C>\<^bsub>declared_global p,prog_cfg p,cinit_stores (declared_global p)\<^esub> v
           \<subseteq> (\<Union>ctx. gamma\<^sub>V (state_at (declared_global p) p ctx v))"
  using fun_route_node_collect_eq_Union[where ctx_fun = ctx_fun and p = p and v = v]
    fun_route_state_at_sound[OF route_const wf solves]
  by (simp add: SUP_mono')

theorem fun_route_report_proved_sound:
  fixes ctx_fun :: "cfg_node \<Rightarrow> 'c \<Rightarrow> store \<Rightarrow> 'c"
  assumes route_const: "\<And>u ctx d ca s. route (declared_global p) u ctx d ca = ctx_fun u ctx s"
    and wf: "wf_program_compile_input p" and solves: "terminates (declared_global p) p"
    and mem: "(v, c, Check_Proved) \<in> set (report (declared_global p) p ctx)"
  shows "\<forall>s \<in> \<A>\<^bsub>declared_global p,call_context_rel_of_fun ctx_fun,root_ctx,
                 prog_cfg p,cinit_stores (declared_global p)\<^esub> v ctx. truthy (\<lbrakk>c\<rbrakk>\<^sub>e s)"
proof -
  have fin: "finite (intra (prog_cfg p))"
    unfolding prog_cfg_def using compile_prog_finite by simp
  show ?thesis
    by (rule classify_checks_proved_sound
          [where g = "prog_cfg p" and env = "state_at (declared_global p) p ctx"
             and classify = classify and \<gamma>\<^sub>S = gamma\<^sub>V
             and reach = "\<lambda>v. \<A>\<^bsub>declared_global p,call_context_rel_of_fun ctx_fun,root_ctx,
                               prog_cfg p,cinit_stores (declared_global p)\<^esub> v ctx",
           OF fin _ classify_proved fun_route_state_at_sound[OF route_const wf solves]])
       (use mem in \<open>simp add: report_def state_at_def analysis_surface.report_def\<close>)
qed

theorem fun_route_report_refuted_sound:
  fixes ctx_fun :: "cfg_node \<Rightarrow> 'c \<Rightarrow> store \<Rightarrow> 'c"
  assumes route_const: "\<And>u ctx d ca s. route (declared_global p) u ctx d ca = ctx_fun u ctx s"
    and wf: "wf_program_compile_input p" and solves: "terminates (declared_global p) p"
    and mem: "(v, c, Check_Refuted) \<in> set (report (declared_global p) p ctx)"
  shows "\<forall>s \<in> \<A>\<^bsub>declared_global p,call_context_rel_of_fun ctx_fun,root_ctx,
                 prog_cfg p,cinit_stores (declared_global p)\<^esub> v ctx. \<not> truthy (\<lbrakk>c\<rbrakk>\<^sub>e s)"
proof -
  have fin: "finite (intra (prog_cfg p))"
    unfolding prog_cfg_def using compile_prog_finite by simp
  show ?thesis
    by (rule classify_checks_refuted_sound
          [where g = "prog_cfg p" and env = "state_at (declared_global p) p ctx"
             and classify = classify and \<gamma>\<^sub>S = gamma\<^sub>V
             and reach = "\<lambda>v. \<A>\<^bsub>declared_global p,call_context_rel_of_fun ctx_fun,root_ctx,
                               prog_cfg p,cinit_stores (declared_global p)\<^esub> v ctx",
           OF fin _ classify_refuted fun_route_state_at_sound[OF route_const wf solves]])
       (use mem in \<open>simp add: report_def state_at_def analysis_surface.report_def\<close>)
qed

theorem fun_route_source_sound:
  fixes ctx_fun :: "cfg_node \<Rightarrow> 'c \<Rightarrow> store \<Rightarrow> 'c" and s0 s :: store
  assumes route_const: "\<And>u ctx d ca s. route (declared_global p) u ctx d ca = ctx_fun u ctx s"
    and wf: "wf_program_compile_input p" and solves: "terminates (declared_global p) p"
    and s0: "s0 \<in> cinit_stores (declared_global p)"
    and run: "declared_global p, prog_table p \<turnstile> (main_body (prog_table p), s0, [])
                \<rightarrow>\<^sub>p\<^sup>* (residual, s, frs)"
  shows "\<exists>v stk ctx. prog_table p, prog_cfg p \<turnstile> (residual, s, frs) \<approx> (v, s, stk)
           \<and> s \<in> gamma\<^sub>V (state_at (declared_global p) p ctx v)"
proof -
  have cfg_eq: "prog_cfg p = compile_prog (prog_table p) (prog_procs p)"
    by (rule prog_cfg_def)
  have "\<exists>v stk. prog_table p, prog_cfg p \<turnstile> (residual, s, frs) \<approx> (v, s, stk)
          \<and> s \<in> (\<Union>ctx. gamma\<^sub>V (state_at (declared_global p) p ctx v))"
    unfolding cfg_eq
    by (rule source_sound_from_node_collect_cap[OF wf s0 run])
       (use fun_route_result_node_sound[OF route_const wf solves] in \<open>simp add: cfg_eq\<close>)
  then show ?thesis by blast
qed

subsection \<open>Entry-state routing\<close>

lemma entry_state_routed_analysis_sound_live_unknowns:
  assumes wf: "wf_program_compile_input p" and solves: "terminates (declared_global p) p"
  shows "routed_analysis (analysis_spec (declared_global p) p)
     (\<lambda>d g. gamma_lift gamma\<^sub>V (map_lift (rd (declared_global p)) d))
     (declared_global p) (prog_cfg p) analysis_global (route (declared_global p)) Bot (Lifted init_st) Bot
     (sol_env (declared_global p) p) (live_unknowns p) (root_query p) seed (\<lambda>d. d = Bot)
     (admitted_contexts (declared_global p) p)
     (map_lift (rd (declared_global p))) gamma\<^sub>V empty\<^sub>V classify"
proof (rule routed_analysis_sound_live_unknowns[OF wf solves])
  fix u ctx dst pars args q cont and s :: store and ctx'
  assume "(u, ctx) \<in> live_unknowns p"
    and "(u, CallEdge dst pars args, FunctionEntry q, cont) \<in> calls (prog_cfg p)"
    and Rc: "admitted_contexts (declared_global p) p u ctx
               (call_info_of (CallEdge dst pars args) q) s
               (call_enter (declared_global p) (CallEdge dst pars args) s) ctx'"
  let ?ci = "call_info_of (CallEdge dst pars args) q"
  let ?caller = "dg_local (sol_env (declared_global p) p (Inl (u, ctx)))"
  let ?ent = "entry_of (declared_global p) p ?ci ?caller"
  from Rc[unfolded admitted_contexts_alt] obtain cont' entry
    where mem: "(cont', entry) \<in> set [(?caller, ?ent)]"
      and req0: "ctx' = route (declared_global p) u ctx entry
                   (CallEdge (ci_dst ?ci) (ci_formals ?ci) (ci_args ?ci))"
    by (rule routed_entry_context_relE)
  show "route (declared_global p) u ctx ?ent (CallEdge dst pars args) = ctx'"
    using mem req0 by simp
next
  fix u ctx dst pars args q cont and s :: store
  assume "(u, ctx) \<in> live_unknowns p"
    and "(u, CallEdge dst pars args, FunctionEntry q, cont) \<in> calls (prog_cfg p)"
    and sin:
      "s \<in> gamma_lift gamma\<^sub>V (map_lift (rd (declared_global p)) (dg_local (sol_env (declared_global p) p (Inl (u, ctx)))))"
  show "\<exists>ctx'. admitted_contexts (declared_global p) p u ctx
                 (call_info_of (CallEdge dst pars args) q) s
                 (call_enter (declared_global p) (CallEdge dst pars args) s) ctx'"
    unfolding admitted_contexts_alt
    by (rule routed_entry_context_rel_total)
       (use entry_cover[OF sin, where ci = "call_info_of (CallEdge dst pars args) q"] in simp)
qed

theorem entry_state_activation_collect_sound_of_terminates:
  assumes wf: "wf_program_compile_input p" and solves: "terminates (declared_global p) p"
  shows "\<A>\<^bsub>declared_global p,admitted_contexts (declared_global p) p,
           root_ctx,prog_cfg p,cinit_stores (declared_global p)\<^esub> v ctx
           \<subseteq> gamma_lift gamma\<^sub>V (map_lift (rd (declared_global p))
                 (reader (declared_global p) p (Inl (v, ctx))))"
proof -
  interpret live: routed_analysis "analysis_spec (declared_global p) p"
      "\<lambda>d g. gamma_lift gamma\<^sub>V (map_lift (rd (declared_global p)) d)"
      "declared_global p" "prog_cfg p" analysis_global "route (declared_global p)" Bot
        "Lifted init_st" Bot
      "sol_env (declared_global p) p" "live_unknowns p" "root_query p" seed "\<lambda>d. d = Bot"
      "admitted_contexts (declared_global p) p"
      "map_lift (rd (declared_global p))" gamma\<^sub>V empty\<^sub>V classify
    by (rule entry_state_routed_analysis_sound_live_unknowns[OF wf solves])
  have "\<A>\<^bsub>declared_global p,admitted_contexts (declared_global p) p,
          root_ctx,prog_cfg p,cinit_stores (declared_global p)\<^esub> v ctx
        \<subseteq> gamma_lift gamma\<^sub>V (map_lift (rd (declared_global p))
             (solved_local_reader (live_unknowns p) (sol_env (declared_global p) p) (Inl (v, ctx))))"
    by (rule live.activation_collect_dg_sound
          [OF ctx_vars_cover_live_entryD[OF live_unknowns_cover[OF wf solves]] cinit_le_init])
  then show ?thesis using gamma_live_reader_le by blast
qed

corollary entry_state_lookup_sound_of_terminates:
  assumes wf: "wf_program_compile_input p" and solves: "terminates (declared_global p) p"
  shows "\<A>\<^bsub>declared_global p,admitted_contexts (declared_global p) p,
           root_ctx,prog_cfg p,cinit_stores (declared_global p)\<^esub> v ctx
           \<subseteq> gamma_lift gamma\<^sub>V (lookup_context (result (declared_global p) p) v ctx)"
  using entry_state_activation_collect_sound_of_terminates[OF wf solves]
  unfolding gamma_reader_eq_lookup .

theorem entry_state_node_collect_eq_Union_of_terminates:
  assumes wf: "wf_program_compile_input p" and solves: "terminates (declared_global p) p"
  shows "\<C>\<^bsub>declared_global p,prog_cfg p,cinit_stores (declared_global p)\<^esub> v
           = (\<Union>ctx. \<A>\<^bsub>declared_global p,admitted_contexts (declared_global p) p,
                       root_ctx,prog_cfg p,cinit_stores (declared_global p)\<^esub> v ctx)"
proof (rule node_collect_eq_Union_activation_of_has_context)
  interpret live: routed_analysis "analysis_spec (declared_global p) p"
      "\<lambda>d g. gamma_lift gamma\<^sub>V (map_lift (rd (declared_global p)) d)"
      "declared_global p" "prog_cfg p" analysis_global "route (declared_global p)" Bot
        "Lifted init_st" Bot
      "sol_env (declared_global p) p" "live_unknowns p" "root_query p" seed "\<lambda>d. d = Bot"
      "admitted_contexts (declared_global p) p"
      "map_lift (rd (declared_global p))" gamma\<^sub>V empty\<^sub>V classify
    by (rule entry_state_routed_analysis_sound_live_unknowns[OF wf solves])
  fix t
  assume "t \<in> \<T>\<^bsub>declared_global p,prog_cfg p,cinit_stores (declared_global p)\<^esub>"
  then show "\<exists>c. activation_context_rel (declared_global p) (admitted_contexts (declared_global p) p)
                   root_ctx (prog_cfg p) t c"
    by (rule live.routed_valid_activation_trace_has_context
          [OF ctx_vars_cover_live_entryD[OF live_unknowns_cover[OF wf solves]] cinit_le_init])
qed

end

end

end
