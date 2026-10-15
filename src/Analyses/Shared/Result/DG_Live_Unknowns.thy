theory DG_Live_Unknowns
  imports DG_Analysis "Voblint_Compile.Live_Nodes"
begin

section \<open>Which solved keys a terminating solve is closed on\<close>

text \<open>
  The key set a terminating solve returns is not one the soundness argument can use as it
  stands: it may hold keys the solver queried under an earlier value and no longer reads,
  and keys of procedures whose result it never solved.  \<open>glive_unknowns\<close> keeps a solved key
  when its node belongs to a procedure (\<^theory>\<open>Voblint_Compile.Live_Nodes\<close>) whose result
  is solved at the same context.  From what each generated equation reads under the final
  valuation, \<open>glive_unknowns_cover\<close> shows that set closed under every intra edge, every call
  continuation and every call that enters a live state, with no premise beyond termination
  and a well-formed program.  The endpoints below restate the routed soundness over these
  keys and carry it to the published table.
\<close>

subsection \<open>What a routed equation reads\<close>

lemma dep_aux_routed_node_rhs:
  assumes wf: "\<And>w. \<forall>q \<in> set (routed_contribution_programs pred_sel site_sel route
                     it cmb extra g cx w). sp_wf q"
  shows "dep_aux \<tau> (routed_node_rhs pred_sel site_sel buffer_key_at route it cmb extra g bot0 d\<^sub>0 g\<^sub>0
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
  shows "(u, cx) \<in> dep\<^sub>L (routed_node_rhs intra_predecessor_addr_list call_site_list buffer_key_at route
            (\<lambda>cx src a. dg_spec_edge_program S a src slot) cmb extra g bot0 d\<^sub>0 g\<^sub>0) \<tau> (v, cx)"
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
  shows "dep_program \<tau> (routed_call_program S global_of seed resolve is_bot route ctx ca cc v)
     = insert (Inl (cc, ctx))
         (\<Union>q\<in>set (resolve v cc ca (dg_local (\<tau> (Inl (cc, ctx))))).
            dep_program \<tau> (routed_callee_call_program S global_of seed route is_bot ctx ca cc
                        (dg_local (\<tau> (Inl (cc, ctx)))) q))"
  by (simp add: routed_call_program_def sp_compile_bind sp_wf_observes
      dep_program_side_rhs_fold_dg_char[OF sp_wf_routed_callee_call_programs[OF wfS]])

lemma routed_call_program_mem:
  assumes fin: "finite (calls g)" and e: "(u, ca, FunctionEntry q, k) \<in> calls g"
  shows "routed_call_program S global_of seed resolve is_bot route cx ca u k
           \<in> set (routed_contribution_programs pred_sel call_site_list route it
                    (routed_call_program S global_of seed resolve is_bot) extra g cx k)"
proof -
  have "(u, ca) \<in> set (call_site_list g k)" using e fin by auto
  then show ?thesis by (rule routed_contribution_programs_combineI)
qed

lemma dep_L_routed_node_rhs_call_site:
  assumes fin: "finite (calls g)" and e: "(u, ca, FunctionEntry q, k) \<in> calls g"
    and wfS: "dg_spec_wf S"
    and wf: "\<And>w. \<forall>q \<in> set (routed_contribution_programs pred_sel call_site_list route it
                     (routed_call_program S global_of seed resolve is_bot) extra g cx w). sp_wf q"
  shows "(u, cx) \<in> dep\<^sub>L (routed_node_rhs pred_sel call_site_list buffer_key_at route it
            (routed_call_program S global_of seed resolve is_bot) extra g bot0 d\<^sub>0 g\<^sub>0) \<tau> (k, cx)"
proof -
  have "Inl (u, cx)
          \<in> dep_program \<tau> (routed_call_program S global_of seed resolve is_bot route cx ca u k)"
    by (simp add: dep_program_routed_call_program[OF wfS])
  then show ?thesis
    unfolding dep\<^sub>L_def dep_def
    using routed_call_program_mem
            [OF fin e, of S global_of seed resolve is_bot route cx pred_sel it extra]
    by (auto simp: dep_aux_routed_node_rhs[OF wf])
qed

lemma dep_L_routed_node_rhs_callee_result:
  assumes fin: "finite (calls g)" and e: "(u, ca, FunctionEntry q, k) \<in> calls g"
    and deps: "enter_deps (enter\<^sup>\<sharp> S (call_info_of ca q))
                 (mk_dg_man (dg_local (\<tau> (Inl (u, cx)))) global_of) \<tau> pairs D"
    and mem: "(c, ent) \<in> set pairs"
    and res: "q \<in> set (resolve k u ca (dg_local (\<tau> (Inl (u, cx)))))"
    and nb: "\<not> is_bot ent"
    and wfS: "dg_spec_wf S"
    and wf: "\<And>w. \<forall>q \<in> set (routed_contribution_programs pred_sel call_site_list route it
                     (routed_call_program S global_of seed resolve is_bot) extra g cx w). sp_wf q"
  shows "(FunctionResult q, route u cx ent ca)
           \<in> dep\<^sub>L (routed_node_rhs pred_sel call_site_list buffer_key_at route it
                (routed_call_program S global_of seed resolve is_bot) extra g bot0 d\<^sub>0 g\<^sub>0) \<tau> (k, cx)"
proof -
  let ?d = "dg_local (\<tau> (Inl (u, cx)))"
  have callee: "dep_program \<tau> (routed_callee_call_program S global_of seed route is_bot cx ca u ?d q)
      = D \<union> dep_program \<tau> (side_rhs_fold_dg bot
          (map (routed_call_alternative_program S global_of seed route is_bot cx ca u q) pairs))"
    unfolding routed_callee_call_program_def sp_compile_bind
    by (rule enter_depsD[OF deps, simplified])
  have "Inl (FunctionResult q, route u cx ent ca)
          \<in> dep_program \<tau> (routed_callee_call_program S global_of seed route is_bot cx ca u ?d q)"
  proof -
    have "Inl (FunctionResult q, route u cx ent ca)
            \<in> dep_program \<tau> (routed_call_alternative_program S global_of seed route is_bot cx ca u q
                           (c, ent))"
      using nb by (simp add: routed_call_alternative_program_def Let_def)
    then show ?thesis
      unfolding callee
        dep_program_side_rhs_fold_dg_char[OF sp_wf_routed_call_alternative_programs[OF wfS]]
      using mem by auto
  qed
  then have "Inl (FunctionResult q, route u cx ent ca)
               \<in> dep_program \<tau> (routed_call_program S global_of seed resolve is_bot route cx ca u k)"
    using res by (auto simp: dep_program_routed_call_program[OF wfS])
  then show ?thesis
    unfolding dep\<^sub>L_def dep_def
    using routed_call_program_mem
            [OF fin e, of S global_of seed resolve is_bot route cx pred_sel it extra]
    by (auto simp: dep_aux_routed_node_rhs[OF wf])
qed

subsection \<open>Keys of a solve whose activation returned\<close>

text \<open>
  The solved key set is closed under the equations' reads (\<open>gsol_vars_dep_closed\<close>).
  Walking those reads backwards, \<open>glive_unknowns_cover\<close> shows \<open>glive_unknowns\<close> closed
  under intra edges, call continuations and the entries of callees a call actually enters.
\<close>

context gdg_analysis
begin

context
  fixes ptab :: "'p \<Rightarrow> ('ann, 'vr, 'e) gptable" and pprocs :: "'p \<Rightarrow> pname list"
    and vars :: "'e \<Rightarrow> 'vr set"
  assumes pcfg_compile: "\<And>p. pcfg p = compile_prog (ptab p) (pprocs p)"
begin

lemma ganalysis_contribs_wf [simp]:
  "\<forall>q \<in> set (routed_contribution_programs intra_predecessor_addr_list call_site_list
       (route (pglob p))
       (\<lambda>ctx' src a. dg_spec_edge_program (analysis_spec (pglob p) p) a src
          global_of)
       (routed_call_program (analysis_spec (pglob p) p) global_of seed rsv
          (\<lambda>d. d = Bot))
       (routed_entry_seed_programs seed) cfg cx w). sp_wf q"
  by (rule routed_contribution_programs_wf) auto

lemma gsol_vars_dep_closed:
  assumes solves: "terminates (pglob p) p"
    and x: "x \<in> sol_vars (pglob p) p"
    and y: "y \<in> dep\<^sub>L
       (routed_node_rhs intra_predecessor_addr_list call_site_list (\<lambda>_. buffer_key)
          (route (pglob p))
          (\<lambda>ctx' src a. dg_spec_edge_program (analysis_spec (pglob p) p) a src global_of)
          (routed_call_program (analysis_spec (pglob p) p) global_of seed
             (static_resolve (pcfg p)) (\<lambda>d. d = Bot))
          (routed_entry_seed_programs seed)
          (pcfg p) Bot (Lifted init_st) (place_rg (pglob p) (Lifted init_st)))
       (sol_env (pglob p) p) x"
  shows "y \<in> sol_vars (pglob p) p"
  using pp_routed[OF solves] x y by blast

lemma gprog_cfg_finite: "finite (intra (pcfg p))" "finite (calls (pcfg p))"
  unfolding pcfg_compile by (simp_all add: compile_prog_finite)

lemma gsol_vars_back_intra:
  assumes solves: "terminates (pglob p) p"
    and v: "(v, cx) \<in> sol_vars (pglob p) p" and e: "(u, a, v) \<in> intra (pcfg p)"
  shows "(u, cx) \<in> sol_vars (pglob p) p"
  by (rule gsol_vars_dep_closed
        [OF solves v dep_L_routed_node_rhs_intra[OF gprog_cfg_finite(1) e ganalysis_contribs_wf]])

lemma gsol_vars_back_call_site:
  assumes solves: "terminates (pglob p) p"
    and k: "(k, cx) \<in> sol_vars (pglob p) p"
    and e: "(u, ca, FunctionEntry q, k) \<in> calls (pcfg p)"
  shows "(u, cx) \<in> sol_vars (pglob p) p"
  by (rule gsol_vars_dep_closed
        [OF solves k dep_L_routed_node_rhs_call_site
           [OF gprog_cfg_finite(2) e dg_spec_wf_analysis_spec ganalysis_contribs_wf]])

lemma gsol_vars_callee_result:
  assumes solves: "terminates (pglob p) p"
    and k: "(k, cx) \<in> sol_vars (pglob p) p"
    and e: "(u, ca, FunctionEntry q, k) \<in> calls (pcfg p)"
    and nb: "entry_of (pglob p) p (call_info_of ca q)
               (dg_local (sol_env (pglob p) p (Inl (u, cx))))
               (sol_global (pglob p) p) \<noteq> Bot"
  shows "(FunctionResult q, ctx_succ (pglob p) p u cx ca q)
           \<in> sol_vars (pglob p) p"
proof -
  let ?d = "dg_local (sol_env (pglob p) p (Inl (u, cx)))"
  let ?alt =
    "entry_alt (pglob p) p (call_info_of ca q) ?d (sol_global (pglob p) p)"
  have res: "q \<in> set (static_resolve (pcfg p) k u ca ?d)"
    using e gprog_cfg_finite(2) by simp
  obtain D where deps: "enter_deps (enter\<^sup>\<sharp> (analysis_spec (pglob p) p) (call_info_of ca q))
      (mk_dg_man ?d global_of) (sol_env (pglob p) p) [?alt] D"
    using gplace_enter_deps unfolding sol_global_def by blast
  have mem: "(fst ?alt, snd ?alt) \<in> set [?alt]" by simp
  show ?thesis
    unfolding ctx_succ_def entry_of_def
    by (rule gsol_vars_dep_closed[OF solves k],
        rule dep_L_routed_node_rhs_callee_result[where resolve = "static_resolve (pcfg p)"
            and \<tau> = "sol_env (pglob p) p" and cx = cx,
          OF gprog_cfg_finite(2) e deps mem res])
       (use nb in \<open>simp add: entry_of_def\<close>, rule dg_spec_wf_analysis_spec, rule
         ganalysis_contribs_wf)
qed

lemma gsol_vars_back_reach:
  assumes solves: "terminates (pglob p) p"
    and w: "(w, cx) \<in> sol_vars (pglob p) p"
    and r: "local_reaches (pcfg p) y w"
  shows "(y, cx) \<in> sol_vars (pglob p) p"
  using r[unfolded local_reaches_def]
proof (induction rule: converse_rtrancl_induct)
  case base show ?case by (rule w)
next
  case (step y z)
  from step.hyps(1) show ?case
    unfolding local_succ_rel_def
    using gsol_vars_back_intra[OF solves step.IH] gsol_vars_back_call_site[OF solves step.IH]
    by blast
qed
definition glive_unknowns :: "'p \<Rightarrow> (pp \<times> 'c) set" where
  "glive_unknowns p =
     {(u, cx) \<in> sol_vars (pglob p) p.
        \<exists>q. prog_node (ptab p) (pprocs p) q u
          \<and> (FunctionResult q, cx) \<in> sol_vars (pglob p) p}"

lemma glive_unknowns_sub: "glive_unknowns p \<subseteq> sol_vars (pglob p) p"
  unfolding glive_unknowns_def by blast

lemma glive_unknowns_of_result:
  assumes wf: "gwf_compile_input vars rv (pglob p) (ptab p) (pprocs p)" and solves:
    "terminates (pglob p) p"
    and live: "prog_node (ptab p) (pprocs p) q y"
    and r: "(FunctionResult q, cx) \<in> sol_vars (pglob p) p"
  shows "(y, cx) \<in> glive_unknowns p"
proof -
  have "local_reaches (pcfg p) y (FunctionResult q)"
    unfolding pcfg_compile by (rule prog_node_reaches[OF live])
  then have "(y, cx) \<in> sol_vars (pglob p) p" by (rule gsol_vars_back_reach[OF solves r])
  then show ?thesis unfolding glive_unknowns_def using live r by blast
qed

theorem glive_unknowns_cover:
  assumes wf: "gwf_compile_input vars rv (pglob p) (ptab p) (pprocs p)" and solves:
    "terminates (pglob p) p"
  shows "ctx_vars_cover_live (pcfg p) (\<lambda>_ _. True) (live_succ (pglob p) p)
           root_ctx (glive_unknowns p)"
proof (rule ctx_vars_cover_liveI)
  have root: "(FunctionResult prog_main_name, root_ctx) \<in> sol_vars (pglob p) p"
    using pp_routed[OF solves] by (simp add: root_query_def pcfg_compile)
  show "(cfg_entry (pcfg p), root_ctx) \<in> glive_unknowns p"
    using glive_unknowns_of_result[OF wf solves prog_node_main_entry[OF wf] root]
    by (simp add: pcfg_compile)
next
  fix u a v ctx
  assume u: "(u, ctx) \<in> glive_unknowns p" and e: "(u, a, v) \<in> intra (pcfg p)"
  from u obtain q where lq: "prog_node (ptab p) (pprocs p) q u"
    and r: "(FunctionResult q, ctx) \<in> sol_vars (pglob p) p"
    unfolding glive_unknowns_def by blast
  have "prog_node (ptab p) (pprocs p) q v"
    using prog_node_intra[OF wf lq] e by (simp add: pcfg_compile)
  then show "(v, ctx) \<in> glive_unknowns p" by (rule glive_unknowns_of_result[OF wf solves _ r])
next
  fix u ctx dst fs as q k
  assume u: "(u, ctx) \<in> glive_unknowns p"
    and e: "(u, CallEdge dst fs as, FunctionEntry q, k) \<in> calls (pcfg p)"
  from u obtain r where lr: "prog_node (ptab p) (pprocs p) r u"
    and res: "(FunctionResult r, ctx) \<in> sol_vars (pglob p) p"
    unfolding glive_unknowns_def by blast
  have "prog_node (ptab p) (pprocs p) r k"
    using prog_node_calls[OF wf lr] e by (simp add: pcfg_compile)
  then show "(k, ctx) \<in> glive_unknowns p" by (rule glive_unknowns_of_result[OF wf solves _ res])
next
  fix u ctx dst fs as q k ctx'
  assume u: "(u, ctx) \<in> glive_unknowns p"
    and e: "(u, CallEdge dst fs as, FunctionEntry q, k) \<in> calls (pcfg p)"
    and s: "live_succ (pglob p) p u ctx (CallEdge dst fs as) q = Some ctx'"
  from u obtain r where lr: "prog_node (ptab p) (pprocs p) r u"
    and res: "(FunctionResult r, ctx) \<in> sol_vars (pglob p) p"
    unfolding glive_unknowns_def by blast
  have "prog_node (ptab p) (pprocs p) r k"
    using prog_node_calls[OF wf lr] e by (simp add: pcfg_compile)
  then have k: "(k, ctx) \<in> sol_vars (pglob p) p"
    using glive_unknowns_of_result[OF wf solves _ res] glive_unknowns_sub by blast
  from s have nb: "entry_of (pglob p) p (call_info_of (CallEdge dst fs as) q)
               (dg_local (sol_env (pglob p) p (Inl (u, ctx))))
               (sol_global (pglob p) p) \<noteq> Bot"
    and c': "ctx' = ctx_succ (pglob p) p u ctx (CallEdge dst fs as) q"
    by (auto simp: live_succ_def split: if_splits)
  have rq: "(FunctionResult q, ctx') \<in> sol_vars (pglob p) p"
    unfolding c' by (rule gsol_vars_callee_result[OF solves k e nb])
  have "prog_node (ptab p) (pprocs p) q (FunctionEntry q)"
    using prog_node_callee_entry[OF wf] e by (simp add: pcfg_compile)
  then show "(FunctionEntry q, ctx') \<in> glive_unknowns p"
    by (rule glive_unknowns_of_result[OF wf solves _ rq])
qed

lemma groot_live_key:
  assumes wf: "gwf_compile_input vars rv (pglob p) (ptab p) (pprocs p)" and solves:
    "terminates (pglob p) p"
  shows "root_query p \<in> glive_unknowns p"
proof -
  have r: "(FunctionResult prog_main_name, root_ctx) \<in> sol_vars (pglob p) p"
    using pp_routed[OF solves] by (simp add: root_query_def pcfg_compile)
  show ?thesis
    using glive_unknowns_of_result[OF wf solves prog_node_result[OF prog_node_main_entry[OF wf]] r]
    by (simp add: root_query_def pcfg_compile)
qed
subsection \<open>The entry-state endpoint over the live keys\<close>

text \<open>
  The routed soundness statement restated over \<open>glive_unknowns\<close>, whose coverage
  needs no premise beyond termination, and carried to the published table and
  the source-level endpoints under the functional context policy.
\<close>

context
  fixes p :: 'p
begin

interpretation dg_base: ganalysis_contract ev rv "pconv p" "pglob p" "analysis_spec (pglob p) p"
    "\<lambda>d e. pgam p d e"
  by (rule gplace_contract)

text \<open>
  Establishes \<open>grouted_analysis\<close> over the live keys, for any relation admitting call contexts.
  Beyond termination and well-formedness a policy owes only its own two facts: an
  admitted context is the one this pipeline routes the entered state to, and every
  concrete call at a live key is admitted somewhere. \<open>glive_unknowns_cover\<close> supplies
  callee-entry membership.
\<close>

lemma grouted_analysis_from_live_unknowns:
  fixes adm :: "('vr, 'e, 'c) gcontext_policy"
  assumes wf: "gwf_compile_input vars rv (pglob p) (ptab p) (pprocs p)" and solves:
    "terminates (pglob p) p"
    and cover_R: "\<And>u ctx dst pars args q cont s ctx'. (u, ctx) \<in> glive_unknowns p
        \<Longrightarrow> (u, CallEdge dst pars args, FunctionEntry q, cont) \<in> calls (pcfg p)
        \<Longrightarrow> ctx' \<in> adm u ctx (call_info_of (CallEdge dst pars args) q) s
              (cfg_transfer_sem.gcall_enter ev (pconv p) (pglob p) (CallEdge dst pars args) s)
        \<Longrightarrow> route (pglob p) u ctx
              (entered p (call_info_of (CallEdge dst pars args) q)
                 (dg_local (sol_env (pglob p) p (Inl (u, ctx)))))
              (CallEdge dst pars args) = ctx'"
    and total_R: "\<And>u ctx dst pars args q cont s. (u, ctx) \<in> glive_unknowns p
        \<Longrightarrow> (u, CallEdge dst pars args, FunctionEntry q, cont) \<in> calls (pcfg p)
        \<Longrightarrow> s \<in> pgam p (dg_local (sol_env (pglob p) p (Inl (u, ctx)))) (gsol p)
        \<Longrightarrow> adm u ctx (call_info_of (CallEdge dst pars args) q) s
                      (cfg_transfer_sem.gcall_enter ev (pconv p) (pglob p) (CallEdge dst pars args) s) \<noteq> {}"
  shows "grouted_analysis ev rv (pconv p) (pglob p) (analysis_spec (pglob p) p) (\<lambda>d e. pgam p d e) (pcfg p) buffer_key global_of
     (route (pglob p)) Bot (Lifted init_st)
     (place_rg (pglob p) (Lifted init_st))
     (sol_env (pglob p) p) (glive_unknowns p) (root_query p) seed (\<lambda>d. d = Bot) adm
     (\<lambda>d e. map_lift (rd (pglob p)) (place_cmb p d e))
     \<gamma>\<^sub>V empty\<^sub>V classify"
proof (unfold_locales, goal_cases CmbWf ExtraWf FinE PP SgCov SgUncov Fwd FinC CallsUnique
    SeedUnknown SeedNeGlobal IsBotBot IsBotSound ResolveSound EnterCover EnterTotal CombFwd GammaRd
    EmptyExact ClProved ClRefuted VarsFin)
  case CmbWf show ?case by (rule sp_wf_routed_call_program[OF dg_spec_wf_analysis_spec])
next
  case ExtraWf then show ?case by (rule sp_wf_routed_entry_seed_programs)
next
  case FinE show ?case unfolding pcfg_compile by (simp add: compile_prog_finite)
next
  case PP show ?case
    by (rule post_bounded_subset[OF post_bounded_of_part_post_solution[OF pp_routed[OF solves]]
          groot_live_key[OF wf solves] glive_unknowns_sub])
next
  case (SgCov v c) then show ?case by simp
next
  case (SgUncov v c) then show ?case by simp
next
  case (Fwd u a v c)
  show ?case
    by (rule ctx_vars_cover_live_edgeD[OF glive_unknowns_cover[OF wf solves] Fwd(1) _ Fwd(3)]) simp
next
  case FinC show ?case unfolding pcfg_compile by (simp add: compile_prog_finite)
next
  case CallsUnique show ?case
    unfolding calls_source_unique_def pcfg_compile
    using compile_prog_calls_source_unique by blast
next
  case (SeedUnknown q ctx) show ?case by (rule gseed_ne_buffer_key)
next
  case (SeedNeGlobal q ctx v) show ?case by (rule gseed_ne_global_of)
next  case IsBotBot show ?case by simp
next
  case (IsBotSound d g') then show ?case by simp
next
  case (ResolveSound u ctx dst pars args q cont s)
  then show ?case unfolding pcfg_compile by (simp add: compile_prog_finite)
next
  case (EnterCover u ctx dst pars args q cont s ctx')
  let ?ci = "call_info_of (CallEdge dst pars args) q"
  let ?caller = "dg_local (sol_env (pglob p) p (Inl (u, ctx)))"
  let ?g = "genv global_of (sol_env (pglob p) p)"
  let ?ent = "entered p ?ci ?caller"
  have sin: "s \<in> pgam p ?caller (gsol p)"
    using EnterCover(3) by (simp add: sol_global_def)
  have cov: "entry_pairs_cover (\<lambda>d. pgam p d (gsol p)) s
      (cfg_transfer_sem.gcall_enter ev (pconv p) (pglob p) (CallEdge dst pars args) s)
      [entry_alt (pglob p) p ?ci ?caller (gsol p)]"
  proof (rule entry_cover[OF solves _ EnterCover(2) sin])
    show "(cont, ctx) \<in> sol_vars (pglob p) p"
      using ctx_vars_cover_live_combineD[OF glive_unknowns_cover[OF wf solves] EnterCover(1,2)]
        glive_unknowns_sub by blast
  qed
  obtain c e where ce: "entry_alt (pglob p) p ?ci ?caller (gsol p) = (c, e)"
    by (cases "entry_alt (pglob p) p ?ci ?caller (gsol p)")
  have nbE: "?ent \<noteq> Bot"
  proof
    assume "?ent = Bot"
    with cov ce show False by (simp add: entry_pairs_cover_def entry_of_def gplace_cmb_bot)
  qed
  have req: "route (pglob p) u ctx ?ent (CallEdge dst pars args) = ctx'"
    by (rule cover_R[OF EnterCover(1,2,4)])
  have covE: "(FunctionEntry q, ctx') \<in> glive_unknowns p"
    by (rule ctx_vars_cover_live_enterD[OF glive_unknowns_cover[OF wf solves] EnterCover(1,2)])
       (use nbE req in \<open>simp add: live_succ_def ctx_succ_def\<close>)
  obtain pub where runs: "enter_runs (enter\<^sup>\<sharp> (analysis_spec (pglob p) p) ?ci)
      (mk_dg_man ?caller global_of) (sol_env (pglob p) p)
      [entry_alt (pglob p) p ?ci ?caller ?g] pub"
    using gplace_enter_runs by blast
  obtain deps where deps: "enter_deps (enter\<^sup>\<sharp> (analysis_spec (pglob p) p) ?ci)
      (mk_dg_man ?caller global_of) (sol_env (pglob p) p)
      [entry_alt (pglob p) p ?ci ?caller ?g] deps"
    using gplace_enter_deps by blast
  have ce': "entry_alt (pglob p) p ?ci ?caller ?g = (c, e)"
    using ce by (simp add: sol_global_def)
  have sc: "s \<in> pgam p c ?g"
    and ec:
      "cfg_transfer_sem.gcall_enter ev (pconv p) (pglob p) (CallEdge dst pars args) s \<in> pgam p e ?g"
    using cov ce by (simp_all add: entry_pairs_cover_def sol_global_def)
  have re: "route (pglob p) u ctx e (CallEdge dst pars args) = ctx'"
    using req ce by (simp add: entry_of_def)
  show ?case
    using runs deps sc ec re covE unfolding ce' by fastforce
next
  case (EnterTotal u ctx dst pars args q cont s)
  then show ?case by (intro total_R) (simp_all add: sol_global_def)
next
  case (CombFwd cl c1 dst pars args q cont)
  show ?case
    by (rule ctx_vars_cover_live_combineD[OF glive_unknowns_cover[OF wf solves] CombFwd(1,2)])
next
  case (GammaRd d g') show ?case by simp
next
  case (EmptyExact v) then show ?case by (rule empty\<^sub>V_soundD)
next
  case (ClProved c d s) then show ?case by (rule gclassify_proved)
next
  case (ClRefuted c d s) then show ?case by (rule gclassify_refuted)
next
  case VarsFin show ?case
    by (rule finite_subset[OF glive_unknowns_sub vars_finite_of_terminates[OF solves]])
qed

text \<open>
  The reader over the live keys agrees with the published one on them and describes
  nothing elsewhere, so a bound proved for it is a bound on the published table.
\<close>

lemma ggamma_live_reader_le:
  "pgam p (solved_local_reader (glive_unknowns p) (sol_env (pglob p) p) (Inl (v, ctx)))
       (gsol p)
     \<subseteq> pgam p (reader (pglob p) p (Inl (v, ctx))) (gsol p)"
proof (cases "(v, ctx) \<in> glive_unknowns p")
  case True
  then have "(v, ctx) \<in> sol_vars (pglob p) p" by (rule subsetD[OF glive_unknowns_sub])
  with True show ?thesis by (simp add: reader_def)
next
  case False then show ?thesis by (simp add: gplace_cmb_bot)
qed

theorem gactivation_collect_sound_live_unknowns:
  fixes adm :: "('vr, 'e, 'c) gcontext_policy"
  assumes wf: "gwf_compile_input vars rv (pglob p) (ptab p) (pprocs p)" and solves:
    "terminates (pglob p) p"
    and cover_R: "\<And>u ctx dst pars args q cont s ctx'. (u, ctx) \<in> glive_unknowns p
        \<Longrightarrow> (u, CallEdge dst pars args, FunctionEntry q, cont) \<in> calls (pcfg p)
        \<Longrightarrow> ctx' \<in> adm u ctx (call_info_of (CallEdge dst pars args) q) s
              (cfg_transfer_sem.gcall_enter ev (pconv p) (pglob p) (CallEdge dst pars args) s)
        \<Longrightarrow> route (pglob p) u ctx
              (entered p (call_info_of (CallEdge dst pars args) q)
                 (dg_local (sol_env (pglob p) p (Inl (u, ctx)))))
              (CallEdge dst pars args) = ctx'"
    and total_R: "\<And>u ctx dst pars args q cont s. (u, ctx) \<in> glive_unknowns p
        \<Longrightarrow> (u, CallEdge dst pars args, FunctionEntry q, cont) \<in> calls (pcfg p)
        \<Longrightarrow> s \<in> pgam p (dg_local (sol_env (pglob p) p (Inl (u, ctx)))) (gsol p)
        \<Longrightarrow> adm u ctx (call_info_of (CallEdge dst pars args) q) s
                      (cfg_transfer_sem.gcall_enter ev (pconv p) (pglob p) (CallEdge dst pars args) s) \<noteq> {}"
  shows "ctx_sem.gactivation_collect ev rv (pconv p) (pglob p) (adm) (root_ctx) (pcfg p) (pinit p) v ctx
           \<subseteq> pgam p (reader (pglob p) p (Inl (v, ctx))) (gsol p)"
proof -
  interpret live: grouted_analysis ev rv "pconv p" "pglob p" "analysis_spec (pglob p) p"
    "\<lambda>d e. pgam p d e" "pcfg p" buffer_key global_of
      "route (pglob p)" Bot
        "Lifted init_st" "place_rg (pglob p) (Lifted init_st)"
      "sol_env (pglob p) p" "glive_unknowns p" "root_query p" seed "\<lambda>d. d = Bot" adm
      "\<lambda>d e. map_lift (rd (pglob p)) (place_cmb p d e)"
      \<gamma>\<^sub>V empty\<^sub>V classify
    by (rule grouted_analysis_from_live_unknowns[where adm = adm, OF wf solves cover_R total_R])
  have entry_cov: "(cfg_entry (pcfg p), root_ctx) \<in> glive_unknowns p"
    by (rule ctx_vars_cover_live_entryD[OF glive_unknowns_cover[OF wf solves]])
  have init_env_le:
    "init_env (pglob p) p \<le> genv global_of (sol_env (pglob p) p)"
    using init_env_le_sol[OF solves subsetD[OF glive_unknowns_sub entry_cov]
      live.pp_entry_init_global_bound[OF entry_cov]]
    by (simp add: sol_global_def)
  have "ctx_sem.gactivation_collect ev rv (pconv p) (pglob p) (adm) (root_ctx) (pcfg p) (pinit p) v ctx
        \<subseteq> pgam p (solved_local_reader (glive_unknowns p) (sol_env (pglob p) p) (Inl (v, ctx)))
             (gsol p)"
    using live.activation_collect_dg_sound
        [OF entry_cov _ init_env_le, of "pinit p" v ctx] cinit_le_init
    by (simp add: sol_global_def)
  then show ?thesis using ggamma_live_reader_le by blast
qed

text \<open>
  A policy whose route ignores the entered state --- a call string, or the unit
  context --- admits exactly the context it computes, so both of its facts are
  immediate.
\<close>

theorem gfun_route_activation_collect_sound_of_terminates:
  fixes ctx_fun :: "cfg_node \<Rightarrow> 'c \<Rightarrow> ('vr \<Rightarrow> int) \<Rightarrow> 'c"
  assumes route_const: "\<And>u ctx d ca s. route (pglob p) u ctx d ca = ctx_fun u ctx s"
    and wf: "gwf_compile_input vars rv (pglob p) (ptab p) (pprocs p)" and solves:
      "terminates (pglob p) p"
  shows "ctx_sem.gactivation_collect ev rv (pconv p) (pglob p) (context_policy_of_fun ctx_fun) (root_ctx) (pcfg p) (pinit p) v ctx
           \<subseteq> pgam p (reader (pglob p) p (Inl (v, ctx))) (gsol p)"
proof (rule gactivation_collect_sound_live_unknowns[OF wf solves])
  fix u ctx dst pars args q cont and s :: "'vr \<Rightarrow> int" and ctx'
  assume "(u, ctx) \<in> glive_unknowns p"
    and "(u, CallEdge dst pars args, FunctionEntry q, cont) \<in> calls (pcfg p)"
    and Rc: "ctx' \<in> context_policy_of_fun ctx_fun u ctx (call_info_of (CallEdge dst pars args) q) s
               (cfg_transfer_sem.gcall_enter ev (pconv p) (pglob p) (CallEdge dst pars args) s)"
  show "route (pglob p) u ctx
          (entered p (call_info_of (CallEdge dst pars args) q)
             (dg_local (sol_env (pglob p) p (Inl (u, ctx)))))
          (CallEdge dst pars args) = ctx'"
    using Rc
    by (simp add:
      route_const[of _ _ _ _
        "cfg_transfer_sem.gcall_enter ev (pconv p) (pglob p) (CallEdge dst pars args) s"])
next
  fix u ctx dst pars args q cont and s :: "'vr \<Rightarrow> int"
  show "context_policy_of_fun ctx_fun u ctx (call_info_of (CallEdge dst pars args) q) s
                 (cfg_transfer_sem.gcall_enter ev (pconv p) (pglob p) (CallEdge dst pars args) s) \<noteq> {}"
    by simp
qed

text \<open>
  The same fact read off the published surface, and what it yields at a program
  point, at a check and at a source run. A store reaching a point lies in one of
  the point's contexts, so the point is bounded by the union of the states published
  there. At the unit policy the union has the one member \<open>()\<close>.
\<close>

theorem gfun_route_state_at_sound:
  fixes ctx_fun :: "cfg_node \<Rightarrow> 'c \<Rightarrow> ('vr \<Rightarrow> int) \<Rightarrow> 'c"
  assumes route_const: "\<And>u ctx d ca s. route (pglob p) u ctx d ca = ctx_fun u ctx s"
    and wf: "gwf_compile_input vars rv (pglob p) (ptab p) (pprocs p)" and solves:
      "terminates (pglob p) p"
  shows "ctx_sem.gactivation_collect ev rv (pconv p) (pglob p) (context_policy_of_fun ctx_fun) (root_ctx) (pcfg p) (pinit p) v ctx
           \<subseteq> \<gamma>\<^sub>V (state_at (pglob p) p ctx v)"
proof -
  have "ctx_sem.gactivation_collect ev rv (pconv p) (pglob p) (context_policy_of_fun ctx_fun) (root_ctx) (pcfg p) (pinit p) v ctx
        \<subseteq> gamma_lift \<gamma>\<^sub>V (lookup_table (result (pglob p) p) v ctx)"
    using gfun_route_activation_collect_sound_of_terminates[OF route_const wf solves]
    unfolding gamma_reader_eq_lookup .
  then show ?thesis
    by (auto simp: state_at_unfold gbot_state_empty split: lifted.splits)
qed

theorem gfun_route_result_node_sound:
  fixes ctx_fun :: "cfg_node \<Rightarrow> 'c \<Rightarrow> ('vr \<Rightarrow> int) \<Rightarrow> 'c"
  assumes route_const: "\<And>u ctx d ca s. route (pglob p) u ctx d ca = ctx_fun u ctx s"
    and wf: "gwf_compile_input vars rv (pglob p) (ptab p) (pprocs p)" and solves:
      "terminates (pglob p) p"
  shows "collect_sem.gnode_collect ev rv (pconv p) (pglob p) (pcfg p) (pinit p) v
           \<subseteq> (\<Union>ctx. \<gamma>\<^sub>V (state_at (pglob p) p ctx v))"
  using fun_route_node_collect_eq_Union[where ctx_fun = ctx_fun and p = p and v = v]
    gfun_route_state_at_sound[OF route_const wf solves]
  by (simp add: SUP_mono')

theorem gfun_route_report_proved_sound:
  fixes ctx_fun :: "cfg_node \<Rightarrow> 'c \<Rightarrow> ('vr \<Rightarrow> int) \<Rightarrow> 'c"
  assumes route_const: "\<And>u ctx d ca s. route (pglob p) u ctx d ca = ctx_fun u ctx s"
    and wf: "gwf_compile_input vars rv (pglob p) (ptab p) (pprocs p)" and solves:
      "terminates (pglob p) p"
    and mem: "(v, c, Check_Proved) \<in> set (report (pglob p) p ctx)"
  shows
    "\<forall>s \<in> ctx_sem.gactivation_collect ev rv (pconv p) (pglob p) (context_policy_of_fun ctx_fun) (root_ctx) (pcfg p) (pinit p) v ctx. truthy (ev c s)"
proof -
  have fin: "finite (intra (pcfg p))"
    unfolding pcfg_compile by (simp add: compile_prog_finite)
  show ?thesis
    by (rule gclassify_checks_proved_sound
          [where g = "pcfg p" and env = "state_at (pglob p) p ctx"
             and classify = classify and \<gamma>\<^sub>S = \<gamma>\<^sub>V
             and reach =
               "\<lambda>v. ctx_sem.gactivation_collect ev rv (pconv p) (pglob p) (context_policy_of_fun ctx_fun) (root_ctx) (pcfg p) (pinit p) v ctx",
           OF fin _ gclassify_proved gfun_route_state_at_sound[OF route_const wf solves]])
       (use mem in \<open>simp add: report_def state_at_def analysis_surface.report_def\<close>)
qed

theorem gfun_route_report_refuted_sound:
  fixes ctx_fun :: "cfg_node \<Rightarrow> 'c \<Rightarrow> ('vr \<Rightarrow> int) \<Rightarrow> 'c"
  assumes route_const: "\<And>u ctx d ca s. route (pglob p) u ctx d ca = ctx_fun u ctx s"
    and wf: "gwf_compile_input vars rv (pglob p) (ptab p) (pprocs p)" and solves:
      "terminates (pglob p) p"
    and mem: "(v, c, Check_Refuted) \<in> set (report (pglob p) p ctx)"
  shows
    "\<forall>s \<in> ctx_sem.gactivation_collect ev rv (pconv p) (pglob p) (context_policy_of_fun ctx_fun) (root_ctx) (pcfg p) (pinit p) v ctx. \<not> truthy (ev c s)"
proof -
  have fin: "finite (intra (pcfg p))"
    unfolding pcfg_compile by (simp add: compile_prog_finite)
  show ?thesis
    by (rule gclassify_checks_refuted_sound
          [where g = "pcfg p" and env = "state_at (pglob p) p ctx"
             and classify = classify and \<gamma>\<^sub>S = \<gamma>\<^sub>V
             and reach =
               "\<lambda>v. ctx_sem.gactivation_collect ev rv (pconv p) (pglob p) (context_policy_of_fun ctx_fun) (root_ctx) (pcfg p) (pinit p) v ctx",
           OF fin _ gclassify_refuted gfun_route_state_at_sound[OF route_const wf solves]])
       (use mem in \<open>simp add: report_def state_at_def analysis_surface.report_def\<close>)
qed

subsection \<open>Entry-state routing\<close>

text \<open>
  Instantiates the live-key endpoints at \<open>admitted_contexts\<close>, the policy that routes
  a call by its entered state. Its two policy facts hold by construction, so the
  results need only termination and a well-formed program.
\<close>

lemma gentry_state_routed_analysis_from_live_unknowns:
  assumes wf: "gwf_compile_input vars rv (pglob p) (ptab p) (pprocs p)" and solves:
    "terminates (pglob p) p"
  shows "grouted_analysis ev rv (pconv p) (pglob p) (analysis_spec (pglob p) p) (\<lambda>d e. pgam p d e) (pcfg p) buffer_key global_of
     (route (pglob p)) Bot (Lifted init_st)
     (place_rg (pglob p) (Lifted init_st))
     (sol_env (pglob p) p) (glive_unknowns p) (root_query p) seed (\<lambda>d. d = Bot)
     (admitted_contexts (pglob p) p)
     (\<lambda>d e. map_lift (rd (pglob p)) (place_cmb p d e))
     \<gamma>\<^sub>V empty\<^sub>V classify"
proof (rule grouted_analysis_from_live_unknowns[OF wf solves])
  fix u ctx dst pars args q cont and s :: "'vr \<Rightarrow> int" and ctx'
  assume "(u, ctx) \<in> glive_unknowns p"
    and "(u, CallEdge dst pars args, FunctionEntry q, cont) \<in> calls (pcfg p)"
    and Rc: "ctx' \<in> admitted_contexts (pglob p) p u ctx
               (call_info_of (CallEdge dst pars args) q) s
               (cfg_transfer_sem.gcall_enter ev (pconv p) (pglob p) (CallEdge dst pars args) s)"
  let ?ci = "call_info_of (CallEdge dst pars args) q"
  let ?caller = "dg_local (sol_env (pglob p) p (Inl (u, ctx)))"
  let ?ent = "entered p ?ci ?caller"
  from Rc[unfolded admitted_contexts_alt] obtain cont' entry
    where mem: "(cont', entry) \<in> set [entry_alt (pglob p) p ?ci ?caller (gsol p)]"
      and req0: "ctx' = route (pglob p) u ctx entry
                   (CallEdge (ci_dst ?ci) (ci_formals ?ci) (ci_args ?ci))"
    by (rule routed_entry_context_relE)
  have "entry = ?ent" using mem by (simp add: entry_of_def) (metis snd_conv)
  then show "route (pglob p) u ctx ?ent (CallEdge dst pars args) = ctx'"
    using req0 by simp
next
  fix u ctx dst pars args q cont and s :: "'vr \<Rightarrow> int"
  assume uL: "(u, ctx) \<in> glive_unknowns p"
    and ce: "(u, CallEdge dst pars args, FunctionEntry q, cont) \<in> calls (pcfg p)"
    and sin: "s \<in> pgam p (dg_local (sol_env (pglob p) p (Inl (u, ctx)))) (gsol p)"
  have cont: "(cont, ctx) \<in> sol_vars (pglob p) p"
    using ctx_vars_cover_live_combineD[OF glive_unknowns_cover[OF wf solves] uL ce]
      glive_unknowns_sub by blast
  show "admitted_contexts (pglob p) p u ctx
                 (call_info_of (CallEdge dst pars args) q) s
                 (cfg_transfer_sem.gcall_enter ev (pconv p) (pglob p) (CallEdge dst pars args) s) \<noteq> {}"
    unfolding admitted_contexts_alt
    by (rule routed_entry_context_rel_total)
       (use entry_cover[OF solves cont ce sin]
         in \<open>simp add: sol_global_def\<close>)
qed

theorem gentry_state_activation_collect_sound_of_terminates:
  assumes wf: "gwf_compile_input vars rv (pglob p) (ptab p) (pprocs p)" and solves:
    "terminates (pglob p) p"
  shows "ctx_sem.gactivation_collect ev rv (pconv p) (pglob p) (admitted_contexts (pglob p) p) (root_ctx) (pcfg p) (pinit p) v ctx
           \<subseteq> pgam p (reader (pglob p) p (Inl (v, ctx))) (gsol p)"
proof -
  interpret live: grouted_analysis ev rv "pconv p" "pglob p" "analysis_spec (pglob p) p"
    "\<lambda>d e. pgam p d e" "pcfg p" buffer_key global_of
      "route (pglob p)" Bot
        "Lifted init_st" "place_rg (pglob p) (Lifted init_st)"
      "sol_env (pglob p) p" "glive_unknowns p" "root_query p" seed "\<lambda>d. d = Bot"
      "admitted_contexts (pglob p) p"
      "\<lambda>d e. map_lift (rd (pglob p)) (place_cmb p d e)"
      \<gamma>\<^sub>V empty\<^sub>V classify
    by (rule gentry_state_routed_analysis_from_live_unknowns[OF wf solves])
  have entry_cov: "(cfg_entry (pcfg p), root_ctx) \<in> glive_unknowns p"
    by (rule ctx_vars_cover_live_entryD[OF glive_unknowns_cover[OF wf solves]])
  have init_env_le:
    "init_env (pglob p) p \<le> genv global_of (sol_env (pglob p) p)"
    using init_env_le_sol[OF solves subsetD[OF glive_unknowns_sub entry_cov]
      live.pp_entry_init_global_bound[OF entry_cov]]
    by (simp add: sol_global_def)
  have "ctx_sem.gactivation_collect ev rv (pconv p) (pglob p) (admitted_contexts (pglob p) p) (root_ctx) (pcfg p) (pinit p) v ctx
        \<subseteq> pgam p (solved_local_reader (glive_unknowns p) (sol_env (pglob p) p) (Inl (v, ctx)))
             (gsol p)"
    using live.activation_collect_dg_sound
        [OF entry_cov _ init_env_le, of "pinit p" v ctx] cinit_le_init
    by (simp add: sol_global_def)
  then show ?thesis using ggamma_live_reader_le by blast
qed

corollary gentry_state_lookup_sound_of_terminates:
  assumes wf: "gwf_compile_input vars rv (pglob p) (ptab p) (pprocs p)" and solves:
    "terminates (pglob p) p"
  shows "ctx_sem.gactivation_collect ev rv (pconv p) (pglob p) (admitted_contexts (pglob p) p) (root_ctx) (pcfg p) (pinit p) v ctx
           \<subseteq> gamma_lift \<gamma>\<^sub>V (lookup_table (result (pglob p) p) v ctx)"
  using gentry_state_activation_collect_sound_of_terminates[OF wf solves]
  unfolding gamma_reader_eq_lookup .

lemma gentry_state_has_context_of_terminates:
  assumes wf: "gwf_compile_input vars rv (pglob p) (ptab p) (pprocs p)" and solves:
    "terminates (pglob p) p"
    and t: "t \<in> trace_sem.gvalid_activation_trace ev rv (pconv p) (pglob p) (pcfg p) (pinit p)"
  shows "\<exists>c. ctx_sem.gactivation_context_rel ev (pconv p) (pglob p) (admitted_contexts (pglob p) p)
               root_ctx (pcfg p) t c"
proof -
  interpret live: grouted_analysis ev rv "pconv p" "pglob p" "analysis_spec (pglob p) p"
    "\<lambda>d e. pgam p d e" "pcfg p" buffer_key global_of
      "route (pglob p)" Bot
        "Lifted init_st" "place_rg (pglob p) (Lifted init_st)"
      "sol_env (pglob p) p" "glive_unknowns p" "root_query p" seed "\<lambda>d. d = Bot"
      "admitted_contexts (pglob p) p"
      "\<lambda>d e. map_lift (rd (pglob p)) (place_cmb p d e)"
      \<gamma>\<^sub>V empty\<^sub>V classify
    by (rule gentry_state_routed_analysis_from_live_unknowns[OF wf solves])
  have entry_cov: "(cfg_entry (pcfg p), root_ctx) \<in> glive_unknowns p"
    by (rule ctx_vars_cover_live_entryD[OF glive_unknowns_cover[OF wf solves]])
  have init_env_le:
    "init_env (pglob p) p \<le> genv global_of (sol_env (pglob p) p)"
    using init_env_le_sol[OF solves subsetD[OF glive_unknowns_sub entry_cov]
      live.pp_entry_init_global_bound[OF entry_cov]]
    by (simp add: sol_global_def)
  show ?thesis
    using live.routed_valid_activation_trace_has_context[OF entry_cov _ init_env_le t] cinit_le_init
    by simp
qed

theorem gentry_state_node_collect_eq_Union_of_terminates:
  assumes wf: "gwf_compile_input vars rv (pglob p) (ptab p) (pprocs p)" and solves:
    "terminates (pglob p) p"
  shows "collect_sem.gnode_collect ev rv (pconv p) (pglob p) (pcfg p) (pinit p) v
           = (\<Union>ctx. ctx_sem.gactivation_collect ev rv (pconv p) (pglob p) (admitted_contexts (pglob p) p) (root_ctx) (pcfg p) (pinit p) v ctx)"
  by (rule collect_sem.node_collect_eq_Union_activation_of_has_context)
     (rule gentry_state_has_context_of_terminates[OF wf solves])

end

end

end

end
