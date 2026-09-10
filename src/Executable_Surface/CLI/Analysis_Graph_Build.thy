theory Analysis_Graph_Build
  imports Analysis_Graph
begin

section \<open>Building the graph from a solved result\<close>

text \<open>
  A solved analysis knows which contexts it covered at each program point, but
  not in what order, and not which of them belong together. This theory turns
  that into a graph: one cluster per (procedure, context) pair, one node per
  covered key, and one edge per routed step --- ordinary control flow, a call
  entering a procedure, a return combining back, and the call-to-return arc
  beside it, plus the reads and writes of a shared global.

  \<open>build_analysis_graph\<close> is the whole construction, and
  \<open>analysis_graph_wf\<close> at the end states what it produces: distinct
  clusters, distinct nodes, distinct edges, and every edge between nodes that
  are actually present. Nothing here assumes that; \<open>Analysis_Graph_Wf\<close>, which
  sits above this theory, proves it always holds.
\<close>

subsection \<open>The graph domain of a result\<close>

text \<open>
  Every \<^typ>\<open>pp\<close> the CFG has, paired with exactly the contexts covered at
  it. Coverage stays the result's own extensional key set ---
  \<^const>\<open>contexts_at\<close> is a membership question, never a traversal --- and only
  the sequence the pairs are laid out in comes from the chosen ordering.
\<close>

definition result_contexts_at ::
  "('ctx, 'g, 'a, 'd) analysis_graph_config \<Rightarrow> ('ctx, 'v) analysis_result
    \<Rightarrow> pp \<Rightarrow> 'ctx list" where
  "result_contexts_at cfg r p = ordered_by_key (context_key cfg) (contexts_at r p)"

definition contextual_result_domain ::
  "('ctx, 'g, 'a, 'd) analysis_graph_config \<Rightarrow> cfg \<Rightarrow> ('ctx, 'v) analysis_result
    \<Rightarrow> ((pp \<times> 'ctx) + 'g) list" where
  "contextual_result_domain cfg g r = contextual_graph_domain g (result_contexts_at cfg r)"

record procedure_scope =
  scope_formals :: "vname list"
  scope_locals :: "vname list"
  scope_return_slot :: "vname option"

fun action_defined_vars :: "edge_action \<Rightarrow> vname list" where
  "action_defined_vars (EA_Assign x e) = [x]"
| "action_defined_vars (EA_Special sc x) = [x]"
| "action_defined_vars _ = []"

definition owner_assigned_vars ::
  "cfg \<Rightarrow> (pp \<Rightarrow> pname) \<Rightarrow> pname \<Rightarrow> vname list" where
  "owner_assigned_vars g point_owner owner =
    remdups
      (concat (map (\<lambda>(u, a, _).
         if point_owner u = owner then action_defined_vars a else [])
         (cfg_intra_list g)) @
       concat (map (\<lambda>(call, ca, _, _).
         if point_owner call = owner then
           (case ca of CallEdge None _ _ \<Rightarrow> []
             | CallEdge (Some x) _ _ \<Rightarrow> [x])
         else []) (cfg_calls_list g)))"

definition compiled_procedure_scope ::
  "(vname \<Rightarrow> bool) \<Rightarrow> proc_table \<Rightarrow> pname list \<Rightarrow> cfg \<Rightarrow> pp \<Rightarrow> procedure_scope" where
  "compiled_procedure_scope gs \<Pi> ps g p =
    (let owner = compiled_owner_of \<Pi> ps p;
         decl = \<Pi> owner;
         fs = if owner = prog_main_name then [] else
           (case decl of None \<Rightarrow> [] | Some d \<Rightarrow> formals d);
         ret = if owner = prog_main_name then None else Some ret_var;
         ls = filter (\<lambda>x. x \<notin> set fs \<and> x \<noteq> ret_var \<and> \<not> gs x)
           (owner_assigned_vars g (compiled_owner_of \<Pi> ps) owner)
     in \<lparr>scope_formals = fs, scope_locals = ls, scope_return_slot = ret\<rparr>)"


definition visible_global ::
  "('ctx, 'g, 'a, 'd) analysis_graph_config \<Rightarrow> 'g \<Rightarrow> bool" where
  "visible_global cfg k =
    (is_shared_global cfg k \<or> show_internal_globals cfg)"

definition covered_local_nodes ::
  "(pp \<times> 'ctx) list \<Rightarrow> ('ctx, 'g) analysis_node list" where
  "covered_local_nodes covered = map (\<lambda>pc. LocalNode (fst pc) (snd pc)) covered"

definition analysis_context_clusters ::
  "('ctx, 'g, 'a, 'd) analysis_graph_config \<Rightarrow> (pp \<times> 'ctx) list
    \<Rightarrow> ('ctx, 'g) analysis_cluster list" where
  "analysis_context_clusters cfg covered =
    remdups (map (\<lambda>pc. ContextCluster (owner_of cfg (fst pc)) (snd pc)) covered)"

definition rendered_global ::
  "('ctx, 'g, 'a, 'd) analysis_graph_config
    \<Rightarrow> (pp \<times> 'ctx + 'g \<Rightarrow> 'a) \<Rightarrow> 'g \<Rightarrow> bool" where
  "rendered_global cfg sol k =
    (visible_global cfg k \<and>
     show_global cfg k (globals_to_show cfg) (sol (Inr k)) \<noteq> [])"

definition analysis_global_nodes ::
  "('ctx, 'g, 'a, 'd) analysis_graph_config
    \<Rightarrow> (pp \<times> 'ctx + 'g \<Rightarrow> 'a) \<Rightarrow> 'g list
    \<Rightarrow> ('ctx, 'g) analysis_node list" where
  "analysis_global_nodes cfg sol keys =
    map GlobalNode (filter (rendered_global cfg sol) (remdups keys))"

definition analysis_source_nodes ::
  "('ctx, 'g, 'a, 'd) analysis_graph_config \<Rightarrow> ('ctx, 'g) analysis_node list" where
  "analysis_source_nodes cfg =
    (case source_text cfg of None \<Rightarrow> [] | Some src \<Rightarrow> [SourceNode src])"

definition analysis_global_cluster ::
  "('ctx, 'g) analysis_node list \<Rightarrow> ('ctx, 'g) analysis_cluster list" where
  "analysis_global_cluster ns =
    (if list_ex (\<lambda>n. case n of GlobalNode _ \<Rightarrow> True | _ \<Rightarrow> False) ns
     then [GlobalCluster] else [])"

definition analysis_source_cluster ::
  "('ctx, 'g) analysis_node list \<Rightarrow> ('ctx, 'g) analysis_cluster list" where
  "analysis_source_cluster ns =
    (if list_ex (\<lambda>n. case n of SourceNode _ \<Rightarrow> True | _ \<Rightarrow> False) ns
     then [SourceCluster] else [])"

text \<open>
  Every edge group walks the same two lists --- the covered keys, then the graph's own
  edge enumeration --- and emits at most one edge per pair. Writing that as
  \<^const>\<open>List.map_filter\<close> over \<^const>\<open>List.product\<close> says so directly, and it is what
  makes the group's well-formedness provable: an edge's producing pair is recoverable
  from the edge, so \<^const>\<open>List.product\<close>'s distinctness carries over. The enumeration
  order is unchanged --- \<^const>\<open>List.product\<close> is first-argument-major, exactly like the
  nested walk it replaces.
\<close>

definition analysis_intra_edges ::
  "cfg \<Rightarrow> (pp \<times> 'ctx) list
    \<Rightarrow> (('ctx, 'g) analysis_node \<times> analysis_edge_kind \<times>
       ('ctx, 'g) analysis_node) list" where
  "analysis_intra_edges g covered =
    List.map_filter
      (\<lambda>(src_ctx, u, a, v).
         if fst src_ctx = u \<and> (v, snd src_ctx) \<in> set covered
         then Some (LocalNode u (snd src_ctx), IntraEdge a, LocalNode v (snd src_ctx))
         else None)
      (List.product covered (cfg_intra_list g))"

definition analysis_enter_edges ::
  "('ctx, 'g, 'a, 'd) analysis_graph_config \<Rightarrow> cfg \<Rightarrow> (pp \<times> 'ctx) list
    \<Rightarrow> (pp \<times> 'ctx + 'g \<Rightarrow> 'a)
    \<Rightarrow> (('ctx, 'g) analysis_node \<times> analysis_edge_kind \<times>
       ('ctx, 'g) analysis_node) list" where
  "analysis_enter_edges cfg g covered sol =
    List.map_filter
      (\<lambda>(src_ctx, u, ca, entry, cont).
         if fst src_ctx = u then
           (case route cfg u (snd src_ctx) ca (local_of cfg (sol (Inl src_ctx))) of
              None \<Rightarrow> None
            | Some callee_ctx \<Rightarrow>
                if (entry, callee_ctx) \<in> set covered
                then Some (LocalNode u (snd src_ctx), EnterEdge (owner_of cfg entry) ca,
                           LocalNode entry callee_ctx)
                else None)
         else None)
      (List.product covered (cfg_calls_list g))"

definition analysis_combine_edges ::
  "('ctx, 'g, 'a, 'd) analysis_graph_config \<Rightarrow> cfg \<Rightarrow> (pp \<times> 'ctx) list
    \<Rightarrow> (pp \<times> 'ctx + 'g \<Rightarrow> 'a)
    \<Rightarrow> (('ctx, 'g) analysis_node \<times> analysis_edge_kind \<times>
       ('ctx, 'g) analysis_node) list" where
  "analysis_combine_edges cfg g covered sol =
    List.map_filter
      (\<lambda>(src_ctx, call, ca, entry, cont).
         case entry of
           FunctionEntry p \<Rightarrow>
             if fst src_ctx = call then
               (case route cfg call (snd src_ctx) ca (local_of cfg (sol (Inl src_ctx))) of
                  None \<Rightarrow> None
                | Some callee_ctx \<Rightarrow>
                    if (FunctionResult p, callee_ctx) \<in> set covered \<and>
                       (cont, snd src_ctx) \<in> set covered
                    then Some (LocalNode (FunctionResult p) callee_ctx,
                               CombineEdge call (case ca of CallEdge dst _ _ \<Rightarrow> dst)
                                 (return_slot_for_pp cfg (FunctionResult p)),
                               LocalNode cont (snd src_ctx))
                    else None)
             else None
         | _ \<Rightarrow> None)
      (List.product covered (cfg_calls_list g))"

text \<open>
  Call sites and their continuations already share a context: @{term cont} is
  the fourth component of every @{term calls} tuple. This edge is purely presentational -- it draws
  that pairing directly, alongside the real interprocedural path through
  @{term EnterEdge} and @{term CombineEdge}, so a call site and its
  return-site stay visually linked even when the callee cluster sits
  elsewhere in the diagram.
\<close>

definition analysis_call_to_return_edges ::
  "('ctx, 'g, 'a, 'd) analysis_graph_config \<Rightarrow> cfg \<Rightarrow> (pp \<times> 'ctx) list
    \<Rightarrow> (('ctx, 'g) analysis_node \<times> analysis_edge_kind \<times>
       ('ctx, 'g) analysis_node) list" where
  "analysis_call_to_return_edges cfg g covered =
    List.map_filter
      (\<lambda>(src_ctx, call, ca, entry, cont).
         case entry of
           FunctionEntry p \<Rightarrow>
             if fst src_ctx = call \<and> (cont, snd src_ctx) \<in> set covered
             then Some (LocalNode call (snd src_ctx), CallToReturnEdge p,
                        LocalNode cont (snd src_ctx))
             else None
         | _ \<Rightarrow> None)
      (List.product covered (cfg_calls_list g))"

fun analysis_local_domain :: "((pp \<times> 'ctx) + 'g) list \<Rightarrow> (pp \<times> 'ctx) list" where
  "analysis_local_domain [] = []"
| "analysis_local_domain (Inl pc # domain) = pc # analysis_local_domain domain"
| "analysis_local_domain (Inr k # domain) = analysis_local_domain domain"

fun analysis_global_domain :: "((pp \<times> 'ctx) + 'g) list \<Rightarrow> 'g list" where
  "analysis_global_domain [] = []"
| "analysis_global_domain (Inl pc # domain) = analysis_global_domain domain"
| "analysis_global_domain (Inr k # domain) = k # analysis_global_domain domain"

definition build_analysis_graph_parts ::
  "('ctx, 'g, 'a, 'd) analysis_graph_config \<Rightarrow> cfg
    \<Rightarrow> (pp \<times> 'ctx) list \<Rightarrow> 'g list \<Rightarrow> (pp \<times> 'ctx + 'g \<Rightarrow> 'a)
    \<Rightarrow> ('ctx, 'g) analysis_graph" where
  "build_analysis_graph_parts cfg g covered global_keys sol =
    (let locals = covered_local_nodes covered;
         globals = analysis_global_nodes cfg sol global_keys;
         sources = analysis_source_nodes cfg;
         ns = locals @ globals @ sources
     in (analysis_context_clusters cfg covered @ analysis_global_cluster ns
           @ analysis_source_cluster ns,
         ns,
         analysis_intra_edges g covered @ analysis_enter_edges cfg g covered sol
           @ analysis_combine_edges cfg g covered sol
           @ analysis_call_to_return_edges cfg g covered))"

text \<open>The graph domain is an executable presentation choice.  Solver coverage remains
  extensional and can be checked propositionally by clients.\<close>

definition build_analysis_graph ::
  "('ctx, 'g, 'a, 'd) analysis_graph_config \<Rightarrow> cfg
    \<Rightarrow> ((pp \<times> 'ctx) + 'g) list \<Rightarrow> (pp \<times> 'ctx + 'g \<Rightarrow> 'a)
    \<Rightarrow> ('ctx, 'g) analysis_graph" where
  "build_analysis_graph cfg g domain sol =
    build_analysis_graph_parts cfg g (analysis_local_domain (remdups domain))
      (analysis_global_domain (remdups domain)) sol"


definition analysis_graph_wf ::
  "('ctx, 'g) analysis_graph \<Rightarrow> bool" where
  "analysis_graph_wf graph =
    (case graph of (clusters, ns, es) \<Rightarrow>
      distinct clusters \<and>
      distinct ns \<and>
      distinct es \<and>
      list_all (\<lambda>e. case e of (src, _, dst) \<Rightarrow> src \<in> set ns \<and> dst \<in> set ns) es)"

end
