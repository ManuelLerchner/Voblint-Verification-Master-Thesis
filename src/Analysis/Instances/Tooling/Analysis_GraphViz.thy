theory Analysis_GraphViz
  imports
    "Voblint_CFG.IMP2_Proc_to_CFG"
    "Voblint_IMP2.IMP2_Source_Print"
    TD_Side_CFG
    Exec_St
    Abstract_Domain
begin

text \<open>
  This theory provides the canonical graph model, raw-CFG builder, CFG action
  printers, DOT escaping helpers, and context-expanded analysis builder.
\<close>

definition prog_cfg_edges ::
    "proc_table \<Rightarrow> pname list \<Rightarrow> com \<Rightarrow> (pp \<times> edge_action \<times> pp) list" where
  "prog_cfg_edges \<Pi> ps main = cfg_edges_list (compile_prog \<Pi> ps main)"

definition prog_cfg_combines ::
    "proc_table \<Rightarrow> pname list \<Rightarrow> com
     \<Rightarrow> (pp \<times> pp \<times> pp \<times> vname option) list" where
  "prog_cfg_combines \<Pi> ps main = cfg_combines_list (compile_prog \<Pi> ps main)"

subsection \<open>CFG and DOT helpers\<close>

fun string_of_action :: "edge_action \<Rightarrow> string" where
  "string_of_action EA_Nop = ''nop''"
| "string_of_action (EA_Assign x a) = x @ '' := '' @ string_of_aexp a"
| "string_of_action (EA_Assume b) = ''['' @ string_of_bexp b @ '']''"
| "string_of_action (EA_AssumeNot b) = ''!['' @ string_of_bexp b @ '']''"
| "string_of_action (EA_Enter xs es) = ''enter''"

definition dq :: string where "dq = [CHR 0x22]"
definition nl :: string where "nl = [CHR 0x0A]"
definition gv_nl :: string where "gv_nl = [CHR 0x5C, CHR 0x6E]"

fun join_gv_nl :: "string list \<Rightarrow> string" where
  "join_gv_nl [] = []"
| "join_gv_nl [s] = s"
| "join_gv_nl (s # ss) = s @ gv_nl @ join_gv_nl ss"

fun graphviz_label_text :: "string \<Rightarrow> string" where
  "graphviz_label_text [] = []"
| "graphviz_label_text (ch # rest) =
    (if ch = CHR 0x0A then gv_nl else [ch]) @ graphviz_label_text rest"

fun enter_targets :: "(pp \<times> edge_action \<times> pp) list \<Rightarrow> pp list" where
  "enter_targets [] = []"
| "enter_targets ((u, EA_Enter xs es, v) # es') = v # enter_targets es'"
| "enter_targets (_ # es) = enter_targets es"

fun combine_exits :: "combine_info list \<Rightarrow> pp list" where
  "combine_exits [] = []"
| "combine_exits ((call, ex, ret, dst) # cs) = ex # combine_exits cs"

definition proc_entry_pps_list :: "cfg \<Rightarrow> pp list" where
  "proc_entry_pps_list g = enter_targets (cfg_edges_list g)"

definition proc_exit_pps_list :: "cfg \<Rightarrow> pp list" where
  "proc_exit_pps_list g = combine_exits (cfg_combines_list g)"

fun mem_pp :: "pp \<Rightarrow> pp list \<Rightarrow> bool" where
  "mem_pp v [] = False"
| "mem_pp v (x # xs) = (if v = x then True else mem_pp v xs)"

fun region_label :: "string option \<Rightarrow> string" where
  "region_label None = ''main''"
| "region_label (Some p) = p"

section \<open>Generic context-expanded analysis graph\<close>

text \<open>
  The analysis graph is independent of DOT.  It records contextual local nodes,
  shared global nodes, and the semantic role of every routed edge.  The builder
  consumes the same routing function as the equation generator.
\<close>

datatype ('ctx, 'g) analysis_cluster =
    ContextCluster string 'ctx
  | GlobalCluster
  | SourceCluster

datatype ('ctx, 'g) analysis_node =
    LocalNode pp 'ctx
  | GlobalNode 'g
  | SourceNode string

datatype analysis_edge_kind =
    IntraEdge edge_action
  | EnterEdge edge_action
  | CombineEdge pp "vname option" "vname option"
  | GlobalReadEdge
  | GlobalWriteEdge

type_synonym ('ctx, 'g) analysis_graph =
  "(('ctx, 'g) analysis_cluster list \<times>
    ('ctx, 'g) analysis_node list \<times>
    (('ctx, 'g) analysis_node \<times> analysis_edge_kind \<times>
      ('ctx, 'g) analysis_node) list)"

record ('ctx, 'g, 'a, 'd) analysis_graph_config =
  local_of :: "'a \<Rightarrow> 'd"
  route :: "pp \<Rightarrow> 'ctx \<Rightarrow> edge_action \<Rightarrow> 'd \<Rightarrow> 'ctx"
  show_context :: "'ctx \<Rightarrow> string"
  locals_for_pp :: "pp \<Rightarrow> vname list"
  return_slot_for_pp :: "pp \<Rightarrow> vname option"
  globals_to_show :: "vname list"
  show_local :: "pp \<Rightarrow> 'ctx \<Rightarrow> vname list \<Rightarrow> 'd \<Rightarrow> string list"
  format_return :: "pp \<Rightarrow> 'ctx \<Rightarrow> vname \<Rightarrow> 'd \<Rightarrow> string list"
  show_global :: "'g \<Rightarrow> vname list \<Rightarrow> 'a \<Rightarrow> string list"
  show_global_key :: "'g \<Rightarrow> string"
  is_shared_global :: "'g \<Rightarrow> bool"
  show_internal_globals :: bool
  owner_of :: "pp \<Rightarrow> string"
  cluster_label :: "string \<Rightarrow> 'ctx \<Rightarrow> string"
  source_text :: "string option"

fun graphviz_owner_of :: "(string option \<times> pp list) list \<Rightarrow> pp \<Rightarrow> string" where
  "graphviz_owner_of [] p = ''unknown''"
| "graphviz_owner_of ((owner, ps) # regions) p =
    (if mem_pp p ps then region_label owner else graphviz_owner_of regions p)"

definition compiled_owner_of ::
  "proc_table \<Rightarrow> pname list \<Rightarrow> com \<Rightarrow> pp \<Rightarrow> string" where
  "compiled_owner_of \<Pi> ps main p =
    graphviz_owner_of (compile_prog_regions \<Pi> ps main) p"

definition cfg_point_list :: "cfg \<Rightarrow> pp list" where
  "cfg_point_list g =
    remdups (cfg_entry g # cfg_exit g #
      (concat (map (\<lambda>e. case e of (u, a, v) \<Rightarrow> [u, v]) (cfg_edges_list g))
       @ concat (map (\<lambda>c. case c of (call, ex, ret, dst) \<Rightarrow> [call, ex, ret])
           (cfg_combines_list g))))"

definition contextual_graph_domain ::
  "cfg \<Rightarrow> (pp \<Rightarrow> 'ctx list) \<Rightarrow> ((pp \<times> 'ctx) + 'g) list" where
  "contextual_graph_domain g contexts_for_pp =
    concat (map (\<lambda>p. map (\<lambda>ctx. Inl (p, ctx)) (contexts_for_pp p))
      (cfg_point_list g))"

record procedure_scope =
  scope_formals :: "vname list"
  scope_locals :: "vname list"
  scope_return_slot :: "vname option"

fun graphviz_action_defs :: "edge_action \<Rightarrow> vname list" where
  "graphviz_action_defs (EA_Assign x e) = [x]"
| "graphviz_action_defs _ = []"

definition cfg_assigned_vars :: "cfg \<Rightarrow> vname list" where
  "cfg_assigned_vars g =
    remdups
      (concat (map (\<lambda>e. case e of (_, a, _) \<Rightarrow> graphviz_action_defs a)
        (cfg_edges_list g))
       @ concat (map (\<lambda>c. case c of (_, _, _, dst) \<Rightarrow>
           (case dst of None \<Rightarrow> [] | Some x \<Rightarrow> [x]))
         (cfg_combines_list g)))"

definition compiled_global_vars :: "cfg \<Rightarrow> vname list" where
  "compiled_global_vars g = filter is_global (cfg_assigned_vars g)"

definition owner_assigned_vars ::
  "cfg \<Rightarrow> (pp \<Rightarrow> string) \<Rightarrow> string \<Rightarrow> vname list" where
  "owner_assigned_vars g point_owner owner =
    remdups
      (concat (map (\<lambda>e. case e of (u, a, v) \<Rightarrow>
        if point_owner u = owner then graphviz_action_defs a else [])
        (cfg_edges_list g))
       @ concat (map (\<lambda>c. case c of (call, ex, ret, dst) \<Rightarrow>
           if point_owner call = owner then
             (case dst of None \<Rightarrow> [] | Some x \<Rightarrow> [x])
           else [])
         (cfg_combines_list g)))"

definition compiled_procedure_scope ::
  "proc_table \<Rightarrow> pname list \<Rightarrow> com \<Rightarrow> cfg \<Rightarrow> pp \<Rightarrow> procedure_scope" where
  "compiled_procedure_scope \<Pi> ps main g p =
    (let owner = compiled_owner_of \<Pi> ps main p;
         decl = \<Pi> owner;
         fs = if owner = ''main'' then [] else
           (case decl of None \<Rightarrow> [] | Some d \<Rightarrow> formals d);
         ret = if owner = ''main'' then None else
           Some ret_var;
         ls = filter (\<lambda>x. x \<notin> set fs \<and> x \<noteq> ret_var \<and> \<not> is_global x)
           (owner_assigned_vars g (compiled_owner_of \<Pi> ps main) owner)
     in \<lparr>scope_formals = fs, scope_locals = ls, scope_return_slot = ret\<rparr>)"

definition visible_global ::
  "('ctx, 'g, 'a, 'd) analysis_graph_config \<Rightarrow> 'g \<Rightarrow> bool" where
  "visible_global cfg k =
    (is_shared_global cfg k \<or> show_internal_globals cfg)"

definition covered_local_nodes ::
  "(pp \<times> 'ctx) list \<Rightarrow> ('ctx, 'g) analysis_node list" where
  "covered_local_nodes covered = map (\<lambda>pc. LocalNode (fst pc) (snd pc)) covered"

fun local_node_member :: "(pp \<times> 'ctx) list \<Rightarrow> pp \<Rightarrow> 'ctx \<Rightarrow> bool" where
  "local_node_member [] p ctx = False"
| "local_node_member ((p', ctx') # covered) p ctx =
    (if p = p' \<and> ctx = ctx' then True else local_node_member covered p ctx)"

fun graph_node_member :: "('ctx, 'g) analysis_node list
  \<Rightarrow> ('ctx, 'g) analysis_node \<Rightarrow> bool" where
  "graph_node_member [] node = False"
| "graph_node_member (node' # rest) node =
    (if node = node' then True else graph_node_member rest node)"

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

definition analysis_intra_edges ::
  "cfg \<Rightarrow> (pp \<times> 'ctx) list
    \<Rightarrow> (('ctx, 'g) analysis_node \<times> analysis_edge_kind \<times>
       ('ctx, 'g) analysis_node) list" where
  "analysis_intra_edges g covered =
    concat (map (\<lambda>src_ctx.
      concat (map (\<lambda>e. case e of (u, a, v) \<Rightarrow>
        if fst src_ctx = u \<and> \<not> is_enter_action a \<and>
           local_node_member covered v (snd src_ctx)
        then [(LocalNode u (snd src_ctx), IntraEdge a, LocalNode v (snd src_ctx))]
        else []) (cfg_edges_list g))) covered)"

definition analysis_enter_edges ::
  "('ctx, 'g, 'a, 'd) analysis_graph_config \<Rightarrow> cfg \<Rightarrow> (pp \<times> 'ctx) list
    \<Rightarrow> (pp \<times> 'ctx + 'g \<Rightarrow> 'a)
    \<Rightarrow> (('ctx, 'g) analysis_node \<times> analysis_edge_kind \<times>
       ('ctx, 'g) analysis_node) list" where
  "analysis_enter_edges cfg g covered sol =
    concat (map (\<lambda>src_ctx.
      concat (map (\<lambda>e. case e of (u, a, v) \<Rightarrow>
        if fst src_ctx = u \<and> is_enter_action a then
          let callee_ctx = route cfg u (snd src_ctx) a
              (local_of cfg (sol (Inl src_ctx)))
          in if local_node_member covered v callee_ctx
             then [(LocalNode u (snd src_ctx), EnterEdge a, LocalNode v callee_ctx)]
             else []
        else []) (cfg_edges_list g))) covered)"

definition analysis_combine_edges ::
  "('ctx, 'g, 'a, 'd) analysis_graph_config \<Rightarrow> cfg \<Rightarrow> (pp \<times> 'ctx) list
    \<Rightarrow> (pp \<times> 'ctx + 'g \<Rightarrow> 'a)
    \<Rightarrow> (('ctx, 'g) analysis_node \<times> analysis_edge_kind \<times>
       ('ctx, 'g) analysis_node) list" where
  "analysis_combine_edges cfg g covered sol =
    concat (map (\<lambda>src_ctx.
      concat (map (\<lambda>c. case c of (call, ex, ret, dst) \<Rightarrow>
        if fst src_ctx = call then
          concat (map (\<lambda>e. case e of (u, a, v) \<Rightarrow>
            if u = call \<and> is_enter_action a then
              let callee_ctx = route cfg call (snd src_ctx) a
                  (local_of cfg (sol (Inl src_ctx)))
              in if local_node_member covered ex callee_ctx \<and>
                    local_node_member covered ret (snd src_ctx)
                 then [(LocalNode ex callee_ctx,
                       CombineEdge call dst (return_slot_for_pp cfg ex),
                       LocalNode ret (snd src_ctx))]
                 else []
            else []) (cfg_edges_list g))
        else []) (cfg_combines_list g))) covered)"

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
           @ analysis_combine_edges cfg g covered sol))"

text \<open>The graph domain is an executable presentation choice.  Solver coverage remains
  extensional and can be checked propositionally by clients.\<close>

definition build_analysis_graph ::
  "('ctx, 'g, 'a, 'd) analysis_graph_config \<Rightarrow> cfg
    \<Rightarrow> ((pp \<times> 'ctx) + 'g) list \<Rightarrow> (pp \<times> 'ctx + 'g \<Rightarrow> 'a)
    \<Rightarrow> ('ctx, 'g) analysis_graph" where
  "build_analysis_graph cfg g domain sol =
    build_analysis_graph_parts cfg g (analysis_local_domain (remdups domain))
      (analysis_global_domain (remdups domain)) sol"

definition analysis_graph_nodes ::
  "('ctx, 'g) analysis_graph \<Rightarrow> ('ctx, 'g) analysis_node list" where
  "analysis_graph_nodes graph = (case graph of (_, ns, _) \<Rightarrow> ns)"

definition analysis_graph_edges ::
  "('ctx, 'g) analysis_graph \<Rightarrow>
    (('ctx, 'g) analysis_node \<times> analysis_edge_kind \<times> ('ctx, 'g) analysis_node) list" where
  "analysis_graph_edges graph = (case graph of (_, _, es) \<Rightarrow> es)"

definition analysis_graph_wf ::
  "('ctx, 'g) analysis_graph \<Rightarrow> bool" where
  "analysis_graph_wf graph =
    (case graph of (clusters, ns, es) \<Rightarrow>
      distinct clusters \<and>
      distinct ns \<and>
      distinct es \<and>
      list_all (\<lambda>e. case e of (src, _, dst) \<Rightarrow> graph_node_member ns src \<and> graph_node_member ns dst) es)"

fun analysis_node_position :: "('ctx, 'g) analysis_node list
  \<Rightarrow> ('ctx, 'g) analysis_node \<Rightarrow> nat" where
  "analysis_node_position [] n = 0"
| "analysis_node_position (m # ms) n =
    (if n = m then 0 else Suc (analysis_node_position ms n))"

fun owner_contexts ::
  "('ctx, 'g, 'a, 'd) analysis_graph_config \<Rightarrow> ('ctx, 'g) analysis_node list
    \<Rightarrow> (string \<times> 'ctx) list" where
  "owner_contexts cfg [] = []"
| "owner_contexts cfg (LocalNode p ctx # ns) =
    (owner_of cfg p, ctx) # owner_contexts cfg ns"
| "owner_contexts cfg (GlobalNode k # ns) = owner_contexts cfg ns"
| "owner_contexts cfg (SourceNode src # ns) = owner_contexts cfg ns"

fun context_position :: "'a list \<Rightarrow> 'a \<Rightarrow> nat" where
  "context_position [] key = 0"
| "context_position (key' # keys) key =
    (if key = key' then 0 else Suc (context_position keys key))"

definition analysis_node_id ::
  "('ctx, 'g, 'a, 'd) analysis_graph_config \<Rightarrow> ('ctx, 'g) analysis_node list
    \<Rightarrow> ('ctx, 'g) analysis_node \<Rightarrow> string" where
  "analysis_node_id cfg ns n =
    (case n of
      LocalNode p ctx \<Rightarrow> owner_of cfg p @ ''_pp'' @ string_of_nat p @ ''_ctx''
        @ string_of_nat (context_position (remdups (owner_contexts cfg ns))
            (owner_of cfg p, ctx))
    | GlobalNode k \<Rightarrow> ''global_'' @ string_of_nat (analysis_node_position ns n)
    | SourceNode src \<Rightarrow> ''source'')" 

fun analysis_cluster_position :: "('ctx, 'g) analysis_cluster list
  \<Rightarrow> ('ctx, 'g) analysis_cluster \<Rightarrow> nat" where
  "analysis_cluster_position [] cluster = 0"
| "analysis_cluster_position (cluster0 # clusters) cluster =
    (if cluster0 = cluster then 0
     else Suc (analysis_cluster_position clusters cluster))"

definition analysis_cluster_id :: "('ctx, 'g) analysis_cluster list
  \<Rightarrow> ('ctx, 'g) analysis_cluster \<Rightarrow> string" where
  "analysis_cluster_id clusters cluster =
    (case cluster of
      GlobalCluster \<Rightarrow> ''cluster_globals''
    | SourceCluster \<Rightarrow> ''cluster_source''
    | ContextCluster owner ctx \<Rightarrow> ''cluster_ctx_''
        @ string_of_nat (analysis_cluster_position clusters cluster))"

definition analysis_nodes_in_cluster ::
  "('ctx, 'g, 'a, 'd) analysis_graph_config \<Rightarrow> ('ctx, 'g) analysis_cluster
    \<Rightarrow> ('ctx, 'g) analysis_node list \<Rightarrow> ('ctx, 'g) analysis_node list" where
  "analysis_nodes_in_cluster cfg cluster ns =
    sort_key (\<lambda>n. case n of LocalNode p ctx \<Rightarrow> p | GlobalNode k \<Rightarrow> 0 | SourceNode src \<Rightarrow> 0)
      (filter (\<lambda>n. case (cluster, n) of
        (ContextCluster owner ctx, LocalNode p ctx') \<Rightarrow> owner = owner_of cfg p \<and> ctx = ctx'
      | (GlobalCluster, GlobalNode _) \<Rightarrow> True
      | (SourceCluster, SourceNode _) \<Rightarrow> True
      | _ \<Rightarrow> False) ns)"

definition graphviz_point_label :: "cfg \<Rightarrow> pp \<Rightarrow> string" where
  "graphviz_point_label g p =
    (if p = cfg_entry g \<or> mem_pp p (proc_entry_pps_list g) then ''start''
     else if p = cfg_exit g \<or> mem_pp p (proc_exit_pps_list g) then ''end''
     else ''pp'' @ string_of_nat p)"

definition contextual_node_label ::
  "('ctx, 'g, 'a, 'd) analysis_graph_config \<Rightarrow> cfg
    \<Rightarrow> (pp \<times> 'ctx + 'g \<Rightarrow> 'a) \<Rightarrow> ('ctx, 'g) analysis_node \<Rightarrow> string" where
  "contextual_node_label cfg g sol n =
    (case n of
      LocalNode p ctx \<Rightarrow> join_gv_nl
        (graphviz_point_label g p #
          show_local cfg p ctx (locals_for_pp cfg p)
            (local_of cfg (sol (Inl (p, ctx))))
          @ (case return_slot_for_pp cfg p of None \<Rightarrow> []
             | Some ret \<Rightarrow> format_return cfg p ctx ret
                 (local_of cfg (sol (Inl (p, ctx))))))
    | GlobalNode k \<Rightarrow> join_gv_nl
        (show_global_key cfg k # show_global cfg k (globals_to_show cfg) (sol (Inr k)))
    | SourceNode src \<Rightarrow> src)"

definition analysis_node_attrs :: "cfg \<Rightarrow> ('ctx, 'g) analysis_node \<Rightarrow> string" where
  "analysis_node_attrs g n =
    (case n of
      LocalNode p _ \<Rightarrow>
        if p = cfg_entry g then ''shape=doublecircle,color=green,style=filled,fillcolor=lightyellow''
        else if p = cfg_exit g then ''shape=doublecircle,color=red,style=filled,fillcolor=mistyrose''
        else if mem_pp p (proc_entry_pps_list g) then ''shape=box,color=green,style=filled,fillcolor=lightgreen''
        else if mem_pp p (proc_exit_pps_list g) then ''shape=box,color=red,style=filled,fillcolor=lightgreen''
        else ''shape=box,style=filled,fillcolor=lightgreen''
    | GlobalNode _ \<Rightarrow> ''shape=note,width=2.2,fixedsize=false''
    | SourceNode _ \<Rightarrow> ''shape=box,color=gray,style=rounded'')" 

fun enter_bindings :: "vname list \<Rightarrow> aexp list \<Rightarrow> string list" where
  "enter_bindings [] _ = []"
| "enter_bindings _ [] = []"
| "enter_bindings (x # xs) (e # es) =
    (x @ '' := '' @ string_of_aexp e) # enter_bindings xs es"

definition enter_action_label :: "edge_action \<Rightarrow> string" where
  "enter_action_label a =
    (case a of EA_Enter xs es \<Rightarrow>
       (let bindings = enter_bindings xs es
        in if bindings = [] then ''enter''
           else ''enter'' @ gv_nl @ join_gv_nl bindings)
     | _ \<Rightarrow> string_of_action a)"

definition source_action_label :: "edge_action \<Rightarrow> string" where
  "source_action_label a =
    (case a of EA_Assign x e \<Rightarrow>
       if x = ret_var then ''ret := '' @ string_of_aexp e else string_of_action a
     | _ \<Rightarrow> string_of_action a)"

definition analysis_edge_attrs :: "analysis_edge_kind \<Rightarrow> string" where
  "analysis_edge_attrs kind =
    (case kind of
      IntraEdge a \<Rightarrow> ''label='' @ dq @ source_action_label a @ dq
    | EnterEdge a \<Rightarrow> ''color=purple,penwidth=2,label='' @ dq
        @ enter_action_label a @ dq
    | CombineEdge call dst ret \<Rightarrow> ''style=dashed,color=blue,label='' @ dq
        @ (case (dst, ret) of
             (Some x, Some r) \<Rightarrow> x @ '' := '' @ r
           | (Some x, None) \<Rightarrow> ''return to '' @ x
           | (None, _) \<Rightarrow> ''return / nop'')
        @ dq
    | GlobalReadEdge \<Rightarrow> ''style=dotted,color=gray,label='' @ dq @ ''read global'' @ dq
    | GlobalWriteEdge \<Rightarrow> ''style=dotted,color=gray,label='' @ dq @ ''write global'' @ dq)"

definition analysis_cluster_label ::
  "('ctx, 'g, 'a, 'd) analysis_graph_config \<Rightarrow> ('ctx, 'g) analysis_cluster \<Rightarrow> string" where
  "analysis_cluster_label cfg cluster =
    (case cluster of
      ContextCluster owner ctx \<Rightarrow> cluster_label cfg owner ctx
    | GlobalCluster \<Rightarrow> ''Shared globals''
    | SourceCluster \<Rightarrow> ''Source'')"

fun analysis_order_pairs :: "'a list \<Rightarrow> ('a \<times> 'a) list" where
  "analysis_order_pairs [] = []"
| "analysis_order_pairs [x] = []"
| "analysis_order_pairs (x # y # xs) = (x, y) # analysis_order_pairs (y # xs)"

fun analysis_real_edge :: 
  "(('ctx, 'g) analysis_node \<times> analysis_edge_kind \<times> ('ctx, 'g) analysis_node) list
    \<Rightarrow> ('ctx, 'g) analysis_node \<Rightarrow> ('ctx, 'g) analysis_node \<Rightarrow> bool" where
  "analysis_real_edge [] src dst = False"
| "analysis_real_edge ((src', kind, dst') # es) src dst =
    (if src = src' \<and> dst = dst' then True else analysis_real_edge es src dst)"

definition analysis_ordering_dot ::
  "('ctx, 'g, 'a, 'd) analysis_graph_config \<Rightarrow> ('ctx, 'g) analysis_node list
    \<Rightarrow> (('ctx, 'g) analysis_node \<times> analysis_edge_kind \<times> ('ctx, 'g) analysis_node) list
    \<Rightarrow> ('ctx, 'g) analysis_node list \<Rightarrow> string" where
  "analysis_ordering_dot cfg ns es ordered =
    concat (map (\<lambda>pair. case pair of (src, dst) \<Rightarrow>
      ''    '' @ analysis_node_id cfg ns src @ '' -> '' @ analysis_node_id cfg ns dst
      @ '' [style=invis,weight=10];'' @ nl)
      (filter (\<lambda>pair. case pair of (src, dst) \<Rightarrow> \<not> analysis_real_edge es src dst)
        (analysis_order_pairs ordered)))"

definition analysis_cluster_dot ::
  "('ctx, 'g, 'a, 'd) analysis_graph_config \<Rightarrow> cfg
    \<Rightarrow> ('ctx, 'g) analysis_cluster list \<Rightarrow> ('ctx, 'g) analysis_node list
    \<Rightarrow> (('ctx, 'g) analysis_node \<times> analysis_edge_kind \<times> ('ctx, 'g) analysis_node) list
    \<Rightarrow> (pp \<times> 'ctx + 'g \<Rightarrow> 'a) \<Rightarrow> ('ctx, 'g) analysis_cluster \<Rightarrow> string" where
  "analysis_cluster_dot cfg g clusters ns es sol cluster =
    (let members = analysis_nodes_in_cluster cfg cluster ns
     in ''  subgraph '' @ analysis_cluster_id clusters cluster @ '' {'' @ nl
      @ ''    label='' @ dq @ analysis_cluster_label cfg cluster @ dq @ '';'' @ nl
      @ ''    style=filled; color=lightgrey; fillcolor=white;'' @ nl
      @ concat (map (\<lambda>n. ''    '' @ analysis_node_id cfg ns n @ '' [''
          @ analysis_node_attrs g n @ '',label='' @ dq
          @ graphviz_label_text (contextual_node_label cfg g sol n)
          @ dq @ ''];'' @ nl) members)
      @ analysis_ordering_dot cfg ns es members
      @ ''  }'' @ nl)"

definition analysis_edge_dot ::
  "('ctx, 'g, 'a, 'd) analysis_graph_config \<Rightarrow> ('ctx, 'g) analysis_node list
    \<Rightarrow> (('ctx, 'g) analysis_node \<times> analysis_edge_kind \<times> ('ctx, 'g) analysis_node)
    \<Rightarrow> string" where
  "analysis_edge_dot cfg ns e =
    (case e of (src, kind, dst) \<Rightarrow> ''  '' @ analysis_node_id cfg ns src @ '' -> ''
      @ analysis_node_id cfg ns dst @ '' ['' @ analysis_edge_attrs kind @ ''];'' @ nl)"

definition analysis_graph_to_dot ::
  "('ctx, 'g, 'a, 'd) analysis_graph_config \<Rightarrow> cfg
    \<Rightarrow> (pp \<times> 'ctx + 'g \<Rightarrow> 'a) \<Rightarrow> ('ctx, 'g) analysis_graph \<Rightarrow> string" where
  "analysis_graph_to_dot cfg g sol graph =
    (case graph of (clusters, ns, es) \<Rightarrow>
      if analysis_graph_wf graph then
        ''digraph AnalysisCFG {'' @ nl
        @ ''  rankdir=TB;'' @ nl
        @ ''  node [fontname='' @ dq @ ''Menlo'' @ dq @ ''];'' @ nl
        @ concat (map (analysis_cluster_dot cfg g clusters ns es sol) clusters)
        @ concat (map (analysis_edge_dot cfg ns) es)
        @ ''}'' @ nl
      else ''digraph AnalysisCFG { invalid_graph }'' @ nl)"

definition contextual_analysis_dot ::
  "('ctx, 'g, 'a, 'd) analysis_graph_config \<Rightarrow> cfg
    \<Rightarrow> ((pp \<times> 'ctx) + 'g) list \<Rightarrow> (pp \<times> 'ctx + 'g \<Rightarrow> 'a) \<Rightarrow> string" where
  "contextual_analysis_dot cfg g domain sol =
    analysis_graph_to_dot cfg g sol (build_analysis_graph cfg g domain sol)"

definition raw_cfg_graph_config ::
  "proc_table \<Rightarrow> pname list \<Rightarrow> com \<Rightarrow> (unit, unit, unit, unit) analysis_graph_config" where
  "raw_cfg_graph_config \<Pi> ps main =
    \<lparr> local_of = id,
      route = (\<lambda>_ _ _ _. ()),
      show_context = (\<lambda>_. ''''),
      locals_for_pp = (\<lambda>_. []),
      return_slot_for_pp = (\<lambda>_. None),
      globals_to_show = [],
      show_local = (\<lambda>_ _ _ _. []),
      format_return = (\<lambda>_ _ _ _. []),
      show_global = (\<lambda>_ _ _. []),
      show_global_key = (\<lambda>_. ''''),
      is_shared_global = (\<lambda>_. False),
      show_internal_globals = False,
      owner_of = compiled_owner_of \<Pi> ps main,
      cluster_label = (\<lambda>owner _. owner),
      source_text = Some (string_of_program \<Pi> ps main)
    \<rparr>"

definition raw_cfg_dot ::
  "proc_table \<Rightarrow> pname list \<Rightarrow> com \<Rightarrow> string" where
  "raw_cfg_dot \<Pi> ps main =
    (let g = compile_prog \<Pi> ps main;
         cfg = raw_cfg_graph_config \<Pi> ps main;
         domain = contextual_graph_domain g (\<lambda>_. [()])
     in contextual_analysis_dot cfg g domain (\<lambda>_. ()))"

definition raw_cfg_dot_lit ::
  "proc_table \<Rightarrow> pname list \<Rightarrow> com \<Rightarrow> String.literal" where
  "raw_cfg_dot_lit \<Pi> ps main = String.implode (raw_cfg_dot \<Pi> ps main)"

end

