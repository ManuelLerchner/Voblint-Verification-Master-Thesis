theory Analysis_Graph_Naming
  imports Analysis_Graph_Build
begin

section \<open>Giving nodes and clusters their names\<close>

text \<open>
  A built graph is a list of clusters and a list of nodes; neither carries an
  identifier. This theory supplies them, and it supplies them positionally: a
  node is named by its index in the node list, a cluster by its index in the
  cluster list, and a context-expanded node takes a \<open>_ctxN\<close> suffix from its
  context's index among those its owner covers. That is what the chosen
  context ordering is for --- nothing here looks inside a context, so the
  scheme works for any context type.

  One concrete context type is presented here too, because presenting it needs
  no domain: a call-string context is a list of CFG nodes, so its key and its
  display text are the same for every domain that routes through
  \<^const>\<open>cs_route\<close>.
\<close>

subsection \<open>Call-string context presentation\<close>

text \<open>
  A call-string context is a \<^typ>\<open>cfg_node list\<close> (\<^theory>\<open>Voblint_Framework.Call_String_Context\<close>),
  so unlike an entry-state context --- whose type is the analysed domain's own value list
  (\<open>ivl list\<close>, \<open>sign list\<close>, ...) --- it carries no domain content at all. Every part of
  presenting one is therefore shared by every domain that routes through
  \<^const>\<open>cs_route\<close>: the key, the display text, and the routing hook below are stated once
  here and instantiated unchanged by Sign, Interval, and Int alike.

  \<open>cs_graph_route\<close> ignores the caller's rendered state exactly as \<^const>\<open>cs_route\<close> ignores
  the entered abstract value, and answers \<^const>\<open>Some\<close> unconditionally: a call-string
  context is defined by the call history alone, so there is no state the callee frame could
  fail to have. That makes it the \<^emph>\<open>total\<close> case of \<open>route\<close>'s \<^typ>\<open>'ctx option\<close> contract, in
  contrast to entry-state routing, which genuinely has no context to offer when the entered
  frame is empty.
\<close>

definition cs_show_context :: "cfg_node list \<Rightarrow> String.literal" where
  "cs_show_context ctx = foldr (\<lambda>u acc. string_of_cfg_node u + STR '' '' + acc) ctx STR ''''"

definition cs_context_key :: "cfg_node list \<Rightarrow> String.literal" where
  "cs_context_key ctx = cs_show_context ctx"

definition cs_graph_route ::
  "nat \<Rightarrow> pp \<Rightarrow> cfg_node list \<Rightarrow> call_action \<Rightarrow> 'd \<Rightarrow> cfg_node list option" where
  "cs_graph_route k u ctx ca d = Some (cs_route k u ctx d ca)"

definition cs_cluster_label :: "String.literal \<Rightarrow> cfg_node list \<Rightarrow> String.literal" where
  "cs_cluster_label owner ctx =
     (if ctx = [] then owner + STR '' / root context''
      else owner + STR '' / call-string='' + cs_show_context ctx)"

subsection \<open>Naming nodes and clusters\<close>

text \<open>
  Identifiers are positional: a node's name is its index in the node list, a
  cluster's its index in the cluster list, and a context-expanded node's
  \<open>_ctxN\<close> suffix its context's index among those its owner covers. That is
  what the chosen ordering above is for --- nothing here inspects a context's
  content, so these work for any context type.
\<close>

definition entry_proc_exit :: "cfg \<Rightarrow> cfg_node" where
  "entry_proc_exit g =
    (case cfg_entry g of FunctionEntry p \<Rightarrow> FunctionResult p | p \<Rightarrow> p)"

fun analysis_node_position :: "('ctx, 'g) analysis_node list
  \<Rightarrow> ('ctx, 'g) analysis_node \<Rightarrow> nat" where
  "analysis_node_position [] n = 0"
| "analysis_node_position (m # ms) n =
    (if n = m then 0 else Suc (analysis_node_position ms n))"

fun owner_contexts ::
  "('ctx, 'g, 'a, 'd) analysis_graph_config \<Rightarrow> ('ctx, 'g) analysis_node list
    \<Rightarrow> (String.literal \<times> 'ctx) list" where
  "owner_contexts cfg [] = []"
| "owner_contexts cfg (LocalNode p ctx # ns) =
    (owner_of cfg p, ctx) # owner_contexts cfg ns"
| "owner_contexts cfg (GlobalNode k # ns) = owner_contexts cfg ns"
| "owner_contexts cfg (SourceNode src # ns) = owner_contexts cfg ns"

fun context_position :: "'a list \<Rightarrow> 'a \<Rightarrow> nat" where
  "context_position [] key = 0"
| "context_position (key' # keys) key =
    (if key = key' then 0 else Suc (context_position keys key))"

text \<open>
  The \<open>_ctxN\<close> index counts only the contexts the node's own owner covers, so
  a node's identifier does not move when some other procedure gains or loses a
  context. Two solves of one program over different domains therefore agree on
  every identifier the context-free drawing produces, where each owner has the
  single unit context.
\<close>

definition analysis_node_id ::
  "('ctx, 'g, 'a, 'd) analysis_graph_config \<Rightarrow> ('ctx, 'g) analysis_node list
    \<Rightarrow> ('ctx, 'g) analysis_node \<Rightarrow> String.literal" where
  "analysis_node_id cfg ns n =
    (case n of
      LocalNode p ctx \<Rightarrow>
        owner_of cfg p + STR ''_'' + string_of_cfg_node p + STR ''_ctx''
          + string_of_nat
              (context_position
                (remdups (map snd (filter (\<lambda>oc. fst oc = owner_of cfg p)
                  (owner_contexts cfg ns))))
                ctx)
    | GlobalNode k \<Rightarrow>
        STR ''global_'' + string_of_nat (analysis_node_position ns n)
    | SourceNode src \<Rightarrow> STR ''source'')"

fun analysis_cluster_position :: "('ctx, 'g) analysis_cluster list
  \<Rightarrow> ('ctx, 'g) analysis_cluster \<Rightarrow> nat" where
  "analysis_cluster_position [] cluster = 0"
| "analysis_cluster_position (cluster0 # clusters) cluster =
    (if cluster0 = cluster then 0
     else Suc (analysis_cluster_position clusters cluster))"

definition analysis_cluster_id :: "('ctx, 'g) analysis_cluster list
  \<Rightarrow> ('ctx, 'g) analysis_cluster \<Rightarrow> String.literal" where
  "analysis_cluster_id clusters cluster =
    (case cluster of
      GlobalCluster \<Rightarrow> STR ''cluster_globals''
    | SourceCluster \<Rightarrow> STR ''cluster_source''
    | ContextCluster owner ctx \<Rightarrow>
        STR ''cluster_ctx_''
          + string_of_nat (analysis_cluster_position clusters cluster))"

definition analysis_nodes_in_cluster ::
  "('ctx, 'g, 'a, 'd) analysis_graph_config \<Rightarrow> ('ctx, 'g) analysis_cluster
    \<Rightarrow> ('ctx, 'g) analysis_node list \<Rightarrow> ('ctx, 'g) analysis_node list" where
  "analysis_nodes_in_cluster cfg cluster ns =
    sort_key (analysis_node_position ns)
      (filter (\<lambda>n. case (cluster, n) of
        (ContextCluster owner ctx, LocalNode p ctx') \<Rightarrow> owner = owner_of cfg p \<and> ctx = ctx'
      | (GlobalCluster, GlobalNode _) \<Rightarrow> True
      | (SourceCluster, SourceNode _) \<Rightarrow> True
      | _ \<Rightarrow> False) ns)"

definition point_label :: "cfg \<Rightarrow> pp \<Rightarrow> String.literal" where
  "point_label g p =
    (case p of
      FunctionEntry owner \<Rightarrow> STR ''entry_'' + owner
    | FunctionResult owner \<Rightarrow> STR ''exit_'' + owner
    | Statement _ \<Rightarrow> string_of_cfg_node p)"

text \<open>
  The per-node label as a line list, before \<^const>\<open>join_esc_nl\<close> escapes it
  into one DOT-attribute string. Factored out so a non-DOT renderer (the
  canonical regression snapshot, below) can walk the same lines without
  re-deriving them from escaped DOT text.
\<close>

definition contextual_node_label_lines ::
  "('ctx, 'g, 'a, 'd) analysis_graph_config \<Rightarrow> cfg
    \<Rightarrow> (pp \<times> 'ctx + 'g \<Rightarrow> 'a) \<Rightarrow> ('ctx, 'g) analysis_node \<Rightarrow> String.literal list" where
  "contextual_node_label_lines cfg g sol n =
    (case n of
      LocalNode p ctx \<Rightarrow>
        point_label g p #
          show_local cfg p ctx (locals_for_pp cfg p)
            (local_of cfg (sol (Inl (p, ctx))))
          @ (case return_slot_for_pp cfg p of
              None \<Rightarrow> []
            | Some ret \<Rightarrow>
                format_return cfg p ctx ret
                  (local_of cfg (sol (Inl (p, ctx)))))
          @ (case node_annotation cfg p ctx of
               None \<Rightarrow> []
             | Some ann \<Rightarrow> annotation_lines ann)
    | GlobalNode k \<Rightarrow>
        show_global_key cfg k #
          show_global cfg k (globals_to_show cfg) (sol (Inr k))
    | SourceNode src \<Rightarrow> [src])"

definition source_action_label :: "cfg \<Rightarrow> edge_action \<Rightarrow> String.literal" where
  "source_action_label g a =
    (case a of
      EA_Assign x e \<Rightarrow>
        if x = ret_var
        then STR ''ret := '' + string_of_exp 0 e
        else string_of_action a
    | EA_Assume b \<Rightarrow> string_of_exp 0 b
    | EA_AssumeNot b \<Rightarrow> STR ''not ('' + string_of_exp 0 b + STR '')''
    | EA_Ret _ p \<Rightarrow>
        if cfg_entry g = FunctionEntry p
        then STR ''terminate''
        else string_of_action a
    | _ \<Rightarrow> string_of_action a)"

text \<open>
  An edge's role in words --- call arguments, combine-slot naming --- carrying
  no presentation syntax, for the canonical regression snapshot below.
\<close>

definition canonical_edge_kind_text ::
  "cfg \<Rightarrow> analysis_edge_kind \<Rightarrow> String.literal" where
  "canonical_edge_kind_text g kind =
    (case kind of
      IntraEdge a \<Rightarrow> source_action_label g a
    | EnterEdge callee a \<Rightarrow>
        STR ''enter '' + callee + STR ''(''
          + (case a of
               CallEdge _ _ es \<Rightarrow>
                 join_source (STR '', '') (map (string_of_exp 0) es))
          + STR '')''
    | CombineEdge call dst ret \<Rightarrow>
        STR ''combine''
          + (case (dst, ret) of
               (Some x, Some r) \<Rightarrow> STR '' '' + x + STR '' := '' + r
             | (Some x, None) \<Rightarrow> STR '' '' + x
             | (None, _) \<Rightarrow> STR '''')
    | CallToReturnEdge callee \<Rightarrow> STR ''call-to-return '' + callee
    | GlobalReadEdge \<Rightarrow> STR ''read global''
    | GlobalWriteEdge \<Rightarrow> STR ''write global'')"

definition analysis_cluster_label ::
  "('ctx, 'g, 'a, 'd) analysis_graph_config
    \<Rightarrow> ('ctx, 'g) analysis_cluster \<Rightarrow> String.literal" where
  "analysis_cluster_label cfg cluster =
    (case cluster of
      ContextCluster owner ctx \<Rightarrow> cluster_label cfg owner ctx
    | GlobalCluster \<Rightarrow> STR ''Shared globals''
    | SourceCluster \<Rightarrow> STR ''Source'')"

end