theory Analysis_GraphViz
  imports
    "Voblint_CFG.VIMP_Proc_to_CFG"
    "Voblint_VIMP.VIMP_Source_Print"
    Voblint_Core.TD_Side_CFG
    Voblint_Core.Exec_St
    Voblint_Core.Abstract_Domain
begin

text \<open>
  This theory provides the canonical graph model, raw-CFG builder, CFG action
  printers, DOT escaping helpers, and context-expanded analysis builder.
\<close>

definition prog_cfg_edges ::
    "proc_table \<Rightarrow> pname list \<Rightarrow> pname \<Rightarrow> com \<Rightarrow> (pp \<times> edge_action \<times> pp) list" where
  "prog_cfg_edges \<Pi> ps mnm main = cfg_intra_list (compile_prog \<Pi> ps mnm main)"

definition prog_cfg_calls ::
    "proc_table \<Rightarrow> pname list \<Rightarrow> pname \<Rightarrow> com
     \<Rightarrow> (pp \<times> call_action \<times> pp \<times> pp) list" where
  "prog_cfg_calls \<Pi> ps mnm main = cfg_calls_list (compile_prog \<Pi> ps mnm main)"

subsection \<open>CFG and DOT helpers\<close>

fun string_of_action :: "edge_action \<Rightarrow> string" where
  "string_of_action EA_Nop = ''nop''"
| "string_of_action (EA_Assign x a) = x @ '' := '' @ string_of_aexp a"
| "string_of_action (EA_Random x) = x @ '' := random()''"
| "string_of_action (EA_Assume b) = ''['' @ string_of_bexp b @ '']''"
| "string_of_action (EA_AssumeNot b) = ''!['' @ string_of_bexp b @ '']''"
| "string_of_action (EA_Ret None p) = ''return''"
| "string_of_action (EA_Ret (Some e) p) =
    ''return '' @ string_of_aexp e"

fun string_of_call_action :: "call_action \<Rightarrow> string" where
  "string_of_call_action (CallEdge None fs es) =
    ''call('' @ concat (map string_of_aexp es) @ '')''"
| "string_of_call_action (CallEdge (Some x) fs es) =
    x @ '' := call('' @ concat (map string_of_aexp es) @ '')''"

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

fun graphviz_html_text :: "string \<Rightarrow> string" where
  "graphviz_html_text [] = []"
| "graphviz_html_text (ch # rest) =
    (if ch = CHR 0x0A then ''<BR ALIGN='' @ dq @ ''LEFT'' @ dq @ ''/>''
     else if ch = CHR 0x20 then ''&#160;''
     else if ch = CHR 0x26 then ''&amp;''
     else if ch = CHR 0x3C then ''&lt;''
     else if ch = CHR 0x3E then ''&gt;''
     else [ch]) @ graphviz_html_text rest"

definition source_html_label :: "string \<Rightarrow> string" where
  "source_html_label src =
    ''<<TABLE BORDER='' @ dq @ ''1'' @ dq @ '' CELLBORDER='' @ dq @ ''0'' @ dq    @ '' CELLPADDING='' @ dq @ ''8'' @ dq
    @ ''><TR><TD ALIGN='' @ dq @ ''LEFT'' @ dq @ '' WIDTH='' @ dq @ ''260'' @ dq
    @ '' FIXEDSIZE='' @ dq @ ''FALSE'' @ dq
    @ ''><FONT FACE='' @ dq @ ''Menlo'' @ dq @ '' POINT-SIZE='' @ dq @ ''10'' @ dq
    @ ''>'' @ graphviz_html_text src @ ''</FONT></TD></TR></TABLE>>''"

definition proc_entry_pps_list :: "cfg \<Rightarrow> pp list" where
  "proc_entry_pps_list g =
    map (\<lambda>(_, _, entry, _). entry) (cfg_calls_list g)"

definition proc_exit_pps_list :: "cfg \<Rightarrow> pp list" where
  "proc_exit_pps_list g =
    map (\<lambda>(_, _, entry, _).
      case entry of FunctionEntry p \<Rightarrow> FunctionResult p | _ \<Rightarrow> entry)
      (cfg_calls_list g)"
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
    ContextCluster (cluster_name: string) (cluster_ctx: 'ctx)
  | GlobalCluster
  | SourceCluster

datatype ('ctx, 'g) analysis_node =
    LocalNode (node_pp: pp) (node_ctx: 'ctx)
  | GlobalNode (node_glob: 'g)
  | SourceNode (node_name: string)

datatype analysis_edge_kind =
    IntraEdge (aek_action: edge_action)
  | EnterEdge (aek_enter_proc: pname) (aek_call: call_action)
  | CombineEdge (combine_call_pp: pp) (combine_dst: "vname option") (combine_ret: "vname option")
  | CallToReturnEdge (aek_ctr_proc: pname)
  | GlobalReadEdge
  | GlobalWriteEdge

type_synonym ('ctx, 'g) analysis_graph =
  "(('ctx, 'g) analysis_cluster list \<times>
    ('ctx, 'g) analysis_node list \<times>
    (('ctx, 'g) analysis_node \<times> analysis_edge_kind \<times>
      ('ctx, 'g) analysis_node) list)"

text \<open>
  A node annotation is presentation metadata a caller attaches to one \<^typ>\<open>pp\<close>: an optional
  extra label line and a DOT style-attribute string that, when present, replaces this renderer's
  own node styling for that point. The renderer stays agnostic to what the annotation
  \<^emph>\<open>means\<close> --- proof status, a debugger breakpoint, anything a caller wants to overlay on the
  CFG --- it only owns turning \<^const>\<open>Some\<close> into DOT attributes and \<^const>\<open>None\<close> into the
  existing entry/exit/default styling.
\<close>

datatype graphviz_node_annotation =
  Node_Annotation (annotation_label: string) (annotation_style: string)

definition no_annotations :: "pp \<Rightarrow> graphviz_node_annotation option" where
  "no_annotations _ = None"

record ('ctx, 'g, 'a, 'd) analysis_graph_config =
  local_of :: "'a \<Rightarrow> 'd"
  route :: "pp \<Rightarrow> 'ctx \<Rightarrow> call_action \<Rightarrow> 'd \<Rightarrow> 'ctx"
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
  node_annotation :: "pp \<Rightarrow> graphviz_node_annotation option"

fun graphviz_owner_of :: "(string option \<times> pp list) list \<Rightarrow> pp \<Rightarrow> string" where
  "graphviz_owner_of [] p = ''unknown''"
| "graphviz_owner_of ((owner, ps) # regions) p =
    (if p \<in> set ps then region_label owner else graphviz_owner_of regions p)"

fun compiled_proc_owner ::
  "proc_table \<Rightarrow> pname list \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> pname option" where
  "compiled_proc_owner \<Pi> [] n k = None"
| "compiled_proc_owner \<Pi> (p # ps) n k =
    (case \<Pi> p of
      None \<Rightarrow> compiled_proc_owner \<Pi> ps n k
    | Some decl \<Rightarrow>
        (let (n', E, K) = compile_proc \<Pi> p decl n
         in if n \<le> k \<and> k < n' then Some p
            else compiled_proc_owner \<Pi> ps n' k))"

definition compiled_owner_of ::
  "proc_table \<Rightarrow> pname list \<Rightarrow> pname \<Rightarrow> com \<Rightarrow> pp \<Rightarrow> string" where
  "compiled_owner_of \<Pi> ps mnm main p =
    (case p of
      FunctionEntry owner \<Rightarrow> owner
    | FunctionResult owner \<Rightarrow> owner
    | Statement k \<Rightarrow>
        (case compiled_proc_owner \<Pi> ps 0 k of Some owner \<Rightarrow> owner | None \<Rightarrow> mnm))"

definition cfg_point_list :: "cfg \<Rightarrow> pp list" where
  "cfg_point_list g =
    remdups
      (cfg_entry g #
       concat (map (\<lambda>(u, _, v). [u, v]) (cfg_intra_list g)) @
       concat (map (\<lambda>(call, _, entry, cont).
         call # entry # cont #
         (case entry of FunctionEntry p \<Rightarrow> [FunctionResult p] | _ \<Rightarrow> []))
         (cfg_calls_list g)))"

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
| "graphviz_action_defs (EA_Random x) = [x]"
| "graphviz_action_defs _ = []"

definition cfg_assigned_vars :: "cfg \<Rightarrow> vname list" where
  "cfg_assigned_vars g =
    remdups
      (concat (map (\<lambda>(_, a, _). graphviz_action_defs a) (cfg_intra_list g)) @
       concat (map (\<lambda>(_, ca, _, _).
         case ca of CallEdge None _ _ \<Rightarrow> [] | CallEdge (Some x) _ _ \<Rightarrow> [x])
         (cfg_calls_list g)))"

definition compiled_global_vars :: "cfg \<Rightarrow> vname list" where
  "compiled_global_vars g = filter is_global (cfg_assigned_vars g)"

definition owner_assigned_vars ::
  "cfg \<Rightarrow> (pp \<Rightarrow> string) \<Rightarrow> string \<Rightarrow> vname list" where
  "owner_assigned_vars g point_owner owner =
    remdups
      (concat (map (\<lambda>(u, a, _).
         if point_owner u = owner then graphviz_action_defs a else [])
         (cfg_intra_list g)) @
       concat (map (\<lambda>(call, ca, _, _).
         if point_owner call = owner then
           (case ca of CallEdge None _ _ \<Rightarrow> []
             | CallEdge (Some x) _ _ \<Rightarrow> [x])
         else []) (cfg_calls_list g)))"

definition compiled_procedure_scope ::
  "proc_table \<Rightarrow> pname list \<Rightarrow> pname \<Rightarrow> com \<Rightarrow> cfg \<Rightarrow> pp \<Rightarrow> procedure_scope" where
  "compiled_procedure_scope \<Pi> ps mnm main g p =
    (let owner = compiled_owner_of \<Pi> ps mnm main p;
         decl = \<Pi> owner;
         fs = if owner = mnm then [] else
           (case decl of None \<Rightarrow> [] | Some d \<Rightarrow> formals d);
         ret = if owner = mnm then None else Some ret_var;
         ls = filter (\<lambda>x. x \<notin> set fs \<and> x \<noteq> ret_var \<and> \<not> is_global x)
           (owner_assigned_vars g (compiled_owner_of \<Pi> ps mnm main) owner)
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

definition analysis_intra_edges ::
  "cfg \<Rightarrow> (pp \<times> 'ctx) list
    \<Rightarrow> (('ctx, 'g) analysis_node \<times> analysis_edge_kind \<times>
       ('ctx, 'g) analysis_node) list" where
  "analysis_intra_edges g covered =
    concat (map (\<lambda>src_ctx.
      concat (map (\<lambda>(u, a, v).
        if fst src_ctx = u \<and> (v, snd src_ctx) \<in> set covered
        then [(LocalNode u (snd src_ctx), IntraEdge a, LocalNode v (snd src_ctx))]
        else []) (cfg_intra_list g))) covered)"

definition analysis_enter_edges ::
  "('ctx, 'g, 'a, 'd) analysis_graph_config \<Rightarrow> cfg \<Rightarrow> (pp \<times> 'ctx) list
    \<Rightarrow> (pp \<times> 'ctx + 'g \<Rightarrow> 'a)
    \<Rightarrow> (('ctx, 'g) analysis_node \<times> analysis_edge_kind \<times>
       ('ctx, 'g) analysis_node) list" where
  "analysis_enter_edges cfg g covered sol =
    concat (map (\<lambda>src_ctx.
      concat (map (\<lambda>(u, ca, entry, _).
        if fst src_ctx = u then
          let callee_ctx = route cfg u (snd src_ctx) ca
              (local_of cfg (sol (Inl src_ctx)))
          in if (entry, callee_ctx) \<in> set covered
             then [(LocalNode u (snd src_ctx), EnterEdge (owner_of cfg entry) ca,
                    LocalNode entry callee_ctx)]
             else []
        else []) (cfg_calls_list g))) covered)"

definition analysis_combine_edges ::
  "('ctx, 'g, 'a, 'd) analysis_graph_config \<Rightarrow> cfg \<Rightarrow> (pp \<times> 'ctx) list
    \<Rightarrow> (pp \<times> 'ctx + 'g \<Rightarrow> 'a)
    \<Rightarrow> (('ctx, 'g) analysis_node \<times> analysis_edge_kind \<times>
       ('ctx, 'g) analysis_node) list" where
  "analysis_combine_edges cfg g covered sol =
    concat (map (\<lambda>src_ctx.
      concat (map (\<lambda>c. case c of (call, ca, entry, cont) \<Rightarrow>
        (case entry of FunctionEntry p \<Rightarrow>
          if fst src_ctx = call then
            let callee_ctx = route cfg call (snd src_ctx) ca
                (local_of cfg (sol (Inl src_ctx)));
                result = FunctionResult p
            in if (result, callee_ctx) \<in> set covered \<and>
                  (cont, snd src_ctx) \<in> set covered
               then [(LocalNode result callee_ctx,
                      CombineEdge call (case ca of CallEdge dst _ _ \<Rightarrow> dst)
                        (return_slot_for_pp cfg result),
                      LocalNode cont (snd src_ctx))]
               else []
          else []
        | _ \<Rightarrow> [])) (cfg_calls_list g))) covered)"

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
    concat (map (\<lambda>src_ctx.
      concat (map (\<lambda>c. case c of (call, _, entry, cont) \<Rightarrow>
        (case entry of FunctionEntry p \<Rightarrow>
          if fst src_ctx = call \<and> (cont, snd src_ctx) \<in> set covered
          then [(LocalNode call (snd src_ctx), CallToReturnEdge p,
                 LocalNode cont (snd src_ctx))]
          else []
        | _ \<Rightarrow> [])) (cfg_calls_list g))) covered)"

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
      list_all (\<lambda>e. case e of (src, _, dst) \<Rightarrow> src \<in> set ns \<and> dst \<in> set ns) es)"
fun string_of_cfg_node :: "cfg_node \<Rightarrow> string" where
  "string_of_cfg_node (Statement n) = ''pp'' @ string_of_nat n"
| "string_of_cfg_node (FunctionEntry p) = ''entry_'' @ p"
| "string_of_cfg_node (FunctionResult p) = ''result_'' @ p"

definition graphviz_exit :: "cfg \<Rightarrow> cfg_node" where
  "graphviz_exit g =
    (case cfg_entry g of FunctionEntry p \<Rightarrow> FunctionResult p | p \<Rightarrow> p)"
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
      LocalNode p ctx \<Rightarrow> owner_of cfg p @ ''_'' @ string_of_cfg_node p @ ''_ctx''
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
    sort_key (analysis_node_position ns)
      (filter (\<lambda>n. case (cluster, n) of
        (ContextCluster owner ctx, LocalNode p ctx') \<Rightarrow> owner = owner_of cfg p \<and> ctx = ctx'
      | (GlobalCluster, GlobalNode _) \<Rightarrow> True
      | (SourceCluster, SourceNode _) \<Rightarrow> True
      | _ \<Rightarrow> False) ns)"



definition graphviz_point_label :: "cfg \<Rightarrow> pp \<Rightarrow> string" where
  "graphviz_point_label g p =
    (case p of
      FunctionEntry owner \<Rightarrow> ''entry_'' @ owner
    | FunctionResult owner \<Rightarrow> ''exit_'' @ owner
    | Statement _ \<Rightarrow> string_of_cfg_node p)"

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
                 (local_of cfg (sol (Inl (p, ctx)))))
          @ (case node_annotation cfg p of
              None \<Rightarrow> []
            | Some ann \<Rightarrow>
                if annotation_label ann = '''' then [] else [annotation_label ann]))
    | GlobalNode k \<Rightarrow> join_gv_nl
        (show_global_key cfg k # show_global cfg k (globals_to_show cfg) (sol (Inr k)))
    | SourceNode src \<Rightarrow> src)"

definition analysis_node_attrs ::
  "('ctx, 'g, 'a, 'd) analysis_graph_config \<Rightarrow> cfg \<Rightarrow> ('ctx, 'g) analysis_node \<Rightarrow> string" where
  "analysis_node_attrs cfg g n =
    (case n of
      LocalNode p _ \<Rightarrow>
        (case node_annotation cfg p of
          Some ann \<Rightarrow> annotation_style ann
        | None \<Rightarrow>
            if p = cfg_entry g then ''shape=doublecircle,color=green,style=filled,fillcolor=lightyellow''
            else if p = graphviz_exit g then ''shape=doublecircle,color=red,style=filled,fillcolor=mistyrose''
            else if p \<in> set (proc_entry_pps_list g) then ''shape=doublecircle,color=green,style=filled,fillcolor=lightyellow''
            else if p \<in> set (proc_exit_pps_list g) then ''shape=doublecircle,color=red,style=filled,fillcolor=mistyrose''
            else ''shape=box,style=filled,fillcolor=lightgreen'')
    | GlobalNode _ \<Rightarrow> ''shape=note,width=2.2,fixedsize=false''
    | SourceNode _ \<Rightarrow> ''shape=plain'')" 

fun enter_bindings :: "vname list \<Rightarrow> aexp list \<Rightarrow> string list" where
  "enter_bindings [] _ = []"
| "enter_bindings _ [] = []"
| "enter_bindings (x # xs) (e # es) =
    (x @ '' := '' @ string_of_aexp e) # enter_bindings xs es"

definition enter_action_label :: "call_action \<Rightarrow> string" where
  "enter_action_label a = string_of_call_action a"

definition source_action_label :: "cfg \<Rightarrow> edge_action \<Rightarrow> string" where
  "source_action_label g a =
    (case a of EA_Assign x e \<Rightarrow>
       if x = ret_var then ''ret := '' @ string_of_aexp e else string_of_action a    | EA_Assume b \<Rightarrow> string_of_bexp b
    | EA_AssumeNot b \<Rightarrow> ''not ('' @ string_of_bexp b @ '')''
    | EA_Ret _ p \<Rightarrow> if cfg_entry g = FunctionEntry p then ''terminate'' else string_of_action a
    | _ \<Rightarrow> string_of_action a)"

definition analysis_edge_attrs :: "cfg \<Rightarrow> analysis_edge_kind \<Rightarrow> string" where
  "analysis_edge_attrs g kind =
    (case kind of
      IntraEdge a \<Rightarrow> ''label='' @ dq @ source_action_label g a @ dq
    | EnterEdge callee a \<Rightarrow> ''color=purple,penwidth=2,weight=10,label='' @ dq
        @ ''call '' @ callee @ ''('' @
          (case a of CallEdge _ _ es \<Rightarrow> join_source '', '' (map string_of_aexp es)) @ '')'' @ dq
    | CombineEdge call dst ret \<Rightarrow> ''style=dashed,color=blue,constraint=false,xlabel='' @ dq
        @ (case (dst, ret) of
             (Some x, Some r) \<Rightarrow> ''resume / '' @ x @ '' := '' @ r
           | (Some x, None) \<Rightarrow> ''resume / '' @ x
           | (None, _) \<Rightarrow> ''resume'')
        @ dq
    | CallToReturnEdge callee \<Rightarrow> ''style=dotted,color=gray40,constraint=false,label='' @ dq
        @ ''resume-site'' @ dq
    | GlobalReadEdge \<Rightarrow> ''style=dotted,color=gray,label='' @ dq @ ''read global'' @ dq
    | GlobalWriteEdge \<Rightarrow> ''style=dotted,color=gray,label='' @ dq @ ''write global'' @ dq)"

definition analysis_cluster_label ::
  "('ctx, 'g, 'a, 'd) analysis_graph_config \<Rightarrow> ('ctx, 'g) analysis_cluster \<Rightarrow> string" where
  "analysis_cluster_label cfg cluster =
    (case cluster of
      ContextCluster owner ctx \<Rightarrow> cluster_label cfg owner ctx
    | GlobalCluster \<Rightarrow> ''Shared globals''
    | SourceCluster \<Rightarrow> ''Source'')"



definition analysis_cluster_dot ::
  "('ctx, 'g, 'a, 'd) analysis_graph_config \<Rightarrow> cfg
    \<Rightarrow> ('ctx, 'g) analysis_cluster list \<Rightarrow> ('ctx, 'g) analysis_node list
    \<Rightarrow> (('ctx, 'g) analysis_node \<times> analysis_edge_kind \<times> ('ctx, 'g) analysis_node) list
    \<Rightarrow> (pp \<times> 'ctx + 'g \<Rightarrow> 'a) \<Rightarrow> ('ctx, 'g) analysis_cluster \<Rightarrow> string" where
  "analysis_cluster_dot cfg g clusters ns es sol cluster =
    (let members = analysis_nodes_in_cluster cfg cluster ns
     in ''  subgraph '' @ analysis_cluster_id clusters cluster @ '' {'' @ nl
      @ ''    label='' @ dq @ analysis_cluster_label cfg cluster @ dq @ '';'' @ nl
      @ ''    style=rounded; color=gray70; penwidth=1;'' @ nl
      @ concat (map (\<lambda>n. ''    '' @ analysis_node_id cfg ns n @ '' [''
          @ analysis_node_attrs cfg g n
          @ (case n of SourceNode _ \<Rightarrow> '',label='' @ source_html_label
              (contextual_node_label cfg g sol n)
             | _ \<Rightarrow> '',label='' @ dq @ graphviz_label_text
              (contextual_node_label cfg g sol n) @ dq)
          @ ''];'' @ nl) members)
      @ ''  }'' @ nl)"

definition analysis_edge_dot ::
  "('ctx, 'g, 'a, 'd) analysis_graph_config \<Rightarrow> cfg \<Rightarrow> ('ctx, 'g) analysis_node list
    \<Rightarrow> (('ctx, 'g) analysis_node \<times> analysis_edge_kind \<times> ('ctx, 'g) analysis_node)
    \<Rightarrow> string" where
  "analysis_edge_dot cfg g ns e =
    (case e of (src, kind, dst) \<Rightarrow> ''  '' @ analysis_node_id cfg ns src @ '' -> ''
      @ analysis_node_id cfg ns dst @ '' ['' @ analysis_edge_attrs g kind @ ''];'' @ nl)"

definition analysis_graph_to_dot ::
  "('ctx, 'g, 'a, 'd) analysis_graph_config \<Rightarrow> cfg
    \<Rightarrow> (pp \<times> 'ctx + 'g \<Rightarrow> 'a) \<Rightarrow> ('ctx, 'g) analysis_graph \<Rightarrow> string" where
  "analysis_graph_to_dot cfg g sol graph =
    (case graph of (clusters, ns, es) \<Rightarrow>
      if analysis_graph_wf graph then
        ''digraph AnalysisCFG {'' @ nl
        @ ''  graph [rankdir=TB,newrank=true,splines=polyline,nodesep=0.5,ranksep=0.7,fontname='' @ dq @ ''Menlo'' @ dq @ ''];'' @ nl
        @ ''  node [shape=box,style=filled,fillcolor=lightgreen,fontname='' @ dq @ ''Menlo'' @ dq @ ''];'' @ nl
        @ ''  edge [fontname='' @ dq @ ''Menlo'' @ dq @ '',fontsize=10,arrowsize=0.8];'' @ nl
        @ concat (map (analysis_cluster_dot cfg g clusters ns es sol) clusters)
        @ concat (map (analysis_edge_dot cfg g ns) es)
        @ ''}'' @ nl
      else ''digraph AnalysisCFG { invalid_graph }'' @ nl)"

definition contextual_analysis_dot ::
  "('ctx, 'g, 'a, 'd) analysis_graph_config \<Rightarrow> cfg
    \<Rightarrow> ((pp \<times> 'ctx) + 'g) list \<Rightarrow> (pp \<times> 'ctx + 'g \<Rightarrow> 'a) \<Rightarrow> string" where
  "contextual_analysis_dot cfg g domain sol =
    analysis_graph_to_dot cfg g sol (build_analysis_graph cfg g domain sol)"

definition raw_cfg_graph_config ::
  "proc_table \<Rightarrow> pname list \<Rightarrow> pname \<Rightarrow> com \<Rightarrow> (pp \<Rightarrow> graphviz_node_annotation option)
    \<Rightarrow> (unit, unit, unit, unit) analysis_graph_config" where
  "raw_cfg_graph_config \<Pi> ps mnm main annotate =
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
      owner_of = compiled_owner_of \<Pi> ps mnm main,
      cluster_label = (\<lambda>owner _. owner),
      source_text = Some (pretty_string_of_program \<Pi> ps main),
      node_annotation = annotate
    \<rparr>"

definition raw_cfg_dot ::
  "proc_table \<Rightarrow> pname list \<Rightarrow> pname \<Rightarrow> com \<Rightarrow> (pp \<Rightarrow> graphviz_node_annotation option) \<Rightarrow> string" where
  "raw_cfg_dot \<Pi> ps mnm main annotate =
    (let g = compile_prog \<Pi> ps mnm main;
         cfg = raw_cfg_graph_config \<Pi> ps mnm main annotate;
         domain = contextual_graph_domain g (\<lambda>_. [()])
     in contextual_analysis_dot cfg g domain (\<lambda>_. ()))"

definition raw_cfg_dot_lit ::
  "proc_table \<Rightarrow> pname list \<Rightarrow> pname \<Rightarrow> com \<Rightarrow> (pp \<Rightarrow> graphviz_node_annotation option)
    \<Rightarrow> String.literal" where
  "raw_cfg_dot_lit \<Pi> ps mnm main annotate =
    String.implode (raw_cfg_dot \<Pi> ps mnm main annotate)"

end

