theory Analysis_Graph_Export
  imports Analysis_Graph_Wf Analysis_Graph_Naming
begin

section \<open>Handing a built graph out\<close>

text \<open>
  A built graph is an Isabelle value; a reader wants a file. This theory is
  the boundary between the two, and it crosses it three times over the same
  graph: a canonical text snapshot for regression fixtures, an
  \<open>export_graph\<close> record for the renderers, and a flat text listing of a
  check report.

  None of the three is a picture. \<open>export_graph\<close> in particular carries no
  colour, shape or label markup --- only clusters, nodes, edges, and for each a
  kind and a status naming what it \<^emph>\<open>is\<close>. Choosing how that looks is the job
  of the OCaml renderers that consume it, which is what keeps DOT and HTML
  reading the same graph rather than two drifting descriptions of it.

  This theory is also the session's single entry point to everything under it:
  importing it brings the graph model, its construction, the well-formedness
  theorem and the naming scheme along.
\<close>

subsection \<open>Canonical regression snapshot\<close>

text \<open>
  A deterministic textual snapshot of an \<^type>\<open>analysis_graph\<close>, for
  regression fixtures. It carries no presentation syntax at all --- colours,
  shapes and label markup belong to the renderers that consume
  \<open>export_graph\<close> (below) outside Isabelle --- so a fixture regresses only on the
  graph's own structure and content: clusters, node labels, check verdicts,
  abstract states, edge roles. Node and cluster identifiers reuse
  \<^const>\<open>analysis_node_id\<close>/\<^const>\<open>analysis_cluster_id\<close> rather than a second
  numbering scheme, so a snapshot and a rendered graph stay
  cross-referenceable. Ordering is the same deterministic insertion order
  \<^const>\<open>build_analysis_graph\<close> already establishes (list position, not a
  fresh sort) --- sorting here would paper over a real ordering regression in
  graph construction rather than catch it. The one omission is
  \<^const>\<open>SourceNode\<close>/\<^const>\<open>SourceCluster\<close>: the embedded pretty-printed
  program text is presentation convenience (the \<open>.vimp\<close> fixture already has
  that text), not graph structure.
\<close>

definition canonical_node_block ::
  "('ctx, 'g, 'a, 'd) analysis_graph_config \<Rightarrow> cfg
    \<Rightarrow> (pp \<times> 'ctx + 'g \<Rightarrow> 'a) \<Rightarrow> ('ctx, 'g) analysis_node list
    \<Rightarrow> ('ctx, 'g) analysis_node \<Rightarrow> string" where
  "canonical_node_block cfg g sol ns n =
    (case contextual_node_label_lines cfg g sol n of
       [] \<Rightarrow> ''  '' @ analysis_node_id cfg ns n @ '':'' @ nl
     | (first # rest) \<Rightarrow>
         ''  '' @ analysis_node_id cfg ns n @ '': '' @ first @ nl
           @ concat (map (\<lambda>line. ''      '' @ line @ nl) rest))"

definition analysis_graph_to_canonical_text ::
  "('ctx, 'g, 'a, 'd) analysis_graph_config \<Rightarrow> cfg
    \<Rightarrow> (pp \<times> 'ctx + 'g \<Rightarrow> 'a) \<Rightarrow> ('ctx, 'g) analysis_graph \<Rightarrow> string" where
  "analysis_graph_to_canonical_text cfg g sol graph =
    (case graph of (clusters, ns, es) \<Rightarrow>
      (let clusters' = filter (\<lambda>c. c \<noteq> SourceCluster) clusters;
           ns' = filter (\<lambda>n. case n of SourceNode _ \<Rightarrow> False | _ \<Rightarrow> True) ns
       in
        ''clusters:'' @ nl
        @ concat (map (\<lambda>c.
            ''  '' @ analysis_cluster_id clusters c @ '':'' @ nl
              @ concat (map (\<lambda>n. ''    '' @ analysis_node_id cfg ns n @ nl)
                  (analysis_nodes_in_cluster cfg c ns))) clusters')
        @ nl
        @ ''nodes:'' @ nl
        @ concat (map (canonical_node_block cfg g sol ns) ns')
        @ nl
        @ ''edges:'' @ nl
        @ concat (map (\<lambda>(src, kind, dst).
            ''  '' @ analysis_node_id cfg ns src @ '' -> '' @ analysis_node_id cfg ns dst
              @ '': '' @ canonical_edge_kind_text g kind @ nl) es)))"

definition contextual_analysis_canonical_text ::
  "('ctx, 'g, 'a, 'd) analysis_graph_config \<Rightarrow> cfg
    \<Rightarrow> ((pp \<times> 'ctx) + 'g) list \<Rightarrow> (pp \<times> 'ctx + 'g \<Rightarrow> 'a) \<Rightarrow> string" where
  "contextual_analysis_canonical_text cfg g domain sol =
    analysis_graph_to_canonical_text cfg g sol (build_analysis_graph cfg g domain sol)"

section \<open>Structured graph export\<close>

text \<open>
  A third view of the same \<^type>\<open>analysis_graph\<close>, alongside the DOT rendering and the
  canonical snapshot, and the only one whose consumer is outside Isabelle. It carries the
  graph's structure and content --- identifiers, labels, state lines, statuses, edge roles
  --- as a value, so a renderer that lives in the unverified CLI can produce DOT, HTML, or
  anything else without a second traversal of the CFG and without parsing rendered text.

  Nothing here is presentation: no DOT attribute strings, no HTML. A node's structural role
  and its \<^typ>\<open>node_status\<close> are stated as tags, leaving every styling decision to whichever
  renderer consumes them. The type is monomorphic where \<^type>\<open>analysis_graph\<close> is not: both
  the context type and the global-key type are already rendered away by the time a node
  reaches here, which is what lets one exported function serve every domain and every
  context discipline.
\<close>

datatype export_node_kind =
  XN_Entry | XN_Exit | XN_ProcEntry | XN_ProcExit | XN_Point | XN_Global | XN_Source

datatype export_edge_kind =
  XE_Intra | XE_Enter | XE_Combine | XE_CallToReturn | XE_GlobalRead | XE_GlobalWrite

record export_node =
  xn_id :: String.literal
  xn_label :: String.literal
  xn_kind :: export_node_kind
  xn_status :: "node_status option"
  xn_lines :: "String.literal list"

record export_edge =
  xe_src :: String.literal
  xe_dst :: String.literal
  xe_kind :: export_edge_kind
  xe_label :: String.literal

record export_cluster =
  xc_id :: String.literal
  xc_label :: String.literal
  xc_nodes :: "String.literal list"

record export_graph =
  xg_clusters :: "export_cluster list"
  xg_nodes :: "export_node list"
  xg_edges :: "export_edge list"

text \<open>
  A point's structural role when it carries no annotation, as a tag instead of as the
  attributes a renderer would pick for it. A renderer reading \<^const>\<open>xn_kind\<close> and
  \<^const>\<open>xn_status\<close> together has everything the styling decision needs.
\<close>

definition export_node_kind_of ::
  "cfg \<Rightarrow> ('ctx, 'g) analysis_node \<Rightarrow> export_node_kind" where
  "export_node_kind_of g n =
    (case n of
      LocalNode p _ \<Rightarrow>
        (if p = cfg_entry g then XN_Entry
         else if p = entry_proc_exit g then XN_Exit
         else if p \<in> set (proc_entry_pps_list g) then XN_ProcEntry
         else if p \<in> set (proc_exit_pps_list g) then XN_ProcExit
         else XN_Point)
    | GlobalNode _ \<Rightarrow> XN_Global
    | SourceNode _ \<Rightarrow> XN_Source)"

definition export_edge_kind_of :: "analysis_edge_kind \<Rightarrow> export_edge_kind" where
  "export_edge_kind_of kind =
    (case kind of
      IntraEdge _ \<Rightarrow> XE_Intra
    | EnterEdge _ _ \<Rightarrow> XE_Enter
    | CombineEdge _ _ _ \<Rightarrow> XE_Combine
    | CallToReturnEdge _ \<Rightarrow> XE_CallToReturn
    | GlobalReadEdge \<Rightarrow> XE_GlobalRead
    | GlobalWriteEdge \<Rightarrow> XE_GlobalWrite)"

text \<open>
  An edge's own content, with none of the wording that names its role. A renderer and
  \<^const>\<open>canonical_edge_kind_text\<close> prefix that content differently --- \<open>call f(x)\<close> against
  \<open>enter f(x)\<close> for one and the same edge --- because each is writing for its own reader.
  Pairing this payload with \<^const>\<open>export_edge_kind_of\<close> leaves that choice to whichever
  renderer consumes the export, instead of freezing one renderer's phrasing into the
  exported value and making every other consumer strip it.
\<close>

definition export_edge_label :: "cfg \<Rightarrow> analysis_edge_kind \<Rightarrow> string" where
  "export_edge_label g kind =
    (case kind of
      IntraEdge a \<Rightarrow> source_action_label g a
    | EnterEdge callee a \<Rightarrow> callee @ ''(''
        @ (case a of CallEdge _ _ es \<Rightarrow> join_source '', '' (map (string_of_exp 0) es)) @ '')''
    | CombineEdge _ dst ret \<Rightarrow>
        (case (dst, ret) of
           (Some x, Some r) \<Rightarrow> String.explode x @ '' := '' @ String.explode r
         | (Some x, None) \<Rightarrow> String.explode x
         | (None, _) \<Rightarrow> '''')
    | CallToReturnEdge callee \<Rightarrow> String.explode callee
    | GlobalReadEdge \<Rightarrow> ''''
    | GlobalWriteEdge \<Rightarrow> '''')"

text \<open>
  \<^const>\<open>contextual_node_label_lines\<close> puts a node's display name first and its content
  after, except at a \<^const>\<open>SourceNode\<close>, whose single line is the program text itself and
  names nothing. Splitting the two apart here is what lets a consumer put the name in a
  graph node and the content somewhere else entirely --- the separation the DOT rendering
  cannot make, because there the two are one joined attribute string.
\<close>

definition export_node_of ::
  "('ctx, 'g, 'a, 'd) analysis_graph_config \<Rightarrow> cfg
    \<Rightarrow> (pp \<times> 'ctx + 'g \<Rightarrow> 'a) \<Rightarrow> ('ctx, 'g) analysis_node list
    \<Rightarrow> ('ctx, 'g) analysis_node \<Rightarrow> export_node" where
  "export_node_of cfg g sol ns n =
    (let lines = contextual_node_label_lines cfg g sol n;
         status = (case n of LocalNode p ctx \<Rightarrow> map_option annotation_status (node_annotation cfg p ctx)
                   | _ \<Rightarrow> None);
         named = (case n of SourceNode _ \<Rightarrow> False | _ \<Rightarrow> True)
     in \<lparr> xn_id = String.implode (analysis_node_id cfg ns n),
          xn_label = String.implode (if named then (case lines of [] \<Rightarrow> '''' | l # _ \<Rightarrow> l) else ''''),
          xn_kind = export_node_kind_of g n,
          xn_status = status,
          xn_lines = map String.implode (if named then (case lines of [] \<Rightarrow> [] | _ # rest \<Rightarrow> rest) else lines) \<rparr>)"

definition export_cluster_of ::
  "('ctx, 'g, 'a, 'd) analysis_graph_config \<Rightarrow> ('ctx, 'g) analysis_cluster list
    \<Rightarrow> ('ctx, 'g) analysis_node list \<Rightarrow> ('ctx, 'g) analysis_cluster \<Rightarrow> export_cluster" where
  "export_cluster_of cfg clusters ns cluster =
    \<lparr> xc_id = String.implode (analysis_cluster_id clusters cluster),
      xc_label = String.implode (analysis_cluster_label cfg cluster),
      xc_nodes = map (\<lambda>n. String.implode (analysis_node_id cfg ns n))
                   (analysis_nodes_in_cluster cfg cluster ns) \<rparr>"

text \<open>
  Ordering is \<^const>\<open>build_analysis_graph\<close>'s own insertion order throughout, the same
  choice \<^const>\<open>analysis_graph_to_canonical_text\<close> makes and for the same reason: sorting
  here would hide an ordering regression in graph construction rather than surface it.
  Unlike the canonical snapshot, the source node is kept --- a viewer that shows the
  program text alongside the graph needs it, and dropping it would force the consumer to
  pretty-print the program a second time.
\<close>

definition analysis_graph_to_export ::
  "('ctx, 'g, 'a, 'd) analysis_graph_config \<Rightarrow> cfg
    \<Rightarrow> (pp \<times> 'ctx + 'g \<Rightarrow> 'a) \<Rightarrow> ('ctx, 'g) analysis_graph \<Rightarrow> export_graph" where
  "analysis_graph_to_export cfg g sol graph =
    (case graph of (clusters, ns, es) \<Rightarrow>
      \<lparr> xg_clusters = map (export_cluster_of cfg clusters ns) clusters,
        xg_nodes = map (export_node_of cfg g sol ns) ns,
        xg_edges = map (\<lambda>(src, kind, dst).
          \<lparr> xe_src = String.implode (analysis_node_id cfg ns src),
            xe_dst = String.implode (analysis_node_id cfg ns dst),
            xe_kind = export_edge_kind_of kind,
            xe_label = String.implode (export_edge_label g kind) \<rparr>) es \<rparr>)"

definition contextual_analysis_export ::
  "('ctx, 'g, 'a, 'd) analysis_graph_config \<Rightarrow> cfg
    \<Rightarrow> ((pp \<times> 'ctx) + 'g) list \<Rightarrow> (pp \<times> 'ctx + 'g \<Rightarrow> 'a) \<Rightarrow> export_graph" where
  "contextual_analysis_export cfg g domain sol =
    analysis_graph_to_export cfg g sol (build_analysis_graph cfg g domain sol)"

definition raw_cfg_graph_config ::
  "proc_table \<Rightarrow> pname list \<Rightarrow> (pp \<Rightarrow> graph_node_annotation option)
    \<Rightarrow> (unit, unit, unit, unit) analysis_graph_config" where
  "raw_cfg_graph_config \<Pi> ps annotate =
    \<lparr> local_of = id,
      route = (\<lambda>_ _ _ _. Some ()),
      context_key = (\<lambda>_. STR ''unit''),
      show_context = (\<lambda>_. ''unit''),
      locals_for_pp = (\<lambda>_. []),
      return_slot_for_pp = (\<lambda>_. None),
      globals_to_show = [],
      show_local = (\<lambda>_ _ _ _. []),
      format_return = (\<lambda>_ _ _ _. []),
      show_global = (\<lambda>_ _ _. []),
      show_global_key = (\<lambda>_. ''''),
      is_shared_global = (\<lambda>_. False),
      show_internal_globals = False,
      owner_of = String.explode o compiled_owner_of \<Pi> ps,
      cluster_label = (\<lambda>owner _. owner @ '' / unit''),
      source_text = Some (pretty_string_of_program \<Pi> ps (main_body \<Pi>) []),
      node_annotation = (\<lambda>p _. annotate p)
    \<rparr>"


definition raw_cfg_canonical_text ::
  "proc_table \<Rightarrow> pname list \<Rightarrow> (pp \<Rightarrow> graph_node_annotation option) \<Rightarrow> string" where
  "raw_cfg_canonical_text \<Pi> ps annotate =
    (let g = compile_prog \<Pi> ps;
         cfg = raw_cfg_graph_config \<Pi> ps annotate;
         domain = contextual_graph_domain g (\<lambda>_. [()])
     in contextual_analysis_canonical_text cfg g domain (\<lambda>_. ()))"

definition raw_cfg_canonical_text_lit ::
  "proc_table \<Rightarrow> pname list \<Rightarrow> (pp \<Rightarrow> graph_node_annotation option)
    \<Rightarrow> String.literal" where
  "raw_cfg_canonical_text_lit \<Pi> ps annotate =
    String.implode (raw_cfg_canonical_text \<Pi> ps annotate)"

text \<open>
  The structured-export sibling of \<^const>\<open>raw_cfg_canonical_text\<close>: the same compiled CFG,
  the same one-context graph configuration, the same annotation hook, differing only in
  which view of the built graph it returns. Already \<^typ>\<open>String.literal\<close>-valued
  throughout, so there is no \<open>_lit\<close> counterpart to write.
\<close>

definition raw_cfg_export ::
  "proc_table \<Rightarrow> pname list \<Rightarrow> (pp \<Rightarrow> graph_node_annotation option)
    \<Rightarrow> export_graph" where
  "raw_cfg_export \<Pi> ps annotate =
    (let g = compile_prog \<Pi> ps;
         cfg = raw_cfg_graph_config \<Pi> ps annotate;
         domain = contextual_graph_domain g (\<lambda>_. [()])
     in contextual_analysis_export cfg g domain (\<lambda>_. ()))"

section \<open>Textual check report\<close>

text \<open>
  A minimal textual rendering of a \<^type>\<open>check_report_entry\<close> list --- kept
  separate from \<^const>\<open>classify_checks\<close> itself, the same separation
  \<^const>\<open>check_result_annotation\<close> keeps between classification and its own
  GraphViz styling. One line per entry: the check's own node, its condition,
  and its status.
\<close>

fun string_of_check_result :: "check_result \<Rightarrow> string" where
  "string_of_check_result Check_Proved = ''PROVED''"
| "string_of_check_result Check_Refuted = ''REFUTED''"
| "string_of_check_result Check_Unknown = ''UNKNOWN''"

definition string_of_check_report_entry :: "check_report_entry \<Rightarrow> string" where
  "string_of_check_report_entry entry =
     (case entry of (v, cnd, res) \<Rightarrow>
        string_of_cfg_node v @ '': '' @ string_of_exp 0 cnd @ ''  '' @ string_of_check_result res)"

section \<open>Report-driven annotation\<close>

text \<open>
  Looks up the report entry at a queried node and, if one exists, renders it
  through \<^const>\<open>check_result_annotation\<close>. This lets a caller's
  \<open>node_annotation\<close> hook consume a whole-program \<^const>\<open>classify_checks\<close>
  report directly instead of restating a manually maintained \<^typ>\<open>pp\<close>-to-
  \<^typ>\<open>exp\<close> table --- the report already names every checked node once.
\<close>

definition check_report_node_annotation ::
    "check_report_entry list \<Rightarrow> pp \<Rightarrow> graph_node_annotation option" where
  "check_report_node_annotation report v =
     (case find (\<lambda>entry. fst entry = v) report of
        Some (_, cnd, res) \<Rightarrow> Some (check_result_annotation res cnd)
      | None \<Rightarrow> None)"

end
