theory Analysis_GraphViz
  imports
    "Voblint_CFG.CFG_GraphViz"
    "Voblint_CFG.IMP2_Proc_to_CFG"
    TD_Side_CFG
    Exec_St
    Abstract_Domain
begin

text \<open>
  Edge and combine enumeration of a compiled program, read off the CFG via the
  sorted-set encodings.  These code-generate: @{const cfg_edges_list} /
  @{const cfg_combines_list} drop their finiteness guard for the code generator
  (CFG_Def), and @{typ edge_action} carries a structural executable linear order.
\<close>

definition prog_cfg_edges ::
    "proc_table \<Rightarrow> pname list \<Rightarrow> com \<Rightarrow> (pp \<times> edge_action \<times> pp) list" where
  "prog_cfg_edges \<Pi> ps main = cfg_edges_list (compile_prog \<Pi> ps main)"

definition prog_cfg_combines ::
    "proc_table \<Rightarrow> pname list \<Rightarrow> com
     \<Rightarrow> (pp \<times> pp \<times> pp \<times> vname option) list" where
  "prog_cfg_combines \<Pi> ps main = cfg_combines_list (compile_prog \<Pi> ps main)"

section \<open>Generic analysis-annotated CFG rendering\<close>

text \<open>
  Bridges the executable abstract state (@{text "'a st"}) with the
  @{const to_graphviz_labeled} entry point in
  @{theory Voblint_CFG.CFG_GraphViz}.

  The @{class show_val} instance for the domain type is resolved
  automatically.  Region-scoped locals come from @{text "sol (Inl pp)"};
  globals from @{text "sol (Inr ())"} in @{text "cluster_globals"}.

  The @{text "_lit"} variants return @{type String.literal}, which the
  code generator maps to native ML @{text "string"}, so example files
  need no @{text "char list"} decoder -- a single @{command ML_val}
  with @{text "writeln"} suffices.
\<close>

subsection \<open>Node-label builder\<close>

text \<open>
  The side TD solver stores @{text "sol (Inl pp)"} (frame-local, flow-sensitive)
  and @{text "sol (Inr ())"} (single global unknown, flow-insensitive) separately.
  Node labels show flow-sensitive @{text "Inl"} locals scoped to each procedure
  region.  Globals are not repeated on nodes (the solver keeps one flow-insensitive
  @{text "Inr"} unknown); they appear once in @{text "cluster_globals"}.
\<close>

definition gv_nl :: string where "gv_nl = [CHR 0x5C, CHR 0x6E]"

fun join_gv_nl :: "string list \<Rightarrow> string" where
  "join_gv_nl [] = []"
| "join_gv_nl [s] = s"
| "join_gv_nl (s # ss) = s @ gv_nl @ join_gv_nl ss"

definition label_of_st ::
    "('a::bot \<Rightarrow> string) \<Rightarrow> vname list \<Rightarrow> 'a st \<Rightarrow> string" where
  "label_of_st pr vars st =
     join_gv_nl (map (\<lambda>x. x @ ''='' @ pr (lookup_st st x)) vars)"

definition side_env_st ::
    "(pp + unit \<Rightarrow> 'a::bounded_semilattice_sup_bot st) \<Rightarrow> pp \<Rightarrow> 'a st" where
  "side_env_st sol p = sol (Inl p) \<squnion> sol (Inr ())"

definition collect_vars_prog ::
    "proc_table \<Rightarrow> pname list \<Rightarrow> com \<Rightarrow> vname list" where
  "collect_vars_prog \<Pi> ps main =
     remdups (concat (map (\<lambda>(_, a, _). vars_of_action a) (prog_cfg_edges \<Pi> ps main)))"

definition collect_region_vars ::
    "(pp \<times> edge_action \<times> pp) list \<Rightarrow> pp list \<Rightarrow> vname list" where
  "collect_region_vars Es pps =
     remdups (concat (map (\<lambda>e. case e of (u, a, v) \<Rightarrow>
            if mem_pp u pps then vars_of_action a else []) Es))"

definition collect_local_vars_region ::
    "(pp \<times> edge_action \<times> pp) list \<Rightarrow> pp list \<Rightarrow> vname list" where
  "collect_local_vars_region Es pps =
     filter (\<lambda>x. \<not> is_global x) (collect_region_vars Es pps)"

fun region_pps_of :: "graphviz_region list \<Rightarrow> pp \<Rightarrow> pp list" where
  "region_pps_of [] p = []"
| "region_pps_of ((owner, vs) # regs) p =
     (if mem_pp p vs then vs else region_pps_of regs p)"

definition collect_global_vars_prog ::
    "proc_table \<Rightarrow> pname list \<Rightarrow> com \<Rightarrow> vname list" where
  "collect_global_vars_prog \<Pi> ps main =
     filter is_global (collect_vars_prog \<Pi> ps main)"

subsection \<open>Per-pp and global-side labelers\<close>

definition analysis_local_node_label ::
    "('a::bounded_semilattice_sup_bot \<Rightarrow> string) \<Rightarrow> vname list \<Rightarrow>
     (pp + unit \<Rightarrow> 'a st) \<Rightarrow> pp \<Rightarrow> string" where
  "analysis_local_node_label pr lvars sol p =
     (let base = string_of_nat p @ [CHR 0x5C, CHR 0x6E] @ label_of_st pr lvars (sol (Inl p))
      in  if lvars = [] then string_of_nat p else base)"

definition analysis_region_node_label_prog ::
    "('a::bounded_semilattice_sup_bot \<Rightarrow> string) \<Rightarrow> proc_table \<Rightarrow> pname list \<Rightarrow> com \<Rightarrow>
     (pp + unit \<Rightarrow> 'a st) \<Rightarrow> pp \<Rightarrow> string" where
  "analysis_region_node_label_prog pr \<Pi> ps main sol p =
     analysis_local_node_label pr
       (collect_local_vars_region (prog_cfg_edges \<Pi> ps main)
          (region_pps_of (compile_prog_regions \<Pi> ps main) p))
       sol p"

definition globals_side_label ::
    "('a::bounded_semilattice_sup_bot \<Rightarrow> string) \<Rightarrow> vname list \<Rightarrow>
     (pp + unit \<Rightarrow> 'a st) \<Rightarrow> string" where
  "globals_side_label pr gvars sol = label_of_st pr gvars (sol (Inr ()))"

definition globals_cluster_dot :: "string \<Rightarrow> string" where
  "globals_cluster_dot lab =
     (if lab = [] then []
      else ''  subgraph cluster_globals {'' @ nl
        @ ''    label='' @ dq @ ''globals (flow-insensitive)'' @ dq @ '';'' @ nl
        @ ''    style=filled; color=lightyellow;'' @ nl
        @ ''    globals_side [shape=note,label='' @ dq @ lab @ dq @ ''];'' @ nl
        @ ''  }'' @ nl)"

(* Legacy combined label (Inl join Inr); kept for cfg-level call sites. *)

definition analysis_node_label ::
    "('a::bounded_semilattice_sup_bot \<Rightarrow> string) \<Rightarrow> vname list \<Rightarrow>
     (pp + unit \<Rightarrow> 'a st) \<Rightarrow> pp \<Rightarrow> string" where
  "analysis_node_label pr vars sol p =
     string_of_nat p @ [CHR 0x5C, CHR 0x6E] @ label_of_st pr vars (side_env_st sol p)"

subsection \<open>Annotated DOT generators\<close>

definition graphviz_of_analysis ::
    "('a::bounded_semilattice_sup_bot \<Rightarrow> string) \<Rightarrow> vname list \<Rightarrow> (pp + unit \<Rightarrow> 'a st) \<Rightarrow>
     cfg \<Rightarrow> graphviz_region list \<Rightarrow> pp list \<Rightarrow> pp list \<Rightarrow> string" where
  "graphviz_of_analysis pr vars sol g regs ents exts =
     to_graphviz_labeled (analysis_node_label pr vars sol) g regs ents exts"

text \<open>
  Auto variant: the @{class show_val} instance supplies the printer.
\<close>

definition graphviz_of_analysis_auto ::
    "vname list \<Rightarrow> (pp + unit \<Rightarrow> 'a::{show_val, bounded_semilattice_sup_bot} st) \<Rightarrow>
     cfg \<Rightarrow> graphviz_region list \<Rightarrow> pp list \<Rightarrow> pp list \<Rightarrow> string" where
  "graphviz_of_analysis_auto vars sol g regs ents exts =
     graphviz_of_analysis show_val vars sol g regs ents exts"

definition edges_to_dot_list :: "(pp \<times> edge_action \<times> pp) list \<Rightarrow> string" where
  "edges_to_dot_list Es = concat (map edge_to_dot Es)"

definition combines_to_dot_list ::
    "(pp \<times> pp \<times> pp \<times> vname option) list \<Rightarrow> string" where
  "combines_to_dot_list Cs = concat (map combine_to_dot Cs)"

definition proc_entry_pps_prog ::
    "proc_table \<Rightarrow> pname list \<Rightarrow> com \<Rightarrow> pp list" where
  "proc_entry_pps_prog \<Pi> ps main = enter_targets (prog_cfg_edges \<Pi> ps main)"

definition proc_exit_pps_prog ::
    "proc_table \<Rightarrow> pname list \<Rightarrow> com \<Rightarrow> pp list" where
  "proc_exit_pps_prog \<Pi> ps main = combine_exits (prog_cfg_combines \<Pi> ps main)"

definition to_graphviz_labeled_prog ::
    "(pp \<Rightarrow> string) \<Rightarrow> proc_table \<Rightarrow> pname list \<Rightarrow> com \<Rightarrow>
     graphviz_region list \<Rightarrow> pp list \<Rightarrow> pp list \<Rightarrow> string" where
  "to_graphviz_labeled_prog lbl \<Pi> ps main regs proc_entries proc_exits =
     (let g = compile_prog \<Pi> ps main
      in  ''digraph CFG {'' @ nl
       @ ''  rankdir=TB;'' @ nl
       @ concat (map (region_to_dot_labeled lbl g proc_entries proc_exits) regs)
       @ edges_to_dot_list (prog_cfg_edges \<Pi> ps main)
       @ combines_to_dot_list (prog_cfg_combines \<Pi> ps main)
       @ ''}'' @ nl)"

definition to_graphviz_side_analysis_prog ::
    "(pp \<Rightarrow> string) \<Rightarrow> string \<Rightarrow> proc_table \<Rightarrow> pname list \<Rightarrow> com \<Rightarrow>
     graphviz_region list \<Rightarrow> pp list \<Rightarrow> pp list \<Rightarrow> string" where
  "to_graphviz_side_analysis_prog lbl globals_lab \<Pi> ps main regs proc_entries proc_exits =
     (let g = compile_prog \<Pi> ps main
      in  ''digraph CFG {'' @ nl
       @ ''  rankdir=TB;'' @ nl
       @ concat (map (region_to_dot_labeled lbl g proc_entries proc_exits) regs)
       @ edges_to_dot_list (prog_cfg_edges \<Pi> ps main)
       @ combines_to_dot_list (prog_cfg_combines \<Pi> ps main)
       @ globals_cluster_dot globals_lab
       @ ''}'' @ nl)"

definition graphviz_of_analysis_prog ::
    "(pp + unit \<Rightarrow> 'a::{show_val, bounded_semilattice_sup_bot} st) \<Rightarrow>
     proc_table \<Rightarrow> pname list \<Rightarrow> com \<Rightarrow> string" where
  "graphviz_of_analysis_prog sol \<Pi> ps main =
     to_graphviz_side_analysis_prog
       (analysis_region_node_label_prog show_val \<Pi> ps main sol)
       (globals_side_label show_val (collect_global_vars_prog \<Pi> ps main) sol)
       \<Pi> ps main
       (compile_prog_regions \<Pi> ps main)
       (proc_entry_pps_prog \<Pi> ps main)
       (proc_exit_pps_prog \<Pi> ps main)"

subsection \<open>Context-indexed debug DOT generators\<close>

text \<open>
  Debug rendering for already-materialised context-indexed analysis graphs.
  The caller supplies the context list, context labels, node labels, and the
  context-specific edges.  This layer only assembles DOT; it does not reconstruct
  call contexts from the plain CFG.
\<close>

definition ctx_debug_node_id :: "('ctx \<Rightarrow> string) \<Rightarrow> pp * 'ctx \<Rightarrow> string" where
  "ctx_debug_node_id ctx_key pc =
     (case pc of (p, k) \<Rightarrow> ''pp'' @ string_of_nat p @ ''_ctx_'' @ ctx_key k)"

definition ctx_debug_nodes_for :: "'ctx \<Rightarrow> (pp * 'ctx) list \<Rightarrow> (pp * 'ctx) list" where
  "ctx_debug_nodes_for k ns = filter (\<lambda>pc. snd pc = k) ns"

definition ctx_debug_cluster_id :: "('ctx \<Rightarrow> string) \<Rightarrow> 'ctx \<Rightarrow> string" where
  "ctx_debug_cluster_id ctx_key k = ''cluster_ctx_'' @ ctx_key k"

definition ctx_debug_node_dot ::
  "('ctx \<Rightarrow> string) \<Rightarrow> (pp * 'ctx \<Rightarrow> string) \<Rightarrow> (pp \<Rightarrow> string) \<Rightarrow> pp * 'ctx \<Rightarrow> string" where
  "ctx_debug_node_dot ctx_key node_label node_attrs pc =
     (case pc of (p, k) \<Rightarrow>
        ''  '' @ ctx_debug_node_id ctx_key pc @ '' ['' @ node_attrs p @
        '',label='' @ dq @ node_label pc @ dq @ ''];'' @ nl)"

definition ctx_debug_cluster_dot ::
  "('ctx \<Rightarrow> string) \<Rightarrow> ('ctx \<Rightarrow> string) \<Rightarrow> (pp * 'ctx \<Rightarrow> string) \<Rightarrow> (pp \<Rightarrow> string) \<Rightarrow>
   (pp * 'ctx) list \<Rightarrow> 'ctx \<Rightarrow> string" where
  "ctx_debug_cluster_dot ctx_key ctx_label node_label node_attrs ns k =
     ''  subgraph '' @ ctx_debug_cluster_id ctx_key k @ '' {'' @ nl @
     ''    label='' @ dq @ ctx_label k @ dq @ '';'' @ nl @
     ''    style=filled; color=lightgrey; fillcolor=white;'' @ nl @
     concat (map (ctx_debug_node_dot ctx_key node_label node_attrs)
       (ctx_debug_nodes_for k ns)) @
     ''  }'' @ nl"

definition ctx_debug_globals_node_id :: "('ctx \<Rightarrow> string) \<Rightarrow> 'ctx \<Rightarrow> string" where
  "ctx_debug_globals_node_id ctx_key k = ''globals_ctx_'' @ ctx_key k"

definition ctx_debug_globals_node_dot :: "('ctx \<Rightarrow> string) \<Rightarrow> ('ctx \<Rightarrow> string) \<Rightarrow> 'ctx \<Rightarrow> string" where
  "ctx_debug_globals_node_dot ctx_key globals_label k =
     (let lab = globals_label k in
      if lab = [] then []
      else ''    '' @ ctx_debug_globals_node_id ctx_key k @
        '' [shape=note,width=2.2,fixedsize=false,label='' @ dq @ ''global env'' @ gv_nl @
        ''(flow-insensitive)'' @ gv_nl @ lab @ dq @ ''];'' @ nl)"

definition ctx_debug_cluster_dot_with_globals ::
  "('ctx \<Rightarrow> string) \<Rightarrow> ('ctx \<Rightarrow> string) \<Rightarrow> ('ctx \<Rightarrow> string) \<Rightarrow>
   (pp * 'ctx \<Rightarrow> string) \<Rightarrow> (pp \<Rightarrow> string) \<Rightarrow> (pp * 'ctx) list \<Rightarrow> 'ctx \<Rightarrow> string" where
  "ctx_debug_cluster_dot_with_globals ctx_key ctx_label globals_label node_label node_attrs ns k =
     ''  subgraph '' @ ctx_debug_cluster_id ctx_key k @ '' {'' @ nl @
     ''    label='' @ dq @ ctx_label k @ dq @ '';'' @ nl @
     ''    style=filled; color=lightgrey; fillcolor=white;'' @ nl @
     concat (map (ctx_debug_node_dot ctx_key node_label node_attrs)
       (ctx_debug_nodes_for k ns)) @
     ctx_debug_globals_node_dot ctx_key globals_label k @
     ''  }'' @ nl"

definition ctx_debug_intra_dot ::
  "('ctx \<Rightarrow> string) \<Rightarrow> (pp * 'ctx) * edge_action * (pp * 'ctx) \<Rightarrow> string" where
  "ctx_debug_intra_dot ctx_key e =
     (case e of (src, a, dst) \<Rightarrow>
        ''  '' @ ctx_debug_node_id ctx_key src @ '' -> '' @ ctx_debug_node_id ctx_key dst @
        '' [label='' @ dq @ string_of_action a @ dq @ ''];'' @ nl)"

definition ctx_debug_call_dot ::
  "('ctx \<Rightarrow> string) \<Rightarrow> ('ctx \<Rightarrow> string) \<Rightarrow> (pp * 'ctx) * (pp * 'ctx) \<Rightarrow> string" where
  "ctx_debug_call_dot ctx_key ctx_label e =
     (case e of (src, dst) \<Rightarrow>
        ''  '' @ ctx_debug_node_id ctx_key src @ '' -> '' @ ctx_debug_node_id ctx_key dst @
        '' [color=purple,penwidth=2,label='' @ dq @ ''EA_Enter'' @ gv_nl @
        ''callee '' @ (case dst of (_, k) \<Rightarrow> ctx_label k) @ dq @ ''];'' @ nl)"

definition ctx_debug_return_dot ::
  "('ctx \<Rightarrow> string) \<Rightarrow> (pp * 'ctx) * combine_info * (pp * 'ctx) \<Rightarrow> string" where
  "ctx_debug_return_dot ctx_key e =
     (case e of (src, (call, ex, ret, cdst), dst) \<Rightarrow>
        ''  '' @ ctx_debug_node_id ctx_key src @ '' -> '' @ ctx_debug_node_id ctx_key dst @
        '' [style=dashed,color=blue,label='' @ dq @ ''return'' @ gv_nl @ ''combine ('' @
        string_of_nat call @ '','' @ string_of_nat ex @ '','' @ string_of_nat ret @
        '')'' @ dq @ ''];'' @ nl)"

definition ctx_debug_graphviz ::
  "('ctx \<Rightarrow> string) \<Rightarrow> ('ctx \<Rightarrow> string) \<Rightarrow> (pp * 'ctx \<Rightarrow> string) \<Rightarrow> (pp \<Rightarrow> string) \<Rightarrow>
   'ctx list \<Rightarrow> (pp * 'ctx) list \<Rightarrow>
   ((pp * 'ctx) * edge_action * (pp * 'ctx)) list \<Rightarrow>
   ((pp * 'ctx) * (pp * 'ctx)) list \<Rightarrow>
   ((pp * 'ctx) * combine_info * (pp * 'ctx)) list \<Rightarrow> string" where
  "ctx_debug_graphviz ctx_key ctx_label node_label node_attrs ks ns intra_edges call_edges return_edges =
     ''digraph CFG_CTX {'' @ nl @
     ''  rankdir=TB;'' @ nl @
     ''  node [fontname='' @ dq @ ''Menlo'' @ dq @ ''];'' @ nl @
     concat (map (ctx_debug_cluster_dot ctx_key ctx_label node_label node_attrs ns) ks) @
     concat (map (ctx_debug_intra_dot ctx_key) intra_edges) @
     concat (map (ctx_debug_call_dot ctx_key ctx_label) call_edges) @
     concat (map (ctx_debug_return_dot ctx_key) return_edges) @
     ''}'' @ nl"

definition ctx_debug_graphviz_with_globals ::
  "('ctx \<Rightarrow> string) \<Rightarrow> ('ctx \<Rightarrow> string) \<Rightarrow> ('ctx \<Rightarrow> string) \<Rightarrow>
   (pp * 'ctx \<Rightarrow> string) \<Rightarrow> (pp \<Rightarrow> string) \<Rightarrow> 'ctx list \<Rightarrow> (pp * 'ctx) list \<Rightarrow>
   ((pp * 'ctx) * edge_action * (pp * 'ctx)) list \<Rightarrow>
   ((pp * 'ctx) * (pp * 'ctx)) list \<Rightarrow>
   ((pp * 'ctx) * combine_info * (pp * 'ctx)) list \<Rightarrow> string" where
  "ctx_debug_graphviz_with_globals ctx_key ctx_label globals_label node_label node_attrs ks ns intra_edges call_edges return_edges =
     ''digraph CFG_CTX {'' @ nl @
     ''  rankdir=TB;'' @ nl @
     ''  node [fontname='' @ dq @ ''Menlo'' @ dq @ ''];'' @ nl @
     concat (map (ctx_debug_cluster_dot_with_globals ctx_key ctx_label globals_label node_label node_attrs ns) ks) @
     concat (map (ctx_debug_intra_dot ctx_key) intra_edges) @
     concat (map (ctx_debug_call_dot ctx_key ctx_label) call_edges) @
     concat (map (ctx_debug_return_dot ctx_key) return_edges) @
     ''}'' @ nl"

text \<open>
  Convenience adapter for witnesses where the rendered context is unchanged
  along every CFG edge and combine edge.  Analyses with value-dependent call
  contexts should call @{const ctx_debug_graphviz} directly with explicit
  context-specific edges.
\<close>

definition ctx_debug_same_ctx_nodes :: "'ctx list \<Rightarrow> pp list \<Rightarrow> (pp * 'ctx) list" where
  "ctx_debug_same_ctx_nodes ks ps = concat (map (\<lambda>k. map (\<lambda>p. (p, k)) ps) ks)"

definition ctx_debug_same_ctx_intra_edges ::
  "'ctx list \<Rightarrow> (pp * edge_action * pp) list \<Rightarrow> ((pp * 'ctx) * edge_action * (pp * 'ctx)) list" where
  "ctx_debug_same_ctx_intra_edges ks es =
     concat (map (\<lambda>k. concat (map (\<lambda>e. case e of
       (u, EA_Enter xs es, v) \<Rightarrow> []
     | (u, a, v) \<Rightarrow> [((u, k), a, (v, k))]) es)) ks)"

definition ctx_debug_same_ctx_call_edges ::
  "'ctx list \<Rightarrow> (pp * edge_action * pp) list \<Rightarrow> ((pp * 'ctx) * (pp * 'ctx)) list" where
  "ctx_debug_same_ctx_call_edges ks es =
     concat (map (\<lambda>k. concat (map (\<lambda>e. case e of
       (u, EA_Enter xs es, v) \<Rightarrow> [((u, k), (v, k))]
     | _ \<Rightarrow> []) es)) ks)"

definition ctx_debug_same_ctx_return_edges ::
  "'ctx list \<Rightarrow> combine_info list
   \<Rightarrow> ((pp * 'ctx) * combine_info * (pp * 'ctx)) list" where
  "ctx_debug_same_ctx_return_edges ks cs =
     concat (map (\<lambda>k. map (\<lambda>(call, ex, ret, dst).
       ((ex, k), (call, ex, ret, dst), (ret, k))) cs) ks)"

definition ctx_debug_graphviz_same_ctx_lists ::
  "('ctx \<Rightarrow> string) \<Rightarrow> ('ctx \<Rightarrow> string) \<Rightarrow> (pp * 'ctx \<Rightarrow> string) \<Rightarrow> (pp \<Rightarrow> string) \<Rightarrow>
   'ctx list \<Rightarrow> pp list \<Rightarrow> (pp * edge_action * pp) list
   \<Rightarrow> combine_info list \<Rightarrow> string" where
  "ctx_debug_graphviz_same_ctx_lists ctx_key ctx_label node_label node_attrs ks ps es cs =
     ctx_debug_graphviz ctx_key ctx_label node_label node_attrs ks
       (ctx_debug_same_ctx_nodes ks ps)
       (ctx_debug_same_ctx_intra_edges ks es)
       (ctx_debug_same_ctx_call_edges ks es)
       (ctx_debug_same_ctx_return_edges ks cs)"

definition ctx_debug_graphviz_same_ctx_lists_with_globals ::
  "('ctx \<Rightarrow> string) \<Rightarrow> ('ctx \<Rightarrow> string) \<Rightarrow> ('ctx \<Rightarrow> string) \<Rightarrow>
   (pp * 'ctx \<Rightarrow> string) \<Rightarrow> (pp \<Rightarrow> string) \<Rightarrow> 'ctx list \<Rightarrow> pp list \<Rightarrow>
   (pp * edge_action * pp) list \<Rightarrow> combine_info list \<Rightarrow> string" where
  "ctx_debug_graphviz_same_ctx_lists_with_globals ctx_key ctx_label globals_label node_label node_attrs ks ps es cs =
     ctx_debug_graphviz_with_globals ctx_key ctx_label globals_label node_label node_attrs ks
       (ctx_debug_same_ctx_nodes ks ps)
       (ctx_debug_same_ctx_intra_edges ks es)
       (ctx_debug_same_ctx_call_edges ks es)
       (ctx_debug_same_ctx_return_edges ks cs)"

definition ctx_debug_graphviz_same_ctx_cfg_with_globals ::
  "('ctx \<Rightarrow> string) \<Rightarrow> ('ctx \<Rightarrow> string) \<Rightarrow> ('ctx \<Rightarrow> string) \<Rightarrow>
   (pp * 'ctx \<Rightarrow> string) \<Rightarrow> (pp \<Rightarrow> string) \<Rightarrow> 'ctx list \<Rightarrow> cfg \<Rightarrow> string" where
  "ctx_debug_graphviz_same_ctx_cfg_with_globals ctx_key ctx_label globals_label node_label node_attrs ks g =
     ctx_debug_graphviz_same_ctx_lists_with_globals ctx_key ctx_label globals_label node_label node_attrs ks
       (sorted_list_of_set (nodes g)) (cfg_edges_list g) (cfg_combines_list g)"

definition ctx_debug_graphviz_same_ctx_cfg ::
  "('ctx \<Rightarrow> string) \<Rightarrow> ('ctx \<Rightarrow> string) \<Rightarrow> (pp * 'ctx \<Rightarrow> string) \<Rightarrow> (pp \<Rightarrow> string) \<Rightarrow>
   'ctx list \<Rightarrow> cfg \<Rightarrow> string" where
  "ctx_debug_graphviz_same_ctx_cfg ctx_key ctx_label node_label node_attrs ks g =
     ctx_debug_graphviz_same_ctx_lists ctx_key ctx_label node_label node_attrs ks
       (sorted_list_of_set (nodes g)) (cfg_edges_list g) (cfg_combines_list g)"

definition ctx_debug_show_key :: "'ctx::show_val \<Rightarrow> string" where
  "ctx_debug_show_key k = show_val k"

definition ctx_debug_show_label :: "string \<Rightarrow> 'ctx::show_val \<Rightarrow> string" where
  "ctx_debug_show_label name k = ''ctx '' @ name @ ''='' @ show_val k"

definition ctx_debug_graphviz_same_ctx_cfg_show ::
  "string \<Rightarrow> (pp * 'ctx::show_val \<Rightarrow> string) \<Rightarrow> (pp \<Rightarrow> string) \<Rightarrow> 'ctx list \<Rightarrow> cfg \<Rightarrow> string" where
  "ctx_debug_graphviz_same_ctx_cfg_show name node_label node_attrs ks g =
     ctx_debug_graphviz_same_ctx_cfg ctx_debug_show_key (ctx_debug_show_label name)
       node_label node_attrs ks g"

definition ctx_debug_show_label_lines :: "('ctx::show_val \<Rightarrow> string list) \<Rightarrow> 'ctx \<Rightarrow> string" where
  "ctx_debug_show_label_lines lines k = join_gv_nl (lines k)"

definition ctx_debug_graphviz_same_ctx_cfg_show_lines ::
  "('ctx::show_val \<Rightarrow> string list) \<Rightarrow> (pp * 'ctx \<Rightarrow> string) \<Rightarrow> (pp \<Rightarrow> string) \<Rightarrow> 'ctx list \<Rightarrow> cfg \<Rightarrow> string" where
  "ctx_debug_graphviz_same_ctx_cfg_show_lines lines node_label node_attrs ks g =
     ctx_debug_graphviz_same_ctx_cfg ctx_debug_show_key (ctx_debug_show_label_lines lines)
       node_label node_attrs ks g"

fun ctx_debug_enter_sources :: "(pp * edge_action * pp) list \<Rightarrow> pp list" where
  "ctx_debug_enter_sources [] = []"
| "ctx_debug_enter_sources ((src, EA_Enter xs es', _) # es) = src # ctx_debug_enter_sources es"
| "ctx_debug_enter_sources (_ # es) = ctx_debug_enter_sources es"

definition ctx_debug_call_source_pps :: "cfg \<Rightarrow> pp list" where
  "ctx_debug_call_source_pps g = ctx_debug_enter_sources (cfg_edges_list g)"

definition ctx_debug_default_node_role :: "cfg \<Rightarrow> pp \<Rightarrow> string" where
  "ctx_debug_default_node_role g p =
     (if p = cfg_entry g then
        (if mem_pp p (ctx_debug_call_source_pps g)
         then ''program entry'' @ gv_nl @ ''call site''
         else ''program entry'')
      else if p = cfg_exit g then ''program exit''
      else if mem_pp p (proc_entry_pps_list g) then ''proc entry''
      else if mem_pp p (proc_exit_pps_list g) then ''proc exit''
      else if mem_pp p (ctx_debug_call_source_pps g) then ''call site''
      else [])"

definition ctx_debug_default_node_label :: "cfg \<Rightarrow> pp * 'ctx \<Rightarrow> string" where
  "ctx_debug_default_node_label g pc =
     (case pc of (p, k) \<Rightarrow> ''pp'' @ string_of_nat p @ gv_nl @ ctx_debug_default_node_role g p)"

text \<open>
  Generic per-node \<^emph>\<open>state\<close> label for the context-clustered renderer.  Any analysis whose
  solution stores a local state per \<open>(pp, ctx)\<close> gets node labels showing the abstract values ---
  \<open>var=value\<close> via \<^const>\<open>label_of_st\<close> on the domain's \<^class>\<open>show_val\<close> printer --- with no
  hand-written label.  \<open>cfg_local_vars\<close> auto-collects the program's local variables, so
  callers supply only the state lookup \<open>loc :: (pp \<times> 'ctx) \<Rightarrow> 'a st\<close> (typically
  \<open>\<lambda>(p, k). snd solution (Inl (p, k))\<close>).
\<close>

definition cfg_local_vars :: "cfg \<Rightarrow> vname list" where
  "cfg_local_vars g =
     filter (\<lambda>x. \<not> is_global x)
       (remdups (concat (map (\<lambda>(_, a, _). vars_of_action a) (cfg_edges_list g))))"

definition ctx_debug_state_node_label ::
  "cfg \<Rightarrow> vname list \<Rightarrow>
   ((pp \<times> 'ctx) \<Rightarrow> ('a::{show_val, bounded_semilattice_sup_bot}) st) \<Rightarrow> pp \<times> 'ctx \<Rightarrow> string" where
  "ctx_debug_state_node_label g vars loc pc =
     (case pc of (p, k) \<Rightarrow>
        ''pp'' @ string_of_nat p
        @ (let r = ctx_debug_default_node_role g p in if r = [] then [] else gv_nl @ r)
        @ (let l = label_of_st show_val vars (loc pc) in if l = [] then [] else gv_nl @ l))"

definition ctx_debug_state_node_label_auto ::
  "cfg \<Rightarrow> ((pp \<times> 'ctx) \<Rightarrow> ('a::{show_val, bounded_semilattice_sup_bot}) st) \<Rightarrow> pp \<times> 'ctx \<Rightarrow> string" where
  "ctx_debug_state_node_label_auto g loc = ctx_debug_state_node_label g (cfg_local_vars g) loc"

definition ctx_debug_default_node_attrs :: "cfg \<Rightarrow> pp \<Rightarrow> string" where
  "ctx_debug_default_node_attrs g p =
     (if p = cfg_entry g then ''shape=doublecircle,color=green,style=filled,fillcolor=lightyellow''
      else if p = cfg_exit g then ''shape=doublecircle,color=red,style=filled,fillcolor=mistyrose''
      else if mem_pp p (proc_entry_pps_list g) then ''shape=box,color=green,style=filled,fillcolor=lightgreen''
      else if mem_pp p (proc_exit_pps_list g) then ''shape=box,color=red,style=filled,fillcolor=lightgreen''
      else ''shape=box,style=filled,fillcolor=lightgreen'')"

definition ctx_debug_graphviz_same_ctx_cfg_show_default ::
  "string \<Rightarrow> 'ctx::show_val list \<Rightarrow> cfg \<Rightarrow> string" where
  "ctx_debug_graphviz_same_ctx_cfg_show_default name ks g =
     ctx_debug_graphviz_same_ctx_cfg_show name
       (ctx_debug_default_node_label g) (ctx_debug_default_node_attrs g) ks g"

definition ctx_debug_graphviz_same_ctx_cfg_show_lines_default ::
  "('ctx::show_val \<Rightarrow> string list) \<Rightarrow> 'ctx list \<Rightarrow> cfg \<Rightarrow> string" where
  "ctx_debug_graphviz_same_ctx_cfg_show_lines_default lines ks g =
     ctx_debug_graphviz_same_ctx_cfg_show_lines lines
       (ctx_debug_default_node_label g) (ctx_debug_default_node_attrs g) ks g"

definition ctx_debug_graphviz_same_ctx_cfg_show_globals_default ::
  "('ctx::show_val \<Rightarrow> string list) \<Rightarrow> ('ctx \<Rightarrow> string list) \<Rightarrow> 'ctx list \<Rightarrow> cfg \<Rightarrow> string" where
  "ctx_debug_graphviz_same_ctx_cfg_show_globals_default ctx_lines globals_lines ks g =
     ctx_debug_graphviz_same_ctx_cfg_with_globals
       ctx_debug_show_key (ctx_debug_show_label_lines ctx_lines) (ctx_debug_show_label_lines globals_lines)
       (ctx_debug_default_node_label g) (ctx_debug_default_node_attrs g) ks g"

subsection \<open>Whole-program convenience wrappers\<close>

text \<open>
  The @{text "annotated_dot_of_prog"} family bundles
  @{const compile_prog}, @{const compile_prog_regions}, region-scoped
  node labels, and @{const graphviz_of_analysis_prog} into a single call.
  @{const String.implode} is applied so the code generator returns a
  native ML @{text "string"} -- no @{text "char list"} decoder needed.
\<close>

definition annotated_dot_of_prog ::
    "proc_table \<Rightarrow> pname list \<Rightarrow> com \<Rightarrow>
     (pp + unit \<Rightarrow> 'a::{show_val, bounded_semilattice_sup_bot} st) \<Rightarrow> string" where
  "annotated_dot_of_prog \<Pi> ps main sol =
     graphviz_of_analysis_prog sol \<Pi> ps main"

definition annotated_dot_of_prog_lit ::
    "proc_table \<Rightarrow> pname list \<Rightarrow> com \<Rightarrow>
     (pp + unit \<Rightarrow> 'a::{show_val, bounded_semilattice_sup_bot} st) \<Rightarrow> String.literal" where
  "annotated_dot_of_prog_lit \<Pi> ps main sol =
     String.implode (annotated_dot_of_prog \<Pi> ps main sol)"

definition plain_dot_of_prog_lit :: "proc_table \<Rightarrow> pname list \<Rightarrow> com \<Rightarrow> String.literal" where
  "plain_dot_of_prog_lit \<Pi> ps main =
     String.implode
       (to_graphviz_labeled_prog pp_plain_label \<Pi> ps main
          (compile_prog_regions \<Pi> ps main)
          (proc_entry_pps_prog \<Pi> ps main)
          (proc_exit_pps_prog \<Pi> ps main))"

section \<open>Generic context-annotated renderer\<close>

text \<open>
  A renderer for a \<^emph>\<open>context-sensitive\<close> solution: one Graphviz cluster per context, each
  node annotated with the abstract state that context assigns it.  Where the whole-program
  \<open>sign_annotated_dot_prog_lit\<close> draws the context-\<^emph>\<open>insensitive\<close> CFG (one copy of each
  procedure), this draws the per-context copies a context-sensitive solution actually holds.

  It is generic over the node type \<^typ>\<open>'v\<close>, the context type \<^typ>\<open>'ctx\<close>, and the way each is
  shown, taking the graph as explicit node and labelled-edge lists.  The caller supplies:
  \<^item> \<open>vid\<close> --- a node identifier (Graphviz-safe token);
  \<^item> \<open>nlab\<close> --- the annotation lines for a node under a context (already newline-joined, e.g.
    via \<^const>\<open>label_of_st\<close> on a solution \<open>(v, k) \<mapsto> state\<close>);
  \<^item> \<open>ckey\<close> --- a per-context token that keeps the cluster and its node ids distinct;
  \<^item> \<open>clabel\<close> --- the cluster header text.
\<close>

definition ctx_annot_node ::
  "('v \<Rightarrow> string) \<Rightarrow> ('v \<Rightarrow> 'ctx \<Rightarrow> string) \<Rightarrow> string \<Rightarrow> 'ctx \<Rightarrow> 'v \<Rightarrow> string" where
  "ctx_annot_node vid nlab ck k v =
     ''    '' @ ck @ ''_'' @ vid v @ '' [label=\"'' @ vid v @ gv_nl @ nlab v k @ ''\"];'' @ [CHR 0x0A]"

definition ctx_annot_edge ::
  "('v \<Rightarrow> string) \<Rightarrow> string \<Rightarrow> ('v \<times> 'v \<times> string) \<Rightarrow> string" where
  "ctx_annot_edge vid ck e =
     (case e of (a, b, l) \<Rightarrow>
        ''    '' @ ck @ ''_'' @ vid a @ '' -> '' @ ck @ ''_'' @ vid b
          @ '' [label=\"'' @ l @ ''\"];'' @ [CHR 0x0A])"

definition ctx_annot_cluster ::
  "('v \<Rightarrow> string) \<Rightarrow> ('v \<Rightarrow> 'ctx \<Rightarrow> string) \<Rightarrow> ('ctx \<Rightarrow> string) \<Rightarrow> ('ctx \<Rightarrow> string)
     \<Rightarrow> 'v list \<Rightarrow> ('v \<times> 'v \<times> string) list \<Rightarrow> 'ctx \<Rightarrow> string" where
  "ctx_annot_cluster vid nlab ckey clabel ns es k =
     ''  subgraph cluster_'' @ ckey k @ '' {'' @ [CHR 0x0A]
       @ ''    label=\"'' @ clabel k @ ''\"; color=blue;'' @ [CHR 0x0A]
       @ concat (map (ctx_annot_node vid nlab (ckey k) k) ns)
       @ concat (map (ctx_annot_edge vid (ckey k)) es)
       @ ''  }'' @ [CHR 0x0A]"

definition ctx_annotated_graphviz ::
  "('v \<Rightarrow> string) \<Rightarrow> ('v \<Rightarrow> 'ctx \<Rightarrow> string) \<Rightarrow> ('ctx \<Rightarrow> string) \<Rightarrow> ('ctx \<Rightarrow> string)
     \<Rightarrow> 'v list \<Rightarrow> ('v \<times> 'v \<times> string) list \<Rightarrow> 'ctx list \<Rightarrow> string" where
  "ctx_annotated_graphviz vid nlab ckey clabel ns es ks =
     ''digraph CtxCFG {'' @ [CHR 0x0A] @ ''  rankdir=TB;'' @ [CHR 0x0A]
       @ concat (map (ctx_annot_cluster vid nlab ckey clabel ns es) ks)
       @ ''}'' @ [CHR 0x0A]"

section \<open>Generic context-expanded analysis graph\<close>

text \<open>
  The analysis graph is independent of DOT.  It records contextual local nodes,
  shared global nodes, and the semantic role of every routed edge.  The builder
  consumes the same routing function as the equation generator; it never
  reconstructs contexts from labels or example-specific values.
\<close>

datatype ('ctx, 'g) analysis_cluster =
    ContextCluster string 'ctx
  | GlobalCluster

datatype ('ctx, 'g) analysis_node =
    LocalNode pp 'ctx
  | GlobalNode 'g

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

fun graphviz_owner_of :: "graphviz_region list \<Rightarrow> pp \<Rightarrow> string" where
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

definition owner_assigned_vars ::
  "cfg \<Rightarrow> (pp \<Rightarrow> string) \<Rightarrow> string \<Rightarrow> vname list" where
  "owner_assigned_vars g point_owner owner =
    remdups (concat (map (\<lambda>e. case e of (u, a, v) \<Rightarrow>
      if point_owner u = owner then graphviz_action_defs a else []) (cfg_edges_list g)))"

definition compiled_procedure_scope ::
  "proc_table \<Rightarrow> pname list \<Rightarrow> com \<Rightarrow> cfg \<Rightarrow> pp \<Rightarrow> procedure_scope" where
  "compiled_procedure_scope \<Pi> ps main g p =
    (let owner = compiled_owner_of \<Pi> ps main p;
         decl = \<Pi> owner;
         fs = if owner = ''main'' then [] else
           (case decl of None \<Rightarrow> [] | Some d \<Rightarrow> formals d);
         ret = if owner = ''main'' then None else
           (case decl of None \<Rightarrow> None
            | Some d \<Rightarrow> case result d of None \<Rightarrow> None | Some _ \<Rightarrow> Some ret_var);
         ls = filter (\<lambda>x. x \<notin> set fs \<and> x \<noteq> ret_var)
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

definition analysis_global_nodes ::
  "('ctx, 'g, 'a, 'd) analysis_graph_config \<Rightarrow> 'g list
    \<Rightarrow> ('ctx, 'g) analysis_node list" where
  "analysis_global_nodes cfg keys =
    map GlobalNode (filter (visible_global cfg) (remdups keys))"

definition analysis_global_cluster ::
  "('ctx, 'g) analysis_node list \<Rightarrow> ('ctx, 'g) analysis_cluster list" where
  "analysis_global_cluster ns =
    (if list_ex (\<lambda>n. case n of GlobalNode _ \<Rightarrow> True | _ \<Rightarrow> False) ns
     then [GlobalCluster] else [])"

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
         globals = analysis_global_nodes cfg global_keys;
         ns = locals @ globals
     in (analysis_context_clusters cfg covered @ analysis_global_cluster ns,
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
    | GlobalNode k \<Rightarrow> ''global_'' @ string_of_nat (analysis_node_position ns n))"

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
    | ContextCluster owner ctx \<Rightarrow> ''cluster_ctx_''
        @ string_of_nat (analysis_cluster_position clusters cluster))"

definition analysis_nodes_in_cluster ::
  "('ctx, 'g, 'a, 'd) analysis_graph_config \<Rightarrow> ('ctx, 'g) analysis_cluster
    \<Rightarrow> ('ctx, 'g) analysis_node list \<Rightarrow> ('ctx, 'g) analysis_node list" where
  "analysis_nodes_in_cluster cfg cluster ns =
    sort_key (\<lambda>n. case n of LocalNode p ctx \<Rightarrow> p | GlobalNode k \<Rightarrow> 0)
      (filter (\<lambda>n. case (cluster, n) of
        (ContextCluster owner ctx, LocalNode p ctx') \<Rightarrow> owner = owner_of cfg p \<and> ctx = ctx'
      | (GlobalCluster, GlobalNode _) \<Rightarrow> True
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
        (show_global_key cfg k # show_global cfg k (globals_to_show cfg) (sol (Inr k))))"

definition analysis_node_attrs :: "cfg \<Rightarrow> ('ctx, 'g) analysis_node \<Rightarrow> string" where
  "analysis_node_attrs g n =
    (case n of
      LocalNode p _ \<Rightarrow> ctx_debug_default_node_attrs g p
    | GlobalNode _ \<Rightarrow> ''shape=note,width=2.2,fixedsize=false'')"

fun enter_bindings :: "vname list \<Rightarrow> aexp list \<Rightarrow> string list" where
  "enter_bindings [] _ = []"
| "enter_bindings _ [] = []"
| "enter_bindings (x # xs) (e # es) =
    (x @ '' := '' @ string_of_aexp e) # enter_bindings xs es"

definition enter_action_label :: "edge_action \<Rightarrow> string" where
  "enter_action_label a =
    (case a of EA_Enter xs es \<Rightarrow> ''enter'' @ gv_nl @ join_gv_nl (enter_bindings xs es)
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
    | GlobalCluster \<Rightarrow> ''Shared globals'')"

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
          @ analysis_node_attrs g n @ '',label='' @ dq @ contextual_node_label cfg g sol n
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

end

