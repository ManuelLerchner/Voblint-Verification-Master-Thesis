theory Analysis_GraphViz
  imports
    "Voblint_CFG.VIMP_Proc_to_CFG"
    "Voblint_VIMP.VIMP_Source_Print"
    Voblint_Core.TD_Side_CFG
    Voblint_Core.Exec_St
    Voblint_Core.Abstract_Domain
    Voblint_Core.Abstract_Checks
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
| "string_of_action (EA_Assign x a) = String.explode x @ '' := '' @ string_of_aexp a"
| "string_of_action (EA_Special sc x) = String.explode x @ '' := random()''"
| "string_of_action (EA_Assume b) = ''['' @ string_of_bexp b @ '']''"
| "string_of_action (EA_AssumeNot b) = ''!['' @ string_of_bexp b @ '']''"
| "string_of_action (EA_Ret None p) = ''return''"
| "string_of_action (EA_Ret (Some e) p) =
    ''return '' @ string_of_aexp e"
| "string_of_action (EA_Check cnd) = ''check('' @ string_of_bexp cnd @ '')''"

fun string_of_call_action :: "call_action \<Rightarrow> string" where
  "string_of_call_action (CallEdge None fs es) =
    ''call('' @ concat (map string_of_aexp es) @ '')''"
| "string_of_call_action (CallEdge (Some x) fs es) =
    String.explode x @ '' := call('' @ concat (map string_of_aexp es) @ '')''"

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

text \<open>
  A line not terminated by its own \<^term>\<open>CHR 0x0A\<close> never gets the
  \<open><BR ALIGN="LEFT"/>\<close> \<^const>\<open>graphviz_html_text\<close> emits for embedded
  newlines, and Graphviz then renders that final line centered instead of
  inheriting the cell's own \<open>ALIGN="LEFT"\<close> --- a documented HTML-label
  quirk, not a property of well-formed DOT. Appending exactly one trailing
  newline when \<open>src\<close> lacks one, idempotent when it already has one, gives
  every line including the last its own \<open>BR\<close> and so its own alignment.
\<close>

definition ensure_trailing_nl :: "string \<Rightarrow> string" where
  "ensure_trailing_nl src =
    (case rev src of
       [] \<Rightarrow> nl
     | (ch # _) \<Rightarrow> if ch = CHR 0x0A then src else src @ nl)"

definition source_html_label :: "string \<Rightarrow> string" where
  "source_html_label src =
    ''<<TABLE BORDER='' @ dq @ ''1'' @ dq @ '' CELLBORDER='' @ dq @ ''0'' @ dq    @ '' CELLPADDING='' @ dq @ ''8'' @ dq
    @ ''><TR><TD ALIGN='' @ dq @ ''LEFT'' @ dq @ '' WIDTH='' @ dq @ ''260'' @ dq
    @ '' FIXEDSIZE='' @ dq @ ''FALSE'' @ dq
    @ ''><FONT FACE='' @ dq @ ''Menlo'' @ dq @ '' POINT-SIZE='' @ dq @ ''10'' @ dq
    @ ''>'' @ graphviz_html_text (ensure_trailing_nl src) @ ''</FONT></TD></TR></TABLE>>''"

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
  | EnterEdge (aek_enter_proc: string) (aek_call: call_action)
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

text \<open>
  Shared status-to-style mapping for a compiled \<^verbatim>\<open>__voblint_check(...)\<close>
  condition, given its executable \<^typ>\<open>check_result\<close> classification.
  Domain-independent (only \<^typ>\<open>check_result\<close> and \<^typ>\<open>bexp\<close>), so every
  domain's check-discharge example renders proof status through this one
  mapping instead of restating it. \<^term>\<open>Check_Proved\<close> renders dark green,
  \<^term>\<open>Check_Refuted\<close> red, \<^term>\<open>Check_Unknown\<close> grey.
\<close>

definition check_result_annotation :: "check_result \<Rightarrow> bexp \<Rightarrow> graphviz_node_annotation" where
  "check_result_annotation res cnd =
     (case res of
        Check_Proved \<Rightarrow>
          Node_Annotation (''check '' @ string_of_bexp cnd)
            ''shape=box,style=filled,fillcolor=darkgreen,fontcolor=white''
      | Check_Unknown \<Rightarrow>
          Node_Annotation (''check '' @ string_of_bexp cnd @ '' [unknown]'')
            ''shape=box,style=filled,fillcolor=gray70''
      | Check_Refuted \<Rightarrow>
          Node_Annotation (''check '' @ string_of_bexp cnd @ '' [REFUTED]'')
            ''shape=box,style=filled,fillcolor=red,fontcolor=white'')"

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
  "proc_table \<Rightarrow> pname list \<Rightarrow> pname \<Rightarrow> com \<Rightarrow> pp \<Rightarrow> pname" where
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
| "graphviz_action_defs (EA_Special sc x) = [x]"
| "graphviz_action_defs _ = []"

definition cfg_assigned_vars :: "cfg \<Rightarrow> vname list" where
  "cfg_assigned_vars g =
    remdups
      (concat (map (\<lambda>(_, a, _). graphviz_action_defs a) (cfg_intra_list g)) @
       concat (map (\<lambda>(_, ca, _, _).
         case ca of CallEdge None _ _ \<Rightarrow> [] | CallEdge (Some x) _ _ \<Rightarrow> [x])
         (cfg_calls_list g)))"

definition compiled_global_vars :: "(vname \<Rightarrow> bool) \<Rightarrow> cfg \<Rightarrow> vname list" where
  "compiled_global_vars gs g = filter gs (cfg_assigned_vars g)"

definition owner_assigned_vars ::
  "cfg \<Rightarrow> (pp \<Rightarrow> pname) \<Rightarrow> pname \<Rightarrow> vname list" where
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
  "(vname \<Rightarrow> bool) \<Rightarrow> proc_table \<Rightarrow> pname list \<Rightarrow> pname \<Rightarrow> com \<Rightarrow> cfg \<Rightarrow> pp \<Rightarrow> procedure_scope" where
  "compiled_procedure_scope gs \<Pi> ps mnm main g p =
    (let owner = compiled_owner_of \<Pi> ps mnm main p;
         decl = \<Pi> owner;
         fs = if owner = mnm then [] else
           (case decl of None \<Rightarrow> [] | Some d \<Rightarrow> formals d);
         ret = if owner = mnm then None else Some ret_var;
         ls = filter (\<lambda>x. x \<notin> set fs \<and> x \<noteq> ret_var \<and> \<not> gs x)
           (owner_assigned_vars g (compiled_owner_of \<Pi> ps mnm main) owner)
     in \<lparr>scope_formals = fs, scope_locals = ls, scope_return_slot = ret\<rparr>)"

text \<open>
  The classic abs-state route: any \<^class>\<open>show_val\<close> instance renders its compiled
  program the same way -- the domain enters only through \<open>is_top_val\<close> (skip an
  untouched return slot) and \<^const>\<open>show_val\<close> (format a value); everything else reads
  the compiler's own scope/owner/global bookkeeping. A per-domain config is this
  specialized at its abstract type, with its own concrete top test.

  \<open>is_top_val\<close> is an explicit parameter, not \<^const>\<open>is_top\<close> from \<^class>\<open>sound_domain\<close>:
  code generation for one class operation materializes that class's whole dictionary,
  and \<^class>\<open>sound_domain\<close>'s \<^const>\<open>gamma\<close> has no executable code equation for every
  instance (an interval domain's, for instance, is a set comprehension over \<^typ>\<open>int\<close>,
  which is not of sort \<open>enum\<close>). Taking the top test as a plain function keeps this
  definition's code generation independent of \<^class>\<open>sound_domain\<close> entirely.
\<close>
definition compiled_domain_graph_config ::
  "(vname \<Rightarrow> bool) \<Rightarrow> proc_table \<Rightarrow> pname list \<Rightarrow> pname \<Rightarrow> com \<Rightarrow> ('a::show_val \<Rightarrow> bool) \<Rightarrow>
    (unit, unit, 'a abs_state, 'a abs_state) analysis_graph_config"
where
  "compiled_domain_graph_config gs \<Pi> ps mnm main is_top_val =
    \<lparr> local_of = id,
      route = (\<lambda>_ _ _ _. ()),
      show_context = (\<lambda>_. ''''),
      locals_for_pp = (\<lambda>p.
        let sc = compiled_procedure_scope gs \<Pi> ps mnm main (compile_prog \<Pi> ps mnm main) p
        in scope_formals sc @ scope_locals sc),
      return_slot_for_pp = (\<lambda>p.
        scope_return_slot (compiled_procedure_scope gs \<Pi> ps mnm main
          (compile_prog \<Pi> ps mnm main) p)),
      globals_to_show = compiled_global_vars gs (compile_prog \<Pi> ps mnm main),
      show_local = (\<lambda>_ _ vars s.
        map (\<lambda>x. String.explode x @ ''='' @ show_val (s x)) vars),
      format_return = (\<lambda>_ _ ret s.
        if is_top_val (s ret) then [] else [''ret='' @ show_val (s ret)]),
      show_global = (\<lambda>_ vars s.
        map (\<lambda>x. String.explode x @ ''='' @ show_val (s x)) vars),
      show_global_key = (\<lambda>_. ''Globals''),
      is_shared_global = (\<lambda>_. True),
      show_internal_globals = False,
      owner_of = String.explode o compiled_owner_of \<Pi> ps mnm main,
      cluster_label = (\<lambda>owner _. owner),
      source_text = Some (pretty_string_of_program \<Pi> ps main []),
      node_annotation = (\<lambda>_. None)
    \<rparr>"


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
| "string_of_cfg_node (FunctionEntry p) = ''entry_'' @ String.explode p"
| "string_of_cfg_node (FunctionResult p) = ''result_'' @ String.explode p"

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
      FunctionEntry owner \<Rightarrow> ''entry_'' @ String.explode owner
    | FunctionResult owner \<Rightarrow> ''exit_'' @ String.explode owner
    | Statement _ \<Rightarrow> string_of_cfg_node p)"

text \<open>
  The inverse of \<^const>\<open>join_gv_nl\<close>: splits a string joined with the
  literal \<open>\n\<close> separator back into its original lines. A caller with
  multi-line content to attach as one \<^typ>\<open>graphviz_node_annotation\<close>
  (a single flat \<^const>\<open>annotation_label\<close> string, by design, so the
  renderer stays agnostic to what any particular annotation means) already
  joins it with \<^const>\<open>join_gv_nl\<close> --- the same convention the per-node
  label-line builder below uses. DOT rendering consumes that joined form
  directly; the canonical snapshot needs the lines apart again, hence this
  being used only there.
\<close>

text \<open>
  Matches \<^const>\<open>graphviz_html_text\<close>'s idiom of comparing characters with
  \<open>=\<close> rather than pattern-matching a literal \<open>CHR\<close> value on a \<open>fun\<close>
  equation's left-hand side --- \<open>HOL-Library.Code_Abstract_Char\<close> (pulled
  in for this session's OCaml code generation) represents \<^typ>\<open>char\<close>
  abstractly for the code generator, which then rejects a literal-\<open>CHR\<close>
  pattern as "not a constructor". An equality test in the body has no such
  restriction.
\<close>

fun split_gv_nl_acc :: "string \<Rightarrow> string \<Rightarrow> string list" where
  "split_gv_nl_acc acc [] = [rev acc]"
| "split_gv_nl_acc acc [ch] = [rev (ch # acc)]"
| "split_gv_nl_acc acc (ch1 # ch2 # rest) =
    (if ch1 = CHR 0x5C \<and> ch2 = CHR 0x6E
     then rev acc # split_gv_nl_acc [] rest
     else split_gv_nl_acc (ch1 # acc) (ch2 # rest))"

definition split_gv_nl :: "string \<Rightarrow> string list" where
  "split_gv_nl s = split_gv_nl_acc [] s"

text \<open>
  The per-node label as a line list, before \<^const>\<open>join_gv_nl\<close> escapes it
  into one DOT-attribute string. Factored out so a non-DOT renderer (the
  canonical regression snapshot, below) can walk the same lines without
  re-deriving them from escaped DOT text.
\<close>

definition contextual_node_label_lines ::
  "('ctx, 'g, 'a, 'd) analysis_graph_config \<Rightarrow> cfg
    \<Rightarrow> (pp \<times> 'ctx + 'g \<Rightarrow> 'a) \<Rightarrow> ('ctx, 'g) analysis_node \<Rightarrow> string list" where
  "contextual_node_label_lines cfg g sol n =
    (case n of
      LocalNode p ctx \<Rightarrow>
        graphviz_point_label g p #
          show_local cfg p ctx (locals_for_pp cfg p)
            (local_of cfg (sol (Inl (p, ctx))))
          @ (case return_slot_for_pp cfg p of None \<Rightarrow> []
             | Some ret \<Rightarrow> format_return cfg p ctx ret
                 (local_of cfg (sol (Inl (p, ctx)))))
          @ (case node_annotation cfg p of
              None \<Rightarrow> []
            | Some ann \<Rightarrow>
                if annotation_label ann = '''' then [] else split_gv_nl (annotation_label ann))
    | GlobalNode k \<Rightarrow>
        show_global_key cfg k # show_global cfg k (globals_to_show cfg) (sol (Inr k))
    | SourceNode src \<Rightarrow> [src])"

definition contextual_node_label ::
  "('ctx, 'g, 'a, 'd) analysis_graph_config \<Rightarrow> cfg
    \<Rightarrow> (pp \<times> 'ctx + 'g \<Rightarrow> 'a) \<Rightarrow> ('ctx, 'g) analysis_node \<Rightarrow> string" where
  "contextual_node_label cfg g sol n = join_gv_nl (contextual_node_label_lines cfg g sol n)"

definition analysis_node_attrs ::
  "('ctx, 'g, 'a, 'd) analysis_graph_config \<Rightarrow> cfg \<Rightarrow> ('ctx, 'g) analysis_node \<Rightarrow> string" where
  "analysis_node_attrs cfg g n =
    (case n of
      LocalNode p _ \<Rightarrow>
        (case node_annotation cfg p of
          Some ann \<Rightarrow> annotation_style ann
        | None \<Rightarrow>
            if p = cfg_entry g then ''shape=doublecircle,color=green,style=filled,fillcolor=lightyellow''
            else if p = graphviz_exit g then ''shape=doublecircle,color=gray40,style=filled,fillcolor=lightgray''
            else if p \<in> set (proc_entry_pps_list g) then ''shape=doublecircle,color=green,style=filled,fillcolor=lightyellow''
            else if p \<in> set (proc_exit_pps_list g) then ''shape=doublecircle,color=gray40,style=filled,fillcolor=lightgray''
            else ''shape=box,style=filled,fillcolor=lightgreen'')
    | GlobalNode _ \<Rightarrow> ''shape=note,width=2.2,fixedsize=false''
    | SourceNode _ \<Rightarrow> ''shape=plain'')" 

fun enter_bindings :: "vname list \<Rightarrow> aexp list \<Rightarrow> string list" where
  "enter_bindings [] _ = []"
| "enter_bindings _ [] = []"
| "enter_bindings (x # xs) (e # es) =
    (String.explode x @ '' := '' @ string_of_aexp e) # enter_bindings xs es"

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
             (Some x, Some r) \<Rightarrow> ''resume / '' @ String.explode x @ '' := '' @ String.explode r
           | (Some x, None) \<Rightarrow> ''resume / '' @ String.explode x
           | (None, _) \<Rightarrow> ''resume'')
        @ dq
    | CallToReturnEdge callee \<Rightarrow> ''style=dotted,color=gray40,constraint=false,label='' @ dq
        @ ''resume-site'' @ dq
    | GlobalReadEdge \<Rightarrow> ''style=dotted,color=gray,label='' @ dq @ ''read global'' @ dq
    | GlobalWriteEdge \<Rightarrow> ''style=dotted,color=gray,label='' @ dq @ ''write global'' @ dq)"

text \<open>
  A DOT-independent counterpart to \<^const>\<open>analysis_edge_attrs\<close>: the same
  semantic content (call arguments, combine-slot naming, edge role) without
  DOT's own color/style/\<open>label=\<close> syntax, for the canonical regression
  snapshot below.
\<close>

definition canonical_edge_kind_text :: "cfg \<Rightarrow> analysis_edge_kind \<Rightarrow> string" where
  "canonical_edge_kind_text g kind =
    (case kind of
      IntraEdge a \<Rightarrow> source_action_label g a
    | EnterEdge callee a \<Rightarrow> ''enter '' @ callee @ ''(''
        @ (case a of CallEdge _ _ es \<Rightarrow> join_source '', '' (map string_of_aexp es)) @ '')''
    | CombineEdge call dst ret \<Rightarrow> ''combine''
        @ (case (dst, ret) of
             (Some x, Some r) \<Rightarrow> '' '' @ String.explode x @ '' := '' @ String.explode r
           | (Some x, None) \<Rightarrow> '' '' @ String.explode x
           | (None, _) \<Rightarrow> '''')
    | CallToReturnEdge callee \<Rightarrow> ''call-to-return '' @ String.explode callee
    | GlobalReadEdge \<Rightarrow> ''read global''
    | GlobalWriteEdge \<Rightarrow> ''write global'')"

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

section \<open>Canonical, DOT-independent regression snapshot\<close>

text \<open>
  A deterministic textual snapshot of an \<^type>\<open>analysis_graph\<close>, for
  regression fixtures: unlike \<^const>\<open>analysis_graph_to_dot\<close>, it carries no
  GraphViz styling/color/shape syntax, so a fixture only regresses on the
  graph's actual structure and content (clusters, node labels, check
  verdicts, abstract states, edge roles) and not on presentation choices
  that \<^const>\<open>analysis_graph_to_dot\<close>'s own DOT-specific tests already
  cover. Node/cluster identifiers reuse \<^const>\<open>analysis_node_id\<close>/
  \<^const>\<open>analysis_cluster_id\<close> rather than a second numbering scheme, so a
  snapshot and its DOT rendering stay cross-referenceable. Ordering is the
  same deterministic insertion order \<^const>\<open>build_analysis_graph\<close> already
  establishes (list position, not a fresh sort) --- sorting here would
  paper over a real ordering regression in graph construction rather than
  catch it. The one omission is \<^const>\<open>SourceNode\<close>/\<^const>\<open>SourceCluster\<close>:
  the embedded pretty-printed program text is presentation convenience
  (the \<open>.vimp\<close> fixture already has that text), not graph structure.
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
      owner_of = String.explode o compiled_owner_of \<Pi> ps mnm main,
      cluster_label = (\<lambda>owner _. owner),
      source_text = Some (pretty_string_of_program \<Pi> ps main []),
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

definition raw_cfg_canonical_text ::
  "proc_table \<Rightarrow> pname list \<Rightarrow> pname \<Rightarrow> com \<Rightarrow> (pp \<Rightarrow> graphviz_node_annotation option) \<Rightarrow> string" where
  "raw_cfg_canonical_text \<Pi> ps mnm main annotate =
    (let g = compile_prog \<Pi> ps mnm main;
         cfg = raw_cfg_graph_config \<Pi> ps mnm main annotate;
         domain = contextual_graph_domain g (\<lambda>_. [()])
     in contextual_analysis_canonical_text cfg g domain (\<lambda>_. ()))"

definition raw_cfg_canonical_text_lit ::
  "proc_table \<Rightarrow> pname list \<Rightarrow> pname \<Rightarrow> com \<Rightarrow> (pp \<Rightarrow> graphviz_node_annotation option)
    \<Rightarrow> String.literal" where
  "raw_cfg_canonical_text_lit \<Pi> ps mnm main annotate =
    String.implode (raw_cfg_canonical_text \<Pi> ps mnm main annotate)"

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
        string_of_cfg_node v @ '': '' @ string_of_bexp cnd @ ''  '' @ string_of_check_result res)"

definition string_of_check_report :: "check_report_entry list \<Rightarrow> string" where
  "string_of_check_report report =
     concat (map (\<lambda>entry. string_of_check_report_entry entry @ nl) report)"

section \<open>Report-driven GraphViz annotation\<close>

text \<open>
  The GraphViz counterpart of \<^const>\<open>string_of_check_report\<close>: looks up the
  report entry at a queried node and, if one exists, renders it through
  \<^const>\<open>check_result_annotation\<close>. This lets a caller's
  \<open>node_annotation\<close> hook consume a whole-program \<^const>\<open>classify_checks\<close>
  report directly instead of restating a manually maintained \<^typ>\<open>pp\<close>-to-
  \<^typ>\<open>bexp\<close> table --- the report already names every checked node once.
\<close>

definition check_report_node_annotation ::
    "check_report_entry list \<Rightarrow> pp \<Rightarrow> graphviz_node_annotation option" where
  "check_report_node_annotation report v =
     (case find (\<lambda>entry. fst entry = v) report of
        Some (_, cnd, res) \<Rightarrow> Some (check_result_annotation res cnd)
      | None \<Rightarrow> None)"

text \<open>
  A standalone DOT box listing every report entry, styled through the same
  \<^const>\<open>source_html_label\<close> table \<^const>\<open>raw_cfg_dot\<close> already uses for its
  source box --- one more read of the same \<^const>\<open>classify_checks\<close> report,
  not a second check representation.
\<close>

definition check_report_html_label :: "check_report_entry list \<Rightarrow> string" where
  "check_report_html_label report = source_html_label (string_of_check_report report)"

definition check_report_dot_cluster :: "check_report_entry list \<Rightarrow> string" where
  "check_report_dot_cluster report =
     ''  subgraph cluster_checks {'' @ nl
       @ ''    label='' @ dq @ ''Checks'' @ dq @ '';'' @ nl
       @ ''    style=rounded; color=gray70; penwidth=1;'' @ nl
       @ ''    checks [shape=plain,label='' @ check_report_html_label report @ ''];'' @ nl
       @ ''  }'' @ nl"

text \<open>Every \<^const>\<open>raw_cfg_dot\<close> output ends in the digraph's own closing
  brace and newline, on both its well-formed and its \<open>invalid_graph\<close>
  fallback path, so splicing one more subgraph in immediately before those
  final two characters is a total operation over any \<^const>\<open>raw_cfg_dot\<close>
  result, not a fragile parse of DOT syntax.\<close>

definition insert_dot_cluster_before_close :: "string \<Rightarrow> string \<Rightarrow> string" where
  "insert_dot_cluster_before_close extra dot =
     take (length dot - 2) dot @ extra @ drop (length dot - 2) dot"

definition raw_cfg_dot_with_report ::
    "proc_table \<Rightarrow> pname list \<Rightarrow> pname \<Rightarrow> com \<Rightarrow> (pp \<Rightarrow> graphviz_node_annotation option)
     \<Rightarrow> check_report_entry list \<Rightarrow> string" where
  "raw_cfg_dot_with_report \<Pi> ps mnm main annotate report =
     insert_dot_cluster_before_close (check_report_dot_cluster report)
       (raw_cfg_dot \<Pi> ps mnm main annotate)"

definition raw_cfg_dot_with_report_lit ::
    "proc_table \<Rightarrow> pname list \<Rightarrow> pname \<Rightarrow> com \<Rightarrow> (pp \<Rightarrow> graphviz_node_annotation option)
     \<Rightarrow> check_report_entry list \<Rightarrow> String.literal" where
  "raw_cfg_dot_with_report_lit \<Pi> ps mnm main annotate report =
     String.implode (raw_cfg_dot_with_report \<Pi> ps mnm main annotate report)"

end

