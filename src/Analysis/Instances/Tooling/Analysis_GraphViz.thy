theory Analysis_GraphViz
  imports
    "Voblint_CFG.VIMP_Proc_to_CFG"
    "Voblint_VIMP.VIMP_Source_Print"
    Voblint_Core.Exec_St
    Voblint_Core.Abstract_Domain
    Voblint_Core.Abstract_Checks
    Voblint_Core.Call_String_Context
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
| "string_of_action (EA_Assign x a) = String.explode x @ '' := '' @ string_of_exp 0 a"
| "string_of_action (EA_Special Nondet_Int x) =
    String.explode x @ '' := __voblint_nondet_int()''"
| "string_of_action (EA_Special (Min a b) x) =
    String.explode x @ '' := min('' @ string_of_exp 0 a @ '', '' @ string_of_exp 0 b @ '')''"
| "string_of_action (EA_Special (Max a b) x) =
    String.explode x @ '' := max('' @ string_of_exp 0 a @ '', '' @ string_of_exp 0 b @ '')''"
| "string_of_action (EA_Assume b) = ''['' @ string_of_exp 0 b @ '']''"
| "string_of_action (EA_AssumeNot b) = ''!['' @ string_of_exp 0 b @ '']''"
| "string_of_action (EA_Ret None p) = ''return''"
| "string_of_action (EA_Ret (Some e) p) =
    ''return '' @ string_of_exp 0 e"
| "string_of_action (EA_Check cnd) = ''check('' @ string_of_exp 0 cnd @ '')''"

fun string_of_call_action :: "call_action \<Rightarrow> string" where
  "string_of_call_action (CallEdge None fs es) =
    ''call('' @ concat (map (string_of_exp 0) es) @ '')''"
| "string_of_call_action (CallEdge (Some x) fs es) =
    String.explode x @ '' := call('' @ concat (map (string_of_exp 0) es) @ '')''"

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
  What a node annotation \<^emph>\<open>means\<close>, as a finite tag rather than as the DOT attributes that
  happen to draw it, so a non-DOT consumer reads the same finding without parsing style text.
\<close>

datatype node_status =
  NS_Plain | NS_Proved | NS_Refuted | NS_Unknown | NS_Unreachable | NS_Exit

text \<open>
  A node annotation is presentation metadata a caller attaches to one \<^typ>\<open>pp\<close>: an optional
  extra label line and a \<^typ>\<open>node_status\<close> that, when present, replaces this renderer's own
  node styling for that point. The renderer stays agnostic to which findings a caller
  overlays on the CFG --- it owns turning \<^const>\<open>Some\<close> into node attributes and
  \<^const>\<open>None\<close> into the existing entry/exit/default styling. The status-to-DOT mapping
  below is the one place those attributes are spelled out.
\<close>

datatype graphviz_node_annotation =
  Node_Annotation (annotation_label: string) (annotation_status: node_status)

definition no_annotations :: "pp \<Rightarrow> graphviz_node_annotation option" where
  "no_annotations _ = None"

text \<open>
  The single status-to-DOT mapping. \<^const>\<open>NS_Unreachable\<close> takes \<open>gray40\<close>, the grey the
  renderer gives its own exit nodes, and deliberately not the \<open>gray70\<close> an undecided check
  carries: ``nothing reaches this node'' and ``something reaches it and the abstraction
  could not decide'' are different findings and must not render alike.
\<close>

definition gv_style_of_status :: "node_status \<Rightarrow> string" where
  "gv_style_of_status status =
     (case status of
        NS_Plain \<Rightarrow> ''shape=box,style=filled,fillcolor=lightgreen''
      | NS_Proved \<Rightarrow> ''shape=box,style=filled,fillcolor=darkgreen,fontcolor=white''
      | NS_Refuted \<Rightarrow> ''shape=box,style=filled,fillcolor=red,fontcolor=white''
      | NS_Unknown \<Rightarrow> ''shape=box,style=filled,fillcolor=gray70''
      | NS_Unreachable \<Rightarrow> ''shape=box,style=filled,fillcolor=gray40,fontcolor=white''
      | NS_Exit \<Rightarrow> ''shape=doublecircle,color=gray40,style=filled,fillcolor=lightgray'')"

definition annotation_style :: "graphviz_node_annotation \<Rightarrow> string" where
  "annotation_style ann = gv_style_of_status (annotation_status ann)"

text \<open>
  Shared status mapping for a compiled \<^verbatim>\<open>__voblint_check(...)\<close>
  condition, given its executable \<^typ>\<open>check_result\<close> classification.
  Domain-independent (only \<^typ>\<open>check_result\<close> and \<^typ>\<open>exp\<close>), so every
  domain's check-discharge example renders proof status through this one
  mapping instead of restating it.
\<close>

definition check_result_annotation :: "check_result \<Rightarrow> exp \<Rightarrow> graphviz_node_annotation" where
  "check_result_annotation res cnd =
     (case res of
        Check_Proved \<Rightarrow>
          Node_Annotation (''check '' @ string_of_exp 0 cnd) NS_Proved
      | Check_Unknown \<Rightarrow>
          Node_Annotation (''check '' @ string_of_exp 0 cnd @ '' [unknown]'') NS_Unknown
      | Check_Refuted \<Rightarrow>
          Node_Annotation (''check '' @ string_of_exp 0 cnd @ '' [REFUTED]'') NS_Refuted)"

text \<open>
  \<open>route\<close> answers \<^const>\<open>None\<close> exactly when a call transition does not exist ---
  the caller is unreachable, or the callee frame it would enter is itself
  semantically empty --- never by returning a distinguished \<open>'ctx\<close> value as a
  sentinel. A real context can coincide with what a "no route" placeholder
  might otherwise look like (the empty list is a genuine root or
  zero-formal context for \<open>ivl list\<close>), so folding "no route" into the context
  type itself would risk exactly the false edge this type is designed to
  rule out: \<open>analysis_enter_edges\<close>/\<open>analysis_combine_edges\<close> below
  draw an edge only on \<^const>\<open>Some\<close>.
\<close>

record ('ctx, 'g, 'a, 'd) analysis_graph_config =
  local_of :: "'a \<Rightarrow> 'd"
  route :: "pp \<Rightarrow> 'ctx \<Rightarrow> call_action \<Rightarrow> 'd \<Rightarrow> 'ctx option"
  context_key :: "'ctx \<Rightarrow> String.literal"
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
  node_annotation :: "pp \<Rightarrow> 'ctx \<Rightarrow> graphviz_node_annotation option"

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

subsection \<open>Enumerating a context set for presentation\<close>

text \<open>
  A solved \<^type>\<open>analysis_result\<close> records its coverage as a set, and a set has
  no order to read off: two lists backing the same set are the same value, so
  any function whose result depended on which one a code-generation backend
  happens to hold would not be a function of the result at all. A drawn graph
  nevertheless needs one --- node sequence, cluster sequence, and the
  \<open>_ctxN\<close> suffix \<open>analysis_node_id\<close> derives through \<open>context_position\<close> below
  are all positional.

  The order is therefore chosen, not read: contexts are sorted by the
  config's own \<^const>\<open>context_key\<close>, kept a separate field from
  \<^const>\<open>show_context\<close> so ordering and display cannot silently drift apart
  by editing one and not the other. \<^typ>\<open>String.literal\<close> carries the
  \<^class>\<open>linorder\<close> this needs; \<^typ>\<open>'ctx\<close> carries nothing. That distinction is
  the point --- real context types do not have a linear order to borrow. An
  interval-vector context is the standing example: the interval domain's own
  \<^class>\<open>order\<close> instance is the abstraction order, under which \<open>[0,1]\<close> and
  \<open>[2,3]\<close> are simply incomparable, so that slot is spoken for and no linear
  one can occupy it. No such constraint is added to \<^typ>\<open>'ctx\<close> here: the
  order lives entirely on the \<^typ>\<open>String.literal\<close> image, never on the
  context type itself.

  \<^const>\<open>the_elem\<close> maps a key back to its context, so the config's
  \<^const>\<open>context_key\<close> must separate the contexts it is asked to order --- an
  exactness requirement independent of, and stricter than, what
  \<^const>\<open>show_context\<close>'s human-readable rendering owes a reader. Two
  contexts sharing a key would produce two clusters with one label and two
  indistinguishable node-id groups, so a diagram needs the same condition to
  be readable at all. \<open>set_ordered_by_key\<close> states it, and a caller discharges
  it by execution on its own program.
\<close>

definition ordered_by_key :: "('a \<Rightarrow> String.literal) \<Rightarrow> 'a set \<Rightarrow> 'a list" where
  "ordered_by_key key S =
    map (\<lambda>k. the_elem (Set.filter (\<lambda>x. key x = k) S))
      (sorted_list_of_set (key ` S))"

lemma set_ordered_by_key:
  assumes fin: "finite S"
    and inj: "inj_on key S"
  shows "set (ordered_by_key key S) = S"
proof -
  have keys: "set (sorted_list_of_set (key ` S)) = key ` S"
    using fin by simp
  have pick: "the_elem (Set.filter (\<lambda>x. key x = key y) S) = y" if "y \<in> S" for y
  proof -
    have "Set.filter (\<lambda>x. key x = key y) S = {y}"
      using that inj by (auto simp: inj_on_def)
    then show ?thesis by simp
  qed
  have "set (ordered_by_key key S)
      = (\<lambda>k. the_elem (Set.filter (\<lambda>x. key x = k) S)) ` (key ` S)"
    unfolding ordered_by_key_def set_map keys by (rule refl)
  also have "\<dots> = S" using pick by (auto simp: image_iff)
  finally show ?thesis .
qed

text \<open>
  An executable guard against exactly the collision \<^const>\<open>the_elem\<close> above
  would otherwise resolve arbitrarily: \<^const>\<open>context_key\<close> must separate the
  contexts it is handed, and this checks that on the actual, finite set a
  render call supplies rather than assuming it. \<^const>\<open>card\<close> of an image
  equalling \<^const>\<open>card\<close> of the source is the executable, finite-set form of
  \<^const>\<open>inj_on\<close> --- \<open>context_keys_distinct_imp_inj_on\<close> below ties the two
  together so a caller can discharge \<open>set_ordered_by_key\<close>'s premise this way.
\<close>

definition context_keys_distinct ::
  "('ctx, 'g, 'a, 'd) analysis_graph_config \<Rightarrow> 'ctx set \<Rightarrow> bool" where
  "context_keys_distinct cfg S = (card (context_key cfg ` S) = card S)"

lemma context_keys_distinct_imp_inj_on:
  assumes fin: "finite S"
    and distinct: "context_keys_distinct cfg S"
  shows "inj_on (context_key cfg) S"
proof (rule eq_card_imp_inj_on[OF fin])
  show "card (context_key cfg ` S) = card S"
    using distinct unfolding context_keys_distinct_def .
qed

text \<open>
  The graph domain of a solved result: every \<^typ>\<open>pp\<close> the CFG has, paired with
  exactly the contexts covered at it. Coverage stays the result's own
  extensional key set --- \<^const>\<open>contexts_at\<close> is a membership question, never a
  traversal --- and only the sequence the pairs are laid out in comes from the
  ordering above.
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
      route = (\<lambda>_ _ _ _. Some ()),
      context_key = (\<lambda>_. STR ''''),
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
      node_annotation = (\<lambda>_ _. None)
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
          (case route cfg u (snd src_ctx) ca (local_of cfg (sol (Inl src_ctx))) of
             None \<Rightarrow> []
           | Some callee_ctx \<Rightarrow>
               if (entry, callee_ctx) \<in> set covered
               then [(LocalNode u (snd src_ctx), EnterEdge (owner_of cfg entry) ca,
                      LocalNode entry callee_ctx)]
               else [])
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
            (case route cfg call (snd src_ctx) ca (local_of cfg (sol (Inl src_ctx))) of
               None \<Rightarrow> []
             | Some callee_ctx \<Rightarrow>
                 let result = FunctionResult p
                 in if (result, callee_ctx) \<in> set covered \<and>
                       (cont, snd src_ctx) \<in> set covered
                    then [(LocalNode result callee_ctx,
                           CombineEdge call (case ca of CallEdge dst _ _ \<Rightarrow> dst)
                             (return_slot_for_pp cfg result),
                           LocalNode cont (snd src_ctx))]
                    else [])
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

subsection \<open>Call-string context presentation\<close>

text \<open>
  A call-string context is a \<^typ>\<open>cfg_node list\<close> (\<^theory>\<open>Voblint_Core.Call_String_Context\<close>),
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

definition cs_show_context :: "cfg_node list \<Rightarrow> string" where
  "cs_show_context ctx = concat (map (\<lambda>u. string_of_cfg_node u @ '' '') ctx)"

definition cs_context_key :: "cfg_node list \<Rightarrow> String.literal" where
  "cs_context_key ctx = String.implode (cs_show_context ctx)"

definition cs_graph_route ::
  "nat \<Rightarrow> pp \<Rightarrow> cfg_node list \<Rightarrow> call_action \<Rightarrow> 'd \<Rightarrow> cfg_node list option" where
  "cs_graph_route k u ctx ca d = Some (cs_route k u ctx d ca)"

definition cs_cluster_label :: "string \<Rightarrow> cfg_node list \<Rightarrow> string" where
  "cs_cluster_label owner ctx =
     (if ctx = [] then owner @ '' / root context''
      else owner @ '' / call-string='' @ cs_show_context ctx)"

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
          @ (case node_annotation cfg p ctx of
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
      LocalNode p ctx \<Rightarrow>
        (case node_annotation cfg p ctx of
          Some ann \<Rightarrow> annotation_style ann
        | None \<Rightarrow>
            if p = cfg_entry g then ''shape=doublecircle,color=green,style=filled,fillcolor=lightyellow''
            else if p = graphviz_exit g then ''shape=doublecircle,color=gray40,style=filled,fillcolor=lightgray''
            else if p \<in> set (proc_entry_pps_list g) then ''shape=doublecircle,color=green,style=filled,fillcolor=lightyellow''
            else if p \<in> set (proc_exit_pps_list g) then ''shape=doublecircle,color=gray40,style=filled,fillcolor=lightgray''
            else ''shape=box,style=filled,fillcolor=lightgreen'')
    | GlobalNode _ \<Rightarrow> ''shape=note,width=2.2,fixedsize=false''
    | SourceNode _ \<Rightarrow> ''shape=plain'')" 

fun enter_bindings :: "vname list \<Rightarrow> exp list \<Rightarrow> string list" where
  "enter_bindings [] _ = []"
| "enter_bindings _ [] = []"
| "enter_bindings (x # xs) (e # es) =
    (String.explode x @ '' := '' @ string_of_exp 0 e) # enter_bindings xs es"

definition enter_action_label :: "call_action \<Rightarrow> string" where
  "enter_action_label a = string_of_call_action a"

definition source_action_label :: "cfg \<Rightarrow> edge_action \<Rightarrow> string" where
  "source_action_label g a =
    (case a of EA_Assign x e \<Rightarrow>
       if x = ret_var then ''ret := '' @ string_of_exp 0 e else string_of_action a    | EA_Assume b \<Rightarrow> string_of_exp 0 b
    | EA_AssumeNot b \<Rightarrow> ''not ('' @ string_of_exp 0 b @ '')''
    | EA_Ret _ p \<Rightarrow> if cfg_entry g = FunctionEntry p then ''terminate'' else string_of_action a
    | _ \<Rightarrow> string_of_action a)"

definition analysis_edge_attrs :: "cfg \<Rightarrow> analysis_edge_kind \<Rightarrow> string" where
  "analysis_edge_attrs g kind =
    (case kind of
      IntraEdge a \<Rightarrow> ''label='' @ dq @ source_action_label g a @ dq
    | EnterEdge callee a \<Rightarrow> ''color=purple,penwidth=2,weight=10,label='' @ dq
        @ ''call '' @ callee @ ''('' @
          (case a of CallEdge _ _ es \<Rightarrow> join_source '', '' (map (string_of_exp 0) es)) @ '')'' @ dq
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
        @ (case a of CallEdge _ _ es \<Rightarrow> join_source '', '' (map (string_of_exp 0) es)) @ '')''
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
  The structural role \<^const>\<open>analysis_node_attrs\<close> falls back on when a point carries no
  annotation, as a tag instead of as the attributes it picks. The case order matches that
  fallback exactly, so a renderer reading \<^const>\<open>xn_kind\<close> and \<^const>\<open>xn_status\<close> together
  reconstructs the same styling decision.
\<close>

definition export_node_kind_of ::
  "cfg \<Rightarrow> ('ctx, 'g) analysis_node \<Rightarrow> export_node_kind" where
  "export_node_kind_of g n =
    (case n of
      LocalNode p _ \<Rightarrow>
        (if p = cfg_entry g then XN_Entry
         else if p = graphviz_exit g then XN_Exit
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
  An edge's own content, with none of the wording that names its role. Both
  \<^const>\<open>analysis_edge_attrs\<close> and \<^const>\<open>canonical_edge_kind_text\<close> prefix that content
  differently --- \<open>call f(x)\<close> against \<open>enter f(x)\<close> for one and the same edge --- because each
  is writing for its own reader. Pairing this payload with \<^const>\<open>export_edge_kind_of\<close>
  leaves that choice to whichever renderer consumes the export, instead of freezing one
  renderer's phrasing into the exported value and making every other consumer strip it.
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
  "proc_table \<Rightarrow> pname list \<Rightarrow> pname \<Rightarrow> com \<Rightarrow> (pp \<Rightarrow> graphviz_node_annotation option)
    \<Rightarrow> (unit, unit, unit, unit) analysis_graph_config" where
  "raw_cfg_graph_config \<Pi> ps mnm main annotate =
    \<lparr> local_of = id,
      route = (\<lambda>_ _ _ _. Some ()),
      context_key = (\<lambda>_. STR ''''),
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
      node_annotation = (\<lambda>p _. annotate p)
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

text \<open>
  The structured-export sibling of \<^const>\<open>raw_cfg_dot\<close> and
  \<^const>\<open>raw_cfg_canonical_text\<close>: the same compiled CFG, the same one-context graph
  configuration, the same annotation hook, differing only in which of the three views of
  the built graph it returns. Already \<^typ>\<open>String.literal\<close>-valued throughout, so there is
  no \<open>_lit\<close> counterpart to write.
\<close>

definition raw_cfg_export ::
  "proc_table \<Rightarrow> pname list \<Rightarrow> pname \<Rightarrow> com \<Rightarrow> (pp \<Rightarrow> graphviz_node_annotation option)
    \<Rightarrow> export_graph" where
  "raw_cfg_export \<Pi> ps mnm main annotate =
    (let g = compile_prog \<Pi> ps mnm main;
         cfg = raw_cfg_graph_config \<Pi> ps mnm main annotate;
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
  \<^typ>\<open>exp\<close> table --- the report already names every checked node once.
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

