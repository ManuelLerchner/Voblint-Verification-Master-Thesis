theory Analysis_Graph
  imports
    "Voblint_Compile.Compile_Wellformed"
    "Voblint_VIMP.VIMP_Source_Print"
    "Voblint_Exec.Exec_St_Reachability"
    "Voblint_Domain.Abstract_Domain"
    "Voblint_Framework.Check_Report"
    "Voblint_Framework.Analysis_Result"
    "Voblint_Framework.Call_String_Context"
begin

section \<open>What an analysis computed, as a graph\<close>

text \<open>
  A solved analysis is a table: one abstract state per (program point, context).
  A reader cannot see a loop or a call chain in a table, so the theories above
  this one rebuild it as a graph --- the compiled CFG, each node carrying the
  state computed there --- and hand that over as data. This theory fixes the
  vocabulary they all speak.

  Three words recur. A \<^emph>\<open>context-expanded\<close> graph holds one node per (point,
  context) pair rather than one per point, so a procedure analysed at two call
  contexts appears twice; that is the only way a context-sensitive result is
  visible at all. A node's \<^emph>\<open>annotation\<close> is what a check verdict adds to it
  --- proved, refuted, unknown, or unreachable --- kept separate from the state
  label so a report can mark a node without changing what it says. And a
  \<^emph>\<open>config\<close> is the caller's half: the record of hooks deciding how contexts
  are keyed, which globals are shown, and how a state is printed.

  Nothing in this session draws a picture. The eventual output is a record of
  clusters, nodes and edges with no colours, shapes or label markup in it; DOT
  and HTML are produced from that record by the OCaml renderers, outside
  Isabelle. Nothing here is domain-specific either: a state is printed through
  the domain's own \<open>to_string\<close>, so Sign and Interval share these files
  unchanged.

  The rest of the layer sits above: \<open>Analysis_Graph_Build\<close> constructs a graph
  from a solved result, \<open>Analysis_Graph_Wf\<close> proves what it constructs is
  well-formed, \<open>Analysis_Graph_Naming\<close> gives its nodes and clusters
  identifiers, and \<open>Analysis_Graph_Export\<close> hands the result out.
\<close>

subsection \<open>CFG text helpers\<close>

fun string_of_action :: "edge_action \<Rightarrow> String.literal" where
  "string_of_action EA_Nop = STR ''nop''"
| "string_of_action (EA_Assign x a) =
    x + STR '' := '' + string_of_exp 0 a"
| "string_of_action (EA_Special Nondet_Int x) =
    x + STR '' := __voblint_nondet_int()''"
| "string_of_action (EA_Special (Min a b) x) =
    x + STR '' := min('' + string_of_exp 0 a
      + STR '', '' + string_of_exp 0 b + STR '')''"
| "string_of_action (EA_Special (Max a b) x) =
    x + STR '' := max('' + string_of_exp 0 a
      + STR '', '' + string_of_exp 0 b + STR '')''"
| "string_of_action (EA_Assume b) =
    STR ''['' + string_of_exp 0 b + STR '']''"
| "string_of_action (EA_AssumeNot b) =
    STR ''!['' + string_of_exp 0 b + STR '']''"
| "string_of_action (EA_Body p) =
    STR ''body('' + p + STR '')''"
| "string_of_action (EA_Ret None p) = STR ''return''"
| "string_of_action (EA_Ret (Some e) p) =
    STR ''return '' + string_of_exp 0 e"
| "string_of_action (EA_Check cnd) =
    STR ''check('' + string_of_exp 0 cnd + STR '')''"

definition nl :: String.literal where
  "nl = String.literal_of_asciis [0x0A]"

definition esc_nl :: String.literal where
  "esc_nl = String.literal_of_asciis [0x5C, 0x6E]"

fun join_esc_nl :: "String.literal list \<Rightarrow> String.literal" where
  "join_esc_nl [] = STR ''''"
| "join_esc_nl [s] = s"
| "join_esc_nl (s # ss) = s + esc_nl + join_esc_nl ss"

definition proc_entry_pps_list :: "cfg \<Rightarrow> pp list" where
  "proc_entry_pps_list g =
    map (\<lambda>(_, _, entry, _). entry) (cfg_calls_list g)"

definition proc_exit_pps_list :: "cfg \<Rightarrow> pp list" where
  "proc_exit_pps_list g =
    map (\<lambda>(_, _, entry, _).
      case entry of FunctionEntry p \<Rightarrow> FunctionResult p | _ \<Rightarrow> entry)
      (cfg_calls_list g)"

fun string_of_cfg_node :: "cfg_node \<Rightarrow> String.literal" where
  "string_of_cfg_node (Statement n) =
    STR ''pp'' + string_of_nat n"
| "string_of_cfg_node (FunctionEntry p) =
    STR ''entry_'' + p"
| "string_of_cfg_node (FunctionResult p) =
    STR ''result_'' + p"

section \<open>Generic context-expanded analysis graph\<close>

text \<open>
  The analysis graph is independent of DOT. It records contextual local nodes,
  shared global nodes, and the semantic role of every routed edge. The builder
  consumes the same routing function as the equation generator.
\<close>

datatype ('ctx, 'g) analysis_cluster =
    ContextCluster
      (cluster_name: String.literal)
      (cluster_ctx: 'ctx)
  | GlobalCluster
  | SourceCluster

datatype ('ctx, 'g) analysis_node =
    LocalNode (node_pp: pp) (node_ctx: 'ctx)
  | GlobalNode (node_glob: 'g)
  | SourceNode (node_name: String.literal)

datatype analysis_edge_kind =
    IntraEdge (aek_action: edge_action)
  | EnterEdge
      (aek_enter_proc: String.literal)
      (aek_call: call_action)
  | CombineEdge
      (combine_call_pp: pp)
      (combine_dst: "vname option")
      (combine_ret: "vname option")
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
  NS_Plain
| NS_Proved
| NS_Refuted
| NS_Unknown
| NS_Unreachable
| NS_Exit

text \<open>
  A node annotation is presentation metadata a caller attaches to one \<^typ>\<open>pp\<close>: an optional
  extra label line and a \<^typ>\<open>node_status\<close> that, when present, overrides the default styling
  for that point. Which findings a caller overlays on the CFG is its own business; turning
  \<^const>\<open>Some\<close> into concrete attributes and \<^const>\<open>None\<close> into default entry/exit styling
  belongs to whichever renderer consumes the export, outside this theory.
\<close>

datatype graph_node_annotation =
  Node_Annotation
    (annotation_lines: "String.literal list")
    (annotation_status: node_status)

text \<open>
  Shared status mapping for a compiled \<^verbatim>\<open>__voblint_check(...)\<close>
  condition, given its executable \<^typ>\<open>check_result\<close> classification.
  Domain-independent (only \<^typ>\<open>check_result\<close> and \<^typ>\<open>exp\<close>), so every
  domain's check-discharge example renders proof status through this one
  mapping instead of restating it.
\<close>

definition check_result_annotation ::
  "check_result \<Rightarrow> exp \<Rightarrow> graph_node_annotation" where
  "check_result_annotation res cnd =
     (case res of
        Check_Proved \<Rightarrow>
          Node_Annotation
            [STR ''check '' + string_of_exp 0 cnd]
            NS_Proved
      | Check_Unknown \<Rightarrow>
          Node_Annotation
            [STR ''check '' + string_of_exp 0 cnd + STR '' [unknown]'']
            NS_Unknown
      | Check_Refuted \<Rightarrow>
          Node_Annotation
            [STR ''check '' + string_of_exp 0 cnd + STR '' [REFUTED]'']
            NS_Refuted)"

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

  is_dead_local :: "'d \<Rightarrow> bool"

  context_key :: "'ctx \<Rightarrow> String.literal"
  show_context :: "'ctx \<Rightarrow> String.literal"

  locals_for_pp :: "pp \<Rightarrow> vname list"
  return_slot_for_pp :: "pp \<Rightarrow> vname option"
  globals_to_show :: "vname list"

  show_local ::
    "pp \<Rightarrow> 'ctx \<Rightarrow> vname list \<Rightarrow> 'd \<Rightarrow> String.literal list"

  format_return ::
    "pp \<Rightarrow> 'ctx \<Rightarrow> vname \<Rightarrow> 'd \<Rightarrow> String.literal list"

  show_global ::
    "'g \<Rightarrow> vname list \<Rightarrow> 'a \<Rightarrow> String.literal list"

  show_global_key ::
    "'g \<Rightarrow> String.literal"

  is_shared_global :: "'g \<Rightarrow> bool"
  show_internal_globals :: bool

  owner_of ::
    "pp \<Rightarrow> String.literal"

  cluster_label ::
    "String.literal \<Rightarrow> 'ctx \<Rightarrow> String.literal"

  source_text ::
    "String.literal option"

  node_annotation ::
    "pp \<Rightarrow> 'ctx \<Rightarrow> graph_node_annotation option"

fun compiled_proc_owner ::
  "proc_table \<Rightarrow> pname list \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> pname option" where
  "compiled_proc_owner \<Pi> [] n k = None"
| "compiled_proc_owner \<Pi> (p # ps) n k =
    (case \<Pi> p of
      None \<Rightarrow> compiled_proc_owner \<Pi> ps n k
    | Some decl \<Rightarrow>
        (let (n', E, K) = compile_proc \<Pi> p decl n
         in if n \<le> k \<and> k < n'
            then Some p
            else compiled_proc_owner \<Pi> ps n' k))"

definition compiled_owner_of ::
  "proc_table \<Rightarrow> pname list \<Rightarrow> pp \<Rightarrow> pname" where
  "compiled_owner_of \<Pi> ps p =
    (case p of
      FunctionEntry owner \<Rightarrow> owner
    | FunctionResult owner \<Rightarrow> owner
    | Statement k \<Rightarrow>
        (case compiled_proc_owner \<Pi> ps 0 k of
           Some owner \<Rightarrow> owner
         | None \<Rightarrow> prog_main_name))"

definition cfg_point_list :: "cfg \<Rightarrow> pp list" where
  "cfg_point_list g =
    remdups
      (cfg_entry g #
       concat (map (\<lambda>(u, _, v). [u, v]) (cfg_intra_list g)) @
       concat (map (\<lambda>(call, _, entry, cont).
         call # entry # cont #
         (case entry of
            FunctionEntry p \<Rightarrow> [FunctionResult p]
          | _ \<Rightarrow> []))
         (cfg_calls_list g)))"

definition contextual_graph_domain ::
  "cfg \<Rightarrow> (pp \<Rightarrow> 'ctx list) \<Rightarrow> ((pp \<times> 'ctx) + 'g) list" where
  "contextual_graph_domain g contexts_for_pp =
    concat
      (map
        (\<lambda>p. map (\<lambda>ctx. Inl (p, ctx)) (contexts_for_pp p))
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

text \<open>
  HOL's own code equation for \<^const>\<open>the_elem\<close> matches only a literal one-element
  list, but a set built by an image or a filter is backed by a list that may repeat
  its element --- the contexts of a context-free table are one \<open>()\<close> per point ---
  and the generated code then fails with a match error. Deduplicating first is the
  same set.
\<close>

lemma the_elem_set_remdups [code]:
  "the_elem (set xs) =
     (case remdups xs of
        [x] \<Rightarrow> x
      | _ \<Rightarrow> Code.abort (STR ''the_elem: not a singleton'') (\<lambda>_. the_elem (set xs)))"
proof (cases "remdups xs")
  case Nil
  then show ?thesis by simp
next
  case (Cons y ys)
  then show ?thesis
  proof (cases ys)
    case Nil
    with Cons have "set xs = {y}" by (metis set_remdups empty_set list.simps(15))
    with Cons Nil show ?thesis by simp
  next
    case (Cons z zs)
    with \<open>remdups xs = y # ys\<close> show ?thesis by simp
  qed
qed

definition ordered_by_key ::
  "('a \<Rightarrow> 'k::linorder) \<Rightarrow> 'a set \<Rightarrow> 'a list" where
  "ordered_by_key key S =
    map
      (\<lambda>k. the_elem (Set.filter (\<lambda>x. key x = k) S))
      (sorted_list_of_set (key ` S))"

lemma set_ordered_by_key:
  assumes fin: "finite S"
    and inj: "inj_on key S"
  shows "set (ordered_by_key key S) = S"
proof -
  have keys:
    "set (sorted_list_of_set (key ` S)) = key ` S"
    using fin by simp

  have pick:
    "the_elem (Set.filter (\<lambda>x. key x = key y) S) = y"
    if "y \<in> S"
    for y
  proof -
    have "Set.filter (\<lambda>x. key x = key y) S = {y}"
      using that inj by (auto simp: inj_on_def)
    then show ?thesis by simp
  qed

  have "set (ordered_by_key key S)
      = (\<lambda>k. the_elem (Set.filter (\<lambda>x. key x = k) S)) ` (key ` S)"
    unfolding ordered_by_key_def set_map keys
    by (rule refl)
  also have "\<dots> = S"
    using pick by (auto simp: image_iff)
  finally show ?thesis .
qed

end