theory Analysis_Render
  imports Analysis_Run
begin

section \<open>Rendering a report\<close>

text \<open>
  A report holds semantic states. What a consumer displays is a projection of it:
  each active analysis's part of a state, as that analysis's own value, then as a
  string. The projection is defined here so that generated code computes it; no
  soundness theorem reads it, and it changes neither the check column nor the
  diagnostics.
\<close>

subsection \<open>The rendered result\<close>

text \<open>
  A rendered state is shown one active analysis at a time, in activation order, each
  as its own \<^typ>\<open>'v field_state\<close>, as Goblint's report shows each component of its
  combined state. A context reads as the formal values its policy keys it by.
\<close>

datatype 'v analysis_context =
    Context_Unit
  | Context_Entry "'v list"
  | Context_Call_String "pp list"

type_synonym 'v analysis_view = "(analysis_domain \<times> 'v field_state) list"

text \<open>
  The states a report holds at a point, joined over its contexts: what a reader who
  ignores contexts can say about the point. It may be coarser than the states it
  joins, but every store any of them describes, it describes too
  (\<open>report_sem_point_join\<close>).
\<close>

text \<open>
  A read state maps names to values, and generated code cannot carry the order of such
  a function, only its join, which is pointwise. \<open>vjoin\<close> is that join alone, per type
  constructor; \<open>join_val_sup\<close> records that it is the lattice join, so the theorems
  about \<open>report_point_join\<close> speak about \<open>\<squnion>\<close>.
\<close>

class join_val =
  fixes vjoin :: "'a \<Rightarrow> 'a \<Rightarrow> 'a"

text \<open>A join that is the lattice join of a semilattice, for the proofs only.\<close>

class join_val_sup = join_val + semilattice_sup +
  assumes vjoin_sup: "vjoin x y = x \<squnion> y"

instantiation "fun" :: (type, semilattice_sup) join_val
begin
definition vjoin_fun :: "('a \<Rightarrow> 'b) \<Rightarrow> ('a \<Rightarrow> 'b) \<Rightarrow> 'a \<Rightarrow> 'b" where
  "vjoin_fun f g = (\<lambda>x. f x \<squnion> g x)"
instance ..
end

instance "fun" :: (type, semilattice_sup) join_val_sup
  by standard (simp add: vjoin_fun_def sup_fun_def)

instantiation lifted :: (join_val) join_val
begin
fun vjoin_lifted :: "'a lifted \<Rightarrow> 'a lifted \<Rightarrow> 'a lifted" where
  "vjoin_lifted Bot y = y"
| "vjoin_lifted (Lifted x) Bot = Lifted x"
| "vjoin_lifted (Lifted x) (Lifted y) = Lifted (vjoin x y)"
instance ..
end

instance lifted :: (join_val_sup) join_val_sup
proof
  fix x y :: "'a lifted"
  show "vjoin x y = x \<squnion> y" by (cases x; cases y) (simp_all add: vjoin_sup)
qed

instantiation analysis_product :: (join_val, join_val) join_val
begin
definition vjoin_analysis_product ::
    "('a, 'b) analysis_product \<Rightarrow> ('a, 'b) analysis_product \<Rightarrow> ('a, 'b) analysis_product" where
  "vjoin_analysis_product p q = Product (vjoin (pleft p) (pleft q)) (vjoin (pright p) (pright q))"
instance ..
end

instance analysis_product :: (join_val_sup, join_val_sup) join_val_sup
  by standard (simp add: vjoin_analysis_product_def sup_analysis_product_def vjoin_sup)

instantiation relc :: join_val
begin
definition vjoin_relc :: "relc \<Rightarrow> relc \<Rightarrow> relc" where "vjoin_relc = sup"
instance ..
end

instance relc :: join_val_sup
  by standard (simp add: vjoin_relc_def)

definition report_point_join :: "analysis_report \<Rightarrow> pp \<Rightarrow> mcp_val lifted" where
  "report_point_join res v =
     fold vjoin (map state_value (filter (\<lambda>st. state_point st = v) (report_states res))) Bot"

text \<open>
  What a point's outgoing steps produce, joined over its contexts the same way. Every
  context lists the point's steps in the order of its outgoing edges, so the lists are
  joined position by position.
\<close>

definition report_steps_join :: "analysis_report \<Rightarrow> pp \<Rightarrow> (pp \<times> mcp_val lifted) list" where
  "report_steps_join res v =
     (case map state_steps (filter (\<lambda>st. state_point st = v) (report_states res)) of
        [] \<Rightarrow> []
      | s # ss \<Rightarrow> fold (map2 (\<lambda>(w, a) (_, b). (w, vjoin a b))) ss s)"

lemma report_point_join_sup:
  "report_point_join res v =
     fold (\<squnion>) (map state_value (filter (\<lambda>st. state_point st = v) (report_states res))) Bot"
  unfolding report_point_join_def by (simp add: vjoin_sup[abs_def])

record 'v run_result =
  res_cfg :: cfg
  res_contexts :: "'v analysis_context list"
  res_states :: "'v analysis_view result_state list"
  res_joined :: "(pp \<times> 'v analysis_view lifted \<times> (pp \<times> 'v analysis_view lifted) list) list"
  res_routes :: "call_route list"
  res_checks :: "result_check list"
  res_globals :: "'v analysis_view result_global list"
  res_diagnostics :: "arithmetic_diagnostic list"

definition map_analysis_view :: "('v \<Rightarrow> 'w) \<Rightarrow> 'v analysis_view \<Rightarrow> 'w analysis_view" where
  "map_analysis_view f = map (\<lambda>(a, s). (a, map_field_state f s))"

definition mcp_render ::
    "analysis_domain list \<Rightarrow> vname list \<Rightarrow> mcp_val \<Rightarrow> abstract_value analysis_view" where
  "mcp_render as vars v = map (\<lambda>a. (a, value_display (registration_of a) v vars)) as"

text \<open>
  The printer \<open>show\<close> is a parameter: \<^const>\<open>string_of_abstract_value\<close> for text,
  composed in the adapter with whatever post-processing its output needs.
\<close>

fun render_context ::
    "(abstract_value \<Rightarrow> 'v) \<Rightarrow> analysis_domain list \<Rightarrow> report_context \<Rightarrow> 'v analysis_context"
where
  "render_context show as Report_Unit = Context_Unit"
| "render_context show as (Report_Entry ctx) = Context_Entry (map show (mcp_ctx_values as ctx))"
| "render_context show as (Report_Call_String us) = Context_Call_String us"

definition render_report :: "(abstract_value \<Rightarrow> 'v) \<Rightarrow> analysis_report \<Rightarrow> 'v run_result" where
  "render_report show res =
     (let as = activation (config_analyses (report_config res));
          state = map_analysis_view show \<circ> mcp_render as (report_vars res)
      in \<lparr> res_cfg = report_cfg res,
           res_contexts = map (render_context show as) (report_contexts res),
           res_states = map (map_result_state state) (report_states res),
           res_joined = map (\<lambda>v. (v, map_lift state (report_point_join res v),
                                  map (\<lambda>(w, s). (w, map_lift state s)) (report_steps_join res v)))
                          (cfg_node_list (report_cfg res)),
           res_routes = report_routes res,
           res_checks = report_checks res,
           res_globals = map (map_result_global state) (report_globals res),
           res_diagnostics = report_diagnostics res \<rparr>)"

lemma render_report_columns [simp]:
  "res_cfg (render_report show res) = report_cfg res"
  "res_checks (render_report show res) = report_checks res"
  "res_diagnostics (render_report show res) = report_diagnostics res"
  "res_routes (render_report show res) = report_routes res"
  by (simp_all add: render_report_def Let_def)

section \<open>The analysis graph\<close>

text \<open>
  The report's states are filed by point \<^emph>\<open>and\<close> context, so the graph a reader sees of
  them has a node per such pair, where the CFG has one per point. A flow-insensitive
  program global adds a node of its own. The edges are the dependencies the equations
  have between those unknowns: a step within a context, a call entering the contexts
  the report routes it to, the callee's result resuming the caller, the call's
  continuation, and the reads and writes of each global, by the same footprints the
  keyed lifter reads and publishes (\<^const>\<open>edge_global_reads\<close>,
  \<^const>\<open>edge_global_writes\<close>, \<^const>\<open>call_global_reads\<close>). It is a projection of the
  report, as the rendering above is, and no theorem reads it.
\<close>

datatype unknown_node = Local_Node pp nat | Global_Node vname

datatype analysis_edge =
    Intra_Dep edge_action
  | Enter_Dep call_action
  | Combine_Dep call_action
  | Continue_Dep call_action
  | Global_Read
  | Global_Write

record analysis_graph =
  graph_nodes :: "unknown_node list"
  graph_edges :: "(unknown_node \<times> analysis_edge \<times> unknown_node) list"

text \<open>The program globals the report keeps at unknowns of their own.\<close>

definition report_global_names :: "analysis_report \<Rightarrow> vname list" where
  "report_global_names res =
     concat (map (\<lambda>g. case global_unknown g of Global_Named x \<Rightarrow> [x] | _ \<Rightarrow> []) (report_globals res))"

definition report_rows_of :: "analysis_report \<Rightarrow> (pp \<times> nat) list" where
  "report_rows_of res = map (\<lambda>st. (state_point st, state_context st)) (report_states res)"

definition report_route_targets :: "analysis_report \<Rightarrow> pp \<Rightarrow> nat \<Rightarrow> nat list" where
  "report_route_targets res u c =
     concat (map route_targets
       (filter (\<lambda>r. route_point r = u \<and> route_context r = c) (report_routes res)))"

definition callee_of :: "pp \<Rightarrow> pname" where
  "callee_of entry = (case entry of FunctionEntry f \<Rightarrow> f | FunctionResult f \<Rightarrow> f | Statement _ \<Rightarrow> STR '''')"

text \<open>What a step within one context adds: the step, and the globals it reads and writes.\<close>

definition intra_deps ::
    "(vname \<Rightarrow> bool) \<Rightarrow> (pp \<times> nat) list \<Rightarrow> pp \<Rightarrow> nat \<Rightarrow> pp \<times> edge_action \<times> pp
     \<Rightarrow> (unknown_node \<times> analysis_edge \<times> unknown_node) list" where
  "intra_deps G rows u c e =
     (case e of (u', a, v) \<Rightarrow>
        if u' = u \<and> (v, c) \<in> set rows
        then (Local_Node u c, Intra_Dep a, Local_Node v c)
             # map (\<lambda>x. (Global_Node x, Global_Read, Local_Node v c)) (edge_global_reads G a)
             @ map (\<lambda>x. (Local_Node v c, Global_Write, Global_Node x)) (edge_global_writes G a)
        else [])"

text \<open>
  What a call adds: an entry into every context the report routes it to, the callee's
  result resuming the caller from each, and the continuation. The continuation's
  equation evaluates the call, so it reads the globals the arguments mention and
  writes a global destination or formal.
\<close>

definition call_deps ::
    "analysis_report \<Rightarrow> (vname \<Rightarrow> bool) \<Rightarrow> (pp \<times> nat) list \<Rightarrow> pp \<Rightarrow> nat
     \<Rightarrow> pp \<times> call_action \<times> pp \<times> pp \<Rightarrow> (unknown_node \<times> analysis_edge \<times> unknown_node) list" where
  "call_deps res G rows u c e =
     (case e of (u', ca, entry, after) \<Rightarrow>
        if u' \<noteq> u then []
        else
          (let targets = report_route_targets res u c;
               result = FunctionResult (callee_of entry)
           in concat (map (\<lambda>t.
                (if (entry, t) \<in> set rows then [(Local_Node u c, Enter_Dep ca, Local_Node entry t)] else [])
                @ (if (result, t) \<in> set rows \<and> (after, c) \<in> set rows
                   then [(Local_Node result t, Combine_Dep ca, Local_Node after c)] else []))
                targets)
              @ (if (after, c) \<in> set rows
                 then (Local_Node u c, Continue_Dep ca, Local_Node after c)
                      # (case ca of CallEdge dst pars args \<Rightarrow>
                           map (\<lambda>x. (Global_Node x, Global_Read, Local_Node after c))
                             (call_global_reads G args)
                           @ map (\<lambda>x. (Local_Node after c, Global_Write, Global_Node x))
                               (global_names_in G (case_option [] (\<lambda>x. [x]) dst @ pars)))
                 else [])))"

definition analysis_graph_of :: "analysis_report \<Rightarrow> analysis_graph" where
  "analysis_graph_of res =
     (let g = report_cfg res;
          rows = report_rows_of res;
          names = report_global_names res;
          G = (\<lambda>x. x \<in> set names)
      in \<lparr> graph_nodes = map (\<lambda>(v, c). Local_Node v c) rows @ map Global_Node names,
           graph_edges =
             concat (map (\<lambda>(u, c).
                 concat (map (intra_deps G rows u c) (cfg_intra_list g))
                 @ concat (map (call_deps res G rows u c) (cfg_calls_list g))
                 @ (if u = cfg_entry g
                    then map (\<lambda>x. (Local_Node u c, Global_Write, Global_Node x)) names else []))
               rows) \<rparr>)"

subsection \<open>What the graph contains\<close>

text \<open>
  The graph's nodes are exactly the report's unknowns, and a step between two reported
  points of one context carries the global reads and writes its footprint names.
\<close>

lemma local_node_in_analysis_graph:
  "Local_Node v c \<in> set (graph_nodes (analysis_graph_of res))
     \<longleftrightarrow> (\<exists>st \<in> set (report_states res). state_point st = v \<and> state_context st = c)"
  by (auto simp: analysis_graph_of_def report_rows_of_def Let_def)

lemma global_node_in_analysis_graph:
  "Global_Node x \<in> set (graph_nodes (analysis_graph_of res))
     \<longleftrightarrow> (\<exists>gl \<in> set (report_globals res). global_unknown gl = Global_Named x)"
proof -
  have "x \<in> set (report_global_names res)
          \<longleftrightarrow> (\<exists>gl \<in> set (report_globals res). global_unknown gl = Global_Named x)"
    by (force simp: report_global_names_def split: result_global_unknown.splits)
  then show ?thesis by (auto simp: analysis_graph_of_def Let_def)
qed

text \<open>A step of a reported context contributes all its dependencies to the graph.\<close>

lemma intra_deps_in_analysis_graph:
  assumes "(u, c) \<in> set (report_rows_of res)" and "e \<in> set (cfg_intra_list (report_cfg res))"
  shows "set (intra_deps (\<lambda>y. y \<in> set (report_global_names res)) (report_rows_of res) u c e)
           \<subseteq> set (graph_edges (analysis_graph_of res))"
  using assms unfolding analysis_graph_of_def Let_def
  by (auto intro!: bexI[where x = "(u, c)"] bexI[where x = e])

text \<open>
  A step both of whose points the report holds in a context reads and writes, in the
  graph, the globals its footprint names.
\<close>

lemma global_deps_in_analysis_graph:
  fixes res defines "G \<equiv> (\<lambda>y. y \<in> set (report_global_names res))"
  assumes e: "(u, a, v) \<in> set (cfg_intra_list (report_cfg res))"
    and u: "(u, c) \<in> set (report_rows_of res)" and v: "(v, c) \<in> set (report_rows_of res)"
  shows "x \<in> set (edge_global_reads G a)
           \<Longrightarrow> (Global_Node x, Global_Read, Local_Node v c) \<in> set (graph_edges (analysis_graph_of res))"
    and "x \<in> set (edge_global_writes G a)
           \<Longrightarrow> (Local_Node v c, Global_Write, Global_Node x) \<in> set (graph_edges (analysis_graph_of res))"
proof -
  have deps: "set (intra_deps G (report_rows_of res) u c (u, a, v))
                \<subseteq> set (graph_edges (analysis_graph_of res))"
    unfolding G_def by (rule intra_deps_in_analysis_graph[OF u e])
  show "x \<in> set (edge_global_reads G a)
          \<Longrightarrow> (Global_Node x, Global_Read, Local_Node v c) \<in> set (graph_edges (analysis_graph_of res))"
    using deps v by (auto simp: intra_deps_def)
  show "x \<in> set (edge_global_writes G a)
          \<Longrightarrow> (Local_Node v c, Global_Write, Global_Node x) \<in> set (graph_edges (analysis_graph_of res))"
    using deps v by (auto simp: intra_deps_def)
qed

text \<open>
  So the graph is read off the report alone: its local nodes are the reported rows
  (@{thm [source] local_node_in_analysis_graph}), its global nodes the keyed program
  globals (@{thm [source] global_node_in_analysis_graph}), and its global edges the
  footprints of the keyed lifter (@{thm [source] global_deps_in_analysis_graph}).
\<close>

end
