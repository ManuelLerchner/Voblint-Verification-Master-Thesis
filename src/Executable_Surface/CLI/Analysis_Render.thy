theory Analysis_Render
  imports Analysis_Run
begin

section \<open>The analysis graph\<close>

text \<open>
  The report's states are filed by point \<^emph>\<open>and\<close> context, so the graph a reader sees of
  them has a node per such pair, where the CFG has one per point. A flow-insensitive
  program global adds a node of its own. The edges are the dependencies the equations
  have between those unknowns: a step within a context, a call entering the contexts
  the report routes it to, the callee's result resuming the caller, the call's
  continuation, and the reads and writes of each global, by the same footprints the
  keyed lifter reads and publishes (\<^const>\<open>gedge_global_reads\<close>,
  \<^const>\<open>gedge_global_writes\<close>, \<^const>\<open>gcall_global_reads\<close>). It is a projection of the
  report, as the rendering below is, and no soundness theorem reads it.
\<close>

datatype 'n unknown_node = Local_Node pp nat | Global_Node 'n

datatype ('vr, 'e) analysis_edge =
    Intra_Dep "('vr, 'e) gedge_action"
  | Enter_Dep "('vr, 'e) gcall_action"
  | Combine_Dep "('vr, 'e) gcall_action"
  | Continue_Dep "('vr, 'e) gcall_action"
  | Global_Read
  | Global_Write

record ('vr, 'e, 'n) analysis_graph =
  graph_nodes :: "'n unknown_node list"
  graph_edges :: "('n unknown_node \<times> ('vr, 'e) analysis_edge \<times> 'n unknown_node) list"

text \<open>
  Which global names an edge or a call reads and writes depends on the language, so the
  graph takes these footprints as an argument.
\<close>

record ('vr, 'e, 'n) footprints =
  fp_edge_reads :: "('n \<Rightarrow> bool) \<Rightarrow> ('vr, 'e) gedge_action \<Rightarrow> 'n list"
  fp_edge_writes :: "('n \<Rightarrow> bool) \<Rightarrow> ('vr, 'e) gedge_action \<Rightarrow> 'n list"
  fp_call_reads :: "('n \<Rightarrow> bool) \<Rightarrow> 'e list \<Rightarrow> 'n list"
  fp_call_writes :: "('n \<Rightarrow> bool) \<Rightarrow> ('vr, 'e) gcall_action \<Rightarrow> 'n list"
text \<open>The program globals the report keeps at unknowns of their own.\<close>

definition report_global_names :: "('k, 'x, 'vr, 'e, 'n, 's) analysis_report \<Rightarrow> 'n list" where
  "report_global_names res =
     concat (map (\<lambda>g. case global_unknown g of Global_Named x \<Rightarrow> [x] | _ \<Rightarrow> []) (report_globals res))"

definition report_rows_of :: "('k, 'x, 'vr, 'e, 'n, 's) analysis_report \<Rightarrow> (pp \<times> nat) list" where
  "report_rows_of res = map (\<lambda>st. (state_point st, state_context st)) (report_states res)"

definition report_route_targets ::
    "('k, 'x, 'vr, 'e, 'n, 's) analysis_report \<Rightarrow> pp \<Rightarrow> nat \<Rightarrow> nat list" where
  "report_route_targets res u c =
     concat (map route_targets
       (filter (\<lambda>r. route_point r = u \<and> route_context r = c) (report_routes res)))"

definition callee_of :: "pp \<Rightarrow> pname" where
  "callee_of entry = (case entry of FunctionEntry f \<Rightarrow> f | FunctionResult f \<Rightarrow> f | Statement _ \<Rightarrow> STR '''')"

text \<open>What a step within one context adds: the step, and the globals it reads and writes.\<close>

definition intra_deps ::
    "('vr, 'e, 'n) footprints \<Rightarrow> ('n \<Rightarrow> bool) \<Rightarrow> (pp \<times> nat) list \<Rightarrow> pp \<Rightarrow> nat
     \<Rightarrow> pp \<times> ('vr, 'e) gedge_action \<times> pp
     \<Rightarrow> ('n unknown_node \<times> ('vr, 'e) analysis_edge \<times> 'n unknown_node) list" where
  "intra_deps fp G rows u c e =
     (case e of (u', a, v) \<Rightarrow>
        if u' = u \<and> (v, c) \<in> set rows
        then (Local_Node u c, Intra_Dep a, Local_Node v c)
             # map (\<lambda>x. (Global_Node x, Global_Read, Local_Node v c)) (fp_edge_reads fp G a)
             @ map (\<lambda>x. (Local_Node v c, Global_Write, Global_Node x)) (fp_edge_writes fp G a)
        else [])"

text \<open>
  What a call adds: an entry into every context the report routes it to, the callee's
  result resuming the caller from each, and the continuation. The continuation's
  equation evaluates the call, so it reads the globals the arguments mention and
  writes a global destination or formal.
\<close>

definition call_deps ::
    "('vr, 'e, 'n) footprints \<Rightarrow> ('k, 'x, 'vr, 'e, 'n, 's) analysis_report \<Rightarrow> ('n \<Rightarrow> bool)
     \<Rightarrow> (pp \<times> nat) list \<Rightarrow> pp \<Rightarrow> nat \<Rightarrow> pp \<times> ('vr, 'e) gcall_action \<times> pp \<times> pp
     \<Rightarrow> ('n unknown_node \<times> ('vr, 'e) analysis_edge \<times> 'n unknown_node) list" where
  "call_deps fp res G rows u c e =
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
                      # map (\<lambda>x. (Global_Node x, Global_Read, Local_Node after c))
                          (fp_call_reads fp G (ce_args ca))
                      @ map (\<lambda>x. (Local_Node after c, Global_Write, Global_Node x))
                          (fp_call_writes fp G ca)
                 else [])))"

definition analysis_graph_of ::
    "('vr::linorder, 'e::linorder, 'n) footprints \<Rightarrow> ('k, 'x, 'vr, 'e, 'n, 's) analysis_report
       \<Rightarrow> ('vr, 'e, 'n) analysis_graph" where
  "analysis_graph_of fp res =
     (let g = report_cfg res;
          rows = report_rows_of res;
          names = report_global_names res;
          G = (\<lambda>x. x \<in> set names)
      in \<lparr> graph_nodes = map (\<lambda>(v, c). Local_Node v c) rows @ map Global_Node names,
           graph_edges =
             concat (map (\<lambda>e. concat (map (\<lambda>(u, c). intra_deps fp G rows u c e) rows))
               (cfg_intra_list g))
             @ concat (map (\<lambda>e. concat (map (\<lambda>(u, c). call_deps fp res G rows u c e) rows))
                 (cfg_calls_list g))
             @ concat (map (\<lambda>(u, c).
                 if u = cfg_entry g
                 then map (\<lambda>x. (Local_Node u c, Global_Write, Global_Node x)) names else [])
               rows) \<rparr>)"

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

type_synonym ('d, 'v) analysis_view = "('d \<times> 'v field_state) list"

text \<open>
  The states a report holds at a point, joined over its contexts: what a reader who
  ignores contexts can say about the point. It may be coarser than the states it
  joins, but every store any of them describes, it describes too.
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


definition report_point_join ::
    "('k, 'x, 'vr, 'e, 'n, 's::join_val) analysis_report \<Rightarrow> pp \<Rightarrow> 's lifted" where
  "report_point_join res v =
     fold vjoin (map state_value (filter (\<lambda>st. state_point st = v) (report_states res))) Bot"

text \<open>
  What a point's outgoing steps produce, joined over its contexts the same way. Every
  context lists the point's steps in the order of its outgoing edges, so the lists are
  joined position by position.
\<close>

definition report_steps_join ::
    "('k, 'x, 'vr, 'e, 'n, 's::join_val) analysis_report \<Rightarrow> pp \<Rightarrow> (pp \<times> 's lifted) list" where
  "report_steps_join res v =
     (case map state_steps (filter (\<lambda>st. state_point st = v) (report_states res)) of
        [] \<Rightarrow> []
      | s # ss \<Rightarrow> fold (map2 (\<lambda>(w, a) (_, b). (w, vjoin a b))) ss s)"

lemma report_point_join_sup:
  fixes res :: "('k, 'x, 'vr, 'e, 'n, 's::join_val_sup) analysis_report"
  shows "report_point_join res v =
     fold (\<squnion>) (map state_value (filter (\<lambda>st. state_point st = v) (report_states res))) Bot"
  unfolding report_point_join_def by (simp add: vjoin_sup[abs_def])

record ('vr, 'e, 'n, 'd, 'v) run_result =
  res_cfg :: "('vr, 'e) gcfg"
  res_contexts :: "'v analysis_context list"
  res_states :: "('e, ('d, 'v) analysis_view) result_state list"
  res_joined :: "(pp \<times> ('d, 'v) analysis_view lifted \<times> (pp \<times> ('d, 'v) analysis_view lifted) list) list"
  res_routes :: "call_route list"
  res_checks :: "'e result_check list"
  res_globals :: "('n, ('d, 'v) analysis_view) result_global list"
  res_diagnostics :: "'e arithmetic_diagnostic list"
  res_graph :: "('vr, 'e, 'n) analysis_graph"

definition map_analysis_view :: "('v \<Rightarrow> 'w) \<Rightarrow> ('d, 'v) analysis_view \<Rightarrow> ('d, 'w) analysis_view" where
  "map_analysis_view f = map (\<lambda>(a, s). (a, map_field_state f s))"

text \<open>
  What a language shows of its report: each active analysis's part of a state, the
  values an entry-state context is keyed by, and the global footprints of its edges.
  The printer \<open>show\<close> is a parameter, composed in the adapter with whatever
  post-processing its output needs.
\<close>

record ('k, 'm, 's, 'vr, 'e, 'n, 'd, 'a) report_renderer =
  rr_view :: "'k \<Rightarrow> 'vr list \<Rightarrow> 's \<Rightarrow> ('d, 'a) analysis_view"
  rr_context :: "'k \<Rightarrow> 'm \<Rightarrow> 'a list"
  rr_footprints :: "('vr, 'e, 'n) footprints"

fun render_context :: "('a \<Rightarrow> 'v) \<Rightarrow> ('m \<Rightarrow> 'a list) \<Rightarrow> 'm report_context \<Rightarrow> 'v analysis_context"
where
  "render_context show vals Report_Unit = Context_Unit"
| "render_context show vals (Report_Entry ctx) = Context_Entry (map show (vals ctx))"
| "render_context show vals (Report_Call_String us) = Context_Call_String us"

definition render_report ::
    "('k, 'm, 's::join_val, 'vr::linorder, 'e::linorder, 'n, 'd, 'a) report_renderer
       \<Rightarrow> ('a \<Rightarrow> 'v) \<Rightarrow> ('k, 'm report_context, 'vr, 'e, 'n, 's) analysis_report
       \<Rightarrow> ('vr, 'e, 'n, 'd, 'v) run_result" where
  "render_report rr show res =
     (let config = report_config res;
          state = map_analysis_view show \<circ> rr_view rr config (report_vars res)
      in \<lparr> res_cfg = report_cfg res,
           res_contexts = map (render_context show (rr_context rr config)) (report_contexts res),
           res_states = map (map_result_state state) (report_states res),
           res_joined = map (\<lambda>v. (v, map_lift state (report_point_join res v),
                                  map (\<lambda>(w, s). (w, map_lift state s)) (report_steps_join res v)))
                          (cfg_node_list (report_cfg res)),
           res_routes = report_routes res,
           res_checks = report_checks res,
           res_globals = map (map_result_global state) (report_globals res),
           res_diagnostics = report_diagnostics res,
           res_graph = analysis_graph_of (rr_footprints rr) res \<rparr>)"


lemma render_report_columns [simp]:
  "res_cfg (render_report rr show res) = report_cfg res"
  "res_checks (render_report rr show res) = report_checks res"
  "res_diagnostics (render_report rr show res) = report_diagnostics res"
  "res_routes (render_report rr show res) = report_routes res"
  by (simp_all add: render_report_def Let_def)

section \<open>What the analysis graph contains\<close>

text \<open>
  The graph's nodes are exactly the report's unknowns, and a step between two reported
  points of one context carries the global reads and writes its footprint names.
\<close>

lemma local_node_in_analysis_graph:
  "Local_Node v c \<in> set (graph_nodes (analysis_graph_of fp res))
     \<longleftrightarrow> (\<exists>st \<in> set (report_states res). state_point st = v \<and> state_context st = c)"
  by (auto simp: analysis_graph_of_def report_rows_of_def Let_def)

lemma global_node_in_analysis_graph:
  "Global_Node x \<in> set (graph_nodes (analysis_graph_of fp res))
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
  shows "set (intra_deps fp (\<lambda>y. y \<in> set (report_global_names res)) (report_rows_of res) u c e)
           \<subseteq> set (graph_edges (analysis_graph_of fp res))"
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
  shows "x \<in> set (fp_edge_reads fp G a)
           \<Longrightarrow> (Global_Node x, Global_Read, Local_Node v c) \<in> set (graph_edges (analysis_graph_of fp res))"
    and "x \<in> set (fp_edge_writes fp G a)
           \<Longrightarrow> (Local_Node v c, Global_Write, Global_Node x) \<in> set (graph_edges (analysis_graph_of fp res))"
proof -
  have deps: "set (intra_deps fp G (report_rows_of res) u c (u, a, v))
                \<subseteq> set (graph_edges (analysis_graph_of fp res))"
    unfolding G_def by (rule intra_deps_in_analysis_graph[OF u e])
  show "x \<in> set (fp_edge_reads fp G a)
          \<Longrightarrow> (Global_Node x, Global_Read, Local_Node v c) \<in> set (graph_edges (analysis_graph_of fp res))"
    using deps v by (auto simp: intra_deps_def)
  show "x \<in> set (fp_edge_writes fp G a)
          \<Longrightarrow> (Local_Node v c, Global_Write, Global_Node x) \<in> set (graph_edges (analysis_graph_of fp res))"
    using deps v by (auto simp: intra_deps_def)
qed

text \<open>
  So the graph is read off the report alone: its local nodes are the reported rows
  (@{thm [source] local_node_in_analysis_graph}), its global nodes the keyed program
  globals (@{thm [source] global_node_in_analysis_graph}), and its global edges the
  footprints of the keyed lifter (@{thm [source] global_deps_in_analysis_graph}).
\<close>

end
