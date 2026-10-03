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

end
