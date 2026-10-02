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

record 'v run_result =
  res_cfg :: cfg
  res_contexts :: "'v analysis_context list"
  res_states :: "'v analysis_view result_state list"
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
