theory Trace_Run
  imports
    Analysis_Run
    "Voblint_Solver.Solver_Trace"
begin

section \<open>The solver trace of one run\<close>

text \<open>
  \<^theory>\<open>Voblint_Solver.Solver_Trace\<close> makes the executable solver report its
  steps. This theory adds the two things only a run knows: which context each
  call is routed to, and how to read the solver's unknowns and values back as
  the result reads them. Both are again alternative code equations, proved
  equal to the equations they replace, and \<^const>\<open>trace_event\<close> is mapped to
  the OCaml hook here, where the exported program is assembled.
\<close>

subsection \<open>Routing\<close>

text \<open>
  A route receives the calling unknown's node and context and the entry value,
  and returns the callee's context. Each routing policy the CLI runs reports
  that triple from its own equation.
\<close>

datatype ('x, 'l, 'c) route_event = Ev_Route 'x 'l 'c

lemma route_unit_traced:
  "route_unit u ctx d ca =
    (let c = (); _ = trace_event STR ''route'' (\<lambda>_. Ev_Route (u, ctx) d c) in c)"
  by (simp add: trace_event_def Let_def)

lemma cs_route_traced:
  "cs_route k u ctx d ca =
    (let c = take k (u # ctx); _ = trace_event STR ''route'' (\<lambda>_. Ev_Route (u, ctx) d c) in c)"
  by (simp add: cs_route_def trace_event_def Let_def)

text \<open>The formals route is generated per analysis registry, so it is wrapped, not restated.\<close>

lemma trace_route:
  fixes route :: "pp \<Rightarrow> 'c \<Rightarrow> 'l \<Rightarrow> call_action \<Rightarrow> 'c"
    and route_rhs :: "pp \<Rightarrow> 'c \<Rightarrow> 'l \<Rightarrow> call_action \<Rightarrow> 'c"
  assumes "\<And>u ctx d ca. route u ctx d ca = route_rhs u ctx d ca"
  shows "route u ctx d ca =
    (let c = route_rhs u ctx d ca; _ = trace_event STR ''route'' (\<lambda>_. Ev_Route (u, ctx) d c) in c)"
  using assms by (simp add: trace_event_def Let_def)

lemmas mcp_formals_route_traced =
  trace_route[where route = "mcp_formals_route as G", OF mcp_formals_route_def] for as G

declare route_unit_def [code del] cs_route_def [code del] mcp_formals_route_def [code del]
declare route_unit_traced [code] cs_route_traced [code] mcp_formals_route_traced [code]

subsection \<open>Reading unknowns and values back\<close>

text \<open>
  The solver is generic in its unknowns and values. Where a run fixes them, it
  hands the trace the functions that read them as the result does: a context
  as the result shows it, a global unknown as the analysis global or the seed
  of a procedure entry in a context, a solver value's local or global part as a
  state, and an entry value as a state.
\<close>

datatype ('c, 'g, 'd, 'l) trace_printers = Trace_Printers
  "'c \<Rightarrow> abstract_value analysis_context"
  "'g \<Rightarrow> (cfg_node \<times> 'c) option"
  "'d \<Rightarrow> abstract_value analysis_view lifted"
  "'d \<Rightarrow> abstract_value analysis_view lifted"
  "'l \<Rightarrow> abstract_value analysis_view lifted"

fun seed_of_global_unknown :: "('v, 'c) global_unknown \<Rightarrow> (cfg_node \<times> 'c) option" where
  "seed_of_global_unknown (Analysis_Global _) = None"
| "seed_of_global_unknown (Activation_Seed n c) = Some (n, c)"

fun seed_of_call_string_gk :: "call_string_gk \<Rightarrow> (cfg_node \<times> call_string) option" where
  "seed_of_call_string_gk Call_String_Context.Global = None"
| "seed_of_call_string_gk (Call_String_Context.Seed n c) = Some (n, c)"

definition mcp_trace_printers ::
    "analysis_domain list \<Rightarrow> imp_prog \<Rightarrow> ('c \<Rightarrow> abstract_value analysis_context)
       \<Rightarrow> ('g \<Rightarrow> (cfg_node \<times> 'c) option)
       \<Rightarrow> ('c, 'g, (mcp_st lifted, mcp_st lifted) dg_state, mcp_st lifted) trace_printers" where
  "mcp_trace_printers as p ctx_view seed_of =
     (let view = (\<lambda>d. map_lift (mcp_render (activation as) (program_vars p))
                    (map_lift (mcp_rd (declared_global p))
                      (canonicalize_lift (mcp_emp (activation as) p) d)))
      in Trace_Printers ctx_view seed_of (\<lambda>d. view (dg_local d)) (\<lambda>d. view (dg_global d)) view)"

lemma trace_run:
  "f = rhs \<Longrightarrow> f = (let _ = trace_event STR ''run'' e in rhs)"
  by (simp add: trace_event_def Let_def)

text \<open>
  Each context mode fixes the types of its contexts and global unknowns; they are
  spelled out, since a type variable left free in a code equation's right-hand
  side makes code export drop the equation.
\<close>

lemmas analysis_result_traced =
  trace_run[OF analysis_result.simps(1)[of as r p],
    of "\<lambda>_. mcp_trace_printers as p (\<lambda>_ :: unit. Context_Unit)
          (seed_of_global_unknown :: (unit, unit) global_unknown \<Rightarrow> _)"]
  trace_run[OF analysis_result.simps(2)[of as r p],
    of "\<lambda>_. mcp_trace_printers as p (\<lambda>ctx. Context_Entry (mcp_ctx_values (activation as) ctx))
          (seed_of_global_unknown :: (unit, mcp_ctx) global_unknown \<Rightarrow> _)"]
  trace_run[OF analysis_result.simps(3)[of as r k p],
    of "\<lambda>_. mcp_trace_printers as p Context_Call_String seed_of_call_string_gk"]
  for as r k p

declare analysis_result.simps [code del]
declare analysis_result_traced [code]

subsection \<open>The hook\<close>

text \<open>
  \<^const>\<open>trace_event\<close> is \<open>()\<close> in the logic. The exported OCaml calls
  \<open>Solver_trace_hook.emit\<close> instead, which records the event only when tracing
  is on, forcing the suspension then and only then, and returns \<open>()\<close>. This
  mapping is trusted in the same way as every other target-language mapping: the
  hook must return, raise nothing and leave the solver's values alone. No mapping
  exists for the Eval target, so evaluation in proofs runs the equation.
\<close>

code_printing constant trace_event \<rightharpoonup> (OCaml) "Solver'_trace'_hook.emit"

end
