theory Trace_Run
  imports
    Analysis_Render
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
  as the result shows it, a global unknown as the node-owned buffer, a program
  global, or the seed of a procedure entry in a context, a solver value's local
  part as a state, a global unknown's value as the globals it describes, and an
  entry value as a state. With shared program globals a local value holds its
  globals at bottom by construction, which the emptiness check would read as
  unreachable; it is shown without that check and without the globals, and a
  program global's unknown shows that global alone.
\<close>

datatype 'c trace_key = Trace_Buffer | Trace_Global vname | Trace_Seed cfg_node 'c

datatype ('c, 'g, 'd, 'l) trace_printers = Trace_Printers
  "'c \<Rightarrow> abstract_value analysis_context"
  "'g \<Rightarrow> 'c trace_key"
  "'d \<Rightarrow> abstract_value analysis_view lifted"
  "vname option \<Rightarrow> 'd \<Rightarrow> abstract_value analysis_view lifted"
  "'l \<Rightarrow> abstract_value analysis_view lifted"

fun key_of_global_unknown :: "(vname, 'c) global_unknown \<Rightarrow> 'c trace_key" where
  "key_of_global_unknown Analysis_Buffer = Trace_Buffer"
| "key_of_global_unknown (Analysis_Global x) = Trace_Global x"
| "key_of_global_unknown (Activation_Seed n c) = Trace_Seed n c"

definition mcp_trace_printers ::
    "program_globals \<Rightarrow> analysis_domain list \<Rightarrow> imp_prog
       \<Rightarrow> ('c \<Rightarrow> abstract_value analysis_context)
       \<Rightarrow> ('c, (vname, 'c) global_unknown, (mcp_st lifted, mcp_st lifted) dg_state, mcp_st lifted)
            trace_printers" where
  "mcp_trace_printers pg as p ctx_view =
     (let raw = (\<lambda>vs d. map_lift (mcp_render (activation as) vs)
                         (map_lift (mcp_rd (declared_global p)) d));
          view = (\<lambda>d. raw (program_vars p) (canonicalize_lift (mcp_emp (activation as) p) d));
          local = (case pg of
                     Program_Globals_Flow_Sensitive \<Rightarrow> view
                   | Program_Globals_Flow_Insensitive \<Rightarrow>
                       raw (filter (\<lambda>x. \<not> declared_global p x) (program_vars p)));
          globals = (\<lambda>n. case n of
                       None \<Rightarrow> filter (declared_global p) (program_vars p)
                     | Some x \<Rightarrow> [x])
      in Trace_Printers ctx_view key_of_global_unknown (\<lambda>d. local (dg_local d))
           (\<lambda>n d. raw (globals n) (dg_global d)) local)"

lemma trace_run:
  "f = rhs \<Longrightarrow> f = (let _ = trace_event STR ''run'' e in rhs)"
  by (simp add: trace_event_def Let_def)

text \<open>
  Each context mode fixes the types of its contexts and global unknowns; they are
  spelled out, since a type variable left free in a code equation's right-hand
  side makes code export drop the equation.
\<close>

text \<open>
  The solve itself is \<^const>\<open>mcp_solve_c\<close>; its traced form adds the start and stop
  events around it, and is the same function in the logic.
\<close>

lemma mcp_solve_c_traced: "mcp_solve_c r T x = solve_c_traced r T x"
  by (simp add: mcp_solve_c_def solve_c_traced_eq)

declare mcp_solve_c_def [code del]
declare mcp_solve_c_traced [code]

lemmas analysis_report_of_traced =
  trace_run[OF analysis_report_of.simps(1)[of as r pg p],
    of "\<lambda>_. mcp_trace_printers pg as p (\<lambda>_ :: unit. Context_Unit)"]
  trace_run[OF analysis_report_of.simps(2)[of as r pg p],
    of "\<lambda>_. mcp_trace_printers pg as p (\<lambda>ctx. Context_Entry (mcp_ctx_values (activation as) ctx))"]
  trace_run[OF analysis_report_of.simps(3)[of as r k pg p],
    of "\<lambda>_. mcp_trace_printers pg as p Context_Call_String"]
  for as r k pg p

declare analysis_report_of.simps [code del]
declare analysis_report_of_traced [code]

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
