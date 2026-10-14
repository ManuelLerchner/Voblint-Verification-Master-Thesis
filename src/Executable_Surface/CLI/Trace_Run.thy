theory Trace_Run
  imports
    Typed_Report
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
  A route receives the calling unknown's node and context and the entry state,
  and returns the callee's context. A context policy whose route is a definition
  reports that triple from its own equation, by wrapping it.
\<close>

datatype ('x, 'l, 'c) route_event = Ev_Route 'x 'l 'c

lemma trace_route:
  fixes route :: "pp \<Rightarrow> 'c \<Rightarrow> 'l \<Rightarrow> ('v, 'e) gcall_action \<Rightarrow> 'c"
    and route_rhs :: "pp \<Rightarrow> 'c \<Rightarrow> 'l \<Rightarrow> ('v, 'e) gcall_action \<Rightarrow> 'c"
  assumes "\<And>u ctx d ca. route u ctx d ca = route_rhs u ctx d ca"
  shows "route u ctx d ca =
    (let c = route_rhs u ctx d ca; _ = trace_event STR ''route'' (\<lambda>_. Ev_Route (u, ctx) d c) in c)"
  using assms by (simp add: trace_event_def Let_def)


subsection \<open>Reading unknowns and values back\<close>

text \<open>
  The solver is generic in its unknowns and values. Where a run fixes them, it
  hands the trace the functions that read them as the result does: a context
  as the result shows it, a global unknown as the node-owned buffer, a program
  global, or the seed of a procedure entry in a context, a solver value's local
  part as a state, a global unknown's value as the globals it describes, and an
  entry state as a state. With shared program globals a local value holds its
  globals at bottom by construction, which the emptiness check would read as
  unreachable; it is shown without that check and without the globals, and a
  program global's unknown shows that global alone.
\<close>

datatype 'c trace_key = Trace_Buffer | Trace_Global vname | Trace_Seed cfg_node 'c

text \<open>
  The printers hand the trace each analysis by its name and each value as its
  rendering, so one trace reader serves every run, whatever the analyses' values.
\<close>

type_synonym trace_view = "(String.literal, String.literal) analysis_view"

datatype ('c, 'g, 'd, 'l) trace_printers = Trace_Printers
  "'c \<Rightarrow> String.literal analysis_context"
  "'g \<Rightarrow> 'c trace_key"
  "'d \<Rightarrow> trace_view lifted"
  "vname option \<Rightarrow> 'd \<Rightarrow> trace_view lifted"
  "'l \<Rightarrow> trace_view lifted"

definition trace_view_of :: "('a \<Rightarrow> String.literal) \<Rightarrow> ('v \<Rightarrow> String.literal)
    \<Rightarrow> ('a, 'v) analysis_view \<Rightarrow> trace_view" where
  "trace_view_of name text = map (\<lambda>(a, f). (name a, map_field_state text f))"


fun typed_domain_name :: "typed_domain \<Rightarrow> String.literal" where
  "typed_domain_name Typed_Sign = STR ''sign''"
| "typed_domain_name Typed_Interval = STR ''interval''"
| "typed_domain_name (Typed_Int _) = STR ''int''"
| "typed_domain_name Typed_Parity = STR ''parity''"
| "typed_domain_name Typed_Congruence = STR ''congruence''"
| "typed_domain_name Typed_Order = STR ''order''"


text \<open>A typed run names a global's unknown by the global's label.\<close>

fun typed_key_of_global_unknown :: "(var_id, 'c) global_unknown \<Rightarrow> 'c trace_key" where
  "typed_key_of_global_unknown Analysis_Buffer = Trace_Buffer"
| "typed_key_of_global_unknown (Analysis_Global x) = Trace_Global (var_label x)"
| "typed_key_of_global_unknown (Activation_Seed n c) = Trace_Seed n c"


text \<open>A typed run's values are read as its report renders them, each variable by its
  label. The trace also shows the return slot, which carries a callee's result to its
  caller. With the declared globals at their own unknowns, a point's value is shown
  without them and a global's unknown shows that global alone.\<close>

definition typed_trace_printers ::
    "program_globals \<Rightarrow> typed_domain list \<Rightarrow> kind_decls \<Rightarrow> imp_prog
       \<Rightarrow> ('c \<Rightarrow> String.literal analysis_context)
       \<Rightarrow> ('c, (var_id, 'c) global_unknown, (tmcp_st lifted, tmcp_st lifted) dg_state, tmcp_st lifted)
            trace_printers" where
  "typed_trace_printers pg as ds p ctx_view =
     (let raw = (\<lambda>vs d. map_lift (trace_view_of typed_domain_name string_of_typed_value
                                    \<circ> typed_render (tactivation as) vs)
                         (map_lift (tmcp_rd tglobal) d));
          vars = typed_vars (typed_cfg p ds) @ [ReturnVar];
          gs = tdeclared_globals p;
          local = (case pg of
                     Program_Globals_Flow_Sensitive \<Rightarrow> raw vars
                   | Program_Globals_Flow_Insensitive \<Rightarrow> raw (filter (\<lambda>x. x \<notin> set gs) vars));
          globals = (\<lambda>n. case n of None \<Rightarrow> gs | Some x \<Rightarrow> [GlobalId x])
      in Trace_Printers ctx_view typed_key_of_global_unknown (\<lambda>d. local (dg_local d))
           (\<lambda>n d. raw (globals n) (dg_global d)) local)"


text \<open>
  A typed run is traced the same way: its printers are announced before the solve,
  and the solve reports its steps. A call-string context of length zero is shown as no
  context, as the report shows it.
\<close>

declare typed_cs_run_def [code del] typed_es_run_def [code del]

lemma typed_cs_run_traced [code]:
  "typed_cs_run conf k ds p =
     (let sem = conf_sem conf; as = conf_analyses conf; r = conf_globals conf;
          key = (\<lambda>ctx. Key_List (map Key_Node ctx));
          tag = (if k = 0 then (\<lambda>_. Report_Unit) else Report_Call_String);
          root = (cfg_exit (typed_cfg p ds), []);
          _ = trace_event STR ''run''
                (\<lambda>_. typed_trace_printers (conf_program_globals conf) as ds p
                       (if k = 0 then (\<lambda>_ :: cfg_node list. Context_Unit) else Context_Call_String))
      in case conf_program_globals conf of
           Program_Globals_Flow_Sensitive \<Rightarrow>
             map_option (\<lambda>sol. typed_report_of conf ds p [] key tag
                                 (typed_mcp.solved_run_of sem ds as k tglobal p sol))
               (solve_c_traced r (typed_mcp.equations sem ds as k tglobal p) root)
         | Program_Globals_Flow_Insensitive \<Rightarrow>
             (let gs = tdeclared_globals p
              in map_option (\<lambda>sol. typed_report_of conf ds p gs key tag
                                     (typed_mcp_split.solved_run_of sem ds as k gs tglobal p sol))
                   (solve_c_traced r (typed_mcp_split.equations sem ds as k gs tglobal p) root)))"
  by (simp add: typed_cs_run_def solve_c_traced_eq trace_event_def Let_def
      split: program_globals.split)

lemma typed_es_run_traced [code]:
  "typed_es_run conf ds p =
     (let sem = conf_sem conf; as = conf_analyses conf; r = conf_globals conf;
          root = (cfg_exit (typed_cfg p ds), tmcp_root_ctx);
          _ = trace_event STR ''run''
                (\<lambda>_. typed_trace_printers (conf_program_globals conf) as ds p
                       (\<lambda>ctx. Context_Entry (map string_of_typed_value
                                (typed_ctx_values (tactivation as) ctx))))
      in case conf_program_globals conf of
           Program_Globals_Flow_Sensitive \<Rightarrow>
             map_option (\<lambda>sol. typed_report_of conf ds p [] tmcp_ctx_key Report_Entry
                                 (typed_mcp_es.solved_run_of sem ds as tglobal p sol))
               (solve_c_traced r (typed_mcp_es.equations sem ds as tglobal p) root)
         | Program_Globals_Flow_Insensitive \<Rightarrow>
             (let gs = tdeclared_globals p
              in map_option (\<lambda>sol. typed_report_of conf ds p gs tmcp_ctx_key Report_Entry
                                     (typed_mcp_split_es.solved_run_of sem ds as gs tglobal p sol))
                   (solve_c_traced r (typed_mcp_split_es.equations sem ds as gs tglobal p) root)))"
  by (simp add: typed_es_run_def solve_c_traced_eq trace_event_def Let_def
      split: program_globals.split)

declare tmcp_route_def [code del]

lemmas tmcp_route_traced [code] =
  trace_route[where route = "tmcp_route as G", OF tmcp_route_def] for as G

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
