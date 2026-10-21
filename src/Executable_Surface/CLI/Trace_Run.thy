theory Trace_Run
  imports
    Analysis_Render
    "Voblint_Solver.Solver_Trace"
begin

section \<open>The solver trace of one run\<close>

text \<open>
  \<^theory>\<open>Voblint_Solver.Solver_Trace\<close> gives the executable solver a traced copy.
  This theory adds the two things only a run knows: which context each call is
  routed to, and how to read the solver's unknowns and values back as the result
  reads them. It assembles them into \<open>run_voblint_traced\<close>, which is
  \<^const>\<open>run_voblint\<close> in the logic and the only exported entry point whose code
  reaches \<^const>\<open>trace_event\<close>. \<^const>\<open>run_voblint\<close> itself keeps its own code
  equations and runs no hook.
\<close>

subsection \<open>Routing\<close>

text \<open>
  A route receives the calling unknown's node and context and the entry state,
  and returns the callee's context. The traced run wraps each context policy's
  route so that it reports that triple.
\<close>

datatype ('x, 'l, 'c) route_event = Ev_Route 'x 'l 'c

definition traced_route ::
    "(pp \<Rightarrow> 'c \<Rightarrow> 'l \<Rightarrow> call_action \<Rightarrow> 'c) \<Rightarrow> pp \<Rightarrow> 'c \<Rightarrow> 'l \<Rightarrow> call_action \<Rightarrow> 'c" where
  "traced_route route u ctx d ca =
    (let c = route u ctx d ca; _ = trace_event STR ''route'' (\<lambda>_. Ev_Route (u, ctx) d c) in c)"

lemma traced_route_eq [simp]: "traced_route route = route"
  by (simp add: fun_eq_iff traced_route_def trace_event_def Let_def)

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

text \<open>
  Each context mode fixes the types of its contexts and global unknowns; they are
  spelled out, since a type variable left free in a code equation's right-hand
  side makes code export drop the equation.
\<close>

text \<open>
  The traced report is \<^const>\<open>analysis_report_of\<close> with a run event carrying the
  printers, the traced solve \<^const>\<open>solve_c_traced\<close> in place of
  \<^const>\<open>mcp_solve_c\<close>, and every route wrapped by \<^const>\<open>traced_route\<close>.
\<close>

fun analysis_report_traced :: "analysis_config \<Rightarrow> imp_prog \<Rightarrow> analysis_report option" where
  "analysis_report_traced (Analysis_Config as r Ctx_None pg) p =
     (let _ = trace_event STR ''run''
                (\<lambda>_. mcp_trace_printers pg as p (\<lambda>_ :: unit. Context_Unit)) in
      map_option
       (\<lambda>sol. report_of (Analysis_Config as r Ctx_None pg) (\<lambda>_. Key_List []) (\<lambda>_. Report_Unit)
          (mcp_classify (activation as))
          (mcp_run_of (activation as) pg Analysis_Global Activation_Seed
             (\<lambda>_. traced_route route_unit) (declared_global p) p sol) p)
       (solve_c_traced r
          (mcp_equations (activation as) pg Analysis_Buffer Analysis_Global Activation_Seed
             (\<lambda>_. traced_route route_unit) () (declared_global p) p)
          (cfg_exit (prog_cfg p), ())))"
| "analysis_report_traced (Analysis_Config as r Ctx_EntryState pg) p =
     (let _ = trace_event STR ''run''
                (\<lambda>_. mcp_trace_printers pg as p
                       (\<lambda>ctx. Context_Entry (mcp_ctx_values (activation as) ctx))) in
      map_option
       (\<lambda>sol. report_of (Analysis_Config as r Ctx_EntryState pg)
          (entry_ctx_key (activation as)) Report_Entry (mcp_classify (activation as))
          (mcp_run_of (activation as) pg Analysis_Global Activation_Seed
             (\<lambda>G. traced_route (mcp_formals_route (activation as) G)) (declared_global p) p sol) p)
       (solve_c_traced r
          (mcp_equations (activation as) pg Analysis_Buffer Analysis_Global Activation_Seed
             (\<lambda>G. traced_route (mcp_formals_route (activation as) G)) mcp_root_ctx
             (declared_global p) p)
          (cfg_exit (prog_cfg p), mcp_root_ctx)))"
| "analysis_report_traced (Analysis_Config as r (Ctx_CallString k) pg) p =
     (let _ = trace_event STR ''run''
                (\<lambda>_. mcp_trace_printers pg as p Context_Call_String) in
      map_option
       (\<lambda>sol. report_of (Analysis_Config as r (Ctx_CallString k) pg)
          (\<lambda>ctx. Key_List (map Key_Node ctx)) Report_Call_String
          (mcp_classify (activation as))
          (mcp_run_of (activation as) pg Analysis_Global Activation_Seed
             (\<lambda>_. traced_route (cs_route k)) (declared_global p) p sol) p)
       (solve_c_traced r
          (mcp_equations (activation as) pg Analysis_Buffer Analysis_Global Activation_Seed
             (\<lambda>_. traced_route (cs_route k)) [] (declared_global p) p)
          (cfg_exit (prog_cfg p), [])))"

lemma analysis_report_traced_eq: "analysis_report_traced config p = analysis_report_of config p"
  by (induct config p rule: analysis_report_of.induct)
     (simp_all add: Let_def trace_event_def solve_c_traced_eq mcp_solve_c_def)

subsection \<open>The traced run\<close>

text \<open>
  The run the command-line tool's \<open>--trace\<close> and the playground's trace replay call.
  It answers exactly as \<^const>\<open>run_voblint\<close> (\<open>run_voblint_traced_eq\<close>), so every
  theorem about \<^const>\<open>run_voblint\<close> covers its answer.
\<close>

definition run_voblint_traced ::
  "analysis_config \<Rightarrow> imp_prog \<Rightarrow> analysis_report analysis_answer"
where
  "run_voblint_traced config p =
     (if \<not> valid_config config then Invalid_Activation
      else if \<not> wf_program_compile_input_exec p then Malformed_Program
      else case analysis_report_traced config p of
             None \<Rightarrow> No_Answer
           | Some res \<Rightarrow> Analysed res)"

theorem run_voblint_traced_eq: "run_voblint_traced = run_voblint"
  by (simp add: fun_eq_iff run_voblint_traced_def run_voblint_def analysis_report_traced_eq)

subsection \<open>The hook\<close>

text \<open>
  \<^const>\<open>trace_event\<close> is \<open>()\<close> in the logic. The exported OCaml calls
  \<open>Solver_trace_hook.emit\<close> instead, which records the event only when tracing
  is on, forcing the suspension then and only then, and returns \<open>()\<close>. This
  mapping is trusted in the same way as every other target-language mapping: the
  hook must return, raise nothing and leave the solver's values alone. Only the
  traced constants above name \<^const>\<open>trace_event\<close>, so only
  \<open>run_voblint_traced\<close> relies on this mapping. No mapping exists for the Eval
  target, so evaluation in proofs runs the equation.
\<close>

code_printing constant trace_event \<rightharpoonup> (OCaml) "Solver'_trace'_hook.emit"

end
