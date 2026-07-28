theory Example_Relational_DG_Demo
  imports
    "Voblint_Analysis.Exec_DG_Bridge"
    "Voblint_Analysis.Rel_Order_Domain"
    "Voblint_Analysis.Interval_DG"
    "Voblint_Analysis.Ivl_Exec"
    "Voblint_Analysis.Solver_Menu"
    "Voblint_Analysis.Analysis_GraphViz"
    "Voblint_CFG.CFG_Prune"
    "Voblint_IMP2.IMP2_Notation"
begin

section \<open>End-to-end demo: a relational analysis on the same executable pipeline as Interval\<close>

text \<open>
  Gap 5 feasibility, execution phase.  \<^file>\<open>../../Analysis/Instances/Mixed/Rel_Order_Domain.thy\<close>
  interprets \<^locale>\<open>sound_dg_spec\<close> over \<open>relc\<close>, a non-\<open>abs_state\<close> relational
  carrier, with zero DG-framework changes -- the mathematical half of the claim.
  This file is the executable half: the same CFG, the same generic \<open>dg_gen_of\<close>
  generator, and the same vendored solver that runs Interval also run \<open>relc\<close>,
  end to end, with a genuinely different observable result.

  \<^bold>\<open>Program.\<close> \<open>if (x < y) { z := 1 } else { z := 0 }\<close>, with \<open>x\<close>/\<open>y\<close> left
  entirely unconstrained at entry (no prior assignment).  This is deliberately
  the case where Interval learns nothing from the guard: \<open>x < y\<close> narrows
  \<open>x\<close>'s interval only using \<open>y\<close>'s \<^emph>\<open>current\<close> upper bound, and vice versa;
  with both at \<open>[-inf,+inf]\<close>, the guard supplies no new bound for either
  variable.  \<open>relc\<close> instead records the pair \<open>(x,y)\<close> directly, because
  \<open>assume_step\<close> reads the guard's syntactic shape, not either variable's
  current abstract value.
\<close>

subsection \<open>The IMP2 source program -- a full program block, not an inline stub\<close>

definition demo_program :: imp_prog where
  "demo_program = program { 
   void main() { 
     if (x < y) 
        { z := 1 } 
     else 
        { z := 0 }
     } 
}"

subsection \<open>CFG construction\<close>

definition demo_pi :: proc_table where
  "demo_pi = prog_table demo_program"

definition demo_cfg :: cfg where
  "demo_cfg = compile_prog demo_pi (prog_procs demo_program) prog_main_name (prog_main demo_program)"

lemma demo_cfg_eq:
  "demo_cfg =
     \<lparr> intra =
         {(FunctionEntry ''main'', EA_Nop, Statement 0),
          (Statement 0, EA_Assume (Less (BaseN (AExp.V ''x'')) (BaseN (AExp.V ''y''))), Statement 1),
          (Statement 0, EA_AssumeNot (Less (BaseN (AExp.V ''x'')) (BaseN (AExp.V ''y''))), Statement 2),
          (Statement 1, EA_Assign ''z'' (BaseN (AExp.N 1)), Statement 3),
          (Statement 2, EA_Assign ''z'' (BaseN (AExp.N 0)), Statement 3),
          (Statement 3, EA_Ret None ''main'', FunctionResult ''main'')},
       calls = {},
       cfg_entry = FunctionEntry ''main'' \<rparr>"
  unfolding demo_cfg_def demo_pi_def demo_program_def by eval

lemma demo_calls: "calls demo_cfg = {}" by (simp add: demo_cfg_eq)
lemma demo_finE: "finite (intra demo_cfg)" by (simp add: demo_cfg_eq)
lemma demo_finC: "finite (calls demo_cfg)" by (simp add: demo_calls)

text \<open>\<open>Statement 1\<close> is the true branch of the guard, right after the
  \<open>assume\<close> and before \<open>z := 1\<close> -- exactly where \<open>x < y\<close> is freshly known
  and nothing else has happened yet.  This is the read point both analyses
  are compared at.\<close>

subsection \<open>Interval, on the same CFG, same generator, same solver menu\<close>

definition demo_ivl_eqs ::
  "pp \<times> unit \<Rightarrow> (pp \<times> unit, unit, (ivl st, ivl st) dg_state) strategy_tree" where
  "demo_ivl_eqs =
     dg_gen_of (unit_dg_spec_st ivl_tf_st ivl_enter_st) demo_cfg
       bot top_ivl_st (restrict_global_st top_ivl_st)"

definition demo_ivl_sol ::
  "(pp \<times> unit) set \<times> (pp \<times> unit + unit \<Rightarrow> (ivl st, ivl st) dg_state)" where
  "demo_ivl_sol = TD_side_always_join_Interp_solve demo_ivl_eqs (cfg_exit demo_cfg, ())"

lemma demo_ivl_terminates:
  "TD_side_always_join_Interp_solve_c demo_ivl_eqs (cfg_exit demo_cfg, ()) \<noteq> None"
  by eval

subsection \<open>The relational analysis, on the very same CFG, generator, and solver\<close>

text \<open>\<open>rel_order_spec\<close> is already both the sound \<^emph>\<open>and\<close> the executable
  specification -- \<open>relc\<close> needed no \<open>Exec_St.thy\<close>-style refinement layer,
  so \<open>dg_gen_of\<close> is applied to it directly, with no bridging step and no
  parallel generator.\<close>

definition demo_rel_eqs ::
  "pp \<times> unit \<Rightarrow> (pp \<times> unit, unit, (relc, relc) dg_state) strategy_tree" where
  "demo_rel_eqs = dg_gen_of rel_order_spec demo_cfg bot top_relc top_relc"

definition demo_rel_sol ::
  "(pp \<times> unit) set \<times> (pp \<times> unit + unit \<Rightarrow> (relc, relc) dg_state)" where
  "demo_rel_sol = TD_side_always_join_Interp_solve demo_rel_eqs (cfg_exit demo_cfg, ())"

lemma demo_rel_terminates:
  "TD_side_always_join_Interp_solve_c demo_rel_eqs (cfg_exit demo_cfg, ()) \<noteq> None"
  by eval

subsection \<open>The comparison\<close>

text \<open>Interval's bound for \<open>x\<close> (and, symmetrically, \<open>y\<close>) at the true branch
  is unchanged from entry: the guard supplied no new information because
  neither operand had a finite bound for the other to narrow against.\<close>

lemma demo_ivl_x_at_branch:
  "lookup_st (locals (snd demo_ivl_sol (Inl (Statement 1, ())))) ''x'' = Ivl MinInf PlusInf"
  unfolding demo_ivl_sol_def demo_ivl_eqs_def by eval

lemma demo_ivl_y_at_branch:
  "lookup_st (locals (snd demo_ivl_sol (Inl (Statement 1, ())))) ''y'' = Ivl MinInf PlusInf"
  unfolding demo_ivl_sol_def demo_ivl_eqs_def by eval

text \<open>\<open>relc\<close>, at the very same point, has recorded the pair directly.\<close>

lemma demo_rel_learns_xy:
  "relc_has ''x'' ''y'' (locals (snd demo_rel_sol (Inl (Statement 1, ()))))"
  unfolding demo_rel_sol_def demo_rel_eqs_def by eval

text \<open>Side by side, evaluated in one call: Interval's two bounds stay
  \<open>[-inf,+inf]\<close>; \<open>relc\<close> answers \<open>True\<close> for the pair \<open>(x,y)\<close>.\<close>

value "(lookup_st (locals (snd demo_ivl_sol (Inl (Statement 1, ())))) ''x'',
        lookup_st (locals (snd demo_ivl_sol (Inl (Statement 1, ())))) ''y'',
        relc_has ''x'' ''y'' (locals (snd demo_rel_sol (Inl (Statement 1, ())))))"

subsection \<open>Rendering the CFG\<close>

text \<open>The plain compiled CFG, rendered through the same GraphViz backend the
  other examples use -- no analysis annotation, just the structure the
  equation system above was generated from: entry, the guard's two branches,
  the two assignments, and the merge into \<open>main\<close>'s exit.\<close>

definition demo_dot :: String.literal where
  "demo_dot = raw_cfg_dot_lit demo_pi (prog_procs demo_program) prog_main_name (prog_main demo_program)"

ML_val \<open>writeln (@{code demo_dot})\<close>

subsection \<open>Rendering the CFG annotated with the computed relational result\<close>

text \<open>Same CFG, same rendering backend, this time with each node labelled by
  the \<open>relc\<close> value the solver computed there -- \<open>string_of_relc\<close> is the
  \<open>relc\<close> analogue of \<open>string_of_ivl\<close>, and \<open>local_of = locals\<close> is the same
  projection the flagship Interval example uses.\<close>

definition demo_rel_graph_config ::
  "(unit, unit, (relc, relc) dg_state, relc) analysis_graph_config" where
  "demo_rel_graph_config =
    \<lparr> local_of = locals,
      route = (\<lambda>_ _ _ _. ()),
      show_context = (\<lambda>_. ''unit''),
      locals_for_pp = (\<lambda>p.
        scope_locals (compiled_procedure_scope demo_pi (prog_procs demo_program)
          prog_main_name (prog_main demo_program) demo_cfg p)),
      return_slot_for_pp = (\<lambda>p.
        scope_return_slot (compiled_procedure_scope demo_pi (prog_procs demo_program)
          prog_main_name (prog_main demo_program) demo_cfg p)),
      globals_to_show = [],
      show_local = (\<lambda>_ _ _ d. [string_of_relc d]),
      format_return = (\<lambda>_ _ _ _. []),
      show_global = (\<lambda>_ _ _. [''(none)'']),
      show_global_key = (\<lambda>_. ''Global''),
      is_shared_global = (\<lambda>_. True),
      show_internal_globals = False,
      owner_of = (\<lambda>_. ''main''),
      cluster_label = (\<lambda>_ _. ''main / relational''),
      source_text = Some (pretty_string_of_program demo_pi (prog_procs demo_program)
        (prog_main demo_program))
    \<rparr>"

definition demo_graph_domain :: "(pp \<times> unit + unit) list" where
  "demo_graph_domain = contextual_graph_domain demo_cfg (\<lambda>_. [()])"

definition demo_rel_dot :: String.literal where
  "demo_rel_dot =
    String.implode
      (case TD_side_always_join_Interp_solve_c demo_rel_eqs (cfg_exit demo_cfg, ()) of
         None \<Rightarrow> ''solver did not terminate''
       | Some sol \<Rightarrow> contextual_analysis_dot demo_rel_graph_config demo_cfg
           demo_graph_domain (snd sol))"

ML_val \<open>writeln (@{code demo_rel_dot})\<close>

end
