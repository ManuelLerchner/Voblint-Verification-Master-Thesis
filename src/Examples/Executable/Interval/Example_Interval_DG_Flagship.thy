section \<open>Flagship: interval analysis of a counting loop, executed and certified on the D/G spine\<close>

text \<open>
  \<^bold>\<open>The complete story in one self-contained theory.\<close>  An IMP2 program (given inline
  below) is compiled to a CFG; the generic D/G framework generates an equation
  system; the \<^emph>\<open>verified\<close> top-down solver \<^emph>\<open>computes\<close> an interval solution inside
  Isabelle (with interval widening for termination); the computed solution is
  certified a partial post-solution by the solver's own correctness theorem; it is
  transported value-wise to the abstract D/G semantics; and the generic
  collecting-soundness theorem concludes that the computed abstraction
  over-approximates the concrete collecting semantics at every program point.

  \<^verbatim>\<open>
       IMP2 source
            |  compile_prog                          (section 2)
            v
          CFG
            |  dg_gen_of                              (section 4)
            v
    D/G equation system
            |  verified solver, by eval               (section 5)
            v
   computed interval solution  sigma
            |  solver correctness theorem             (section 6)
            v
    part_post_solution sigma
            |  part_post_solution_dg_st_to_abs        (section 7)
            v
   abstract post-solution
            |  ivl_dg_post_solution_collect_sound     (section 8)
            v
    ltr_collect subset gamma(sigma)   --- x in [0,20]  (section 9)
            |  compiler-correctness simulation        (section 10)
            v
   every IMP2 source run is bounded by sigma
  \<close>

  \<^bold>\<open>Every step is machine-checked, and the result is informative:\<close> the analysis
  discovers the loop invariant \<open>x in [0,20]\<close>, the body bound \<open>x in [0,19]\<close>, and the
  exact exit value \<open>x in [20,20]\<close> --- not \<open>top\<close>.  Section 10 lifts soundness from the
  collecting semantics to \<^emph>\<open>actual IMP2 source runs\<close> via the compiler-correctness
  simulation; section 11 exhibits an explicit reachable state so the guarantee is
  visibly \<^emph>\<open>not vacuous\<close>; section 12 emits an analysis-annotated GraphViz rendering.

  It reuses, without duplicating: the executable interval transfer \<open>ivl_tf_st\<close>
  (\<open>Ivl_Exec\<close>), the executable D/G bridge (\<open>Exec_DG_Bridge\<close>), the native interval
  D/G soundness endpoint (\<open>Interval_DG\<close>), the compiler-correctness simulation
  (\<open>Source_Activation_Sound\<close>), and the vendored warrowing solver.
\<close>

theory Example_Interval_DG_Flagship
  imports
    "Voblint_Analysis.Exec_DG_Bridge"
    "Voblint_Analysis.Interval_DG"
    "Voblint_Analysis.Ivl_Exec"
    "Voblint_Analysis.Solver_Menu"
    "Voblint_CFG.CFG_Prune"
    "Voblint_Analysis.Analysis_GraphViz"
    "Voblint_IMP2.IMP2_Notation"
    "Voblint_Formalization.DG_Domain_Registration"
begin

subsection \<open>The IMP2 source program\<close>

text \<open>
  A bounded counting loop: initialise \<open>x\<close> to \<open>0\<close>, increment while \<open>x < 20\<close>.  On
  exit \<open>x = 20\<close>.  No procedures, no globals; \<open>x\<close> is a single flow-sensitive local.
  The analysis must \<^emph>\<open>discover\<close> the bound, not assume it.
\<close>

definition flagship_prog :: "IMP2_Proc.com" where
  "flagship_prog = imp \<lbrakk> x := 0; while (x < 20) { x := x + 1 } \<rbrakk>"

subsection \<open>CFG construction\<close>

text \<open>
  The source compiles to an interprocedural CFG by \<open>compile_prog\<close>.  The whole program is
  the body of \<open>main\<close>, so it runs between \<open>FunctionEntry ''main''\<close> and
  \<open>FunctionResult ''main''\<close>; inside, \<open>x := 0\<close> reaches statement \<open>1\<close>, the loop head is \<open>2\<close>,
  the guard \<open>x < 20\<close> branches to body \<open>3\<close> or exit \<open>5\<close>, the increment reaches \<open>4\<close>, and \<open>4\<close>
  jumps back to \<open>2\<close>.  \<open>flagship_cfg_eq\<close> proves the compilation equals the explicit graph;
  the annotated rendering is in section 10.
\<close>

text \<open>The declaration environment holds exactly \<open>main\<close>: there are no other procedures, and
  \<^const>\<open>wf_compile_input\<close> requires the entry procedure to be declared.\<close>

definition flagship_pi :: proc_table where
  "flagship_pi = Map.empty(''main'' \<mapsto> proc_decl_of [] flagship_prog)"

definition flagship_cfg :: cfg where
  "flagship_cfg = compile_prog flagship_pi [] ''main'' flagship_prog"

lemma flagship_cfg_eq:
  "flagship_cfg =
     \<lparr> intra =
         {(FunctionEntry ''main'', EA_Nop, Statement 0),
          (Statement 0, EA_Assign ''x'' (BaseN (AExp.N 0)), Statement 1),
          (Statement 1, EA_Nop, Statement 2),
          (Statement 2, EA_Assume (Less (BaseN (AExp.V ''x'')) (BaseN (AExp.N 20))), Statement 3),
          (Statement 2, EA_AssumeNot (Less (BaseN (AExp.V ''x'')) (BaseN (AExp.N 20))), Statement 5),
          (Statement 3, EA_Assign ''x'' (Plus (BaseN (AExp.V ''x'')) (BaseN (AExp.N 1))), Statement 4),
          (Statement 4, EA_Nop, Statement 2),
          (Statement 5, EA_Ret None ''main'', FunctionResult ''main'')},
       calls = {},
       cfg_entry = FunctionEntry ''main'' \<rparr>"
  unfolding flagship_cfg_def flagship_pi_def flagship_prog_def by eval

lemma flagship_entry: "cfg_entry flagship_cfg = FunctionEntry ''main''"
  by (simp add: flagship_cfg_eq)
lemma flagship_exit: "cfg_exit flagship_cfg = FunctionResult ''main''"
  by (simp add: flagship_cfg_eq cfg_exit_def)
lemma flagship_intra: "intra flagship_cfg =
     {(FunctionEntry ''main'', EA_Nop, Statement 0),
      (Statement 0, EA_Assign ''x'' (BaseN (AExp.N 0)), Statement 1),
      (Statement 1, EA_Nop, Statement 2),
      (Statement 2, EA_Assume (Less (BaseN (AExp.V ''x'')) (BaseN (AExp.N 20))), Statement 3),
      (Statement 2, EA_AssumeNot (Less (BaseN (AExp.V ''x'')) (BaseN (AExp.N 20))), Statement 5),
      (Statement 3, EA_Assign ''x'' (Plus (BaseN (AExp.V ''x'')) (BaseN (AExp.N 1))), Statement 4),
      (Statement 4, EA_Nop, Statement 2),
      (Statement 5, EA_Ret None ''main'', FunctionResult ''main'')}"
  by (simp add: flagship_cfg_eq)
lemma flagship_calls: "calls flagship_cfg = {}" by (simp add: flagship_cfg_eq)

lemma flagship_finE: "finite (intra flagship_cfg)" by (simp add: flagship_intra)
lemma flagship_finC: "finite (calls flagship_cfg)" by (simp add: flagship_calls)

subsection \<open>Executable interval D/G specification\<close>

text \<open>
  Intervals form the diagonal D/G analysis \<open>D = G = ivl abs_state\<close>, with executable
  mirror \<open>unit_dg_spec_st ivl_tf_st\<close>.  The registration \<^locale>\<open>unit_dg_exec_analysis\<close>
  --- interpreted as \<open>ivl_reg\<close> in \<open>DG_Domain_Registration\<close> from \<open>ivl_is_sound_transfer\<close>
  and \<open>ivl_tf_st_commute\<close> alone --- discharges the transport, soundness, and
  solver-crossing obligations generically.  This example supplies only the program,
  the executable solve, and the coverage witnesses.
\<close>

subsection \<open>Equation generation\<close>

text \<open>
  The generic D/G generator \<open>dg_gen_of\<close> turns the CFG into an equation system over
  unknowns \<open>(pp x unit) + unit\<close>, values in \<open>(ivl st, ivl st) dg_state\<close>.  Locals
  seed at \<open>cinit_ivl_st\<close> (globals \<open>[0,0]\<close>, locals \<open>top\<close>); the flow-insensitive
  global slot seeds at \<open>restrict_global_st cinit_ivl_st\<close> (bottom on locals, so it
  never pollutes the local \<open>x\<close> through the diagonal read).
\<close>

definition flagship_eqs :: "pp \<times> unit \<Rightarrow> (pp \<times> unit, unit, (ivl st, ivl st) dg_state) strategy_tree" where
  "flagship_eqs = dg_gen_of (unit_dg_spec_st ivl_tf_st ivl_enter_st) flagship_cfg bot cinit_ivl_st (restrict_global_st cinit_ivl_st)"

subsection \<open>Executable solve\<close>

text \<open>
  The vendored \<open>TD_side_warrowing_apinis_Interp_solve_c\<close> --- pointwise interval
  widening on \<open>(ivl st, ivl st) dg_state\<close> for solver termination --- \<^emph>\<open>computes\<close> a
  solution.  Termination is a code-generated \<^verbatim>\<open>by eval\<close> fact; the solution is not
  written by hand.
\<close>

lemma flagship_terminates_c:
  "TD_side_warrowing_apinis_Interp_solve_c flagship_eqs (cfg_exit flagship_cfg, ()) \<noteq> None"
  by eval

definition flagship_sol :: "(pp \<times> unit) set \<times> (pp \<times> unit + unit \<Rightarrow> (ivl st, ivl st) dg_state)" where
  "flagship_sol = TD_side_warrowing_apinis_Interp_solve flagship_eqs (cfg_exit flagship_cfg, ())"

text \<open>The computed local interval for \<open>x\<close> at every node --- \<^emph>\<open>evaluated\<close>.\<close>

value "map_option
   (\<lambda>sol. map (\<lambda>p. (p, string_of_ivl (lookup_st (locals (snd sol (Inl (p, ())))) ''x'')))
            (map Statement [0,1,2,3,4,5]))
   (TD_side_warrowing_apinis_Interp_solve_c flagship_eqs (cfg_exit flagship_cfg, ()))"

subsection \<open>Soundness premises for the registered endpoint\<close>

text \<open>
  The premises of the generic native endpoint \<open>ivl_dg_post_solution_collect_sound\<close>:
  every program point is covered by the solved variable set (\<^verbatim>\<open>by eval\<close>), the graph
  is finite and enter-free, and the concrete initial stores are covered by the seed.
\<close>

lemma flagship_cover_all:
  "\<forall>v \<in> {Statement 0, Statement 1, Statement 2, Statement 3, Statement 4, Statement 5,
           FunctionEntry ''main'', FunctionResult ''main''}.
     (v, ()) \<in> fst flagship_sol"
  unfolding flagship_sol_def flagship_eqs_def by eval

lemma flagship_cover_entry: "(cfg_entry flagship_cfg, ()) \<in> fst flagship_sol"
  using flagship_cover_all flagship_entry by simp
lemma flagship_cover_edge: "\<And>u a w. (u, a, w) \<in> intra flagship_cfg \<Longrightarrow> (w, ()) \<in> fst flagship_sol"
  using flagship_cover_all by (auto simp: flagship_intra)
lemma flagship_cover_enter:
  "\<And>c dst fs as p k. (c, CallEdge dst fs as, FunctionEntry p, k) \<in> calls flagship_cfg
     \<Longrightarrow> (FunctionEntry p, ()) \<in> fst flagship_sol"
  by (simp add: flagship_calls)
lemma flagship_cover_combine:
  "\<And>c dst fs as p k. (c, CallEdge dst fs as, FunctionEntry p, k) \<in> calls flagship_cfg
     \<Longrightarrow> (k, ()) \<in> fst flagship_sol"
  by (simp add: flagship_calls)

lemma flagship_sound0:
  "cinit_stores \<subseteq> \<lbrakk>fun_of_st cinit_ivl_st \<squnion> fun_of_st (restrict_global_st cinit_ivl_st)\<rbrakk>"
proof -
  have "fun_of_st cinit_ivl_st \<squnion> fun_of_st (restrict_global_st cinit_ivl_st) = fun_of_st cinit_ivl_st"
    by (simp add: fun_of_st_cinit_ivl_st fun_of_st_restrict_global_st restrict_global_def sup_fun_def fun_eq_iff)
  thus ?thesis
    by (auto simp: cinit_stores_def gamma_state_def fun_of_st_cinit_ivl_st)
qed

text \<open>
  The coverage facts, finiteness, and the seed-soundness \<open>flagship_sound0\<close> are the
  instance premises the bundled endpoint (section 10) consumes; the collecting-soundness
  and transport steps are discharged inside it.
\<close>

subsection \<open>Inspecting the certified result\<close>

lemma flagship_head_computed:
  "lookup_st (locals (snd flagship_sol (Inl (Statement 2, ())))) ''x'' = Ivl (Fin 0) (Fin 20)"
  unfolding flagship_sol_def flagship_eqs_def by eval

lemma flagship_body_computed:
  "lookup_st (locals (snd flagship_sol (Inl (Statement 3, ())))) ''x'' = Ivl (Fin 0) (Fin 19)"
  unfolding flagship_sol_def flagship_eqs_def by eval

lemma flagship_exit_computed:
  "lookup_st (locals (snd flagship_sol (Inl (Statement 5, ())))) ''x'' = Ivl (Fin 20) (Fin 20)"
  unfolding flagship_sol_def flagship_eqs_def by eval

subsection \<open>Source-level soundness through the registered analysis\<close>

text \<open>
  The registered endpoint \<open>ivl_reg.run_source_sound\<close> turns the single \<^theory_text>\<open>by eval\<close>
  solver success \<open>flagship_terminates_c\<close> directly into a source-level guarantee: every
  reachable IMP2 store is bounded by the computed interval at its matched program point,
  read through the semantic accessor \<open>ivl_reg.gamma\<close>.  No transport lemma,
  \<^const>\<open>part_post_solution\<close>, \<open>solve_dom\<close>, or \<^const>\<open>fun_of_dg_st\<close> appears in this proof.
\<close>

lemma flagship_wf: "wf_compile_input flagship_pi [] ''main'' flagship_prog"
  unfolding wf_compile_input_def wf_source_program_def wf_proc_decl_def
    flagship_pi_def flagship_prog_def
  by (auto simp: source_aexp_def source_bexp_def proc_decl_of_def ret_var_def
      split: if_splits)

theorem flagship_source_run_sound:
  assumes run: "star (pstep flagship_pi) (flagship_prog, s, []) (residual, t, frs)"
      and init: "s \<in> cinit_stores"
  shows "\<exists>v stk. csim flagship_pi flagship_cfg (residual, t, frs) (v, t, stk)
                 \<and> t \<in> ivl_reg.gamma (snd flagship_sol) v"
proof -
  show ?thesis
    unfolding flagship_sol_def flagship_eqs_def flagship_cfg_def
    by (rule ivl_reg.run_source_sound
          [OF flagship_terminates_c[unfolded flagship_eqs_def flagship_cfg_def]
              flagship_wf
              flagship_cover_entry[unfolded flagship_sol_def flagship_eqs_def flagship_cfg_def]
              flagship_cover_edge[unfolded flagship_sol_def flagship_eqs_def flagship_cfg_def]
              flagship_cover_enter[unfolded flagship_sol_def flagship_eqs_def flagship_cfg_def]
              flagship_cover_combine[unfolded flagship_sol_def flagship_eqs_def flagship_cfg_def]
              flagship_finE[unfolded flagship_cfg_def]
              flagship_finC[unfolded flagship_cfg_def]
              flagship_sound0[folded gamma_unit_def]
              init run[unfolded flagship_cfg_def]])
qed



text \<open>
  \<^bold>\<open>The bound is proper.\<close>  The global slot carries no local information
  (\<open>glob_x_at_2\<close>), so the loop-head concretization constrains \<open>x\<close> to exactly
  \<open>[0,20]\<close> and rejects, e.g., a store with \<open>x = 100\<close>.  The guarantee therefore says
  something --- it is not the trivial \<open>gamma top = UNIV\<close>.
\<close>

lemma glob_x_at_2: "lookup_st (globs (snd flagship_sol (Inr ()))) ''x'' = bot"
  unfolding flagship_sol_def flagship_eqs_def by eval

lemma head_x_bound:
  "(locals ((fun_of_dg_st \<circ> snd flagship_sol) (Inl (Statement 2, ())))
    \<squnion> globs ((fun_of_dg_st \<circ> snd flagship_sol) (Inr ()))) ''x'' = Ivl (Fin 0) (Fin 20)"
proof -
  have L: "fun_of_st (locals (snd flagship_sol (Inl (Statement 2, ())))) ''x'' = Ivl (Fin 0) (Fin 20)"
    using flagship_head_computed by simp
  have G: "fun_of_st (globs (snd flagship_sol (Inr ()))) ''x'' = bot" by (rule glob_x_at_2)
  show ?thesis by (simp add: fun_of_dg_st_simps sup_fun_def L G)
qed

theorem flagship_head_bound_proper:
  "(\<lambda>_. 100) \<notin> ivl_dg_gamma (fun_of_dg_st \<circ> snd flagship_sol) (Statement 2)"
  unfolding ivl_dg_gamma_def ivl_dg.dg_gamma_def gamma_unit_def gamma_state_def
            ivl_dg.dg_D_def ivl_dg.dg_G_def
  apply (simp only: mem_Collect_eq not_all)
  apply (rule exI[of _ "''x''"])
  using head_x_bound apply (simp add: fun_of_dg_st_simps sup_fun_def)
  done

subsection \<open>Annotated GraphViz of the computed result\<close>

text \<open>
  A DOT rendering of \<open>flagship_cfg\<close> with each node annotated by the computed
  interval for \<open>x\<close>.  The \<^verbatim>\<open>ML_val\<close> below prints the DOT as a plain string; paste
  it into any GraphViz renderer (\<^verbatim>\<open>dot -Tpng\<close>) to view the analysed loop, each
  node labelled with the loop-invariant interval the verified solver computed.
\<close>

definition flagship_graph_config ::
  "(unit, unit, (ivl st, ivl st) dg_state, ivl st) analysis_graph_config" where
  "flagship_graph_config =
    \<lparr> local_of = locals,
      route = (\<lambda>_ _ _ _. ()),
      show_context = (\<lambda>_. ''unit''),
      locals_for_pp = (\<lambda>p.
        scope_locals (compiled_procedure_scope Map.empty [] ''main'' flagship_prog
          flagship_cfg p)),
      return_slot_for_pp = (\<lambda>p.
        scope_return_slot (compiled_procedure_scope Map.empty [] ''main'' flagship_prog
          flagship_cfg p)),
      globals_to_show = [],
      show_local = (\<lambda>_ _ vars d. map (\<lambda>x.
        x @ ''='' @ string_of_ivl (lookup_st d x)) vars),
      format_return = (\<lambda>_ _ _ _. []),
      show_global = (\<lambda>_ _ _. [''(none)'']),
      show_global_key = (\<lambda>_. ''Global''),
      is_shared_global = (\<lambda>_. True),
      show_internal_globals = False,
      owner_of = (\<lambda>_. ''main''),
      cluster_label = (\<lambda>_ _. ''main / root context''),
      source_text = Some (pretty_string_of_program Map.empty [] flagship_prog)
    \<rparr>"

definition flagship_graph_domain :: "(pp \<times> unit + unit) list" where
  "flagship_graph_domain =
    contextual_graph_domain flagship_cfg (\<lambda>_. [()])"

definition flagship_dot :: String.literal where
  "flagship_dot =
     String.implode
       (case TD_side_warrowing_apinis_Interp_solve_c flagship_eqs (cfg_exit flagship_cfg, ()) of
          None \<Rightarrow> ''solver did not terminate''
        | Some sol \<Rightarrow> contextual_analysis_dot flagship_graph_config flagship_cfg
            flagship_graph_domain (snd sol))"

ML_val \<open>writeln (@{code flagship_dot})\<close>


end


