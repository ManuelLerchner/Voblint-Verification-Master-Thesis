theory Example_Interval_DG_IP_Flagship
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

definition twice_program :: imp_prog where
  "twice_program = program {
     void twice(p) { return p + p }
     void main() { x := twice(3); y := twice(10) }
   }"

definition twice_pi :: proc_table where "twice_pi = prog_table twice_program"
definition twice_procs :: "pname list" where "twice_procs = prog_procs twice_program"
definition twice_main :: "IMP2_Proc.com" where "twice_main = prog_main twice_program"

definition twice_cfg :: cfg where
  "twice_cfg = compile_prog twice_pi twice_procs ''main'' twice_main"

text \<open>
  The compiled CFG, read off by \<^verbatim>\<open>eval\<close>.  Procedure \<open>twice\<close> runs between
  \<open>FunctionEntry ''twice''\<close> and \<open>FunctionResult ''twice''\<close>, occupying statements \<open>0..1\<close>:
  the body's \<open>return p + p\<close> publishes through \<open>EA_Ret\<close> at statement \<open>0\<close>, and statement \<open>1\<close>
  is the void fall-through return.  \<open>main\<close> occupies statements \<open>2..5\<close>: \<open>2\<close> is the first
  call site (continuing at \<open>3\<close>), \<open>4\<close> is the second (continuing at \<open>5\<close>).
  \<^bold>\<open>Both call edges name the same callee entry \<open>FunctionEntry ''twice''\<close>\<close> --- this is the
  monovariant (single-context) view.
\<close>

lemma twice_entry: "cfg_entry twice_cfg = FunctionEntry ''main''" by eval
lemma twice_exit: "cfg_exit twice_cfg = FunctionResult ''main''"
  by (simp add: cfg_exit_def twice_entry)

lemma twice_intra:
  "intra twice_cfg =
     {(FunctionEntry ''twice'', EA_Nop, Statement 0),
      (Statement 0,
       EA_Ret (Some (Plus (IMP2_Syntax.V ''p'') (IMP2_Syntax.V ''p''))) ''twice'',
       FunctionResult ''twice''),
      (Statement 1, EA_Ret None ''twice'', FunctionResult ''twice''),
      (FunctionEntry ''main'', EA_Nop, Statement 2),
      (Statement 3, EA_Nop, Statement 4),
      (Statement 5, EA_Ret None ''main'', FunctionResult ''main'')}"
  by eval

lemma twice_calls:
  "calls twice_cfg =
     {(Statement 2, CallEdge (Some ''x'') [''p''] [IMP2_Syntax.N 3],
       FunctionEntry ''twice'', Statement 3),
      (Statement 4, CallEdge (Some ''y'') [''p''] [IMP2_Syntax.N 10],
       FunctionEntry ''twice'', Statement 5)}"
  by eval

lemma twice_finE: "finite (intra twice_cfg)" unfolding twice_intra by simp
lemma twice_finC: "finite (calls twice_cfg)" unfolding twice_calls by simp

subsection \<open>The analysis specification (interval, as an executable D/G analysis)\<close>

lemmas ivl_Hstep =
  unit_dg_Hstep[OF ivl_tf_st_commute ivl_tf_st_ret_None ivl_tf_st_ret_Some]

lemmas ivl_Henter = unit_dg_Henter[OF ivl_enter_st_commute]

lemmas ivl_Hcomb = unit_dg_Hcomb

lemma dg_gen_of_eq_ivl_dg_gen:
  "dg_gen_of (unit_dg_spec ivl_tf) g bot0 s0d s0g = ivl_dg.dg_gen g bot0 s0d s0g"
proof -
  have cmb: "dg_cmb_of (unit_dg_spec ivl_tf) = ivl_dg.dg_cmb"
    by (rule ext)+ (simp add: dg_cmb_of_def ivl_dg.dg_cmb_def)
  have extra: "dg_extra_of (unit_dg_spec ivl_tf) g = ivl_dg.dg_extra g"
    by (rule ext)+ (simp add: dg_extra_of_def ivl_dg.dg_extra_def ivl_dg.dg_enter_def)
  show ?thesis by (simp add: dg_gen_of_def ivl_dg.dg_gen_def cmb extra)
qed

subsection \<open>Equation generation\<close>

definition twice_eqs ::
  "pp \<times> unit \<Rightarrow> (pp \<times> unit, unit, (ivl st, ivl st) dg_state) strategy_tree" where
  "twice_eqs = dg_gen_of (unit_dg_spec_st ivl_tf_st ivl_enter_st) twice_cfg bot cinit_ivl_st (restrict_global_st cinit_ivl_st)"

subsection \<open>Executable solve\<close>

lemma twice_terminates_c:
  "TD_side_warrowing_apinis_Interp_solve_c twice_eqs (cfg_exit twice_cfg, ()) \<noteq> None"
  by eval

definition twice_sol ::
  "(pp \<times> unit) set \<times> (pp \<times> unit + unit \<Rightarrow> (ivl st, ivl st) dg_state)" where
  "twice_sol = TD_side_warrowing_apinis_Interp_solve twice_eqs (cfg_exit twice_cfg, ())"

text \<open>The computed local intervals, \<^emph>\<open>evaluated\<close>: \<open>p in [3,10]\<close> at the shared
  callee entry, \<open>#ret in [6,20]\<close> at the callee exit, and \<open>x = y in [6,20]\<close> at the
  return sites.\<close>

value "map_option
   (\<lambda>sol. map (\<lambda>p. (p, string_of_ivl (lookup_st (locals (snd sol (Inl (p, ())))) ''p''),
                       string_of_ivl (lookup_st (locals (snd sol (Inl (p, ())))) ''#ret''),
                       string_of_ivl (lookup_st (locals (snd sol (Inl (p, ())))) ''x''),
                       string_of_ivl (lookup_st (locals (snd sol (Inl (p, ())))) ''y'')))
            ([FunctionEntry ''twice'', FunctionResult ''twice'',
              FunctionEntry ''main'', FunctionResult ''main'']
             @ map Statement [0,1,2,3,4,5]))
   (TD_side_warrowing_apinis_Interp_solve_c twice_eqs (cfg_exit twice_cfg, ()))"

subsection \<open>Certified solution (reusing solver correctness)\<close>

lemma twice_solve_dom:
  "TD_side_warrowing_apinis_Interp.solve_dom TYPE(unit) TYPE((ivl st, ivl st) dg_state)
     twice_eqs (cfg_exit twice_cfg, ())"
  using twice_terminates_c
  unfolding TD_side_warrowing_apinis_Interp.term_equivalence
            TD_side_warrowing_apinis_Interp.solve_c_dom_def
  by simp

lemma twice_pp_st:
  "part_post_solution twice_eqs (cfg_exit twice_cfg, ()) (snd twice_sol) (fst twice_sol)"
  using TD_side_warrowing_apinis_Interp.partial_post_solution
          [OF twice_solve_dom, of "fst twice_sol" "snd twice_sol"]
  unfolding twice_sol_def by simp

subsection \<open>Transport to the abstract D/G semantics\<close>

lemma twice_pp_abs:
  "part_post_solution
     (ivl_dg.dg_gen twice_cfg (fun_of_st (bot::ivl st)) (fun_of_st cinit_ivl_st)
        (fun_of_st (restrict_global_st cinit_ivl_st)))
     (cfg_exit twice_cfg, ()) (fun_of_dg_st \<circ> snd twice_sol) (fst twice_sol)"
  using part_post_solution_dg_st_to_abs[OF ivl_Hstep ivl_Henter ivl_Hcomb twice_pp_st[unfolded twice_eqs_def]]
  unfolding dg_gen_of_eq_ivl_dg_gen .

subsection \<open>Soundness: the computed analysis over-approximates the collecting semantics\<close>

text \<open>
  The premises of the \<^emph>\<open>generalized\<close> endpoint \<open>ivl_dg_post_solution_collect_sound\<close>:
  every point is solved (\<^verbatim>\<open>eval\<close>), the graph is finite --- and, crucially,
  \<^bold>\<open>no \<open>no_enter\<close> premise\<close>: the two \<^const>\<open>CallEdge\<close> entries are covered by the
  same collecting-soundness theorem as ordinary intra edges.
\<close>

lemma twice_cover_all:
  "\<forall>v \<in> {FunctionEntry ''twice'', FunctionResult ''twice'',
           FunctionEntry ''main'', FunctionResult ''main'',
           Statement 0, Statement 1, Statement 2, Statement 3, Statement 4, Statement 5}.
     (v, ()) \<in> fst twice_sol"
  unfolding twice_sol_def twice_eqs_def by eval

lemma twice_cover_entry: "(cfg_entry twice_cfg, ()) \<in> fst twice_sol"
  using twice_cover_all twice_entry by simp
lemma twice_cover_edge: "\<And>u a w. (u, a, w) \<in> intra twice_cfg \<Longrightarrow> (w, ()) \<in> fst twice_sol"
  using twice_cover_all by (auto simp: twice_intra)
lemma twice_cover_enter:
  "\<And>c dst fs as p k. (c, CallEdge dst fs as, FunctionEntry p, k) \<in> calls twice_cfg
     \<Longrightarrow> (FunctionEntry p, ()) \<in> fst twice_sol"
  using twice_cover_all by (auto simp: twice_calls)
lemma twice_cover_combine:
  "\<And>c dst fs as p k. (c, CallEdge dst fs as, FunctionEntry p, k) \<in> calls twice_cfg
     \<Longrightarrow> (k, ()) \<in> fst twice_sol"
  using twice_cover_all by (auto simp: twice_calls)

lemma twice_sound0:
  "cinit_stores \<subseteq> \<lbrakk>fun_of_st cinit_ivl_st \<squnion> fun_of_st (restrict_global_st cinit_ivl_st)\<rbrakk>"
proof -
  have "fun_of_st cinit_ivl_st \<squnion> fun_of_st (restrict_global_st cinit_ivl_st) = fun_of_st cinit_ivl_st"
    by (simp add: fun_of_st_cinit_ivl_st restrict_global_def sup_fun_def fun_eq_iff)
  thus ?thesis
    by (auto simp: cinit_stores_def gamma_state_def fun_of_st_cinit_ivl_st)
qed

text \<open>
  The computed D/G post-solution bounds every stack-faithful local trace, including matched calls
  and returns, at each CFG point.
\<close>

theorem twice_collect_sound:
  "ltr_collect twice_cfg cinit_stores v
     \<subseteq> ivl_dg_gamma (fun_of_dg_st \<circ> snd twice_sol) v"
  by (rule ivl_dg_post_solution_collect_sound
        [OF twice_pp_abs[folded ivl_dg_generator_def]
            twice_cover_entry twice_cover_edge twice_cover_enter twice_cover_combine
            twice_finE twice_finC twice_sound0])

subsection \<open>Inspecting the certified result\<close>

lemma twice_p_at_entry:
  "lookup_st (locals (snd twice_sol (Inl (FunctionEntry ''twice'', ())))) ''p''
     = Ivl (Fin 3) (Fin 10)"
  unfolding twice_sol_def twice_eqs_def by eval

lemma twice_ret_at_exit:
  "lookup_st (locals (snd twice_sol (Inl (FunctionResult ''twice'', ())))) ''#ret''
     = Ivl (Fin 6) (Fin 20)"
  unfolding twice_sol_def twice_eqs_def by eval

lemma twice_x_computed:
  "lookup_st (locals (snd twice_sol (Inl (Statement 3, ())))) ''x'' = Ivl (Fin 6) (Fin 20)"
  unfolding twice_sol_def twice_eqs_def by eval

lemma twice_y_computed:
  "lookup_st (locals (snd twice_sol (Inl (Statement 5, ())))) ''y'' = Ivl (Fin 6) (Fin 20)"
  unfolding twice_sol_def twice_eqs_def by eval

subsection \<open>Source-level soundness\<close>

lemma twice_wf: "wf_compile_input twice_pi twice_procs ''main'' twice_main"
  unfolding wf_compile_input_def wf_source_program_def wf_proc_decl_def
    twice_pi_def twice_procs_def twice_main_def twice_program_def
  by (auto simp: proc_decl_of_def prog_main_name_def valid_formal_def
      value_providing_def source_aexp_def ret_var_def is_global_def
      split: if_splits option.splits)

theorem twice_source_run_sound:
  assumes run: "star (pstep twice_pi) (twice_main, s, []) src'"
      and init: "s \<in> cinit_stores"
  shows "\<exists>v t stk. csim twice_pi twice_cfg src' (v, t, stk)
                   \<and> t \<in> ivl_reg.gamma (snd twice_sol) v"
proof -
  obtain residual t frs where src': "src' = (residual, t, frs)" by (cases src')
  have cert:
    "\<exists>v stk. csim twice_pi twice_cfg (residual, t, frs) (v, t, stk)
       \<and> t \<in> ivl_reg.gamma (snd twice_sol) v"
    unfolding twice_cfg_def twice_sol_def twice_eqs_def
    apply (rule ivl_reg.run_source_sound
      [where Pi=twice_pi and ps=twice_procs and mnm="''main''" and main=twice_main])
    apply (rule twice_terminates_c[unfolded twice_eqs_def twice_cfg_def])
    apply (rule twice_wf)
    apply (rule twice_cover_entry[unfolded twice_sol_def twice_eqs_def twice_cfg_def])
    apply (erule twice_cover_edge[unfolded twice_sol_def twice_eqs_def twice_cfg_def])
    apply (erule twice_cover_enter[unfolded twice_sol_def twice_eqs_def twice_cfg_def])
    apply (erule twice_cover_combine[unfolded twice_sol_def twice_eqs_def twice_cfg_def])
    apply (rule twice_finE[unfolded twice_cfg_def])
    apply (rule twice_finC[unfolded twice_cfg_def])
    apply (rule twice_sound0[folded gamma_unit_def])
    apply (rule init)
    apply (rule run[unfolded src'])
    done
  show ?thesis using cert src' by blast
qed

subsection \<open>Annotated GraphViz of the computed result\<close>

text \<open>
  A DOT rendering of \<open>twice_cfg\<close> annotated with the solver-computed intervals.
  The tooling renders the two \<^const>\<open>CallEdge\<close> entries \<^bold>\<open>distinctly\<close> (thick
  purple, labelled \<open>enter\<close>) and the two combine/return edges as \<^bold>\<open>dashed blue\<close>
  (labelled \<open>combine via call@N\<close>).  Each node is annotated with \<open>p\<close>, \<open>#ret\<close>,
  \<open>x\<close>, \<open>y\<close>; in particular the shared callee entry \<open>FunctionEntry ''twice''\<close> shows
  \<open>p in [3,10]\<close> and \<open>FunctionResult ''twice''\<close> shows \<open>#ret in [6,20]\<close>, while the
  continuations \<open>3\<close> / \<open>5\<close> show \<open>x\<close> / \<open>y in [6,20]\<close>.
\<close>

definition twice_graph_config ::
  "(unit, unit, (ivl st, ivl st) dg_state, ivl st) analysis_graph_config" where
  "twice_graph_config =
    \<lparr> local_of = locals,
      route = (\<lambda>_ _ _ _. ()),
      show_context = (\<lambda>_. ''unit''),
      locals_for_pp = (\<lambda>p.
        let sc = compiled_procedure_scope twice_pi twice_procs ''main'' twice_main
          twice_cfg p
        in scope_formals sc @ scope_locals sc),
      return_slot_for_pp = (\<lambda>p.
        scope_return_slot (compiled_procedure_scope twice_pi twice_procs ''main'' twice_main
          twice_cfg p)),
      globals_to_show = [],
      show_local = (\<lambda>p ctx vars d. map (\<lambda>x.
        x @ ''='' @ string_of_ivl (lookup_st d x)) vars),
      format_return = (\<lambda>p ctx ret d.
        if lookup_st d ret = ivl_top then []
        else [''ret='' @ string_of_ivl (lookup_st d ret)]),
      show_global = (\<lambda>_ vars s. [''(none)'']),
      show_global_key = (\<lambda>_. ''Global''),
      is_shared_global = (\<lambda>_. True),
      show_internal_globals = False,
      owner_of = compiled_owner_of twice_pi twice_procs ''main'' twice_main,
      cluster_label = (\<lambda>owner _. owner @ '' / context=unit''),
      source_text = Some (pretty_string_of_program twice_pi twice_procs twice_main)
    \<rparr>"

definition twice_graph_domain :: "(pp \<times> unit + unit) list" where
  "twice_graph_domain =
    contextual_graph_domain twice_cfg (\<lambda>_. [()])"

definition twice_dot :: String.literal where
  "twice_dot =
     String.implode
       (case TD_side_warrowing_apinis_Interp_solve_c twice_eqs (cfg_exit twice_cfg, ()) of
          None \<Rightarrow> ''solver did not terminate''
        | Some sol \<Rightarrow> contextual_analysis_dot twice_graph_config twice_cfg
            twice_graph_domain (snd sol))"

ML_val \<open>writeln (@{code twice_dot})\<close>



end


