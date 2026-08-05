theory Example_Interval_DG_IP_Flagship
  imports
    "Voblint_Analysis.Exec_DG_Bridge"
    "Voblint_Analysis.Interval_DG"
    "Voblint_Analysis.Ivl_Exec"
    "Voblint_Core.Solver_Menu"
    "Voblint_CFG.CFG_Prune"
    "Voblint_Analysis.Analysis_GraphViz"
    "Voblint_VIMP.VIMP_Notation"
    "Voblint_Formalization.Run_Analysis_Sound"
begin

section \<open>The context-insensitive (monovariant) interval flagship\<close>

text \<open>
  This is the non-context IP baseline: every call to \<open>twice\<close> is analyzed
  under a single, shared abstract state at \<open>FunctionEntry ''twice''\<close>,
  regardless of which call site reached it. It is the flagship the
  context-sensitive siblings sharpen -- \<open>Example_Interval_DG_Ctx_Flagship\<close>
  routes by the entered argument's abstract value, \<open>Example_Interval_DG_CallString\<close>
  routes by call site (a 1-CFA-style call string) -- so run this file first to
  see the precision loss two calls to the same procedure with different
  arguments incur when their entry states are forced to join, then compare
  against the routed variants.
\<close>

definition twice_program :: imp_prog where
  "twice_program = program {
     void twice(p) { return p + p }
     void main() { x := twice(3); y := twice(10) }
   }"

definition twice_pi :: proc_table where "twice_pi = prog_table twice_program"
definition twice_procs :: "pname list" where "twice_procs = prog_procs twice_program"
definition twice_main :: "VIMP_Proc.com" where "twice_main = prog_main twice_program"

text \<open>The storage classifier: \<open>twice_program\<close> declares no globals, so \<open>twice_gs\<close>
  classifies every variable this chain touches as local, matching the
  \<open>declared_global\<close> pattern used by every other flagship rather than
  the \<open>is_global\<close> naming convention.\<close>
abbreviation twice_gs :: "vname \<Rightarrow> bool" where
  "twice_gs \<equiv> declared_global twice_program"

definition twice_cfg :: cfg where
  "twice_cfg = compile_prog twice_pi twice_procs ''main'' twice_main"

text \<open>
  The compiled CFG.  Procedure \<open>twice\<close> runs between
  \<open>FunctionEntry ''twice''\<close> and \<open>FunctionResult ''twice''\<close>: the body's \<open>return p + p\<close>
  publishes through \<open>EA_Ret\<close> at statement \<open>0\<close>.  \<open>twice\<close> never falls through, so the
  continuation-passing compiler reserves no epilogue edge --- statement \<open>1\<close> is an
  unused index, not a node of the compiled graph.  \<open>main\<close> occupies statements \<open>2..4\<close>:
  \<open>2\<close> is the first call site, continuing directly at \<open>3\<close>, which is also the second
  call site, continuing at \<open>4\<close>.  Both call edges name the same callee entry
  \<open>FunctionEntry ''twice''\<close> --- this is the monovariant (single-context) view.
\<close>

lemma twice_entry: "cfg_entry twice_cfg = FunctionEntry ''main''" by eval

text \<open>The two call edges' shape, computed directly from \<open>twice_cfg\<close>: each call site \<open>u\<close>
  pins down its destination variable, callee, arguments, and continuation. Exported for the
  routed/context-sensitive siblings (\<open>Example_Interval_DG_Ctx_Collect\<close>,
  \<open>Example_Interval_DG_CallString\<close>), which case-split on the same two call sites.\<close>
lemma twice_calls_shape:
  "\<forall>(u, ca, ce, cont) \<in> calls twice_cfg.
     case ca of CallEdge dst pars args \<Rightarrow>
       (case ce of FunctionEntry p \<Rightarrow>
          (u = Statement 2 \<and> dst = Some ''x'' \<and> pars = [''p''] \<and> args = [VIMP_Syntax.N 3]
             \<and> p = ''twice'' \<and> cont = Statement 3) \<or>
          (u = Statement 3 \<and> dst = Some ''y'' \<and> pars = [''p''] \<and> args = [VIMP_Syntax.N 10]
             \<and> p = ''twice'' \<and> cont = Statement 4)
        | _ \<Rightarrow> True)"
  unfolding twice_cfg_def by eval

text \<open>Each call site has exactly one outgoing edge.\<close>
lemma twice_calls_unique_site:
  "\<forall>(u1, ca1, ce1, k1) \<in> calls twice_cfg. \<forall>(u2, ca2, ce2, k2) \<in> calls twice_cfg.
      u1 = u2 \<longrightarrow> ca1 = ca2 \<and> ce1 = ce2 \<and> k1 = k2"
  unfolding twice_cfg_def by eval

lemma twice_finE: "finite (intra twice_cfg)" unfolding twice_cfg_def using compile_prog_finite by simp
lemma twice_finC: "finite (calls twice_cfg)" unfolding twice_cfg_def using compile_prog_finite by simp

subsection \<open>The analysis specification (interval, as an executable D/G analysis)\<close>

text \<open>Classifier-parametric commutation mirrors, generic in \<open>gs\<close>: the entry point for
  this file, generic in the classifier rather than fixed to \<^const>\<open>is_global\<close>.\<close>

lemmas ivl_Hstep_for =
  unit_dg_Hstep_for[OF ivl_tf_st_for_commute[folded fun_of_exec_dg_st_for_def]
    ivl_tf_st_for_ret_None ivl_tf_st_for_ret_Some]

lemmas ivl_Henter_for =
  unit_dg_Henter_for[OF ivl_enter_st_for_commute[folded fun_of_exec_dg_st_for_def]]

lemmas ivl_Hcomb_for = unit_dg_Hcomb_for

text \<open>The abstract D/G soundness interpretation at \<open>twice_gs\<close>, generic in the
  storage classifier: gives access to this instantiation's own \<open>dg_gen\<close>/\<open>dg_gamma\<close>
  accessors and the \<open>dg_post_solution_collect_sound_ltr_for\<close> endpoint below.\<close>
interpretation twice_sds:
  sound_dg_spec_ltr_for "unit_dg_spec_for twice_gs (ivl_tf_for twice_gs)" gamma_unit twice_gs
  unfolding sound_dg_spec_ltr_for_def
  by (rule sound_dg_spec_unit_for[OF ivl_is_sound_transfer_for])

subsection \<open>Equation generation\<close>

definition twice_eqs ::
  "pp \<times> unit \<Rightarrow> (pp \<times> unit, unit, (ivl exec_dg_st, ivl exec_dg_st) dg_state) strategy_tree" where
  "twice_eqs = dg_gen_of (unit_dg_spec_st_for twice_gs (ivl_tf_st_for twice_gs) (ivl_enter_st_for twice_gs))
     twice_cfg bot cinit_ivl_st (restrict_global_resolved_q cinit_ivl_st)"

subsection \<open>Executable solve\<close>

lemma twice_terminates_c:
  "TD_side_warrowing_apinis_Interp_solve_c twice_eqs (cfg_exit twice_cfg, ()) \<noteq> None"
  by eval

definition twice_sol ::
  "(pp \<times> unit) set \<times> (pp \<times> unit + unit \<Rightarrow> (ivl exec_dg_st, ivl exec_dg_st) dg_state)" where
  "twice_sol = TD_side_warrowing_apinis_Interp_solve twice_eqs (cfg_exit twice_cfg, ())"

text \<open>The computed local intervals, \<^emph>\<open>evaluated\<close>: \<open>p in [3,10]\<close> at the shared
  callee entry, \<open>#ret in [6,20]\<close> at the callee exit, and \<open>x = y in [6,20]\<close> at the
  return sites.\<close>

value "map_option
   (\<lambda>sol. map (\<lambda>p. (p, string_of_ivl (lookup_exec_dg_st (locals (snd sol (Inl (p, ())))) ''p''),
                       string_of_ivl (lookup_exec_dg_st (locals (snd sol (Inl (p, ())))) ''#ret''),
                       string_of_ivl (lookup_exec_dg_st (locals (snd sol (Inl (p, ())))) ''x''),
                       string_of_ivl (lookup_exec_dg_st (locals (snd sol (Inl (p, ())))) ''y'')))
            ([FunctionEntry ''twice'', FunctionResult ''twice'',
              FunctionEntry ''main'', FunctionResult ''main'']
             @ map Statement [0,2,3,4]))
   (TD_side_warrowing_apinis_Interp_solve_c twice_eqs (cfg_exit twice_cfg, ()))"

subsection \<open>Certified solution (reusing solver correctness)\<close>

lemma twice_solve_dom:
  "TD_side_warrowing_apinis_Interp.solve_dom TYPE(unit) TYPE((ivl exec_dg_st, ivl exec_dg_st) dg_state)
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
     (twice_sds.dg_gen twice_cfg (fun_of_exec_dg_st_for twice_gs (bot::ivl exec_dg_st))
        (fun_of_exec_dg_st_for twice_gs cinit_ivl_st)
        (fun_of_exec_dg_st_for twice_gs (restrict_global_resolved_q cinit_ivl_st)))
     (cfg_exit twice_cfg, ()) (fun_of_dg_st_for twice_gs \<circ> snd twice_sol) (fst twice_sol)"
  using part_post_solution_dg_st_to_abs_for[OF ivl_Hstep_for ivl_Henter_for ivl_Hcomb_for twice_pp_st[unfolded twice_eqs_def]]
  unfolding twice_sds.dg_gen_of_eq_for .

subsection \<open>Soundness: the computed analysis over-approximates the collecting semantics\<close>

text \<open>
  The premises of the \<^emph>\<open>generic\<close> endpoint \<open>dg_post_solution_collect_sound_ltr_for\<close>:
  every point is solved (\<^verbatim>\<open>eval\<close>), the graph is finite --- and, crucially,
  \<^bold>\<open>no \<open>no_enter\<close> premise\<close>: the two \<^const>\<open>CallEdge\<close> entries are covered by the
  same collecting-soundness theorem as ordinary intra edges.
\<close>

lemma twice_cover_entry: "(cfg_entry twice_cfg, ()) \<in> fst twice_sol"
  unfolding twice_sol_def twice_eqs_def twice_entry by eval

lemma twice_cover_edge_ball: "\<forall>(u, a, w) \<in> intra twice_cfg. (w, ()) \<in> fst twice_sol"
  unfolding twice_sol_def twice_eqs_def by eval
lemma twice_cover_edge: "\<And>u a w. (u, a, w) \<in> intra twice_cfg \<Longrightarrow> (w, ()) \<in> fst twice_sol"
  using twice_cover_edge_ball by auto

lemma twice_cover_calls_ball:
  "\<forall>(c, ca, ce, k) \<in> calls twice_cfg.
     case ca of CallEdge dst fs as \<Rightarrow>
       (case ce of FunctionEntry p \<Rightarrow> (FunctionEntry p, ()) \<in> fst twice_sol \<and> (k, ()) \<in> fst twice_sol
        | _ \<Rightarrow> True)"
  unfolding twice_sol_def twice_eqs_def by eval
lemma twice_cover_enter:
  "\<And>c dst fs as p k. (c, CallEdge dst fs as, FunctionEntry p, k) \<in> calls twice_cfg
     \<Longrightarrow> (FunctionEntry p, ()) \<in> fst twice_sol"
  using twice_cover_calls_ball by fastforce
lemma twice_cover_combine:
  "\<And>c dst fs as p k. (c, CallEdge dst fs as, FunctionEntry p, k) \<in> calls twice_cfg
     \<Longrightarrow> (k, ()) \<in> fst twice_sol"
  using twice_cover_calls_ball by fastforce

lemma twice_sound0:
  "cinit_stores twice_gs \<subseteq>
     \<lbrakk>fun_of_exec_dg_st_for twice_gs cinit_ivl_st \<squnion> fun_of_exec_dg_st_for twice_gs (restrict_global_resolved_q cinit_ivl_st)\<rbrakk>"
proof -
  have "fun_of_exec_dg_st_for twice_gs cinit_ivl_st \<squnion>
          fun_of_exec_dg_st_for twice_gs (restrict_global_resolved_q cinit_ivl_st)
        = fun_of_exec_dg_st_for twice_gs cinit_ivl_st"
    by (simp add: fun_of_exec_dg_st_for_def fun_of_st_cinit_ivl_st_for restrict_global_def sup_fun_def fun_eq_iff)
  thus ?thesis
    by (auto simp: cinit_stores_def gamma_state_def fun_of_exec_dg_st_for_def fun_of_st_cinit_ivl_st_for)
qed

text \<open>
  The computed D/G post-solution bounds every stack-faithful local trace, including matched calls
  and returns, at each CFG point.
\<close>

theorem twice_collect_sound:
  "ltr_collect twice_gs twice_cfg (cinit_stores twice_gs) v
     \<subseteq> twice_sds.dg_gamma (fun_of_dg_st_for twice_gs \<circ> snd twice_sol) v"
  by (rule twice_sds.dg_post_solution_collect_sound_ltr_for
        [OF twice_pp_abs
            twice_cover_entry twice_cover_edge twice_cover_enter twice_cover_combine
            twice_finE twice_finC twice_sound0[folded gamma_unit_def]])

subsection \<open>Inspecting the certified result\<close>

lemma twice_p_at_entry:
  "lookup_exec_dg_st (locals (snd twice_sol (Inl (FunctionEntry ''twice'', ())))) ''p''
     = Ivl (Fin 3) (Fin 10)"
  unfolding twice_sol_def twice_eqs_def by eval

lemma twice_ret_at_exit:
  "lookup_exec_dg_st (locals (snd twice_sol (Inl (FunctionResult ''twice'', ())))) ''#ret''
     = Ivl (Fin 6) (Fin 20)"
  unfolding twice_sol_def twice_eqs_def by eval

lemma twice_x_computed:
  "lookup_exec_dg_st (locals (snd twice_sol (Inl (Statement 3, ())))) ''x'' = Ivl (Fin 6) (Fin 20)"
  unfolding twice_sol_def twice_eqs_def by eval

lemma twice_y_computed:
  "lookup_exec_dg_st (locals (snd twice_sol (Inl (Statement 4, ())))) ''y'' = Ivl (Fin 6) (Fin 20)"
  unfolding twice_sol_def twice_eqs_def by eval

subsection \<open>Registration through the classifier-parametric registration locale\<close>

text \<open>Interpret \<^locale>\<open>unit_dg_exec_analysis\<close> once here at \<open>twice_gs\<close>, matching the
  pattern in \<open>Exec_Sign_DG_Run\<close>, \<open>Example_Parity_DG_Flagship\<close>, and
  \<open>Example_Interval_DG_Flagship\<close>.  The interpretation absorbs the sound-transfer and
  primitive-commutation obligations once, so \<open>twice_source_run_sound\<close> below only
  supplies the compiled-input and solver facts.\<close>

interpretation twice_ex_reg:
  unit_dg_exec_analysis twice_gs
    "ivl_tf_for twice_gs" "ivl_tf_st_for twice_gs" "ivl_enter_st_for twice_gs"
    "TD_side_warrowing_apinis_Interp.solve" "TD_side_warrowing_apinis_Interp.solve_c"
proof -
  interpret twice_transfer: sound_transfer_for twice_gs "ivl_tf_for twice_gs"
    by (rule ivl_is_sound_transfer_for)
  show "unit_dg_exec_analysis twice_gs (ivl_tf_for twice_gs) (ivl_tf_st_for twice_gs)
          (ivl_enter_st_for twice_gs)
          TD_side_warrowing_apinis_Interp.solve TD_side_warrowing_apinis_Interp.solve_c"
    by unfold_locales
       (rule twice_transfer.tf_sound_assign_for twice_transfer.tf_sound_random_for
             twice_transfer.tf_sound_assume_for twice_transfer.tf_sound_assume_not_for
             twice_transfer.tf_sound_enter_for twice_transfer.tf_sound_combine_for
             ivl_tf_st_for_commute[folded fun_of_exec_dg_st_for_def]
             ivl_enter_st_for_commute[folded fun_of_exec_dg_st_for_def]
             ivl_tf_st_for_ret_None ivl_tf_st_for_ret_Some
             TD_side_warrowing_apinis_Interp.part_post_solution_of_solve_c)+
qed

subsection \<open>Source-level soundness\<close>

lemma twice_wf: "wf_compile_input twice_gs twice_pi twice_procs ''main'' twice_main"
  unfolding wf_compile_input_def wf_source_program_def wf_proc_decl_def
    twice_pi_def twice_procs_def twice_main_def twice_program_def
  by (auto simp: proc_decl_of_def prog_main_name_def valid_formal_def reserved_ret_var_def
      value_providing_def source_aexp_def ret_var_def
      split: if_splits option.splits)

theorem twice_source_run_sound:
  assumes run: "star (pstep twice_gs twice_pi) (twice_main, s, []) src'"
      and init: "s \<in> cinit_stores twice_gs"
  shows "\<exists>v t stk. csim twice_pi twice_cfg src' (v, t, stk)
                   \<and> t \<in> twice_ex_reg.gamma (snd twice_sol) v"
proof -
  obtain residual t frs where src': "src' = (residual, t, frs)" by (cases src')
  have cert:
    "\<exists>v stk. csim twice_pi twice_cfg (residual, t, frs) (v, t, stk)
       \<and> t \<in> twice_ex_reg.gamma (snd twice_sol) v"
    unfolding twice_cfg_def twice_sol_def twice_eqs_def
    apply (rule twice_ex_reg.run_source_sound
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
  continuations \<open>3\<close> / \<open>4\<close> show \<open>x\<close> / \<open>y in [6,20]\<close>.
\<close>

definition twice_graph_config ::
  "(unit, unit, (ivl exec_dg_st, ivl exec_dg_st) dg_state, ivl exec_dg_st) analysis_graph_config" where
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
        x @ ''='' @ string_of_ivl (lookup_exec_dg_st d x)) vars),
      format_return = (\<lambda>p ctx ret d.
        if lookup_exec_dg_st d ret = ivl_top then []
        else [''ret='' @ string_of_ivl (lookup_exec_dg_st d ret)]),
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




