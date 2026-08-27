theory Example_Interval_DG_IP_Flagship
  imports
    "Voblint_Core.Exec_DG_Bridge"
    "Voblint_Core.DG_LTR_Sound"
    "Voblint_Analysis.Interval_Transfer"
    "Voblint_Analysis.Ivl_Exec"
    "Voblint_Core.Solver_Menu"
    "Voblint_Core.DG_Coverage"
    "Voblint_CFG.CFG_Prune"
    "Voblint_Analysis.Analysis_GraphViz"
    "Voblint_VIMP.VIMP_Notation"
    "Voblint_Soundness.Run_Analysis_Sound"
begin

section \<open>The context-insensitive (monovariant) interval flagship\<close>

text \<open>
  This is the non-context IP baseline: every call to \<open>twice\<close> is analyzed
  under a single, shared abstract state at \<open>FunctionEntry (STR ''twice'')\<close>,
  regardless of which call site reached it. It is the flagship the
  context-sensitive sibling \<open>Example_Interval_DG_Ctx_Flagship\<close> sharpens by
  routing on the entered argument's abstract value -- so run this file first to
  see the precision loss two calls to the same procedure with different
  arguments incur when their entry states are forced to join, then compare
  against the routed variant.
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

text \<open>Local shorthand for the executable state's lookup projection, fixed at this
  file's own \<open>twice_gs\<close> classifier.\<close>
abbreviation twice_lookup :: "('a::bot) exec_dg_st \<Rightarrow> vname \<Rightarrow> 'a" where
  "twice_lookup s x \<equiv> lookup_resolved_st_q s (location_of twice_gs x)"

definition twice_cfg :: cfg where
  "twice_cfg = compile_prog (prog_tyenv twice_program) twice_pi twice_procs (STR ''main'') twice_main"

text \<open>
  The compiled CFG.  Procedure \<open>twice\<close> runs between
  \<open>FunctionEntry (STR ''twice'')\<close> and \<open>FunctionResult (STR ''twice'')\<close>: the body's \<open>return p + p\<close>
  publishes through \<open>EA_Ret\<close> at statement \<open>0\<close>.  \<open>twice\<close> never falls through, so the
  continuation-passing compiler reserves no epilogue edge --- statement \<open>1\<close> is an
  unused index, not a node of the compiled graph.  \<open>main\<close> occupies statements \<open>2..4\<close>:
  \<open>2\<close> is the first call site, continuing directly at \<open>3\<close>, which is also the second
  call site, continuing at \<open>4\<close>.  Both call edges name the same callee entry
  \<open>FunctionEntry (STR ''twice'')\<close> --- this is the monovariant (single-context) view.
\<close>

lemma twice_entry: "cfg_entry twice_cfg = FunctionEntry (STR ''main'')"
  unfolding twice_cfg_def by (rule inv16_entry_is_main)

text \<open>The two call edges' shape, computed directly from \<open>twice_cfg\<close>: each call site \<open>u\<close>
  pins down its destination variable, callee, arguments, and continuation. Exported for the
  routed/context-sensitive sibling \<open>Example_Interval_DG_Ctx_Collect\<close>, which case-splits on
  the same two call sites.\<close>
lemma twice_calls_shape:
  "\<forall>(u, ca, ce, cont) \<in> calls twice_cfg.
     case ca of CallEdge dst pars args \<Rightarrow>
       (case ce of FunctionEntry p \<Rightarrow>
          (u = Statement 2 \<and> dst = compile_dst (prog_tyenv twice_program) (Some (STR ''x'')) \<and> pars = [(STR ''p'')]
             \<and> args = compile_actuals (prog_tyenv twice_program) [(STR ''p'')] [VIMP_Syntax.N 3]
             \<and> p = (STR ''twice'') \<and> cont = Statement 3) \<or>
          (u = Statement 3 \<and> dst = compile_dst (prog_tyenv twice_program) (Some (STR ''y'')) \<and> pars = [(STR ''p'')]
             \<and> args = compile_actuals (prog_tyenv twice_program) [(STR ''p'')] [VIMP_Syntax.N 10]
             \<and> p = (STR ''twice'') \<and> cont = Statement 4)
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
  this file, generic in the classifier rather than fixed to a name-based convention.\<close>

text \<open>
  \<open>Hstep\<close> is proved here per \<^const>\<open>dg_spec_step\<close> case rather than through
  \<open>unit_dg_Hstep_for\<close> (\<open>Run_Analysis_Sound\<close>), which routes the return case
  through \<open>action_reduces\<close>: every case of the dispatch reduces to the single
  per-action commutation \<^const>\<open>ivl_tf_st_for\<close> already satisfies, so
  \<open>unit_step_st_commute_for\<close> together with \<open>ivl_tf_st_for_commute\<close> closes each
  one directly. The action's own \<open>rk\<close> never enters the argument: the compiler
  elaborated the returned expression at the procedure's declared return kind,
  so the conversion sits inside the \<^typ>\<open>texp\<close> payload as a \<^const>\<open>TCast\<close>
  node and both sides read it from there.
\<close>
lemma ivl_Hstep_for:
  "map_prod (fun_of_exec_dg_st_for twice_gs) (fun_of_exec_dg_st_for twice_gs)
     (dg_spec_step (unit_dg_spec_st_for twice_gs (ivl_tf_st_for twice_gs)
                      (ivl_enter_st_for twice_gs)) a d g)
   = dg_spec_step (unit_dg_spec_for twice_gs (ivl_tf_for twice_gs)) a
       (fun_of_exec_dg_st_for twice_gs d) (fun_of_exec_dg_st_for twice_gs g)"
  apply (cases a)
  apply (simp_all add: unit_dg_spec_st_for_def unit_dg_spec_for_def dg_spec_step.simps)
  apply ((rule unit_step_st_commute_for,
          subst ivl_tf_st_for_commute[folded fun_of_exec_dg_st_for_def], simp))+
  done

lemmas ivl_Henter_for =
  unit_dg_Henter_for[OF ivl_enter_st_for_commute[folded fun_of_exec_dg_st_for_def]]

lemmas ivl_Hcomb_for = unit_dg_Hcomb_for
lemmas ivl_Hcont_for = unit_dg_Hcont_for

text \<open>The abstract D/G soundness interpretation at \<open>twice_gs\<close>, generic in the
  storage classifier: gives access to this instantiation's own \<open>dg_gen\<close>/\<open>dg_gamma\<close>
  accessors and the \<open>dg_post_solution_collect_sound_ltr_for\<close> endpoint below.\<close>
lemma twice_reserved: "reserved_ret_var twice_gs"
  unfolding wf_compile_input_simps
    twice_pi_def twice_procs_def twice_main_def twice_program_def
  by (auto simp: proc_decl_of_def prog_main_name_def valid_formal_def reserved_ret_var_def
      value_providing_def source_exp_def ret_var_def
      split: if_splits option.splits)

interpretation twice_sds:
  sound_dg_spec_ltr_for "unit_dg_spec_for twice_gs (ivl_tf_for twice_gs)"
    "gamma_unit twice_gs" twice_gs "prog_tyenv twice_program"
  unfolding sound_dg_spec_ltr_for_def
  by (rule sound_dg_spec_unit_for[OF ivl_is_sound_transfer_for twice_reserved])

subsection \<open>Equation generation\<close>

definition twice_eqs ::
  "pp \<times> unit \<Rightarrow> (pp \<times> unit, unit, (ivl exec_dg_st, ivl exec_dg_st) dg_state) strategy_tree" where
  "twice_eqs = dg_gen_of (unit_dg_spec_st_for twice_gs (ivl_tf_st_for twice_gs)
       (ivl_enter_st_for twice_gs))
     twice_cfg bot cinit_ivl_st (restrict_global_resolved_q cinit_ivl_st)"

subsection \<open>Executable solve\<close>

lemma twice_terminates_c:
  "TD_side_warrowing_apinis_Interp_solve_c twice_eqs (cfg_exit twice_cfg, ()) \<noteq> None"
  by eval

definition twice_sol ::
  "(pp \<times> unit) set \<times> (pp \<times> unit + unit \<Rightarrow> (ivl exec_dg_st, ivl exec_dg_st) dg_state)" where
  "twice_sol = TD_side_warrowing_apinis_Interp_solve twice_eqs (cfg_exit twice_cfg, ())"

subsection \<open>Certified solution (reusing solver correctness)\<close>

lemma twice_solve_dom:
  "TD_side_warrowing_apinis_Interp.solve_dom TYPE(unit) TYPE((ivl exec_dg_st, ivl exec_dg_st) dg_state)
     twice_eqs (cfg_exit twice_cfg, ())"
  by (rule TD_side_warrowing_apinis_Interp.solve_dom_of_solve_c[OF twice_terminates_c])

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
  using part_post_solution_dg_st_to_abs_for[OF ivl_Hstep_for ivl_Henter_for ivl_Hcomb_for ivl_Hcont_for twice_pp_st[unfolded twice_eqs_def]]
  unfolding twice_sds.dg_gen_of_eq_for .

subsection \<open>Soundness: the computed analysis over-approximates the collecting semantics\<close>

text \<open>
  The premises of the \<^emph>\<open>generic\<close> endpoint \<open>dg_post_solution_collect_sound_ltr_for\<close>:
  every point is solved (\<^verbatim>\<open>eval\<close>), the graph is finite --- and, crucially,
  \<^bold>\<open>no \<open>no_enter\<close> premise\<close>: the two \<^const>\<open>CallEdge\<close> entries are covered by the
  same collecting-soundness theorem as ordinary intra edges.
\<close>

text \<open>Coverage is not read off the solved key set. Every node of \<open>twice_cfg\<close> ---
  including both callee entries and both continuations --- reaches
  \<^const>\<open>cfg_exit\<close>, a structural fact about the graph alone decided by
  \<^const>\<open>cfg_exit_covers\<close>, and \<^const>\<open>vars_cover\<close> follows from that together with
  the post-solution the solver already returns.\<close>

lemma twice_wf_cfg: "wf_cfg twice_cfg"
  unfolding twice_cfg_def by (rule compile_prog_wf)

lemma twice_exit_covers: "cfg_exit_covers twice_cfg" by eval

lemma twice_vars_cover: "vars_cover twice_cfg (fst twice_sol)"
  by (rule vars_cover_of_dg_gen_of_covers
        [OF twice_finE twice_finC twice_wf_cfg twice_exit_covers
            twice_pp_st[unfolded twice_eqs_def]])
lemma twice_sound0:
  "cinit_stores twice_gs \<subseteq>
     \<lbrakk>combine_env_abs twice_gs (fun_of_exec_dg_st_for twice_gs cinit_ivl_st)
        (fun_of_exec_dg_st_for twice_gs (restrict_global_resolved_q cinit_ivl_st))\<rbrakk>"
proof -
  have "combine_env_abs twice_gs (fun_of_exec_dg_st_for twice_gs cinit_ivl_st)
          (fun_of_exec_dg_st_for twice_gs (restrict_global_resolved_q cinit_ivl_st))
        = fun_of_exec_dg_st_for twice_gs cinit_ivl_st"
    by (simp add: combine_env_abs_def fun_of_exec_dg_st_for_def fun_of_st_cinit_ivl_st_for
                  restrict_global_for_def declared_global_def fun_eq_iff)
  thus ?thesis
    by (auto simp: cinit_stores_def gamma_state_def fun_of_exec_dg_st_for_def fun_of_st_cinit_ivl_st_for)
qed

text \<open>
  The computed D/G post-solution bounds every stack-faithful local trace, including matched calls
  and returns, at each CFG point.
\<close>

theorem twice_collect_sound:
  "ltr_collect (prog_tyenv twice_program) twice_gs twice_cfg (cinit_stores twice_gs) v
     \<subseteq> twice_sds.dg_gamma (fun_of_dg_st_for twice_gs \<circ> snd twice_sol) v"
  by (rule twice_sds.dg_post_solution_collect_sound_ltr_for
        [OF twice_pp_abs
            twice_vars_cover
            twice_finE twice_finC twice_sound0[folded gamma_unit_def]])

subsection \<open>Inspecting the certified result\<close>

lemma twice_p_at_entry:
  "twice_lookup (locals (snd twice_sol (Inl (FunctionEntry (STR ''twice''), ())))) (STR ''p'')
     = Ivl (Fin 3) (Fin 10)"
  unfolding twice_sol_def twice_eqs_def by eval

text \<open>
  \<open>#ret\<close> at \<open>twice\<close>'s exit, and \<open>x\<close>/\<open>y\<close> after each call, are read off
  \<^const>\<open>return_ivl\<close>, which evaluates the \<^typ>\<open>texp\<close> the \<open>EA_Ret\<close> edge
  carries -- the elaborated \<open>p + p\<close>, already cast to \<open>twice\<close>'s declared return
  kind by the compiler. \<open>p\<close>'s own bound at entry (\<open>twice_p_at_entry\<close>) comes
  from the join of the two call sites' arguments, upstream of the return edge.
\<close>

lemma twice_ret_at_exit:
  "twice_lookup (locals (snd twice_sol (Inl (FunctionResult (STR ''twice''), ())))) (STR ''#ret'')
     = Ivl (Fin 6) (Fin 20)"
  unfolding twice_sol_def twice_eqs_def by eval

lemma twice_x_computed:
  "twice_lookup (locals (snd twice_sol (Inl (Statement 3, ())))) (STR ''x'')
     = Ivl (Fin 6) (Fin 20)"
  unfolding twice_sol_def twice_eqs_def by eval

lemma twice_y_computed:
  "twice_lookup (locals (snd twice_sol (Inl (Statement 4, ())))) (STR ''y'')
     = Ivl (Fin 6) (Fin 20)"
  unfolding twice_sol_def twice_eqs_def by eval

subsection \<open>Registration through the classifier-parametric registration locale\<close>

text \<open>Interpret \<^locale>\<open>unit_dg_exec_analysis\<close> once here at \<open>twice_gs\<close>, matching the
  pattern in \<open>Exec_Sign_DG_Run\<close>, \<open>Example_Parity_DG_Flagship\<close>, and
  \<open>Example_Interval_DG_Flagship\<close>.  The interpretation absorbs the sound-transfer and
  primitive-commutation obligations once, so \<open>twice_source_run_sound\<close> below only
  supplies the compiled-input and solver facts.\<close>

text \<open>
  \<open>reduces\<close> is
  \<open>action_reduces (ivl_tf_st_for twice_gs)\<close>, which holds because
  \<^const>\<open>ivl_tf_st_for\<close>'s value-return case evaluates the edge's own
  \<^typ>\<open>texp\<close> exactly as its \<open>EA_Assign\<close> case does.
\<close>
interpretation twice_ex_reg:
  unit_dg_exec_analysis twice_gs
    "ivl_tf_for twice_gs"
    "ivl_tf_st_for twice_gs"
    "ivl_enter_st_for twice_gs"
    "TD_side_warrowing_apinis_Interp.solve" "TD_side_warrowing_apinis_Interp.solve_c"
proof -
  interpret twice_transfer: sound_transfer_for twice_gs
    "ivl_tf_for twice_gs"
    by (rule ivl_is_sound_transfer_for)
  show "unit_dg_exec_analysis twice_gs (ivl_tf_for twice_gs)
          (ivl_tf_st_for twice_gs)
          (ivl_enter_st_for twice_gs)
          TD_side_warrowing_apinis_Interp.solve TD_side_warrowing_apinis_Interp.solve_c"
    apply unfold_locales
       apply (rule twice_reserved)
      apply (rule ivl_tf_st_for_commute[folded fun_of_exec_dg_st_for_def])
     apply (rule ivl_enter_st_for_commute[folded fun_of_exec_dg_st_for_def])
     apply (simp add: fun_eq_iff)
    apply (simp add: fun_eq_iff)
   apply (simp add: fun_eq_iff)
  apply (erule TD_side_warrowing_apinis_Interp.part_post_solution_of_solve_c)
    done
qed

subsection \<open>Source-level soundness\<close>

lemma twice_wf: "wf_compile_input twice_gs twice_pi twice_procs (STR ''main'') twice_main"
  unfolding wf_compile_input_simps
    twice_pi_def twice_procs_def twice_main_def twice_program_def
  by (auto simp: proc_decl_of_def prog_main_name_def valid_formal_def reserved_ret_var_def
      value_providing_def source_exp_def ret_var_def
      special_table_def special_pname_nondet_int_def
      special_pname_min_def special_pname_max_def
      split: if_splits option.splits)

theorem twice_source_run_sound:
  assumes run: "star (pstep (prog_tyenv twice_program) twice_gs twice_pi)
                  (twice_main, s, [], proc_ret_kind twice_pi (STR ''main'')) src'"
      and init: "s \<in> cinit_stores twice_gs"
      and sty: "styped (prog_tyenv twice_program) s"
  shows "\<exists>v t stk. csim (prog_tyenv twice_program) twice_pi twice_cfg src' (v, t, stk)
                   \<and> t \<in> twice_ex_reg.gamma (snd twice_sol) v"
proof -
  obtain residual t frs rk where src': "src' = (residual, t, frs, rk)" by (cases src')
  have cert:
    "\<exists>v stk. csim (prog_tyenv twice_program) twice_pi twice_cfg (residual, t, frs, rk) (v, t, stk)
       \<and> t \<in> twice_ex_reg.gamma (snd twice_sol) v"
    unfolding twice_cfg_def twice_sol_def twice_eqs_def
    by (rule twice_ex_reg.run_source_sound
          [OF twice_terminates_c[unfolded twice_eqs_def twice_cfg_def]
              twice_wf
              twice_vars_cover[unfolded twice_sol_def twice_eqs_def twice_cfg_def]
              twice_finE[unfolded twice_cfg_def]
              twice_finC[unfolded twice_cfg_def]
              twice_sound0[folded gamma_unit_def]
              init sty run[unfolded src']])
  show ?thesis using cert src' by blast
qed

subsection \<open>Annotated GraphViz of the computed result\<close>

text \<open>
  A DOT rendering of \<open>twice_cfg\<close> annotated with the solver-computed intervals.
  The tooling renders the two \<^const>\<open>CallEdge\<close> entries \<^bold>\<open>distinctly\<close> (thick
  purple, labelled \<open>enter\<close>) and the two combine/return edges as \<^bold>\<open>dashed blue\<close>
  (labelled \<open>combine via call@N\<close>).  Each node is annotated with \<open>p\<close>, \<open>#ret\<close>,
  \<open>x\<close>, \<open>y\<close>; in particular the shared callee entry \<open>FunctionEntry (STR ''twice'')\<close> shows
  \<open>p in [3,10]\<close> and \<open>FunctionResult (STR ''twice'')\<close> shows \<open>#ret in [6,20]\<close>, while the
  continuations \<open>3\<close> / \<open>4\<close> show \<open>x\<close> / \<open>y in [6,20]\<close>.
\<close>

definition twice_graph_config ::
  "(unit, unit, (ivl exec_dg_st, ivl exec_dg_st) dg_state, ivl exec_dg_st) analysis_graph_config" where
  "twice_graph_config =
    \<lparr> local_of = locals,
      route = (\<lambda>_ _ _ _. Some ()),
      context_key = (\<lambda>_. STR ''unit''),
      show_context = (\<lambda>_. ''unit''),
      locals_for_pp = (\<lambda>p.
        let sc = compiled_procedure_scope twice_gs (prog_tyenv twice_program) twice_pi twice_procs (STR ''main'') twice_main
          twice_cfg p
        in scope_formals sc @ scope_locals sc),
      return_slot_for_pp = (\<lambda>p.
        scope_return_slot (compiled_procedure_scope twice_gs (prog_tyenv twice_program) twice_pi twice_procs (STR ''main'') twice_main
          twice_cfg p)),
      globals_to_show = [],
      show_local = (\<lambda>p ctx vars d. map (\<lambda>x.
        String.explode x @ ''='' @ string_of_ivl (twice_lookup d x)) vars),
      format_return = (\<lambda>p ctx ret d.
        if twice_lookup d ret = ivl_top then []
        else [''ret='' @ string_of_ivl (twice_lookup d ret)]),
      show_global = (\<lambda>_ vars s. [''(none)'']),
      show_global_key = (\<lambda>_. ''Global''),
      is_shared_global = (\<lambda>_. True),
      show_internal_globals = False,
      owner_of = String.explode o compiled_owner_of (prog_tyenv twice_program) twice_pi twice_procs (STR ''main'') twice_main,
      cluster_label = (\<lambda>owner _. owner @ '' / context=unit''),
      source_text = Some (pretty_string_of_program twice_pi twice_procs twice_main []),
      node_annotation = (\<lambda>_ _. None)
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



end




