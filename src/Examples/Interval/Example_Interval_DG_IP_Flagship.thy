theory Example_Interval_DG_IP_Flagship
  imports
    "Voblint_Framework.DG_LTR_Sound"
    "Voblint_Analysis.Interval_Transfer"
    "Voblint_Analysis.Ivl_Exec"
    "Voblint_Solver.TD_Solver_Bridge"
    "Voblint_Exec.DG_Coverage"
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
  "twice_cfg = compile_prog twice_pi twice_procs"

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

interpretation twice: compiled_cfg twice_pi twice_procs twice_cfg
  by (unfold_locales; unfold twice_cfg_def; simp add: compile_prog_finite)

text \<open>The two call edges' shape, computed directly from \<open>twice_cfg\<close>: each call site \<open>u\<close>
  pins down its destination variable, callee, arguments, and continuation. Exported for the
  routed/context-sensitive sibling \<open>Example_Interval_DG_Ctx_Collect\<close>, which case-splits on
  the same two call sites.\<close>
lemma twice_calls_shape:
  "\<forall>(u, ca, ce, cont) \<in> calls twice_cfg.
     case ca of CallEdge dst pars args \<Rightarrow>
       (case ce of FunctionEntry p \<Rightarrow>
          (u = Statement 2 \<and> dst = Some (STR ''x'') \<and> pars = [(STR ''p'')] \<and> args = [VIMP_Syntax.N 3]
             \<and> p = (STR ''twice'') \<and> cont = Statement 3) \<or>
          (u = Statement 3 \<and> dst = Some (STR ''y'') \<and> pars = [(STR ''p'')] \<and> args = [VIMP_Syntax.N 10]
             \<and> p = (STR ''twice'') \<and> cont = Statement 4)
        | _ \<Rightarrow> True)"
  unfolding twice_cfg_def by eval

text \<open>Each call site has exactly one outgoing edge.\<close>
lemma twice_calls_unique_site:
  "\<forall>(u1, ca1, ce1, k1) \<in> calls twice_cfg. \<forall>(u2, ca2, ce2, k2) \<in> calls twice_cfg.
      u1 = u2 \<longrightarrow> ca1 = ca2 \<and> ce1 = ce2 \<and> k1 = k2"
  unfolding twice_cfg_def by eval

lemmas twice_finE = twice.finite_intra
lemmas twice_finC = twice.finite_calls

subsection \<open>The analysis specification (interval, as an executable D/G analysis)\<close>

text \<open>
  Intervals form the diagonal D/G analysis \<open>D = G = ivl abs_state\<close>, with executable
  mirror \<open>ownership_split_dg_spec_st_for twice_gs (ivl_tf_st_for twice_gs)\<close>.  The registration
  \<^locale>\<open>ownership_split_dg_exec_analysis\<close> --- interpreted as \<open>twice_ex_reg\<close> below, at this
  file's own classifier \<open>twice_gs\<close>, from \<open>ivl_is_sound_transfer_for\<close> and
  \<open>ivl_tf_st_for_commute\<close> alone --- discharges the transport, soundness, and
  solver-crossing obligations generically.  This example supplies only the program,
  the executable solve, and the coverage witnesses.
\<close>

lemma twice_reserved: "reserved_ret_var twice_gs"
  by (auto simp: wf_compile_input_simps
      twice_pi_def twice_procs_def twice_main_def twice_program_def
      split: if_splits option.splits)

subsection \<open>Equation generation\<close>

definition twice_eqs ::
  "pp \<times> unit \<Rightarrow> (pp \<times> unit, unit, (ivl exec_dg_st, ivl exec_dg_st) dg_state) strategy_tree" where
  "twice_eqs = dg_gen_of (ownership_split_dg_spec_st_for twice_gs (ivl_tf_st_for twice_gs) (ivl_enter_st_for twice_gs))
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

subsection \<open>Soundness premises for the registered endpoint\<close>

text \<open>
  The premises \<open>twice_ex_reg.run_source_sound\<close> consumes: every program point is
  covered by the solved variable set, the graph is finite and enter-free, and the
  concrete initial stores are covered by the seed.

  Coverage is not read off the solved key set. Every node of \<open>twice_cfg\<close> ---
  including both callee entries and both continuations --- reaches
  \<^const>\<open>cfg_exit\<close>, a structural fact about the graph alone decided by
  \<^const>\<open>cfg_exit_covers\<close>, and \<^const>\<open>vars_cover\<close> follows from that together with
  the post-solution the solver already returns.\<close>

lemmas twice_wf_cfg = twice.wf

lemma twice_exit_covers: "cfg_exit_covers twice_cfg" by eval

lemma twice_vars_cover: "vars_cover twice_cfg (fst twice_sol)"
  by (rule vars_cover_of_dg_gen_of_covers
        [OF twice_finE twice_finC twice_wf_cfg twice_exit_covers
            twice_pp_st[unfolded twice_eqs_def]])
lemma twice_sound0:
  "cinit_stores twice_gs \<subseteq>
     \<lbrakk>combine_env twice_gs (fun_of_exec_dg_st_for twice_gs cinit_ivl_st)
        (fun_of_exec_dg_st_for twice_gs (restrict_global_resolved_q cinit_ivl_st))\<rbrakk>"
proof -
  have "combine_env twice_gs (fun_of_exec_dg_st_for twice_gs cinit_ivl_st)
          (fun_of_exec_dg_st_for twice_gs (restrict_global_resolved_q cinit_ivl_st))
        = fun_of_exec_dg_st_for twice_gs cinit_ivl_st"
    by (simp add: combine_env_def fun_of_exec_dg_st_for_def fun_of_st_cinit_ivl_st_for
                  restrict_global_for_def declared_global_def fun_eq_iff)
  thus ?thesis
    by (auto simp: cinit_stores_def gamma_state_def fun_of_exec_dg_st_for_def fun_of_st_cinit_ivl_st_for)
qed

text \<open>
  The coverage facts, finiteness, and the seed-soundness \<open>twice_sound0\<close> are the
  instance premises the bundled endpoint \<open>twice_ex_reg.run_source_sound\<close> consumes;
  the collecting-soundness and transport steps are discharged inside it.
\<close>

subsection \<open>Inspecting the certified result\<close>

lemma twice_p_at_entry:
  "twice_lookup (locals (snd twice_sol (Inl (FunctionEntry (STR ''twice''), ())))) (STR ''p'')
     = Ivl (Fin 3) (Fin 10)"
  unfolding twice_sol_def twice_eqs_def by eval

lemma twice_ret_at_exit:
  "twice_lookup (locals (snd twice_sol (Inl (FunctionResult (STR ''twice''), ())))) (STR ''#ret'')
     = Ivl (Fin 6) (Fin 20)"
  unfolding twice_sol_def twice_eqs_def by eval

lemma twice_x_computed:
  "twice_lookup (locals (snd twice_sol (Inl (Statement 3, ())))) (STR ''x'') = Ivl (Fin 6) (Fin 20)"
  unfolding twice_sol_def twice_eqs_def by eval

lemma twice_y_computed:
  "twice_lookup (locals (snd twice_sol (Inl (Statement 4, ())))) (STR ''y'') = Ivl (Fin 6) (Fin 20)"
  unfolding twice_sol_def twice_eqs_def by eval

subsection \<open>Registration through the classifier-parametric registration locale\<close>

text \<open>Interpret \<^locale>\<open>ownership_split_dg_exec_analysis\<close> once here at \<open>twice_gs\<close>, matching the
  pattern in \<open>Exec_Sign_DG_Run\<close>, \<open>Example_Parity_DG_Flagship\<close>, and
  \<open>Example_Interval_DG_Flagship\<close>.  The interpretation absorbs the sound-transfer and
  primitive-commutation obligations once, so \<open>twice_source_run_sound\<close> below only
  supplies the compiled-input and solver facts.\<close>
interpretation twice_ex_reg:
  ownership_split_dg_exec_analysis twice_gs
    skip_ivl assign_ivl special_ivl branch_ivl body_ivl return_ivl
    "enter_ivl_ci_for twice_gs" event_ivl
    "ivl_tf_st_for twice_gs" "ivl_enter_st_for twice_gs"
    "TD_side_warrowing_apinis_Interp.solve" "TD_side_warrowing_apinis_Interp.solve_c"
proof -
  interpret twice_transfer: sound_transfer_for twice_gs
      skip_ivl assign_ivl special_ivl branch_ivl body_ivl return_ivl
      "enter_ivl_ci_for twice_gs" event_ivl
    by (rule ivl_is_sound_transfer_for)
  show "ownership_split_dg_exec_analysis twice_gs
          skip_ivl assign_ivl special_ivl branch_ivl body_ivl return_ivl
          (enter_ivl_ci_for twice_gs) event_ivl
          (ivl_tf_st_for twice_gs)
          (ivl_enter_st_for twice_gs)
          TD_side_warrowing_apinis_Interp.solve TD_side_warrowing_apinis_Interp.solve_c"
    by unfold_locales
       (rule twice_reserved
             twice_transfer.tf_sound_assign_for twice_transfer.tf_sound_special_for
             twice_transfer.tf_sound_branch_for
             twice_transfer.tf_sound_enter_entry_for
             ivl_tf_st_for_commute[unfolded ivl_tf_abs_def, folded fun_of_exec_dg_st_for_def]
             ivl_enter_st_for_commute[folded fun_of_exec_dg_st_for_def]
             TD_side_warrowing_apinis_Interp.part_post_solution_of_solve_c
        | assumption)+
qed

subsection \<open>Source-level soundness\<close>

lemma twice_main_body [simp]: "main_body twice_pi = twice_main"
  by (simp add: main_body_def prog_main_name_def twice_pi_def twice_program_def
        twice_main_def)

lemma twice_wf: "wf_compile_input twice_gs twice_pi twice_procs"
  by (auto simp: wf_compile_input_simps
      twice_pi_def twice_procs_def twice_main_def twice_program_def
      split: if_splits option.splits)

theorem twice_source_run_sound:
  assumes run: "star (pstep twice_gs twice_pi) (twice_main, s, []) src'"
      and init: "s \<in> cinit_stores twice_gs"
  shows "\<exists>v t stk. csim twice_pi twice_cfg src' (v, t, stk)
                   \<and> t \<in> twice_ex_reg.gamma (snd twice_sol) v"
proof -
  obtain residual t frs where src': "src' = (residual, t, frs)" by (cases src')
  have run': "star (pstep twice_gs twice_pi) (main_body twice_pi, s, []) (residual, t, frs)"
    using run[unfolded src'] by simp
  have cert:
    "\<exists>v stk. csim twice_pi twice_cfg (residual, t, frs) (v, t, stk)
       \<and> t \<in> twice_ex_reg.gamma (snd twice_sol) v"
    unfolding twice_cfg_def twice_sol_def twice_eqs_def
    by (rule twice_ex_reg.run_source_sound
          [OF twice_terminates_c[unfolded twice_eqs_def twice_cfg_def]
              twice_wf
              twice_vars_cover[unfolded twice_sol_def twice_eqs_def twice_cfg_def]
              twice_finE[unfolded twice_cfg_def]
              twice_finC[unfolded twice_cfg_def]
              twice_sound0[folded gamma_ownership_split_def, folded twice_ex_reg.gamma_ownership_split_exec_def]
              init run'])
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
        let sc = compiled_procedure_scope twice_gs twice_pi twice_procs
          twice_cfg p
        in scope_formals sc @ scope_locals sc),
      return_slot_for_pp = (\<lambda>p.
        scope_return_slot (compiled_procedure_scope twice_gs twice_pi twice_procs
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
      owner_of = String.explode o compiled_owner_of twice_pi twice_procs,
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




