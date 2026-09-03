section \<open>Flagship: interval analysis of a counting loop, executed and certified on the D/G spine\<close>

text \<open>
  \<^bold>\<open>The complete story in one self-contained theory.\<close>  A VIMP program (given inline
  below) is compiled to a CFG; the generic D/G framework generates an equation
  system; the \<^emph>\<open>verified\<close> top-down solver \<^emph>\<open>computes\<close> an interval solution inside
  Isabelle (with interval widening for termination); and the single registered
  endpoint \<open>flagship_ex_reg.run_source_sound\<close> turns that computed solution directly
  into a source-level guarantee.

  \<^verbatim>\<open>
       VIMP source
            |  compile_prog
            v
          CFG
            |  dg_gen_of, executable D/G specification
            v
    D/G equation system
            |  verified solver, by eval
            v
   computed interval solution  sigma
            |  flagship_ex_reg.run_source_sound
            v
   every VIMP source run is bounded by sigma, read through flagship_ex_reg.gamma
  \<close>

  \<^bold>\<open>Every step is machine-checked, and the result is informative:\<close> the analysis
  discovers the loop invariant \<open>x in [0,20]\<close>, the body bound \<open>x in [0,19]\<close>, and the
  exact exit value \<open>x in [20,20]\<close> --- not \<open>top\<close>.  \<open>flagship_ex_reg.run_source_sound\<close>
  bundles executable/pure commutation, D/G collecting soundness, and the
  compiler-correctness simulation into one application, so none of those
  intermediate obligations appear in this file's own proofs -- the solved
  system is never transported to the abstract carrier; the registration
  locale proves soundness directly at the executable one.  A later
  subsection exhibits an explicit reachable state so the guarantee is visibly
  \<^emph>\<open>not vacuous\<close>, reusing the native interval D/G locale from \<open>Interval_DG\<close>; the
  final subsection emits an analysis-annotated GraphViz rendering.

  It reuses, without duplicating: the executable interval transfer \<open>ivl_tf_st_for\<close>
  (\<open>Ivl_Exec\<close>), the registration locale \<open>ownership_split_dg_exec_analysis\<close>
  (\<open>Run_Analysis_Sound\<close>), and the vendored warrowing solver.
\<close>

theory Example_Interval_DG_Flagship
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
    Example_Compile_Call_Free
begin

(* Disambiguate our N constructor from the phase datatype constructor. *)
hide_const phase.N
subsection \<open>The VIMP source program\<close>

text \<open>
  A bounded counting loop: initialise \<open>x\<close> to \<open>0\<close>, increment while \<open>x < 20\<close>.  On
  exit \<open>x = 20\<close>.  No procedures, no globals; \<open>x\<close> is a single flow-sensitive local.
  The analysis must \<^emph>\<open>discover\<close> the bound, not assume it.
\<close>

definition flagship_prog :: imp_prog where
  "flagship_prog = program { void main() { x := 0; while (x < 20) { x := x + 1 } } }"

text \<open>The storage classifier: \<open>flagship_prog\<close> declares no globals, so \<open>flagship_gs\<close>
  classifies \<open>x\<close> as local, matching the \<open>declared_global\<close> pattern used by
  every other flagship rather than the \<open>is_global\<close> naming convention.\<close>
abbreviation flagship_gs :: "vname \<Rightarrow> bool" where
  "flagship_gs \<equiv> declared_global flagship_prog"

subsection \<open>CFG construction\<close>

text \<open>
  The source compiles to an interprocedural CFG by \<open>compile_prog\<close>.  The whole program is
  the body of \<open>main\<close>, so it runs between \<open>FunctionEntry (STR ''main'')\<close> and
  \<open>FunctionResult (STR ''main'')\<close>; inside, \<open>x := 0\<close> falls directly into the loop head \<open>1\<close> (the
  continuation-passing compiler needs no separate join node), the guard \<open>x < 20\<close> branches
  to body \<open>2\<close> or exit \<open>3\<close>, and the increment at \<open>2\<close> jumps back to \<open>1\<close>.  \<open>flagship_cfg\<close>
  is the compilation itself, so the shape lemmas below read off the compiled graph
  rather than a hand-written one; the annotated rendering is in section 10.
\<close>

text \<open>The declaration environment holds exactly \<open>main\<close>: there are no other procedures, and
  \<^const>\<open>wf_compile_input\<close> requires the entry procedure to be declared.\<close>

text \<open>Local shorthand for the executable state's lookup and refinement projections,
  fixed at this file's own \<open>flagship_gs\<close> classifier.\<close>
abbreviation flagship_lookup :: "('a::bot) exec_dg_st \<Rightarrow> vname \<Rightarrow> 'a" where
  "flagship_lookup s x \<equiv> lookup_resolved_st_q s (location_of flagship_gs x)"

abbreviation flagship_fun_of :: "('a::bot) exec_dg_st \<Rightarrow> 'a abs_state" where
  "flagship_fun_of \<equiv> fun_of_resolved_st_q_for flagship_gs"

definition flagship_pi :: proc_table where
  "flagship_pi = prog_table flagship_prog"

definition flagship_cfg :: cfg where
  "flagship_cfg = compile_prog flagship_pi (prog_procs flagship_prog)"

interpretation flagship: compiled_cfg flagship_pi "prog_procs flagship_prog" flagship_cfg
  by (unfold_locales; unfold flagship_cfg_def; simp add: compile_prog_finite)

lemmas flagship_entry = flagship.entry[unfolded prog_main_name_def]

lemma flagship_calls: "calls flagship_cfg = {}"
  unfolding flagship_cfg_def flagship_pi_def
  by (rule compile_prog_calls_empty)
     (simp_all add: flagship_prog_def main_body_def prog_main_name_def)

subsection \<open>Executable interval D/G specification\<close>

text \<open>
  Intervals form the diagonal D/G analysis \<open>D = G = ivl abs_state\<close>, with executable
  mirror \<open>ownership_split_dg_spec_st_for flagship_gs (ivl_tf_st_for flagship_gs)\<close>.  The
  registration \<^locale>\<open>ownership_split_dg_exec_analysis\<close> --- interpreted as \<open>flagship_ex_reg\<close>
  below, at this file's own classifier \<open>flagship_gs\<close>, from \<open>ivl_is_sound_transfer_for\<close>
  and \<open>ivl_tf_st_for_commute\<close> alone --- discharges the transport, soundness, and
  solver-crossing obligations generically.  This example supplies only the program,
  the executable solve, and the coverage witnesses.
\<close>

subsection \<open>Equation generation\<close>

text \<open>
  The generic D/G generator \<open>dg_gen_of\<close> turns the CFG into an equation system over
  unknowns \<open>(pp x unit) + unit\<close>, values in \<open>(ivl exec_dg_st, ivl exec_dg_st) dg_state\<close>.  Locals
  seed at \<open>cinit_ivl_st\<close> (globals \<open>[0,0]\<close>, locals \<open>top\<close>); the flow-insensitive
  global slot seeds at \<open>restrict_global_resolved_q cinit_ivl_st\<close> (bottom on locals, so it
  never pollutes the local \<open>x\<close> through the diagonal read).
\<close>

definition flagship_eqs :: "pp \<times> unit \<Rightarrow> (pp \<times> unit, unit, (ivl exec_dg_st, ivl exec_dg_st) dg_state) strategy_tree" where
  "flagship_eqs = dg_gen_of (ownership_split_dg_spec_st_for flagship_gs (ivl_tf_st_for flagship_gs) (ivl_enter_st_for flagship_gs))
     flagship_cfg bot cinit_ivl_st (restrict_global_resolved_q cinit_ivl_st)"

subsection \<open>Executable solve\<close>

text \<open>
  The vendored \<open>TD_side_warrowing_apinis_Interp_solve_c\<close> --- pointwise interval
  widening on \<open>(ivl exec_dg_st, ivl exec_dg_st) dg_state\<close> for solver termination --- \<^emph>\<open>computes\<close> a
  solution.  Termination is a code-generated \<^verbatim>\<open>by eval\<close> fact; the solution is not
  written by hand.
\<close>

lemma flagship_terminates_c:
  "TD_side_warrowing_apinis_Interp_solve_c flagship_eqs (cfg_exit flagship_cfg, ()) \<noteq> None"
  by eval

definition flagship_sol :: "(pp \<times> unit) set \<times> (pp \<times> unit + unit \<Rightarrow> (ivl exec_dg_st, ivl exec_dg_st) dg_state)" where
  "flagship_sol = TD_side_warrowing_apinis_Interp_solve flagship_eqs (cfg_exit flagship_cfg, ())"

subsection \<open>Soundness premises for the registered endpoint\<close>

text \<open>
  The premises \<open>flagship_ex_reg.run_source_sound\<close> consumes: every program point is
  covered by the solved variable set, the graph is finite and enter-free, and the
  concrete initial stores are covered by the seed.

  Coverage is not read off the solved key set. Every node of \<open>flagship_cfg\<close> reaches
  \<^const>\<open>cfg_exit\<close> --- a structural fact about the graph alone, decided by
  \<^const>\<open>cfg_exit_covers\<close> --- and \<^const>\<open>vars_cover\<close> follows from that together
  with the post-solution the solver already returns.
\<close>

lemma flagship_solve_dom:
  "TD_side_warrowing_apinis_Interp.solve_dom TYPE(unit)
     TYPE((ivl exec_dg_st, ivl exec_dg_st) dg_state)
     flagship_eqs (cfg_exit flagship_cfg, ())"
  by (rule TD_side_warrowing_apinis_Interp.solve_dom_of_solve_c[OF flagship_terminates_c])

lemma flagship_pp_st:
  "part_post_solution flagship_eqs (cfg_exit flagship_cfg, ())
     (snd flagship_sol) (fst flagship_sol)"
  using TD_side_warrowing_apinis_Interp.partial_post_solution
          [OF flagship_solve_dom, of "fst flagship_sol" "snd flagship_sol"]
  unfolding flagship_sol_def by simp

lemma flagship_exit_covers: "cfg_exit_covers flagship_cfg" by eval

lemma flagship_vars_cover: "vars_cover flagship_cfg (fst flagship_sol)"
  by (rule vars_cover_of_dg_gen_of_covers
        [OF flagship.finite_intra flagship.finite_calls flagship.wf flagship_exit_covers
            flagship_pp_st[unfolded flagship_eqs_def]])

lemma flagship_sound0:
  "cinit_stores flagship_gs \<subseteq>
     \<lbrakk>combine_env flagship_gs (fun_of_exec_dg_st_for flagship_gs cinit_ivl_st)
        (fun_of_exec_dg_st_for flagship_gs (restrict_global_resolved_q cinit_ivl_st))\<rbrakk>"
proof -
  have "combine_env flagship_gs (fun_of_exec_dg_st_for flagship_gs cinit_ivl_st)
          (fun_of_exec_dg_st_for flagship_gs (restrict_global_resolved_q cinit_ivl_st))
        = fun_of_exec_dg_st_for flagship_gs cinit_ivl_st"
    by (simp add: combine_env_def fun_of_exec_dg_st_for_def fun_of_st_cinit_ivl_st_for
                  restrict_global_for_def declared_global_def fun_eq_iff)
  thus ?thesis
    by (auto simp: cinit_stores_def gamma_state_def fun_of_exec_dg_st_for_def fun_of_st_cinit_ivl_st_for)
qed

text \<open>
  The coverage facts, finiteness, and the seed-soundness \<open>flagship_sound0\<close> are the
  instance premises the bundled endpoint \<open>flagship_ex_reg.run_source_sound\<close> consumes;
  the collecting-soundness and transport steps are discharged inside it.
\<close>

subsection \<open>Inspecting the certified result\<close>

lemma flagship_head_computed:
  "flagship_lookup (locals (snd flagship_sol (Inl (Statement 1, ())))) (STR ''x'') = Ivl (Fin 0) (Fin 20)"
  unfolding flagship_sol_def flagship_eqs_def by eval

lemma flagship_body_computed:
  "flagship_lookup (locals (snd flagship_sol (Inl (Statement 2, ())))) (STR ''x'') = Ivl (Fin 0) (Fin 19)"
  unfolding flagship_sol_def flagship_eqs_def by eval

lemma flagship_exit_computed:
  "flagship_lookup (locals (snd flagship_sol (Inl (Statement 3, ())))) (STR ''x'') = Ivl (Fin 20) (Fin 20)"
  unfolding flagship_sol_def flagship_eqs_def by eval

subsection \<open>Registration through the classifier-parametric registration locale\<close>

text \<open>Interpret \<^locale>\<open>ownership_split_dg_exec_analysis\<close> once here at \<open>flagship_gs\<close>,
  matching the pattern in \<open>Exec_Sign_DG_Run\<close> and \<open>Example_Parity_DG_Flagship\<close>.
  The interpretation absorbs the sound-transfer and primitive-commutation
  obligations once, so \<open>flagship_source_run_sound\<close> below only supplies the
  compiled-input and solver facts.\<close>

lemma flagship_wf_reserved: "reserved_ret_var flagship_gs"
  by (auto simp: wf_compile_input_simps flagship_pi_def flagship_prog_def split: if_splits)

interpretation flagship_ex_reg:
  ownership_split_dg_exec_analysis flagship_gs
    "ivl_tf_for flagship_gs" "ivl_tf_st_for flagship_gs" "ivl_enter_st_for flagship_gs"
    "TD_side_warrowing_apinis_Interp.solve" "TD_side_warrowing_apinis_Interp.solve_c"
proof -
  interpret flagship_ex_transfer: sound_transfer_for flagship_gs "ivl_tf_for flagship_gs"
    by (rule ivl_is_sound_transfer_for)
  show "ownership_split_dg_exec_analysis flagship_gs (ivl_tf_for flagship_gs) (ivl_tf_st_for flagship_gs)
          (ivl_enter_st_for flagship_gs)
          TD_side_warrowing_apinis_Interp.solve TD_side_warrowing_apinis_Interp.solve_c"
    by unfold_locales
       (rule flagship_wf_reserved
             flagship_ex_transfer.tf_sound_assign_for flagship_ex_transfer.tf_sound_special_for
             flagship_ex_transfer.tf_sound_branch_for
             flagship_ex_transfer.tf_sound_enter_entry_for flagship_ex_transfer.tf_sound_combine_env_for
             ivl_tf_st_for_commute[folded fun_of_exec_dg_st_for_def]
             ivl_enter_st_for_commute[folded fun_of_exec_dg_st_for_def]
             TD_side_warrowing_apinis_Interp.part_post_solution_of_solve_c)+
qed

text \<open>
  The registered endpoint \<open>flagship_ex_reg.run_source_sound\<close> turns the single \<^theory_text>\<open>by eval\<close>
  solver success \<open>flagship_terminates_c\<close> directly into a source-level guarantee: every
  reachable VIMP store is bounded by the computed interval at its matched program point,
  read through the semantic accessor \<open>flagship_ex_reg.gamma\<close>.  No transport lemma,
  \<^const>\<open>part_post_solution\<close>, \<open>solve_dom\<close>, or \<open>fun_of_dg_st_for\<close> appears in this proof.
\<close>

lemma flagship_wf:
  "wf_compile_input flagship_gs flagship_pi (prog_procs flagship_prog)"
  by (auto simp: wf_compile_input_simps flagship_pi_def flagship_prog_def split: if_splits)

theorem flagship_source_run_sound:
  assumes run: "star (pstep flagship_gs flagship_pi) (prog_main flagship_prog, s, []) (residual, t, frs)"
      and init: "s \<in> cinit_stores flagship_gs"
  shows "\<exists>v stk. csim flagship_pi flagship_cfg (residual, t, frs) (v, t, stk)
                 \<and> t \<in> flagship_ex_reg.gamma (snd flagship_sol) v"
proof -
  have run': "star (pstep flagship_gs flagship_pi) (main_body flagship_pi, s, []) (residual, t, frs)"
    using run by (simp add: flagship_pi_def)
  show ?thesis
    unfolding flagship_sol_def flagship_eqs_def flagship_cfg_def
    by (rule flagship_ex_reg.run_source_sound
          [OF flagship_terminates_c[unfolded flagship_eqs_def flagship_cfg_def]
              flagship_wf
              flagship_vars_cover[unfolded flagship_sol_def flagship_eqs_def flagship_cfg_def]
              flagship.finite_intra[unfolded flagship_cfg_def]
              flagship.finite_calls[unfolded flagship_cfg_def]
              flagship_sound0[folded gamma_ownership_split_def, folded flagship_ex_reg.gamma_ownership_split_exec_def]
              init run'])
qed



text \<open>
  \<^bold>\<open>The bound is proper.\<close>  \<open>x\<close> is a local name (\<open>flagship_x_not_global\<close>), so
  \<^const>\<open>combine_env\<close> routes it to the local answer directly, never through
  the global/side slot; the loop-head concretization therefore constrains
  \<open>x\<close> to exactly \<open>[0,20]\<close> and rejects, e.g., a store with \<open>x = 100\<close>.  The
  guarantee therefore says something --- it is not the trivial
  \<open>gamma top = UNIV\<close>. (\<open>glob_x_at_head\<close> records, independently, that the
  global slot has no information for \<open>x\<close> either --- unsurprising for a
  purely local name, and not needed by the bound's own proof.)
\<close>

lemma glob_x_at_head: "flagship_lookup (globs (snd flagship_sol (Inr ()))) (STR ''x'') = bot"
  unfolding flagship_sol_def flagship_eqs_def by eval

lemma flagship_x_not_global: "\<not> flagship_gs (STR ''x'')"
  unfolding flagship_pi_def flagship_prog_def by (simp add: declared_global_def)

lemma head_x_bound:
  "combine_env flagship_gs
     (locals ((fun_of_dg_st_for flagship_gs \<circ> snd flagship_sol) (Inl (Statement (Suc 0), ()))))
     (globs ((fun_of_dg_st_for flagship_gs \<circ> snd flagship_sol) (Inr ()))) (STR ''x'') = Ivl (Fin 0) (Fin 20)"
proof -
  have L: "flagship_fun_of (locals (snd flagship_sol (Inl (Statement (Suc 0), ())))) (STR ''x'') = Ivl (Fin 0) (Fin 20)"
    using flagship_head_computed
    by (simp add: fun_of_resolved_st_q_for_def)
  have C: "combine_env flagship_gs
             (flagship_fun_of (locals (snd flagship_sol (Inl (Statement (Suc 0), ())))))
             (flagship_fun_of (globs (snd flagship_sol (Inr ())))) (STR ''x'')
           = flagship_fun_of (locals (snd flagship_sol (Inl (Statement (Suc 0), ())))) (STR ''x'')"
    by (rule combine_env_local_eq[where gs = flagship_gs and x = "STR ''x''",
          OF flagship_x_not_global])
  show ?thesis
    by (metis (no_types, opaque_lifting) C L comp_apply fun_of_dg_st_for_simps(1,2)
        fun_of_exec_dg_st_for_def)
qed

theorem flagship_head_bound_proper:
  "(\<lambda>_. 100) \<notin> dg_hook_gamma (gamma_ownership_split flagship_gs)
                 (fun_of_dg_st_for flagship_gs \<circ> snd flagship_sol) (Statement (Suc 0))"
  unfolding dg_hook_gamma_def gamma_ownership_split_def gamma_state_def
            dg_hook_D_def dg_hook_G_def
  apply (simp only: mem_Collect_eq not_all)
  apply (rule exI[of _ "(STR ''x'')"])
  using head_x_bound apply (simp add: fun_of_dg_st_for_simps combine_env_def)
  done

subsection \<open>Annotated GraphViz of the computed result\<close>

text \<open>
  A DOT rendering of \<open>flagship_cfg\<close> with each node annotated by the computed
  interval for \<open>x\<close>.  The \<^verbatim>\<open>ML_val\<close> below prints the DOT as a plain string; paste
  it into any GraphViz renderer (\<^verbatim>\<open>dot -Tpng\<close>) to view the analysed loop, each
  node labelled with the loop-invariant interval the verified solver computed.
\<close>

definition flagship_graph_config ::
  "(unit, unit, (ivl exec_dg_st, ivl exec_dg_st) dg_state, ivl exec_dg_st) analysis_graph_config" where
  "flagship_graph_config =
    \<lparr> local_of = locals,
      route = (\<lambda>_ _ _ _. Some ()),
      context_key = (\<lambda>_. STR ''unit''),
      show_context = (\<lambda>_. ''unit''),
      locals_for_pp = (\<lambda>p.
        scope_locals (compiled_procedure_scope flagship_gs Map.empty []
          flagship_cfg p)),
      return_slot_for_pp = (\<lambda>p.
        scope_return_slot (compiled_procedure_scope flagship_gs Map.empty []
          flagship_cfg p)),
      globals_to_show = [],
      show_local = (\<lambda>_ _ vars d. map (\<lambda>x.
        String.explode x @ ''='' @ string_of_ivl (flagship_lookup d x)) vars),
      format_return = (\<lambda>_ _ _ _. []),
      show_global = (\<lambda>_ _ _. [''(none)'']),
      show_global_key = (\<lambda>_. ''Global''),
      is_shared_global = (\<lambda>_. True),
      show_internal_globals = False,
      owner_of = (\<lambda>_. ''main''),
      cluster_label = (\<lambda>_ _. ''main / root context''),
      source_text = Some (pretty_string_of_program Map.empty [] (prog_main flagship_prog) []),
      node_annotation = (\<lambda>_ _. None)
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


end




