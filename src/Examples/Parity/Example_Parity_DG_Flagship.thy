
section \<open>Flagship: parity analysis of an even-step loop, executed and certified on the D/G spine\<close>

text \<open>
  \<^bold>\<open>Second domain, same registration.\<close>  This theory is the E1 validation of the
  domain-registration API: parity registers through the \<open>base_dg_exec_analysis\<close>
  locale (as \<open>parity_ex_reg\<close> below, at this file's own storage classifier
  \<open>parity_gs\<close>) with \<^emph>\<open>no\<close> copied \<open>Hstep\<close>, \<open>Hcomb\<close>, \<open>strategy_tree\<close>, \<open>Inl\<close>/\<open>Inr\<close>,
  or manual post-solution transport lemmas.  An IMP2 program is compiled to a
  CFG; the generic D/G framework generates the equation system; the
  \<^emph>\<open>verified\<close> always-join solver \<^emph>\<open>computes\<close> a parity solution inside
  Isabelle (finite lattice, no widening needed); and the single registered
  endpoint \<open>parity_ex_reg.run_source_sound\<close> lifts the result to actual
  source runs.

  The result is informative: the analysis \<^emph>\<open>discovers\<close> that \<open>x\<close> is even at every
  program point (\<open>x = 0\<close> initially, then \<open>x := x + 2\<close> preserves parity), so the loop
  invariant \<open>x\<close> even holds without any guard refinement --- parity ignores the guard.

  Registration is on the generic Base construction (\<open>DG_Base_Exec\<close>), matching
  Sign's own production route: the local unknown carries the whole
  reachability-lifted \<open>parity exec_dg_st\<close>,
  locals and \<open>total\<close> (the one declared global) alike, with no separate
  flow-insensitive \<open>G\<close> slot to reconstruct through. \<open>total\<close> is therefore
  read back the same way as \<open>x\<close> and \<open>Gcount\<close> below: through the local
  unknown at a program point, not through a global summary.
\<close>

theory Example_Parity_DG_Flagship
  imports
    "Voblint_Core.Exec_DG_Bridge"
    "Voblint_Core.DG_Base_Exec"
    "Voblint_Analysis.Parity_Exec"
    "Voblint_Analysis.Parity_Print"
    "Voblint_Core.Solver_Menu"
    "Voblint_Core.DG_Coverage"
    "Voblint_CFG.CFG_Prune"
    "Voblint_Analysis.Analysis_GraphViz"
    "Voblint_VIMP.VIMP_Notation"
    "Voblint_Soundness.Run_Analysis_Sound"
    Example_Compile_Call_Free
begin

hide_const (open) Update_rules.N

subsection \<open>1. The program (proper IMP2 program notation, explicit main)\<close>

text \<open>
  A bounded counting loop that increments by two: initialise \<open>x\<close> to \<open>0\<close>,
  add \<open>2\<close> while \<open>x < 20\<close>.  No procedures beyond \<open>main\<close>; \<open>x\<close> is a single
  flow-sensitive local, \<open>Gcount\<close> a second, \<open>G\<close>-prefixed local, and \<open>total\<close>
  the one declared global despite carrying no naming hint. The parity of
  \<open>x\<close> stays even at every reachable point regardless of the guard, which the
  analysis must discover, not assume.
\<close>

definition parity_program :: imp_prog where
  "parity_program = program {

      global total;

      void main() {
        x := 0;
        Gcount:=1;
        while (x < 20) {
          x := x + 2;
          Gcount:=Gcount + 1
        };
        total:= x + Gcount
      }
}"

definition parity_prog :: "VIMP_Proc.com" where
  "parity_prog = prog_main parity_program"

text \<open>The storage classifier: \<open>total\<close> is declared global despite its plain
  name, and \<open>Gcount\<close> stays local despite its \<open>G\<close> prefix, so \<open>parity_gs\<close> is
  the M4 entry point for a family that actually exercises global/local
  separation through the program's own declaration, not a naming
  convention (see \<open>parity_total_global\<close>/\<open>parity_gcount_not_global\<close> below).\<close>
abbreviation parity_gs :: "vname \<Rightarrow> bool" where
  "parity_gs \<equiv> declared_global parity_program"

lemma parity_total_global [simp]: "parity_gs (STR ''total'')"
  by (simp add: parity_program_def)

lemma parity_gcount_not_global [simp]: "\<not> parity_gs (STR ''Gcount'')"
  by (simp add: parity_program_def)

text \<open>
  The Base construction routes the whole abstract state through the local
  unknown, reachability-lifted: \<open>parity_lookup\<close> reads a computed \<open>exec_dg_st
  lifted\<close> value back through \<^const>\<open>fun_of_exec_dg_st_for\<close>, matching
  Sign's own DG flagship -- a genuinely unreachable local unknown (\<open>Bot\<close>)
  reads back as \<open>PTop\<close>, never spuriously observed here since every inspected
  node below is reachable.
\<close>
abbreviation parity_lookup :: "parity exec_dg_st lifted \<Rightarrow> vname \<Rightarrow> parity" where
  "parity_lookup d x \<equiv> (case map_lift (fun_of_exec_dg_st_for parity_gs) d of Lifted f \<Rightarrow> f x | Bot \<Rightarrow> PTop)"

definition parity_pi :: proc_table where
  "parity_pi = prog_table parity_program"

subsection \<open>2. CFG construction\<close>

text \<open>
  The source compiles to an interprocedural CFG by \<open>compile_prog\<close>, exactly like the
  interval flagship's counting loop --- same topology, only the increment differs.
\<close>

definition parity_cfg :: cfg where
  "parity_cfg = compile_prog parity_pi []"

lemma parity_finE: "finite (intra parity_cfg)" and parity_finC: "finite (calls parity_cfg)"
  unfolding parity_cfg_def
  using compile_prog_finite by auto

lemma parity_calls: "calls parity_cfg = {}"
  unfolding parity_cfg_def parity_pi_def
  by (rule compile_prog_calls_empty)
     (simp_all add: parity_prog_def parity_program_def main_body_def prog_main_name_def)

subsection \<open>3. Executable parity D/G specification\<close>

text \<open>
  Parity forms the Base D/G analysis, with executable mirror
  \<^const>\<open>base_dg_spec_st_for_lifted\<close> \<open>parity_gs\<close> over \<open>parity_tf_st_for\<close>/
  \<open>parity_enter_st_for\<close>.  The registration \<^locale>\<open>base_dg_exec_analysis\<close> ---
  interpreted as \<open>parity_ex_reg\<close> below, at this file's own classifier
  \<open>parity_gs\<close>, from \<open>parity_is_sound_transfer_for\<close> and
  \<open>parity_tf_st_for_commute\<close> alone --- discharges the transport, soundness, and
  solver-crossing obligations generically.  This example supplies only the program,
  the executable solve, and the coverage witnesses.
\<close>

subsection \<open>4. Equation generation\<close>

definition parity_eqs :: "pp \<times> unit \<Rightarrow> (pp \<times> unit, unit, (parity exec_dg_st lifted, parity exec_dg_st lifted) dg_state) strategy_tree" where
  "parity_eqs = dg_gen_of
     (base_dg_spec_st_for_lifted parity_gs (resolved_st_q_is_bot_for (declared_global_vars parity_program))
       (parity_tf_st_for parity_gs) (parity_enter_st_for parity_gs))
     parity_cfg bot (Lifted cinit_parity_st) (Lifted cinit_parity_st)"

subsection \<open>5. Executable solve (always-join; parity is finite-height)\<close>

lemma parity_terminates_c:
  "TD_side_always_join_Interp_solve_c parity_eqs (cfg_exit parity_cfg, ()) \<noteq> None"
  by eval

definition parity_sol :: "(pp \<times> unit) set \<times> (pp \<times> unit + unit \<Rightarrow> (parity exec_dg_st lifted, parity exec_dg_st lifted) dg_state)" where
  "parity_sol = TD_side_always_join_Interp_solve parity_eqs (cfg_exit parity_cfg, ())"

subsection \<open>6. Soundness premises for the registered endpoint\<close>

text \<open>Coverage is not read off the solved key set. Every node of \<open>parity_cfg\<close> reaches
  \<^const>\<open>cfg_exit\<close> --- a structural fact about the graph alone, decided by
  \<^const>\<open>cfg_exit_covers\<close> --- and \<^const>\<open>vars_cover\<close> follows from that together
  with the post-solution the solver already returns.\<close>

lemma parity_solve_dom:
  "TD_side_always_join_Interp.solve_dom TYPE(unit)
     TYPE((parity exec_dg_st lifted, parity exec_dg_st lifted) dg_state)
     parity_eqs (cfg_exit parity_cfg, ())"
  by (rule TD_side_always_join_Interp.solve_dom_of_solve_c[OF parity_terminates_c])

lemma parity_pp_st:
  "part_post_solution parity_eqs (cfg_exit parity_cfg, ()) (snd parity_sol) (fst parity_sol)"
  using TD_side_always_join_Interp.partial_post_solution
          [OF parity_solve_dom, of "fst parity_sol" "snd parity_sol"]
  unfolding parity_sol_def by simp

lemma parity_wf_cfg: "wf_cfg parity_cfg"
  unfolding parity_cfg_def by (rule compile_prog_wf)

lemma parity_exit_covers: "cfg_exit_covers parity_cfg" by eval

lemma parity_vars_cover: "vars_cover parity_cfg (fst parity_sol)"
  by (rule vars_cover_of_dg_gen_of_covers
        [OF parity_finE parity_finC parity_wf_cfg parity_exit_covers
            parity_pp_st[unfolded parity_eqs_def]])
lemma parity_is_bot_exact:
  "\<And>s. resolved_st_q_is_bot_for (declared_global_vars parity_program) s = is_bot_state (fun_of_exec_dg_st_for parity_gs s)"
  by (rule resolved_st_q_is_bot_for_iff[OF declared_global_iff, folded fun_of_exec_dg_st_for_def])

lemma parity_sound0:
  "cinit_stores parity_gs \<subseteq> gamma_dg_base (map_lift (fun_of_exec_dg_st_for parity_gs) (Lifted cinit_parity_st))
                                (map_lift (fun_of_exec_dg_st_for parity_gs) (Lifted cinit_parity_st))"
  by (auto simp add: fun_of_exec_dg_st_for_def fun_of_st_cinit_parity_st_for cinit_stores_def gamma_state_def
      gamma_dg_base_def)

subsection \<open>7. Inspecting the certified result\<close>

lemma parity_head_computed:
  "parity_lookup (locals (snd parity_sol (Inl (Statement (Suc 0), ())))) (STR ''x'') = PEven"
  unfolding parity_sol_def parity_eqs_def by eval

lemma parity_exit_computed:
  "parity_lookup (locals (snd parity_sol (Inl (Statement 3, ())))) (STR ''x'') = PEven"
  unfolding parity_sol_def parity_eqs_def by eval

subsection \<open>8. Source-level soundness through the registered analysis\<close>

text \<open>
  The registered endpoint \<open>parity_ex_reg.run_source_sound\<close> turns the single \<open>by eval\<close>
  solver success \<open>parity_terminates_c\<close> directly into a source-level guarantee: every
  reachable IMP2 store is bounded by the computed parity at its matched program point,
  read through the semantic accessor \<open>parity_ex_reg.gamma\<close>.  No transport lemma,
  \<^const>\<open>part_post_solution\<close>, \<open>solve_dom\<close>, or \<open>fun_of_dg_st_for\<close> appears in this proof.
\<close>

lemma parity_main_body [simp]: "main_body parity_pi = parity_prog"
  by (simp add: main_body_def prog_main_name_def parity_pi_def parity_program_def
        parity_prog_def)

lemma parity_wf: "wf_compile_input parity_gs parity_pi []"
  by (auto simp: wf_compile_input_simps parity_pi_def parity_prog_def parity_program_def
      split: if_splits)

text \<open>Interpret \<^locale>\<open>base_dg_exec_analysis\<close> once here at \<^const>\<open>parity_gs\<close> with
  the classifier-parametric transfer/enter functions, matching the pattern in
  \<open>Exec_Sign_DG_Run\<close>.  The interpretation absorbs the sound-transfer, primitive-
  commutation, and \<open>is_bot_pred\<close>-exactness obligations once, so
  \<open>parity_source_run_sound\<close> below only supplies the compiled-input and solver
  facts.\<close>

interpretation parity_ex_reg:
  base_dg_exec_analysis parity_gs
    "parity_tf_for parity_gs" "parity_tf_st_for parity_gs" "parity_enter_st_for parity_gs"
    "resolved_st_q_is_bot_for (declared_global_vars parity_program)"
    "TD_side_always_join_Interp.solve" "TD_side_always_join_Interp.solve_c"
proof -
  interpret parity_ex_transfer: sound_transfer_for parity_gs "parity_tf_for parity_gs"
    by (rule parity_is_sound_transfer_for)
  show "base_dg_exec_analysis parity_gs (parity_tf_for parity_gs) (parity_tf_st_for parity_gs)
          (parity_enter_st_for parity_gs) (resolved_st_q_is_bot_for (declared_global_vars parity_program))
          TD_side_always_join_Interp.solve TD_side_always_join_Interp.solve_c"
    by unfold_locales
       (rule parity_wf[THEN wf_compile_input_reserved_ret_var]
             parity_ex_transfer.tf_sound_assign_for parity_ex_transfer.tf_sound_special_for
             parity_ex_transfer.tf_sound_branch_for
             parity_ex_transfer.tf_sound_enter_for parity_ex_transfer.tf_sound_combine_env_for
             parity_tf_st_for_commute[folded fun_of_exec_dg_st_for_def]
             parity_enter_st_for_commute[folded fun_of_exec_dg_st_for_def]
             parity_is_bot_exact
             TD_side_always_join_Interp.part_post_solution_of_solve_c)+
qed

theorem parity_source_run_sound:
  assumes run: "star (pstep parity_gs parity_pi) (parity_prog, s, []) (residual, t, frs)"
      and init: "s \<in> cinit_stores parity_gs"
  shows "\<exists>v stk. csim parity_pi parity_cfg (residual, t, frs) (v, t, stk)
                 \<and> t \<in> parity_ex_reg.gamma (snd parity_sol) v"
proof -
  have run': "star (pstep parity_gs parity_pi) (main_body parity_pi, s, []) (residual, t, frs)"
    using run by simp
  show ?thesis
    unfolding parity_sol_def parity_eqs_def parity_cfg_def
    by (rule parity_ex_reg.run_source_sound
          [OF parity_terminates_c[unfolded parity_eqs_def parity_cfg_def]
              parity_wf
              parity_vars_cover[unfolded parity_sol_def parity_eqs_def parity_cfg_def]
              parity_finE[unfolded parity_cfg_def]
              parity_finC[unfolded parity_cfg_def]
              parity_sound0
              init run'])
qed

subsection \<open>9. The result is not vacuous\<close>

text \<open>
  The computed loop-head value for \<open>x\<close> is \<open>PEven\<close>, strictly below \<open>PTop\<close>: the
  analysis genuinely discovered that \<open>x\<close> is even, and its concretization excludes
  every odd integer.  The guarantee therefore says something.
\<close>

lemma parity_head_proper:
  "parity_lookup (locals (snd parity_sol (Inl (Statement (Suc 0), ())))) (STR ''x'') \<noteq> PTop"
  by (simp add: parity_head_computed)

lemma parity_head_excludes_odd:
  "n \<in> gamma_parity (parity_lookup (locals (snd parity_sol (Inl (Statement (Suc 0), ())))) (STR ''x''))
     \<Longrightarrow> even n"
  by (simp add: parity_head_computed)

subsection \<open>10. Annotated GraphViz of the computed result\<close>

text \<open>
  A DOT rendering of \<open>parity_cfg\<close> with each node annotated by the computed
  parity for \<open>x\<close>, \<open>Gcount\<close>, and \<open>total\<close> alike: the Base construction keeps
  \<open>total\<close> inside the same reachability-lifted local unknown as every other
  variable, so it is rendered per program point rather than through a
  separate global summary node -- \<open>globals_to_show\<close> stays empty and
  \<open>show_global\<close> renders nothing. The \<open>ML_val\<close> below prints the DOT as a
  plain string; paste it into any GraphViz renderer (\<open>dot -Tpng\<close>) to view
  the analysed loop, each node labelled with the loop-invariant parity the
  verified solver computed.
\<close>

definition parity_graph_config ::
  "(unit, unit, (parity exec_dg_st lifted, parity exec_dg_st lifted) dg_state, parity exec_dg_st lifted) analysis_graph_config" where
  "parity_graph_config =
    \<lparr> local_of = locals,
      route = (\<lambda>_ _ _ _. Some ()),
      context_key = (\<lambda>_. STR ''unit''),
      show_context = (\<lambda>_. ''unit''),
      locals_for_pp = (\<lambda>p.
        scope_locals (compiled_procedure_scope parity_gs parity_pi []
          parity_cfg p) @ [STR ''total'']),
      return_slot_for_pp = (\<lambda>p.
        scope_return_slot (compiled_procedure_scope parity_gs parity_pi []
          parity_cfg p)),
      globals_to_show = [],
      show_local = (\<lambda>_ _ vars d.
        map (\<lambda>x.
          String.explode x @ ''='' @ string_of_parity (parity_lookup d x)) vars),
      format_return = (\<lambda>_ _ _ _. []),
      show_global = (\<lambda>_ _ _. []),
      show_global_key = (\<lambda>_. ''Global''),
      is_shared_global = (\<lambda>_. False),
      show_internal_globals = False,
      owner_of = (\<lambda>_. ''main''),
      cluster_label = (\<lambda>_ _. ''main / root context''),
      source_text = Some (pretty_string_of_program parity_pi [] parity_prog []),
      node_annotation = (\<lambda>_ _. None)
    \<rparr>"

definition parity_graph_domain :: "(pp \<times> unit + unit) list" where
  "parity_graph_domain =
    contextual_graph_domain parity_cfg (\<lambda>_. [()])
    @ [Inr ()]"

definition parity_dot :: String.literal where
  "parity_dot =
     String.implode
       (case TD_side_always_join_Interp_solve_c parity_eqs (cfg_exit parity_cfg, ()) of
          None \<Rightarrow> ''solver did not terminate''
        | Some sol \<Rightarrow> contextual_analysis_dot parity_graph_config parity_cfg
            parity_graph_domain (snd sol))"

end

