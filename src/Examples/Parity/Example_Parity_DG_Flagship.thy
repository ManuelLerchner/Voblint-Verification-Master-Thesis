section \<open>Flagship: parity analysis of an even-step loop, executed and certified on the D/G spine\<close>

text \<open>
  \<^bold>\<open>Second domain, same registration.\<close>  This theory is the E1 validation of the
  domain-registration API: parity registers through the \<open>unit_dg_exec_analysis\<close> locale
  (as \<open>parity_reg\<close> in \<open>DG_Domain_Registration\<close>) with \<^emph>\<open>no\<close> copied \<open>Hstep\<close>, \<open>Hcomb\<close>,
  \<open>strategy_tree\<close>, \<open>Inl\<close>/\<open>Inr\<close>, or manual post-solution transport lemmas.  An IMP2
  program is compiled to a CFG; the generic D/G framework generates the equation
  system; the \<^emph>\<open>verified\<close> always-join solver \<^emph>\<open>computes\<close> a parity solution inside
  Isabelle (finite lattice, no widening needed); and the single registered endpoint
  \<open>parity_reg.run_source_sound\<close> lifts the result to actual source runs.

  The result is informative: the analysis \<^emph>\<open>discovers\<close> that \<open>x\<close> is even at every
  program point (\<open>x = 0\<close> initially, then \<open>x := x + 2\<close> preserves parity), so the loop
  invariant \<open>x\<close> even holds without any guard refinement --- parity ignores the guard.
\<close>

theory Example_Parity_DG_Flagship
  imports
    "Voblint_Analysis.Exec_DG_Bridge"
    "Voblint_Analysis.Parity_Exec"
    "Voblint_Analysis.Parity_Print"
    "Voblint_Core.Solver_Menu"
    "Voblint_CFG.CFG_Prune"
    "Voblint_Analysis.Analysis_GraphViz"
    "Voblint_VIMP.VIMP_Notation"
    "Voblint_Formalization.DG_Domain_Registration"
begin

hide_const (open) Update_rules.N

subsection \<open>1. The program (proper IMP2 program notation, explicit main)\<close>

text \<open>
  A bounded counting loop that increments by two: initialise \<open>x\<close> to \<open>0\<close>,
  add \<open>2\<close> while \<open>x < 20\<close>.  No procedures beyond \<open>main\<close>, no globals; \<open>x\<close> is a
  single flow-sensitive local.  The parity of \<open>x\<close> stays even at every
  reachable point regardless of the guard, which the analysis must discover,
  not assume.
\<close>

definition parity_program :: imp_prog where
  "parity_program = program {

      global G;

      void main() { 
        x := 0;
        y:=1;
        while (x < 20) { 
          x := x + 2; 
          y:=y + 1 
        }; 
        G:= x + y
      }
}"

definition parity_prog :: "VIMP_Proc.com" where
  "parity_prog = prog_main parity_program"

definition parity_pi :: proc_table where
  "parity_pi = prog_table parity_program"

subsection \<open>2. CFG construction\<close>

text \<open>
  The source compiles to an interprocedural CFG by \<open>compile_prog\<close>, exactly like the
  interval flagship's counting loop --- same topology, only the increment differs.
\<close>

definition parity_cfg :: cfg where
  "parity_cfg = compile_prog parity_pi [] ''main'' parity_prog"

lemma parity_finE: "finite (intra parity_cfg)" and parity_finC: "finite (calls parity_cfg)"
  unfolding parity_cfg_def
  using compile_prog_finite by auto

lemma parity_calls: "calls parity_cfg = {}" by eval

subsection \<open>3. Executable parity D/G specification\<close>

text \<open>
  Parity forms the diagonal D/G analysis \<open>D = G = parity abs_state\<close>, with executable
  mirror \<open>unit_dg_spec_st parity_tf_st\<close>.  The registration \<^locale>\<open>unit_dg_exec_analysis\<close>
  --- interpreted as \<open>parity_reg\<close> in \<open>DG_Domain_Registration\<close> from
  \<open>parity_is_sound_transfer\<close> and \<open>parity_tf_st_commute\<close> alone --- discharges the
  transport, soundness, and solver-crossing obligations generically.  This example
  supplies only the program, the executable solve, and the coverage witnesses.
\<close>

subsection \<open>4. Equation generation\<close>

definition parity_eqs :: "pp \<times> unit \<Rightarrow> (pp \<times> unit, unit, (parity st, parity st) dg_state) strategy_tree" where
  "parity_eqs = dg_gen_of (unit_dg_spec_st parity_tf_st parity_enter_st) parity_cfg
     bot cinit_parity_st (restrict_global_st cinit_parity_st)"

subsection \<open>5. Executable solve (always-join; parity is finite-height)\<close>

lemma parity_terminates_c:
  "TD_side_always_join_Interp_solve_c parity_eqs (cfg_exit parity_cfg, ()) \<noteq> None"
  by eval

definition parity_sol :: "(pp \<times> unit) set \<times> (pp \<times> unit + unit \<Rightarrow> (parity st, parity st) dg_state)" where
  "parity_sol = TD_side_always_join_Interp_solve parity_eqs (cfg_exit parity_cfg, ())"

text \<open>The computed parity of \<open>x\<close> at every node --- \<^emph>\<open>evaluated\<close>.\<close>

value "map_option
   (\<lambda>sol. map (\<lambda>p. (p, lookup_st (locals (snd sol (Inl (p, ())))) ''x''))
            (map Statement [0,1,2,3]))
   (TD_side_always_join_Interp_solve_c parity_eqs (cfg_exit parity_cfg, ()))"

subsection \<open>6. Soundness premises for the registered endpoint\<close>

lemma parity_cover_all:
  "\<forall>v \<in> {Statement 0, Statement 1, Statement 2, Statement 3,
           Statement 4, Statement 5, Statement 6,
           FunctionEntry ''main'', FunctionResult ''main''}.
     (v, ()) \<in> fst parity_sol"
  unfolding parity_sol_def parity_eqs_def by eval

lemma parity_cover_entry: "(cfg_entry parity_cfg, ()) \<in> fst parity_sol"
  using parity_cover_all parity_cfg_def
  by (metis insert_iff inv16_entry_is_main)

lemma parity_cover_edge_ball: "\<forall>(u, a, w) \<in> intra parity_cfg. (w, ()) \<in> fst parity_sol"
  unfolding parity_sol_def parity_eqs_def by eval
lemma parity_cover_edge: "\<And>u a w. (u, a, w) \<in> intra parity_cfg \<Longrightarrow> (w, ()) \<in> fst parity_sol"
  using parity_cover_edge_ball by auto

lemma parity_cover_enter:
  "\<And>c dst fs as p k. (c, CallEdge dst fs as, FunctionEntry p, k) \<in> calls parity_cfg
     \<Longrightarrow> (FunctionEntry p, ()) \<in> fst parity_sol"
  by (simp add: parity_calls)
lemma parity_cover_combine:
  "\<And>c dst fs as p k. (c, CallEdge dst fs as, FunctionEntry p, k) \<in> calls parity_cfg
     \<Longrightarrow> (k, ()) \<in> fst parity_sol"
  by (simp add: parity_calls)

lemma parity_sound0:
  "cinit_stores is_global \<subseteq> \<lbrakk>fun_of_st cinit_parity_st \<squnion> fun_of_st (restrict_global_st cinit_parity_st)\<rbrakk>"
proof -
  have "fun_of_st cinit_parity_st \<squnion> fun_of_st (restrict_global_st cinit_parity_st) = fun_of_st cinit_parity_st"
    by (simp add: fun_of_st_cinit_parity_st fun_of_st_restrict_global_st restrict_global_def
                  sup_fun_def fun_eq_iff)
  thus ?thesis
    by (auto simp: cinit_stores_def gamma_state_def fun_of_st_cinit_parity_st)
qed

subsection \<open>7. Inspecting the certified result\<close>

lemma parity_head_computed:
  "lookup_st (locals (snd parity_sol (Inl (Statement (Suc 0), ())))) ''x'' = PEven"
  unfolding parity_sol_def parity_eqs_def by eval

lemma parity_exit_computed:
  "lookup_st (locals (snd parity_sol (Inl (Statement 3, ())))) ''x'' = PEven"
  unfolding parity_sol_def parity_eqs_def by eval

subsection \<open>8. Source-level soundness through the registered analysis\<close>

text \<open>
  The registered endpoint \<open>parity_reg.run_source_sound\<close> turns the single \<open>by eval\<close>
  solver success \<open>parity_terminates_c\<close> directly into a source-level guarantee: every
  reachable IMP2 store is bounded by the computed parity at its matched program point,
  read through the semantic accessor \<open>parity_reg.gamma\<close>.  No transport lemma,
  \<^const>\<open>part_post_solution\<close>, \<open>solve_dom\<close>, or \<^const>\<open>fun_of_dg_st\<close> appears in this proof.
\<close>

lemma parity_wf: "wf_compile_input is_global parity_pi [] ''main'' parity_prog"
  unfolding wf_compile_input_def wf_source_program_def wf_proc_decl_def
    parity_pi_def parity_prog_def parity_program_def
  by (auto simp: source_aexp_def source_bexp_def proc_decl_of_def ret_var_def reserved_ret_var_def is_global_def
      prog_main_name_def split: if_splits)

theorem parity_source_run_sound:
  assumes run: "star (pstep is_global parity_pi) (parity_prog, s, []) (residual, t, frs)"
      and init: "s \<in> cinit_stores is_global"
  shows "\<exists>v stk. csim parity_pi parity_cfg (residual, t, frs) (v, t, stk)
                 \<and> t \<in> parity_reg.gamma (snd parity_sol) v"
proof -
  show ?thesis
    unfolding parity_sol_def parity_eqs_def parity_cfg_def
    by (rule parity_reg.run_source_sound
          [OF parity_terminates_c[unfolded parity_eqs_def parity_cfg_def]
              parity_wf
              parity_cover_entry[unfolded parity_sol_def parity_eqs_def parity_cfg_def]
              parity_cover_edge[unfolded parity_sol_def parity_eqs_def parity_cfg_def]
              parity_cover_enter[unfolded parity_sol_def parity_eqs_def parity_cfg_def]
              parity_cover_combine[unfolded parity_sol_def parity_eqs_def parity_cfg_def]
              parity_finE[unfolded parity_cfg_def]
              parity_finC[unfolded parity_cfg_def]
              parity_sound0[folded gamma_unit_def]
              init run[unfolded parity_cfg_def]])
qed

subsection \<open>9. The result is not vacuous\<close>

text \<open>
  The computed loop-head value for \<open>x\<close> is \<open>PEven\<close>, strictly below \<open>PTop\<close>: the
  analysis genuinely discovered that \<open>x\<close> is even, and its concretization excludes
  every odd integer.  The guarantee therefore says something.
\<close>

lemma parity_head_proper:
  "lookup_st (locals (snd parity_sol (Inl (Statement (Suc 0), ())))) ''x'' \<noteq> PTop"
  by (simp add: parity_head_computed)

lemma parity_head_excludes_odd:
  "n \<in> gamma_parity (lookup_st (locals (snd parity_sol (Inl (Statement (Suc 0), ())))) ''x'')
     \<Longrightarrow> even n"
  by (simp add: parity_head_computed)

subsection \<open>10. Annotated GraphViz of the computed result\<close>

text \<open>
  A DOT rendering of \<open>parity_cfg\<close> with each node annotated by the computed
  parity for \<open>x\<close>.  The \<open>ML_val\<close> below prints the DOT as a plain string; paste
  it into any GraphViz renderer (\<open>dot -Tpng\<close>) to view the analysed loop, each
  node labelled with the loop-invariant parity the verified solver computed.
\<close>

definition parity_graph_config ::
  "(unit, unit, (parity st, parity st) dg_state, parity st) analysis_graph_config" where
  "parity_graph_config =
    \<lparr> local_of = locals,
      route = (\<lambda>_ _ _ _. ()),
      show_context = (\<lambda>_. ''unit''),
      locals_for_pp = (\<lambda>p.
        scope_locals (compiled_procedure_scope parity_pi [] ''main'' parity_prog
          parity_cfg p)),
      return_slot_for_pp = (\<lambda>p.
        scope_return_slot (compiled_procedure_scope parity_pi [] ''main'' parity_prog
          parity_cfg p)),
      globals_to_show = [''G''],
      show_local = (\<lambda>_ _ vars d.
        map (\<lambda>x.
          x @ ''='' @ string_of_parity (lookup_st d x)) vars),
      format_return = (\<lambda>_ _ _ _. []),
      show_global = (\<lambda>_ _ d.
        map (\<lambda>g.
          g @ ''='' @ string_of_parity (lookup_st (globs d) g)) [''G'']),
      show_global_key = (\<lambda>_. ''Global''),
      is_shared_global = (\<lambda>_. True),
      show_internal_globals = True,
      owner_of = (\<lambda>_. ''main''),
      cluster_label = (\<lambda>_ _. ''main / root context''),
      source_text = Some (pretty_string_of_program parity_pi [] parity_prog)
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

ML_val \<open>writeln (@{code parity_dot})\<close>

end

