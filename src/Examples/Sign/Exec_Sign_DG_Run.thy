section \<open>Running the verified solver on the native D/G spine (Sign)\<close>

text \<open>
  An end-to-end certified run on the carrier-opaque D/G equation system, registered
  through the \<open>unit_dg_exec_analysis\<close> locale (interpreted as \<open>sign_reg\<close> in
  \<open>DG_Domain_Registration\<close> from just \<open>sign_is_sound_transfer\<close> and \<open>sign_tf_st_commute\<close>).
  A concrete call-free Sign program is compiled to a CFG; the executable D/G
  generator (\<open>dg_gen_of (unit_dg_spec_st sign_tf_st)\<close>, values in
  \<open>(sign exec_dg_st, sign exec_dg_st) dg_state\<close>) is handed to the vendored always-join TD-side
  solver; the solver \<^emph>\<open>computes\<close> a partial post-solution.

  The final theorem \<open>dgEx_source_run_sound\<close> turns the single \<open>by eval\<close> solver success
  directly into a source-level guarantee, matching the pattern in
  \<open>Example_Interval_DG_Flagship\<close>: no transport lemma, \<open>part_post_solution\<close>, \<open>solve_dom\<close>,
  or \<open>fun_of_dg_st\<close> appears in this file's own proofs.  It depends on the \<^emph>\<open>computed\<close>
  solver result \<open>snd dgEx_sol\<close>, not on any hand-written candidate solution.
\<close>

theory Exec_Sign_DG_Run
  imports
    "Voblint_Analysis.Exec_DG_Bridge"
    "Voblint_Analysis.Sign_Exec_Sound"
    "Voblint_Analysis.Sign_DG"
    "Voblint_VIMP.VIMP_Notation"
    "Voblint_Formalization.DG_Domain_Registration"
begin

(* Disambiguate our N constructor from the phase datatype constructor. *)
hide_const phase.N
subsection \<open>The concrete program and its compiled CFG\<close>

text \<open>
  A minimal call-free program \<^verbatim>\<open>x := 1; y := x\<close> inside \<open>main\<close>: the body occupies
  \<open>Statement 0\<close>--\<open>Statement 2\<close> between \<open>FunctionEntry ''main''\<close> and
  \<open>FunctionResult ''main''\<close>, and \<open>calls\<close> is empty.  \<open>gEx_eq\<close> proves the compilation
  equals the explicit graph, matching the source-soundness pattern in
  \<open>Example_Interval_DG_Flagship\<close>.
\<close>

definition sign_ex_prog :: imp_prog where
  "sign_ex_prog = program { void main() { x := 1; y := x } }"

definition sign_ex_pi :: proc_table where
  "sign_ex_pi = prog_table sign_ex_prog"

definition gEx :: cfg where
  "gEx = compile_prog sign_ex_pi (prog_procs sign_ex_prog) prog_main_name (prog_main sign_ex_prog)"

lemma gEx_calls: "calls gEx = {}" by eval
lemma gEx_entry: "cfg_entry gEx = FunctionEntry ''main''" by eval
lemma gEx_finE: "finite (intra gEx)" unfolding gEx_def using compile_prog_finite by simp
lemma gEx_finC: "finite (calls gEx)" unfolding gEx_def using compile_prog_finite by simp

definition dgEx_eqs :: "pp \<times> unit \<Rightarrow> (pp \<times> unit, unit, (sign exec_dg_st, sign exec_dg_st) dg_state) strategy_tree" where
  "dgEx_eqs = dg_gen_of (unit_dg_spec_st sign_tf_st sign_enter_st) gEx bot cinit_sign_st cinit_sign_st"

definition dgEx_sol :: "(pp \<times> unit) set \<times> (pp \<times> unit + unit \<Rightarrow> (sign exec_dg_st, sign exec_dg_st) dg_state)" where
  "dgEx_sol = TD_side_always_join_Interp_solve dgEx_eqs (cfg_exit gEx, ())"

subsection \<open>The solver computes a partial post-solution\<close>

text \<open>
  The executable option-valued solver terminates on the D/G equation system --- a
  code-generated \<open>by eval\<close> fact --- so the solver-domain predicate holds and the
  vendored partial-post-solution theorem applies to the computed result.
\<close>

lemma dgEx_terminates_c: "TD_side_always_join_Interp_solve_c dgEx_eqs (cfg_exit gEx, ()) \<noteq> None"
  by eval

lemma dgEx_solve_dom:
  "TD_side_always_join_Interp.solve_dom TYPE(unit) TYPE((sign exec_dg_st, sign exec_dg_st) dg_state) dgEx_eqs (cfg_exit gEx, ())"
  using dgEx_terminates_c
  unfolding TD_side_always_join_Interp.term_equivalence TD_side_always_join_Interp.solve_c_dom_def
  by simp

lemma dgEx_pp_st:
  "part_post_solution dgEx_eqs (cfg_exit gEx, ()) (snd dgEx_sol) (fst dgEx_sol)"
  using TD_side_always_join_Interp.partial_post_solution[OF dgEx_solve_dom, of "fst dgEx_sol" "snd dgEx_sol"]
  unfolding dgEx_sol_def by simp

subsection \<open>Well-formedness of the compiled input\<close>

lemma dgEx_wf:
  "wf_compile_input is_global sign_ex_pi (prog_procs sign_ex_prog) prog_main_name (prog_main sign_ex_prog)"
  unfolding wf_compile_input_def wf_source_program_def wf_proc_decl_def
    sign_ex_pi_def sign_ex_prog_def
  by (auto simp: source_aexp_def source_bexp_def proc_decl_of_def ret_var_def
      reserved_ret_var_def is_global_def split: if_splits)

subsection \<open>Collecting-semantics over-approximation from the computed result\<close>

lemma dgEx_cover_entry: "(cfg_entry gEx, ()) \<in> fst dgEx_sol"
  unfolding dgEx_sol_def gEx_entry by eval

lemma dgEx_cover_edge_ball: "\<forall>(u, a, w) \<in> intra gEx. (w, ()) \<in> fst dgEx_sol"
  unfolding dgEx_sol_def by eval
lemma dgEx_cover_edge: "\<And>u a w. (u, a, w) \<in> intra gEx \<Longrightarrow> (w, ()) \<in> fst dgEx_sol"
  using dgEx_cover_edge_ball by auto
lemma dgEx_cover_enter:
  "\<And>c dst fs as p k. (c, CallEdge dst fs as, FunctionEntry p, k) \<in> calls gEx
     \<Longrightarrow> (FunctionEntry p, ()) \<in> fst dgEx_sol"
  by (simp add: gEx_calls)
lemma dgEx_cover_combine:
  "\<And>c dst fs as p k. (c, CallEdge dst fs as, FunctionEntry p, k) \<in> calls gEx
     \<Longrightarrow> (k, ()) \<in> fst dgEx_sol"
  by (simp add: gEx_calls)
lemma dgEx_sound0: "cinit_stores is_global \<subseteq> \<lbrakk>fun_of_exec_dg_st cinit_sign_st \<squnion> fun_of_exec_dg_st cinit_sign_st\<rbrakk>"
  by (simp add: fun_of_st_cinit_sign_st cinit_stores_def gamma_state_def sup.idem)

subsection \<open>Source-level soundness through the registered analysis\<close>

text \<open>
  The registered endpoint \<open>sign_reg.run_source_sound\<close> turns the single \<^theory_text>\<open>by eval\<close>
  solver success \<open>dgEx_terminates_c\<close> directly into a source-level guarantee: every
  reachable VIMP store is bounded by the computed Sign answer at its matched program
  point, read through the semantic accessor \<open>sign_reg.gamma\<close>.  No transport lemma,
  \<^const>\<open>part_post_solution\<close>, \<open>solve_dom\<close>, or \<^const>\<open>fun_of_dg_st\<close> appears in this proof,
  matching the pattern in \<open>Example_Interval_DG_Flagship\<close>.
\<close>

theorem dgEx_source_run_sound:
  assumes run: "star (pstep is_global sign_ex_pi) (prog_main sign_ex_prog, s, []) (residual, t, frs)"
      and init: "s \<in> cinit_stores is_global"
  shows "\<exists>v stk. csim sign_ex_pi gEx (residual, t, frs) (v, t, stk)
                 \<and> t \<in> sign_reg.gamma (snd dgEx_sol) v"
proof -
  show ?thesis
    unfolding dgEx_sol_def dgEx_eqs_def gEx_def
    by (rule sign_reg.run_source_sound
          [OF dgEx_terminates_c[unfolded dgEx_eqs_def gEx_def]
              dgEx_wf
              dgEx_cover_entry[unfolded dgEx_sol_def dgEx_eqs_def gEx_def]
              dgEx_cover_edge[unfolded dgEx_sol_def dgEx_eqs_def gEx_def]
              dgEx_cover_enter[unfolded dgEx_sol_def dgEx_eqs_def gEx_def]
              dgEx_cover_combine[unfolded dgEx_sol_def dgEx_eqs_def gEx_def]
              gEx_finE[unfolded gEx_def]
              gEx_finC[unfolded gEx_def]
              dgEx_sound0[folded gamma_unit_def]
              init run[unfolded gEx_def]])
qed

subsection \<open>Inspecting the computed result\<close>

text \<open>The diagonal Sign instance joins local answers and global side effects at
  each edge. The executable result is therefore sound but imprecise at the exit.\<close>

lemma dgEx_inspect:
  "map_option (\<lambda>sol. (lookup_exec_dg_st (locals (snd sol (Inl (Statement 2, ())))) ''x'',
                       lookup_exec_dg_st (globs (snd sol (Inr ()))) ''x''))
     (TD_side_always_join_Interp_solve_c dgEx_eqs (cfg_exit gEx, ())) = Some (STop, STop)"
  by eval

end




