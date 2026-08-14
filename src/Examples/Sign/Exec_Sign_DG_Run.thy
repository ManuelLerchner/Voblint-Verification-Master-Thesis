section \<open>Running the verified solver on the native D/G spine (Sign)\<close>

text \<open>
  An end-to-end certified run on the carrier-opaque D/G equation system, registered
  through the \<open>unit_dg_exec_analysis\<close> locale (interpreted as \<open>sign_ex_reg\<close> below, at
  this file's own storage classifier \<open>sign_ex_gs\<close>, from just \<open>sign_is_sound_transfer_for\<close>
  and \<open>sign_tf_st_for_commute\<close>).
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
    "Voblint_Formalization.Run_Analysis_Sound"
begin

(* Disambiguate our N constructor from the phase datatype constructor. *)
hide_const phase.N
subsection \<open>The concrete program and its compiled CFG\<close>

text \<open>
  A minimal call-free program \<^verbatim>\<open>x := 1; y := x\<close> inside \<open>main\<close>: the body occupies
  \<open>Statement 0\<close>--\<open>Statement 2\<close> between \<open>FunctionEntry (STR ''main'')\<close> and
  \<open>FunctionResult (STR ''main'')\<close>, and \<open>calls\<close> is empty.  \<open>gEx_eq\<close> proves the compilation
  equals the explicit graph, matching the source-soundness pattern in
  \<open>Example_Interval_DG_Flagship\<close>.
\<close>

definition sign_ex_prog :: imp_prog where
  "sign_ex_prog = program { void main() { x := 1; y := x } }"

text \<open>The storage classifier: \<open>sign_ex_prog\<close> declares no globals, so \<open>sign_ex_gs\<close>
  classifies every variable this chain touches as local. This validates
  domain-independence of the generic transport, matching \<open>parity_gs\<close>'s role for the
  parity flagship, rather than global/local separation.\<close>
abbreviation sign_ex_gs :: "vname \<Rightarrow> bool" where
  "sign_ex_gs \<equiv> declared_global sign_ex_prog"

text \<open>Local shorthand for the executable state's lookup projection, fixed at this
  file's own \<open>sign_ex_gs\<close> classifier.\<close>
abbreviation sign_ex_lookup :: "('a::bot) exec_dg_st \<Rightarrow> vname \<Rightarrow> 'a" where
  "sign_ex_lookup s x \<equiv> lookup_resolved_st_q s (location_of sign_ex_gs x)"

definition sign_ex_pi :: proc_table where
  "sign_ex_pi = prog_table sign_ex_prog"

definition gEx :: cfg where
  "gEx = compile_prog sign_ex_pi (prog_procs sign_ex_prog) prog_main_name (prog_main sign_ex_prog)"

lemma gEx_calls: "calls gEx = {}" by eval
lemma gEx_entry: "cfg_entry gEx = FunctionEntry (STR ''main'')" by eval
lemma gEx_finE: "finite (intra gEx)" unfolding gEx_def using compile_prog_finite by simp
lemma gEx_finC: "finite (calls gEx)" unfolding gEx_def using compile_prog_finite by simp

definition dgEx_eqs :: "pp \<times> unit \<Rightarrow> (pp \<times> unit, unit, (sign exec_dg_st, sign exec_dg_st) dg_state) strategy_tree" where
  "dgEx_eqs = dg_gen_of (unit_dg_spec_st_for sign_ex_gs (sign_tf_st_for sign_ex_gs) (sign_enter_st_for sign_ex_gs)) gEx bot cinit_sign_st cinit_sign_st"

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
  "wf_compile_input sign_ex_gs sign_ex_pi (prog_procs sign_ex_prog) prog_main_name (prog_main sign_ex_prog)"
  unfolding wf_compile_input_simps
    sign_ex_pi_def sign_ex_prog_def
  by (auto simp: source_aexp_def source_bexp_def proc_decl_of_def ret_var_def
      reserved_ret_var_def prog_main_name_def special_table_def special_pname_nondet_int_def
      split: if_splits)

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
lemma dgEx_reserved: "reserved_ret_var sign_ex_gs"
  unfolding wf_compile_input_simps sign_ex_pi_def sign_ex_prog_def
  by (auto simp: source_aexp_def source_bexp_def proc_decl_of_def ret_var_def
      reserved_ret_var_def split: if_splits)

lemma dgEx_sound0:
  "cinit_stores sign_ex_gs \<subseteq> \<lbrakk>combine_env_abs sign_ex_gs
     (fun_of_exec_dg_st_for sign_ex_gs cinit_sign_st) (fun_of_exec_dg_st_for sign_ex_gs cinit_sign_st)\<rbrakk>"
  by (simp add: fun_of_exec_dg_st_for_def fun_of_st_cinit_sign_st_for cinit_stores_def gamma_state_def
      combine_env_abs_def)

subsection \<open>Registration through the classifier-parametric registration locale\<close>

text \<open>Interpret \<^locale>\<open>unit_dg_exec_analysis\<close> once here at \<^const>\<open>sign_ex_gs\<close>
  with the classifier-parametric transfer/enter functions, matching the pattern in
  \<open>Example_Parity_DG_Flagship\<close>.  The interpretation absorbs the sound-transfer and
  primitive-commutation obligations once, so \<open>dgEx_source_run_sound\<close> below only
  supplies the compiled-input and solver facts.\<close>

interpretation sign_ex_reg:
  unit_dg_exec_analysis sign_ex_gs
    "sign_tf_for sign_ex_gs" "sign_tf_st_for sign_ex_gs" "sign_enter_st_for sign_ex_gs"
    "TD_side_always_join_Interp.solve" "TD_side_always_join_Interp.solve_c"
proof -
  interpret sign_ex_transfer: sound_transfer_for sign_ex_gs "sign_tf_for sign_ex_gs"
    by (rule sign_is_sound_transfer_for)
  show "unit_dg_exec_analysis sign_ex_gs (sign_tf_for sign_ex_gs) (sign_tf_st_for sign_ex_gs)
          (sign_enter_st_for sign_ex_gs)
          TD_side_always_join_Interp.solve TD_side_always_join_Interp.solve_c"
    by unfold_locales
       (rule dgEx_reserved
             sign_ex_transfer.tf_sound_assign_for sign_ex_transfer.tf_sound_special_for
             sign_ex_transfer.tf_sound_branch_for
             sign_ex_transfer.tf_sound_enter_for sign_ex_transfer.tf_sound_combine_env_for
             sign_tf_st_for_commute[folded fun_of_exec_dg_st_for_def]
             sign_enter_st_for_commute[folded fun_of_exec_dg_st_for_def]
             action_reduces.ret_none[OF sign_tf_st_for_reduces]
             action_reduces.ret_some[OF sign_tf_st_for_reduces]
             action_reduces.check[OF sign_tf_st_for_reduces]
             TD_side_always_join_Interp.part_post_solution_of_solve_c)+
qed

theorem dgEx_source_run_sound:
  assumes run: "star (pstep sign_ex_gs sign_ex_pi) (prog_main sign_ex_prog, s, []) (residual, t, frs)"
      and init: "s \<in> cinit_stores sign_ex_gs"
  shows "\<exists>v stk. csim sign_ex_pi gEx (residual, t, frs) (v, t, stk)
                 \<and> t \<in> sign_ex_reg.gamma (snd dgEx_sol) v"
proof -
  show ?thesis
    unfolding dgEx_sol_def dgEx_eqs_def gEx_def
    by (rule sign_ex_reg.run_source_sound
          [OF dgEx_terminates_c[unfolded dgEx_eqs_def gEx_def]
              dgEx_wf
              vars_coverI[OF dgEx_cover_entry[unfolded dgEx_sol_def dgEx_eqs_def gEx_def]
                             dgEx_cover_edge[unfolded dgEx_sol_def dgEx_eqs_def gEx_def]
                             dgEx_cover_enter[unfolded dgEx_sol_def dgEx_eqs_def gEx_def]
                             dgEx_cover_combine[unfolded dgEx_sol_def dgEx_eqs_def gEx_def]]
              gEx_finE[unfolded gEx_def]
              gEx_finC[unfolded gEx_def]
              dgEx_sound0[folded gamma_unit_def]
              init run[unfolded gEx_def]])
qed

subsection \<open>Inspecting the computed result\<close>

text \<open>The diagonal Sign instance routes each name to the exec state that owns it
  at every edge: the local answer stays exactly \<open>SPos\<close> at the exit, while the
  global/side unknown's own value for \<open>x\<close> (a name no \<open>global\<close> declaration ever
  makes it track) keeps its unrelated \<open>STop\<close> default -- expected, since nothing
  ever queries that slot for a purely local name.\<close>

lemma dgEx_inspect:
  "map_option (\<lambda>sol. (sign_ex_lookup (locals (snd sol (Inl (Statement 2, ())))) (STR ''x''),
                       sign_ex_lookup (globs (snd sol (Inr ()))) (STR ''x'')))
     (TD_side_always_join_Interp_solve_c dgEx_eqs (cfg_exit gEx, ())) = Some (SPos, STop)"
  by eval

end

