section \<open>Running the verified solver on the native D/G spine (Sign)\<close>

text \<open>
  An end-to-end certified run on the Base-style D/G equation system, registered
  through the \<open>base_dg_exec_analysis\<close> locale (interpreted as \<open>sign_ex_reg\<close> below, at
  this file's own storage classifier \<open>sign_ex_gs\<close>, from \<open>sign_is_sound_transfer_for\<close>,
  \<open>sign_tf_st_for_commute\<close>, and \<open>sign_enter_st_for_commute\<close>).
  A concrete call-free Sign program is compiled to a CFG; the executable D/G
  generator (\<open>dg_gen_of (base_dg_spec_st_for_lifted sign_ex_gs \<dots> sign_tf_st_for sign_enter_st_for)\<close>,
  values in \<open>(sign exec_dg_st lifted, sign exec_dg_st lifted) dg_state\<close> --- the whole
  abstract state routed through the local unknown, no separate global/side slot) is
  handed to the vendored always-join TD-side solver; the solver \<^emph>\<open>computes\<close> a
  partial post-solution.

  The final theorem \<open>dgEx_source_run_sound\<close> turns the single \<open>by eval\<close> solver success
  directly into a source-level guarantee, matching the pattern in
  \<open>Example_Interval_DG_Flagship\<close>: no transport lemma, \<open>part_post_solution\<close>, \<open>solve_dom\<close>,
  or \<open>fun_of_dg_st_for\<close> appears in this file's own proofs.  It depends on the \<^emph>\<open>computed\<close>
  solver result \<open>snd dgEx_sol\<close>, not on any hand-written candidate solution.
\<close>

theory Exec_Sign_DG_Run
  imports
    "Voblint_Core.Exec_DG_Bridge"
    "Voblint_Core.DG_Base_Exec"
    "Voblint_Core.DG_Coverage"
    "Voblint_Analysis.Sign_Exec"
    "Voblint_Core.Solver_Side_RG"
    "TD.TD_side_upd_rule"
    "Voblint_CFG.CFG_Prune"
    "Voblint_CFG.Compile_Invariants"
    "Voblint_VIMP.VIMP_Notation"
    "Voblint_Soundness.Run_Analysis_Sound"
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
  "gEx = compile_prog (prog_tyenv sign_ex_prog) sign_ex_pi (prog_procs sign_ex_prog)
     prog_main_name (prog_main sign_ex_prog)"

lemma gEx_calls: "calls gEx = {}"
  unfolding gEx_def sign_ex_pi_def
  by (rule compile_prog_calls_empty) (simp_all add: sign_ex_prog_def)
lemma gEx_entry: "cfg_entry gEx = FunctionEntry (STR ''main'')"
  unfolding gEx_def prog_main_name_def by (rule inv16_entry_is_main)
lemma gEx_wf_cfg: "wf_cfg gEx" unfolding gEx_def by (rule compile_prog_wf)
lemma gEx_finE: "finite (intra gEx)" unfolding gEx_def using compile_prog_finite by simp
lemma gEx_finC: "finite (calls gEx)" unfolding gEx_def using compile_prog_finite by simp

definition dgEx_eqs :: "pp \<times> unit \<Rightarrow> (pp \<times> unit, unit, (sign exec_dg_st lifted, sign exec_dg_st lifted) dg_state) strategy_tree" where
  "dgEx_eqs = dg_gen_of
     (base_dg_spec_st_for_lifted sign_ex_gs (resolved_st_q_is_bot_for (declared_global_vars sign_ex_prog))
       (sign_tf_st_for sign_ex_gs) (sign_enter_st_for sign_ex_gs))
     gEx bot (Lifted cinit_sign_st) (Lifted cinit_sign_st)"

definition dgEx_sol :: "(pp \<times> unit) set \<times> (pp \<times> unit + unit \<Rightarrow> (sign exec_dg_st lifted, sign exec_dg_st lifted) dg_state)" where
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
  "TD_side_always_join_Interp.solve_dom TYPE(unit) TYPE((sign exec_dg_st lifted, sign exec_dg_st lifted) dg_state) dgEx_eqs (cfg_exit gEx, ())"
  by (rule TD_side_always_join_Interp.solve_dom_of_solve_c[OF dgEx_terminates_c])

lemma dgEx_pp_st:
  "part_post_solution dgEx_eqs (cfg_exit gEx, ()) (snd dgEx_sol) (fst dgEx_sol)"
  using TD_side_always_join_Interp.partial_post_solution[OF dgEx_solve_dom, of "fst dgEx_sol" "snd dgEx_sol"]
  unfolding dgEx_sol_def by simp

subsection \<open>Well-formedness of the compiled input\<close>

lemma dgEx_wf:
  "wf_compile_input sign_ex_gs sign_ex_pi (prog_procs sign_ex_prog) prog_main_name (prog_main sign_ex_prog)"
  unfolding wf_compile_input_simps
    sign_ex_pi_def sign_ex_prog_def
  by (auto simp: source_exp_def source_exp_def proc_decl_of_def ret_var_def
      reserved_ret_var_def prog_main_name_def special_table_def special_pname_nondet_int_def
      special_pname_min_def special_pname_max_def
      split: if_splits)

subsection \<open>Collecting-semantics over-approximation from the computed result\<close>

text \<open>Coverage is not read off the solved key set. Every node of \<open>gEx\<close> reaches
  \<^const>\<open>cfg_exit\<close> --- a structural fact about the graph alone, decided by
  \<^const>\<open>cfg_exit_covers\<close> --- and \<^const>\<open>vars_cover\<close> follows from that together
  with the post-solution the solver already returns.\<close>

lemma dgEx_exit_covers: "cfg_exit_covers gEx" by eval

lemma dgEx_vars_cover: "vars_cover gEx (fst dgEx_sol)"
  by (rule vars_cover_of_dg_gen_of_covers
        [OF gEx_finE gEx_finC gEx_wf_cfg dgEx_exit_covers
            dgEx_pp_st[unfolded dgEx_eqs_def]])
lemma dgEx_reserved: "reserved_ret_var sign_ex_gs"
  unfolding wf_compile_input_simps sign_ex_pi_def sign_ex_prog_def
  by (auto simp: source_exp_def source_exp_def proc_decl_of_def ret_var_def
      reserved_ret_var_def split: if_splits)

lemma dgEx_is_bot_exact:
  "\<And>s. resolved_st_q_is_bot_for (declared_global_vars sign_ex_prog) s = is_bot_state (fun_of_exec_dg_st_for sign_ex_gs s)"
  by (rule resolved_st_q_is_bot_for_iff[OF declared_global_iff, folded fun_of_exec_dg_st_for_def])

lemma dgEx_sound0:
  "cinit_stores sign_ex_gs \<subseteq> gamma_dg_base (map_lift (fun_of_exec_dg_st_for sign_ex_gs) (Lifted cinit_sign_st))
                                (map_lift (fun_of_exec_dg_st_for sign_ex_gs) (Lifted cinit_sign_st))"
  by (simp add: fun_of_exec_dg_st_for_def fun_of_st_cinit_sign_st_for cinit_stores_def gamma_state_def
      gamma_dg_base_def)

subsection \<open>Registration through the classifier-parametric registration locale\<close>

text \<open>Interpret \<^locale>\<open>base_dg_exec_analysis\<close> once here at \<^const>\<open>sign_ex_gs\<close>
  with the classifier-parametric transfer/enter functions and \<^const>\<open>resolved_st_q_is_bot_for\<close>
  at this program's own declared globals -- the same five domain facts
  \<^locale>\<open>unit_dg_exec_analysis\<close> needed, plus the one new \<open>is_bot_pred\<close> exactness obligation. \<open>G\<close>
  is instantiated at \<open>sign exec_dg_st lifted\<close> too (the plumbing constraint
  \<^theory>\<open>Voblint_Soundness.Run_Analysis_Sound\<close>'s \<open>base_dg_exec_analysis\<close> documents), not because
  \<open>G\<close>'s content matters here.\<close>

interpretation sign_ex_reg:
  base_dg_exec_analysis sign_ex_gs
    "sign_tf_for sign_ex_gs" "sign_tf_st_for sign_ex_gs" "sign_enter_st_for sign_ex_gs"
    "resolved_st_q_is_bot_for (declared_global_vars sign_ex_prog)"
    "TD_side_always_join_Interp.solve" "TD_side_always_join_Interp.solve_c"
proof -
  interpret sign_ex_transfer: sound_transfer_for sign_ex_gs "sign_tf_for sign_ex_gs"
    by (rule sign_is_sound_transfer_for)
  show "base_dg_exec_analysis sign_ex_gs (sign_tf_for sign_ex_gs) (sign_tf_st_for sign_ex_gs)
          (sign_enter_st_for sign_ex_gs) (resolved_st_q_is_bot_for (declared_global_vars sign_ex_prog))
          TD_side_always_join_Interp.solve TD_side_always_join_Interp.solve_c"
    by unfold_locales
       (rule dgEx_reserved
             sign_ex_transfer.tf_sound_assign_for sign_ex_transfer.tf_sound_special_for
             sign_ex_transfer.tf_sound_branch_for
             sign_ex_transfer.tf_sound_enter_for sign_ex_transfer.tf_sound_combine_env_for
             sign_tf_st_for_commute[folded fun_of_exec_dg_st_for_def]
             sign_enter_st_for_commute[folded fun_of_exec_dg_st_for_def]
             dgEx_is_bot_exact
             TD_side_always_join_Interp.part_post_solution_of_solve_c)+
qed

theorem dgEx_source_run_sound:
  assumes run: "star (pstep (prog_tyenv sign_ex_prog) sign_ex_gs sign_ex_pi)
                  (prog_main sign_ex_prog, s, [], proc_ret_kind sign_ex_pi prog_main_name)
                  (residual, t, frs, rk)"
      and init: "s \<in> cinit_stores sign_ex_gs"
  shows "\<exists>v stk. csim (prog_tyenv sign_ex_prog) sign_ex_pi gEx (residual, t, frs, rk) (v, t, stk)
                 \<and> t \<in> sign_ex_reg.gamma (snd dgEx_sol) v"
proof -
  show ?thesis
    unfolding dgEx_sol_def dgEx_eqs_def gEx_def
    by (rule sign_ex_reg.run_source_sound
          [OF dgEx_terminates_c[unfolded dgEx_eqs_def gEx_def]
              dgEx_wf
              dgEx_vars_cover[unfolded dgEx_sol_def dgEx_eqs_def gEx_def]
              gEx_finE[unfolded gEx_def]
              gEx_finC[unfolded gEx_def]
              dgEx_sound0
              init run[unfolded gEx_def]])
qed

subsection \<open>Inspecting the computed result\<close>

text \<open>The Base instance routes the whole abstract state through the local unknown,
  reachability-lifted: the local answer at the exit is exactly \<open>Lifted\<close> of a state
  mapping \<open>x\<close> to \<open>SPos\<close>, with no separate global/side slot to inspect for a purely
  local name.\<close>

lemma dgEx_inspect:
  "map_option (\<lambda>sol. case map_lift (fun_of_exec_dg_st_for sign_ex_gs) (locals (snd sol (Inl (Statement 2, ()))))
                      of Lifted s \<Rightarrow> Some (s (STR ''x'')) | Bot \<Rightarrow> None)
     (TD_side_always_join_Interp_solve_c dgEx_eqs (cfg_exit gEx, ())) = Some (Some SPos)"
  by eval

end

