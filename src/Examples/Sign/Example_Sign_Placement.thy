theory Example_Sign_Placement
  imports
    "Voblint_Examples.Placement_Policy_Exec"
    "Voblint_Exec.DG_Coverage"
    "Voblint_Analysis.Sign_Exec"
    "Voblint_VIMP.VIMP_Notation"
begin

section \<open>A Sign analysis under the keep-everything-local placement\<close>

text \<open>
  The smallest placement instance: every name -- the global \<open>g\<close> included --
  is kept in the local component, and nothing is published to the side
  channel. The covering pair is \<open>keep_local = \<top>\<close>, \<open>publish_side = \<bottom>\<close>; its
  classifier-split representation keeps all locals and lists the one
  declared global. The example runs the verified warrowing solver on the
  placed executable specification and certifies the computed table through
  \<^locale>\<open>placed_dg_exec_analysis\<close>: \<open>g\<close> is \<open>SPos\<close> at the exit, carried
  entirely by the local unknown, and the shared side unknown stays bottom.
\<close>

definition sign_placement_prog :: imp_prog where
  "sign_placement_prog = program {
     global g;
     void main() {
       x := 5;
       g := x
     }
   }"

abbreviation sign_placement_gs :: "vname \<Rightarrow> bool" where
  "sign_placement_gs \<equiv> declared_global sign_placement_prog"

definition sign_placement_cfg :: cfg where
  "sign_placement_cfg =
    compile_prog (prog_table sign_placement_prog) (prog_procs sign_placement_prog)"

text \<open>The single declared global, as the fact the classifier-split shape
  obligations reduce to.\<close>
lemma sign_placement_globals:
  "sign_placement_gs x \<longleftrightarrow> x = STR ''g''"
  by (auto simp: sign_placement_prog_def)

subsection \<open>The placed equation system and its computed solution\<close>

definition sign_placement_dg_eqs ::
  "pp \<times> unit =>
    (pp \<times> unit, unit, (sign exec_dg_st, sign exec_dg_st) dg_state) strategy_tree"
where
  "sign_placement_dg_eqs =
    dg_gen_of
      (unit_dg_spec_placed_st sign_placement_gs True [STR ''g''] False []
        (sign_tf_st_for sign_placement_gs) (sign_enter_st_for sign_placement_gs))
      sign_placement_cfg bot cinit_sign_st bot"

definition sign_placement_dg_td_sol ::
  "(pp \<times> unit) set \<times>
    ((pp \<times> unit) + unit => (sign exec_dg_st, sign exec_dg_st) dg_state)"
where
  "sign_placement_dg_td_sol =
    TD_side_warrowing_apinis_Interp_solve sign_placement_dg_eqs
      (cfg_exit sign_placement_cfg, ())"

lemma sign_placement_dg_td_terminates:
  "TD_side_warrowing_apinis_Interp_solve_c sign_placement_dg_eqs
    (cfg_exit sign_placement_cfg, ()) \<noteq> None"
  by eval

lemma sign_placement_dg_td_post_solution:
  "part_post_solution sign_placement_dg_eqs (cfg_exit sign_placement_cfg, ())
    (snd sign_placement_dg_td_sol) (fst sign_placement_dg_td_sol)"
  unfolding sign_placement_dg_td_sol_def
  by (rule TD_side_warrowing_apinis_Interp.part_post_solution_of_solve_c[
    OF sign_placement_dg_td_terminates])

text \<open>The two executable post-solution facts this example pins: \<open>g\<close> is
  exactly \<open>SPos\<close> at the exit -- assigned from \<open>x\<close>, itself the positive
  literal \<open>5\<close> -- and it sits in the local unknown, because the policy keeps
  it there; the shared side unknown never receives a publication.\<close>

lemma sign_placement_dg_td_value:
  "lookup_resolved_st_q
    (locals (snd sign_placement_dg_td_sol (Inl (FunctionResult prog_main_name, ()))))
    (Global_Location (STR ''g'')) = SPos"
  by eval

lemma sign_placement_dg_td_side_bot:
  "snd sign_placement_dg_td_sol (Inr ()) = bot"
  by eval

subsection \<open>CFG structure facts\<close>

interpretation sign_placement: compiled_cfg "prog_table sign_placement_prog"
    "prog_procs sign_placement_prog" sign_placement_cfg
  by (unfold_locales; unfold sign_placement_cfg_def; simp add: compile_prog_finite)

lemmas sign_placement_wf_cfg = sign_placement.wf
lemmas sign_placement_finE = sign_placement.finite_intra
lemmas sign_placement_finC = sign_placement.finite_calls

lemma sign_placement_exit_covers: "cfg_exit_covers sign_placement_cfg" by eval

lemma sign_placement_vars_cover:
  "vars_cover sign_placement_cfg (fst sign_placement_dg_td_sol)"
  by (rule vars_cover_of_dg_gen_of_covers
        [OF sign_placement_finE sign_placement_finC sign_placement_wf_cfg
            sign_placement_exit_covers
            sign_placement_dg_td_post_solution[unfolded sign_placement_dg_eqs_def]])

lemma sign_placement_wf:
  "wf_compile_input sign_placement_gs (prog_table sign_placement_prog)
     (prog_procs sign_placement_prog)"
  by (auto simp: wf_compile_input_simps sign_placement_prog_def split: if_splits)

lemma sign_placement_sound0:
  "cinit_stores sign_placement_gs \<subseteq> gamma_join_exec sign_placement_gs cinit_sign_st bot"
  by (simp add: gamma_join_exec_def gamma_join_def fun_of_resolved_st_q_for_def
      fun_of_st_cinit_sign_st_for[unfolded fun_of_exec_dg_st_for_def]
      cinit_stores_def gamma_state_def)

subsection \<open>Registration through the placed registration locale\<close>

interpretation sign_placement_reg:
  placed_dg_exec_analysis sign_placement_gs "\<lambda>_. True" "\<lambda>_. False"
    True False "[STR ''g'']" "[]"
    "sign_tf_for sign_placement_gs"
    "sign_tf_st_for sign_placement_gs" "sign_enter_st_for sign_placement_gs"
    "TD_side_warrowing_apinis_Interp.solve" "TD_side_warrowing_apinis_Interp.solve_c"
  by (rule placed_dg_exec_analysis.intro)
     (rule sign_is_sound_transfer_for sign_tf_st_for_commute sign_enter_st_for_commute
           TD_side_warrowing_apinis_Interp.part_post_solution_of_solve_c
      | force simp: sign_placement_globals sign_placement_prog_def)+

subsection \<open>Collecting soundness of the computed placed result\<close>

theorem sign_placement_dg_td_collect_sound:
  "ltr_collect sign_placement_gs sign_placement_cfg
     (cinit_stores sign_placement_gs) v
   \<subseteq> sign_placement_reg.gamma (snd sign_placement_dg_td_sol) v"
  unfolding sign_placement_dg_td_sol_def sign_placement_dg_eqs_def sign_placement_cfg_def
  by (rule sign_placement_reg.collect_sound
        [OF sign_placement_dg_td_terminates
              [unfolded sign_placement_dg_eqs_def sign_placement_cfg_def]
            sign_placement_wf
            sign_placement_vars_cover
              [unfolded sign_placement_dg_td_sol_def sign_placement_dg_eqs_def
                 sign_placement_cfg_def]
            sign_placement_finE[unfolded sign_placement_cfg_def]
            sign_placement_finC[unfolded sign_placement_cfg_def]
            sign_placement_sound0])

end
