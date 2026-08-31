theory Example_Interval_Placement
  imports
    "Voblint_Examples.Placement_Policy_Exec"
    "Voblint_Exec.DG_Coverage"
    "Voblint_Analysis.Ivl_Exec"
    "Voblint_VIMP.VIMP_Notation"
begin

section \<open>Interval placement slice with independent global policies\<close>

text \<open>
  The program has two declared globals with independent placement.  The procedure
  call binds a formal, introduces the implicit local \<open>tmp\<close>, and returns into the
  caller-local \<open>answer\<close>.

  \<open>balance\<close> and \<open>request_count\<close> are placed as a static analogue of Goblint's own
  protected/unprotected privatization split (\<open>VojdaniPriv\<close> in \<open>basePriv.ml\<close>):
  \<open>balance\<close> is \<open>keep_local\<close>-only, never \<open>publish_side\<close> -- the protected case, whose
  write updates the local \<open>CPA\<close> but skips \<open>sideg\<close>.  \<open>request_count\<close> is
  \<open>publish_side\<close>-only, never \<open>keep_local\<close> -- the unprotected case, whose write goes
  straight to the shared side.  This is a static per-variable policy, fixed for the
  whole program; it does not model the dynamic transition a real lock/unlock would
  drive (a protected global's write becoming visible to \<open>G\<close> only once the critical
  section it was written under is released). Modelling that transition needs an
  action-specific publish hook at the unlock edge, which \<open>unit_dg_spec_placed\<close>'s
  generic per-edge transfer does not have; it is a framework extension, not an
  example, and is out of scope here.  Even this static split already needs
  \<open>gamma_join\<close>, not \<open>gamma_unit\<close>: \<open>balance\<close>'s and \<open>request_count\<close>'s live values
  sit on different sides regardless of the declared-global classifier, so no
  single-bit ownership routing can recover both.  The classifier-split
  representation of the covering pair keeps all locals plus \<open>balance\<close> and lists
  \<open>request_count\<close> as the one published global.
\<close>

definition placement_prog :: imp_prog where
  "placement_prog = program {
     global balance, request_count;
     void add(x) {
       tmp := balance + x;
       balance := tmp;
       request_count := request_count + 1;
       return balance
     }
     void main() { answer := add(3) }
   }"

abbreviation placement_gs :: "vname \<Rightarrow> bool" where
  "placement_gs \<equiv> declared_global placement_prog"

definition placement_cfg :: cfg where
  "placement_cfg =
    compile_prog (prog_table placement_prog) (prog_procs placement_prog)"

text \<open>The two declared globals, as the fact the classifier-split shape
  obligations reduce to.\<close>
lemma placement_globals:
  "placement_gs x \<longleftrightarrow> x = STR ''balance'' \<or> x = STR ''request_count''"
  by (auto simp: placement_prog_def)

subsection \<open>The placed equation system and its computed solution\<close>

text \<open>The seeds mirror the policy: the local seed carries the full initial
  state (everything \<open>keep_local\<close> covers reads from it), while the shared side
  seed is the \<open>publish_side\<close> projection of the same initial state, so
  \<open>request_count\<close>'s initial value is visible flow-insensitively from the
  start.\<close>

definition placement_dg_eqs ::
  "pp \<times> unit =>
    (pp \<times> unit, unit, (ivl exec_dg_st, ivl exec_dg_st) dg_state) strategy_tree"
where
  "placement_dg_eqs =
    dg_gen_of
      (unit_dg_spec_placed_st placement_gs
        True [STR ''balance''] False [STR ''request_count'']
        (ivl_tf_st_for placement_gs) (ivl_enter_st_for placement_gs))
      placement_cfg bot cinit_ivl_st
      (project_placed_resolved_q False [STR ''request_count''] cinit_ivl_st)"

definition placement_dg_td_sol ::
  "(pp \<times> unit) set \<times>
    ((pp \<times> unit) + unit => (ivl exec_dg_st, ivl exec_dg_st) dg_state)"
where
  "placement_dg_td_sol =
    TD_side_warrowing_apinis_Interp_solve placement_dg_eqs
      (cfg_exit placement_cfg, ())"

lemma placement_dg_td_terminates:
  "TD_side_warrowing_apinis_Interp_solve_c placement_dg_eqs
    (cfg_exit placement_cfg, ()) \<noteq> None"
  by eval

text \<open>The executable post-solution facts this example pins: the bound formal
  \<open>x\<close> at the callee entry, the protected \<open>balance\<close> carried flow-sensitively
  through the local unknowns, the unprotected \<open>request_count\<close> accumulated
  (and widened) on the shared side, and the return value landing in the
  caller-local \<open>answer\<close>.\<close>

lemma placement_dg_td_values:
  "lookup_resolved_st_q
    (locals (snd placement_dg_td_sol (Inl (Statement 0, ()))))
    (Local_Location (STR ''x'')) = Ivl (Fin 3) (Fin 3)"
  "lookup_resolved_st_q
    (locals (snd placement_dg_td_sol (Inl (Statement 2, ()))))
    (Global_Location (STR ''balance'')) = Ivl (Fin 3) (Fin 3)"
  "lookup_resolved_st_q
    (globs (snd placement_dg_td_sol (Inr ())))
    (Global_Location (STR ''request_count'')) = Ivl (Fin 0) PlusInf"
  "lookup_resolved_st_q
    (locals (snd placement_dg_td_sol (Inl (Statement 6, ()))))
    (Local_Location (STR ''answer'')) = Ivl (Fin 3) (Fin 3)"
  by eval+

lemma placement_dg_td_post_solution:
  "part_post_solution placement_dg_eqs (cfg_exit placement_cfg, ())
    (snd placement_dg_td_sol) (fst placement_dg_td_sol)"
  unfolding placement_dg_td_sol_def
  by (rule TD_side_warrowing_apinis_Interp.part_post_solution_of_solve_c[
    OF placement_dg_td_terminates])

subsection \<open>CFG structure facts\<close>

interpretation placement: compiled_cfg "prog_table placement_prog"
    "prog_procs placement_prog" placement_cfg
  by (unfold_locales; unfold placement_cfg_def; simp add: compile_prog_finite)

lemmas placement_wf_cfg = placement.wf
lemmas placement_finE = placement.finite_intra
lemmas placement_finC = placement.finite_calls

lemma placement_exit_covers: "cfg_exit_covers placement_cfg" by eval

lemma placement_vars_cover:
  "vars_cover placement_cfg (fst placement_dg_td_sol)"
  by (rule vars_cover_of_dg_gen_of_covers
        [OF placement_finE placement_finC placement_wf_cfg
            placement_exit_covers
            placement_dg_td_post_solution[unfolded placement_dg_eqs_def]])

lemma placement_wf:
  "wf_compile_input placement_gs (prog_table placement_prog)
     (prog_procs placement_prog)"
  by (auto simp: wf_compile_input_simps placement_prog_def split: if_splits)

lemma placement_sound0:
  "cinit_stores placement_gs
   \<subseteq> gamma_join_exec placement_gs cinit_ivl_st
       (project_placed_resolved_q False [STR ''request_count''] cinit_ivl_st)"
proof -
  have base: "cinit_stores placement_gs
      \<subseteq> \<lbrakk>fun_of_resolved_st_q_for placement_gs cinit_ivl_st\<rbrakk>"
    by (auto simp add: fun_of_resolved_st_q_for_def
        fun_of_st_cinit_ivl_st_for[unfolded fun_of_exec_dg_st_for_def]
        cinit_stores_def gamma_state_def)
  have mono: "\<lbrakk>fun_of_resolved_st_q_for placement_gs cinit_ivl_st\<rbrakk>
      \<subseteq> \<lbrakk>fun_of_resolved_st_q_for placement_gs cinit_ivl_st
           \<squnion> fun_of_resolved_st_q_for placement_gs
               (project_placed_resolved_q False [STR ''request_count''] cinit_ivl_st)\<rbrakk>"
    by (rule gamma_state_mono) simp
  show ?thesis
    unfolding gamma_join_exec_def gamma_join_def using base mono by blast
qed

subsection \<open>Registration through the placed registration locale\<close>

interpretation placement_reg:
  placed_dg_exec_analysis placement_gs
    "\<lambda>x. \<not> placement_gs x \<or> x = STR ''balance''"
    "\<lambda>x. placement_gs x \<and> x = STR ''request_count''"
    True False "[STR ''balance'']" "[STR ''request_count'']"
    "ivl_tf_for placement_gs"
    "ivl_tf_st_for placement_gs" "ivl_enter_st_for placement_gs"
    "TD_side_warrowing_apinis_Interp.solve" "TD_side_warrowing_apinis_Interp.solve_c"
  by (rule placed_dg_exec_analysis.intro)
     (rule ivl_is_sound_transfer_for ivl_tf_st_for_commute ivl_enter_st_for_commute
           TD_side_warrowing_apinis_Interp.part_post_solution_of_solve_c
      | force simp: placement_globals placement_prog_def)+

subsection \<open>Collecting soundness of the computed placed result\<close>

text \<open>The trace-native collecting soundness endpoint: every stack-faithful
  local trace starting from the concrete initial stores is bounded by the
  computed placed post-solution at every program point, read back through
  \<open>gamma_join\<close>.\<close>

theorem placement_dg_td_collect_sound:
  "ltr_collect placement_gs placement_cfg
     (cinit_stores placement_gs) v
   \<subseteq> placement_reg.gamma (snd placement_dg_td_sol) v"
  unfolding placement_dg_td_sol_def placement_dg_eqs_def placement_cfg_def
  by (rule placement_reg.collect_sound
        [OF placement_dg_td_terminates
              [unfolded placement_dg_eqs_def placement_cfg_def]
            placement_wf
            placement_vars_cover
              [unfolded placement_dg_td_sol_def placement_dg_eqs_def
                 placement_cfg_def]
            placement_finE[unfolded placement_cfg_def]
            placement_finC[unfolded placement_cfg_def]
            placement_sound0])

end
