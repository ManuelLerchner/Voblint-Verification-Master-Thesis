theory Sign_Exec_Sound
  imports Sign_Exec Sign_Side_Soundness Solver_Side_RG
          "TD.TD_side_upd_rule"
          "Voblint_IMP2.IMP2_Notation"
          Analysis_GraphViz
begin

section \<open>Executable sign analysis: the computed result and its certified soundness\<close>

text \<open>
  High-level vocabulary for the executable analyzer, so example statements read
  at the level of intent rather than solver plumbing:

    \<^item> \<open>sign_exec_raw \<Pi> ps main\<close>  -- the raw solver solution (\<open>pp + unit => sign st\<close>),
      code-generating, the thing @{command value} / \<open>eval\<close> evaluates;
    \<^item> \<open>sign_exec \<Pi> ps main\<close>      -- the analyzer's computed abstract state at the
      program exit (a \<open>sign abs_state\<close>), read back through \<open>fun_of_st\<close>;
    \<^item> \<open>sign_exec_terminates \<Pi> ps main\<close> -- the single assumption: the vendored
      solver terminates on this program.

  \<open>sign_exec_sound_collecting\<close> / \<open>sign_exec_sound_trace\<close> are the program-parametric
  soundness theorems; concrete examples only fix a program and instantiate them.
\<close>

definition sign_exec_eqs ::
    "proc_table \<Rightarrow> pname list \<Rightarrow> com \<Rightarrow> (pp, unit, sign st) eqsT" where
  "sign_exec_eqs \<Pi> ps main =
     side_cfg_T_eff_st (compile_prog \<Pi> ps main) sign_etf_st bot cinit_sign_st ()"

definition sign_exec_raw ::
    "proc_table \<Rightarrow> pname list \<Rightarrow> com \<Rightarrow> (pp + unit \<Rightarrow> sign st)" where
  "sign_exec_raw \<Pi> ps main =
     snd (TD_side_always_join_Interp_solve (sign_exec_eqs \<Pi> ps main)
            (cfg_exit (compile_prog \<Pi> ps main)))"

definition sign_exec ::
    "proc_table \<Rightarrow> pname list \<Rightarrow> com \<Rightarrow> sign abs_state" where
  "sign_exec \<Pi> ps main =
     side_env (fun_of_st \<circ> sign_exec_raw \<Pi> ps main) (cfg_exit (compile_prog \<Pi> ps main))"

definition sign_exec_terminates ::
    "proc_table \<Rightarrow> pname list \<Rightarrow> com \<Rightarrow> bool" where
  "sign_exec_terminates \<Pi> ps main =
     TD_side_always_join_Interp.solve_dom TYPE(unit) TYPE(sign st)
        (sign_exec_eqs \<Pi> ps main) (cfg_exit (compile_prog \<Pi> ps main))"

text \<open>
  Discharging termination by execution.  When the vendored side solver's
  executable @{const TD_side_always_join_Interp_solve_c} returns a result on a
  concrete program, that program lies in the solver's domain, so
  @{const sign_exec_terminates} holds.  The bridge is the solver's
  @{thm TD_side_always_join_Interp.term_equivalence}
  (\<open>solve_dom x \<longleftrightarrow> solve_c_dom x\<close>): the option-valued @{const TD_side_always_join_Interp_solve_c}
  code-generates, so examples discharge the premise by @{method eval}, turning
  the soundness assumption into a proved fact.
\<close>

lemma sign_exec_terminates_via_solve_c:
  assumes "TD_side_always_join_Interp_solve_c (sign_exec_eqs \<Pi> ps main)
             (cfg_exit (compile_prog \<Pi> ps main)) \<noteq> None"
  shows "sign_exec_terminates \<Pi> ps main"
  unfolding sign_exec_terminates_def TD_side_always_join_Interp.term_equivalence
            TD_side_always_join_Interp.solve_c_dom_def
  using assms by simp

text \<open>
  Soundness at the state level: starting from any C-faithful initial store
  (globals zero, locals arbitrary), every store reaching the exit under the
  interprocedural collecting semantics is over-approximated by the computed
  result.  Switching the seed from \<open>top_sign_st\<close> to \<open>cinit_sign_st\<close> (globals
  at \<open>SZero\<close>) lets the richer lattice give tighter global bounds, e.g.\
  \<open>Gresult = SNonNeg\<close> instead of \<open>STop\<close>.

  The side solver keeps \<open>Inr\<close> slots globally restricted via
  @{theory Voblint_Analysis.Solver_Side_RG} (\<open>side_rg\<close> on the eqsys
  \<open>\<Longrightarrow>\<close> \<open>TD_side_always_join_solve_Inr_rg\<close> \<open>\<Longrightarrow>\<close> \<open>inr_slot_locals_bot\<close>).
\<close>



theorem sign_exec_sound_collecting:
  assumes solves: "sign_exec_terminates \<Pi> ps main"
  shows "cfg_collect (compile_prog \<Pi> ps main) cinit_stores (cfg_exit (compile_prog \<Pi> ps main))
         \<le> \<lbrakk>sign_exec \<Pi> ps main\<rbrakk>"
proof -
  define g :: cfg where "g = compile_prog \<Pi> ps main"
  define sol :: "pp set \<times> (pp + unit \<Rightarrow> sign st)" where
    "sol = TD_side_always_join_Interp_solve (sign_exec_eqs \<Pi> ps main) (cfg_exit g)"
  define \<sigma> :: "pp + unit \<Rightarrow> sign abs_state" where "\<sigma> = fun_of_st \<circ> snd sol"
  have fin: "finite (edges g)" unfolding g_def using compile_prog_finite by simp
  have finC: "finite (combines g)" unfolding g_def using compile_prog_finite by simp
  have dom: "TD_side_always_join_Interp.solve_dom TYPE(unit) TYPE(sign st)
               (sign_exec_eqs \<Pi> ps main) (cfg_exit g)"
    using solves unfolding sign_exec_terminates_def g_def by simp
  have pp0: "part_post_solution (sign_exec_eqs \<Pi> ps main) (cfg_exit g) (snd sol) (fst sol)"
    using TD_side_always_join_Interp.partial_post_solution[OF dom, of "fst sol" "snd sol"]
    unfolding sol_def by simp
  have pp_st: "part_post_solution (side_cfg_T_eff_st g sign_etf_st bot cinit_sign_st ())
                 (cfg_exit g) (snd sol) (fst sol)"
    using pp0 by (simp add: sign_exec_eqs_def g_def)
  have pp_eff: "part_post_solution
                  (side_cfg_T_eff g sign_etf_unit bot
                     (\<lambda>x. if is_global x then SZero else STop) ())
                  (cfg_exit g) \<sigma> (fst sol)"
    using part_post_solution_st_to_abs_eff_unit_transfer
            [OF sign_etf_unit_edge_tree sign_etf_unit_combine_tree
                sign_etf_st_edge_tree sign_etf_st_combine_tree sign_tf_st_commute pp_st]
    by (simp add: \<sigma>_def fun_of_st_cinit_sign_st bot_fun_def)
  have cone: "cone_compatible_etf sign_etf_unit" by (rule sign_etf_unit_cone_compatible)
  have srz: "\<And>z. side_rg (sign_exec_eqs \<Pi> ps main z)"
    unfolding sign_exec_eqs_def
    by (rule side_rg_side_cfg_T_eff_st_unit
          [OF sign_etf_st_exists_unit sign_etf_st_combine_tree])
  have solpair: "TD_side_always_join_Interp_solve (sign_exec_eqs \<Pi> ps main) (cfg_exit g)
                   = (fst sol, snd sol)"
    unfolding sol_def by simp
  have rg: "\<And>gg. snd sol (Inr gg) = restrict_global_st (snd sol (Inr gg))"
    by (rule TD_side_always_join_solve_Inr_rg[OF dom srz solpair])
  have inr: "inr_slot_locals_bot \<sigma>"
    unfolding \<sigma>_def
    using inr_slot_locals_bot_fun_of_st_restrict_global_st rg by blast
  have reach: "cfg_reaches g (cfg_entry g) (cfg_exit g)"
    by (simp add: g_def compile_prog_entry_cfg_reaches_exit)
  have entry_in: "cfg_entry g \<in> fst sol"
    by (rule side_cone_in_vars_eff_cone[OF pp_eff fin finC cone reach])
  have entry_le: "(\<lambda>x. if is_global x then SZero else STop) \<le> side_env \<sigma> (cfg_entry g)"
    by (rule s0_le_side_env_entry_eff[OF pp_eff entry_in])
  have seed_cov: "cinit_stores \<subseteq> \<lbrakk>\<lambda>x. if is_global x then SZero else STop\<rbrakk>"
    unfolding cinit_stores_def gamma_state_def
    by auto
  have entry_cov: "cinit_stores \<le> \<lbrakk>side_env \<sigma> (cfg_entry g)\<rbrakk>"
    using seed_cov gamma_state_mono[OF entry_le] by (rule subset_trans)
  have "cfg_collect g cinit_stores (cfg_exit g)
        \<le> \<lbrakk>side_env \<sigma> (cfg_exit g)\<rbrakk>"
    by (rule side_collect_sound_exit_pruned_eff_cone
          [OF sign_sound_etf_unit pp_eff fin finC entry_cov cone inr])
  then show ?thesis
    by (simp add: g_def \<sigma>_def sol_def sign_exec_def sign_exec_raw_def)
qed

section \<open>Whole-program convenience layer\<close>

text \<open>
  An @{type imp_prog} written with the \<open>\<lbrakk> \<dots> \<rbrakk>\<close> bracket already bundles the
  procedure table, procedure-name list, and main command.  The wrappers below
  feed those three projections to the analyzer in one step, so example
  statements name the program once instead of repeating the triple.
\<close>

definition prog_cfg :: "imp_prog \<Rightarrow> cfg" where
  "prog_cfg p = compile_prog (prog_table p) (prog_procs p) (prog_main p)"

definition sign_exec_prog :: "imp_prog \<Rightarrow> sign abs_state" where
  "sign_exec_prog p = sign_exec (prog_table p) (prog_procs p) (prog_main p)"

definition sign_terminates_prog :: "imp_prog \<Rightarrow> bool" where
  "sign_terminates_prog p = sign_exec_terminates (prog_table p) (prog_procs p) (prog_main p)"

lemma sign_terminates_prog_via_solve_c:
  assumes "TD_side_always_join_Interp_solve_c
             (sign_exec_eqs (prog_table p) (prog_procs p) (prog_main p))
             (cfg_exit (compile_prog (prog_table p) (prog_procs p) (prog_main p))) \<noteq> None"
  shows "sign_terminates_prog p"
  unfolding sign_terminates_prog_def
  using assms by (rule sign_exec_terminates_via_solve_c)

corollary sign_exec_prog_sound_collecting:
  assumes "sign_terminates_prog p"
  shows "cfg_collect (prog_cfg p) cinit_stores (cfg_exit (prog_cfg p))
           \<le> \<lbrakk>sign_exec_prog p\<rbrakk>"
  using assms unfolding sign_terminates_prog_def prog_cfg_def sign_exec_prog_def
  by (rule sign_exec_sound_collecting)

section \<open>Visualisation convenience\<close>

text \<open>
  One-command annotated CFG rendering for the sign domain through the canonical
  context-expanded graph model.  It compiles the program, runs the solver, and
  adapts the unit context to the explicit presentation domain.

  Typical example-file use:

  @{text [display] "ML_val \<open>
    writeln (@{code sign_annotated_dot_prog_lit} @{code my_prog})
  \<close>"}
\<close>


definition sign_graph_config ::
  "proc_table \<Rightarrow> pname list \<Rightarrow> com \<Rightarrow>
    (unit, unit, sign abs_state, sign abs_state) analysis_graph_config" where
  "sign_graph_config \<Pi> ps main =
    \<lparr> local_of = id,
      route = (\<lambda>_ _ _ _. ()),
      show_context = (\<lambda>_. ''''),
      locals_for_pp = (\<lambda>p.
        let sc = compiled_procedure_scope \<Pi> ps main (compile_prog \<Pi> ps main) p
        in scope_formals sc @ scope_locals sc),
      return_slot_for_pp = (\<lambda>p.
        scope_return_slot (compiled_procedure_scope \<Pi> ps main
          (compile_prog \<Pi> ps main) p)),
      globals_to_show = compiled_global_vars (compile_prog \<Pi> ps main),
      show_local = (\<lambda>_ _ vars s.
        map (\<lambda>x. x @ ''='' @ show_val (s x)) vars),
      format_return = (\<lambda>_ _ ret s.
        if s ret = STop then [] else [''ret='' @ show_val (s ret)]),
      show_global = (\<lambda>_ vars s.
        map (\<lambda>x. x @ ''='' @ show_val (s x)) vars),
      show_global_key = (\<lambda>_. ''Globals''),
      is_shared_global = (\<lambda>_. True),
      show_internal_globals = False,
      owner_of = compiled_owner_of \<Pi> ps main,
      cluster_label = (\<lambda>owner _. owner),
      source_text = Some (string_of_program \<Pi> ps main)
    \<rparr>"

definition sign_graph_solution ::
  "(pp + unit \<Rightarrow> sign st) \<Rightarrow> (pp \<times> unit + unit \<Rightarrow> sign abs_state)" where
  "sign_graph_solution sol z =
    (case z of Inl (p, ()) \<Rightarrow> fun_of_st (sol (Inl p))
     | Inr () \<Rightarrow> fun_of_st (sol (Inr ())) )"

definition sign_annotated_dot_lit ::
  "proc_table \<Rightarrow> pname list \<Rightarrow> com \<Rightarrow> String.literal" where
  "sign_annotated_dot_lit \<Pi> ps main =
    String.implode
      (let g = compile_prog \<Pi> ps main;
           domain = contextual_graph_domain g (\<lambda>_. [()]) @ [Inr ()];
           sol = sign_graph_solution (sign_exec_raw \<Pi> ps main)
       in contextual_analysis_dot (sign_graph_config \<Pi> ps main) g domain sol)"

definition sign_annotated_dot_prog_lit :: "imp_prog \<Rightarrow> String.literal" where
  "sign_annotated_dot_prog_lit p =
     sign_annotated_dot_lit (prog_table p) (prog_procs p) (prog_main p)"

end
