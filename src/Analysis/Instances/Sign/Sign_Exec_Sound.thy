theory Sign_Exec_Sound
  imports Sign_Exec Sign_Side_Soundness Voblint_Core.Solver_Side_RG
          "TD.TD_side_upd_rule"
          "Voblint_VIMP.VIMP_Notation"
          "Voblint_CFG.Compile_Invariants"
          Analysis_GraphViz
          "Voblint_Analysis.Exec_DG_Bridge"
begin

section \<open>Executable sign analysis: the computed result and its certified soundness\<close>

text \<open>
  High-level vocabulary for the executable analyzer, so example statements read
  at the level of intent rather than solver plumbing:

    \<^item> \<open>sign_exec_raw \<Pi> ps main\<close>  -- the raw solver solution (\<open>pp + unit => sign resolved_st_q\<close>),
      code-generating, the thing @{command value} / \<open>eval\<close> evaluates;
    \<^item> \<open>sign_exec gs \<Pi> ps main\<close>   -- the analyzer's computed abstract state at the
      program exit (a \<open>sign abs_state\<close>), read back through \<open>fun_of_resolved_st_q_for gs\<close>;
    \<^item> \<open>sign_exec_terminates \<Pi> ps main\<close> -- the single assumption: the vendored
      solver terminates on this program.

  \<open>sign_exec_sound_collecting\<close> / \<open>sign_exec_sound_trace\<close> are the program-parametric
  soundness theorems; concrete examples only fix a program and instantiate them.
\<close>

definition sign_exec_eqs ::
    "(vname \<Rightarrow> bool) \<Rightarrow> proc_table \<Rightarrow> pname list \<Rightarrow> pname \<Rightarrow> com \<Rightarrow> (pp, unit, sign resolved_st_q) eqsT" where
  "sign_exec_eqs gs \<Pi> ps mnm main =
     side_cfg_T_eff_st (compile_prog \<Pi> ps mnm main) (sign_etf_st_for gs) bot cinit_sign_st ()"

definition sign_exec_raw ::
    "(vname \<Rightarrow> bool) \<Rightarrow> proc_table \<Rightarrow> pname list \<Rightarrow> pname \<Rightarrow> com \<Rightarrow> (pp + unit \<Rightarrow> sign resolved_st_q)" where
  "sign_exec_raw gs \<Pi> ps mnm main =
     snd (TD_side_always_join_Interp_solve (sign_exec_eqs gs \<Pi> ps mnm main)
            (cfg_exit (compile_prog \<Pi> ps mnm main)))"

definition sign_exec_at ::
    "(vname \<Rightarrow> bool) \<Rightarrow> proc_table \<Rightarrow> pname list \<Rightarrow> pname \<Rightarrow> com \<Rightarrow> pp \<Rightarrow> sign abs_state" where
  "sign_exec_at gs \<Pi> ps mnm main v =
     side_env (fun_of_resolved_st_q_for gs \<circ> sign_exec_raw gs \<Pi> ps mnm main) v"

definition sign_exec ::
    "(vname \<Rightarrow> bool) \<Rightarrow> proc_table \<Rightarrow> pname list \<Rightarrow> pname \<Rightarrow> com \<Rightarrow> sign abs_state" where
  "sign_exec gs \<Pi> ps mnm main = sign_exec_at gs \<Pi> ps mnm main (cfg_exit (compile_prog \<Pi> ps mnm main))"

definition sign_exec_terminates ::
    "(vname \<Rightarrow> bool) \<Rightarrow> proc_table \<Rightarrow> pname list \<Rightarrow> pname \<Rightarrow> com \<Rightarrow> bool" where
  "sign_exec_terminates gs \<Pi> ps mnm main =
     TD_side_always_join_Interp.solve_dom TYPE(unit) TYPE(sign resolved_st_q)
        (sign_exec_eqs gs \<Pi> ps mnm main) (cfg_exit (compile_prog \<Pi> ps mnm main))"

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
  assumes "TD_side_always_join_Interp_solve_c (sign_exec_eqs gs \<Pi> ps mnm main)
             (cfg_exit (compile_prog \<Pi> ps mnm main)) \<noteq> None"
  shows "sign_exec_terminates gs \<Pi> ps mnm main"
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
  @{theory Voblint_Core.Solver_Side_RG} (\<open>side_rg\<close> on the eqsys
  \<open>\<Longrightarrow>\<close> \<open>TD_side_always_join_solve_Inr_rg\<close> \<open>\<Longrightarrow>\<close> \<open>inr_slot_locals_bot\<close>).
\<close>



text \<open>
  Node-local: the query cone theorem \<open>side_collect_sound_in_eff_cone\<close> already
  bounds \<open>ltr_collect\<close> at any node \<open>v\<close> the solve call's query seed (here \<open>cfg_exit\<close>)
  can reach --- not only at the seed itself. \<open>sign_exec_sound_collecting\<close> below is the
  \<open>v = cfg_exit g\<close> specialization, via \<open>cfg_reaches_refl\<close>, matching how
  \<open>side_collect_sound_exit_eff_ltr_cone\<close> specializes its own cone theorem.
\<close>

theorem sign_exec_sound_collecting_at:
  fixes mnm :: pname and v :: pp
  assumes solves: "sign_exec_terminates gs \<Pi> ps mnm main"
    and reach_v: "cfg_reaches (compile_prog \<Pi> ps mnm main) v (cfg_exit (compile_prog \<Pi> ps mnm main))"
  shows "ltr_collect gs (compile_prog \<Pi> ps mnm main) (cinit_stores gs) v
         \<le> \<lbrakk>sign_exec_at gs \<Pi> ps mnm main v\<rbrakk>"
proof -
  define g :: cfg where "g = compile_prog \<Pi> ps mnm main"
  define sol :: "pp set \<times> (pp + unit \<Rightarrow> sign resolved_st_q)" where
    "sol = TD_side_always_join_Interp_solve (sign_exec_eqs gs \<Pi> ps mnm main) (cfg_exit g)"
  define \<sigma> :: "pp + unit \<Rightarrow> sign abs_state" where "\<sigma> = fun_of_resolved_st_q_for gs \<circ> snd sol"
  have fin: "finite (intra g)" unfolding g_def using compile_prog_finite by simp
  have finC: "finite (calls g)" unfolding g_def using compile_prog_finite by simp
  have wf: "wf_cfg g" unfolding g_def by (rule compile_prog_wf)
  have dom: "TD_side_always_join_Interp.solve_dom TYPE(unit) TYPE(sign resolved_st_q)
               (sign_exec_eqs gs \<Pi> ps mnm main) (cfg_exit g)"
    using solves unfolding sign_exec_terminates_def g_def by simp
  have pp0: "part_post_solution (sign_exec_eqs gs \<Pi> ps mnm main) (cfg_exit g) (snd sol) (fst sol)"
    using TD_side_always_join_Interp.partial_post_solution[OF dom, of "fst sol" "snd sol"]
    unfolding sol_def by simp
  have pp_st: "part_post_solution (side_cfg_T_eff_st g (sign_etf_st_for gs) bot cinit_sign_st ())
                 (cfg_exit g) (snd sol) (fst sol)"
    using pp0 by (simp add: sign_exec_eqs_def g_def)
  have pp_eff: "part_post_solution
                  (side_cfg_T_eff gs g (sign_etf_unit gs) bot
                     (\<lambda>x. if gs x then SZero else STop) ())
                  (cfg_exit g) \<sigma> (fst sol)"
    using part_post_solution_st_to_abs_eff_unit_transfer
            [OF sign_etf_unit_edge_tree sign_etf_unit_combine_tree
                sign_etf_st_for_edge_tree sign_etf_st_for_combine_tree sign_tf_st_for_commute
                sign_etf_unit_enter_tree_tf sign_etf_st_for_enter_tree sign_enter_st_for_commute pp_st]
    by (simp add: \<sigma>_def fun_of_st_cinit_sign_st_for bot_fun_def)
  have cone: "cone_compatible_etf gs (sign_etf_unit gs)" by (rule sign_etf_unit_cone_compatible)
  have srz: "\<And>z. side_rg (sign_exec_eqs gs \<Pi> ps mnm main z)"
    unfolding sign_exec_eqs_def
    by (rule side_rg_side_cfg_T_eff_st_unit
          [OF sign_etf_st_for_exists_unit sign_etf_st_for_enter_exists_unit sign_etf_st_for_combine_tree])
  have solpair: "TD_side_always_join_Interp_solve (sign_exec_eqs gs \<Pi> ps mnm main) (cfg_exit g)
                   = (fst sol, snd sol)"
    unfolding sol_def by simp
  have rg: "\<And>gg. snd sol (Inr gg) = restrict_global_resolved_q (snd sol (Inr gg))"
    by (rule TD_side_always_join_solve_Inr_rg[OF dom srz solpair])
  have inr: "inr_slot_locals_bot gs \<sigma>"
    unfolding \<sigma>_def
    using inr_slot_locals_bot_fun_of_resolved_st_q_for_restrict_global_abs rg by blast
  have reach: "cfg_reaches g (cfg_entry g) (cfg_exit g)"
    by (simp add: g_def compile_prog_entry_cfg_reaches_exit)
  have entry_in: "cfg_entry g \<in> fst sol"
    by (rule side_cone_in_vars_eff_cone[OF pp_eff fin finC wf cone reach])
  have entry_le: "(\<lambda>x. if gs x then SZero else STop) \<le> side_env \<sigma> (cfg_entry g)"
    by (rule s0_le_side_env_entry_eff[OF pp_eff entry_in])
  have seed_cov: "cinit_stores gs \<subseteq> \<lbrakk>\<lambda>x. if gs x then SZero else STop\<rbrakk>"
    unfolding cinit_stores_def gamma_state_def
    by auto
  have entry_cov: "cinit_stores gs \<le> \<lbrakk>side_env \<sigma> (cfg_entry g)\<rbrakk>"
    using seed_cov gamma_state_mono[OF entry_le] by (rule subset_trans)
  have reach_v': "cfg_reaches g v (cfg_exit g)"
    using reach_v unfolding g_def by simp
  have "ltr_collect gs g (cinit_stores gs) v
        \<le> \<lbrakk>side_env \<sigma> v\<rbrakk>"
    by (rule side_collect_sound_in_eff_cone
          [OF sign_sound_etf_unit pp_eff fin finC wf entry_cov cone inr reach_v'])
  then show ?thesis
    by (simp add: g_def \<sigma>_def sol_def sign_exec_at_def sign_exec_raw_def)
qed

corollary sign_exec_sound_collecting:
  fixes mnm :: pname
  assumes solves: "sign_exec_terminates gs \<Pi> ps mnm main"
  shows "ltr_collect gs (compile_prog \<Pi> ps mnm main) (cinit_stores gs) (cfg_exit (compile_prog \<Pi> ps mnm main))
         \<le> \<lbrakk>sign_exec gs \<Pi> ps mnm main\<rbrakk>"
  unfolding sign_exec_def
  by (rule sign_exec_sound_collecting_at[OF solves cfg_reaches_refl])

section \<open>Whole-program convenience layer\<close>

text \<open>
  An @{type imp_prog} written with the \<open>\<lbrakk> \<dots> \<rbrakk>\<close> bracket already bundles the
  procedure table, procedure-name list, and main command.  The wrappers below
  feed those three projections to the analyzer in one step, so example
  statements name the program once instead of repeating the triple.
  \<^const>\<open>prog_cfg\<close> (\<^theory>\<open>Voblint_CFG.Compile_Invariants\<close>) is the shared,
  domain-independent instance of this same projection for the CFG itself, so
  it is imported rather than redefined here.
\<close>

definition sign_exec_prog_at :: "(vname \<Rightarrow> bool) \<Rightarrow> pname \<Rightarrow> imp_prog \<Rightarrow> pp \<Rightarrow> sign abs_state" where
  "sign_exec_prog_at gs mnm p v = sign_exec_at gs (prog_table p) (prog_procs p) mnm (prog_main p) v"

definition sign_exec_prog :: "(vname \<Rightarrow> bool) \<Rightarrow> pname \<Rightarrow> imp_prog \<Rightarrow> sign abs_state" where
  "sign_exec_prog gs mnm p = sign_exec_prog_at gs mnm p (cfg_exit (prog_cfg mnm p))"

definition sign_terminates_prog :: "(vname \<Rightarrow> bool) \<Rightarrow> pname \<Rightarrow> imp_prog \<Rightarrow> bool" where
  "sign_terminates_prog gs mnm p = sign_exec_terminates gs (prog_table p) (prog_procs p) mnm (prog_main p)"

lemma sign_terminates_prog_via_solve_c:
  assumes "TD_side_always_join_Interp_solve_c
             (sign_exec_eqs gs (prog_table p) (prog_procs p) mnm (prog_main p))
             (cfg_exit (compile_prog (prog_table p) (prog_procs p) mnm (prog_main p))) \<noteq> None"
  shows "sign_terminates_prog gs mnm p"
  unfolding sign_terminates_prog_def
  using assms by (rule sign_exec_terminates_via_solve_c)

corollary sign_exec_prog_sound_collecting_at:
  assumes "sign_terminates_prog gs mnm p"
    and "cfg_reaches (prog_cfg mnm p) v (cfg_exit (prog_cfg mnm p))"
  shows "ltr_collect gs (prog_cfg mnm p) (cinit_stores gs) v
           \<le> \<lbrakk>sign_exec_prog_at gs mnm p v\<rbrakk>"
  using assms unfolding sign_terminates_prog_def prog_cfg_def sign_exec_prog_at_def
  by (rule sign_exec_sound_collecting_at)

corollary sign_exec_prog_sound_collecting:
  assumes "sign_terminates_prog gs mnm p"
  shows "ltr_collect gs (prog_cfg mnm p) (cinit_stores gs) (cfg_exit (prog_cfg mnm p))
           \<le> \<lbrakk>sign_exec_prog gs mnm p\<rbrakk>"
  unfolding sign_exec_prog_def
  by (rule sign_exec_prog_sound_collecting_at[OF assms cfg_reaches_refl])

section \<open>Native D/G runtime API: an arbitrary VIMP program\<close>

text \<open>
  \<open>sign_exec_prog\<close> above is the older \<open>side_cfg_T_eff_st\<close> pipeline, mirroring
  \<open>Interval_Exec_Sound\<close>'s \<open>ivl_exec_prog\<close> exactly. The exported runtime API \<open>analyse\<close>
  (\<open>Example_Analysis_Dispatch\<close>, downstream in Examples) dispatches through a
  different, newer pipeline instead: the native D/G equation system (\<open>dg_gen_of\<close>,
  \<^theory>\<open>Voblint_Analysis.Exec_DG_Bridge\<close>), because that is what the \<open>Exec_Sign_DG_Run\<close> flagship
  example (\<open>dgEx_sol\<close>, downstream in Examples) already used before this API existed. Only the
  raw computation lives here --- \<open>analyse_sign_for\<close>'s soundness proof needs the
  \<open>unit_dg_exec_analysis\<close> locale (\<open>Run_Analysis_Sound\<close>, Formalization session), one session
  later than Analysis in the locked six-session chain, so that half cannot live in this file; it
  stays in \<open>Example_Sign_Codegen\<close> (downstream in Examples), which references these definitions
  with \<open>gs\<close>/\<open>p\<close> applied explicitly.
\<close>

definition analyse_sign_eqs_for ::
  "(vname \<Rightarrow> bool) \<Rightarrow> imp_prog \<Rightarrow>
     pp \<times> unit \<Rightarrow> (pp \<times> unit, unit, (sign exec_dg_st, sign exec_dg_st) dg_state) strategy_tree" where
  "analyse_sign_eqs_for gs p =
     dg_gen_of
       (unit_dg_spec_st_for gs (sign_tf_st_for gs) (sign_enter_st_for gs))
       (prog_cfg prog_main_name p) bot cinit_sign_st cinit_sign_st"

definition analyse_sign_for :: "(vname \<Rightarrow> bool) \<Rightarrow> imp_prog \<Rightarrow>
    (pp \<times> unit) set \<times> (pp \<times> unit + unit \<Rightarrow> (sign exec_dg_st, sign exec_dg_st) dg_state)" where
  "analyse_sign_for gs p =
     TD_side_always_join_Interp_solve (analyse_sign_eqs_for gs p) (cfg_exit (prog_cfg prog_main_name p), ())"

text \<open>
  \<open>analyse_sign_env_for\<close> reads the exit-answer/side-effect split \<open>dg_state\<close> keeps (\<open>Inl (v, ())\<close>
  for the local answer at \<open>v\<close>, \<open>Inr ()\<close> for the global side effect) the same way \<open>dgEx_inspect\<close>
  in \<open>Exec_Sign_DG_Run\<close> (downstream in Examples) does by hand.
\<close>

definition analyse_sign_env_for :: "(vname \<Rightarrow> bool) \<Rightarrow> imp_prog \<Rightarrow> pp \<Rightarrow> sign abs_state" where
  "analyse_sign_env_for gs p v =
     combine_abs gs
       (fun_of_exec_dg_st_for gs (locals (snd (analyse_sign_for gs p) (Inl (v, ())))))
       (fun_of_exec_dg_st_for gs (globs (snd (analyse_sign_for gs p) (Inr ()))))"

text \<open>
  Convenience instances at \<^const>\<open>declared_global\<close> \<open>p\<close>, matching \<open>analyse_interval\<close>'s shape.
\<close>

definition analyse_sign_eqs :: "imp_prog \<Rightarrow>
    pp \<times> unit \<Rightarrow> (pp \<times> unit, unit, (sign exec_dg_st, sign exec_dg_st) dg_state) strategy_tree" where
  "analyse_sign_eqs p = analyse_sign_eqs_for (declared_global p) p"

definition analyse_sign :: "imp_prog \<Rightarrow>
    (pp \<times> unit) set \<times> (pp \<times> unit + unit \<Rightarrow> (sign exec_dg_st, sign exec_dg_st) dg_state)" where
  "analyse_sign p = analyse_sign_for (declared_global p) p"

definition analyse_sign_env :: "imp_prog \<Rightarrow> pp \<Rightarrow> sign abs_state" where
  "analyse_sign_env p = analyse_sign_env_for (declared_global p) p"

section \<open>Visualisation convenience\<close>

text \<open>
  One-command annotated CFG rendering for the sign domain through the canonical
  context-expanded graph model.  It compiles the program, runs the solver, and
  adapts the unit context to the explicit presentation domain.

  Typical example-file use:

  @{text [display] "ML_val \<open>
    writeln (@{code sign_annotated_dot_prog_lit} ''main'' @{code my_prog})
  \<close>"}
\<close>


definition sign_graph_config ::
  "(vname \<Rightarrow> bool) \<Rightarrow> proc_table \<Rightarrow> pname list \<Rightarrow> pname \<Rightarrow> com \<Rightarrow>
    (unit, unit, sign abs_state, sign abs_state) analysis_graph_config" where
  "sign_graph_config gs \<Pi> ps mnm main = compiled_domain_graph_config gs \<Pi> ps mnm main (\<lambda>v. v = STop)"

text \<open>
  Proof-side only: confirms the executable top test \<^const>\<open>sign_graph_config\<close> is built
  from agrees with the semantic \<^const>\<open>is_top\<close> from \<^class>\<open>sound_domain\<close>. Not used in
  any exported definition, so it never reintroduces \<^class>\<open>sound_domain\<close>'s code
  dependency into \<^const>\<open>compiled_domain_graph_config\<close>.
\<close>
lemma sign_top_test_eq_is_top: "(\<lambda>v. v = STop) = (is_top :: sign \<Rightarrow> bool)"
  by (rule ext) (simp add: is_top_sign_correct top_sign_def)

definition sign_graph_solution ::
  "(vname \<Rightarrow> bool) \<Rightarrow> (pp + unit \<Rightarrow> sign resolved_st_q) \<Rightarrow> (pp \<times> unit + unit \<Rightarrow> sign abs_state)" where
  "sign_graph_solution gs sol z =
    (case z of Inl (p, ()) \<Rightarrow> fun_of_resolved_st_q_for gs (sol (Inl p))
     | Inr () \<Rightarrow> fun_of_resolved_st_q_for gs (sol (Inr ())) )"

definition sign_annotated_dot_lit ::
  "(vname \<Rightarrow> bool) \<Rightarrow> proc_table \<Rightarrow> pname list \<Rightarrow> pname \<Rightarrow> com \<Rightarrow> String.literal" where
  "sign_annotated_dot_lit gs \<Pi> ps mnm main =
    String.implode
      (let g = compile_prog \<Pi> ps mnm main;
           domain = contextual_graph_domain g (\<lambda>_. [()]) @ [Inr ()];
           sol = sign_graph_solution gs (sign_exec_raw gs \<Pi> ps mnm main)
       in contextual_analysis_dot (sign_graph_config gs \<Pi> ps mnm main) g domain sol)"

definition sign_annotated_dot_prog_lit :: "(vname \<Rightarrow> bool) \<Rightarrow> pname \<Rightarrow> imp_prog \<Rightarrow> String.literal" where
  "sign_annotated_dot_prog_lit gs mnm p =
     sign_annotated_dot_lit gs (prog_table p) (prog_procs p) mnm (prog_main p)"

end


