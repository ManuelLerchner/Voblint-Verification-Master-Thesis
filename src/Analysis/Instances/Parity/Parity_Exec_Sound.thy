theory Parity_Exec_Sound
  imports Parity_Exec Parity_Side_Soundness Voblint_Core.Solver_Side_RG
          "TD.TD_side_upd_rule"
          "Voblint_VIMP.VIMP_Notation"
          "Voblint_CFG.Compile_Invariants"
begin

section \<open>Executable parity analysis: the computed result and its certified soundness\<close>

text \<open>

    \<^item> \<open>parity_exec_raw \<Pi> ps main\<close>  -- the raw solver solution
      (\<open>pp + unit \<Rightarrow> parity resolved_st_q\<close>), code-generating, the thing
      @{command value} / \<open>eval\<close> evaluates;
    \<^item> \<open>parity_exec_at gs \<Pi> ps main v\<close> -- the analyzer's computed abstract state
      at node \<open>v\<close> (a \<open>parity abs_state\<close>), read back through
      \<open>fun_of_resolved_st_q_for gs\<close>;
    \<^item> \<open>parity_exec_terminates \<Pi> ps main\<close> -- the single assumption: the
      vendored solver terminates on this program.

  No GraphViz whole-program renderer is added here: the worked check example
  renders through the domain-independent \<open>raw_cfg_dot_lit\<close> pipeline directly,
  exactly as Voblint_Examples.Example_Checks_Store_Only does for Sign,
  so no \<open>parity_graph_config\<close> is needed.
\<close>

definition parity_exec_eqs ::
    "(vname \<Rightarrow> bool) \<Rightarrow> proc_table \<Rightarrow> pname list \<Rightarrow> pname \<Rightarrow> com \<Rightarrow> (pp, unit, parity resolved_st_q) eqsT" where
  "parity_exec_eqs gs \<Pi> ps mnm main =
     side_cfg_T_eff_st (compile_prog \<Pi> ps mnm main) (parity_etf_st_for gs) bot cinit_parity_st ()"

definition parity_exec_raw ::
    "(vname \<Rightarrow> bool) \<Rightarrow> proc_table \<Rightarrow> pname list \<Rightarrow> pname \<Rightarrow> com \<Rightarrow> (pp + unit \<Rightarrow> parity resolved_st_q)" where
  "parity_exec_raw gs \<Pi> ps mnm main =
     snd (TD_side_always_join_Interp_solve (parity_exec_eqs gs \<Pi> ps mnm main)
            (cfg_exit (compile_prog \<Pi> ps mnm main)))"

definition parity_exec_at ::
    "(vname \<Rightarrow> bool) \<Rightarrow> proc_table \<Rightarrow> pname list \<Rightarrow> pname \<Rightarrow> com \<Rightarrow> pp \<Rightarrow> parity abs_state" where
  "parity_exec_at gs \<Pi> ps mnm main v =
     side_env (fun_of_resolved_st_q_for gs \<circ> parity_exec_raw gs \<Pi> ps mnm main) v"

definition parity_exec ::
    "(vname \<Rightarrow> bool) \<Rightarrow> proc_table \<Rightarrow> pname list \<Rightarrow> pname \<Rightarrow> com \<Rightarrow> parity abs_state" where
  "parity_exec gs \<Pi> ps mnm main = parity_exec_at gs \<Pi> ps mnm main (cfg_exit (compile_prog \<Pi> ps mnm main))"

definition parity_exec_terminates ::
    "(vname \<Rightarrow> bool) \<Rightarrow> proc_table \<Rightarrow> pname list \<Rightarrow> pname \<Rightarrow> com \<Rightarrow> bool" where
  "parity_exec_terminates gs \<Pi> ps mnm main =
     TD_side_always_join_Interp.solve_dom TYPE(unit) TYPE(parity resolved_st_q)
        (parity_exec_eqs gs \<Pi> ps mnm main) (cfg_exit (compile_prog \<Pi> ps mnm main))"

text \<open>
  Discharging termination by execution, exactly as \<open>sign_exec_terminates_via_solve_c\<close>/
  \<open>ivl_exec_terminates_via_solve_c\<close>: when the vendored side solver's
  executable @{const TD_side_always_join_Interp_solve_c} returns a result on a
  concrete program, that program lies in the solver's domain.
\<close>

lemma parity_exec_terminates_via_solve_c:
  assumes "TD_side_always_join_Interp_solve_c (parity_exec_eqs gs \<Pi> ps mnm main)
             (cfg_exit (compile_prog \<Pi> ps mnm main)) \<noteq> None"
  shows "parity_exec_terminates gs \<Pi> ps mnm main"
  unfolding parity_exec_terminates_def TD_side_always_join_Interp.term_equivalence
            TD_side_always_join_Interp.solve_c_dom_def
  using assms by simp

text \<open>
  Soundness at the state level, node-local: the query cone theorem
  \<open>side_collect_sound_in_eff_cone\<close> bounds \<open>ltr_collect\<close> at any node \<open>v\<close> the
  solve call's query seed (here \<open>cfg_exit\<close>) can reach --- not only at the
  seed itself. Same generic solver theorems as \<open>sign_exec_sound_collecting_at\<close>/
  \<open>ivl_exec_sound_collecting_at\<close>; only the domain-specific transfer facts
  (\<open>parity_etf_st\<close>/\<open>parity_etf\<close>/\<open>cinit_parity_st\<close> and their
  commutation/cone/soundness lemmas) differ.
\<close>

theorem parity_exec_sound_collecting_at:
  fixes mnm :: pname and v :: pp
  assumes solves: "parity_exec_terminates gs \<Pi> ps mnm main"
    and reach_v: "cfg_reaches (compile_prog \<Pi> ps mnm main) v (cfg_exit (compile_prog \<Pi> ps mnm main))"
  shows "ltr_collect gs (compile_prog \<Pi> ps mnm main) (cinit_stores gs) v
         \<le> \<lbrakk>parity_exec_at gs \<Pi> ps mnm main v\<rbrakk>"
proof -
  define g :: cfg where "g = compile_prog \<Pi> ps mnm main"
  define sol :: "pp set \<times> (pp + unit \<Rightarrow> parity resolved_st_q)" where
    "sol = TD_side_always_join_Interp_solve (parity_exec_eqs gs \<Pi> ps mnm main) (cfg_exit g)"
  define \<sigma> :: "pp + unit \<Rightarrow> parity abs_state" where "\<sigma> = fun_of_resolved_st_q_for gs \<circ> snd sol"
  have fin: "finite (intra g)" unfolding g_def using compile_prog_finite by simp
  have finC: "finite (calls g)" unfolding g_def using compile_prog_finite by simp
  have wf: "wf_cfg g" unfolding g_def by (rule compile_prog_wf)
  have dom: "TD_side_always_join_Interp.solve_dom TYPE(unit) TYPE(parity resolved_st_q)
               (parity_exec_eqs gs \<Pi> ps mnm main) (cfg_exit g)"
    using solves unfolding parity_exec_terminates_def g_def by simp
  have pp0: "part_post_solution (parity_exec_eqs gs \<Pi> ps mnm main) (cfg_exit g) (snd sol) (fst sol)"
    using TD_side_always_join_Interp.partial_post_solution[OF dom, of "fst sol" "snd sol"]
    unfolding sol_def by simp
  have pp_st: "part_post_solution (side_cfg_T_eff_st g (parity_etf_st_for gs) bot cinit_parity_st ())
                 (cfg_exit g) (snd sol) (fst sol)"
    using pp0 by (simp add: parity_exec_eqs_def g_def)
  have pp_eff: "part_post_solution
                  (side_cfg_T_eff gs g (parity_etf gs) bot
                     (\<lambda>x. if gs x then PEven else PTop) ())
                  (cfg_exit g) \<sigma> (fst sol)"
    using part_post_solution_st_to_abs_eff_unit_transfer
            [OF parity_etf_edge_tree parity_etf_combine_tree
                parity_etf_st_for_edge_tree parity_etf_st_for_combine_tree parity_tf_st_for_commute
                parity_etf_enter_tree parity_etf_st_for_enter_tree parity_enter_st_for_commute pp_st]
    by (simp add: \<sigma>_def fun_of_st_cinit_parity_st_for bot_fun_def)
  have cone: "cone_compatible_etf gs (parity_etf gs)" by (rule parity_etf_cone_compatible)
  have srz: "\<And>z. side_rg (parity_exec_eqs gs \<Pi> ps mnm main z)"
    unfolding parity_exec_eqs_def
    by (rule side_rg_side_cfg_T_eff_st_unit
          [OF parity_etf_st_for_exists_unit parity_etf_st_for_enter_exists_unit parity_etf_st_for_combine_tree])
  have solpair: "TD_side_always_join_Interp_solve (parity_exec_eqs gs \<Pi> ps mnm main) (cfg_exit g)
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
  have entry_le: "(\<lambda>x. if gs x then PEven else PTop) \<le> side_env \<sigma> (cfg_entry g)"
    by (rule s0_le_side_env_entry_eff[OF pp_eff entry_in])
  have seed_cov: "cinit_stores gs \<subseteq> \<lbrakk>\<lambda>x. if gs x then PEven else PTop\<rbrakk>"
    unfolding cinit_stores_def gamma_state_def
    by auto
  have entry_cov: "cinit_stores gs \<le> \<lbrakk>side_env \<sigma> (cfg_entry g)\<rbrakk>"
    using seed_cov gamma_state_mono[OF entry_le] by (rule subset_trans)
  have reach_v': "cfg_reaches g v (cfg_exit g)"
    using reach_v unfolding g_def by simp
  have "ltr_collect gs g (cinit_stores gs) v
        \<le> \<lbrakk>side_env \<sigma> v\<rbrakk>"
    by (rule side_collect_sound_in_eff_cone
          [OF parity_sound_etf pp_eff fin finC wf entry_cov cone inr reach_v'])
  then show ?thesis
    by (simp add: g_def \<sigma>_def sol_def parity_exec_at_def parity_exec_raw_def)
qed

corollary parity_exec_sound_collecting:
  fixes mnm :: pname
  assumes solves: "parity_exec_terminates gs \<Pi> ps mnm main"
  shows "ltr_collect gs (compile_prog \<Pi> ps mnm main) (cinit_stores gs) (cfg_exit (compile_prog \<Pi> ps mnm main))
         \<le> \<lbrakk>parity_exec gs \<Pi> ps mnm main\<rbrakk>"
  unfolding parity_exec_def
  by (rule parity_exec_sound_collecting_at[OF solves cfg_reaches_refl])

section \<open>Whole-program convenience layer\<close>

text \<open>
  An @{type imp_prog} written with the \<open>\<lbrakk> \<dots> \<rbrakk>\<close> bracket already bundles the
  procedure table, procedure-name list, and main command. The wrappers below
  feed those three projections to the analyzer in one step, mirroring
  \<open>Sign_Exec_Sound\<close>/\<open>Interval_Exec_Sound\<close>'s \<open>*_exec_prog_at\<close> family.
  \<^const>\<open>prog_cfg\<close> (\<^theory>\<open>Voblint_CFG.Compile_Invariants\<close>) is the shared,
  domain-independent instance of this same projection for the CFG itself, so
  it is imported rather than redefined here --- Sign and Interval use the
  exact same constant, not equivalent local copies.
\<close>

definition parity_exec_prog_at :: "(vname \<Rightarrow> bool) \<Rightarrow> pname \<Rightarrow> imp_prog \<Rightarrow> pp \<Rightarrow> parity abs_state" where
  "parity_exec_prog_at gs mnm p v = parity_exec_at gs (prog_table p) (prog_procs p) mnm (prog_main p) v"

definition parity_exec_prog :: "(vname \<Rightarrow> bool) \<Rightarrow> pname \<Rightarrow> imp_prog \<Rightarrow> parity abs_state" where
  "parity_exec_prog gs mnm p = parity_exec_prog_at gs mnm p (cfg_exit (prog_cfg mnm p))"

definition parity_terminates_prog :: "(vname \<Rightarrow> bool) \<Rightarrow> pname \<Rightarrow> imp_prog \<Rightarrow> bool" where
  "parity_terminates_prog gs mnm p = parity_exec_terminates gs (prog_table p) (prog_procs p) mnm (prog_main p)"

lemma parity_terminates_prog_via_solve_c:
  assumes "TD_side_always_join_Interp_solve_c
             (parity_exec_eqs gs (prog_table p) (prog_procs p) mnm (prog_main p))
             (cfg_exit (compile_prog (prog_table p) (prog_procs p) mnm (prog_main p))) \<noteq> None"
  shows "parity_terminates_prog gs mnm p"
  unfolding parity_terminates_prog_def
  using assms by (rule parity_exec_terminates_via_solve_c)

corollary parity_exec_prog_sound_collecting_at:
  assumes "parity_terminates_prog gs mnm p"
    and "cfg_reaches (prog_cfg mnm p) v (cfg_exit (prog_cfg mnm p))"
  shows "ltr_collect gs (prog_cfg mnm p) (cinit_stores gs) v
           \<le> \<lbrakk>parity_exec_prog_at gs mnm p v\<rbrakk>"
  using assms unfolding parity_terminates_prog_def prog_cfg_def parity_exec_prog_at_def
  by (rule parity_exec_sound_collecting_at)

corollary parity_exec_prog_sound_collecting:
  assumes "parity_terminates_prog gs mnm p"
  shows "ltr_collect gs (prog_cfg mnm p) (cinit_stores gs) (cfg_exit (prog_cfg mnm p))
           \<le> \<lbrakk>parity_exec_prog gs mnm p\<rbrakk>"
  unfolding parity_exec_prog_def
  by (rule parity_exec_prog_sound_collecting_at[OF assms cfg_reaches_refl])

end
