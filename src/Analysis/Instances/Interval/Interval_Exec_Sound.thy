theory Interval_Exec_Sound
  imports Ivl_Exec Interval_Side_Soundness Voblint_Core.Solver_Side_RG
          "TD.TD_side_upd_rule"
          "Voblint_VIMP.VIMP_Notation"
          "Voblint_CFG.Compile_Invariants"
          Analysis_GraphViz
begin

section \<open>Executable interval analysis: the computed result and its certified soundness\<close>

text \<open>
  High-level vocabulary for the executable analyzer, mirroring
  \<open>Sign_Exec_Sound\<close> at the interval domain:

    \<^item> \<open>ivl_exec_raw \<Pi> ps main\<close>  -- the raw solver solution (\<open>pp + unit => ivl resolved_st_q\<close>),
      code-generating, the thing @{command value} / \<open>eval\<close> evaluates;
    \<^item> \<open>ivl_exec gs \<Pi> ps main\<close>   -- the analyzer's computed abstract state at the
      program exit (an \<open>ivl abs_state\<close>), read back through \<open>fun_of_resolved_st_q_for gs\<close>;
    \<^item> \<open>ivl_exec_terminates \<Pi> ps main\<close> -- the single assumption: the vendored
      solver terminates on this program.

  \<open>ivl_exec_sound_collecting\<close> / \<open>ivl_exec_sound_collecting_at\<close> are the program-parametric
  soundness theorems; concrete examples only fix a program and instantiate them.
\<close>

definition ivl_exec_eqs ::
    "(vname \<Rightarrow> bool) \<Rightarrow> proc_table \<Rightarrow> pname list \<Rightarrow> pname \<Rightarrow> com \<Rightarrow> (pp, unit, ivl resolved_st_q) eqsT" where
  "ivl_exec_eqs gs \<Pi> ps mnm main =
     side_cfg_T_eff_st (compile_prog \<Pi> ps mnm main) (ivl_etf_st_for gs) bot cinit_ivl_st ()"

definition ivl_exec_raw ::
    "(vname \<Rightarrow> bool) \<Rightarrow> proc_table \<Rightarrow> pname list \<Rightarrow> pname \<Rightarrow> com \<Rightarrow> (pp + unit \<Rightarrow> ivl resolved_st_q)" where
  "ivl_exec_raw gs \<Pi> ps mnm main =
     snd (TD_side_always_join_Interp_solve (ivl_exec_eqs gs \<Pi> ps mnm main)
            (cfg_exit (compile_prog \<Pi> ps mnm main)))"

definition ivl_exec_at ::
    "(vname \<Rightarrow> bool) \<Rightarrow> proc_table \<Rightarrow> pname list \<Rightarrow> pname \<Rightarrow> com \<Rightarrow> pp \<Rightarrow> ivl abs_state" where
  "ivl_exec_at gs \<Pi> ps mnm main v =
     side_env (fun_of_resolved_st_q_for gs \<circ> ivl_exec_raw gs \<Pi> ps mnm main) v"

definition ivl_exec ::
    "(vname \<Rightarrow> bool) \<Rightarrow> proc_table \<Rightarrow> pname list \<Rightarrow> pname \<Rightarrow> com \<Rightarrow> ivl abs_state" where
  "ivl_exec gs \<Pi> ps mnm main = ivl_exec_at gs \<Pi> ps mnm main (cfg_exit (compile_prog \<Pi> ps mnm main))"

definition ivl_exec_terminates ::
    "(vname \<Rightarrow> bool) \<Rightarrow> proc_table \<Rightarrow> pname list \<Rightarrow> pname \<Rightarrow> com \<Rightarrow> bool" where
  "ivl_exec_terminates gs \<Pi> ps mnm main =
     TD_side_always_join_Interp.solve_dom TYPE(unit) TYPE(ivl resolved_st_q)
        (ivl_exec_eqs gs \<Pi> ps mnm main) (cfg_exit (compile_prog \<Pi> ps mnm main))"

text \<open>
  Discharging termination by execution, exactly as
  \<open>Sign_Exec_Sound\<close>'s \<open>sign_exec_terminates_via_solve_c\<close>:
  when the vendored side solver's executable
  @{const TD_side_always_join_Interp_solve_c} returns a result on a concrete
  program, that program lies in the solver's domain.
\<close>

lemma ivl_exec_terminates_via_solve_c:
  assumes "TD_side_always_join_Interp_solve_c (ivl_exec_eqs gs \<Pi> ps mnm main)
             (cfg_exit (compile_prog \<Pi> ps mnm main)) \<noteq> None"
  shows "ivl_exec_terminates gs \<Pi> ps mnm main"
  unfolding ivl_exec_terminates_def TD_side_always_join_Interp.term_equivalence
            TD_side_always_join_Interp.solve_c_dom_def
  using assms by simp

text \<open>
  Soundness at the state level: starting from any C-faithful initial store
  (globals zero, locals arbitrary), every store reaching the exit under the
  interprocedural collecting semantics is over-approximated by the computed
  result. Node-local: the query cone theorem \<open>side_collect_sound_in_eff_cone\<close>
  already bounds \<open>ltr_collect\<close> at any node \<open>v\<close> the solve call's query seed
  (here \<open>cfg_exit\<close>) can reach --- not only at the seed itself.
  \<open>ivl_exec_sound_collecting\<close> below is the \<open>v = cfg_exit g\<close> specialization,
  via \<open>cfg_reaches_refl\<close>. Same generic solver theorems as
  \<open>sign_exec_sound_collecting_at\<close>; only the domain-specific transfer facts
  (\<open>ivl_etf_st\<close>/\<open>ivl_etf\<close>/\<open>cinit_ivl_st\<close> and their commutation/cone/soundness
  lemmas) differ.
\<close>

theorem ivl_exec_sound_collecting_at:
  fixes mnm :: pname and v :: pp
  assumes solves: "ivl_exec_terminates gs \<Pi> ps mnm main"
    and reach_v: "cfg_reaches (compile_prog \<Pi> ps mnm main) v (cfg_exit (compile_prog \<Pi> ps mnm main))"
  shows "ltr_collect gs (compile_prog \<Pi> ps mnm main) (cinit_stores gs) v
         \<le> \<lbrakk>ivl_exec_at gs \<Pi> ps mnm main v\<rbrakk>"
proof -
  define g :: cfg where "g = compile_prog \<Pi> ps mnm main"
  define sol :: "pp set \<times> (pp + unit \<Rightarrow> ivl resolved_st_q)" where
    "sol = TD_side_always_join_Interp_solve (ivl_exec_eqs gs \<Pi> ps mnm main) (cfg_exit g)"
  define \<sigma> :: "pp + unit \<Rightarrow> ivl abs_state" where "\<sigma> = fun_of_resolved_st_q_for gs \<circ> snd sol"
  have fin: "finite (intra g)" unfolding g_def using compile_prog_finite by simp
  have finC: "finite (calls g)" unfolding g_def using compile_prog_finite by simp
  have wf: "wf_cfg g" unfolding g_def by (rule compile_prog_wf)
  have dom: "TD_side_always_join_Interp.solve_dom TYPE(unit) TYPE(ivl resolved_st_q)
               (ivl_exec_eqs gs \<Pi> ps mnm main) (cfg_exit g)"
    using solves unfolding ivl_exec_terminates_def g_def by simp
  have pp0: "part_post_solution (ivl_exec_eqs gs \<Pi> ps mnm main) (cfg_exit g) (snd sol) (fst sol)"
    using TD_side_always_join_Interp.partial_post_solution[OF dom, of "fst sol" "snd sol"]
    unfolding sol_def by simp
  have pp_st: "part_post_solution (side_cfg_T_eff_st g (ivl_etf_st_for gs) bot cinit_ivl_st ())
                 (cfg_exit g) (snd sol) (fst sol)"
    using pp0 by (simp add: ivl_exec_eqs_def g_def)
  have pp_eff: "part_post_solution
                  (side_cfg_T_eff gs g (ivl_etf gs) bot
                     (\<lambda>x. if gs x then Ivl (Fin 0) (Fin 0) else Ivl MinInf PlusInf) ())
                  (cfg_exit g) \<sigma> (fst sol)"
    using part_post_solution_st_to_abs_eff_unit_transfer
            [OF ivl_etf_edge_tree ivl_etf_combine_tree
                ivl_etf_st_for_edge_tree ivl_etf_st_for_combine_tree ivl_tf_st_for_commute
                ivl_etf_enter_tree ivl_etf_st_for_enter_tree ivl_enter_st_for_commute pp_st]
    by (simp add: \<sigma>_def fun_of_st_cinit_ivl_st_for bot_fun_def)
  have cone: "cone_compatible_etf gs (ivl_etf gs)" by (rule ivl_etf_cone_compatible)
  have srz: "\<And>z. side_rg (ivl_exec_eqs gs \<Pi> ps mnm main z)"
    unfolding ivl_exec_eqs_def
    by (rule side_rg_side_cfg_T_eff_st_unit
          [OF ivl_etf_st_for_exists_unit ivl_etf_st_for_enter_exists_unit ivl_etf_st_for_combine_tree])
  have solpair: "TD_side_always_join_Interp_solve (ivl_exec_eqs gs \<Pi> ps mnm main) (cfg_exit g)
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
  have entry_le: "(\<lambda>x. if gs x then Ivl (Fin 0) (Fin 0) else Ivl MinInf PlusInf)
                    \<le> side_env \<sigma> (cfg_entry g)"
    by (rule s0_le_side_env_entry_eff[OF pp_eff entry_in])
  have seed_cov: "cinit_stores gs
                    \<subseteq> \<lbrakk>\<lambda>x. if gs x then Ivl (Fin 0) (Fin 0) else Ivl MinInf PlusInf\<rbrakk>"
    unfolding cinit_stores_def gamma_state_def
    by auto
  have entry_cov: "cinit_stores gs \<le> \<lbrakk>side_env \<sigma> (cfg_entry g)\<rbrakk>"
    using seed_cov gamma_state_mono[OF entry_le] by (rule subset_trans)
  have reach_v': "cfg_reaches g v (cfg_exit g)"
    using reach_v unfolding g_def by simp
  have "ltr_collect gs g (cinit_stores gs) v
        \<le> \<lbrakk>side_env \<sigma> v\<rbrakk>"
    by (rule side_collect_sound_in_eff_cone
          [OF ivl_sound_etf pp_eff fin finC wf entry_cov cone inr reach_v'])
  then show ?thesis
    by (simp add: g_def \<sigma>_def sol_def ivl_exec_at_def ivl_exec_raw_def)
qed

corollary ivl_exec_sound_collecting:
  fixes mnm :: pname
  assumes solves: "ivl_exec_terminates gs \<Pi> ps mnm main"
  shows "ltr_collect gs (compile_prog \<Pi> ps mnm main) (cinit_stores gs) (cfg_exit (compile_prog \<Pi> ps mnm main))
         \<le> \<lbrakk>ivl_exec gs \<Pi> ps mnm main\<rbrakk>"
  unfolding ivl_exec_def
  by (rule ivl_exec_sound_collecting_at[OF solves cfg_reaches_refl])

section \<open>Whole-program convenience layer\<close>

text \<open>
  An @{type imp_prog} written with the \<open>\<lbrakk> \<dots> \<rbrakk>\<close> bracket already bundles the
  procedure table, procedure-name list, and main command. The wrappers below
  feed those three projections to the analyzer in one step, mirroring
  \<open>Sign_Exec_Sound\<close>'s \<open>sign_exec_prog_at\<close> family.
  \<^const>\<open>prog_cfg\<close> (\<^theory>\<open>Voblint_CFG.Compile_Invariants\<close>) is the shared,
  domain-independent instance of this same projection for the CFG itself, so
  it is imported rather than redefined here --- Sign uses the exact same
  constant, not an equivalent local copy.
\<close>

definition ivl_exec_prog_at :: "(vname \<Rightarrow> bool) \<Rightarrow> pname \<Rightarrow> imp_prog \<Rightarrow> pp \<Rightarrow> ivl abs_state" where
  "ivl_exec_prog_at gs mnm p v = ivl_exec_at gs (prog_table p) (prog_procs p) mnm (prog_main p) v"

definition ivl_exec_prog :: "(vname \<Rightarrow> bool) \<Rightarrow> pname \<Rightarrow> imp_prog \<Rightarrow> ivl abs_state" where
  "ivl_exec_prog gs mnm p = ivl_exec_prog_at gs mnm p (cfg_exit (prog_cfg mnm p))"

definition ivl_terminates_prog :: "(vname \<Rightarrow> bool) \<Rightarrow> pname \<Rightarrow> imp_prog \<Rightarrow> bool" where
  "ivl_terminates_prog gs mnm p = ivl_exec_terminates gs (prog_table p) (prog_procs p) mnm (prog_main p)"

lemma ivl_terminates_prog_via_solve_c:
  assumes "TD_side_always_join_Interp_solve_c
             (ivl_exec_eqs gs (prog_table p) (prog_procs p) mnm (prog_main p))
             (cfg_exit (compile_prog (prog_table p) (prog_procs p) mnm (prog_main p))) \<noteq> None"
  shows "ivl_terminates_prog gs mnm p"
  unfolding ivl_terminates_prog_def
  using assms by (rule ivl_exec_terminates_via_solve_c)

corollary ivl_exec_prog_sound_collecting_at:
  assumes "ivl_terminates_prog gs mnm p"
    and "cfg_reaches (prog_cfg mnm p) v (cfg_exit (prog_cfg mnm p))"
  shows "ltr_collect gs (prog_cfg mnm p) (cinit_stores gs) v
           \<le> \<lbrakk>ivl_exec_prog_at gs mnm p v\<rbrakk>"
  using assms unfolding ivl_terminates_prog_def prog_cfg_def ivl_exec_prog_at_def
  by (rule ivl_exec_sound_collecting_at)

corollary ivl_exec_prog_sound_collecting:
  assumes "ivl_terminates_prog gs mnm p"
  shows "ltr_collect gs (prog_cfg mnm p) (cinit_stores gs) (cfg_exit (prog_cfg mnm p))
           \<le> \<lbrakk>ivl_exec_prog gs mnm p\<rbrakk>"
  unfolding ivl_exec_prog_def
  by (rule ivl_exec_prog_sound_collecting_at[OF assms cfg_reaches_refl])

text \<open>
  \<open>analyse_interval_for\<close>/\<open>analyse_interval\<close> fix the main-procedure name to
  \<open>prog_main_name\<close>, matching the \<open>imp_prog\<close> bracket notation's convention:
  thin renames of \<open>ivl_exec_prog\<close>/\<open>ivl_terminates_prog\<close>, not a new proof, so
  callers coming from executable code generation reach the same generic
  collecting-soundness chain \<open>ivl_exec_prog_sound_collecting\<close> already gives.
\<close>

definition analyse_interval_for :: "(vname \<Rightarrow> bool) \<Rightarrow> imp_prog \<Rightarrow> ivl abs_state" where
  "analyse_interval_for gs p = ivl_exec_prog gs prog_main_name p"

definition analyse_interval :: "imp_prog \<Rightarrow> ivl abs_state" where
  "analyse_interval p = analyse_interval_for (declared_global p) p"

corollary analyse_interval_sound:
  assumes "ivl_terminates_prog (declared_global p) prog_main_name p"
  shows "ltr_collect (declared_global p) (prog_cfg prog_main_name p) (cinit_stores (declared_global p))
           (cfg_exit (prog_cfg prog_main_name p))
         \<le> \<lbrakk>analyse_interval p\<rbrakk>"
  unfolding analyse_interval_def analyse_interval_for_def
  by (rule ivl_exec_prog_sound_collecting[OF assms])

text \<open>
  \<open>analyse_interval_td\<close>/\<open>analyse_interval_td_for\<close> mirror \<open>analyse_interval\<close>
  but solve via @{const TD_side_warrowing_apinis_Interp_solve} instead of the
  always-join rule, following \<open>ivl_exec_raw\<close>/\<open>ivl_exec_at\<close>/\<open>ivl_exec_prog\<close>'s
  own shape.  A soundness theorem for this pipeline follows the same collecting chain
  \<open>ivl_exec_sound_collecting_at\<close> uses, with \<open>TD_side_always_join_solve_Inr_rg\<close> replaced by
  \<^theory>\<open>Voblint_Core.Solver_Side_RG\<close>'s \<open>TD_side_warrowing_apinis_solve_Inr_rg\<close>: the warrowing
  update rule reads back its own per-origin bookkeeping (@{const sup_over_origins}) rather than
  just joining, so that bridge lemma additionally needs \<open>bot \<nabla> bot = bot\<close>/\<open>bot \<Delta> bot = bot\<close> for
  the domain in play --- \<open>ivl_widen_bot_bot\<close>/\<open>ivl_narrow_bot_bot\<close>
  (\<^theory>\<open>Voblint_Analysis.Interval_Warrowing\<close>) discharge exactly that for \<open>ivl\<close>.
\<close>

definition analyse_interval_td_raw ::
    "(vname \<Rightarrow> bool) \<Rightarrow> proc_table \<Rightarrow> pname list \<Rightarrow> pname \<Rightarrow> com \<Rightarrow> (pp + unit \<Rightarrow> ivl resolved_st_q)" where
  "analyse_interval_td_raw gs Pi ps mnm main =
     snd (TD_side_warrowing_apinis_Interp_solve
            (ivl_exec_eqs gs Pi ps mnm main) (cfg_exit (compile_prog Pi ps mnm main)))"

definition analyse_interval_td_at ::
    "(vname \<Rightarrow> bool) \<Rightarrow> proc_table \<Rightarrow> pname list \<Rightarrow> pname \<Rightarrow> com \<Rightarrow> pp \<Rightarrow> ivl abs_state" where
  "analyse_interval_td_at gs Pi ps mnm main v =
     side_env (fun_of_resolved_st_q_for gs \<circ> analyse_interval_td_raw gs Pi ps mnm main) v"

definition analyse_interval_td_for :: "(vname \<Rightarrow> bool) \<Rightarrow> imp_prog \<Rightarrow> ivl abs_state" where
  "analyse_interval_td_for gs p =
     analyse_interval_td_at gs (prog_table p) (prog_procs p) prog_main_name (prog_main p)
       (cfg_exit (prog_cfg prog_main_name p))"

definition analyse_interval_td :: "imp_prog \<Rightarrow> ivl abs_state" where
  "analyse_interval_td p = analyse_interval_td_for (declared_global p) p"

text \<open>
  \<open>analyse_interval_td_terminates\<close> mirrors \<open>ivl_exec_terminates\<close>, one layer down from
  \<open>analyse_interval_td_raw\<close>/\<open>analyse_interval_td_at\<close> exactly as \<open>ivl_exec_terminates\<close> sits
  below \<open>ivl_exec_raw\<close>/\<open>ivl_exec_at\<close>.
\<close>

definition analyse_interval_td_terminates ::
    "(vname \<Rightarrow> bool) \<Rightarrow> proc_table \<Rightarrow> pname list \<Rightarrow> pname \<Rightarrow> com \<Rightarrow> bool" where
  "analyse_interval_td_terminates gs Pi ps mnm main =
     TD_side_warrowing_apinis_Interp.solve_dom TYPE(unit) TYPE(ivl resolved_st_q)
        (ivl_exec_eqs gs Pi ps mnm main) (cfg_exit (compile_prog Pi ps mnm main))"

lemma analyse_interval_td_terminates_via_solve_c:
  assumes "TD_side_warrowing_apinis_Interp_solve_c (ivl_exec_eqs gs Pi ps mnm main)
             (cfg_exit (compile_prog Pi ps mnm main)) \<noteq> None"
  shows "analyse_interval_td_terminates gs Pi ps mnm main"
  unfolding analyse_interval_td_terminates_def TD_side_warrowing_apinis_Interp.term_equivalence
            TD_side_warrowing_apinis_Interp.solve_c_dom_def
  using assms by simp

text \<open>
  \<open>analyse_interval_td_sound_collecting_at\<close> is \<open>ivl_exec_sound_collecting_at\<close>'s proof, with the
  always-join interpretation and its \<open>Inr\<close>-restriction lemma swapped for the warrowing ones ---
  every other step (the executable-to-abstract transport, the cone/entry lemmas, the collecting
  soundness endpoint itself) is already generic in which solver produced the \<open>part_post_solution\<close>
  witness.
\<close>

theorem analyse_interval_td_sound_collecting_at:
  fixes mnm :: pname and v :: pp
  assumes solves: "analyse_interval_td_terminates gs Pi ps mnm main"
    and reach_v: "cfg_reaches (compile_prog Pi ps mnm main) v (cfg_exit (compile_prog Pi ps mnm main))"
  shows "ltr_collect gs (compile_prog Pi ps mnm main) (cinit_stores gs) v
         \<le> \<lbrakk>analyse_interval_td_at gs Pi ps mnm main v\<rbrakk>"
proof -
  define g :: cfg where "g = compile_prog Pi ps mnm main"
  define sol :: "pp set \<times> (pp + unit \<Rightarrow> ivl resolved_st_q)" where
    "sol = TD_side_warrowing_apinis_Interp_solve (ivl_exec_eqs gs Pi ps mnm main) (cfg_exit g)"
  define sigma :: "pp + unit \<Rightarrow> ivl abs_state" where "sigma = fun_of_resolved_st_q_for gs \<circ> snd sol"
  have fin: "finite (intra g)" unfolding g_def using compile_prog_finite by simp
  have finC: "finite (calls g)" unfolding g_def using compile_prog_finite by simp
  have wf: "wf_cfg g" unfolding g_def by (rule compile_prog_wf)
  have dom: "TD_side_warrowing_apinis_Interp.solve_dom TYPE(unit) TYPE(ivl resolved_st_q)
               (ivl_exec_eqs gs Pi ps mnm main) (cfg_exit g)"
    using solves unfolding analyse_interval_td_terminates_def g_def by simp
  have pp0: "part_post_solution (ivl_exec_eqs gs Pi ps mnm main) (cfg_exit g) (snd sol) (fst sol)"
    using TD_side_warrowing_apinis_Interp.partial_post_solution[OF dom, of "fst sol" "snd sol"]
    unfolding sol_def by simp
  have pp_st: "part_post_solution (side_cfg_T_eff_st g (ivl_etf_st_for gs) bot cinit_ivl_st ())
                 (cfg_exit g) (snd sol) (fst sol)"
    using pp0 by (simp add: ivl_exec_eqs_def g_def)
  have pp_eff: "part_post_solution
                  (side_cfg_T_eff gs g (ivl_etf gs) bot
                     (\<lambda>x. if gs x then Ivl (Fin 0) (Fin 0) else Ivl MinInf PlusInf) ())
                  (cfg_exit g) sigma (fst sol)"
    using part_post_solution_st_to_abs_eff_unit_transfer
            [OF ivl_etf_edge_tree ivl_etf_combine_tree
                ivl_etf_st_for_edge_tree ivl_etf_st_for_combine_tree ivl_tf_st_for_commute
                ivl_etf_enter_tree ivl_etf_st_for_enter_tree ivl_enter_st_for_commute pp_st]
    by (simp add: sigma_def fun_of_st_cinit_ivl_st_for bot_fun_def)
  have cone: "cone_compatible_etf gs (ivl_etf gs)" by (rule ivl_etf_cone_compatible)
  have srz: "\<And>z. side_rg (ivl_exec_eqs gs Pi ps mnm main z)"
    unfolding ivl_exec_eqs_def
    by (rule side_rg_side_cfg_T_eff_st_unit
          [OF ivl_etf_st_for_exists_unit ivl_etf_st_for_enter_exists_unit ivl_etf_st_for_combine_tree])
  have solpair: "TD_side_warrowing_apinis_Interp_solve (ivl_exec_eqs gs Pi ps mnm main) (cfg_exit g)
                   = (fst sol, snd sol)"
    unfolding sol_def by simp
  have rg: "\<And>gg. snd sol (Inr gg) = restrict_global_resolved_q (snd sol (Inr gg))"
    by (rule TD_side_warrowing_apinis_solve_Inr_rg
          [OF dom srz ivl_widen_bot_bot ivl_narrow_bot_bot solpair])
  have inr: "inr_slot_locals_bot gs sigma"
    unfolding sigma_def
    using inr_slot_locals_bot_fun_of_resolved_st_q_for_restrict_global_abs rg by blast
  have reach: "cfg_reaches g (cfg_entry g) (cfg_exit g)"
    by (simp add: g_def compile_prog_entry_cfg_reaches_exit)
  have entry_in: "cfg_entry g \<in> fst sol"
    by (rule side_cone_in_vars_eff_cone[OF pp_eff fin finC wf cone reach])
  have entry_le: "(\<lambda>x. if gs x then Ivl (Fin 0) (Fin 0) else Ivl MinInf PlusInf)
                    \<le> side_env sigma (cfg_entry g)"
    by (rule s0_le_side_env_entry_eff[OF pp_eff entry_in])
  have seed_cov: "cinit_stores gs
                    \<subseteq> \<lbrakk>\<lambda>x. if gs x then Ivl (Fin 0) (Fin 0) else Ivl MinInf PlusInf\<rbrakk>"
    unfolding cinit_stores_def gamma_state_def
    by auto
  have entry_cov: "cinit_stores gs \<le> \<lbrakk>side_env sigma (cfg_entry g)\<rbrakk>"
    using seed_cov gamma_state_mono[OF entry_le] by (rule subset_trans)
  have reach_v': "cfg_reaches g v (cfg_exit g)"
    using reach_v unfolding g_def by simp
  have "ltr_collect gs g (cinit_stores gs) v
        \<le> \<lbrakk>side_env sigma v\<rbrakk>"
    by (rule side_collect_sound_in_eff_cone
          [OF ivl_sound_etf pp_eff fin finC wf entry_cov cone inr reach_v'])
  then show ?thesis
    by (simp add: g_def sigma_def sol_def analyse_interval_td_at_def analyse_interval_td_raw_def)
qed

corollary analyse_interval_td_sound_collecting:
  fixes mnm :: pname
  assumes solves: "analyse_interval_td_terminates gs Pi ps mnm main"
  shows "ltr_collect gs (compile_prog Pi ps mnm main) (cinit_stores gs)
           (cfg_exit (compile_prog Pi ps mnm main))
         \<le> \<lbrakk>analyse_interval_td_at gs Pi ps mnm main (cfg_exit (compile_prog Pi ps mnm main))\<rbrakk>"
  by (rule analyse_interval_td_sound_collecting_at[OF solves cfg_reaches_refl])

text \<open>
  The node-arbitrary prog-level corollary, mirroring \<open>ivl_exec_prog_sound_collecting_at\<close>:
  needed by a check-report layer, which classifies a check at whatever node it sits at, not only
  at \<open>cfg_exit\<close>.
\<close>

corollary analyse_interval_td_prog_sound_collecting_at:
  assumes "analyse_interval_td_terminates (declared_global p) (prog_table p) (prog_procs p)
             prog_main_name (prog_main p)"
    and "cfg_reaches (prog_cfg prog_main_name p) v (cfg_exit (prog_cfg prog_main_name p))"
  shows "ltr_collect (declared_global p) (prog_cfg prog_main_name p) (cinit_stores (declared_global p)) v
           \<le> \<lbrakk>analyse_interval_td_at (declared_global p) (prog_table p) (prog_procs p)
                prog_main_name (prog_main p) v\<rbrakk>"
  unfolding prog_cfg_def
  by (rule analyse_interval_td_sound_collecting_at[OF assms(1) assms(2)[unfolded prog_cfg_def]])

text \<open>
  Convenience instance at \<^const>\<open>declared_global\<close> \<open>p\<close>, matching \<open>analyse_interval_sound\<close>'s shape.
\<close>

corollary analyse_interval_td_sound:
  assumes "analyse_interval_td_terminates (declared_global p) (prog_table p) (prog_procs p)
             prog_main_name (prog_main p)"
  shows "ltr_collect (declared_global p) (prog_cfg prog_main_name p) (cinit_stores (declared_global p))
           (cfg_exit (prog_cfg prog_main_name p))
         \<le> \<lbrakk>analyse_interval_td p\<rbrakk>"
  unfolding analyse_interval_td_def analyse_interval_td_for_def prog_cfg_def
  by (rule analyse_interval_td_sound_collecting[OF assms[unfolded prog_cfg_def]])

section \<open>Visualisation convenience\<close>

text \<open>
  One-command annotated CFG rendering for the interval domain, mirroring
  \<open>Sign_Exec_Sound\<close>'s \<open>sign_graph_config\<close>/
  \<open>sign_annotated_dot_lit\<close>.

  Typical example-file use:

  @{text [display] "ML_val \<open>
    writeln (@{code ivl_annotated_dot_prog_lit} ''main'' @{code my_prog})
  \<close>"}
\<close>

definition ivl_graph_config ::
  "(vname \<Rightarrow> bool) \<Rightarrow> proc_table \<Rightarrow> pname list \<Rightarrow> pname \<Rightarrow> com \<Rightarrow>
    (unit, unit, ivl abs_state, ivl abs_state) analysis_graph_config" where
  "ivl_graph_config gs \<Pi> ps mnm main =
    \<lparr> local_of = id,
      route = (\<lambda>_ _ _ _. ()),
      show_context = (\<lambda>_. ''''),
      locals_for_pp = (\<lambda>p.
        let sc = compiled_procedure_scope gs \<Pi> ps mnm main (compile_prog \<Pi> ps mnm main) p
        in scope_formals sc @ scope_locals sc),
      return_slot_for_pp = (\<lambda>p.
        scope_return_slot (compiled_procedure_scope gs \<Pi> ps mnm main
          (compile_prog \<Pi> ps mnm main) p)),
      globals_to_show = compiled_global_vars gs (compile_prog \<Pi> ps mnm main),
      show_local = (\<lambda>_ _ vars s.
        map (\<lambda>x. String.explode x @ ''='' @ show_val (s x)) vars),
      format_return = (\<lambda>_ _ ret s.
        if s ret = ivl_top then [] else [''ret='' @ show_val (s ret)]),
      show_global = (\<lambda>_ vars s.
        map (\<lambda>x. String.explode x @ ''='' @ show_val (s x)) vars),
      show_global_key = (\<lambda>_. ''Globals''),
      is_shared_global = (\<lambda>_. True),
      show_internal_globals = False,
      owner_of = String.explode o compiled_owner_of \<Pi> ps mnm main,
      cluster_label = (\<lambda>owner _. owner),
      source_text = Some (pretty_string_of_program \<Pi> ps main []),
      node_annotation = (\<lambda>_. None)
    \<rparr>"

definition ivl_graph_solution ::
  "(vname \<Rightarrow> bool) \<Rightarrow> (pp + unit \<Rightarrow> ivl resolved_st_q) \<Rightarrow> (pp \<times> unit + unit \<Rightarrow> ivl abs_state)" where
  "ivl_graph_solution gs sol z =
    (case z of Inl (p, ()) \<Rightarrow> fun_of_resolved_st_q_for gs (sol (Inl p))
     | Inr () \<Rightarrow> fun_of_resolved_st_q_for gs (sol (Inr ())) )"

definition ivl_annotated_dot_lit ::
  "(vname \<Rightarrow> bool) \<Rightarrow> proc_table \<Rightarrow> pname list \<Rightarrow> pname \<Rightarrow> com \<Rightarrow> String.literal" where
  "ivl_annotated_dot_lit gs \<Pi> ps mnm main =
    String.implode
      (let g = compile_prog \<Pi> ps mnm main;
           domain = contextual_graph_domain g (\<lambda>_. [()]) @ [Inr ()];
           sol = ivl_graph_solution gs (ivl_exec_raw gs \<Pi> ps mnm main)
       in contextual_analysis_dot (ivl_graph_config gs \<Pi> ps mnm main) g domain sol)"

definition ivl_annotated_dot_prog_lit :: "(vname \<Rightarrow> bool) \<Rightarrow> pname \<Rightarrow> imp_prog \<Rightarrow> String.literal" where
  "ivl_annotated_dot_prog_lit gs mnm p =
     ivl_annotated_dot_lit gs (prog_table p) (prog_procs p) mnm (prog_main p)"

end
