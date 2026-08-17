theory Interval_Exec_Sound
  imports Ivl_Exec Interval_Side_Soundness Voblint_Core.Solver_Side_RG
          "TD.TD_side_upd_rule"
          "Voblint_VIMP.VIMP_Notation"
          "Voblint_CFG.Compile_Invariants"
          Analysis_GraphViz
          "Voblint_Analysis.Exec_DG_Bridge"
          "Voblint_Analysis.DG_Base_Exec"
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

text \<open>
  Every definition here is generic in \<open>is_bot_pred\<close>, the executable
  witness-bottom test \<^const>\<open>unit_edge_tree_st\<close>/\<^const>\<open>unit_combine_tree_st\<close>
  need (@{theory Voblint_Core.Exec_Bridge}): at this \<open>(\<Pi>, ps, mnm, main)\<close>
  layer there is no @{type imp_prog} yet to read a declared-global list off
  of. The \<open>prog_at\<close> family below, which does have one, instantiates
  \<open>is_bot_pred\<close> to \<^const>\<open>resolved_st_q_is_bot_for\<close> at that program's own
  \<^const>\<open>declared_global_vars\<close> and closes the \<open>exact\<close> obligation with
  @{thm resolved_st_q_is_bot_for_iff}, so its own signature stays exactly
  what it was before this parameter existed -- mirroring
  \<open>Sign_Exec_Sound\<close>'s \<open>sign_exec_eqs\<close> family.
\<close>

definition ivl_exec_eqs ::
    "(ivl resolved_st_q \<Rightarrow> bool) \<Rightarrow> (vname \<Rightarrow> bool) \<Rightarrow> proc_table \<Rightarrow> pname list \<Rightarrow> pname \<Rightarrow> com
     \<Rightarrow> (pp, unit, ivl resolved_st_q lifted) eqsT" where
  "ivl_exec_eqs is_bot_pred gs \<Pi> ps mnm main =
     side_cfg_T_eff_st_buffered (compile_prog \<Pi> ps mnm main)
       (ivl_etf_st_contribution_for is_bot_pred gs) bot cinit_ivl_st ()"

definition ivl_exec_raw ::
    "(ivl resolved_st_q \<Rightarrow> bool) \<Rightarrow> (vname \<Rightarrow> bool) \<Rightarrow> proc_table \<Rightarrow> pname list \<Rightarrow> pname \<Rightarrow> com
     \<Rightarrow> (pp + unit \<Rightarrow> ivl resolved_st_q lifted)" where
  "ivl_exec_raw is_bot_pred gs \<Pi> ps mnm main =
     snd (TD_side_always_join_Interp_solve (ivl_exec_eqs is_bot_pred gs \<Pi> ps mnm main)
            (cfg_exit (compile_prog \<Pi> ps mnm main)))"

definition ivl_exec_at ::
    "(ivl resolved_st_q \<Rightarrow> bool) \<Rightarrow> (vname \<Rightarrow> bool) \<Rightarrow> proc_table \<Rightarrow> pname list \<Rightarrow> pname \<Rightarrow> com \<Rightarrow> pp
     \<Rightarrow> ivl abs_state lifted" where
  "ivl_exec_at is_bot_pred gs \<Pi> ps mnm main v =
     side_env_lift (map_lift (fun_of_resolved_st_q_for gs) \<circ> ivl_exec_raw is_bot_pred gs \<Pi> ps mnm main) v"

text \<open>
  Same finite readback swap as \<open>Interval_Checks\<close>'s \<open>interval_check_report_code\<close>:
  \<open>side_env_lift\<close> materializes the full \<open>vname \<Rightarrow> ivl\<close> function via pointwise \<open>\<squnion>\<close>,
  not executable over the infinite @{typ vname}. \<open>side_env_lift_st\<close> computes the
  same value straight from the two finite \<open>resolved_st_q\<close> slots.
\<close>

declare ivl_exec_at_def [code del]

lemma ivl_exec_at_code [code]:
  "ivl_exec_at is_bot_pred gs \<Pi> ps mnm main v =
     side_env_lift_st gs
       (ivl_exec_raw is_bot_pred gs \<Pi> ps mnm main (Inl v))
       (ivl_exec_raw is_bot_pred gs \<Pi> ps mnm main (Inr ()))"
  unfolding ivl_exec_at_def side_env_lift_st_eq_side_env_lift
  by (rule refl)

definition ivl_exec ::
    "(ivl resolved_st_q \<Rightarrow> bool) \<Rightarrow> (vname \<Rightarrow> bool) \<Rightarrow> proc_table \<Rightarrow> pname list \<Rightarrow> pname \<Rightarrow> com
     \<Rightarrow> ivl abs_state lifted" where
  "ivl_exec is_bot_pred gs \<Pi> ps mnm main = ivl_exec_at is_bot_pred gs \<Pi> ps mnm main (cfg_exit (compile_prog \<Pi> ps mnm main))"

definition ivl_exec_terminates ::
    "(ivl resolved_st_q \<Rightarrow> bool) \<Rightarrow> (vname \<Rightarrow> bool) \<Rightarrow> proc_table \<Rightarrow> pname list \<Rightarrow> pname \<Rightarrow> com \<Rightarrow> bool" where
  "ivl_exec_terminates is_bot_pred gs \<Pi> ps mnm main =
     TD_side_always_join_Interp.solve_dom TYPE(unit) TYPE(ivl resolved_st_q lifted)
        (ivl_exec_eqs is_bot_pred gs \<Pi> ps mnm main) (cfg_exit (compile_prog \<Pi> ps mnm main))"

text \<open>
  Discharging termination by execution, exactly as
  \<open>Sign_Exec_Sound\<close>'s \<open>sign_exec_terminates_via_solve_c\<close>:
  when the vendored side solver's executable
  @{const TD_side_always_join_Interp_solve_c} returns a result on a concrete
  program, that program lies in the solver's domain.
\<close>

lemma ivl_exec_terminates_via_solve_c:
  assumes "TD_side_always_join_Interp_solve_c (ivl_exec_eqs is_bot_pred gs \<Pi> ps mnm main)
             (cfg_exit (compile_prog \<Pi> ps mnm main)) \<noteq> None"
  shows "ivl_exec_terminates is_bot_pred gs \<Pi> ps mnm main"
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
  assumes solves: "ivl_exec_terminates is_bot_pred gs \<Pi> ps mnm main"
    and exact: "\<And>s. is_bot_pred s = is_bot_state (fun_of_resolved_st_q_for gs s)"
    and reach_v: "cfg_reaches (compile_prog \<Pi> ps mnm main) v (cfg_exit (compile_prog \<Pi> ps mnm main))"
  shows "ltr_collect gs (compile_prog \<Pi> ps mnm main) (cinit_stores gs) v
         \<le> gamma_state_lift (ivl_exec_at is_bot_pred gs \<Pi> ps mnm main v)"
proof -
  define g :: cfg where "g = compile_prog \<Pi> ps mnm main"
  define sol :: "pp set \<times> (pp + unit \<Rightarrow> ivl resolved_st_q lifted)" where
    "sol = TD_side_always_join_Interp_solve (ivl_exec_eqs is_bot_pred gs \<Pi> ps mnm main) (cfg_exit g)"
  define \<sigma> :: "pp + unit \<Rightarrow> ivl abs_state lifted" where
    "\<sigma> = map_lift (fun_of_resolved_st_q_for gs) \<circ> snd sol"
  have fin: "finite (intra g)" unfolding g_def using compile_prog_finite by simp
  have finC: "finite (calls g)" unfolding g_def using compile_prog_finite by simp
  have wf: "wf_cfg g" unfolding g_def by (rule compile_prog_wf)
  have dom: "TD_side_always_join_Interp.solve_dom TYPE(unit) TYPE(ivl resolved_st_q lifted)
               (ivl_exec_eqs is_bot_pred gs \<Pi> ps mnm main) (cfg_exit g)"
    using solves unfolding ivl_exec_terminates_def g_def by simp
  have pp0: "part_post_solution (ivl_exec_eqs is_bot_pred gs \<Pi> ps mnm main) (cfg_exit g) (snd sol) (fst sol)"
    using TD_side_always_join_Interp.partial_post_solution[OF dom, of "fst sol" "snd sol"]
    unfolding sol_def by simp
  have pp_st: "part_post_solution (side_cfg_T_eff_st g (ivl_etf_st_for is_bot_pred gs) bot cinit_ivl_st ())
                 (cfg_exit g) (snd sol) (fst sol)"
    using pp0
    unfolding ivl_exec_eqs_def g_def side_cfg_T_eff_st_buffered_def side_cfg_T_eff_st_def
              dep_def dep\<^sub>L_def
    by (simp add: ivl_buffered_correspondence ivl_buffered_dep_aux ivl_buffered_sides_full)
  have pp_eff: "part_post_solution
                  (side_cfg_T_eff gs g (ivl_etf gs) bot
                     (\<lambda>x. if gs x then Ivl (Fin 0) (Fin 0) else Ivl MinInf PlusInf) ())
                  (cfg_exit g) \<sigma> (fst sol)"
    using part_post_solution_st_to_abs_eff_unit_transfer
            [OF ivl_etf_edge_tree ivl_etf_combine_tree
                ivl_etf_st_for_edge_tree ivl_etf_st_for_combine_tree ivl_tf_st_for_commute
                ivl_etf_enter_tree ivl_etf_st_for_enter_tree ivl_enter_st_for_commute
                exact pp_st]
    by (simp add: \<sigma>_def fun_of_st_cinit_ivl_st_for bot_fun_def)
  have cone: "cone_compatible_etf gs (ivl_etf gs)" by (rule ivl_etf_cone_compatible)
  have srz: "\<And>z. side_rg (ivl_exec_eqs is_bot_pred gs \<Pi> ps mnm main z)"
    unfolding ivl_exec_eqs_def side_cfg_T_eff_st_buffered_def ivl_etf_st_contribution_for_def
    by (rule side_rg_unit_etf_st_contribution_of_transfer[OF ivl_tf_st_for_reduces])
  have solpair: "TD_side_always_join_Interp_solve (ivl_exec_eqs is_bot_pred gs \<Pi> ps mnm main) (cfg_exit g)
                   = (fst sol, snd sol)"
    unfolding sol_def by simp
  have rg: "\<And>gg. snd sol (Inr gg) = map_lift restrict_global_resolved_q (snd sol (Inr gg))"
    by (rule TD_side_always_join_solve_Inr_rg[OF dom srz solpair])
  have inr: "inr_slot_locals_bot gs \<sigma>"
    unfolding \<sigma>_def
    using inr_slot_locals_bot_fun_of_resolved_st_q_for_restrict_global_abs rg by blast
  have reach: "cfg_reaches g (cfg_entry g) (cfg_exit g)"
    by (simp add: g_def compile_prog_entry_cfg_reaches_exit)
  have entry_in: "cfg_entry g \<in> fst sol"
    by (rule side_cone_in_vars_eff_cone[OF pp_eff fin finC wf cone reach])
  have entry_le: "Lifted (\<lambda>x. if gs x then Ivl (Fin 0) (Fin 0) else Ivl MinInf PlusInf)
                    \<le> side_env_lift \<sigma> (cfg_entry g)"
    by (rule s0_le_side_env_entry_eff[OF pp_eff entry_in])
  have seed_cov: "cinit_stores gs
                    \<subseteq> \<lbrakk>\<lambda>x. if gs x then Ivl (Fin 0) (Fin 0) else Ivl MinInf PlusInf\<rbrakk>"
    unfolding cinit_stores_def gamma_state_def
    by auto
  have entry_le': "\<lbrakk>\<lambda>x. if gs x then Ivl (Fin 0) (Fin 0) else Ivl MinInf PlusInf\<rbrakk>
                     \<subseteq> gamma_state_lift (side_env_lift \<sigma> (cfg_entry g))"
    using gamma_lift_mono[OF gamma_state_mono entry_le] by simp
  have entry_cov: "cinit_stores gs \<le> gamma_state_lift (side_env_lift \<sigma> (cfg_entry g))"
    using seed_cov entry_le' by (rule subset_trans)
  have reach_v': "cfg_reaches g v (cfg_exit g)"
    using reach_v unfolding g_def by simp
  have "ltr_collect gs g (cinit_stores gs) v
        \<le> gamma_state_lift (side_env_lift \<sigma> v)"
    by (rule side_collect_sound_in_eff_cone
          [OF ivl_sound_etf pp_eff fin finC wf entry_cov cone inr reach_v'])
  then show ?thesis
    by (simp add: g_def \<sigma>_def sol_def ivl_exec_at_def ivl_exec_raw_def)
qed

corollary ivl_exec_sound_collecting:
  fixes mnm :: pname
  assumes solves: "ivl_exec_terminates is_bot_pred gs \<Pi> ps mnm main"
    and exact: "\<And>s. is_bot_pred s = is_bot_state (fun_of_resolved_st_q_for gs s)"
  shows "ltr_collect gs (compile_prog \<Pi> ps mnm main) (cinit_stores gs) (cfg_exit (compile_prog \<Pi> ps mnm main))
         \<le> gamma_state_lift (ivl_exec is_bot_pred gs \<Pi> ps mnm main)"
  unfolding ivl_exec_def
  by (rule ivl_exec_sound_collecting_at[OF solves exact cfg_reaches_refl])

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

  This is where a concrete @{type imp_prog} finally exists, so \<open>is_bot_pred\<close>
  is fixed here to \<^const>\<open>resolved_st_q_is_bot_for\<close> at \<open>p\<close>'s own
  \<^const>\<open>declared_global_vars\<close> -- executable, and exact for
  @{const is_bot_state} by @{thm resolved_st_q_is_bot_for_iff}
  (@{thm declared_global_iff}) -- rather than staying a parameter, so every
  signature below is unchanged from before \<open>is_bot_pred\<close> existed.
\<close>

definition ivl_exec_prog_at :: "(vname \<Rightarrow> bool) \<Rightarrow> pname \<Rightarrow> imp_prog \<Rightarrow> pp \<Rightarrow> ivl abs_state lifted" where
  "ivl_exec_prog_at gs mnm p v =
     ivl_exec_at (resolved_st_q_is_bot_for (declared_global_vars p)) gs
       (prog_table p) (prog_procs p) mnm (prog_main p) v"

definition ivl_exec_prog :: "(vname \<Rightarrow> bool) \<Rightarrow> pname \<Rightarrow> imp_prog \<Rightarrow> ivl abs_state lifted" where
  "ivl_exec_prog gs mnm p = ivl_exec_prog_at gs mnm p (cfg_exit (prog_cfg mnm p))"

definition ivl_terminates_prog :: "(vname \<Rightarrow> bool) \<Rightarrow> pname \<Rightarrow> imp_prog \<Rightarrow> bool" where
  "ivl_terminates_prog gs mnm p =
     ivl_exec_terminates (resolved_st_q_is_bot_for (declared_global_vars p)) gs
       (prog_table p) (prog_procs p) mnm (prog_main p)"

lemma ivl_terminates_prog_via_solve_c:
  assumes "TD_side_always_join_Interp_solve_c
             (ivl_exec_eqs (resolved_st_q_is_bot_for (declared_global_vars p)) gs
                (prog_table p) (prog_procs p) mnm (prog_main p))
             (cfg_exit (compile_prog (prog_table p) (prog_procs p) mnm (prog_main p))) \<noteq> None"
  shows "ivl_terminates_prog gs mnm p"
  unfolding ivl_terminates_prog_def
  using assms by (rule ivl_exec_terminates_via_solve_c)

text \<open>
  The exactness of \<^const>\<open>resolved_st_q_is_bot_for\<close> baked into
  \<^const>\<open>ivl_exec_prog_at\<close> needs \<open>gs\<close> to actually be the classifier
  \<^const>\<open>declared_global_vars\<close> \<open>p\<close> lists -- true of every real caller (\<open>gs\<close> is
  always some program's own \<^const>\<open>declared_global\<close>), but not a fact the
  generic \<open>gs\<close>/\<open>p\<close> signature enforces on its own, so it becomes an explicit
  hypothesis here.
\<close>

corollary ivl_exec_prog_sound_collecting_at:
  assumes gs_eq: "gs = declared_global p"
    and terminates: "ivl_terminates_prog gs mnm p"
    and reach: "cfg_reaches (prog_cfg mnm p) v (cfg_exit (prog_cfg mnm p))"
  shows "ltr_collect gs (prog_cfg mnm p) (cinit_stores gs) v
           \<le> gamma_state_lift (ivl_exec_prog_at gs mnm p v)"
proof -
  have exact: "\<And>s. resolved_st_q_is_bot_for (declared_global_vars p) s = is_bot_state (fun_of_resolved_st_q_for gs s)"
    unfolding gs_eq by (rule resolved_st_q_is_bot_for_iff[OF declared_global_iff])
  show ?thesis
    using terminates reach exact
    unfolding ivl_terminates_prog_def prog_cfg_def ivl_exec_prog_at_def
    using ivl_exec_sound_collecting_at by blast
qed

corollary ivl_exec_prog_sound_collecting:
  assumes gs_eq: "gs = declared_global p"
    and terminates: "ivl_terminates_prog gs mnm p"
  shows "ltr_collect gs (prog_cfg mnm p) (cinit_stores gs) (cfg_exit (prog_cfg mnm p))
           \<le> gamma_state_lift (ivl_exec_prog gs mnm p)"
  unfolding ivl_exec_prog_def
  by (rule ivl_exec_prog_sound_collecting_at[OF gs_eq terminates cfg_reaches_refl])

text \<open>
  \<open>analyse_interval_for\<close>/\<open>analyse_interval\<close> fix the main-procedure name to
  \<open>prog_main_name\<close>, matching the \<open>imp_prog\<close> bracket notation's convention:
  thin renames of \<open>ivl_exec_prog\<close>/\<open>ivl_terminates_prog\<close>, not a new proof, so
  callers coming from executable code generation reach the same generic
  collecting-soundness chain \<open>ivl_exec_prog_sound_collecting\<close> already gives.
\<close>

definition analyse_interval_for :: "(vname \<Rightarrow> bool) \<Rightarrow> imp_prog \<Rightarrow> ivl abs_state lifted" where
  "analyse_interval_for gs p = ivl_exec_prog gs prog_main_name p"

definition analyse_interval :: "imp_prog \<Rightarrow> ivl abs_state lifted" where
  "analyse_interval p = analyse_interval_for (declared_global p) p"

corollary analyse_interval_sound:
  assumes "ivl_terminates_prog (declared_global p) prog_main_name p"
  shows "ltr_collect (declared_global p) (prog_cfg prog_main_name p) (cinit_stores (declared_global p))
           (cfg_exit (prog_cfg prog_main_name p))
         \<le> gamma_state_lift (analyse_interval p)"
  unfolding analyse_interval_def analyse_interval_for_def
  by (rule ivl_exec_prog_sound_collecting[OF refl assms])

text \<open>
  \<open>analyse_interval_td\<close>/\<open>analyse_interval_td_for\<close> mirror \<open>analyse_interval\<close>
  but solve via @{const TD_side_warrowing_apinis_Interp_solve} instead of the
  always-join rule, following \<open>ivl_exec_raw\<close>/\<open>ivl_exec_at\<close>/\<open>ivl_exec_prog\<close>'s
  own shape -- the unmodified, vendored APINIS warrowing rule.  Voblint issue #121:
  a CFG merge node's RHS evaluation issues more than one \<open>Side\<close> write to the same
  global key (one per predecessor edge, through @{const unit_edge_tree_st}'s shared
  global slot), and if one write is structurally \<^const>\<open>Bot\<close> the per-origin-gated
  update rule can destabilize its own \<open>QueryG\<close> dependency forever. \<open>ivl_exec_eqs\<close> fixes
  this at the generator layer instead of the solver: \<^const>\<open>side_cfg_T_eff_st_buffered\<close>
  folds every predecessor's Side-free contribution (\<^const>\<open>ivl_etf_st_contribution_for\<close>)
  through the untouched \<^const>\<open>fold_rhs_trees\<close> combinator and publishes the aggregated
  result as a single \<open>Side\<close> write per RHS evaluation, so the solver never observes more
  than one write per \<open>(global key, origin)\<close> pair. \<open>ivl_buffered_correspondence\<close>/
  \<open>ivl_buffered_dep_aux\<close>/\<open>ivl_buffered_sides_full\<close> transport \<open>part_post_solution\<close> and
  \<open>side_rg\<close> facts for the buffered generator back to the original, unbuffered
  \<^const>\<open>side_cfg_T_eff_st\<close> shape the executable-to-abstract transport lemmas
  (\<open>part_post_solution_st_to_abs_eff_unit_transfer\<close> etc.) are stated against, so those
  lemmas need no changes of their own. A soundness theorem for this pipeline follows the
  same collecting chain \<open>ivl_exec_sound_collecting_at\<close> uses, with
  \<open>TD_side_always_join_solve_Inr_rg\<close> replaced by \<^theory>\<open>Voblint_Core.Solver_Side_RG\<close>'s
  \<open>TD_side_warrowing_apinis_solve_Inr_rg\<close>: the warrowing update rule reads back its own
  per-origin bookkeeping (@{const sup_over_origins}) rather than just joining, so that
  bridge lemma additionally needs \<open>bot \<nabla> bot = bot\<close>/\<open>bot \<Delta> bot = bot\<close> for the domain in
  play --- \<open>ivl_widen_bot_bot\<close>/\<open>ivl_narrow_bot_bot\<close>
  (\<^theory>\<open>Voblint_Analysis.Interval_Warrowing\<close>) discharge exactly that for \<open>ivl\<close>.
\<close>

definition analyse_interval_td_raw ::
    "(ivl resolved_st_q \<Rightarrow> bool) \<Rightarrow> (vname \<Rightarrow> bool) \<Rightarrow> proc_table \<Rightarrow> pname list \<Rightarrow> pname \<Rightarrow> com
     \<Rightarrow> (pp + unit \<Rightarrow> ivl resolved_st_q lifted)" where
  "analyse_interval_td_raw is_bot_pred gs Pi ps mnm main =
     snd (TD_side_warrowing_apinis_Interp_solve
            (ivl_exec_eqs is_bot_pred gs Pi ps mnm main) (cfg_exit (compile_prog Pi ps mnm main)))"

definition analyse_interval_td_at ::
    "(ivl resolved_st_q \<Rightarrow> bool) \<Rightarrow> (vname \<Rightarrow> bool) \<Rightarrow> proc_table \<Rightarrow> pname list \<Rightarrow> pname \<Rightarrow> com \<Rightarrow> pp
     \<Rightarrow> ivl abs_state lifted" where
  "analyse_interval_td_at is_bot_pred gs Pi ps mnm main v =
     side_env_lift (map_lift (fun_of_resolved_st_q_for gs) \<circ> analyse_interval_td_raw is_bot_pred gs Pi ps mnm main) v"

text \<open>
  \<open>side_env_lift\<close> materializes the full \<open>vname \<Rightarrow> ivl\<close> function via pointwise \<open>\<squnion>\<close>,
  not executable over the infinite @{typ vname}. \<open>side_env_lift_st\<close> computes the
  same value straight from the two finite \<open>resolved_st_q\<close> slots.

  Point-free in \<open>v\<close>, matching \<open>interval_td_check_report_code\<close>'s own single-solve-per-report
  fix one layer up: naive unfolding calls \<^const>\<open>analyse_interval_td_raw\<close> -- a full TD solve --
  twice per \<open>v\<close> queried (once each for \<open>Inl v\<close>/\<open>Inr ()\<close>), so a caller that queries several
  points against the same solved analysis (e.g. a full-state GraphViz render walking every CFG
  node) must not hit the unfolded form. Binding \<open>raw\<close> here, outside the returned \<open>\<lambda>v\<close>, means a
  partial application to \<open>is_bot_pred gs Pi ps mnm main\<close> solves exactly once, reused for every
  \<open>v\<close> queried afterward against the resulting closure.
\<close>

lemma analyse_interval_td_at_code [code]:
  "analyse_interval_td_at is_bot_pred gs Pi ps mnm main =
     (let raw = analyse_interval_td_raw is_bot_pred gs Pi ps mnm main
      in (\<lambda>v. side_env_lift_st gs (raw (Inl v)) (raw (Inr ()))))"
  unfolding analyse_interval_td_at_def side_env_lift_st_eq_side_env_lift Let_def
  by (rule refl)

definition analyse_interval_td_for :: "(vname \<Rightarrow> bool) \<Rightarrow> imp_prog \<Rightarrow> ivl abs_state lifted" where
  "analyse_interval_td_for gs p =
     analyse_interval_td_at (resolved_st_q_is_bot_for (declared_global_vars p)) gs
       (prog_table p) (prog_procs p) prog_main_name (prog_main p)
       (cfg_exit (prog_cfg prog_main_name p))"

definition analyse_interval_td :: "imp_prog \<Rightarrow> ivl abs_state lifted" where
  "analyse_interval_td p = analyse_interval_td_for (declared_global p) p"

text \<open>
  \<open>analyse_interval_td_terminates\<close> mirrors \<open>ivl_exec_terminates\<close>, one layer down from
  \<open>analyse_interval_td_raw\<close>/\<open>analyse_interval_td_at\<close> exactly as \<open>ivl_exec_terminates\<close> sits
  below \<open>ivl_exec_raw\<close>/\<open>ivl_exec_at\<close>.
\<close>

definition analyse_interval_td_terminates ::
    "(ivl resolved_st_q \<Rightarrow> bool) \<Rightarrow> (vname \<Rightarrow> bool) \<Rightarrow> proc_table \<Rightarrow> pname list \<Rightarrow> pname \<Rightarrow> com \<Rightarrow> bool" where
  "analyse_interval_td_terminates is_bot_pred gs Pi ps mnm main =
     TD_side_warrowing_apinis_Interp.solve_dom TYPE(unit) TYPE(ivl resolved_st_q lifted)
        (ivl_exec_eqs is_bot_pred gs Pi ps mnm main) (cfg_exit (compile_prog Pi ps mnm main))"

lemma analyse_interval_td_terminates_via_solve_c:
  assumes "TD_side_warrowing_apinis_Interp_solve_c (ivl_exec_eqs is_bot_pred gs Pi ps mnm main)
             (cfg_exit (compile_prog Pi ps mnm main)) \<noteq> None"
  shows "analyse_interval_td_terminates is_bot_pred gs Pi ps mnm main"
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
  assumes solves: "analyse_interval_td_terminates is_bot_pred gs Pi ps mnm main"
    and exact: "\<And>s. is_bot_pred s = is_bot_state (fun_of_resolved_st_q_for gs s)"
    and reach_v: "cfg_reaches (compile_prog Pi ps mnm main) v (cfg_exit (compile_prog Pi ps mnm main))"
  shows "ltr_collect gs (compile_prog Pi ps mnm main) (cinit_stores gs) v
         \<le> gamma_state_lift (analyse_interval_td_at is_bot_pred gs Pi ps mnm main v)"
proof -
  define g :: cfg where "g = compile_prog Pi ps mnm main"
  define sol :: "pp set \<times> (pp + unit \<Rightarrow> ivl resolved_st_q lifted)" where
    "sol = TD_side_warrowing_apinis_Interp_solve (ivl_exec_eqs is_bot_pred gs Pi ps mnm main) (cfg_exit g)"
  define sigma :: "pp + unit \<Rightarrow> ivl abs_state lifted" where
    "sigma = map_lift (fun_of_resolved_st_q_for gs) \<circ> snd sol"
  have fin: "finite (intra g)" unfolding g_def using compile_prog_finite by simp
  have finC: "finite (calls g)" unfolding g_def using compile_prog_finite by simp
  have wf: "wf_cfg g" unfolding g_def by (rule compile_prog_wf)
  have dom: "TD_side_warrowing_apinis_Interp.solve_dom TYPE(unit) TYPE(ivl resolved_st_q lifted)
               (ivl_exec_eqs is_bot_pred gs Pi ps mnm main) (cfg_exit g)"
    using solves unfolding analyse_interval_td_terminates_def g_def by simp
  have pp0: "part_post_solution (ivl_exec_eqs is_bot_pred gs Pi ps mnm main) (cfg_exit g) (snd sol) (fst sol)"
    using TD_side_warrowing_apinis_Interp.partial_post_solution[OF dom, of "fst sol" "snd sol"]
    unfolding sol_def by simp
  have pp_st: "part_post_solution (side_cfg_T_eff_st g (ivl_etf_st_for is_bot_pred gs) bot cinit_ivl_st ())
                 (cfg_exit g) (snd sol) (fst sol)"
    using pp0
    unfolding ivl_exec_eqs_def g_def side_cfg_T_eff_st_buffered_def side_cfg_T_eff_st_def
              dep_def dep\<^sub>L_def
    by (simp add: ivl_buffered_correspondence ivl_buffered_dep_aux ivl_buffered_sides_full)
  have pp_eff: "part_post_solution
                  (side_cfg_T_eff gs g (ivl_etf gs) bot
                     (\<lambda>x. if gs x then Ivl (Fin 0) (Fin 0) else Ivl MinInf PlusInf) ())
                  (cfg_exit g) sigma (fst sol)"
    using part_post_solution_st_to_abs_eff_unit_transfer
            [OF ivl_etf_edge_tree ivl_etf_combine_tree
                ivl_etf_st_for_edge_tree ivl_etf_st_for_combine_tree ivl_tf_st_for_commute
                ivl_etf_enter_tree ivl_etf_st_for_enter_tree ivl_enter_st_for_commute
                exact pp_st]
    by (simp add: sigma_def fun_of_st_cinit_ivl_st_for bot_fun_def)
  have cone: "cone_compatible_etf gs (ivl_etf gs)" by (rule ivl_etf_cone_compatible)
  have srz: "\<And>z. side_rg (ivl_exec_eqs is_bot_pred gs Pi ps mnm main z)"
    unfolding ivl_exec_eqs_def side_cfg_T_eff_st_buffered_def ivl_etf_st_contribution_for_def
    by (rule side_rg_unit_etf_st_contribution_of_transfer[OF ivl_tf_st_for_reduces])
  have solpair: "TD_side_warrowing_apinis_Interp_solve (ivl_exec_eqs is_bot_pred gs Pi ps mnm main) (cfg_exit g)
                   = (fst sol, snd sol)"
    unfolding sol_def by simp
  have rg: "\<And>gg. snd sol (Inr gg) = map_lift restrict_global_resolved_q (snd sol (Inr gg))"
    by (rule TD_side_warrowing_apinis_solve_Inr_rg
          [OF dom srz ivl_widen_bot_bot ivl_narrow_bot_bot solpair])
  have inr: "inr_slot_locals_bot gs sigma"
    unfolding sigma_def
    using inr_slot_locals_bot_fun_of_resolved_st_q_for_restrict_global_abs rg by blast
  have reach: "cfg_reaches g (cfg_entry g) (cfg_exit g)"
    by (simp add: g_def compile_prog_entry_cfg_reaches_exit)
  have entry_in: "cfg_entry g \<in> fst sol"
    by (rule side_cone_in_vars_eff_cone[OF pp_eff fin finC wf cone reach])
  have entry_le: "Lifted (\<lambda>x. if gs x then Ivl (Fin 0) (Fin 0) else Ivl MinInf PlusInf)
                    \<le> side_env_lift sigma (cfg_entry g)"
    by (rule s0_le_side_env_entry_eff[OF pp_eff entry_in])
  have seed_cov: "cinit_stores gs
                    \<subseteq> \<lbrakk>\<lambda>x. if gs x then Ivl (Fin 0) (Fin 0) else Ivl MinInf PlusInf\<rbrakk>"
    unfolding cinit_stores_def gamma_state_def
    by auto
  have entry_le': "\<lbrakk>\<lambda>x. if gs x then Ivl (Fin 0) (Fin 0) else Ivl MinInf PlusInf\<rbrakk>
                     \<subseteq> gamma_state_lift (side_env_lift sigma (cfg_entry g))"
    using gamma_lift_mono[OF gamma_state_mono entry_le] by simp
  have entry_cov: "cinit_stores gs \<le> gamma_state_lift (side_env_lift sigma (cfg_entry g))"
    using seed_cov entry_le' by (rule subset_trans)
  have reach_v': "cfg_reaches g v (cfg_exit g)"
    using reach_v unfolding g_def by simp
  have "ltr_collect gs g (cinit_stores gs) v
        \<le> gamma_state_lift (side_env_lift sigma v)"
    by (rule side_collect_sound_in_eff_cone
          [OF ivl_sound_etf pp_eff fin finC wf entry_cov cone inr reach_v'])
  then show ?thesis
    by (simp add: g_def sigma_def sol_def analyse_interval_td_at_def analyse_interval_td_raw_def)
qed

corollary analyse_interval_td_sound_collecting:
  fixes mnm :: pname
  assumes solves: "analyse_interval_td_terminates is_bot_pred gs Pi ps mnm main"
    and exact: "\<And>s. is_bot_pred s = is_bot_state (fun_of_resolved_st_q_for gs s)"
  shows "ltr_collect gs (compile_prog Pi ps mnm main) (cinit_stores gs)
           (cfg_exit (compile_prog Pi ps mnm main))
         \<le> gamma_state_lift (analyse_interval_td_at is_bot_pred gs Pi ps mnm main
              (cfg_exit (compile_prog Pi ps mnm main)))"
  by (rule analyse_interval_td_sound_collecting_at[OF solves exact cfg_reaches_refl])

text \<open>
  The node-arbitrary prog-level corollary, mirroring \<open>ivl_exec_prog_sound_collecting_at\<close>:
  needed by a check-report layer, which classifies a check at whatever node it sits at, not only
  at \<open>cfg_exit\<close>.
\<close>

corollary analyse_interval_td_prog_sound_collecting_at:
  assumes terminates: "analyse_interval_td_terminates
             (resolved_st_q_is_bot_for (declared_global_vars p))
             (declared_global p) (prog_table p) (prog_procs p) prog_main_name (prog_main p)"
    and reach: "cfg_reaches (prog_cfg prog_main_name p) v (cfg_exit (prog_cfg prog_main_name p))"
  shows "ltr_collect (declared_global p) (prog_cfg prog_main_name p) (cinit_stores (declared_global p)) v
           \<le> gamma_state_lift (analyse_interval_td_at
                (resolved_st_q_is_bot_for (declared_global_vars p))
                (declared_global p) (prog_table p) (prog_procs p)
                prog_main_name (prog_main p) v)"
  unfolding prog_cfg_def
  by (rule analyse_interval_td_sound_collecting_at
        [OF terminates resolved_st_q_is_bot_for_iff[OF declared_global_iff] reach[unfolded prog_cfg_def]])

text \<open>
  Convenience instance at \<^const>\<open>declared_global\<close> \<open>p\<close>, matching \<open>analyse_interval_sound\<close>'s shape.
\<close>

corollary analyse_interval_td_sound:
  assumes terminates: "analyse_interval_td_terminates
             (resolved_st_q_is_bot_for (declared_global_vars p))
             (declared_global p) (prog_table p) (prog_procs p) prog_main_name (prog_main p)"
  shows "ltr_collect (declared_global p) (prog_cfg prog_main_name p) (cinit_stores (declared_global p))
           (cfg_exit (prog_cfg prog_main_name p))
         \<le> gamma_state_lift (analyse_interval_td p)"
  unfolding analyse_interval_td_def analyse_interval_td_for_def prog_cfg_def
  by (rule analyse_interval_td_sound_collecting
        [OF terminates[unfolded prog_cfg_def] resolved_st_q_is_bot_for_iff[OF declared_global_iff]])

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
  "ivl_graph_config gs \<Pi> ps mnm main = compiled_domain_graph_config gs \<Pi> ps mnm main (\<lambda>v. v = ivl_top)"

text \<open>
  Proof-side only: confirms the executable top test \<^const>\<open>ivl_graph_config\<close> is built
  from agrees with the semantic \<^const>\<open>is_top\<close> from \<^class>\<open>sound_domain\<close>. Not used in
  any exported definition, so it never reintroduces \<^class>\<open>sound_domain\<close>'s code
  dependency into \<^const>\<open>compiled_domain_graph_config\<close>.
\<close>
lemma ivl_top_test_eq_is_top: "(\<lambda>v. v = ivl_top) = (is_top :: ivl \<Rightarrow> bool)"
  by (rule ext) (simp add: is_top_ivl_correct top_ivl_def)

definition ivl_graph_solution ::
  "(vname \<Rightarrow> bool) \<Rightarrow> (pp + unit \<Rightarrow> ivl resolved_st_q) \<Rightarrow> (pp \<times> unit + unit \<Rightarrow> ivl abs_state)" where
  "ivl_graph_solution gs sol z =
    (case z of Inl (p, ()) \<Rightarrow> fun_of_resolved_st_q_for gs (sol (Inl p))
     | Inr () \<Rightarrow> fun_of_resolved_st_q_for gs (sol (Inr ())) )"

definition ivl_annotated_dot_lit ::
  "(ivl resolved_st_q \<Rightarrow> bool) \<Rightarrow> (vname \<Rightarrow> bool) \<Rightarrow> proc_table \<Rightarrow> pname list \<Rightarrow> pname \<Rightarrow> com \<Rightarrow> String.literal" where
  "ivl_annotated_dot_lit is_bot_pred gs \<Pi> ps mnm main =
    String.implode
      (let g = compile_prog \<Pi> ps mnm main;
           domain = contextual_graph_domain g (\<lambda>_. [()]) @ [Inr ()];
           sol = ivl_graph_solution gs
                   (\<lambda>z. case ivl_exec_raw is_bot_pred gs \<Pi> ps mnm main z of Bot \<Rightarrow> bot | Lifted d \<Rightarrow> d)
       in contextual_analysis_dot (ivl_graph_config gs \<Pi> ps mnm main) g domain sol)"

definition ivl_annotated_dot_prog_lit :: "(vname \<Rightarrow> bool) \<Rightarrow> pname \<Rightarrow> imp_prog \<Rightarrow> String.literal" where
  "ivl_annotated_dot_prog_lit gs mnm p =
     ivl_annotated_dot_lit (resolved_st_q_is_bot_for (declared_global_vars p)) gs
       (prog_table p) (prog_procs p) mnm (prog_main p)"

section \<open>Native D/G runtime API: an arbitrary VIMP program\<close>

text \<open>
  \<open>ivl_exec_prog\<close>/\<open>analyse_interval_td\<close> above are the older \<open>side_cfg_T_eff_st\<close>
  pipeline. The definitions below give Interval the same Base-style native D/G route
  Sign's \<open>analyse_sign_eqs_for\<close>/\<open>analyse_sign_for\<close>/\<open>analyse_sign_env_for\<close> (\<open>Sign_Exec_Sound\<close>)
  already give Sign: the local unknown is the whole
  reachability-lifted abstract state (\<open>D\<close>), so a VIMP global lives exactly where a
  local does, with no separate flow-insensitive solver-global summary to route it
  through. Named \<open>analyse_interval_dg_*\<close>, distinct from the existing \<open>analyse_interval\<close>/
  \<open>analyse_interval_td\<close> families above, so this new route can be introduced without
  changing what those two already-wired pipelines mean --- \<open>analyse_interval_td_report_for\<close>
  (\<open>Interval_Checks\<close>, downstream) is the only caller repointed onto this route;
  \<open>analyse_interval_td_at\<close>/\<open>analyse_interval_td_terminates\<close> keep their existing callers
  (the entry-state context analysis, the GraphViz state-report tooling) unchanged.

  Interval's local lattice has infinite height (an unbounded integer bound), so unlike
  Sign this route still needs widening for termination even though the flow-insensitive
  global summary that motivated \<open>analyse_interval_td\<close>'s own switch to warrowing is gone:
  a loop-carried local bound still needs \<^const>\<open>TD_side_warrowing_apinis_Interp_solve\<close>,
  not the always-join rule \<open>analyse_sign_for\<close> uses --- \<open>Example_Interval_DG_Flagship\<close>
  already demonstrates the same warrowing solver terminating on a genuinely unbounded
  loop through the (pre-Base) native D/G spine.

  Only the raw computation lives here --- soundness needs the \<open>base_dg_exec_analysis\<close>
  locale (\<open>Run_Analysis_Sound\<close>, Formalization session), one session later than Analysis
  in the locked six-session chain, so that half stays downstream in
  \<open>Example_Interval_Codegen\<close> (Examples), mirroring \<open>Example_Sign_Codegen\<close>.

  \<open>G\<close> stays diagonal at \<open>ivl exec_dg_st lifted\<close>, matching what \<open>dg_gen_of\<close> needs; its
  content is never read, since every field of \<^const>\<open>base_dg_spec_st_for_lifted\<close>
  threads its incoming \<open>g\<close> through unchanged.
\<close>

definition analyse_interval_dg_eqs_for ::
  "(ivl exec_dg_st \<Rightarrow> bool) \<Rightarrow> (vname \<Rightarrow> bool) \<Rightarrow> imp_prog \<Rightarrow>
     pp \<times> unit \<Rightarrow> (pp \<times> unit, unit, (ivl exec_dg_st lifted, ivl exec_dg_st lifted) dg_state) strategy_tree" where
  "analyse_interval_dg_eqs_for is_bot_pred gs p =
     dg_gen_of
       (base_dg_spec_st_for_lifted gs is_bot_pred (ivl_tf_st_for gs) (ivl_enter_st_for gs))
       (prog_cfg prog_main_name p) bot (Lifted cinit_ivl_st) (Lifted cinit_ivl_st)"

definition analyse_interval_dg_for :: "(ivl exec_dg_st \<Rightarrow> bool) \<Rightarrow> (vname \<Rightarrow> bool) \<Rightarrow> imp_prog \<Rightarrow>
    (pp \<times> unit) set \<times> (pp \<times> unit + unit \<Rightarrow> (ivl exec_dg_st lifted, ivl exec_dg_st lifted) dg_state)" where
  "analyse_interval_dg_for is_bot_pred gs p =
     TD_side_warrowing_apinis_Interp_solve (analyse_interval_dg_eqs_for is_bot_pred gs p)
       (cfg_exit (prog_cfg prog_main_name p), ())"

text \<open>
  \<open>analyse_interval_dg_env_for\<close> reads the local unknown at \<open>v\<close> (\<open>Inl (v, ())\<close>) straight
  back through \<^const>\<open>fun_of_exec_dg_st_for\<close>/\<^const>\<open>map_lift\<close>, mirroring
  \<open>analyse_sign_env_for\<close> exactly: the whole abstract state already lives there, so there
  is no locals-from-\<open>D\<close>/globals-from-\<open>G\<close> reconstruction to perform. A genuinely
  unreachable local unknown (\<open>Bot\<close>) concretizes to \<open>bot\<close>, matching
  \<^const>\<open>gamma_state_lift\<close>'s own \<open>Bot\<close> case.

  The \<open>[code]\<close> rewrite below is point-free in \<open>v\<close>, the same single-solve-per-report fix
  \<open>analyse_sign_env_for_code\<close> uses: \<^const>\<open>analyse_interval_dg_for\<close> is solved exactly
  once per partial application to \<open>is_bot_pred gs p\<close>, reused for every \<open>v\<close> queried
  afterward against the resulting closure.
\<close>

definition analyse_interval_dg_env_for :: "(ivl exec_dg_st \<Rightarrow> bool) \<Rightarrow> (vname \<Rightarrow> bool) \<Rightarrow> imp_prog \<Rightarrow> pp \<Rightarrow> ivl abs_state" where
  "analyse_interval_dg_env_for is_bot_pred gs p v =
     (case map_lift (fun_of_exec_dg_st_for gs) (locals (snd (analyse_interval_dg_for is_bot_pred gs p) (Inl (v, ()))))
      of Bot \<Rightarrow> bot | Lifted s \<Rightarrow> s)"

declare analyse_interval_dg_env_for_def [code del]

lemma analyse_interval_dg_env_for_code [code]:
  "analyse_interval_dg_env_for is_bot_pred gs p =
     (let sol = snd (analyse_interval_dg_for is_bot_pred gs p)
      in (\<lambda>v. case map_lift (fun_of_exec_dg_st_for gs) (locals (sol (Inl (v, ()))))
              of Bot \<Rightarrow> bot | Lifted s \<Rightarrow> s))"
  unfolding analyse_interval_dg_env_for_def Let_def by (rule refl)

text \<open>
  Convenience instances at \<^const>\<open>declared_global\<close> \<open>p\<close>, matching \<open>analyse_sign_eqs\<close>/
  \<open>analyse_sign\<close>/\<open>analyse_sign_env\<close>'s shape. \<open>is_bot_pred\<close> is fixed here to
  \<^const>\<open>resolved_st_q_is_bot_for\<close> at \<open>p\<close>'s own \<^const>\<open>declared_global_vars\<close>, exact for
  \<^const>\<open>is_bot_state\<close> by @{thm resolved_st_q_is_bot_for_iff} (@{thm declared_global_iff}).
\<close>

definition analyse_interval_dg_eqs :: "imp_prog \<Rightarrow>
    pp \<times> unit \<Rightarrow> (pp \<times> unit, unit, (ivl exec_dg_st lifted, ivl exec_dg_st lifted) dg_state) strategy_tree" where
  "analyse_interval_dg_eqs p = analyse_interval_dg_eqs_for (resolved_st_q_is_bot_for (declared_global_vars p)) (declared_global p) p"

definition analyse_interval_dg :: "imp_prog \<Rightarrow>
    (pp \<times> unit) set \<times> (pp \<times> unit + unit \<Rightarrow> (ivl exec_dg_st lifted, ivl exec_dg_st lifted) dg_state)" where
  "analyse_interval_dg p = analyse_interval_dg_for (resolved_st_q_is_bot_for (declared_global_vars p)) (declared_global p) p"

definition analyse_interval_dg_env :: "imp_prog \<Rightarrow> pp \<Rightarrow> ivl abs_state" where
  "analyse_interval_dg_env p = analyse_interval_dg_env_for (resolved_st_q_is_bot_for (declared_global_vars p)) (declared_global p) p"

subsection \<open>Solver-choice variants: join and per-origin update rules, on the same equation system\<close>

text \<open>
  \<open>analyse_interval_dg_join_for\<close>/\<open>analyse_interval_dg_per_origin_for\<close> are
  \<^const>\<open>analyse_interval_dg_for\<close>'s siblings under the always-join and per-origin update rules
  (\<^const>\<open>TD_side_always_join_Interp_solve\<close>, \<^const>\<open>TD_side_per_origin_Interp_solve\<close>) instead of
  Apinis warrowing --- solving the exact same \<^const>\<open>analyse_interval_dg_eqs_for\<close> equation
  system, so a VIMP global still lives only in the reachability-lifted local unknown, with no
  separate flow-insensitive summary reintroduced for either update rule. Mirrors Sign's
  \<open>Sign_Checks.analyse_sign_for_per_origin\<close>, and gives Interval's own join/per-origin variants
  the same \<open>_env_for\<close> reading layer \<^const>\<open>analyse_interval_dg_env_for\<close> already has, so their
  soundness proofs (in the Examples session, downstream) can reuse the identical
  \<open>base_dg_exec_analysis\<close>/\<open>gamma_eq_env\<close> proof shape the warrowing route uses, not a bespoke
  argument per update rule.
\<close>

definition analyse_interval_dg_join_for :: "(ivl exec_dg_st \<Rightarrow> bool) \<Rightarrow> (vname \<Rightarrow> bool) \<Rightarrow> imp_prog \<Rightarrow>
    (pp \<times> unit) set \<times> (pp \<times> unit + unit \<Rightarrow> (ivl exec_dg_st lifted, ivl exec_dg_st lifted) dg_state)" where
  "analyse_interval_dg_join_for is_bot_pred gs p =
     TD_side_always_join_Interp_solve (analyse_interval_dg_eqs_for is_bot_pred gs p)
       (cfg_exit (prog_cfg prog_main_name p), ())"

definition analyse_interval_dg_join_env_for :: "(ivl exec_dg_st \<Rightarrow> bool) \<Rightarrow> (vname \<Rightarrow> bool) \<Rightarrow> imp_prog \<Rightarrow> pp \<Rightarrow> ivl abs_state" where
  "analyse_interval_dg_join_env_for is_bot_pred gs p v =
     (case map_lift (fun_of_exec_dg_st_for gs) (locals (snd (analyse_interval_dg_join_for is_bot_pred gs p) (Inl (v, ()))))
      of Bot \<Rightarrow> bot | Lifted s \<Rightarrow> s)"

declare analyse_interval_dg_join_env_for_def [code del]

lemma analyse_interval_dg_join_env_for_code [code]:
  "analyse_interval_dg_join_env_for is_bot_pred gs p =
     (let sol = snd (analyse_interval_dg_join_for is_bot_pred gs p)
      in (\<lambda>v. case map_lift (fun_of_exec_dg_st_for gs) (locals (sol (Inl (v, ()))))
              of Bot \<Rightarrow> bot | Lifted s \<Rightarrow> s))"
  unfolding analyse_interval_dg_join_env_for_def Let_def by (rule refl)

definition analyse_interval_dg_per_origin_for :: "(ivl exec_dg_st \<Rightarrow> bool) \<Rightarrow> (vname \<Rightarrow> bool) \<Rightarrow> imp_prog \<Rightarrow>
    (pp \<times> unit) set \<times> (pp \<times> unit + unit \<Rightarrow> (ivl exec_dg_st lifted, ivl exec_dg_st lifted) dg_state)" where
  "analyse_interval_dg_per_origin_for is_bot_pred gs p =
     TD_side_per_origin_Interp_solve (analyse_interval_dg_eqs_for is_bot_pred gs p)
       (cfg_exit (prog_cfg prog_main_name p), ())"

definition analyse_interval_dg_per_origin_env_for :: "(ivl exec_dg_st \<Rightarrow> bool) \<Rightarrow> (vname \<Rightarrow> bool) \<Rightarrow> imp_prog \<Rightarrow> pp \<Rightarrow> ivl abs_state" where
  "analyse_interval_dg_per_origin_env_for is_bot_pred gs p v =
     (case map_lift (fun_of_exec_dg_st_for gs) (locals (snd (analyse_interval_dg_per_origin_for is_bot_pred gs p) (Inl (v, ()))))
      of Bot \<Rightarrow> bot | Lifted s \<Rightarrow> s)"

declare analyse_interval_dg_per_origin_env_for_def [code del]

lemma analyse_interval_dg_per_origin_env_for_code [code]:
  "analyse_interval_dg_per_origin_env_for is_bot_pred gs p =
     (let sol = snd (analyse_interval_dg_per_origin_for is_bot_pred gs p)
      in (\<lambda>v. case map_lift (fun_of_exec_dg_st_for gs) (locals (sol (Inl (v, ()))))
              of Bot \<Rightarrow> bot | Lifted s \<Rightarrow> s))"
  unfolding analyse_interval_dg_per_origin_env_for_def Let_def by (rule refl)

text \<open>
  Convenience instances at \<^const>\<open>declared_global\<close> \<open>p\<close>, matching \<^const>\<open>analyse_interval_dg\<close>/
  \<^const>\<open>analyse_interval_dg_env\<close>'s own shape.
\<close>

definition analyse_interval_dg_join :: "imp_prog \<Rightarrow>
    (pp \<times> unit) set \<times> (pp \<times> unit + unit \<Rightarrow> (ivl exec_dg_st lifted, ivl exec_dg_st lifted) dg_state)" where
  "analyse_interval_dg_join p = analyse_interval_dg_join_for (resolved_st_q_is_bot_for (declared_global_vars p)) (declared_global p) p"

definition analyse_interval_dg_join_env :: "imp_prog \<Rightarrow> pp \<Rightarrow> ivl abs_state" where
  "analyse_interval_dg_join_env p = analyse_interval_dg_join_env_for (resolved_st_q_is_bot_for (declared_global_vars p)) (declared_global p) p"

definition analyse_interval_dg_per_origin :: "imp_prog \<Rightarrow>
    (pp \<times> unit) set \<times> (pp \<times> unit + unit \<Rightarrow> (ivl exec_dg_st lifted, ivl exec_dg_st lifted) dg_state)" where
  "analyse_interval_dg_per_origin p = analyse_interval_dg_per_origin_for (resolved_st_q_is_bot_for (declared_global_vars p)) (declared_global p) p"

definition analyse_interval_dg_per_origin_env :: "imp_prog \<Rightarrow> pp \<Rightarrow> ivl abs_state" where
  "analyse_interval_dg_per_origin_env p = analyse_interval_dg_per_origin_env_for (resolved_st_q_is_bot_for (declared_global_vars p)) (declared_global p) p"

end
