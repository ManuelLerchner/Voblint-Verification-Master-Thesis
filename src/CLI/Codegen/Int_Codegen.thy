theory Int_Codegen
  imports "Voblint_Analysis.Int_Checks" "Voblint_Formalization.Run_Analysis_Sound"
begin

section \<open>Int codegen API: an arbitrary VIMP program, and its production soundness\<close>

text \<open>
  Mirrors Interval's \<open>Interval_Codegen\<close>: \<open>analyse_int_dg_eqs_for\<close>/
  \<open>analyse_int_dg_for\<close>/\<open>analyse_int_dg_env_for\<close> (\<^theory>\<open>Voblint_Analysis.Int_Exec_Sound\<close>)
  and \<open>analyse_int_report_for\<close>/\<open>analyse_int_report\<close> (\<^theory>\<open>Voblint_Analysis.Int_Checks\<close>)
  are pure computation, no dependence on the \<open>base_dg_exec_analysis\<close> locale interpreted
  below, so they live one session earlier (Analysis). Only the soundness half needs that
  locale, one session later than Analysis in the locked six-session chain, so it lives here.

  Like Interval, \<open>int_dom\<close>'s \<open>int_ivl\<close> component has infinite height, so the first
  interpretation below solves via \<^const>\<open>TD_side_warrowing_apinis_Interp.solve\<close>/\<open>.solve_c\<close>,
  matching \<open>analyse_int_dg_for\<close>'s own solver choice --- \<open>base_dg_exec_analysis\<close> is generic
  in the solver, so this is a like-for-like swap of the locale's \<open>solve\<close>/\<open>solve_c\<close>
  parameters, not a different registration shape. All three refinement modes are proved at
  once, by \<open>cases mode\<close>; the two further interpretations after it repeat this exact
  \<open>cases mode\<close> shape for the always-join and per-origin update rules
  (\<^theory>\<open>Voblint_Analysis.Int_Exec_Sound\<close>'s \<open>analyse_int_dg_join_for\<close>/
  \<open>analyse_int_dg_per_origin_for\<close>), mirroring Interval's own solver-choice soundness block
  --- only the \<open>solve\<close>/\<open>solve_c\<close> parameters and the final \<open>part_post_solution_of_solve_c\<close>
  citation differ per solver.
\<close>

context
  fixes p :: imp_prog and mode :: refine_mode
  assumes reserved: "reserved_ret_var (declared_global p)"
begin

abbreviation pgs :: "vname \<Rightarrow> bool" where "pgs \<equiv> declared_global p"

text \<open>
  \<open>mode\<close> ranges over all three refinement modes (\<open>Refine_Never\<close>, \<open>Refine_Once\<close>,
  \<open>Refine_Fixpoint\<close>, \<^theory>\<open>Voblint_Analysis.Int_Refinement\<close>): the case split below
  picks the matching \<^theory>\<open>Voblint_Analysis.Int_Transfer\<close>/\<open>Int_Exec\<close> bundle per mode,
  the same three bundles \<open>int_tf_st_for\<close>/\<open>int_dom_enter_st_for\<close>
  (\<^theory>\<open>Voblint_Analysis.Int_Exec_Sound\<close>) already dispatch on. Never's and Once's
  \<open>apply_tf\<close> monotonicity bonus and Fixpoint's absent one
  (\<^theory>\<open>Voblint_Analysis.Int_Transfer\<close>) play no role here: \<open>base_dg_exec_analysis\<close>'s own
  assumptions (\<open>tf_sound\<close>, \<open>tf_commute\<close>, \<open>enter_commute\<close>, \<open>is_bot_exact\<close>, \<open>solver_pps\<close>,
  \<^theory>\<open>Voblint_Formalization.Run_Analysis_Sound\<close>) never cite a monotonicity fact, so all
  three modes discharge the identical locale by the identical proof shape, just citing
  each mode's own pre-proved \<open>sound_transfer_for\<close>/\<open>_st_for_commute\<close>/\<open>_st_for_reduces\<close>
  triple (\<^theory>\<open>Voblint_Analysis.Int_Transfer\<close>/\<open>Int_Exec\<close>).
\<close>

interpretation p_reg:
  base_dg_exec_analysis pgs
    "int_tf_for mode pgs" "int_tf_st_for mode pgs" "int_dom_enter_st_for mode pgs"
    "resolved_st_q_is_bot_for (declared_global_vars p)"
    "TD_side_warrowing_apinis_Interp.solve" "TD_side_warrowing_apinis_Interp.solve_c"
proof (cases mode)
  case Refine_Never
  interpret p_transfer: sound_transfer_for pgs "int_tf_never_for pgs"
    by (rule int_never_is_sound_transfer_for)
  show "base_dg_exec_analysis pgs
          (int_tf_for mode pgs) (int_tf_st_for mode pgs) (int_dom_enter_st_for mode pgs)
          (resolved_st_q_is_bot_for (declared_global_vars p))
          TD_side_warrowing_apinis_Interp.solve TD_side_warrowing_apinis_Interp.solve_c"
    unfolding Refine_Never int_tf_for.simps int_tf_st_for.simps int_dom_enter_st_for.simps
    by unfold_locales
       (rule reserved
             p_transfer.tf_sound_assign_for p_transfer.tf_sound_special_for
             p_transfer.tf_sound_branch_for
             p_transfer.tf_sound_enter_for p_transfer.tf_sound_combine_env_for
             int_tf_st_never_for_commute[folded fun_of_exec_dg_st_for_def]
             int_dom_enter_never_st_for_commute[folded fun_of_exec_dg_st_for_def]
             resolved_st_q_is_bot_for_iff[OF declared_global_iff, folded fun_of_exec_dg_st_for_def]
             action_reduces.ret_none[OF int_tf_st_never_for_reduces]
             action_reduces.ret_some[OF int_tf_st_never_for_reduces]
             action_reduces.check[OF int_tf_st_never_for_reduces]
             TD_side_warrowing_apinis_Interp.part_post_solution_of_solve_c)+
next
  case Refine_Once
  interpret p_transfer: sound_transfer_for pgs "int_tf_once_for pgs"
    by (rule int_once_is_sound_transfer_for)
  show "base_dg_exec_analysis pgs
          (int_tf_for mode pgs) (int_tf_st_for mode pgs) (int_dom_enter_st_for mode pgs)
          (resolved_st_q_is_bot_for (declared_global_vars p))
          TD_side_warrowing_apinis_Interp.solve TD_side_warrowing_apinis_Interp.solve_c"
    unfolding Refine_Once int_tf_for.simps int_tf_st_for.simps int_dom_enter_st_for.simps
    by unfold_locales
       (rule reserved
             p_transfer.tf_sound_assign_for p_transfer.tf_sound_special_for
             p_transfer.tf_sound_branch_for
             p_transfer.tf_sound_enter_for p_transfer.tf_sound_combine_env_for
             int_tf_st_once_for_commute[folded fun_of_exec_dg_st_for_def]
             int_dom_enter_once_st_for_commute[folded fun_of_exec_dg_st_for_def]
             resolved_st_q_is_bot_for_iff[OF declared_global_iff, folded fun_of_exec_dg_st_for_def]
             action_reduces.ret_none[OF int_tf_st_once_for_reduces]
             action_reduces.ret_some[OF int_tf_st_once_for_reduces]
             action_reduces.check[OF int_tf_st_once_for_reduces]
             TD_side_warrowing_apinis_Interp.part_post_solution_of_solve_c)+
next
  case Refine_Fixpoint
  interpret p_transfer: sound_transfer_for pgs "int_tf_fixpoint_for pgs"
    by (rule int_fixpoint_is_sound_transfer_for)
  show "base_dg_exec_analysis pgs
          (int_tf_for mode pgs) (int_tf_st_for mode pgs) (int_dom_enter_st_for mode pgs)
          (resolved_st_q_is_bot_for (declared_global_vars p))
          TD_side_warrowing_apinis_Interp.solve TD_side_warrowing_apinis_Interp.solve_c"
    unfolding Refine_Fixpoint int_tf_for.simps int_tf_st_for.simps int_dom_enter_st_for.simps
    by unfold_locales
       (rule reserved
             p_transfer.tf_sound_assign_for p_transfer.tf_sound_special_for
             p_transfer.tf_sound_branch_for
             p_transfer.tf_sound_enter_for p_transfer.tf_sound_combine_env_for
             int_tf_st_fixpoint_for_commute[folded fun_of_exec_dg_st_for_def]
             int_dom_enter_fixpoint_st_for_commute[folded fun_of_exec_dg_st_for_def]
             resolved_st_q_is_bot_for_iff[OF declared_global_iff, folded fun_of_exec_dg_st_for_def]
             action_reduces.ret_none[OF int_tf_st_fixpoint_for_reduces]
             action_reduces.ret_some[OF int_tf_st_fixpoint_for_reduces]
             action_reduces.check[OF int_tf_st_fixpoint_for_reduces]
             TD_side_warrowing_apinis_Interp.part_post_solution_of_solve_c)+
qed

text \<open>
  Always-join and per-origin siblings of \<open>p_reg\<close>, same \<open>cases mode\<close> shape, same
  \<open>int_tf_for\<close>/\<open>int_tf_st_for\<close>/\<open>int_dom_enter_st_for\<close> dispatch, only the \<open>solve\<close>/\<open>solve_c\<close>
  parameters and the trailing \<open>part_post_solution_of_solve_c\<close> fact swapped --- mirroring
  \<open>Interval_Codegen\<close>'s own \<open>p_reg_join\<close>/\<open>p_reg_per_origin\<close> blocks.
\<close>

interpretation p_reg_join:
  base_dg_exec_analysis pgs
    "int_tf_for mode pgs" "int_tf_st_for mode pgs" "int_dom_enter_st_for mode pgs"
    "resolved_st_q_is_bot_for (declared_global_vars p)"
    "TD_side_always_join_Interp.solve" "TD_side_always_join_Interp.solve_c"
proof (cases mode)
  case Refine_Never
  interpret p_transfer: sound_transfer_for pgs "int_tf_never_for pgs"
    by (rule int_never_is_sound_transfer_for)
  show "base_dg_exec_analysis pgs
          (int_tf_for mode pgs) (int_tf_st_for mode pgs) (int_dom_enter_st_for mode pgs)
          (resolved_st_q_is_bot_for (declared_global_vars p))
          TD_side_always_join_Interp.solve TD_side_always_join_Interp.solve_c"
    unfolding Refine_Never int_tf_for.simps int_tf_st_for.simps int_dom_enter_st_for.simps
    by unfold_locales
       (rule reserved
             p_transfer.tf_sound_assign_for p_transfer.tf_sound_special_for
             p_transfer.tf_sound_branch_for
             p_transfer.tf_sound_enter_for p_transfer.tf_sound_combine_env_for
             int_tf_st_never_for_commute[folded fun_of_exec_dg_st_for_def]
             int_dom_enter_never_st_for_commute[folded fun_of_exec_dg_st_for_def]
             resolved_st_q_is_bot_for_iff[OF declared_global_iff, folded fun_of_exec_dg_st_for_def]
             action_reduces.ret_none[OF int_tf_st_never_for_reduces]
             action_reduces.ret_some[OF int_tf_st_never_for_reduces]
             action_reduces.check[OF int_tf_st_never_for_reduces]
             TD_side_always_join_Interp.part_post_solution_of_solve_c)+
next
  case Refine_Once
  interpret p_transfer: sound_transfer_for pgs "int_tf_once_for pgs"
    by (rule int_once_is_sound_transfer_for)
  show "base_dg_exec_analysis pgs
          (int_tf_for mode pgs) (int_tf_st_for mode pgs) (int_dom_enter_st_for mode pgs)
          (resolved_st_q_is_bot_for (declared_global_vars p))
          TD_side_always_join_Interp.solve TD_side_always_join_Interp.solve_c"
    unfolding Refine_Once int_tf_for.simps int_tf_st_for.simps int_dom_enter_st_for.simps
    by unfold_locales
       (rule reserved
             p_transfer.tf_sound_assign_for p_transfer.tf_sound_special_for
             p_transfer.tf_sound_branch_for
             p_transfer.tf_sound_enter_for p_transfer.tf_sound_combine_env_for
             int_tf_st_once_for_commute[folded fun_of_exec_dg_st_for_def]
             int_dom_enter_once_st_for_commute[folded fun_of_exec_dg_st_for_def]
             resolved_st_q_is_bot_for_iff[OF declared_global_iff, folded fun_of_exec_dg_st_for_def]
             action_reduces.ret_none[OF int_tf_st_once_for_reduces]
             action_reduces.ret_some[OF int_tf_st_once_for_reduces]
             action_reduces.check[OF int_tf_st_once_for_reduces]
             TD_side_always_join_Interp.part_post_solution_of_solve_c)+
next
  case Refine_Fixpoint
  interpret p_transfer: sound_transfer_for pgs "int_tf_fixpoint_for pgs"
    by (rule int_fixpoint_is_sound_transfer_for)
  show "base_dg_exec_analysis pgs
          (int_tf_for mode pgs) (int_tf_st_for mode pgs) (int_dom_enter_st_for mode pgs)
          (resolved_st_q_is_bot_for (declared_global_vars p))
          TD_side_always_join_Interp.solve TD_side_always_join_Interp.solve_c"
    unfolding Refine_Fixpoint int_tf_for.simps int_tf_st_for.simps int_dom_enter_st_for.simps
    by unfold_locales
       (rule reserved
             p_transfer.tf_sound_assign_for p_transfer.tf_sound_special_for
             p_transfer.tf_sound_branch_for
             p_transfer.tf_sound_enter_for p_transfer.tf_sound_combine_env_for
             int_tf_st_fixpoint_for_commute[folded fun_of_exec_dg_st_for_def]
             int_dom_enter_fixpoint_st_for_commute[folded fun_of_exec_dg_st_for_def]
             resolved_st_q_is_bot_for_iff[OF declared_global_iff, folded fun_of_exec_dg_st_for_def]
             action_reduces.ret_none[OF int_tf_st_fixpoint_for_reduces]
             action_reduces.ret_some[OF int_tf_st_fixpoint_for_reduces]
             action_reduces.check[OF int_tf_st_fixpoint_for_reduces]
             TD_side_always_join_Interp.part_post_solution_of_solve_c)+
qed

interpretation p_reg_per_origin:
  base_dg_exec_analysis pgs
    "int_tf_for mode pgs" "int_tf_st_for mode pgs" "int_dom_enter_st_for mode pgs"
    "resolved_st_q_is_bot_for (declared_global_vars p)"
    "TD_side_per_origin_Interp.solve" "TD_side_per_origin_Interp.solve_c"
proof (cases mode)
  case Refine_Never
  interpret p_transfer: sound_transfer_for pgs "int_tf_never_for pgs"
    by (rule int_never_is_sound_transfer_for)
  show "base_dg_exec_analysis pgs
          (int_tf_for mode pgs) (int_tf_st_for mode pgs) (int_dom_enter_st_for mode pgs)
          (resolved_st_q_is_bot_for (declared_global_vars p))
          TD_side_per_origin_Interp.solve TD_side_per_origin_Interp.solve_c"
    unfolding Refine_Never int_tf_for.simps int_tf_st_for.simps int_dom_enter_st_for.simps
    by unfold_locales
       (rule reserved
             p_transfer.tf_sound_assign_for p_transfer.tf_sound_special_for
             p_transfer.tf_sound_branch_for
             p_transfer.tf_sound_enter_for p_transfer.tf_sound_combine_env_for
             int_tf_st_never_for_commute[folded fun_of_exec_dg_st_for_def]
             int_dom_enter_never_st_for_commute[folded fun_of_exec_dg_st_for_def]
             resolved_st_q_is_bot_for_iff[OF declared_global_iff, folded fun_of_exec_dg_st_for_def]
             action_reduces.ret_none[OF int_tf_st_never_for_reduces]
             action_reduces.ret_some[OF int_tf_st_never_for_reduces]
             action_reduces.check[OF int_tf_st_never_for_reduces]
             TD_side_per_origin_Interp.part_post_solution_of_solve_c)+
next
  case Refine_Once
  interpret p_transfer: sound_transfer_for pgs "int_tf_once_for pgs"
    by (rule int_once_is_sound_transfer_for)
  show "base_dg_exec_analysis pgs
          (int_tf_for mode pgs) (int_tf_st_for mode pgs) (int_dom_enter_st_for mode pgs)
          (resolved_st_q_is_bot_for (declared_global_vars p))
          TD_side_per_origin_Interp.solve TD_side_per_origin_Interp.solve_c"
    unfolding Refine_Once int_tf_for.simps int_tf_st_for.simps int_dom_enter_st_for.simps
    by unfold_locales
       (rule reserved
             p_transfer.tf_sound_assign_for p_transfer.tf_sound_special_for
             p_transfer.tf_sound_branch_for
             p_transfer.tf_sound_enter_for p_transfer.tf_sound_combine_env_for
             int_tf_st_once_for_commute[folded fun_of_exec_dg_st_for_def]
             int_dom_enter_once_st_for_commute[folded fun_of_exec_dg_st_for_def]
             resolved_st_q_is_bot_for_iff[OF declared_global_iff, folded fun_of_exec_dg_st_for_def]
             action_reduces.ret_none[OF int_tf_st_once_for_reduces]
             action_reduces.ret_some[OF int_tf_st_once_for_reduces]
             action_reduces.check[OF int_tf_st_once_for_reduces]
             TD_side_per_origin_Interp.part_post_solution_of_solve_c)+
next
  case Refine_Fixpoint
  interpret p_transfer: sound_transfer_for pgs "int_tf_fixpoint_for pgs"
    by (rule int_fixpoint_is_sound_transfer_for)
  show "base_dg_exec_analysis pgs
          (int_tf_for mode pgs) (int_tf_st_for mode pgs) (int_dom_enter_st_for mode pgs)
          (resolved_st_q_is_bot_for (declared_global_vars p))
          TD_side_per_origin_Interp.solve TD_side_per_origin_Interp.solve_c"
    unfolding Refine_Fixpoint int_tf_for.simps int_tf_st_for.simps int_dom_enter_st_for.simps
    by unfold_locales
       (rule reserved
             p_transfer.tf_sound_assign_for p_transfer.tf_sound_special_for
             p_transfer.tf_sound_branch_for
             p_transfer.tf_sound_enter_for p_transfer.tf_sound_combine_env_for
             int_tf_st_fixpoint_for_commute[folded fun_of_exec_dg_st_for_def]
             int_dom_enter_fixpoint_st_for_commute[folded fun_of_exec_dg_st_for_def]
             resolved_st_q_is_bot_for_iff[OF declared_global_iff, folded fun_of_exec_dg_st_for_def]
             action_reduces.ret_none[OF int_tf_st_fixpoint_for_reduces]
             action_reduces.ret_some[OF int_tf_st_fixpoint_for_reduces]
             action_reduces.check[OF int_tf_st_fixpoint_for_reduces]
             TD_side_per_origin_Interp.part_post_solution_of_solve_c)+
qed

definition analyse_int_dg_gamma_join_for ::
  "(pp \<times> unit + unit \<Rightarrow> (int_dom exec_dg_st lifted, int_dom exec_dg_st lifted) dg_state) \<Rightarrow> pp \<Rightarrow> store set" where
  "analyse_int_dg_gamma_join_for = p_reg_join.gamma"

definition analyse_int_dg_gamma_per_origin_for ::
  "(pp \<times> unit + unit \<Rightarrow> (int_dom exec_dg_st lifted, int_dom exec_dg_st lifted) dg_state) \<Rightarrow> pp \<Rightarrow> store set" where
  "analyse_int_dg_gamma_per_origin_for = p_reg_per_origin.gamma"

text \<open>
  \<open>p_reg\<close>/\<open>p_reg_join\<close>/\<open>p_reg_per_origin\<close> are local to this context block, so their
  qualified constants do not survive past the closing \<open>end\<close> --- \<open>analyse_int_dg_gamma_for\<close>
  names \<open>p_reg\<close>'s fully-applied locale concretization once, mirroring
  \<open>analyse_interval_dg_gamma_for\<close>, so the soundness corollaries below can state their
  conclusion after the context closes. \<open>analyse_int_dg_gamma_join_for\<close>/
  \<open>_per_origin_for\<close> above do the same for the two solver-choice interpretations, in case a
  future corollary needs their own \<open>collect_sound\<close>; nothing downstream in this file yet
  consumes them, mirroring how Interval's own solver-choice interpretations exist as a
  soundness fact even before every possible downstream corollary is written against them.
\<close>

definition analyse_int_dg_gamma_for ::
  "(pp \<times> unit + unit \<Rightarrow> (int_dom exec_dg_st lifted, int_dom exec_dg_st lifted) dg_state) \<Rightarrow> pp \<Rightarrow> store set" where
  "analyse_int_dg_gamma_for = p_reg.gamma"

text \<open>
  The per-node collecting soundness connection: reuses \<open>base_dg_exec_analysis.collect_sound\<close>
  exactly as \<open>p_reg.collect_sound\<close> does for Interval, just with the solver-domain,
  well-formedness, and coverage facts left as hypotheses instead of discharged \<open>by eval\<close> ---
  a symbolic \<open>p\<close> cannot be run through the executable solver at proof time the way a
  hard-coded example program can.
\<close>

theorem analyse_int_dg_collect_sound_for:
  assumes solve: "TD_side_warrowing_apinis_Interp_solve_c
                    (analyse_int_dg_eqs_for mode (resolved_st_q_is_bot_for (declared_global_vars p)) pgs p)
                    (cfg_exit (prog_cfg prog_main_name p), ()) \<noteq> None"
      and wf: "wf_compile_input pgs (prog_table p) (prog_procs p) prog_main_name (prog_main p)"
      and cover_entry: "(cfg_entry (prog_cfg prog_main_name p), ()) \<in>
                           fst (analyse_int_dg_for mode (resolved_st_q_is_bot_for (declared_global_vars p)) pgs p)"
      and cover_edge:
        "\<And>u a w. (u, a, w) \<in> intra (prog_cfg prog_main_name p) \<Longrightarrow>
           (w, ()) \<in> fst (analyse_int_dg_for mode (resolved_st_q_is_bot_for (declared_global_vars p)) pgs p)"
      and cover_enter:
        "\<And>c dst fs as q k. (c, CallEdge dst fs as, FunctionEntry q, k) \<in> calls (prog_cfg prog_main_name p)
           \<Longrightarrow> (FunctionEntry q, ()) \<in> fst (analyse_int_dg_for mode (resolved_st_q_is_bot_for (declared_global_vars p)) pgs p)"
      and cover_combine:
        "\<And>c dst fs as q k. (c, CallEdge dst fs as, FunctionEntry q, k) \<in> calls (prog_cfg prog_main_name p)
           \<Longrightarrow> (k, ()) \<in> fst (analyse_int_dg_for mode (resolved_st_q_is_bot_for (declared_global_vars p)) pgs p)"
      and finI: "finite (intra (prog_cfg prog_main_name p))"
      and finC: "finite (calls (prog_cfg prog_main_name p))"
  shows "ltr_collect pgs (prog_cfg prog_main_name p) (cinit_stores pgs) v
           \<subseteq> analyse_int_dg_gamma_for
               (snd (analyse_int_dg_for mode (resolved_st_q_is_bot_for (declared_global_vars p)) pgs p)) v"
proof -
  have sound0:
    "cinit_stores pgs \<subseteq> gamma_dg_base (map_lift (fun_of_exec_dg_st_for pgs) (Lifted cinit_int_dom_st))
                          (map_lift (fun_of_exec_dg_st_for pgs) (Lifted cinit_int_dom_st))"
    by (auto simp: fun_of_exec_dg_st_for_def fun_of_st_cinit_int_dom_st_for cinit_stores_def
                  gamma_state_def gamma_dg_base_def gamma_int_dom_top)
  show ?thesis
    unfolding analyse_int_dg_gamma_for_def analyse_int_dg_for_def analyse_int_dg_eqs_for_def
              prog_cfg_def
    by (rule p_reg.collect_sound
          [OF solve[unfolded analyse_int_dg_eqs_for_def prog_cfg_def]
              wf
              vars_coverI[OF cover_entry[unfolded analyse_int_dg_for_def analyse_int_dg_eqs_for_def prog_cfg_def]
                             cover_edge[unfolded analyse_int_dg_for_def analyse_int_dg_eqs_for_def prog_cfg_def]
                             cover_enter[unfolded analyse_int_dg_for_def analyse_int_dg_eqs_for_def prog_cfg_def]
                             cover_combine[unfolded analyse_int_dg_for_def analyse_int_dg_eqs_for_def prog_cfg_def]]
              finI[unfolded prog_cfg_def] finC[unfolded prog_cfg_def]
              sound0])
qed

text \<open>
  \<open>p_reg\<close> is local, so its qualified constants (and the raw locale predicate
  \<open>base_dg_exec_analysis\<close>) do not survive past the closing \<open>end\<close> either ---
  \<open>analyse_int_dg_env_for\<close> reads the local unknown at \<open>v\<close> directly, and
  \<open>analyse_int_dg_gamma_eq_env_for\<close> proves it is exactly what \<open>analyse_int_dg_gamma_for\<close>
  already concretizes, mirroring \<open>analyse_interval_dg_gamma_eq_env_for\<close> --- via
  \<open>p_reg.gamma_def\<close> and \<open>p_reg.sds\<close>, not a new soundness argument.
\<close>

lemma analyse_int_dg_gamma_eq_env_for:
  "analyse_int_dg_gamma_for
     (snd (analyse_int_dg_for mode (resolved_st_q_is_bot_for (declared_global_vars p)) pgs p)) v
     = \<lbrakk>analyse_int_dg_env_for mode (resolved_st_q_is_bot_for (declared_global_vars p)) pgs p v\<rbrakk>"
  unfolding analyse_int_dg_gamma_for_def analyse_int_dg_env_for_def
  by (simp add: p_reg.gamma_def
                sound_dg_spec.dg_gamma_def[OF p_reg.sds[unfolded sound_dg_spec_ltr_for_def]]
                sound_dg_spec.dg_D_def[OF p_reg.sds[unfolded sound_dg_spec_ltr_for_def]]
                gamma_dg_base_def fun_of_dg_st_gen_def gamma_state_bot
         split: lifted.splits)

text \<open>
  The corollary the CLI's exported \<open>unreachable\<close> flag
  (\<^const>\<open>resolved_st_q_lifted_is_bot_for\<close>, \<^theory>\<open>Voblint_Core.Exec_St\<close>) needs,
  mirroring \<open>analyse_sign_report_unreachable_sound_for\<close>'s Sign counterpart:
  when that flag holds at a report entry's own solved local unknown, the
  point is genuinely unreachable under the collecting semantics, not merely
  witness-bottom by construction.
\<close>

theorem analyse_int_report_unreachable_sound_for:
  assumes solve: "TD_side_warrowing_apinis_Interp_solve_c
                    (analyse_int_dg_eqs_for mode (resolved_st_q_is_bot_for (declared_global_vars p)) pgs p)
                    (cfg_exit (prog_cfg prog_main_name p), ()) \<noteq> None"
      and wf: "wf_compile_input pgs (prog_table p) (prog_procs p) prog_main_name (prog_main p)"
      and cover_entry: "(cfg_entry (prog_cfg prog_main_name p), ()) \<in>
                           fst (analyse_int_dg_for mode (resolved_st_q_is_bot_for (declared_global_vars p)) pgs p)"
      and cover_edge:
        "\<And>u a w. (u, a, w) \<in> intra (prog_cfg prog_main_name p) \<Longrightarrow>
           (w, ()) \<in> fst (analyse_int_dg_for mode (resolved_st_q_is_bot_for (declared_global_vars p)) pgs p)"
      and cover_enter:
        "\<And>c dst fs as q k. (c, CallEdge dst fs as, FunctionEntry q, k) \<in> calls (prog_cfg prog_main_name p)
           \<Longrightarrow> (FunctionEntry q, ()) \<in> fst (analyse_int_dg_for mode (resolved_st_q_is_bot_for (declared_global_vars p)) pgs p)"
      and cover_combine:
        "\<And>c dst fs as q k. (c, CallEdge dst fs as, FunctionEntry q, k) \<in> calls (prog_cfg prog_main_name p)
           \<Longrightarrow> (k, ()) \<in> fst (analyse_int_dg_for mode (resolved_st_q_is_bot_for (declared_global_vars p)) pgs p)"
      and finI: "finite (intra (prog_cfg prog_main_name p))"
      and finC: "finite (calls (prog_cfg prog_main_name p))"
      and unreachable: "resolved_st_q_lifted_is_bot_for (declared_global_vars p)
        (locals (snd (analyse_int_dg_for mode (resolved_st_q_is_bot_for (declared_global_vars p)) pgs p) (Inl (v, ()))))"
  shows "ltr_collect pgs (prog_cfg prog_main_name p) (cinit_stores pgs) v = {}"
proof -
  have node_sound: "ltr_collect pgs (prog_cfg prog_main_name p) (cinit_stores pgs) v
      \<subseteq> \<lbrakk>analyse_int_dg_env_for mode (resolved_st_q_is_bot_for (declared_global_vars p)) pgs p v\<rbrakk>"
    using analyse_int_dg_collect_sound_for[OF solve wf cover_entry cover_edge cover_enter cover_combine finI finC]
    unfolding analyse_int_dg_gamma_eq_env_for .
  have empty: "\<lbrakk>analyse_int_dg_env_for mode (resolved_st_q_is_bot_for (declared_global_vars p)) pgs p v\<rbrakk> = {}"
    using unreachable[unfolded resolved_st_q_lifted_is_bot_for_iff[OF declared_global_iff]
                                is_bot_state_lift_iff]
    unfolding analyse_int_dg_env_for_def
    by (cases "map_lift (fun_of_exec_dg_st_for pgs)
                 (locals (snd (analyse_int_dg_for mode (resolved_st_q_is_bot_for (declared_global_vars p)) pgs p) (Inl (v, ()))))")
       (simp_all add: gamma_state_bot fun_of_exec_dg_st_for_def)
  from node_sound empty show ?thesis by blast
qed

text \<open>
  \<open>analyse_int_report_for\<close> (\<^theory>\<open>Voblint_Analysis.Int_Checks\<close>) reads its per-node state
  through its \<open>monovariant_analysis_result_for\<close> table's \<^const>\<open>lookup_context\<close> rather than
  through \<open>analyse_int_dg_env_for\<close> directly. \<open>analyse_int_result_node_sound_for\<close> below is
  the node-soundness bridge across that boundary, mirroring
  \<open>analyse_sign_result_node_sound_for\<close>: the two envs' concretizations agree at every genuine
  CFG node, not merely a solver-covered one, because the monovariant table's key domain is
  \<^const>\<open>cfg_node_list\<close> itself, and \<open>gamma_point_normalize_point_canonicalize_lift\<close>
  transports the raw concretization across \<^const>\<open>canonicalize_lift\<close>/\<open>normalize_point\<close>
  unconditionally.
\<close>

lemma analyse_int_result_node_sound_for:
  assumes solve: "TD_side_warrowing_apinis_Interp_solve_c
                    (analyse_int_dg_eqs_for mode (resolved_st_q_is_bot_for (declared_global_vars p)) pgs p)
                    (cfg_exit (prog_cfg prog_main_name p), ()) \<noteq> None"
      and wf: "wf_compile_input pgs (prog_table p) (prog_procs p) prog_main_name (prog_main p)"
      and cover_entry: "(cfg_entry (prog_cfg prog_main_name p), ()) \<in>
                           fst (analyse_int_dg_for mode (resolved_st_q_is_bot_for (declared_global_vars p)) pgs p)"
      and cover_edge:
        "\<And>u a w. (u, a, w) \<in> intra (prog_cfg prog_main_name p) \<Longrightarrow>
           (w, ()) \<in> fst (analyse_int_dg_for mode (resolved_st_q_is_bot_for (declared_global_vars p)) pgs p)"
      and cover_enter:
        "\<And>c dst fs as q k. (c, CallEdge dst fs as, FunctionEntry q, k) \<in> calls (prog_cfg prog_main_name p)
           \<Longrightarrow> (FunctionEntry q, ()) \<in> fst (analyse_int_dg_for mode (resolved_st_q_is_bot_for (declared_global_vars p)) pgs p)"
      and cover_combine:
        "\<And>c dst fs as q k. (c, CallEdge dst fs as, FunctionEntry q, k) \<in> calls (prog_cfg prog_main_name p)
           \<Longrightarrow> (k, ()) \<in> fst (analyse_int_dg_for mode (resolved_st_q_is_bot_for (declared_global_vars p)) pgs p)"
      and finI: "finite (intra (prog_cfg prog_main_name p))"
      and finC: "finite (calls (prog_cfg prog_main_name p))"
      and node: "v \<in> cfg_nodes (prog_cfg prog_main_name p)"
  shows "ltr_collect pgs (prog_cfg prog_main_name p) (cinit_stores pgs) v
           \<subseteq> gamma_state (case lookup_context
                                (monovariant_analysis_result_for
                                   (\<lambda>gs p. analyse_int_dg_for mode (resolved_st_q_is_bot_for (declared_global_vars p)) gs p) pgs p)
                                v ()
                           of Unreachable \<Rightarrow> bot | Reachable st \<Rightarrow> st)"
proof -
  have old_sound: "ltr_collect pgs (prog_cfg prog_main_name p) (cinit_stores pgs) v
      \<subseteq> \<lbrakk>analyse_int_dg_env_for mode (resolved_st_q_is_bot_for (declared_global_vars p)) pgs p v\<rbrakk>"
    using analyse_int_dg_collect_sound_for[OF solve wf cover_entry cover_edge cover_enter cover_combine finI finC]
    unfolding analyse_int_dg_gamma_eq_env_for .
  have mem_keys: "v \<in> set (cfg_node_list (prog_cfg prog_main_name p))"
    using node finI finC by simp
  have lookup_eq: "lookup_context
      (monovariant_analysis_result_for
         (\<lambda>gs p. analyse_int_dg_for mode (resolved_st_q_is_bot_for (declared_global_vars p)) gs p) pgs p)
      v () =
      normalize_point pgs (canonicalize_lift (resolved_st_q_is_bot_for (declared_global_vars p))
        (locals (snd (analyse_int_dg_for mode (resolved_st_q_is_bot_for (declared_global_vars p)) pgs p) (Inl (v, ())))))"
    by (simp add: lookup_context_monovariant_analysis_result_for mem_keys)
  have bot_sound: "\<And>s. resolved_st_q_is_bot_for (declared_global_vars p) s
      \<Longrightarrow> is_bot_state (fun_of_resolved_st_q_for pgs s)"
    using resolved_st_q_is_bot_for_iff[OF declared_global_iff] by blast
  have raw_eq: "gamma_point
      (lookup_context
         (monovariant_analysis_result_for
            (\<lambda>gs p. analyse_int_dg_for mode (resolved_st_q_is_bot_for (declared_global_vars p)) gs p) pgs p)
         v ()) =
      \<lbrakk>analyse_int_dg_env_for mode (resolved_st_q_is_bot_for (declared_global_vars p)) pgs p v\<rbrakk>"
  proof -
    let ?q = "locals (snd (analyse_int_dg_for mode (resolved_st_q_is_bot_for (declared_global_vars p)) pgs p) (Inl (v, ())))"
    have step1: "gamma_point
        (lookup_context
           (monovariant_analysis_result_for
              (\<lambda>gs p. analyse_int_dg_for mode (resolved_st_q_is_bot_for (declared_global_vars p)) gs p) pgs p)
           v ()) =
        gamma_state_lift (map_lift (fun_of_resolved_st_q_for pgs) ?q)"
      unfolding lookup_eq
      by (rule gamma_point_normalize_point_canonicalize_lift[OF bot_sound])
    have step2: "gamma_state_lift (map_lift (fun_of_resolved_st_q_for pgs) ?q) =
        \<lbrakk>analyse_int_dg_env_for mode (resolved_st_q_is_bot_for (declared_global_vars p)) pgs p v\<rbrakk>"
      unfolding analyse_int_dg_env_for_def fun_of_exec_dg_st_for_def
      by (cases ?q) (simp_all add: gamma_state_bot)
    from step1 step2 show ?thesis by simp
  qed
  show ?thesis
    unfolding gamma_state_of_reachable_env raw_eq
    by (rule old_sound)
qed

theorem analyse_int_report_sound_proved_for:
  fixes v :: pp and c :: exp
  assumes solve: "TD_side_warrowing_apinis_Interp_solve_c
                    (analyse_int_dg_eqs_for mode (resolved_st_q_is_bot_for (declared_global_vars p)) pgs p)
                    (cfg_exit (prog_cfg prog_main_name p), ()) \<noteq> None"
      and wf: "wf_compile_input pgs (prog_table p) (prog_procs p) prog_main_name (prog_main p)"
      and cover_entry: "(cfg_entry (prog_cfg prog_main_name p), ()) \<in>
                           fst (analyse_int_dg_for mode (resolved_st_q_is_bot_for (declared_global_vars p)) pgs p)"
      and cover_edge:
        "\<And>u a w. (u, a, w) \<in> intra (prog_cfg prog_main_name p) \<Longrightarrow>
           (w, ()) \<in> fst (analyse_int_dg_for mode (resolved_st_q_is_bot_for (declared_global_vars p)) pgs p)"
      and cover_enter:
        "\<And>c dst fs as q k. (c, CallEdge dst fs as, FunctionEntry q, k) \<in> calls (prog_cfg prog_main_name p)
           \<Longrightarrow> (FunctionEntry q, ()) \<in> fst (analyse_int_dg_for mode (resolved_st_q_is_bot_for (declared_global_vars p)) pgs p)"
      and cover_combine:
        "\<And>c dst fs as q k. (c, CallEdge dst fs as, FunctionEntry q, k) \<in> calls (prog_cfg prog_main_name p)
           \<Longrightarrow> (k, ()) \<in> fst (analyse_int_dg_for mode (resolved_st_q_is_bot_for (declared_global_vars p)) pgs p)"
      and finI: "finite (intra (prog_cfg prog_main_name p))"
      and finC: "finite (calls (prog_cfg prog_main_name p))"
      and mem: "(v, c, Check_Proved) \<in> set (analyse_int_report_for mode pgs p)"
  shows "\<forall>s \<in> ltr_collect pgs (prog_cfg prog_main_name p) (cinit_stores pgs) v. truthy (aval c s)"
proof -
  obtain tgt where edge: "(v, EA_Check c, tgt) \<in> intra (prog_cfg prog_main_name p)"
    using mem[unfolded analyse_int_report_for_def Let_def]
          classify_checks_mem_iff[OF finI, of v c Check_Proved
            "\<lambda>v. case lookup_context
                       (monovariant_analysis_result_for
                          (\<lambda>gs p. analyse_int_dg_for mode (resolved_st_q_is_bot_for (declared_global_vars p)) gs p) pgs p)
                       v ()
                 of Unreachable \<Rightarrow> bot | Reachable st \<Rightarrow> st"
            int_classify_check]
    by auto
  have node: "v \<in> cfg_nodes (prog_cfg prog_main_name p)"
    using intra_endpoints_in_nodes(1)[OF edge] .
  have node_sound: "ltr_collect pgs (prog_cfg prog_main_name p) (cinit_stores pgs) v
      \<subseteq> gamma_state (case lookup_context
                           (monovariant_analysis_result_for
                              (\<lambda>gs p. analyse_int_dg_for mode (resolved_st_q_is_bot_for (declared_global_vars p)) gs p) pgs p)
                           v ()
                      of Unreachable \<Rightarrow> bot | Reachable st \<Rightarrow> st)"
    by (rule analyse_int_result_node_sound_for
          [OF solve wf cover_entry cover_edge cover_enter cover_combine finI finC node])
  show ?thesis
    by (rule classify_checks_proved_sound
          [where g = "prog_cfg prog_main_name p"
             and env = "\<lambda>v. case lookup_context
                                  (monovariant_analysis_result_for
                                     (\<lambda>gs p. analyse_int_dg_for mode (resolved_st_q_is_bot_for (declared_global_vars p)) gs p) pgs p)
                                  v ()
                            of Unreachable \<Rightarrow> bot | Reachable st \<Rightarrow> st"
             and classify = int_classify_check
             and reach = "ltr_collect pgs (prog_cfg prog_main_name p) (cinit_stores pgs)"
             and v = v and gamma_state = "gamma_state :: int_dom abs_state \<Rightarrow> store set",
           OF finI mem[unfolded analyse_int_report_for_def Let_def] int_classify_check_proved node_sound])
qed

theorem analyse_int_report_sound_refuted_for:
  fixes v :: pp and c :: exp
  assumes solve: "TD_side_warrowing_apinis_Interp_solve_c
                    (analyse_int_dg_eqs_for mode (resolved_st_q_is_bot_for (declared_global_vars p)) pgs p)
                    (cfg_exit (prog_cfg prog_main_name p), ()) \<noteq> None"
      and wf: "wf_compile_input pgs (prog_table p) (prog_procs p) prog_main_name (prog_main p)"
      and cover_entry: "(cfg_entry (prog_cfg prog_main_name p), ()) \<in>
                           fst (analyse_int_dg_for mode (resolved_st_q_is_bot_for (declared_global_vars p)) pgs p)"
      and cover_edge:
        "\<And>u a w. (u, a, w) \<in> intra (prog_cfg prog_main_name p) \<Longrightarrow>
           (w, ()) \<in> fst (analyse_int_dg_for mode (resolved_st_q_is_bot_for (declared_global_vars p)) pgs p)"
      and cover_enter:
        "\<And>c dst fs as q k. (c, CallEdge dst fs as, FunctionEntry q, k) \<in> calls (prog_cfg prog_main_name p)
           \<Longrightarrow> (FunctionEntry q, ()) \<in> fst (analyse_int_dg_for mode (resolved_st_q_is_bot_for (declared_global_vars p)) pgs p)"
      and cover_combine:
        "\<And>c dst fs as q k. (c, CallEdge dst fs as, FunctionEntry q, k) \<in> calls (prog_cfg prog_main_name p)
           \<Longrightarrow> (k, ()) \<in> fst (analyse_int_dg_for mode (resolved_st_q_is_bot_for (declared_global_vars p)) pgs p)"
      and finI: "finite (intra (prog_cfg prog_main_name p))"
      and finC: "finite (calls (prog_cfg prog_main_name p))"
      and mem: "(v, c, Check_Refuted) \<in> set (analyse_int_report_for mode pgs p)"
  shows "\<forall>s \<in> ltr_collect pgs (prog_cfg prog_main_name p) (cinit_stores pgs) v. \<not> truthy (aval c s)"
proof -
  obtain tgt where edge: "(v, EA_Check c, tgt) \<in> intra (prog_cfg prog_main_name p)"
    using mem[unfolded analyse_int_report_for_def Let_def]
          classify_checks_mem_iff[OF finI, of v c Check_Refuted
            "\<lambda>v. case lookup_context
                       (monovariant_analysis_result_for
                          (\<lambda>gs p. analyse_int_dg_for mode (resolved_st_q_is_bot_for (declared_global_vars p)) gs p) pgs p)
                       v ()
                 of Unreachable \<Rightarrow> bot | Reachable st \<Rightarrow> st"
            int_classify_check]
    by auto
  have node: "v \<in> cfg_nodes (prog_cfg prog_main_name p)"
    using intra_endpoints_in_nodes(1)[OF edge] .
  have node_sound: "ltr_collect pgs (prog_cfg prog_main_name p) (cinit_stores pgs) v
      \<subseteq> gamma_state (case lookup_context
                           (monovariant_analysis_result_for
                              (\<lambda>gs p. analyse_int_dg_for mode (resolved_st_q_is_bot_for (declared_global_vars p)) gs p) pgs p)
                           v ()
                      of Unreachable \<Rightarrow> bot | Reachable st \<Rightarrow> st)"
    by (rule analyse_int_result_node_sound_for
          [OF solve wf cover_entry cover_edge cover_enter cover_combine finI finC node])
  show ?thesis
    by (rule classify_checks_refuted_sound
          [where g = "prog_cfg prog_main_name p"
             and env = "\<lambda>v. case lookup_context
                                  (monovariant_analysis_result_for
                                     (\<lambda>gs p. analyse_int_dg_for mode (resolved_st_q_is_bot_for (declared_global_vars p)) gs p) pgs p)
                                  v ()
                            of Unreachable \<Rightarrow> bot | Reachable st \<Rightarrow> st"
             and classify = int_classify_check
             and reach = "ltr_collect pgs (prog_cfg prog_main_name p) (cinit_stores pgs)"
             and v = v and gamma_state = "gamma_state :: int_dom abs_state \<Rightarrow> store set",
           OF finI mem[unfolded analyse_int_report_for_def Let_def] int_classify_check_refuted node_sound])
qed

end

text \<open>
  \<open>analyse_int_dg_eqs\<close>/\<open>analyse_int_dg\<close> (\<^theory>\<open>Voblint_Analysis.Int_Exec_Sound\<close>) and
  \<open>analyse_int_report\<close> (\<^theory>\<open>Voblint_Analysis.Int_Checks\<close>) are the \<^const>\<open>declared_global\<close>
  \<open>p\<close> convenience instances the context above's \<open>_for\<close> layer already feeds, matching
  \<open>analyse_interval_td_report_sound_proved\<close>'s own shape. \<open>wf[THEN wf_compile_input_reserved_ret_var]\<close>
  discharges the context's \<open>reserved\<close> assumption from the concrete program's own
  well-formedness fact --- the same instantiation step Interval's own corollary uses.
\<close>

corollary analyse_int_report_sound_proved:
  fixes p :: imp_prog and v :: pp and c :: exp
  assumes solve: "TD_side_warrowing_apinis_Interp_solve_c (analyse_int_dg_eqs Refine_Fixpoint p)
                    (cfg_exit (prog_cfg prog_main_name p), ()) \<noteq> None"
      and wf: "wf_compile_input (declared_global p) (prog_table p) (prog_procs p) prog_main_name (prog_main p)"
      and cover_entry: "(cfg_entry (prog_cfg prog_main_name p), ()) \<in> fst (analyse_int_dg Refine_Fixpoint p)"
      and cover_edge:
        "\<And>u a w. (u, a, w) \<in> intra (prog_cfg prog_main_name p) \<Longrightarrow> (w, ()) \<in> fst (analyse_int_dg Refine_Fixpoint p)"
      and cover_enter:
        "\<And>c dst fs as q k. (c, CallEdge dst fs as, FunctionEntry q, k) \<in> calls (prog_cfg prog_main_name p)
           \<Longrightarrow> (FunctionEntry q, ()) \<in> fst (analyse_int_dg Refine_Fixpoint p)"
      and cover_combine:
        "\<And>c dst fs as q k. (c, CallEdge dst fs as, FunctionEntry q, k) \<in> calls (prog_cfg prog_main_name p)
           \<Longrightarrow> (k, ()) \<in> fst (analyse_int_dg Refine_Fixpoint p)"
      and finI: "finite (intra (prog_cfg prog_main_name p))"
      and finC: "finite (calls (prog_cfg prog_main_name p))"
      and mem: "(v, c, Check_Proved) \<in> set (analyse_int_report p)"
  shows "\<forall>s \<in> ltr_collect (declared_global p) (prog_cfg prog_main_name p) (cinit_stores (declared_global p)) v.
           truthy (aval c s)"
  unfolding analyse_int_report_def analyse_int_dg_eqs_def
  by (rule analyse_int_report_sound_proved_for
        [OF wf[THEN wf_compile_input_reserved_ret_var]
            solve[unfolded analyse_int_dg_eqs_def]
            wf
            cover_entry[unfolded analyse_int_dg_def]
            cover_edge[unfolded analyse_int_dg_def]
            cover_enter[unfolded analyse_int_dg_def]
            cover_combine[unfolded analyse_int_dg_def]
            finI finC mem[unfolded analyse_int_report_def]])

corollary analyse_int_report_sound_refuted:
  fixes p :: imp_prog and v :: pp and c :: exp
  assumes solve: "TD_side_warrowing_apinis_Interp_solve_c (analyse_int_dg_eqs Refine_Fixpoint p)
                    (cfg_exit (prog_cfg prog_main_name p), ()) \<noteq> None"
      and wf: "wf_compile_input (declared_global p) (prog_table p) (prog_procs p) prog_main_name (prog_main p)"
      and cover_entry: "(cfg_entry (prog_cfg prog_main_name p), ()) \<in> fst (analyse_int_dg Refine_Fixpoint p)"
      and cover_edge:
        "\<And>u a w. (u, a, w) \<in> intra (prog_cfg prog_main_name p) \<Longrightarrow> (w, ()) \<in> fst (analyse_int_dg Refine_Fixpoint p)"
      and cover_enter:
        "\<And>c dst fs as q k. (c, CallEdge dst fs as, FunctionEntry q, k) \<in> calls (prog_cfg prog_main_name p)
           \<Longrightarrow> (FunctionEntry q, ()) \<in> fst (analyse_int_dg Refine_Fixpoint p)"
      and cover_combine:
        "\<And>c dst fs as q k. (c, CallEdge dst fs as, FunctionEntry q, k) \<in> calls (prog_cfg prog_main_name p)
           \<Longrightarrow> (k, ()) \<in> fst (analyse_int_dg Refine_Fixpoint p)"
      and finI: "finite (intra (prog_cfg prog_main_name p))"
      and finC: "finite (calls (prog_cfg prog_main_name p))"
      and mem: "(v, c, Check_Refuted) \<in> set (analyse_int_report p)"
  shows "\<forall>s \<in> ltr_collect (declared_global p) (prog_cfg prog_main_name p) (cinit_stores (declared_global p)) v.
           \<not> truthy (aval c s)"
  unfolding analyse_int_report_def analyse_int_dg_eqs_def
  by (rule analyse_int_report_sound_refuted_for
        [OF wf[THEN wf_compile_input_reserved_ret_var]
            solve[unfolded analyse_int_dg_eqs_def]
            wf
            cover_entry[unfolded analyse_int_dg_def]
            cover_edge[unfolded analyse_int_dg_def]
            cover_enter[unfolded analyse_int_dg_def]
            cover_combine[unfolded analyse_int_dg_def]
            finI finC mem[unfolded analyse_int_report_def]])

end
