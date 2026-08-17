theory Example_Interval_Codegen
  imports Exec_Ivl_Run Voblint_Analysis.Interval_Checks "Voblint_Formalization.Run_Analysis_Sound"
begin

section \<open>Interval codegen API: an arbitrary VIMP program, and its production soundness\<close>

text \<open>
  Mirrors Sign's \<open>Example_Sign_Codegen\<close>: \<open>analyse_interval_dg_eqs_for\<close>/
  \<open>analyse_interval_dg_for\<close>/\<open>analyse_interval_dg_env_for\<close> (\<^theory>\<open>Voblint_Analysis.Interval_Exec_Sound\<close>)
  and \<open>analyse_interval_td_report_for\<close>/\<open>analyse_interval_td_report\<close>
  (\<^theory>\<open>Voblint_Analysis.Interval_Checks\<close>) are pure computation, no dependence on the
  \<open>base_dg_exec_analysis\<close> locale interpreted below, so they live one session earlier
  (Analysis). Only the soundness half needs that locale, one session later than Analysis
  in the locked six-session chain, so it lives here.

  Unlike Sign, Interval's local carrier has infinite height (an unbounded integer bound),
  so this interpretation solves via \<^const>\<open>TD_side_warrowing_apinis_Interp.solve\<close>/
  \<open>.solve_c\<close> instead of the always-join rule Sign uses --- \<open>base_dg_exec_analysis\<close> is
  generic in the solver, so this is a like-for-like swap of the locale's \<open>solve\<close>/
  \<open>solve_c\<close> parameters, not a different registration shape.
\<close>

context
  fixes p :: imp_prog
  assumes reserved: "reserved_ret_var (declared_global p)"
begin

abbreviation pgs :: "vname \<Rightarrow> bool" where "pgs \<equiv> declared_global p"

interpretation p_reg:
  base_dg_exec_analysis pgs
    "ivl_tf_for pgs" "ivl_tf_st_for pgs" "ivl_enter_st_for pgs"
    "resolved_st_q_is_bot_for (declared_global_vars p)"
    "TD_side_warrowing_apinis_Interp.solve" "TD_side_warrowing_apinis_Interp.solve_c"
proof -
  interpret p_transfer: sound_transfer_for pgs "ivl_tf_for pgs"
    by (rule ivl_is_sound_transfer_for)
  show "base_dg_exec_analysis pgs (ivl_tf_for pgs)
          (ivl_tf_st_for pgs) (ivl_enter_st_for pgs) (resolved_st_q_is_bot_for (declared_global_vars p))
          TD_side_warrowing_apinis_Interp.solve TD_side_warrowing_apinis_Interp.solve_c"
    by unfold_locales
       (rule reserved
             p_transfer.tf_sound_assign_for p_transfer.tf_sound_special_for
             p_transfer.tf_sound_branch_for
             p_transfer.tf_sound_enter_for p_transfer.tf_sound_combine_env_for
             ivl_tf_st_for_commute[folded fun_of_exec_dg_st_for_def]
             ivl_enter_st_for_commute[folded fun_of_exec_dg_st_for_def]
             resolved_st_q_is_bot_for_iff[OF declared_global_iff, folded fun_of_exec_dg_st_for_def]
             action_reduces.ret_none[OF ivl_tf_st_for_reduces]
             action_reduces.ret_some[OF ivl_tf_st_for_reduces]
             action_reduces.check[OF ivl_tf_st_for_reduces]
             TD_side_warrowing_apinis_Interp.part_post_solution_of_solve_c)+
qed

text \<open>
  \<open>p_reg\<close> is local to this context block, so its qualified constants do not survive past
  the closing \<open>end\<close> --- \<open>analyse_interval_dg_gamma_for\<close> names the fully-applied locale
  concretization once, mirroring \<open>analyse_sign_gamma_for\<close>, so the soundness corollaries
  below can state their conclusion after the context closes.
\<close>

definition analyse_interval_dg_gamma_for ::
  "(pp \<times> unit + unit \<Rightarrow> (ivl exec_dg_st lifted, ivl exec_dg_st lifted) dg_state) \<Rightarrow> pp \<Rightarrow> store set" where
  "analyse_interval_dg_gamma_for = p_reg.gamma"

text \<open>
  The per-node collecting soundness connection: reuses
  \<open>base_dg_exec_analysis.collect_sound\<close> exactly as \<open>flagship_ex_reg.run_source_sound\<close> does
  in \<open>Example_Interval_DG_Flagship\<close>, just with the solver-domain, well-formedness, and
  coverage facts left as hypotheses instead of discharged \<open>by eval\<close> --- a symbolic \<open>p\<close>
  cannot be run through the executable solver at proof time the way a hard-coded example
  program can. \<open>sound0\<close> stays internal: it never depends on the program, only on
  \<open>cinit_ivl_st\<close> and the classifier.
\<close>

theorem analyse_interval_dg_collect_sound_for:
  assumes solve: "TD_side_warrowing_apinis_Interp_solve_c
                    (analyse_interval_dg_eqs_for (resolved_st_q_is_bot_for (declared_global_vars p)) pgs p)
                    (cfg_exit (prog_cfg prog_main_name p), ()) \<noteq> None"
      and wf: "wf_compile_input pgs (prog_table p) (prog_procs p) prog_main_name (prog_main p)"
      and cover_entry: "(cfg_entry (prog_cfg prog_main_name p), ()) \<in>
                           fst (analyse_interval_dg_for (resolved_st_q_is_bot_for (declared_global_vars p)) pgs p)"
      and cover_edge:
        "\<And>u a w. (u, a, w) \<in> intra (prog_cfg prog_main_name p) \<Longrightarrow>
           (w, ()) \<in> fst (analyse_interval_dg_for (resolved_st_q_is_bot_for (declared_global_vars p)) pgs p)"
      and cover_enter:
        "\<And>c dst fs as q k. (c, CallEdge dst fs as, FunctionEntry q, k) \<in> calls (prog_cfg prog_main_name p)
           \<Longrightarrow> (FunctionEntry q, ()) \<in> fst (analyse_interval_dg_for (resolved_st_q_is_bot_for (declared_global_vars p)) pgs p)"
      and cover_combine:
        "\<And>c dst fs as q k. (c, CallEdge dst fs as, FunctionEntry q, k) \<in> calls (prog_cfg prog_main_name p)
           \<Longrightarrow> (k, ()) \<in> fst (analyse_interval_dg_for (resolved_st_q_is_bot_for (declared_global_vars p)) pgs p)"
      and finI: "finite (intra (prog_cfg prog_main_name p))"
      and finC: "finite (calls (prog_cfg prog_main_name p))"
  shows "ltr_collect pgs (prog_cfg prog_main_name p) (cinit_stores pgs) v
           \<subseteq> analyse_interval_dg_gamma_for
               (snd (analyse_interval_dg_for (resolved_st_q_is_bot_for (declared_global_vars p)) pgs p)) v"
proof -
  have sound0:
    "cinit_stores pgs \<subseteq> gamma_dg_base (map_lift (fun_of_exec_dg_st_for pgs) (Lifted cinit_ivl_st))
                          (map_lift (fun_of_exec_dg_st_for pgs) (Lifted cinit_ivl_st))"
    by (auto simp: fun_of_exec_dg_st_for_def fun_of_st_cinit_ivl_st_for cinit_stores_def
                  gamma_state_def gamma_dg_base_def)
  show ?thesis
    unfolding analyse_interval_dg_gamma_for_def analyse_interval_dg_for_def analyse_interval_dg_eqs_for_def
              prog_cfg_def
    by (rule p_reg.collect_sound
          [OF solve[unfolded analyse_interval_dg_eqs_for_def prog_cfg_def]
              wf
              vars_coverI[OF cover_entry[unfolded analyse_interval_dg_for_def analyse_interval_dg_eqs_for_def prog_cfg_def]
                             cover_edge[unfolded analyse_interval_dg_for_def analyse_interval_dg_eqs_for_def prog_cfg_def]
                             cover_enter[unfolded analyse_interval_dg_for_def analyse_interval_dg_eqs_for_def prog_cfg_def]
                             cover_combine[unfolded analyse_interval_dg_for_def analyse_interval_dg_eqs_for_def prog_cfg_def]]
              finI[unfolded prog_cfg_def] finC[unfolded prog_cfg_def]
              sound0])
qed

text \<open>
  \<open>p_reg\<close> is local, so its qualified constants (and the raw locale predicate
  \<open>base_dg_exec_analysis\<close>) do not survive past the closing \<open>end\<close> either ---
  \<open>analyse_interval_dg_env_for\<close> reads the local unknown at \<open>v\<close> directly, and
  \<open>analyse_interval_dg_gamma_eq_env_for\<close> proves it is exactly what
  \<open>analyse_interval_dg_gamma_for\<close> already concretizes, mirroring
  \<open>analyse_sign_gamma_eq_env_for\<close> --- via \<open>p_reg.gamma_def\<close> and \<open>p_reg.sds\<close>, not a new
  soundness argument.
\<close>

lemma analyse_interval_dg_gamma_eq_env_for:
  "analyse_interval_dg_gamma_for
     (snd (analyse_interval_dg_for (resolved_st_q_is_bot_for (declared_global_vars p)) pgs p)) v
     = \<lbrakk>analyse_interval_dg_env_for (resolved_st_q_is_bot_for (declared_global_vars p)) pgs p v\<rbrakk>"
  unfolding analyse_interval_dg_gamma_for_def analyse_interval_dg_env_for_def
  by (simp add: p_reg.gamma_def
                sound_dg_spec.dg_gamma_def[OF p_reg.sds[unfolded sound_dg_spec_ltr_for_def]]
                sound_dg_spec.dg_D_def[OF p_reg.sds[unfolded sound_dg_spec_ltr_for_def]]
                gamma_dg_base_def fun_of_dg_st_gen_def gamma_state_bot
         split: lifted.splits)

text \<open>
  Soundness for \<open>analyse_interval_td_report_for\<close> (\<^theory>\<open>Voblint_Analysis.Interval_Checks\<close>):
  reuses \<open>classify_checks_proved_sound\<close>/\<open>classify_checks_refuted_sound\<close>
  (\<^theory>\<open>Voblint_Core.Abstract_Checks\<close>, fully domain-generic already) with
  \<open>analyse_interval_dg_collect_sound_for\<close> and \<open>analyse_interval_dg_gamma_eq_env_for\<close> together
  supplying the one per-node fact each needs, mirroring \<open>analyse_sign_report_sound_proved_for\<close>/
  \<open>_refuted_for\<close>.
\<close>

theorem analyse_interval_td_report_sound_proved_for:
  fixes v :: pp and c :: exp
  assumes solve: "TD_side_warrowing_apinis_Interp_solve_c
                    (analyse_interval_dg_eqs_for (resolved_st_q_is_bot_for (declared_global_vars p)) pgs p)
                    (cfg_exit (prog_cfg prog_main_name p), ()) \<noteq> None"
      and wf: "wf_compile_input pgs (prog_table p) (prog_procs p) prog_main_name (prog_main p)"
      and cover_entry: "(cfg_entry (prog_cfg prog_main_name p), ()) \<in>
                           fst (analyse_interval_dg_for (resolved_st_q_is_bot_for (declared_global_vars p)) pgs p)"
      and cover_edge:
        "\<And>u a w. (u, a, w) \<in> intra (prog_cfg prog_main_name p) \<Longrightarrow>
           (w, ()) \<in> fst (analyse_interval_dg_for (resolved_st_q_is_bot_for (declared_global_vars p)) pgs p)"
      and cover_enter:
        "\<And>c dst fs as q k. (c, CallEdge dst fs as, FunctionEntry q, k) \<in> calls (prog_cfg prog_main_name p)
           \<Longrightarrow> (FunctionEntry q, ()) \<in> fst (analyse_interval_dg_for (resolved_st_q_is_bot_for (declared_global_vars p)) pgs p)"
      and cover_combine:
        "\<And>c dst fs as q k. (c, CallEdge dst fs as, FunctionEntry q, k) \<in> calls (prog_cfg prog_main_name p)
           \<Longrightarrow> (k, ()) \<in> fst (analyse_interval_dg_for (resolved_st_q_is_bot_for (declared_global_vars p)) pgs p)"
      and finI: "finite (intra (prog_cfg prog_main_name p))"
      and finC: "finite (calls (prog_cfg prog_main_name p))"
      and mem: "(v, c, Check_Proved) \<in> set (analyse_interval_td_report_for pgs p)"
  shows "\<forall>s \<in> ltr_collect pgs (prog_cfg prog_main_name p) (cinit_stores pgs) v. truthy (aval c s)"
proof -
  have node_sound: "ltr_collect pgs (prog_cfg prog_main_name p) (cinit_stores pgs) v
                       \<subseteq> \<lbrakk>analyse_interval_dg_env_for (resolved_st_q_is_bot_for (declared_global_vars p)) pgs p v\<rbrakk>"
    using analyse_interval_dg_collect_sound_for[OF solve wf cover_entry cover_edge cover_enter cover_combine finI finC]
    unfolding analyse_interval_dg_gamma_eq_env_for .
  show ?thesis
    by (rule classify_checks_proved_sound
          [where g = "prog_cfg prog_main_name p"
             and env = "analyse_interval_dg_env_for (resolved_st_q_is_bot_for (declared_global_vars p)) pgs p"
             and classify = interval_classify_check
             and reach = "ltr_collect pgs (prog_cfg prog_main_name p) (cinit_stores pgs)"
             and v = v and gamma_state = "gamma_state :: ivl abs_state \<Rightarrow> store set",
           OF finI mem[unfolded analyse_interval_td_report_for_def] interval_classify_check_proved node_sound])
qed

theorem analyse_interval_td_report_sound_refuted_for:
  fixes v :: pp and c :: exp
  assumes solve: "TD_side_warrowing_apinis_Interp_solve_c
                    (analyse_interval_dg_eqs_for (resolved_st_q_is_bot_for (declared_global_vars p)) pgs p)
                    (cfg_exit (prog_cfg prog_main_name p), ()) \<noteq> None"
      and wf: "wf_compile_input pgs (prog_table p) (prog_procs p) prog_main_name (prog_main p)"
      and cover_entry: "(cfg_entry (prog_cfg prog_main_name p), ()) \<in>
                           fst (analyse_interval_dg_for (resolved_st_q_is_bot_for (declared_global_vars p)) pgs p)"
      and cover_edge:
        "\<And>u a w. (u, a, w) \<in> intra (prog_cfg prog_main_name p) \<Longrightarrow>
           (w, ()) \<in> fst (analyse_interval_dg_for (resolved_st_q_is_bot_for (declared_global_vars p)) pgs p)"
      and cover_enter:
        "\<And>c dst fs as q k. (c, CallEdge dst fs as, FunctionEntry q, k) \<in> calls (prog_cfg prog_main_name p)
           \<Longrightarrow> (FunctionEntry q, ()) \<in> fst (analyse_interval_dg_for (resolved_st_q_is_bot_for (declared_global_vars p)) pgs p)"
      and cover_combine:
        "\<And>c dst fs as q k. (c, CallEdge dst fs as, FunctionEntry q, k) \<in> calls (prog_cfg prog_main_name p)
           \<Longrightarrow> (k, ()) \<in> fst (analyse_interval_dg_for (resolved_st_q_is_bot_for (declared_global_vars p)) pgs p)"
      and finI: "finite (intra (prog_cfg prog_main_name p))"
      and finC: "finite (calls (prog_cfg prog_main_name p))"
      and mem: "(v, c, Check_Refuted) \<in> set (analyse_interval_td_report_for pgs p)"
  shows "\<forall>s \<in> ltr_collect pgs (prog_cfg prog_main_name p) (cinit_stores pgs) v. \<not> truthy (aval c s)"
proof -
  have node_sound: "ltr_collect pgs (prog_cfg prog_main_name p) (cinit_stores pgs) v
                       \<subseteq> \<lbrakk>analyse_interval_dg_env_for (resolved_st_q_is_bot_for (declared_global_vars p)) pgs p v\<rbrakk>"
    using analyse_interval_dg_collect_sound_for[OF solve wf cover_entry cover_edge cover_enter cover_combine finI finC]
    unfolding analyse_interval_dg_gamma_eq_env_for .
  show ?thesis
    by (rule classify_checks_refuted_sound
          [where g = "prog_cfg prog_main_name p"
             and env = "analyse_interval_dg_env_for (resolved_st_q_is_bot_for (declared_global_vars p)) pgs p"
             and classify = interval_classify_check
             and reach = "ltr_collect pgs (prog_cfg prog_main_name p) (cinit_stores pgs)"
             and v = v and gamma_state = "gamma_state :: ivl abs_state \<Rightarrow> store set",
           OF finI mem[unfolded analyse_interval_td_report_for_def] interval_classify_check_refuted node_sound])
qed

end

text \<open>
  \<open>analyse_interval_dg_eqs\<close>/\<open>analyse_interval_dg\<close> (\<^theory>\<open>Voblint_Analysis.Interval_Exec_Sound\<close>)
  and \<open>analyse_interval_td_report\<close> (\<^theory>\<open>Voblint_Analysis.Interval_Checks\<close>) are the
  \<^const>\<open>declared_global\<close> \<open>p\<close> convenience instances the context above's \<open>_for\<close> layer already
  feeds, matching \<open>analyse_sign_sound\<close>/\<open>analyse_sign_report_sound_proved\<close>'s own shape.
  \<open>wf[THEN wf_compile_input_reserved_ret_var]\<close> discharges the context's \<open>reserved\<close>
  assumption from the concrete program's own well-formedness fact --- the same
  instantiation step \<open>analyse_sign_sound\<close> uses.
\<close>

corollary analyse_interval_td_report_sound_proved:
  fixes p :: imp_prog and v :: pp and c :: exp
  assumes solve: "TD_side_warrowing_apinis_Interp_solve_c (analyse_interval_dg_eqs p)
                    (cfg_exit (prog_cfg prog_main_name p), ()) \<noteq> None"
      and wf: "wf_compile_input (declared_global p) (prog_table p) (prog_procs p) prog_main_name (prog_main p)"
      and cover_entry: "(cfg_entry (prog_cfg prog_main_name p), ()) \<in> fst (analyse_interval_dg p)"
      and cover_edge:
        "\<And>u a w. (u, a, w) \<in> intra (prog_cfg prog_main_name p) \<Longrightarrow> (w, ()) \<in> fst (analyse_interval_dg p)"
      and cover_enter:
        "\<And>c dst fs as q k. (c, CallEdge dst fs as, FunctionEntry q, k) \<in> calls (prog_cfg prog_main_name p)
           \<Longrightarrow> (FunctionEntry q, ()) \<in> fst (analyse_interval_dg p)"
      and cover_combine:
        "\<And>c dst fs as q k. (c, CallEdge dst fs as, FunctionEntry q, k) \<in> calls (prog_cfg prog_main_name p)
           \<Longrightarrow> (k, ()) \<in> fst (analyse_interval_dg p)"
      and finI: "finite (intra (prog_cfg prog_main_name p))"
      and finC: "finite (calls (prog_cfg prog_main_name p))"
      and mem: "(v, c, Check_Proved) \<in> set (analyse_interval_td_report p)"
  shows "\<forall>s \<in> ltr_collect (declared_global p) (prog_cfg prog_main_name p) (cinit_stores (declared_global p)) v.
           truthy (aval c s)"
  unfolding analyse_interval_td_report_def analyse_interval_dg_eqs_def
  by (rule analyse_interval_td_report_sound_proved_for
        [OF wf[THEN wf_compile_input_reserved_ret_var]
            solve[unfolded analyse_interval_dg_eqs_def]
            wf
            cover_entry[unfolded analyse_interval_dg_def]
            cover_edge[unfolded analyse_interval_dg_def]
            cover_enter[unfolded analyse_interval_dg_def]
            cover_combine[unfolded analyse_interval_dg_def]
            finI finC mem[unfolded analyse_interval_td_report_def]])

corollary analyse_interval_td_report_sound_refuted:
  fixes p :: imp_prog and v :: pp and c :: exp
  assumes solve: "TD_side_warrowing_apinis_Interp_solve_c (analyse_interval_dg_eqs p)
                    (cfg_exit (prog_cfg prog_main_name p), ()) \<noteq> None"
      and wf: "wf_compile_input (declared_global p) (prog_table p) (prog_procs p) prog_main_name (prog_main p)"
      and cover_entry: "(cfg_entry (prog_cfg prog_main_name p), ()) \<in> fst (analyse_interval_dg p)"
      and cover_edge:
        "\<And>u a w. (u, a, w) \<in> intra (prog_cfg prog_main_name p) \<Longrightarrow> (w, ()) \<in> fst (analyse_interval_dg p)"
      and cover_enter:
        "\<And>c dst fs as q k. (c, CallEdge dst fs as, FunctionEntry q, k) \<in> calls (prog_cfg prog_main_name p)
           \<Longrightarrow> (FunctionEntry q, ()) \<in> fst (analyse_interval_dg p)"
      and cover_combine:
        "\<And>c dst fs as q k. (c, CallEdge dst fs as, FunctionEntry q, k) \<in> calls (prog_cfg prog_main_name p)
           \<Longrightarrow> (k, ()) \<in> fst (analyse_interval_dg p)"
      and finI: "finite (intra (prog_cfg prog_main_name p))"
      and finC: "finite (calls (prog_cfg prog_main_name p))"
      and mem: "(v, c, Check_Refuted) \<in> set (analyse_interval_td_report p)"
  shows "\<forall>s \<in> ltr_collect (declared_global p) (prog_cfg prog_main_name p) (cinit_stores (declared_global p)) v.
           \<not> truthy (aval c s)"
  unfolding analyse_interval_td_report_def analyse_interval_dg_eqs_def
  by (rule analyse_interval_td_report_sound_refuted_for
        [OF wf[THEN wf_compile_input_reserved_ret_var]
            solve[unfolded analyse_interval_dg_eqs_def]
            wf
            cover_entry[unfolded analyse_interval_dg_def]
            cover_edge[unfolded analyse_interval_dg_def]
            cover_enter[unfolded analyse_interval_dg_def]
            cover_combine[unfolded analyse_interval_dg_def]
            finI finC mem[unfolded analyse_interval_td_report_def]])

section \<open>Solver-choice soundness: join and per-origin update rules\<close>

text \<open>
  Mirrors the warrowing soundness block above exactly, one \<open>base_dg_exec_analysis\<close>
  interpretation per update rule --- the locale is generic in \<open>solve\<close>/\<open>solve_c\<close>, so swapping
  \<^const>\<open>TD_side_warrowing_apinis_Interp.solve\<close> for \<^const>\<open>TD_side_always_join_Interp.solve\<close> (here)
  and \<^const>\<open>TD_side_per_origin_Interp.solve\<close> (below) is a like-for-like registration, not a
  different proof shape. Sign's own soundness (\<open>Example_Sign_Codegen.analyse_sign_sound_for\<close>) is
  exactly this join interpretation already; Interval needed its own copy only because Interval's
  \<open>ivl_tf_for\<close>/\<open>ivl_tf_st_for\<close>/\<open>ivl_enter_st_for\<close> transfer facts differ from Sign's. Each block
  below writes \<^term>\<open>declared_global p\<close> out in full rather than reusing the \<open>pgs\<close> abbreviation:
  \<open>pgs\<close> is local to the first context block above and, once that block closes, its global residue
  takes \<open>p\<close> as an explicit argument, so a second same-named local abbreviation here would clash.
\<close>

context
  fixes p :: imp_prog
  assumes reserved: "reserved_ret_var (declared_global p)"
begin

interpretation p_reg_join:
  base_dg_exec_analysis "declared_global p"
    "ivl_tf_for (declared_global p)" "ivl_tf_st_for (declared_global p)" "ivl_enter_st_for (declared_global p)"
    "resolved_st_q_is_bot_for (declared_global_vars p)"
    "TD_side_always_join_Interp.solve" "TD_side_always_join_Interp.solve_c"
proof -
  interpret p_transfer: sound_transfer_for "declared_global p" "ivl_tf_for (declared_global p)"
    by (rule ivl_is_sound_transfer_for)
  show "base_dg_exec_analysis (declared_global p) (ivl_tf_for (declared_global p))
          (ivl_tf_st_for (declared_global p)) (ivl_enter_st_for (declared_global p))
          (resolved_st_q_is_bot_for (declared_global_vars p))
          TD_side_always_join_Interp.solve TD_side_always_join_Interp.solve_c"
    by unfold_locales
       (rule reserved
             p_transfer.tf_sound_assign_for p_transfer.tf_sound_special_for
             p_transfer.tf_sound_branch_for
             p_transfer.tf_sound_enter_for p_transfer.tf_sound_combine_env_for
             ivl_tf_st_for_commute[folded fun_of_exec_dg_st_for_def]
             ivl_enter_st_for_commute[folded fun_of_exec_dg_st_for_def]
             resolved_st_q_is_bot_for_iff[OF declared_global_iff, folded fun_of_exec_dg_st_for_def]
             action_reduces.ret_none[OF ivl_tf_st_for_reduces]
             action_reduces.ret_some[OF ivl_tf_st_for_reduces]
             action_reduces.check[OF ivl_tf_st_for_reduces]
             TD_side_always_join_Interp.part_post_solution_of_solve_c)+
qed

definition analyse_interval_dg_gamma_join_for ::
  "(pp \<times> unit + unit \<Rightarrow> (ivl exec_dg_st lifted, ivl exec_dg_st lifted) dg_state) \<Rightarrow> pp \<Rightarrow> store set" where
  "analyse_interval_dg_gamma_join_for = p_reg_join.gamma"

theorem analyse_interval_dg_collect_join_sound_for:
  assumes solve: "TD_side_always_join_Interp_solve_c
                    (analyse_interval_dg_eqs_for (resolved_st_q_is_bot_for (declared_global_vars p)) (declared_global p) p)
                    (cfg_exit (prog_cfg prog_main_name p), ()) \<noteq> None"
      and wf: "wf_compile_input (declared_global p) (prog_table p) (prog_procs p) prog_main_name (prog_main p)"
      and cover_entry: "(cfg_entry (prog_cfg prog_main_name p), ()) \<in>
                           fst (analyse_interval_dg_join_for (resolved_st_q_is_bot_for (declared_global_vars p)) (declared_global p) p)"
      and cover_edge:
        "\<And>u a w. (u, a, w) \<in> intra (prog_cfg prog_main_name p) \<Longrightarrow>
           (w, ()) \<in> fst (analyse_interval_dg_join_for (resolved_st_q_is_bot_for (declared_global_vars p)) (declared_global p) p)"
      and cover_enter:
        "\<And>c dst fs as q k. (c, CallEdge dst fs as, FunctionEntry q, k) \<in> calls (prog_cfg prog_main_name p)
           \<Longrightarrow> (FunctionEntry q, ()) \<in> fst (analyse_interval_dg_join_for (resolved_st_q_is_bot_for (declared_global_vars p)) (declared_global p) p)"
      and cover_combine:
        "\<And>c dst fs as q k. (c, CallEdge dst fs as, FunctionEntry q, k) \<in> calls (prog_cfg prog_main_name p)
           \<Longrightarrow> (k, ()) \<in> fst (analyse_interval_dg_join_for (resolved_st_q_is_bot_for (declared_global_vars p)) (declared_global p) p)"
      and finI: "finite (intra (prog_cfg prog_main_name p))"
      and finC: "finite (calls (prog_cfg prog_main_name p))"
  shows "ltr_collect (declared_global p) (prog_cfg prog_main_name p) (cinit_stores (declared_global p)) v
           \<subseteq> analyse_interval_dg_gamma_join_for
               (snd (analyse_interval_dg_join_for (resolved_st_q_is_bot_for (declared_global_vars p)) (declared_global p) p)) v"
proof -
  have sound0:
    "cinit_stores (declared_global p) \<subseteq> gamma_dg_base (map_lift (fun_of_exec_dg_st_for (declared_global p)) (Lifted cinit_ivl_st))
                          (map_lift (fun_of_exec_dg_st_for (declared_global p)) (Lifted cinit_ivl_st))"
    by (auto simp: fun_of_exec_dg_st_for_def fun_of_st_cinit_ivl_st_for cinit_stores_def
                  gamma_state_def gamma_dg_base_def)
  show ?thesis
    unfolding analyse_interval_dg_gamma_join_for_def analyse_interval_dg_join_for_def analyse_interval_dg_eqs_for_def
              prog_cfg_def
    by (rule p_reg_join.collect_sound
          [OF solve[unfolded analyse_interval_dg_eqs_for_def prog_cfg_def]
              wf
              vars_coverI[OF cover_entry[unfolded analyse_interval_dg_join_for_def analyse_interval_dg_eqs_for_def prog_cfg_def]
                             cover_edge[unfolded analyse_interval_dg_join_for_def analyse_interval_dg_eqs_for_def prog_cfg_def]
                             cover_enter[unfolded analyse_interval_dg_join_for_def analyse_interval_dg_eqs_for_def prog_cfg_def]
                             cover_combine[unfolded analyse_interval_dg_join_for_def analyse_interval_dg_eqs_for_def prog_cfg_def]]
              finI[unfolded prog_cfg_def] finC[unfolded prog_cfg_def]
              sound0])
qed

lemma analyse_interval_dg_gamma_eq_env_join_for:
  "analyse_interval_dg_gamma_join_for
     (snd (analyse_interval_dg_join_for (resolved_st_q_is_bot_for (declared_global_vars p)) (declared_global p) p)) v
     = \<lbrakk>analyse_interval_dg_join_env_for (resolved_st_q_is_bot_for (declared_global_vars p)) (declared_global p) p v\<rbrakk>"
  unfolding analyse_interval_dg_gamma_join_for_def analyse_interval_dg_join_env_for_def
  by (simp add: p_reg_join.gamma_def
                sound_dg_spec.dg_gamma_def[OF p_reg_join.sds[unfolded sound_dg_spec_ltr_for_def]]
                sound_dg_spec.dg_D_def[OF p_reg_join.sds[unfolded sound_dg_spec_ltr_for_def]]
                gamma_dg_base_def fun_of_dg_st_gen_def gamma_state_bot
         split: lifted.splits)

theorem analyse_interval_report_sound_proved_for:
  fixes v :: pp and c :: exp
  assumes solve: "TD_side_always_join_Interp_solve_c
                    (analyse_interval_dg_eqs_for (resolved_st_q_is_bot_for (declared_global_vars p)) (declared_global p) p)
                    (cfg_exit (prog_cfg prog_main_name p), ()) \<noteq> None"
      and wf: "wf_compile_input (declared_global p) (prog_table p) (prog_procs p) prog_main_name (prog_main p)"
      and cover_entry: "(cfg_entry (prog_cfg prog_main_name p), ()) \<in>
                           fst (analyse_interval_dg_join_for (resolved_st_q_is_bot_for (declared_global_vars p)) (declared_global p) p)"
      and cover_edge:
        "\<And>u a w. (u, a, w) \<in> intra (prog_cfg prog_main_name p) \<Longrightarrow>
           (w, ()) \<in> fst (analyse_interval_dg_join_for (resolved_st_q_is_bot_for (declared_global_vars p)) (declared_global p) p)"
      and cover_enter:
        "\<And>c dst fs as q k. (c, CallEdge dst fs as, FunctionEntry q, k) \<in> calls (prog_cfg prog_main_name p)
           \<Longrightarrow> (FunctionEntry q, ()) \<in> fst (analyse_interval_dg_join_for (resolved_st_q_is_bot_for (declared_global_vars p)) (declared_global p) p)"
      and cover_combine:
        "\<And>c dst fs as q k. (c, CallEdge dst fs as, FunctionEntry q, k) \<in> calls (prog_cfg prog_main_name p)
           \<Longrightarrow> (k, ()) \<in> fst (analyse_interval_dg_join_for (resolved_st_q_is_bot_for (declared_global_vars p)) (declared_global p) p)"
      and finI: "finite (intra (prog_cfg prog_main_name p))"
      and finC: "finite (calls (prog_cfg prog_main_name p))"
      and mem: "(v, c, Check_Proved) \<in> set (analyse_interval_report_for (declared_global p) p)"
  shows "\<forall>s \<in> ltr_collect (declared_global p) (prog_cfg prog_main_name p) (cinit_stores (declared_global p)) v. truthy (aval c s)"
proof -
  have node_sound: "ltr_collect (declared_global p) (prog_cfg prog_main_name p) (cinit_stores (declared_global p)) v
                       \<subseteq> \<lbrakk>analyse_interval_dg_join_env_for (resolved_st_q_is_bot_for (declared_global_vars p)) (declared_global p) p v\<rbrakk>"
    using analyse_interval_dg_collect_join_sound_for[OF solve wf cover_entry cover_edge cover_enter cover_combine finI finC]
    unfolding analyse_interval_dg_gamma_eq_env_join_for .
  show ?thesis
    by (rule classify_checks_proved_sound
          [where g = "prog_cfg prog_main_name p"
             and env = "analyse_interval_dg_join_env_for (resolved_st_q_is_bot_for (declared_global_vars p)) (declared_global p) p"
             and classify = interval_classify_check
             and reach = "ltr_collect (declared_global p) (prog_cfg prog_main_name p) (cinit_stores (declared_global p))"
             and v = v and gamma_state = "gamma_state :: ivl abs_state \<Rightarrow> store set",
           OF finI mem[unfolded analyse_interval_report_for_def] interval_classify_check_proved node_sound])
qed

theorem analyse_interval_report_sound_refuted_for:
  fixes v :: pp and c :: exp
  assumes solve: "TD_side_always_join_Interp_solve_c
                    (analyse_interval_dg_eqs_for (resolved_st_q_is_bot_for (declared_global_vars p)) (declared_global p) p)
                    (cfg_exit (prog_cfg prog_main_name p), ()) \<noteq> None"
      and wf: "wf_compile_input (declared_global p) (prog_table p) (prog_procs p) prog_main_name (prog_main p)"
      and cover_entry: "(cfg_entry (prog_cfg prog_main_name p), ()) \<in>
                           fst (analyse_interval_dg_join_for (resolved_st_q_is_bot_for (declared_global_vars p)) (declared_global p) p)"
      and cover_edge:
        "\<And>u a w. (u, a, w) \<in> intra (prog_cfg prog_main_name p) \<Longrightarrow>
           (w, ()) \<in> fst (analyse_interval_dg_join_for (resolved_st_q_is_bot_for (declared_global_vars p)) (declared_global p) p)"
      and cover_enter:
        "\<And>c dst fs as q k. (c, CallEdge dst fs as, FunctionEntry q, k) \<in> calls (prog_cfg prog_main_name p)
           \<Longrightarrow> (FunctionEntry q, ()) \<in> fst (analyse_interval_dg_join_for (resolved_st_q_is_bot_for (declared_global_vars p)) (declared_global p) p)"
      and cover_combine:
        "\<And>c dst fs as q k. (c, CallEdge dst fs as, FunctionEntry q, k) \<in> calls (prog_cfg prog_main_name p)
           \<Longrightarrow> (k, ()) \<in> fst (analyse_interval_dg_join_for (resolved_st_q_is_bot_for (declared_global_vars p)) (declared_global p) p)"
      and finI: "finite (intra (prog_cfg prog_main_name p))"
      and finC: "finite (calls (prog_cfg prog_main_name p))"
      and mem: "(v, c, Check_Refuted) \<in> set (analyse_interval_report_for (declared_global p) p)"
  shows "\<forall>s \<in> ltr_collect (declared_global p) (prog_cfg prog_main_name p) (cinit_stores (declared_global p)) v. \<not> truthy (aval c s)"
proof -
  have node_sound: "ltr_collect (declared_global p) (prog_cfg prog_main_name p) (cinit_stores (declared_global p)) v
                       \<subseteq> \<lbrakk>analyse_interval_dg_join_env_for (resolved_st_q_is_bot_for (declared_global_vars p)) (declared_global p) p v\<rbrakk>"
    using analyse_interval_dg_collect_join_sound_for[OF solve wf cover_entry cover_edge cover_enter cover_combine finI finC]
    unfolding analyse_interval_dg_gamma_eq_env_join_for .
  show ?thesis
    by (rule classify_checks_refuted_sound
          [where g = "prog_cfg prog_main_name p"
             and env = "analyse_interval_dg_join_env_for (resolved_st_q_is_bot_for (declared_global_vars p)) (declared_global p) p"
             and classify = interval_classify_check
             and reach = "ltr_collect (declared_global p) (prog_cfg prog_main_name p) (cinit_stores (declared_global p))"
             and v = v and gamma_state = "gamma_state :: ivl abs_state \<Rightarrow> store set",
           OF finI mem[unfolded analyse_interval_report_for_def] interval_classify_check_refuted node_sound])
qed

end

corollary analyse_interval_report_sound_proved:
  fixes p :: imp_prog and v :: pp and c :: exp
  assumes solve: "TD_side_always_join_Interp_solve_c (analyse_interval_dg_eqs p)
                    (cfg_exit (prog_cfg prog_main_name p), ()) \<noteq> None"
      and wf: "wf_compile_input (declared_global p) (prog_table p) (prog_procs p) prog_main_name (prog_main p)"
      and cover_entry: "(cfg_entry (prog_cfg prog_main_name p), ()) \<in> fst (analyse_interval_dg_join p)"
      and cover_edge:
        "\<And>u a w. (u, a, w) \<in> intra (prog_cfg prog_main_name p) \<Longrightarrow> (w, ()) \<in> fst (analyse_interval_dg_join p)"
      and cover_enter:
        "\<And>c dst fs as q k. (c, CallEdge dst fs as, FunctionEntry q, k) \<in> calls (prog_cfg prog_main_name p)
           \<Longrightarrow> (FunctionEntry q, ()) \<in> fst (analyse_interval_dg_join p)"
      and cover_combine:
        "\<And>c dst fs as q k. (c, CallEdge dst fs as, FunctionEntry q, k) \<in> calls (prog_cfg prog_main_name p)
           \<Longrightarrow> (k, ()) \<in> fst (analyse_interval_dg_join p)"
      and finI: "finite (intra (prog_cfg prog_main_name p))"
      and finC: "finite (calls (prog_cfg prog_main_name p))"
      and mem: "(v, c, Check_Proved) \<in> set (analyse_interval_report p)"
  shows "\<forall>s \<in> ltr_collect (declared_global p) (prog_cfg prog_main_name p) (cinit_stores (declared_global p)) v.
           truthy (aval c s)"
  unfolding analyse_interval_report_def analyse_interval_dg_eqs_def
  by (rule analyse_interval_report_sound_proved_for
        [OF wf[THEN wf_compile_input_reserved_ret_var]
            solve[unfolded analyse_interval_dg_eqs_def]
            wf
            cover_entry[unfolded analyse_interval_dg_join_def]
            cover_edge[unfolded analyse_interval_dg_join_def]
            cover_enter[unfolded analyse_interval_dg_join_def]
            cover_combine[unfolded analyse_interval_dg_join_def]
            finI finC mem[unfolded analyse_interval_report_def]])

corollary analyse_interval_report_sound_refuted:
  fixes p :: imp_prog and v :: pp and c :: exp
  assumes solve: "TD_side_always_join_Interp_solve_c (analyse_interval_dg_eqs p)
                    (cfg_exit (prog_cfg prog_main_name p), ()) \<noteq> None"
      and wf: "wf_compile_input (declared_global p) (prog_table p) (prog_procs p) prog_main_name (prog_main p)"
      and cover_entry: "(cfg_entry (prog_cfg prog_main_name p), ()) \<in> fst (analyse_interval_dg_join p)"
      and cover_edge:
        "\<And>u a w. (u, a, w) \<in> intra (prog_cfg prog_main_name p) \<Longrightarrow> (w, ()) \<in> fst (analyse_interval_dg_join p)"
      and cover_enter:
        "\<And>c dst fs as q k. (c, CallEdge dst fs as, FunctionEntry q, k) \<in> calls (prog_cfg prog_main_name p)
           \<Longrightarrow> (FunctionEntry q, ()) \<in> fst (analyse_interval_dg_join p)"
      and cover_combine:
        "\<And>c dst fs as q k. (c, CallEdge dst fs as, FunctionEntry q, k) \<in> calls (prog_cfg prog_main_name p)
           \<Longrightarrow> (k, ()) \<in> fst (analyse_interval_dg_join p)"
      and finI: "finite (intra (prog_cfg prog_main_name p))"
      and finC: "finite (calls (prog_cfg prog_main_name p))"
      and mem: "(v, c, Check_Refuted) \<in> set (analyse_interval_report p)"
  shows "\<forall>s \<in> ltr_collect (declared_global p) (prog_cfg prog_main_name p) (cinit_stores (declared_global p)) v.
           \<not> truthy (aval c s)"
  unfolding analyse_interval_report_def analyse_interval_dg_eqs_def
  by (rule analyse_interval_report_sound_refuted_for
        [OF wf[THEN wf_compile_input_reserved_ret_var]
            solve[unfolded analyse_interval_dg_eqs_def]
            wf
            cover_entry[unfolded analyse_interval_dg_join_def]
            cover_edge[unfolded analyse_interval_dg_join_def]
            cover_enter[unfolded analyse_interval_dg_join_def]
            cover_combine[unfolded analyse_interval_dg_join_def]
            finI finC mem[unfolded analyse_interval_report_def]])

text \<open>Per-origin sibling of the join block above: the vendored solver has the identical
  \<open>part_post_solution_of_solve_c\<close> bridge fact under \<^const>\<open>TD_side_per_origin_Interp.solve\<close>, so
  the same proof shape carries over verbatim.\<close>

context
  fixes p :: imp_prog
  assumes reserved: "reserved_ret_var (declared_global p)"
begin

interpretation p_reg_per_origin:
  base_dg_exec_analysis "declared_global p"
    "ivl_tf_for (declared_global p)" "ivl_tf_st_for (declared_global p)" "ivl_enter_st_for (declared_global p)"
    "resolved_st_q_is_bot_for (declared_global_vars p)"
    "TD_side_per_origin_Interp.solve" "TD_side_per_origin_Interp.solve_c"
proof -
  interpret p_transfer: sound_transfer_for "declared_global p" "ivl_tf_for (declared_global p)"
    by (rule ivl_is_sound_transfer_for)
  show "base_dg_exec_analysis (declared_global p) (ivl_tf_for (declared_global p))
          (ivl_tf_st_for (declared_global p)) (ivl_enter_st_for (declared_global p))
          (resolved_st_q_is_bot_for (declared_global_vars p))
          TD_side_per_origin_Interp.solve TD_side_per_origin_Interp.solve_c"
    by unfold_locales
       (rule reserved
             p_transfer.tf_sound_assign_for p_transfer.tf_sound_special_for
             p_transfer.tf_sound_branch_for
             p_transfer.tf_sound_enter_for p_transfer.tf_sound_combine_env_for
             ivl_tf_st_for_commute[folded fun_of_exec_dg_st_for_def]
             ivl_enter_st_for_commute[folded fun_of_exec_dg_st_for_def]
             resolved_st_q_is_bot_for_iff[OF declared_global_iff, folded fun_of_exec_dg_st_for_def]
             action_reduces.ret_none[OF ivl_tf_st_for_reduces]
             action_reduces.ret_some[OF ivl_tf_st_for_reduces]
             action_reduces.check[OF ivl_tf_st_for_reduces]
             TD_side_per_origin_Interp.part_post_solution_of_solve_c)+
qed

definition analyse_interval_dg_gamma_per_origin_for ::
  "(pp \<times> unit + unit \<Rightarrow> (ivl exec_dg_st lifted, ivl exec_dg_st lifted) dg_state) \<Rightarrow> pp \<Rightarrow> store set" where
  "analyse_interval_dg_gamma_per_origin_for = p_reg_per_origin.gamma"

theorem analyse_interval_dg_collect_per_origin_sound_for:
  assumes solve: "TD_side_per_origin_Interp_solve_c
                    (analyse_interval_dg_eqs_for (resolved_st_q_is_bot_for (declared_global_vars p)) (declared_global p) p)
                    (cfg_exit (prog_cfg prog_main_name p), ()) \<noteq> None"
      and wf: "wf_compile_input (declared_global p) (prog_table p) (prog_procs p) prog_main_name (prog_main p)"
      and cover_entry: "(cfg_entry (prog_cfg prog_main_name p), ()) \<in>
                           fst (analyse_interval_dg_per_origin_for (resolved_st_q_is_bot_for (declared_global_vars p)) (declared_global p) p)"
      and cover_edge:
        "\<And>u a w. (u, a, w) \<in> intra (prog_cfg prog_main_name p) \<Longrightarrow>
           (w, ()) \<in> fst (analyse_interval_dg_per_origin_for (resolved_st_q_is_bot_for (declared_global_vars p)) (declared_global p) p)"
      and cover_enter:
        "\<And>c dst fs as q k. (c, CallEdge dst fs as, FunctionEntry q, k) \<in> calls (prog_cfg prog_main_name p)
           \<Longrightarrow> (FunctionEntry q, ()) \<in> fst (analyse_interval_dg_per_origin_for (resolved_st_q_is_bot_for (declared_global_vars p)) (declared_global p) p)"
      and cover_combine:
        "\<And>c dst fs as q k. (c, CallEdge dst fs as, FunctionEntry q, k) \<in> calls (prog_cfg prog_main_name p)
           \<Longrightarrow> (k, ()) \<in> fst (analyse_interval_dg_per_origin_for (resolved_st_q_is_bot_for (declared_global_vars p)) (declared_global p) p)"
      and finI: "finite (intra (prog_cfg prog_main_name p))"
      and finC: "finite (calls (prog_cfg prog_main_name p))"
  shows "ltr_collect (declared_global p) (prog_cfg prog_main_name p) (cinit_stores (declared_global p)) v
           \<subseteq> analyse_interval_dg_gamma_per_origin_for
               (snd (analyse_interval_dg_per_origin_for (resolved_st_q_is_bot_for (declared_global_vars p)) (declared_global p) p)) v"
proof -
  have sound0:
    "cinit_stores (declared_global p) \<subseteq> gamma_dg_base (map_lift (fun_of_exec_dg_st_for (declared_global p)) (Lifted cinit_ivl_st))
                          (map_lift (fun_of_exec_dg_st_for (declared_global p)) (Lifted cinit_ivl_st))"
    by (auto simp: fun_of_exec_dg_st_for_def fun_of_st_cinit_ivl_st_for cinit_stores_def
                  gamma_state_def gamma_dg_base_def)
  show ?thesis
    unfolding analyse_interval_dg_gamma_per_origin_for_def analyse_interval_dg_per_origin_for_def analyse_interval_dg_eqs_for_def
              prog_cfg_def
    by (rule p_reg_per_origin.collect_sound
          [OF solve[unfolded analyse_interval_dg_eqs_for_def prog_cfg_def]
              wf
              vars_coverI[OF cover_entry[unfolded analyse_interval_dg_per_origin_for_def analyse_interval_dg_eqs_for_def prog_cfg_def]
                             cover_edge[unfolded analyse_interval_dg_per_origin_for_def analyse_interval_dg_eqs_for_def prog_cfg_def]
                             cover_enter[unfolded analyse_interval_dg_per_origin_for_def analyse_interval_dg_eqs_for_def prog_cfg_def]
                             cover_combine[unfolded analyse_interval_dg_per_origin_for_def analyse_interval_dg_eqs_for_def prog_cfg_def]]
              finI[unfolded prog_cfg_def] finC[unfolded prog_cfg_def]
              sound0])
qed

lemma analyse_interval_dg_gamma_eq_env_per_origin_for:
  "analyse_interval_dg_gamma_per_origin_for
     (snd (analyse_interval_dg_per_origin_for (resolved_st_q_is_bot_for (declared_global_vars p)) (declared_global p) p)) v
     = \<lbrakk>analyse_interval_dg_per_origin_env_for (resolved_st_q_is_bot_for (declared_global_vars p)) (declared_global p) p v\<rbrakk>"
  unfolding analyse_interval_dg_gamma_per_origin_for_def analyse_interval_dg_per_origin_env_for_def
  by (simp add: p_reg_per_origin.gamma_def
                sound_dg_spec.dg_gamma_def[OF p_reg_per_origin.sds[unfolded sound_dg_spec_ltr_for_def]]
                sound_dg_spec.dg_D_def[OF p_reg_per_origin.sds[unfolded sound_dg_spec_ltr_for_def]]
                gamma_dg_base_def fun_of_dg_st_gen_def gamma_state_bot
         split: lifted.splits)

theorem analyse_interval_report_per_origin_sound_proved_for:
  fixes v :: pp and c :: exp
  assumes solve: "TD_side_per_origin_Interp_solve_c
                    (analyse_interval_dg_eqs_for (resolved_st_q_is_bot_for (declared_global_vars p)) (declared_global p) p)
                    (cfg_exit (prog_cfg prog_main_name p), ()) \<noteq> None"
      and wf: "wf_compile_input (declared_global p) (prog_table p) (prog_procs p) prog_main_name (prog_main p)"
      and cover_entry: "(cfg_entry (prog_cfg prog_main_name p), ()) \<in>
                           fst (analyse_interval_dg_per_origin_for (resolved_st_q_is_bot_for (declared_global_vars p)) (declared_global p) p)"
      and cover_edge:
        "\<And>u a w. (u, a, w) \<in> intra (prog_cfg prog_main_name p) \<Longrightarrow>
           (w, ()) \<in> fst (analyse_interval_dg_per_origin_for (resolved_st_q_is_bot_for (declared_global_vars p)) (declared_global p) p)"
      and cover_enter:
        "\<And>c dst fs as q k. (c, CallEdge dst fs as, FunctionEntry q, k) \<in> calls (prog_cfg prog_main_name p)
           \<Longrightarrow> (FunctionEntry q, ()) \<in> fst (analyse_interval_dg_per_origin_for (resolved_st_q_is_bot_for (declared_global_vars p)) (declared_global p) p)"
      and cover_combine:
        "\<And>c dst fs as q k. (c, CallEdge dst fs as, FunctionEntry q, k) \<in> calls (prog_cfg prog_main_name p)
           \<Longrightarrow> (k, ()) \<in> fst (analyse_interval_dg_per_origin_for (resolved_st_q_is_bot_for (declared_global_vars p)) (declared_global p) p)"
      and finI: "finite (intra (prog_cfg prog_main_name p))"
      and finC: "finite (calls (prog_cfg prog_main_name p))"
      and mem: "(v, c, Check_Proved) \<in> set (analyse_interval_report_per_origin_for (declared_global p) p)"
  shows "\<forall>s \<in> ltr_collect (declared_global p) (prog_cfg prog_main_name p) (cinit_stores (declared_global p)) v. truthy (aval c s)"
proof -
  have node_sound: "ltr_collect (declared_global p) (prog_cfg prog_main_name p) (cinit_stores (declared_global p)) v
                       \<subseteq> \<lbrakk>analyse_interval_dg_per_origin_env_for (resolved_st_q_is_bot_for (declared_global_vars p)) (declared_global p) p v\<rbrakk>"
    using analyse_interval_dg_collect_per_origin_sound_for[OF solve wf cover_entry cover_edge cover_enter cover_combine finI finC]
    unfolding analyse_interval_dg_gamma_eq_env_per_origin_for .
  show ?thesis
    by (rule classify_checks_proved_sound
          [where g = "prog_cfg prog_main_name p"
             and env = "analyse_interval_dg_per_origin_env_for (resolved_st_q_is_bot_for (declared_global_vars p)) (declared_global p) p"
             and classify = interval_classify_check
             and reach = "ltr_collect (declared_global p) (prog_cfg prog_main_name p) (cinit_stores (declared_global p))"
             and v = v and gamma_state = "gamma_state :: ivl abs_state \<Rightarrow> store set",
           OF finI mem[unfolded analyse_interval_report_per_origin_for_def] interval_classify_check_proved node_sound])
qed

theorem analyse_interval_report_per_origin_sound_refuted_for:
  fixes v :: pp and c :: exp
  assumes solve: "TD_side_per_origin_Interp_solve_c
                    (analyse_interval_dg_eqs_for (resolved_st_q_is_bot_for (declared_global_vars p)) (declared_global p) p)
                    (cfg_exit (prog_cfg prog_main_name p), ()) \<noteq> None"
      and wf: "wf_compile_input (declared_global p) (prog_table p) (prog_procs p) prog_main_name (prog_main p)"
      and cover_entry: "(cfg_entry (prog_cfg prog_main_name p), ()) \<in>
                           fst (analyse_interval_dg_per_origin_for (resolved_st_q_is_bot_for (declared_global_vars p)) (declared_global p) p)"
      and cover_edge:
        "\<And>u a w. (u, a, w) \<in> intra (prog_cfg prog_main_name p) \<Longrightarrow>
           (w, ()) \<in> fst (analyse_interval_dg_per_origin_for (resolved_st_q_is_bot_for (declared_global_vars p)) (declared_global p) p)"
      and cover_enter:
        "\<And>c dst fs as q k. (c, CallEdge dst fs as, FunctionEntry q, k) \<in> calls (prog_cfg prog_main_name p)
           \<Longrightarrow> (FunctionEntry q, ()) \<in> fst (analyse_interval_dg_per_origin_for (resolved_st_q_is_bot_for (declared_global_vars p)) (declared_global p) p)"
      and cover_combine:
        "\<And>c dst fs as q k. (c, CallEdge dst fs as, FunctionEntry q, k) \<in> calls (prog_cfg prog_main_name p)
           \<Longrightarrow> (k, ()) \<in> fst (analyse_interval_dg_per_origin_for (resolved_st_q_is_bot_for (declared_global_vars p)) (declared_global p) p)"
      and finI: "finite (intra (prog_cfg prog_main_name p))"
      and finC: "finite (calls (prog_cfg prog_main_name p))"
      and mem: "(v, c, Check_Refuted) \<in> set (analyse_interval_report_per_origin_for (declared_global p) p)"
  shows "\<forall>s \<in> ltr_collect (declared_global p) (prog_cfg prog_main_name p) (cinit_stores (declared_global p)) v. \<not> truthy (aval c s)"
proof -
  have node_sound: "ltr_collect (declared_global p) (prog_cfg prog_main_name p) (cinit_stores (declared_global p)) v
                       \<subseteq> \<lbrakk>analyse_interval_dg_per_origin_env_for (resolved_st_q_is_bot_for (declared_global_vars p)) (declared_global p) p v\<rbrakk>"
    using analyse_interval_dg_collect_per_origin_sound_for[OF solve wf cover_entry cover_edge cover_enter cover_combine finI finC]
    unfolding analyse_interval_dg_gamma_eq_env_per_origin_for .
  show ?thesis
    by (rule classify_checks_refuted_sound
          [where g = "prog_cfg prog_main_name p"
             and env = "analyse_interval_dg_per_origin_env_for (resolved_st_q_is_bot_for (declared_global_vars p)) (declared_global p) p"
             and classify = interval_classify_check
             and reach = "ltr_collect (declared_global p) (prog_cfg prog_main_name p) (cinit_stores (declared_global p))"
             and v = v and gamma_state = "gamma_state :: ivl abs_state \<Rightarrow> store set",
           OF finI mem[unfolded analyse_interval_report_per_origin_for_def] interval_classify_check_refuted node_sound])
qed

end

corollary analyse_interval_report_per_origin_sound_proved:
  fixes p :: imp_prog and v :: pp and c :: exp
  assumes solve: "TD_side_per_origin_Interp_solve_c (analyse_interval_dg_eqs p)
                    (cfg_exit (prog_cfg prog_main_name p), ()) \<noteq> None"
      and wf: "wf_compile_input (declared_global p) (prog_table p) (prog_procs p) prog_main_name (prog_main p)"
      and cover_entry: "(cfg_entry (prog_cfg prog_main_name p), ()) \<in> fst (analyse_interval_dg_per_origin p)"
      and cover_edge:
        "\<And>u a w. (u, a, w) \<in> intra (prog_cfg prog_main_name p) \<Longrightarrow> (w, ()) \<in> fst (analyse_interval_dg_per_origin p)"
      and cover_enter:
        "\<And>c dst fs as q k. (c, CallEdge dst fs as, FunctionEntry q, k) \<in> calls (prog_cfg prog_main_name p)
           \<Longrightarrow> (FunctionEntry q, ()) \<in> fst (analyse_interval_dg_per_origin p)"
      and cover_combine:
        "\<And>c dst fs as q k. (c, CallEdge dst fs as, FunctionEntry q, k) \<in> calls (prog_cfg prog_main_name p)
           \<Longrightarrow> (k, ()) \<in> fst (analyse_interval_dg_per_origin p)"
      and finI: "finite (intra (prog_cfg prog_main_name p))"
      and finC: "finite (calls (prog_cfg prog_main_name p))"
      and mem: "(v, c, Check_Proved) \<in> set (analyse_interval_report_per_origin p)"
  shows "\<forall>s \<in> ltr_collect (declared_global p) (prog_cfg prog_main_name p) (cinit_stores (declared_global p)) v.
           truthy (aval c s)"
  unfolding analyse_interval_report_per_origin_def analyse_interval_dg_eqs_def
  by (rule analyse_interval_report_per_origin_sound_proved_for
        [OF wf[THEN wf_compile_input_reserved_ret_var]
            solve[unfolded analyse_interval_dg_eqs_def]
            wf
            cover_entry[unfolded analyse_interval_dg_per_origin_def]
            cover_edge[unfolded analyse_interval_dg_per_origin_def]
            cover_enter[unfolded analyse_interval_dg_per_origin_def]
            cover_combine[unfolded analyse_interval_dg_per_origin_def]
            finI finC mem[unfolded analyse_interval_report_per_origin_def]])

corollary analyse_interval_report_per_origin_sound_refuted:
  fixes p :: imp_prog and v :: pp and c :: exp
  assumes solve: "TD_side_per_origin_Interp_solve_c (analyse_interval_dg_eqs p)
                    (cfg_exit (prog_cfg prog_main_name p), ()) \<noteq> None"
      and wf: "wf_compile_input (declared_global p) (prog_table p) (prog_procs p) prog_main_name (prog_main p)"
      and cover_entry: "(cfg_entry (prog_cfg prog_main_name p), ()) \<in> fst (analyse_interval_dg_per_origin p)"
      and cover_edge:
        "\<And>u a w. (u, a, w) \<in> intra (prog_cfg prog_main_name p) \<Longrightarrow> (w, ()) \<in> fst (analyse_interval_dg_per_origin p)"
      and cover_enter:
        "\<And>c dst fs as q k. (c, CallEdge dst fs as, FunctionEntry q, k) \<in> calls (prog_cfg prog_main_name p)
           \<Longrightarrow> (FunctionEntry q, ()) \<in> fst (analyse_interval_dg_per_origin p)"
      and cover_combine:
        "\<And>c dst fs as q k. (c, CallEdge dst fs as, FunctionEntry q, k) \<in> calls (prog_cfg prog_main_name p)
           \<Longrightarrow> (k, ()) \<in> fst (analyse_interval_dg_per_origin p)"
      and finI: "finite (intra (prog_cfg prog_main_name p))"
      and finC: "finite (calls (prog_cfg prog_main_name p))"
      and mem: "(v, c, Check_Refuted) \<in> set (analyse_interval_report_per_origin p)"
  shows "\<forall>s \<in> ltr_collect (declared_global p) (prog_cfg prog_main_name p) (cinit_stores (declared_global p)) v.
           \<not> truthy (aval c s)"
  unfolding analyse_interval_report_per_origin_def analyse_interval_dg_eqs_def
  by (rule analyse_interval_report_per_origin_sound_refuted_for
        [OF wf[THEN wf_compile_input_reserved_ret_var]
            solve[unfolded analyse_interval_dg_eqs_def]
            wf
            cover_entry[unfolded analyse_interval_dg_per_origin_def]
            cover_edge[unfolded analyse_interval_dg_per_origin_def]
            cover_enter[unfolded analyse_interval_dg_per_origin_def]
            cover_combine[unfolded analyse_interval_dg_per_origin_def]
            finI finC mem[unfolded analyse_interval_report_per_origin_def]])

end
