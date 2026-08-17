theory Example_Sign_Codegen
  imports Exec_Sign_DG_Run Voblint_Analysis.Sign_Checks
begin

section \<open>Sign codegen API: an arbitrary VIMP program, and its OCaml export\<close>

subsection \<open>Whole-program entry point: an arbitrary VIMP program\<close>

text \<open>
  \<open>gEx\<close>/\<open>dgEx_eqs\<close>/\<open>dgEx_sol\<close> in \<open>Exec_Sign_DG_Run\<close> fix one hard-coded example.
  This section widens that same native D/G chain to an arbitrary program \<open>p\<close>,
  reusing \<^const>\<open>prog_cfg\<close> for the compiled CFG.  The locale interpretation below is the
  program-generic twin of \<open>sign_ex_reg\<close> in \<open>Exec_Sign_DG_Run\<close>: the same five
  transfer facts discharge \<^locale>\<open>base_dg_exec_analysis\<close> for any \<open>p\<close>, not only at
  \<open>sign_ex_prog\<close>, because \<open>sign_is_sound_transfer_for\<close>,
  \<open>sign_tf_st_for_commute\<close>, and \<open>sign_enter_st_for_commute\<close> are already
  stated for an arbitrary classifier.  The classifier itself is fixed to \<^const>\<open>declared_global\<close>
  \<open>p\<close> directly here (named \<open>pgs\<close>, not the common local name \<open>gs\<close>, so it cannot shadow that
  name at any import site): every caller of this \<open>_for\<close> layer already instantiates it that
  way (\<open>Sign_Checks\<close>, the regression suite, the GraphViz tooling), so keeping the classifier
  independently parametric would only add an \<open>is_bot_pred\<close> exactness obligation no caller
  ever exercises.
\<close>

context
  fixes p :: imp_prog
  assumes reserved: "reserved_ret_var (declared_global p)"
begin

abbreviation pgs :: "vname \<Rightarrow> bool" where "pgs \<equiv> declared_global p"

interpretation p_reg:
  base_dg_exec_analysis pgs
    "sign_tf_for pgs" "sign_tf_st_for pgs" "sign_enter_st_for pgs"
    "resolved_st_q_is_bot_for (declared_global_vars p)"
    "TD_side_always_join_Interp.solve" "TD_side_always_join_Interp.solve_c"
proof -
  interpret p_transfer: sound_transfer_for pgs "sign_tf_for pgs"
    by (rule sign_is_sound_transfer_for)
  show "base_dg_exec_analysis pgs (sign_tf_for pgs)
          (sign_tf_st_for pgs) (sign_enter_st_for pgs) (resolved_st_q_is_bot_for (declared_global_vars p))
          TD_side_always_join_Interp.solve TD_side_always_join_Interp.solve_c"
    by unfold_locales
       (rule reserved
             p_transfer.tf_sound_assign_for p_transfer.tf_sound_special_for
             p_transfer.tf_sound_branch_for
             p_transfer.tf_sound_enter_for p_transfer.tf_sound_combine_env_for
             sign_tf_st_for_commute[folded fun_of_exec_dg_st_for_def]
             sign_enter_st_for_commute[folded fun_of_exec_dg_st_for_def]
             resolved_st_q_is_bot_for_iff[OF declared_global_iff, folded fun_of_exec_dg_st_for_def]
             action_reduces.ret_none[OF sign_tf_st_for_reduces]
             action_reduces.ret_some[OF sign_tf_st_for_reduces]
             action_reduces.check[OF sign_tf_st_for_reduces]
             TD_side_always_join_Interp.part_post_solution_of_solve_c)+
qed

text \<open>
  \<open>p_reg\<close> is local to this context block, so its qualified constants do not
  survive past the closing \<open>end\<close> --- \<open>analyse_sign_gamma_for\<close> names the
  fully-applied locale concretization once, the same way \<open>Sign_DG\<close>'s
  \<open>sign_dg_gamma\<close> names \<open>sound_dg_spec.dg_gamma\<close>, so \<open>analyse_sign_sound\<close>
  below can state its conclusion after the context closes.
\<close>

definition analyse_sign_gamma_for ::
  "(pp \<times> unit + unit \<Rightarrow> (sign exec_dg_st lifted, sign exec_dg_st lifted) dg_state) \<Rightarrow> pp \<Rightarrow> store set" where
  "analyse_sign_gamma_for = p_reg.gamma"

text \<open>
  \<open>analyse_sign_eqs_for\<close>/\<open>analyse_sign_for\<close> (the native D/G equation system and its solved
  result, at \<^const>\<open>declared_global\<close> \<open>p\<close>) and \<open>analyse_sign_env_for\<close> now live in
  \<^theory>\<open>Voblint_Analysis.Sign_Exec_Sound\<close> --- they are pure computation, no dependence on the
  \<open>base_dg_exec_analysis\<close> locale \<open>p_reg\<close> interprets here, so they need not sit in this Examples
  session. Every reference below applies them to this context's fixed \<open>p\<close> explicitly, since
  outside a context a definition takes its fixed variables as ordinary leading arguments.

  The connection lemma: soundness for an arbitrary \<open>p\<close> reuses
  \<open>base_dg_exec_analysis.run_source_sound\<close> exactly as \<open>dgEx_source_run_sound\<close>
  does, just with the solver-domain, well-formedness, and coverage facts left
  as hypotheses instead of discharged \<open>by eval\<close> --- a symbolic \<open>p\<close> cannot
  be run through the executable solver at proof time the way the one
  hard-coded \<open>sign_ex_prog\<close> can.  \<open>sound0\<close> stays internal: it
  never depended on the program, only on \<open>cinit_sign_st\<close> and the classifier,
  exactly as in \<open>dgEx_sound0\<close> -- and, unlike the old unlifted route, needs no
  \<^const>\<open>combine_env_abs\<close> reconstruction: \<^const>\<open>gamma_dg_base\<close> concretizes the
  local unknown directly.
\<close>

theorem analyse_sign_sound_for:
  assumes solve: "TD_side_always_join_Interp_solve_c (analyse_sign_eqs_for (resolved_st_q_is_bot_for (declared_global_vars p)) pgs p) (cfg_exit (prog_cfg prog_main_name p), ()) \<noteq> None"
      and wf: "wf_compile_input pgs (prog_table p) (prog_procs p) prog_main_name (prog_main p)"
      and cover_entry: "(cfg_entry (prog_cfg prog_main_name p), ()) \<in> fst (analyse_sign_for (resolved_st_q_is_bot_for (declared_global_vars p)) pgs p)"
      and cover_edge:
        "\<And>u a w. (u, a, w) \<in> intra (prog_cfg prog_main_name p) \<Longrightarrow> (w, ()) \<in> fst (analyse_sign_for (resolved_st_q_is_bot_for (declared_global_vars p)) pgs p)"
      and cover_enter:
        "\<And>c dst fs as q k. (c, CallEdge dst fs as, FunctionEntry q, k) \<in> calls (prog_cfg prog_main_name p)
           \<Longrightarrow> (FunctionEntry q, ()) \<in> fst (analyse_sign_for (resolved_st_q_is_bot_for (declared_global_vars p)) pgs p)"
      and cover_combine:
        "\<And>c dst fs as q k. (c, CallEdge dst fs as, FunctionEntry q, k) \<in> calls (prog_cfg prog_main_name p)
           \<Longrightarrow> (k, ()) \<in> fst (analyse_sign_for (resolved_st_q_is_bot_for (declared_global_vars p)) pgs p)"
      and finI: "finite (intra (prog_cfg prog_main_name p))"
      and finC: "finite (calls (prog_cfg prog_main_name p))"
      and run: "star (pstep pgs (prog_table p)) (prog_main p, s, []) (residual, t, frs)"
      and init: "s \<in> cinit_stores pgs"
  shows "\<exists>v stk. csim (prog_table p) (prog_cfg prog_main_name p) (residual, t, frs) (v, t, stk)
                 \<and> t \<in> analyse_sign_gamma_for (snd (analyse_sign_for (resolved_st_q_is_bot_for (declared_global_vars p)) pgs p)) v"
proof -
  have sound0:
    "cinit_stores pgs \<subseteq> gamma_dg_base (map_lift (fun_of_exec_dg_st_for pgs) (Lifted cinit_sign_st))
                          (map_lift (fun_of_exec_dg_st_for pgs) (Lifted cinit_sign_st))"
    by (simp add: fun_of_exec_dg_st_for_def fun_of_st_cinit_sign_st_for cinit_stores_def
                  gamma_state_def gamma_dg_base_def)
  show ?thesis
    unfolding analyse_sign_gamma_for_def analyse_sign_for_def analyse_sign_eqs_for_def prog_cfg_def
    by (rule p_reg.run_source_sound
          [OF solve[unfolded analyse_sign_eqs_for_def prog_cfg_def]
              wf
              vars_coverI[OF cover_entry[unfolded analyse_sign_for_def analyse_sign_eqs_for_def prog_cfg_def]
                             cover_edge[unfolded analyse_sign_for_def analyse_sign_eqs_for_def prog_cfg_def]
                             cover_enter[unfolded analyse_sign_for_def analyse_sign_eqs_for_def prog_cfg_def]
                             cover_combine[unfolded analyse_sign_for_def analyse_sign_eqs_for_def prog_cfg_def]]
              finI[unfolded prog_cfg_def] finC[unfolded prog_cfg_def]
              sound0 init run])
qed

text \<open>
  The per-node collecting analogue of \<open>analyse_sign_sound_for\<close>, for a
  check-report layer that wants soundness at an arbitrary node without a
  concrete source run --- reuses \<open>p_reg.collect_sound\<close>, the same
  locale-level fact \<open>run_source_sound\<close> itself is built from
  (\<^theory>\<open>Voblint_Formalization.Run_Analysis_Sound\<close>).
\<close>

theorem analyse_sign_collect_sound_for:
  assumes solve: "TD_side_always_join_Interp_solve_c (analyse_sign_eqs_for (resolved_st_q_is_bot_for (declared_global_vars p)) pgs p) (cfg_exit (prog_cfg prog_main_name p), ()) \<noteq> None"
      and wf: "wf_compile_input pgs (prog_table p) (prog_procs p) prog_main_name (prog_main p)"
      and cover_entry: "(cfg_entry (prog_cfg prog_main_name p), ()) \<in> fst (analyse_sign_for (resolved_st_q_is_bot_for (declared_global_vars p)) pgs p)"
      and cover_edge:
        "\<And>u a w. (u, a, w) \<in> intra (prog_cfg prog_main_name p) \<Longrightarrow> (w, ()) \<in> fst (analyse_sign_for (resolved_st_q_is_bot_for (declared_global_vars p)) pgs p)"
      and cover_enter:
        "\<And>c dst fs as q k. (c, CallEdge dst fs as, FunctionEntry q, k) \<in> calls (prog_cfg prog_main_name p)
           \<Longrightarrow> (FunctionEntry q, ()) \<in> fst (analyse_sign_for (resolved_st_q_is_bot_for (declared_global_vars p)) pgs p)"
      and cover_combine:
        "\<And>c dst fs as q k. (c, CallEdge dst fs as, FunctionEntry q, k) \<in> calls (prog_cfg prog_main_name p)
           \<Longrightarrow> (k, ()) \<in> fst (analyse_sign_for (resolved_st_q_is_bot_for (declared_global_vars p)) pgs p)"
      and finI: "finite (intra (prog_cfg prog_main_name p))"
      and finC: "finite (calls (prog_cfg prog_main_name p))"
  shows "ltr_collect pgs (prog_cfg prog_main_name p) (cinit_stores pgs) v
           \<subseteq> analyse_sign_gamma_for (snd (analyse_sign_for (resolved_st_q_is_bot_for (declared_global_vars p)) pgs p)) v"
proof -
  have sound0:
    "cinit_stores pgs \<subseteq> gamma_dg_base (map_lift (fun_of_exec_dg_st_for pgs) (Lifted cinit_sign_st))
                          (map_lift (fun_of_exec_dg_st_for pgs) (Lifted cinit_sign_st))"
    by (simp add: fun_of_exec_dg_st_for_def fun_of_st_cinit_sign_st_for cinit_stores_def
                  gamma_state_def gamma_dg_base_def)
  show ?thesis
    unfolding analyse_sign_gamma_for_def analyse_sign_for_def analyse_sign_eqs_for_def prog_cfg_def
    by (rule p_reg.collect_sound
          [OF solve[unfolded analyse_sign_eqs_for_def prog_cfg_def]
              wf
              vars_coverI[OF cover_entry[unfolded analyse_sign_for_def analyse_sign_eqs_for_def prog_cfg_def]
                             cover_edge[unfolded analyse_sign_for_def analyse_sign_eqs_for_def prog_cfg_def]
                             cover_enter[unfolded analyse_sign_for_def analyse_sign_eqs_for_def prog_cfg_def]
                             cover_combine[unfolded analyse_sign_for_def analyse_sign_eqs_for_def prog_cfg_def]]
              finI[unfolded prog_cfg_def] finC[unfolded prog_cfg_def]
              sound0])
qed

text \<open>
  \<open>p_reg\<close> is local, so its qualified constants (and the raw locale
  predicate \<open>base_dg_exec_analysis\<close>) do not survive past the closing
  \<open>end\<close> either --- \<open>analyse_sign_env_for\<close> reads the local unknown at \<open>v\<close>
  (\<open>Inl (v, ())\<close>) directly, the same way \<open>dgEx_inspect\<close> in
  \<open>Exec_Sign_DG_Run\<close> does by hand, and \<open>analyse_sign_gamma_eq_env_for\<close>
  proves it is exactly what \<open>analyse_sign_gamma_for\<close> already concretizes ---
  via \<open>p_reg.gamma_def\<close> and \<open>p_reg.sds\<close>, not a new soundness argument.
\<close>

lemma analyse_sign_gamma_eq_env_for:
  "analyse_sign_gamma_for (snd (analyse_sign_for (resolved_st_q_is_bot_for (declared_global_vars p)) pgs p)) v
     = \<lbrakk>analyse_sign_env_for (resolved_st_q_is_bot_for (declared_global_vars p)) pgs p v\<rbrakk>"
  unfolding analyse_sign_gamma_for_def analyse_sign_env_for_def
  by (simp add: p_reg.gamma_def
                sound_dg_spec.dg_gamma_def[OF p_reg.sds[unfolded sound_dg_spec_ltr_for_def]]
                sound_dg_spec.dg_D_def[OF p_reg.sds[unfolded sound_dg_spec_ltr_for_def]]
                gamma_dg_base_def fun_of_dg_st_gen_def gamma_state_bot
         split: lifted.splits)

text \<open>
  The check report itself is a thin composition, exactly mirroring
  \<open>sign_check_report\<close>/\<open>interval_check_report\<close>: \<^const>\<open>classify_checks\<close>
  owns the traversal and ordering, \<open>analyse_sign_env_for\<close> owns the
  node-indexed Sign environment, and \<open>sign_classify_check\<close> owns the
  per-check classification.
\<close>

text \<open>
  \<open>analyse_sign_report_for\<close> itself (\<^theory>\<open>Voblint_Analysis.Sign_Checks\<close>) needs
  \<open>sign_classify_check\<close>, defined there rather than in \<^theory>\<open>Voblint_Analysis.Sign_Exec_Sound\<close>, so
  it cannot join \<open>analyse_sign_env_for\<close> in that theory either --- but its soundness still needs
  \<open>p_reg\<close>, so it stays here.

  Soundness reuses \<open>classify_checks_proved_sound\<close>/\<open>classify_checks_refuted_sound\<close>
  (\<^theory>\<open>Voblint_Core.Abstract_Checks\<close>, fully domain-generic already) with
  \<open>analyse_sign_collect_sound_for\<close> and \<open>analyse_sign_gamma_eq_env_for\<close>
  together supplying the one per-node fact each needs.
\<close>

theorem analyse_sign_report_sound_proved_for:
  fixes v :: pp and c :: exp
  assumes solve: "TD_side_always_join_Interp_solve_c (analyse_sign_eqs_for (resolved_st_q_is_bot_for (declared_global_vars p)) pgs p) (cfg_exit (prog_cfg prog_main_name p), ()) \<noteq> None"
      and wf: "wf_compile_input pgs (prog_table p) (prog_procs p) prog_main_name (prog_main p)"
      and cover_entry: "(cfg_entry (prog_cfg prog_main_name p), ()) \<in> fst (analyse_sign_for (resolved_st_q_is_bot_for (declared_global_vars p)) pgs p)"
      and cover_edge:
        "\<And>u a w. (u, a, w) \<in> intra (prog_cfg prog_main_name p) \<Longrightarrow> (w, ()) \<in> fst (analyse_sign_for (resolved_st_q_is_bot_for (declared_global_vars p)) pgs p)"
      and cover_enter:
        "\<And>c dst fs as q k. (c, CallEdge dst fs as, FunctionEntry q, k) \<in> calls (prog_cfg prog_main_name p)
           \<Longrightarrow> (FunctionEntry q, ()) \<in> fst (analyse_sign_for (resolved_st_q_is_bot_for (declared_global_vars p)) pgs p)"
      and cover_combine:
        "\<And>c dst fs as q k. (c, CallEdge dst fs as, FunctionEntry q, k) \<in> calls (prog_cfg prog_main_name p)
           \<Longrightarrow> (k, ()) \<in> fst (analyse_sign_for (resolved_st_q_is_bot_for (declared_global_vars p)) pgs p)"
      and finI: "finite (intra (prog_cfg prog_main_name p))"
      and finC: "finite (calls (prog_cfg prog_main_name p))"
      and mem: "(v, c, Check_Proved) \<in> set (analyse_sign_report_for pgs p)"
  shows "\<forall>s \<in> ltr_collect pgs (prog_cfg prog_main_name p) (cinit_stores pgs) v. truthy (aval c s)"
proof -
  have node_sound: "ltr_collect pgs (prog_cfg prog_main_name p) (cinit_stores pgs) v \<subseteq> \<lbrakk>analyse_sign_env_for (resolved_st_q_is_bot_for (declared_global_vars p)) pgs p v\<rbrakk>"
    using analyse_sign_collect_sound_for[OF solve wf cover_entry cover_edge cover_enter cover_combine finI finC]
    unfolding analyse_sign_gamma_eq_env_for .
  show ?thesis
    by (rule classify_checks_proved_sound
          [where g = "prog_cfg prog_main_name p" and env = "analyse_sign_env_for (resolved_st_q_is_bot_for (declared_global_vars p)) pgs p"
             and classify = sign_classify_check
             and reach = "ltr_collect pgs (prog_cfg prog_main_name p) (cinit_stores pgs)"
             and v = v and gamma_state = "gamma_state :: sign abs_state \<Rightarrow> store set",
           OF finI mem[unfolded analyse_sign_report_for_def] sign_classify_check_proved node_sound])
qed

theorem analyse_sign_report_sound_refuted_for:
  fixes v :: pp and c :: exp
  assumes solve: "TD_side_always_join_Interp_solve_c (analyse_sign_eqs_for (resolved_st_q_is_bot_for (declared_global_vars p)) pgs p) (cfg_exit (prog_cfg prog_main_name p), ()) \<noteq> None"
      and wf: "wf_compile_input pgs (prog_table p) (prog_procs p) prog_main_name (prog_main p)"
      and cover_entry: "(cfg_entry (prog_cfg prog_main_name p), ()) \<in> fst (analyse_sign_for (resolved_st_q_is_bot_for (declared_global_vars p)) pgs p)"
      and cover_edge:
        "\<And>u a w. (u, a, w) \<in> intra (prog_cfg prog_main_name p) \<Longrightarrow> (w, ()) \<in> fst (analyse_sign_for (resolved_st_q_is_bot_for (declared_global_vars p)) pgs p)"
      and cover_enter:
        "\<And>c dst fs as q k. (c, CallEdge dst fs as, FunctionEntry q, k) \<in> calls (prog_cfg prog_main_name p)
           \<Longrightarrow> (FunctionEntry q, ()) \<in> fst (analyse_sign_for (resolved_st_q_is_bot_for (declared_global_vars p)) pgs p)"
      and cover_combine:
        "\<And>c dst fs as q k. (c, CallEdge dst fs as, FunctionEntry q, k) \<in> calls (prog_cfg prog_main_name p)
           \<Longrightarrow> (k, ()) \<in> fst (analyse_sign_for (resolved_st_q_is_bot_for (declared_global_vars p)) pgs p)"
      and finI: "finite (intra (prog_cfg prog_main_name p))"
      and finC: "finite (calls (prog_cfg prog_main_name p))"
      and mem: "(v, c, Check_Refuted) \<in> set (analyse_sign_report_for pgs p)"
  shows "\<forall>s \<in> ltr_collect pgs (prog_cfg prog_main_name p) (cinit_stores pgs) v. \<not> truthy (aval c s)"
proof -
  have node_sound: "ltr_collect pgs (prog_cfg prog_main_name p) (cinit_stores pgs) v \<subseteq> \<lbrakk>analyse_sign_env_for (resolved_st_q_is_bot_for (declared_global_vars p)) pgs p v\<rbrakk>"
    using analyse_sign_collect_sound_for[OF solve wf cover_entry cover_edge cover_enter cover_combine finI finC]
    unfolding analyse_sign_gamma_eq_env_for .
  show ?thesis
    by (rule classify_checks_refuted_sound
          [where g = "prog_cfg prog_main_name p" and env = "analyse_sign_env_for (resolved_st_q_is_bot_for (declared_global_vars p)) pgs p"
             and classify = sign_classify_check
             and reach = "ltr_collect pgs (prog_cfg prog_main_name p) (cinit_stores pgs)"
             and v = v and gamma_state = "gamma_state :: sign abs_state \<Rightarrow> store set",
           OF finI mem[unfolded analyse_sign_report_for_def] sign_classify_check_refuted node_sound])
qed

end



text \<open>
  \<open>analyse_sign_eqs\<close>/\<open>analyse_sign\<close> (\<^theory>\<open>Voblint_Analysis.Sign_Exec_Sound\<close>) are the
  \<^const>\<open>declared_global\<close> \<open>p\<close> convenience instances, matching the shape \<open>gEx\<close>/\<open>dgEx_eqs\<close>/\<open>dgEx_sol\<close>
  already use for \<open>sign_ex_gs\<close>.
\<close>

corollary analyse_sign_sound:
  fixes p :: imp_prog
  assumes solve: "TD_side_always_join_Interp_solve_c (analyse_sign_eqs p) (cfg_exit (prog_cfg prog_main_name p), ()) \<noteq> None"
      and wf: "wf_compile_input (declared_global p) (prog_table p) (prog_procs p) prog_main_name (prog_main p)"
      and cover_entry: "(cfg_entry (prog_cfg prog_main_name p), ()) \<in> fst (analyse_sign p)"
      and cover_edge:
        "\<And>u a w. (u, a, w) \<in> intra (prog_cfg prog_main_name p) \<Longrightarrow> (w, ()) \<in> fst (analyse_sign p)"
      and cover_enter:
        "\<And>c dst fs as q k. (c, CallEdge dst fs as, FunctionEntry q, k) \<in> calls (prog_cfg prog_main_name p)
           \<Longrightarrow> (FunctionEntry q, ()) \<in> fst (analyse_sign p)"
      and cover_combine:
        "\<And>c dst fs as q k. (c, CallEdge dst fs as, FunctionEntry q, k) \<in> calls (prog_cfg prog_main_name p)
           \<Longrightarrow> (k, ()) \<in> fst (analyse_sign p)"
      and finI: "finite (intra (prog_cfg prog_main_name p))"
      and finC: "finite (calls (prog_cfg prog_main_name p))"
      and run: "star (pstep (declared_global p) (prog_table p)) (prog_main p, s, []) (residual, t, frs)"
      and init: "s \<in> cinit_stores (declared_global p)"
  shows "\<exists>v stk. csim (prog_table p) (prog_cfg prog_main_name p) (residual, t, frs) (v, t, stk)
                 \<and> t \<in> analyse_sign_gamma_for p (snd (analyse_sign p)) v"
  unfolding analyse_sign_def analyse_sign_eqs_def
  by (rule analyse_sign_sound_for
        [OF wf[THEN wf_compile_input_reserved_ret_var]
            solve[unfolded analyse_sign_def analyse_sign_eqs_def]
            wf
            cover_entry[unfolded analyse_sign_def]
            cover_edge[unfolded analyse_sign_def]
            cover_enter[unfolded analyse_sign_def]
            cover_combine[unfolded analyse_sign_def]
            finI finC run init])

text \<open>
  \<open>analyse_sign_env\<close>/\<open>analyse_sign_report\<close> (\<^theory>\<open>Voblint_Analysis.Sign_Exec_Sound\<close>/
  \<^theory>\<open>Voblint_Analysis.Sign_Checks\<close>) are the check-report layer's own
  \<^const>\<open>declared_global\<close> \<open>p\<close> convenience instances, matching \<open>analyse_sign\<close>/\<open>analyse_sign_sound\<close>
  above.
\<close>

corollary analyse_sign_report_sound_proved:
  fixes p :: imp_prog and v :: pp and c :: exp
  assumes solve: "TD_side_always_join_Interp_solve_c (analyse_sign_eqs p) (cfg_exit (prog_cfg prog_main_name p), ()) \<noteq> None"
      and wf: "wf_compile_input (declared_global p) (prog_table p) (prog_procs p) prog_main_name (prog_main p)"
      and cover_entry: "(cfg_entry (prog_cfg prog_main_name p), ()) \<in> fst (analyse_sign p)"
      and cover_edge:
        "\<And>u a w. (u, a, w) \<in> intra (prog_cfg prog_main_name p) \<Longrightarrow> (w, ()) \<in> fst (analyse_sign p)"
      and cover_enter:
        "\<And>c dst fs as q k. (c, CallEdge dst fs as, FunctionEntry q, k) \<in> calls (prog_cfg prog_main_name p)
           \<Longrightarrow> (FunctionEntry q, ()) \<in> fst (analyse_sign p)"
      and cover_combine:
        "\<And>c dst fs as q k. (c, CallEdge dst fs as, FunctionEntry q, k) \<in> calls (prog_cfg prog_main_name p)
           \<Longrightarrow> (k, ()) \<in> fst (analyse_sign p)"
      and finI: "finite (intra (prog_cfg prog_main_name p))"
      and finC: "finite (calls (prog_cfg prog_main_name p))"
      and mem: "(v, c, Check_Proved) \<in> set (analyse_sign_report p)"
  shows "\<forall>s \<in> ltr_collect (declared_global p) (prog_cfg prog_main_name p) (cinit_stores (declared_global p)) v. truthy (aval c s)"
  unfolding analyse_sign_def analyse_sign_eqs_def
  by (rule analyse_sign_report_sound_proved_for
        [OF wf[THEN wf_compile_input_reserved_ret_var]
            solve[unfolded analyse_sign_def analyse_sign_eqs_def]
            wf
            cover_entry[unfolded analyse_sign_def]
            cover_edge[unfolded analyse_sign_def]
            cover_enter[unfolded analyse_sign_def]
            cover_combine[unfolded analyse_sign_def]
            finI finC mem[unfolded analyse_sign_report_def]])

corollary analyse_sign_report_sound_refuted:
  fixes p :: imp_prog and v :: pp and c :: exp
  assumes solve: "TD_side_always_join_Interp_solve_c (analyse_sign_eqs p) (cfg_exit (prog_cfg prog_main_name p), ()) \<noteq> None"
      and wf: "wf_compile_input (declared_global p) (prog_table p) (prog_procs p) prog_main_name (prog_main p)"
      and cover_entry: "(cfg_entry (prog_cfg prog_main_name p), ()) \<in> fst (analyse_sign p)"
      and cover_edge:
        "\<And>u a w. (u, a, w) \<in> intra (prog_cfg prog_main_name p) \<Longrightarrow> (w, ()) \<in> fst (analyse_sign p)"
      and cover_enter:
        "\<And>c dst fs as q k. (c, CallEdge dst fs as, FunctionEntry q, k) \<in> calls (prog_cfg prog_main_name p)
           \<Longrightarrow> (FunctionEntry q, ()) \<in> fst (analyse_sign p)"
      and cover_combine:
        "\<And>c dst fs as q k. (c, CallEdge dst fs as, FunctionEntry q, k) \<in> calls (prog_cfg prog_main_name p)
           \<Longrightarrow> (k, ()) \<in> fst (analyse_sign p)"
      and finI: "finite (intra (prog_cfg prog_main_name p))"
      and finC: "finite (calls (prog_cfg prog_main_name p))"
      and mem: "(v, c, Check_Refuted) \<in> set (analyse_sign_report p)"
  shows "\<forall>s \<in> ltr_collect (declared_global p) (prog_cfg prog_main_name p) (cinit_stores (declared_global p)) v. \<not> truthy (aval c s)"
  unfolding analyse_sign_def analyse_sign_eqs_def
  by (rule analyse_sign_report_sound_refuted_for
        [OF wf[THEN wf_compile_input_reserved_ret_var]
            solve[unfolded analyse_sign_def analyse_sign_eqs_def]
            wf
            cover_entry[unfolded analyse_sign_def]
            cover_edge[unfolded analyse_sign_def]
            cover_enter[unfolded analyse_sign_def]
            cover_combine[unfolded analyse_sign_def]
            finI finC mem[unfolded analyse_sign_report_def]])

text \<open>
  \<open>gEx\<close>, \<open>dgEx_eqs\<close>, and \<open>dgEx_sol\<close> really are the \<open>gs = sign_ex_gs\<close>,
  \<open>p = sign_ex_prog\<close> instance of the arbitrary-classifier, arbitrary-program
  chain above, not a separate parallel definition.
\<close>

lemma gEx_prog_cfg: "gEx = prog_cfg prog_main_name sign_ex_prog"
  unfolding gEx_def prog_cfg_def sign_ex_pi_def by simp

lemma dgEx_eqs_is_analyse_sign_eqs: "dgEx_eqs = analyse_sign_eqs sign_ex_prog"
  unfolding dgEx_eqs_def analyse_sign_eqs_def analyse_sign_eqs_for_def gEx_prog_cfg by simp

lemma dgEx_sol_is_analyse_sign: "dgEx_sol = analyse_sign sign_ex_prog"
  unfolding dgEx_sol_def analyse_sign_def analyse_sign_for_def dgEx_eqs_is_analyse_sign_eqs
    analyse_sign_eqs_def gEx_prog_cfg by simp

subsection \<open>A second program through the same entry point\<close>

text \<open>
  \<open>analyse_sign_demo2_prog\<close> is a different program from \<open>sign_ex_prog\<close>, run
  through the very same \<open>analyse_sign\<close>: the entry point above is not
  specialized to one hard-coded example.
\<close>

definition analyse_sign_demo2_prog :: imp_prog where
  "analyse_sign_demo2_prog = program { void main() { a := 1; b := a; c := b } }"

text \<open>
  Precise, not a coincidence: \<open>a := 1\<close> is exactly \<open>SPos\<close>, and each name is
  routed to the exec state that owns it at every edge, so the value carries
  through \<open>b := a; c := b\<close> untouched to the exit. What matters here is that
  \<open>analyse_sign\<close> computes at all on a program it was never specialized to,
  and does so precisely.
\<close>

lemma analyse_sign_demo2_result:
  "map_option (\<lambda>sol. case map_lift (fun_of_exec_dg_st_for (declared_global analyse_sign_demo2_prog))
                        (locals (snd sol (Inl (cfg_exit (prog_cfg prog_main_name analyse_sign_demo2_prog), ()))))
                      of Lifted s \<Rightarrow> Some (s (STR ''c'')) | Bot \<Rightarrow> None)
     (TD_side_always_join_Interp_solve_c (analyse_sign_eqs analyse_sign_demo2_prog)
        (cfg_exit (prog_cfg prog_main_name analyse_sign_demo2_prog), ())) = Some (Some SPos)"
  by eval


text \<open>
  No per-domain \<open>export_code\<close> here: \<^const>\<open>dgEx_sol\<close>, \<^const>\<open>analyse_sign_for\<close>, and
  \<^const>\<open>analyse_sign\<close> already export cleanly (confirmed once, historically, as the M1
  codegen-closure milestone), but a caller reaches the same generic, already-sound
  \<^const>\<open>analyse_sign_report\<close> through the unified dispatcher \<open>analyse\<close>
  (\<open>Analyse_Dispatch\<close>, downstream), which is the one thing actually exported to
  OCaml --- a second, domain-specific export module here would just be a parallel,
  redundant API surface for the same computation.
\<close>
subsection \<open>Base-style flow-sensitive global regressions\<close>

text \<open>
  Acceptance regressions for the Base-style migration: \<open>D\<close> carries the whole abstract
  state (VIMP globals included), reachability-lifted, instead of routing globals
  through a separate flow-\<^emph>\<open>in\<close>sensitive solver-global unknown.
\<close>

definition sign_flow_sensitive_global_prog :: imp_prog where
  "sign_flow_sensitive_global_prog = program { global Gx;
     void f() { Gx := 1 }
     void main() { Gx := 0; f(); __voblint_check(0 < Gx) } }"

text \<open>
  Under the old unlifted routing, \<open>Gx := 0\<close> and \<open>Gx := 1\<close> both feed the same
  flow-insensitive shared summary and join to \<open>SNonNeg\<close>, leaving the check
  \<open>UNKNOWN\<close>. With the whole state lifted into \<open>D\<close>, the call's own local answer
  at the \<open>main\<close> exit carries \<open>Gx\<close>'s value exactly as \<^const>\<open>sign_tf_st_for\<close>
  and \<^const>\<open>sign_enter_st_for\<close> left it, so the check is exact.
\<close>

lemma sign_flow_sensitive_global_result:
  "(Statement 4, Less (N 0) (V (STR ''Gx'')), Check_Proved) \<in> set (analyse_sign_report sign_flow_sensitive_global_prog)"
  by eval

definition sign_dead_branch_bot_prog :: imp_prog where
  "sign_dead_branch_bot_prog = program { global Gx;
     void f(n) { if (n < 0) { Gx := -1 } else { Gx := 1 } }
     void main() { Gx := 0; f(5); __voblint_check(0 < Gx) } }"

text \<open>
  \<open>f\<close> is called with \<open>n = 5\<close>, abstracted to \<open>SPos\<close>: Sign's own comparison-against-zero
  tables refute \<open>n < 0\<close> exactly (\<open>SPos < SZero\<close> is definitely false), so the \<open>Gx := -1\<close>
  arm's own local answer is genuinely \<^const>\<open>Bot\<close> in the lifted carrier, not merely an
  imprecise contribution the exit join has to absorb. The two arms deliberately carry
  \<^emph>\<open>different\<close> signs so a leaked dead arm is observable: were the reachability-lift
  fix absent (or otherwise defeated), the join \<open>SNeg \<squnion> SPos = STop\<close> would leave the
  check \<open>UNKNOWN\<close> instead of \<open>PROVED\<close>. Contrast a numeric-bound guard such as \<open>n < 2\<close>
  at \<open>n = 5\<close>: Sign cannot refute that from \<open>SPos\<close> alone (unlike Interval, which tracks
  exact bounds -- see \<open>03-procedures/precision/05-dead_branch_no_bottom_leak.vimp\<close>), so
  that shape does not isolate this property for Sign.
\<close>

lemma sign_dead_branch_bot_result:
  "(Statement 6, Less (N 0) (V (STR ''Gx'')), Check_Proved) \<in> set (analyse_sign_report sign_dead_branch_bot_prog)"
  by eval

end

