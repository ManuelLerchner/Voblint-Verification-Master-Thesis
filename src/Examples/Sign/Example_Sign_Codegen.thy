theory Example_Sign_Codegen
  imports Exec_Sign_DG_Run Voblint_Analysis.Sign_Checks
begin

section \<open>Sign codegen API: an arbitrary VIMP program, and its OCaml export\<close>

subsection \<open>Whole-program entry point: an arbitrary VIMP program\<close>

text \<open>
  \<open>gEx\<close>/\<open>dgEx_eqs\<close>/\<open>dgEx_sol\<close> in \<open>Exec_Sign_DG_Run\<close> fix one hard-coded example.
  This section widens that same native D/G chain to an arbitrary classifier
  \<open>gs\<close> and program \<open>p\<close>, reusing \<^const>\<open>prog_cfg\<close> for the compiled CFG.  The
  locale interpretation below is the classifier-generic twin of
  \<open>sign_ex_reg\<close> in \<open>Exec_Sign_DG_Run\<close>: the same five transfer facts
  discharge \<^locale>\<open>unit_dg_exec_analysis\<close> at any classifier, not only at
  \<open>sign_ex_gs\<close>, because \<open>sign_is_sound_transfer_for\<close>,
  \<open>sign_tf_st_for_commute\<close>, and \<open>sign_enter_st_for_commute\<close> are already
  stated for an arbitrary \<open>gs\<close>.  \<open>gs\<close> stays an explicit parameter (rather
  than hard-wired to \<^const>\<open>declared_global\<close> applied to \<open>p\<close>) so a caller can
  override which variables count as global; \<open>analyse_sign\<close> below is the
  convenience instance at \<^const>\<open>declared_global\<close> \<open>p\<close>.
\<close>

context
  fixes gs :: "vname \<Rightarrow> bool"
    and p :: imp_prog
  assumes reserved: "reserved_ret_var gs"
begin

interpretation p_reg:
  unit_dg_exec_analysis gs
    "sign_tf_for gs" "sign_tf_st_for gs" "sign_enter_st_for gs"
    "TD_side_always_join_Interp.solve" "TD_side_always_join_Interp.solve_c"
proof -
  interpret p_transfer: sound_transfer_for gs "sign_tf_for gs"
    by (rule sign_is_sound_transfer_for)
  show "unit_dg_exec_analysis gs (sign_tf_for gs)
          (sign_tf_st_for gs) (sign_enter_st_for gs)
          TD_side_always_join_Interp.solve TD_side_always_join_Interp.solve_c"
    by unfold_locales
       (rule reserved
             p_transfer.tf_sound_assign_for p_transfer.tf_sound_random_for
             p_transfer.tf_sound_assume_for p_transfer.tf_sound_assume_not_for
             p_transfer.tf_sound_enter_for p_transfer.tf_sound_combine_for
             sign_tf_st_for_commute[folded fun_of_exec_dg_st_for_def]
             sign_enter_st_for_commute[folded fun_of_exec_dg_st_for_def]
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
  "(pp \<times> unit + unit \<Rightarrow> (sign exec_dg_st, sign exec_dg_st) dg_state) \<Rightarrow> pp \<Rightarrow> store set" where
  "analyse_sign_gamma_for = p_reg.gamma"

text \<open>
  \<open>analyse_sign_eqs_for\<close>/\<open>analyse_sign_for\<close> (the native D/G equation system and its solved
  result, at an arbitrary classifier \<open>gs\<close> and program \<open>p\<close>) and \<open>analyse_sign_env_for\<close> now live in
  \<^theory>\<open>Voblint_Analysis.Sign_Exec_Sound\<close> --- they are pure computation, no dependence on the
  \<open>unit_dg_exec_analysis\<close> locale \<open>p_reg\<close> interprets here, so they need not sit in this Examples
  session. Every reference below applies them to this context's fixed \<open>gs\<close>/\<open>p\<close> explicitly, since
  outside a context a definition takes its fixed variables as ordinary leading arguments.

  The connection lemma: soundness for an arbitrary \<open>gs\<close> and \<open>p\<close> reuses
  \<open>unit_dg_exec_analysis.run_source_sound\<close> exactly as \<open>dgEx_source_run_sound\<close>
  does, just with the solver-domain, well-formedness, and coverage facts left
  as hypotheses instead of discharged \<open>by eval\<close> --- symbolic \<open>gs\<close>/\<open>p\<close> cannot
  be run through the executable solver at proof time the way the one
  hard-coded \<open>sign_ex_gs\<close>/\<open>sign_ex_prog\<close> can.  \<open>sound0\<close> stays internal: it
  never depended on the program, only on \<open>cinit_sign_st\<close> and the classifier,
  exactly as in \<open>dgEx_sound0\<close>.
\<close>

theorem analyse_sign_sound_for:
  assumes solve: "TD_side_always_join_Interp_solve_c (analyse_sign_eqs_for gs p) (cfg_exit (prog_cfg prog_main_name p), ()) \<noteq> None"
      and wf: "wf_compile_input gs (prog_table p) (prog_procs p) prog_main_name (prog_main p)"
      and cover_entry: "(cfg_entry (prog_cfg prog_main_name p), ()) \<in> fst (analyse_sign_for gs p)"
      and cover_edge:
        "\<And>u a w. (u, a, w) \<in> intra (prog_cfg prog_main_name p) \<Longrightarrow> (w, ()) \<in> fst (analyse_sign_for gs p)"
      and cover_enter:
        "\<And>c dst fs as q k. (c, CallEdge dst fs as, FunctionEntry q, k) \<in> calls (prog_cfg prog_main_name p)
           \<Longrightarrow> (FunctionEntry q, ()) \<in> fst (analyse_sign_for gs p)"
      and cover_combine:
        "\<And>c dst fs as q k. (c, CallEdge dst fs as, FunctionEntry q, k) \<in> calls (prog_cfg prog_main_name p)
           \<Longrightarrow> (k, ()) \<in> fst (analyse_sign_for gs p)"
      and finI: "finite (intra (prog_cfg prog_main_name p))"
      and finC: "finite (calls (prog_cfg prog_main_name p))"
      and run: "star (pstep gs (prog_table p)) (prog_main p, s, []) (residual, t, frs)"
      and init: "s \<in> cinit_stores gs"
  shows "\<exists>v stk. csim (prog_table p) (prog_cfg prog_main_name p) (residual, t, frs) (v, t, stk)
                 \<and> t \<in> analyse_sign_gamma_for (snd (analyse_sign_for gs p)) v"
proof -
  have sound0:
    "cinit_stores gs \<subseteq>
       \<lbrakk>combine_env\<^sup># gs (fun_of_exec_dg_st_for gs cinit_sign_st)
          (fun_of_exec_dg_st_for gs cinit_sign_st)\<rbrakk>"
    by (simp add: fun_of_exec_dg_st_for_def fun_of_st_cinit_sign_st_for cinit_stores_def
                  gamma_state_def combine_env_abs_def)
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
              sound0[folded gamma_unit_def] init run])
qed

text \<open>
  The per-node collecting analogue of \<open>analyse_sign_sound_for\<close>, for a
  check-report layer that wants soundness at an arbitrary node without a
  concrete source run --- reuses \<open>p_reg.collect_sound\<close>, the same
  locale-level fact \<open>run_source_sound\<close> itself is built from
  (\<^theory>\<open>Voblint_Formalization.Run_Analysis_Sound\<close>).
\<close>

theorem analyse_sign_collect_sound_for:
  assumes solve: "TD_side_always_join_Interp_solve_c (analyse_sign_eqs_for gs p) (cfg_exit (prog_cfg prog_main_name p), ()) \<noteq> None"
      and wf: "wf_compile_input gs (prog_table p) (prog_procs p) prog_main_name (prog_main p)"
      and cover_entry: "(cfg_entry (prog_cfg prog_main_name p), ()) \<in> fst (analyse_sign_for gs p)"
      and cover_edge:
        "\<And>u a w. (u, a, w) \<in> intra (prog_cfg prog_main_name p) \<Longrightarrow> (w, ()) \<in> fst (analyse_sign_for gs p)"
      and cover_enter:
        "\<And>c dst fs as q k. (c, CallEdge dst fs as, FunctionEntry q, k) \<in> calls (prog_cfg prog_main_name p)
           \<Longrightarrow> (FunctionEntry q, ()) \<in> fst (analyse_sign_for gs p)"
      and cover_combine:
        "\<And>c dst fs as q k. (c, CallEdge dst fs as, FunctionEntry q, k) \<in> calls (prog_cfg prog_main_name p)
           \<Longrightarrow> (k, ()) \<in> fst (analyse_sign_for gs p)"
      and finI: "finite (intra (prog_cfg prog_main_name p))"
      and finC: "finite (calls (prog_cfg prog_main_name p))"
  shows "ltr_collect gs (prog_cfg prog_main_name p) (cinit_stores gs) v
           \<subseteq> analyse_sign_gamma_for (snd (analyse_sign_for gs p)) v"
proof -
  have sound0:
    "cinit_stores gs \<subseteq>
       \<lbrakk>combine_env\<^sup># gs (fun_of_exec_dg_st_for gs cinit_sign_st)
          (fun_of_exec_dg_st_for gs cinit_sign_st)\<rbrakk>"
    by (simp add: fun_of_exec_dg_st_for_def fun_of_st_cinit_sign_st_for cinit_stores_def
                  gamma_state_def combine_env_abs_def)
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
              sound0[folded gamma_unit_def]])
qed

text \<open>
  \<open>p_reg\<close> is local, so its qualified constants (and the raw locale
  predicate \<open>unit_dg_exec_analysis\<close>) do not survive past the closing
  \<open>end\<close> either --- \<open>analyse_sign_env_for\<close> reads the exit-answer/side-effect
  split \<open>dg_state\<close> keeps (\<open>Inl (v, ())\<close> for the local answer at \<open>v\<close>,
  \<open>Inr ()\<close> for the global side effect) the same way \<open>dgEx_inspect\<close> in
  \<open>Exec_Sign_DG_Run\<close> does by hand, and \<open>analyse_sign_gamma_eq_env_for\<close>
  proves it is exactly what \<open>analyse_sign_gamma_for\<close> already concretizes ---
  via \<open>p_reg.gamma_def\<close> and \<open>p_reg.sds\<close>, not a new soundness argument.
\<close>

lemma analyse_sign_gamma_eq_env_for:
  "analyse_sign_gamma_for (snd (analyse_sign_for gs p)) v = \<lbrakk>analyse_sign_env_for gs p v\<rbrakk>"
  unfolding analyse_sign_gamma_for_def analyse_sign_env_for_def
  by (simp add: p_reg.gamma_def
                sound_dg_spec.dg_gamma_def[OF p_reg.sds[unfolded sound_dg_spec_ltr_for_def]]
                sound_dg_spec.dg_D_def[OF p_reg.sds[unfolded sound_dg_spec_ltr_for_def]]
                sound_dg_spec.dg_G_def[OF p_reg.sds[unfolded sound_dg_spec_ltr_for_def]]
                gamma_unit_def fun_of_dg_st_for_def)

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
  fixes v :: pp and c :: bexp
  assumes solve: "TD_side_always_join_Interp_solve_c (analyse_sign_eqs_for gs p) (cfg_exit (prog_cfg prog_main_name p), ()) \<noteq> None"
      and wf: "wf_compile_input gs (prog_table p) (prog_procs p) prog_main_name (prog_main p)"
      and cover_entry: "(cfg_entry (prog_cfg prog_main_name p), ()) \<in> fst (analyse_sign_for gs p)"
      and cover_edge:
        "\<And>u a w. (u, a, w) \<in> intra (prog_cfg prog_main_name p) \<Longrightarrow> (w, ()) \<in> fst (analyse_sign_for gs p)"
      and cover_enter:
        "\<And>c dst fs as q k. (c, CallEdge dst fs as, FunctionEntry q, k) \<in> calls (prog_cfg prog_main_name p)
           \<Longrightarrow> (FunctionEntry q, ()) \<in> fst (analyse_sign_for gs p)"
      and cover_combine:
        "\<And>c dst fs as q k. (c, CallEdge dst fs as, FunctionEntry q, k) \<in> calls (prog_cfg prog_main_name p)
           \<Longrightarrow> (k, ()) \<in> fst (analyse_sign_for gs p)"
      and finI: "finite (intra (prog_cfg prog_main_name p))"
      and finC: "finite (calls (prog_cfg prog_main_name p))"
      and mem: "(v, c, Check_Proved) \<in> set (analyse_sign_report_for gs p)"
  shows "\<forall>s \<in> ltr_collect gs (prog_cfg prog_main_name p) (cinit_stores gs) v. bval c s"
proof -
  have node_sound: "ltr_collect gs (prog_cfg prog_main_name p) (cinit_stores gs) v \<subseteq> \<lbrakk>analyse_sign_env_for gs p v\<rbrakk>"
    using analyse_sign_collect_sound_for[OF solve wf cover_entry cover_edge cover_enter cover_combine finI finC]
    unfolding analyse_sign_gamma_eq_env_for .
  show ?thesis
    by (rule classify_checks_proved_sound
          [where g = "prog_cfg prog_main_name p" and env = "analyse_sign_env_for gs p"
             and classify = sign_classify_check
             and reach = "ltr_collect gs (prog_cfg prog_main_name p) (cinit_stores gs)"
             and v = v and gamma_state = "gamma_state :: sign abs_state \<Rightarrow> store set",
           OF finI mem[unfolded analyse_sign_report_for_def] sign_classify_check_proved node_sound])
qed

theorem analyse_sign_report_sound_refuted_for:
  fixes v :: pp and c :: bexp
  assumes solve: "TD_side_always_join_Interp_solve_c (analyse_sign_eqs_for gs p) (cfg_exit (prog_cfg prog_main_name p), ()) \<noteq> None"
      and wf: "wf_compile_input gs (prog_table p) (prog_procs p) prog_main_name (prog_main p)"
      and cover_entry: "(cfg_entry (prog_cfg prog_main_name p), ()) \<in> fst (analyse_sign_for gs p)"
      and cover_edge:
        "\<And>u a w. (u, a, w) \<in> intra (prog_cfg prog_main_name p) \<Longrightarrow> (w, ()) \<in> fst (analyse_sign_for gs p)"
      and cover_enter:
        "\<And>c dst fs as q k. (c, CallEdge dst fs as, FunctionEntry q, k) \<in> calls (prog_cfg prog_main_name p)
           \<Longrightarrow> (FunctionEntry q, ()) \<in> fst (analyse_sign_for gs p)"
      and cover_combine:
        "\<And>c dst fs as q k. (c, CallEdge dst fs as, FunctionEntry q, k) \<in> calls (prog_cfg prog_main_name p)
           \<Longrightarrow> (k, ()) \<in> fst (analyse_sign_for gs p)"
      and finI: "finite (intra (prog_cfg prog_main_name p))"
      and finC: "finite (calls (prog_cfg prog_main_name p))"
      and mem: "(v, c, Check_Refuted) \<in> set (analyse_sign_report_for gs p)"
  shows "\<forall>s \<in> ltr_collect gs (prog_cfg prog_main_name p) (cinit_stores gs) v. \<not> bval c s"
proof -
  have node_sound: "ltr_collect gs (prog_cfg prog_main_name p) (cinit_stores gs) v \<subseteq> \<lbrakk>analyse_sign_env_for gs p v\<rbrakk>"
    using analyse_sign_collect_sound_for[OF solve wf cover_entry cover_edge cover_enter cover_combine finI finC]
    unfolding analyse_sign_gamma_eq_env_for .
  show ?thesis
    by (rule classify_checks_refuted_sound
          [where g = "prog_cfg prog_main_name p" and env = "analyse_sign_env_for gs p"
             and classify = sign_classify_check
             and reach = "ltr_collect gs (prog_cfg prog_main_name p) (cinit_stores gs)"
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
                 \<and> t \<in> analyse_sign_gamma_for (declared_global p) (snd (analyse_sign p)) v"
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
  fixes p :: imp_prog and v :: pp and c :: bexp
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
  shows "\<forall>s \<in> ltr_collect (declared_global p) (prog_cfg prog_main_name p) (cinit_stores (declared_global p)) v. bval c s"
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
  fixes p :: imp_prog and v :: pp and c :: bexp
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
  shows "\<forall>s \<in> ltr_collect (declared_global p) (prog_cfg prog_main_name p) (cinit_stores (declared_global p)) v. \<not> bval c s"
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
  "map_option (\<lambda>sol. lookup_resolved_st_q
                        (locals (snd sol (Inl (cfg_exit (prog_cfg prog_main_name analyse_sign_demo2_prog), ()))))
                        (location_of (declared_global analyse_sign_demo2_prog) (STR ''c'')))
     (TD_side_always_join_Interp_solve_c (analyse_sign_eqs analyse_sign_demo2_prog)
        (cfg_exit (prog_cfg prog_main_name analyse_sign_demo2_prog), ())) = Some SPos"
  by eval

text \<open>
  No per-domain \<open>export_code\<close> here: \<^const>\<open>dgEx_sol\<close>, \<^const>\<open>analyse_sign_for\<close>, and
  \<^const>\<open>analyse_sign\<close> already export cleanly (confirmed once, historically, as the M1
  codegen-closure milestone), but a caller reaches the same generic, already-sound
  \<^const>\<open>analyse_sign_report\<close> through the unified dispatcher \<open>analyse\<close>
  (\<open>Example_Analysis_Dispatch\<close>, downstream), which is the one thing actually exported to
  OCaml --- a second, domain-specific export module here would just be a parallel,
  redundant API surface for the same computation.
\<close>

end
